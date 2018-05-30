%%%-------------------------------------------------------------------
%%% @author Chen Slepher <slepheric@gmail.com>
%%% @copyright (C) 2018, Chen Slepher
%%% @doc
%%%
%%% @end
%%% Created : 17 May 2018 by Chen Slepher <slepheric@gmail.com>
%%%-------------------------------------------------------------------
-module(type_expansion).

%% API
-export([core/1, exported_types/1, expand/3, expand/4, types_and_rec_map/1, dialyzer_utils/0]).
-export([cache/0, finalize_cache/1, cache_errors/1]).

-record(cache, {rec_table, module_table, type_table, error_table}).

%%%===================================================================
%%% API
%%%===================================================================
core(Module) ->
    DialyzerUtils = dialyzer_utils(),
    case code:get_object_code(Module) of
        {Module, _, Beam} ->
            DialyzerUtils:get_core_from_beam(Beam);
        error -> 
            error
    end.

%% from unexported function dialyzer_analysis_callgraph:exported_types_from_core/1
exported_types(Core) ->
    Attrs = cerl:module_attrs(Core),
    ExpTypes1 = [cerl:concrete(L2) || {L1, L2} <- Attrs, cerl:is_literal(L1),
                                      cerl:is_literal(L2),
                                      cerl:concrete(L1) =:= 'export_type'],
    ExpTypes2 = lists:flatten(ExpTypes1),
    M = cerl:atom_val(cerl:module_name(Core)),
    sets:from_list([{M, F, A} || {F, A} <- ExpTypes2]).


expand(Module, Type, Arity) ->
    Cache = cache(),
    Expansion = 
        case expand(Module, Type, Arity, Cache) of
            {ok, ExpandedForm} ->
                case ets:tab2list(error_table) of
                    [] ->
                        {ok, ExpandedForm};
                    Errors -> 
                        {error, Errors}
                end;
            {error, Reason} ->
                {error, Reason}
        end,
    finalize_cache(Cache),
    Expansion.

expand(Module, Type, Arity, Cache) ->
    case preload_types(Module, Type, Arity, Cache) of
        ok ->
            t_from_mfa(Module, Type, Arity, Cache);
        {error, Reason} ->
            {error, Reason}
    end.

preload_types_with_context(Module, Type, Arity, #cache{error_table = ErrorTable} = Cache, ContextModule, Line) ->
    case preload_types(Module, Type, Arity, Cache) of
        ok ->
            ok;
        {error, find_module_failed} ->
            ets:insert(ErrorTable, {Module, ContextModule, Line}),
            ok;
        {error, find_type_failed} ->
            ets:insert(ErrorTable, {{Module, Type, Arity}, ContextModule, Line}),
            ok
    end.

preload_types(Module, Type, Arity, #cache{rec_table = RecTable, module_table = ModuleTable} = Cache) ->
    case load_module_data(Module, Cache) of
        ok ->
            TypesVisited = get_types_visited(Module, ModuleTable),
            case ordsets:is_element({Type, Arity}, TypesVisited) of
                false ->
                    NTypesVisited = ordsets:add_element({Type, Arity}, TypesVisited),
                    ets:insert(ModuleTable, {Module, NTypesVisited}),
                    case rec_table_find_form(Module, Type, Arity, RecTable) of
                        {ok, Form} ->
                            preload_form_types(Form, Module, Cache),
                            ok;
                        error ->
                            {error, find_type_failed}
                    end;
                true ->
                    ok
            end;
        error ->
            {error, find_module_failed}
    end.

preload_form_types(Form, Module, Cache) ->
    ast_traverse:map(
      fun(pre, Node) ->
              preload_node_types(Node, Module, Cache);
         (_, Node) ->
              Node
      end, Form).

preload_node_types(
  {remote_type, Line, [{atom, _, RemoteModule}, {atom, _, Type}, Args]} = Node,
  Module, Cache) ->
    Arity = length(Args),
    preload_types_with_context(RemoteModule, Type, Arity, Cache, Module, Line),
    Node;

preload_node_types(
  {user_type, Line, Type, Args} = Node, Module, Cache) ->
    Arity = length(Args),
    preload_types_with_context(Module, Type, Arity, Cache, Module, Line),
    Node;

preload_node_types(Node, _Module, _Cache) ->
    Node.

cache() ->
    RecTable = ets:new(rec_table, [protected]),
    ModuleTable = ets:new(module_table, [protected]),
    TypeTable = ets:new(type_table, [protected, bag]),
    ErrorTable = ets:new(error_table, [protected, bag]),
    cache(RecTable, ModuleTable, TypeTable, ErrorTable).

cache(RecTable, ModuleTable, TypeTable, ErrorTable) ->
    #cache{rec_table = RecTable, module_table = ModuleTable, type_table = TypeTable,
           error_table = ErrorTable}.

finalize_cache(#cache{rec_table = RecTable, module_table = ModuleTable, type_table = TypeTable,
                      error_table = ErrorTable}) ->
    ets:delete(RecTable),
    ets:delete(ModuleTable),
    ets:delete(TypeTable),
    ets:delete(ErrorTable).

cache_errors(#cache{error_table = ErrorTable}) ->
    ets:tab2list(ErrorTable).

%%--------------------------------------------------------------------
%% @doc
%% @spec
%% @end
%%--------------------------------------------------------------------

%%%===================================================================
%%% Internal functions
%%%===================================================================
load_module_data(Module, #cache{module_table = ModuleTable, type_table = TypeTable, rec_table = RecTable}) ->
    case ets:lookup(ModuleTable, Module) of
        [] ->
            ets:insert(ModuleTable, {Module, ordsets:new()}),
            case types_and_rec_map(Module) of
                {ok, {Types, RecMap}} ->
                    ets:insert(TypeTable, {Module, Types}),
                    ets:insert(RecTable, {Module, RecMap}),
                    ok;
                error ->
                    error
            end;
        _ ->
            ok
    end.

get_types_visited(Module, ModuleTab) ->
    case ets:lookup(ModuleTab, Module) of
        [{Module, TypesVisited}] ->
            TypesVisited;
        [] ->
            ordsets:new()
    end.

rec_table_find_form(Module, Type, Arity, RecTable) ->
    case ets:lookup(RecTable, Module) of
        [{Module, RecMap}] ->
            case map_find_form(Type, Arity, RecMap) of
                {ok, Form} ->
                    {ok, Form};
                error ->
                    error
            end;
        [] ->
            error
  end.

map_find_form(Type, Arity, RecMap) ->
    case maps:find({type, Type, Arity}, RecMap) of
        {ok, {{_Module, _Line, Form, _Args}, _}} ->
            {ok, Form};
        _ ->
            error
    end.

types_and_rec_map(Module) ->
    DialyzerUtils = dialyzer_utils(),
    case core(Module) of
        {ok, Core} ->
            Types = exported_types(Core),
            case DialyzerUtils:get_record_and_type_info(Core) of
                {ok, RecMap} ->
                    {ok, {Types, RecMap}};
                _ ->
                    error
            end;
        _ ->
            error
    end.

t_from_mfa(Module, Type, Arity, #cache{type_table = TypeTable, rec_table = RecTable}) ->
    case rec_table_find_form(Module, Type, Arity, RecTable) of
        {ok, Form} ->
            Types = types_from_table(TypeTable),
            TypeKey = {type, {Module, Type, Arity}},
            Cache = erl_types:cache__new(),
            VarTable = erl_types:var_table__new(),
            {ExpandedForm, _NCache} =
                erl_types:t_from_form(Form, Types, TypeKey, RecTable, VarTable, Cache),
            {ok, ExpandedForm};
        error ->
            error
    end.

types_from_table(TypeTable) ->
    ets:foldl(
      fun({_Module, Types}, Acc) ->
              sets:union(Types, Acc)
      end, sets:new(), TypeTable).

dialyzer_utils() ->
    case lists:member({get_core_from_beam, 1}, dialyzer_utils:module_info(exports)) of
        true ->
            dialyzer_utils;
        false ->
            dialyzer_utils_R20
    end.
