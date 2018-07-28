%%%-------------------------------------------------------------------
%%% @author Chen Slepher <slepheric@gmail.com>
%%% @copyright (C) 2018, Chen Slepher
%%% @doc
%%%
%%% @end
%%% Created : 29 May 2018 by Chen Slepher <slepheric@gmail.com>
%%%-------------------------------------------------------------------
-module(type_formal_trans).

%% API
-export([to_clauses/1]).

%%%===================================================================
%%% API
%%%===================================================================
to_clauses(Type) ->
    Clauses = to_clauses(Type, [], 1),
    lists:map(
      fun({Pattern, Guards, _NextVar}) ->
          {Pattern, Guards}
      end, Clauses).

to_clauses({c, tuple, Tuples, _}, Guards, NextVar) when is_list(Tuples) ->
    map_pattern(fun(Pattern) -> {tuple, Pattern} end, mapfold(Tuples, Guards, NextVar, true));
to_clauses({c, tuple, _, _}, Guards, NextVar) ->
    [{{var, NextVar}, [{is_tuple, NextVar}|Guards], NextVar + 1}];
to_clauses({c, function, _Function, _}, Guards, NextVar) ->
    [{{var, NextVar}, [{is_function, NextVar}|Guards], NextVar + 1}];
to_clauses({c, atom, Atoms, _}, Guards, NextVar) when is_list(Atoms) ->
    lists:map(fun(Atom) -> {Atom, Guards, NextVar} end, Atoms);
to_clauses({c, atom, any, _}, Guards, NextVar) ->
    [{{var, NextVar}, [{is_atom, NextVar}|Guards], NextVar + 1}];
to_clauses({c, tuple_set, [{_N, Sets}], _}, Guards, NextVar) ->
    lists:foldl(fun(Item, Acc) -> to_clauses(Item, Guards, NextVar) ++ Acc end, [], Sets);
to_clauses({c, union, Unions, _}, Guards, NextVar) ->
    lists:foldl(fun(Item, Acc) -> to_clauses(Item, Guards, NextVar) ++ Acc end, [], Unions);
to_clauses({c, list, _, _}, Guards, NextVar) ->
    [{{var, NextVar}, [{is_list, NextVar}|Guards], NextVar + 1}];
to_clauses({c, map, {Maps, _, _}, _}, Guards, NextVar) ->
    case mapfold(Maps, Guards, NextVar, false) of
        [] ->
            [{{var, NextVar}, [{is_map, NextVar}|Guards], NextVar + 1}];
        Clauses ->
            map_pattern(fun(Pattern) -> {map, Pattern} end, Clauses)
    end;
%to_clauses({_KeyType, mandatory, {c, atom, any, _}}, _Guards, _NextVar) ->
%    [];
to_clauses({_KeyType, mandatory, any}, _Guards, _NextVar) ->
    [];
to_clauses({{c, atom, [Atom], _}, mandatory, ValueType}, Guards, NextVar) ->
    map_pattern(fun(Pattern) -> {Atom, Pattern} end, to_clauses(ValueType, Guards, NextVar));
to_clauses({_KeyType, mandatory, _ValueType}, _Guards, _NextVar) ->
    [];
to_clauses({_KeyType, optional, _ValueType}, _Guards, _NextVar) ->
    [];
to_clauses({c, binary, _, _}, Guards, NextVar) ->
    [{{var, NextVar}, [{is_binary, NextVar}|Guards], NextVar + 1}];
to_clauses({c, var, _, _}, Guards, NextVar) ->
    [{{var, 0}, Guards, NextVar}];
to_clauses(any, Guards, NextVar) ->
    [{{var, 0}, Guards, NextVar}];
to_clauses({c, opaque, _Body, _Qualifier}, Guards, NextVar) ->
    [{{var, 0}, Guards, NextVar}];
to_clauses(none, _Guards, _NextVar) ->
    [];
to_clauses({c, _Type, _Body, _Qualifier}, _Guards, _NextVar) ->
    [].

to_clauses(H, Guards, NextVar, StrictMode) ->
    case to_clauses(H, Guards, NextVar) of
        [] ->
            case StrictMode of
                true ->
                    [{{var, 0}, Guards, NextVar}];
                false ->
                    []
            end;
        Clauses ->
            Clauses
    end.

mapfold(Values, Guards, NextVar, StrictMode) ->
    lists:flatten(cartesian(Values, Guards, NextVar, StrictMode)).    

cartesian([H|T], Guards, NextVar, StrictMode) ->
    case cartesian(T, Guards, NextVar, StrictMode) of
        [] ->
            map_pattern(fun(Pattern) -> [Pattern] end, to_clauses(H, Guards, NextVar, StrictMode));
        TClauses ->
            lists:flatten(
              lists:map(
                fun({TPatterns, NGuards, NNextVar}) ->
                      case to_clauses(H, NGuards, NNextVar, StrictMode) of
                          [] ->
                              [{TPatterns, NGuards, NNextVar}];
                          Clauses ->
                              map_pattern(fun(Pattern) -> [Pattern|TPatterns] end, Clauses)
                      end
              end, TClauses))
    end;
cartesian([], _Guards, _NextVar, _StrictMode) ->
    [].

map_pattern(Fun, Clauses) ->
    lists:map(
      fun({Pattern, NGuards, NNextVar}) ->
            {Fun(Pattern), NGuards, NNextVar}
      end, Clauses).

%%--------------------------------------------------------------------
%% @doc
%% @spec
%% @end
%%--------------------------------------------------------------------

%%%===================================================================
%%% Internal functions
%%%===================================================================

