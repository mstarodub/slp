:- op(1199,xfx,::).
:- discontiguous (::)/2.

% meta-assumptions:
%   only conjunctions
%   normalized SLP (all clauses forming a predicate add up to 1)
%   pure SLP (no non-prob. clauses)

% invariant helper
err(X) :-
    % TODO: print an error message
    write(user_error, "broken invariant"),
    halt.

% assumptions:
%   G is the goal with only free variables
%   G is non-compound; TODO: assert user input as clause and retract later
%   ArgList contains the instantiated parameters for G
p(G, ArgList, Result) :-
    functor(G, Functor, Arity),
    ( length(ArgList, Len), Len \= Arity -> err(Len) ; true ),
    GInstantiated =.. [Functor|ArgList],
    z(GInstantiated, Numerator),
    z(G, Denominator),
    Result is Numerator / Denominator.

% head recursion 
z((G1 ,G2), WeightRes) :-
    z(G1, Weight1),
    z(G2, Weight2),
    WeightRes is Weight1*Weight2.

% body recursion, compound
z(G, Weight) :-
    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    [UnifClause|UnifSetTail] = UnifSet,
    nth0(0, UnifClause, ClauseProb),
    nth0(2, UnifClause, ClauseBody),
    % only non-variable bodies won't cause infinite recursion
    nonvar(ClauseBody),
    ClauseBody = (Body1, Body2),
    z(Body1, W1),
    z(Body2, W2),
    Weight is ClauseProb * W1 * W2.

% body recursion, non-compound
z(G, Weight) :-
    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    [UnifClause|UnifSetTail] = UnifSet,
    nth0(0, UnifClause, ClauseProb),
    nth0(2, UnifClause, ClauseBody),
    % only non-variable bodies won't cause infinite recursion
    ClauseBody \= (Body1, Body2),
    % TODO: maybe exclude true as well? / base case
    z(ClauseBody, W),
    Weight is ClauseProb * W.
