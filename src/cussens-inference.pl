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

aux(_, [], 0).

aux(RemainingGoal, [UnifClause|UnifSetTail], Akk) :-
    nth0(0, UnifClause, ClauseProb),
    nth0(2, UnifClause, ClauseBody),
    z((ClauseBody, RemainingGoal), W),
    aux(RemainingGoal, UnifSetTail, Akknew),
    Akk is Akknew + W*ClauseProb.

% base case
z(true, 1).

% compound head
z((G1, G2), Weight) :-
    % if we share no variables, compute by decomposing
    % z(G1, Weight1),
    % z(G2, Weight2),
    % Weight is Weight1*Weight2,

    % assume we share some variables:
    bagof([Prob, G1, Body], clause((Prob :: G1), Body), UnifSet),
    aux(G2, UnifSet, Weight).

% non-compound head
z(G, Weight) :-
    G \= (_, _),
    G \= true,
    bagof([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    aux(true, UnifSet, Weight).


% TESTS
0.6 :: p(a).
0.4 :: p(b).
0.3 :: q(a).
0.7 :: q(b).
