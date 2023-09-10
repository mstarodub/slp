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


aux(_, _, [], 0).
aux(CurrentGoal, RemainingGoal, [UnifClause|UnifSetTail], Akk) :-
    nth0(0, UnifClause, ClauseProb),
    nth0(1, UnifClause, ClauseHead),
    nth0(2, UnifClause, ClauseBody),
    unifiable(ClauseHead, CurrentGoal, UnifBag),
    unify_helper(RemainingGoal, UnifBag),
    z((ClauseBody, RemainingGoal), W),
    aux(CurrentGoal, RemainingGoal, UnifSetTail, Akknew),
    Akk is Akknew + W*ClauseProb.



% the List in the form [X=a, Y=b, ...]
unify_helper(_, []).
unify_helper(Term, [L=R|BT]) :-
    findall(Term, L=R, [Term]),
    unify_helper(Term, BT).


% base case
z(true, 1).

% compound base case
z((true, G), Weight) :- z(G, Weight).

% compound head
z((G1, G2), Weight) :-
    % if we share no variables, compute by decomposing
    % z(G1, Weight1),
    % z(G2, Weight2),
    % Weight is Weight1*Weight2,

    % assume we share some variables:
    findall([Prob, G1, Body], clause((Prob :: G1), Body), UnifSet),
    aux(G1, G2, UnifSet, Weight).

% non-compound head
z(G, Weight) :-
    G \= (_, _),
    G \= true,
    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    aux(G, true, UnifSet, Weight).


% TESTS
0.6 :: p(a).
0.4 :: p(b).
0.3 :: q(a).
0.7 :: q(b).
