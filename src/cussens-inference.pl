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

aux(_, _, [], 0) :- !. % base case cut: prevents further backtracking and final output "false"
aux(CurrentGoal, RemainingGoal, [UnifClause|UnifSetTail], RoundedAkk) :-
    % aux recursion requires all subgoals to be as unbound as possible
    % free variable relations must be preserved, e.g. p(X), q(X) must become p(Y), q(Y)
    copy_term((CurrentGoal,RemainingGoal), (CurrentGoalFree,RemainingGoalFree)),

    nth0(0, UnifClause, ClauseProb),
    nth0(1, UnifClause, ClauseHead),
    nth0(2, UnifClause, ClauseBody),
    unifiable(ClauseHead, CurrentGoal, UnifBag),
    unify_helper(RemainingGoal, UnifBag), % how should unify_helper behave if variables in UnifBag have more unification options?
    z((ClauseBody, RemainingGoal), Weight),
    aux(CurrentGoalFree, RemainingGoalFree, UnifSetTail, Akknew),
    Akk is ClauseProb*Weight + Akknew,
    round_third(Akk, RoundedAkk).

% propagates bindings of CurrentGoal to RemainingGoal
% the List in the form [X=a, Y=b, ...]
unify_helper(_, []) :- !.
unify_helper(Term, [Var=Binding|BagTail]) :-
    findall(Term, Var=Binding, [Term]),
    unify_helper(Term, BagTail).

% rounding result to third decimal
round_third(Float, RoundedFloat) :-
    RoundedScaled is round(Float*1000),
    RoundedFloat is RoundedScaled/1000. 


% base case
z(true, 1) :- !. % base case cut: prevents further backtracking and final output "false"

% compound base case; simplifying conjunction
z((true, G), Weight) :- z(G, Weight), !. % base case cut: prevents further backtracking and final output "false"

% compound head
z((G1, G2), Weight) :-
    % if we share no variables, compute by decomposing
    % z(G1, Weight1),
    % z(G2, Weight2),
    % Weight is Weight1*Weight2,

    % assume we share some variables:
    G1 \= true, % mutual exclusivity of goals
    findall([Prob, G1, Body], clause((Prob :: G1), Body), UnifSet),
    aux(G1, G2, UnifSet, Weight).

% non-compound head
z(G, Weight) :-
    % mutual exclusivity of goals
    G \= (_, _),
    G \= true,

    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    aux(G, true, UnifSet, Weight).


% TESTS
0.6 :: p(a).
0.4 :: p(b).
0.3 :: q(a).
0.7 :: q(b).
