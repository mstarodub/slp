:- op(1199,xfx,::).
:- discontiguous (::)/2.

% meta-assumptions:
%   only conjunctions
%   normalized SLP (all clauses forming a predicate add up to 1)
%   pure SLP (no non-prob. clauses)

% assumptions:
%   G is the goal with only free variables
%   G is non-compound; TODO: assert user input as clause and retract later
%   ArgList contains the instantiated parameters for G
p(G, ArgList, RoundedResult) :-
    functor(G, Functor, Arity),
    GInstantiated =.. [Functor|ArgList],
    z(GInstantiated, Numerator),
    z(G, Denominator),
    Result is Numerator / Denominator,
    round_third(Result, RoundedResult).

% reimplementation of maplist for singleton list [Singleton] applied to arbitrarily long list [Elem|Tail]
map_singleton(_, _, [], []) :- !.
map_singleton(Goal, [Singleton], [Elem|Tail], [ResElem|ResTail]) :-
    call(Goal, Singleton, Elem, ResElem),
    map_singleton(Goal, [Singleton], Tail, ResTail).


% propagates bindings of CurrentGoal to RemainingGoal
% the List in the form [X=a, Y=b, ...]
% https://stackoverflow.com/a/64722773
unify_helper(_, []) :- !.
unify_helper(Term, [Var=Binding|BagTail]) :-
    findall(Term, Var=Binding, [Term]),
    unify_helper(Term, BagTail).

% rounding result to third decimal
round_third(Float, RoundedFloat) :-
    RoundedScaled is round(Float*1000),
    RoundedFloat is RoundedScaled/1000. 

unifSet_rec(_, _, [], 0) :- !. % base case cut: prevents further backtracking and final output "false"
unifSet_rec(CurrentGoal, RemainingGoal, [UnifClause|UnifSetTail], Akk) :-
    % unifSet_rec recursion requires all subgoals to be as unbound as possible
    % free variable relations must be preserved, e.g. p(X), q(X) must become p(Y), q(Y)
    copy_term((CurrentGoal,RemainingGoal, UnifSetTail), (CurrentGoalFree,RemainingGoalFree, UnifSetTailFree)),

    nth0(0, UnifClause, ClauseProb),
    nth0(1, UnifClause, ClauseHead),
    nth0(2, UnifClause, ClauseBody),
    unifiable(ClauseHead, CurrentGoal, UnifBag),
    unify_helper(RemainingGoal, UnifBag), % how should unify_helper behave if variables in UnifBag have more unification options?
    z((ClauseBody, RemainingGoal), Weight),
    unifSet_rec(CurrentGoalFree, RemainingGoalFree, UnifSetTailFree, Akknew),
    Akk is ClauseProb*Weight + Akknew.

substitSet_rec(_, _, [], 0) :- !. % base case cut: prevents further backtracking and final output "false"
substitSet_rec(CurrentGoal, RemainingGoal, [Substitutions|PairedVarBindingsTail], Akk) :-
    % substitSet_rec recursion requires all subgoals to be as unbound as possible
    % PairedVarBindings must also remain unbound, e.g. old: [X=a], [X=b] becomes [Y=b] instead of [a=b]
    % free variable relations must be preserved, e.g. p(X), q(X) must become p(Y), q(Y)
    copy_term((CurrentGoal,RemainingGoal, PairedVarBindingsTail), (CurrentGoalFree,RemainingGoalFree, PairedVarBindingsTailFree)),

    unify_helper(CurrentGoal, Substitutions),
    unify_helper(RemainingGoal, Substitutions),
    z(CurrentGoal, Weight1),
    z(RemainingGoal, Weight2),
    substitSet_rec(CurrentGoalFree, RemainingGoalFree, PairedVarBindingsTailFree, Akknew),
    Akk is Weight1*Weight2 + Akknew.

% base case
z(true, 1).

% compound base cases; simplifying conjunction
% base case cuts: prevent further backtracking and final output "false"
z((G, true), Weight) :- z(G, Weight), !. % fires for G as body of a non-compound head
z((true, G), Weight) :- z(G, Weight), !.

% compound head
z((G1, G2), Weight) :-
    G1 \= true, % mutual exclusivity of goals

    % shared variable test
    sub_term_shared_variables(G1, (G1, G2), SharedVars),
    ( SharedVars = [] 
    % no shared variables --> decomposition
    ->  z(G1, Weight1),
        z(G2, Weight2),
        Weight is Weight1*Weight2
    % shared variables --> computation of splitting substitution set
    ;   % only ground terms make goals disjunct
        findall(SharedVars, (clause((_ :: G1), _), ground(SharedVars)), SubstitList),
        list_to_set(SubstitList, SubstitSet),
        map_singleton(unifiable, [SharedVars], SubstitSet, PairedVarBindings),
        substitSet_rec(G1, G2, PairedVarBindings, Weight)        
    ).

% non-compound head
z(G, Weight) :-
    % mutual exclusivity of goals
    G \= (_, _),
    G \= true,

    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    unifSet_rec(G, true, UnifSet, Weight).


% compound body
sample((G1, G2)) :-
    !,
    sample(G1),
    sample(G2).

% Should this case really be a subclause of sample or does it rather belong to the (toplevel) metainterpreter
sample(G) :-
    \+clause((Prob :: G), _),
    !,
    G.

sample(Head) :-
    findall([Prob, Head, Body], clause((Prob :: Head), Body), Bag),
    random_clause(Head, Body, Bag),
    !,
    sample(Body).

% probabilistic clause selector
random_clause(Head, Body, Bag) :-
    Rand is random_float,
    choose(Bag, Head, Body, 0, Rand, Sum).
choose([], _, _, _, _, 0).
choose([[Prob, Head, Body]|Tail], Head1, Body1, Akk, Rand, Rest) :-
    Akknew is Akk + Prob,
    choose(Tail, Head1, Body1, Akknew, Rand, Rest1),
    Rest is Rest1 + Prob,
    ((var(Body1),
        Prob1 is Akk/(Akk+Rest), Rand >= Prob1, Head1 = Head, Body1 = Body);
    true).

% TESTS
% want: z((q(X), p(X)), W) === 0.46
0.6 :: p(a).
0.4 :: p(b).
0.3 :: q(a).
0.7 :: q(b).

0.7 :: s(X, b) :- q(X).
0.1 :: s(a, c).
0.2 :: s(b, b).
0.2 :: r(b, Z) :- p(Z).
0.8 :: r(a, b).
