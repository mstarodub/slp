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

inference_marginal(Goal, BindingProbList) :- z(Goal, BindingProbList, 0).



% want p(f(b), P)
% -> p(f(X), [X=b], P).
p(G, ArgList, RoundedResult) :-
    copy_term(G, GFree),
    unify_helper(G, ArgList),
    z(G, Numerator, _),
    z(GFree, Denominator, _),
    Result is Numerator / Denominator,
    round_third(Result, RoundedResult).

% ---WIP---

% https://stackoverflow.com/questions/12638347/replace-atom-with-variable
% https://stackoverflow.com/questions/37260614/prolog-replacing-subterms/53145013#53145013
% https://stackoverflow.com/questions/22812691/prolog-replace-each-instance-of-a-constant-in-a-list-with-a-variable

as_vars_helper([], [], _).
as_vars_helper([I|Is], [V|Vs], Map) :-
    once(member(I/V, Map)),
    as_vars_helper(Is, Vs, Map).

as_vars(T, TV) :-
    T =.. TList,
    as_vars_helper(TList, TVList, _),
    TV =.. TVList.

replace(Term,Term,With,With) :-
    !.
replace(Term,Find,Replacement,Result) :-
    Term =.. [Functor|Args],
    replace_args(Args,Find,Replacement,ReplacedArgs),
    Result =.. [Functor|ReplacedArgs].

replace_args([],_,_,[]).
replace_args([Arg|Rest],Find,Replacement,[ReplacedArg|ReplacedRest]) :-
    replace(Arg,Find,Replacement,ReplacedArg),
    replace_args(Rest,Find,Replacement,ReplacedRest).

p(G, RoundedResult) :-
    %as_vars(G, GFree),
    replace(G, b, X, GFree),
    z(G, Numerator, 1),
    z(GFree, Denominator, 1),
    Result is Numerator / Denominator,
    round_third(Result, RoundedResult).

% --- WIP End ---

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

unifSet_rec(_, _, [], 0, _) :- !. % base case cut: prevents further backtracking and final output "false"
unifSet_rec(CurrentGoal, RemainingGoal, [UnifClause|UnifSetTail], Akk, Depth) :-
    % unifSet_rec recursion requires all subgoals to be as unbound as possible
    % free variable relations must be preserved, e.g. p(X), q(X) must become p(Y), q(Y)
    copy_term((CurrentGoal,RemainingGoal, UnifSetTail), (CurrentGoalFree,RemainingGoalFree, UnifSetTailFree)),

    nth0(0, UnifClause, ClauseProb),
    nth0(1, UnifClause, ClauseHead),
    nth0(2, UnifClause, ClauseBody),
    unifiable(ClauseHead, CurrentGoal, UnifBag),
    unify_helper(RemainingGoal, UnifBag), % how should unify_helper behave if variables in UnifBag have more unification options?
    DepthNew is Depth+1,
    z((ClauseBody, RemainingGoal), Weight, DepthNew),
    unifSet_rec(CurrentGoalFree, RemainingGoalFree, UnifSetTailFree, Akknew, Depth),
    ( Depth = 0
        ->  BindingProb is ClauseProb*Weight,
            round_third(BindingProb, BindingProbRound), % rounding probability occurring in output
            append(UnifBag, [BindingProbRound], AkkTemp),
            ( \+ integer(Akknew) -> append(AkkTemp, Akknew, Akk); Akk = AkkTemp ) % for all but the last element in unif set Akknew will be a list
        ;   Akk is ClauseProb*Weight + Akknew).

substitSet_rec(_, _, [], 0, _) :- !. % base case cut: prevents further backtracking and final output "false"
substitSet_rec(CurrentGoal, RemainingGoal, [Substitutions|PairedVarBindingsTail], Akk, Depth) :-
    % substitSet_rec recursion requires all subgoals to be as unbound as possible
    % PairedVarBindings must also remain unbound, e.g. old: [X=a], [X=b] becomes [Y=b] instead of [a=b]
    % free variable relations must be preserved, e.g. p(X), q(X) must become p(Y), q(Y)
    copy_term((CurrentGoal,RemainingGoal, PairedVarBindingsTail), (CurrentGoalFree,RemainingGoalFree, PairedVarBindingsTailFree)),

    unify_helper(CurrentGoal, Substitutions),
    unify_helper(RemainingGoal, Substitutions),
    z(CurrentGoal, Weight1, Depth),
    z(RemainingGoal, Weight2, Depth),
    substitSet_rec(CurrentGoalFree, RemainingGoalFree, PairedVarBindingsTailFree, Akknew, Depth),
    Akk is Weight1*Weight2 + Akknew.

% base case
z(true, 1, _).

% compound base cases; simplifying conjunction
% base case cuts: prevent further backtracking and final output "false"
z((G, true), Weight, Depth) :- z(G, Weight, Depth), !. % fires for G as body of a non-compound head
z((true, G), Weight, Depth) :- z(G, Weight, Depth), !.

% compound head
z((G1, G2), Weight, Depth) :-
    G1 \= true, % mutual exclusivity of goals

    % marginal inference --> standard not optimised z computation (with nonvar Depth)
    ( nonvar(Depth) 
    ->  findall([Prob, G1, Body], clause((Prob :: G1), Body), UnifSet),
        unifSet_rec(G1, G2, UnifSet, Weight, Depth)
    % success constraint inference --> optimised z computation (with var Depth)
    ;   % shared variable test
        sub_term_shared_variables(G1, (G1, G2), SharedVars),
        ( SharedVars = [] 
        % no shared variables --> decomposition
        ->  z(G1, Weight1, Depth),
            z(G2, Weight2, Depth),
            Weight is Weight1*Weight2
        % shared variables --> computation of splitting substitution set
        ;   % only ground terms make goals disjunct
            findall(SharedVars, (clause((_ :: G1), _), ground(SharedVars)), SubstitList),
            list_to_set(SubstitList, SubstitSet),

            map_singleton(unifiable, [SharedVars], SubstitSet, PairedVarBindings),
            substitSet_rec(G1, G2, PairedVarBindings, Weight, Depth)        
        )
    ).

% non-compound head
z(G, Weight, Depth) :-
    % mutual exclusivity of goals
    G \= (_, _),
    G \= true,

    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    unifSet_rec(G, true, UnifSet, Weight, Depth).


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
0.6 :: q(b).
0.1 :: q(c).

0.6 :: qq(X).
0.2 :: qq(a).
0.1 :: qq(b).

0.2 :: f(b).
0.6 :: f(X).
0.2 :: f(X) :- fail.

0.1 :: st(a, b).
0.9 :: st(X, b) :- fail.

0.7 :: s(X, b) :- q(X).
0.1 :: s(a, c).
0.2 :: s(b, b).
0.2 :: r(b, Z) :- p(Z).
0.8 :: r(a, b).

% current state: inference_marginal((s(X,Y), r(Y,Z)), Prob) results in Y=b, Prob = [b=b, _=X, 0.14, c=c, _=a, 0, b=b, _=b, 0.04] ; false.
