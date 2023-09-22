:- op(1199,xfx,::).
:- discontiguous (::)/2.
:- dynamic (::)/2.

% assumptions:
%   only conjunctions
%   normalized SLP (all clauses forming a predicate add up to 1)
%   pure SLP (no non-prob. clauses)

% used for propagating bindings of CurrentGoal to RemainingGoal
% takes List in the form [X=a, Y=b, ...]
% TODO: should be this ideally, but issues in e.g. unifSet_rec
% unify_list(_, []) :- !.
% unify_list(Term, [Var=Binding|BagTail]) :-
%     Var=Binding,
%     unify_list(Term, BagTail).
% https://stackoverflow.com/a/64722773
unify_list(_, []) :- !.
unify_list(Term, [Var=Binding|BagTail]) :-
    findall(Term, Var=Binding, [Term]),
    unify_list(Term, BagTail).

% other predicates analyzing and replacing (sub)terms operate on lists
% rewrites conjuncts to elements
goal_to_list((G1, G2), [G1|GoalTail]) :- goal_to_list(G2, GoalTail).
goal_to_list(G, [G]) :- G \= (_ , _).

% collects all bindings / ground atoms
collect_grounds(Term, GroundList) :-
    (   nonvar(Term)
    ->  Term =.. [X|Args],
        (   Args = []
        ->  GroundList = [X]
        ;   % concatmap
            maplist(collect_grounds, Args, Nested),
            flatten(Nested, GroundList)
        )
    ;   GroundList = []
    ).

% used for replacing ground atoms with variables
replace(Replacee, Replacement, Term, Res) :-
    (   Term == Replacee
    % base case - ground atom
    ->  Res = Replacement
    ;   (   var(Term)
        % preserve variable
        ->  Res = Term
        % functor case - separate the arguments and recur
        ;   Term =.. [F|Args0],
            maplist(replace(Replacee, Replacement), Args0, Args),
            % reassemble
            Res =.. [F|Args]
        )
    ).

replace_grounds(Term, [], [], Term).
replace_grounds(Term, [GroundHead|GroundTail], [VarHead|VarTail], FreeTerm) :-
    replace(GroundHead, VarHead, Term, ReplacedTerm),
    % replaced (Res) becomes new replacee
    replace_grounds(ReplacedTerm, GroundTail, VarTail, FreeTerm).

% need to traverse the goal twice:
% first - collect all grounds and de-duplicate
% then - replace them with fresh variables
free_up_bindings(Goal, FreeGoals) :-
    collect_grounds(Goal, GroundList),
    % list_to_set to obtain same variable name for same binding
    list_to_set(GroundList, GroundSet),
    % for each ground atom in GroundSet get one fresh free variable
    length(GroundSet, GroundLength),
    length(VarSet, GroundLength),
    % for every distinct ground atom in input goal: replace with free variable
    replace_grounds(Goal, GroundSet, VarSet, FreeGoals).

% forces backtracking over possible bindings for free variables in goal
bind_goal([]).
bind_goal([GoalHead|GoalTail]) :-
    clause((_::GoalHead), _),
    bind_goal(GoalTail).

inference_marginal(Goal, ProbRounded) :-
    goal_to_list(Goal, GoalList),
    bind_goal(GoalList),
    goal_to_list(GoalBound, GoalList),
    term_variables(GoalBound, VarList),
    ( VarList \= [] -> writeln('true,'); true),
    z(GoalBound, Prob),
    round_third(Prob, ProbRounded).

inference_SC(Goal, ProbRounded) :-
    goal_to_list(Goal, GoalList),
    bind_goal(GoalList),
    goal_to_list(GoalBound, GoalList),
    term_variables(GoalBound, VarList),
    ( VarList \= [] -> writeln('true,'); true),
    p(GoalBound, Prob),
    round_third(Prob, ProbRounded).

p(G, RoundedResult) :-
    goal_to_list(G, GList),
    free_up_bindings(GList, GFreeList),
    goal_to_list(GFree, GFreeList),
    z(G, Numerator),
    z(GFree, Denominator),
    Result is Numerator / Denominator,
    round_third(Result, RoundedResult).

% Prob's differ for t(X, X) and t(X,Y) when calling t(a,a) if clause t(a, g) exists
% --> need a way to pass goal + instantiations explicitly: p(t(X,Y), [X=a, Y=a], P).
p(G, ArgList, RoundedResult) :-
    copy_term(G, GFree),
    unify_list(G, ArgList),
    z(G, Numerator),
    z(GFree, Denominator),
    Result is Numerator / Denominator,
    round_third(Result, RoundedResult).

% rounds to third decimal
round_third(Float, RoundedFloat) :-
    RoundedScaled is round(Float*1000),
    RoundedFloat is RoundedScaled/1000.

% unifSet_rec and substitSet_rec recursion require all subgoals
% to be as unbound as possible. TODO: which subgoals?
% free variable identifications must be preserved, e.g. p(X), q(X) --> p(Y), q(Y)

unifSet_rec(_, _, [], 0).
unifSet_rec(CurrentGoal, RemainingGoal, [[CProb, CHead, CBody]|UnifSetTail], Akk) :-
    % copy everything but the current C
    copy_term((CurrentGoal,RemainingGoal, UnifSetTail), (CurrentGoalFree,RemainingGoalFree, UnifSetTailFree)),
    % instantiation of variables for the current C, e.g. [X=Y, Y=b]
    unifiable(CurrentGoal, CHead, UnifBag),
    % TODO: how should we unify if variables in UnifBag have more unification options?
    unify_list(RemainingGoal, UnifBag),
    z((CBody, RemainingGoal), Weight),
    unifSet_rec(CurrentGoalFree, RemainingGoalFree, UnifSetTailFree, Akknew),
    Akk is CProb*Weight + Akknew.

% third argument are suitable substitutions, as opposed to clauses in unifSet_rec
substitSet_rec(_, _, [], 0).
substitSet_rec(CurrentGoal, RemainingGoal, [Substitutions|PairedVarBindingsTail], Akk) :-
    % PairedVarBindings must also remain unbound
    % e.g. old: [X=a], [X=b] becomes [Y=b] instead of [a=b]
    copy_term((CurrentGoal,RemainingGoal, PairedVarBindingsTail), (CurrentGoalFree,RemainingGoalFree, PairedVarBindingsTailFree)),
    unify_list(CurrentGoal, Substitutions),
    unify_list(RemainingGoal, Substitutions),
    z(CurrentGoal, Weight1),
    z(RemainingGoal, Weight2),
    % sum over all possible splitting substitutions
    substitSet_rec(CurrentGoalFree, RemainingGoalFree, PairedVarBindingsTailFree, Akknew),
    Akk is Weight1*Weight2 + Akknew.

% base cases, prevent backtracking to other clauses
z(true, 1) :- !.
% fires when e.g. G is body of non-compound head
z((G, true), Weight) :- z(G, Weight), !.
z((true, G), Weight) :- z(G, Weight), !.

z((G1, G2), Weight) :-
    % mutual exclusivity of goals
    G1 \= true,
    sub_term_shared_variables(G1, (G1, G2), SharedVars),
    (   SharedVars = []
    % no shared variables --> decomposition
    ->  z(G1, Weight1),
        z(G2, Weight2),
        Weight is Weight1*Weight2
    % shared variables --> computation of Theta, the set of splitting substitutions
    ;   % only ground terms make goals disjunct (e.g. we don't want Y=Y)
        % collect all possible values of SharedVars in matching clause heads
        % example: (G1, G2) = (s(X,Y), r(Y,Z))
        % --> SharedVars = [Y]
        % --> SubstitList = [[b],[c]]
        %   (in each entry list we have the bindings for all shared variables)
        findall(SharedVars, (clause((_ :: G1), _), ground(SharedVars)), SubstitList),
        % SubstitSet is now Theta
        % in the case of (s(X,Y), r(Y,Z)), a substitution of Y=b or Y=c makes Vars in G1, G2 disjoint
        list_to_set(SubstitList, SubstitSet),
        % PairedVarBindings === all possibilities for binding the shared variables
        maplist(unifiable(SharedVars), SubstitSet, PairedVarBindings),
        substitSet_rec(G1, G2, PairedVarBindings, Weight)
    ).

% TODO: give example when this fires
z(G, Weight) :-
    % mutual exclusivity of goals
    G \= (_, _),
    G \= true,
    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    unifSet_rec(G, true, UnifSet, Weight).

% unconstrained loglinear sampling
sample_UC(Head) :-
    findall([Prob::Head, Body], clause((Prob :: Head), Body), ClauseBag),
    % probabilistic clause selector binds Head and Body
    random_clause(Head, Body, ClauseBag),
    % sample once - stick to choice of random_clause
    !,
    sample_UC(Body).

sample_UC((G1, G2)) :-
    !,
    sample_UC(G1),
    sample_UC(G2).

% base case: true or fail.
% executes "fail" when encountering failure, making sure
% we don't get spurious bindings through backtracking.
sample_UC(G) :-
    !,
    G.

random_clause(Head, Body, ClauseBag) :-
    transform_probabilities(ClauseBag, ShiftedClauseBag),
    % get random float between 0 and 1
    Rand is random_float,
    choose(ShiftedClauseBag, Rand, [Head, Body]).

choose([], _, false).
choose([[ShiftedProb::ShiftedHead, Body]|Tail], SampleProb, Sample) :-
    (   ShiftedProb >= SampleProb
    ->  Sample = [ShiftedHead, Body]
    ;   choose(Tail, SampleProb, Sample)
    ).

% shift probabilities so we can sample from uniform distribution
% implicit failure/base case:
% probability of failure === 1 - sum of probabilities for successful cases
transform_probabilities([[P::H, B]], [[P::H, B], Failure]) :-
    % need head with same functor and arity, but all free variables as args
    functor(H, FailureName, FailureArity),
    length(K, FailureArity),
    FailureH =.. [FailureName|K],
    Failure = [1-P::FailureH, fail].
transform_probabilities([[P1::H1, B1],[P2::H2, B2]|Tail], L) :-
    TransfromedProb is P1 + P2,
    transform_probabilities([[TransfromedProb::H2, B2]|Tail], TempL),
    L = [[P1::H1, B1]|TempL].

% success-constrained backtrackable sampling
sample_SC(Head) :-
    findall([Prob::Head, Body], clause((Prob :: Head), Body), ClauseBag),
    random_clause(Head, Body, ClauseBag),
    % Head + Body ground; bind Prob
    clause((Prob :: Head), Body),
    !,
    (   sample_SC(Body)
    ->  !
    % if we fail in the above, preprocess the tree, rewriting probabilities
    ;   writeln([Prob::Head, Body]),
        % probabilities of current Head without the failed clause Prob::Head :- Body
        sum_remaining(ClauseBag, Prob, 0, Denominator),
        writeln(Denominator),
        % rewrite probabilities of remaining clauses proportional to remaining branches
        change_prob(ClauseBag, [Prob::Head, Body], Denominator)
    ).

sample_SC((G1, G2)) :-
    sample_SC(G1),
    sample_SC(G2).

sample_SC(G) :-
    G.

change_prob([], [_::_, _], _).
% failed clause Prob::Head :- Body --> 0 probability
change_prob([[Prob::Head, Body]|BagTail], [Prob::Head, Body], Denominator) :-
    writeln([Prob::Head, Body]),
    retract(Prob::Head :- Body),
    % assertz(0::Head :- Body),
    change_prob(BagTail, [Prob::Head, Body], Denominator).
% otherwise --> adjust
% no backtracking of failed case to this because clause with that Prob was retracted
change_prob([[P::H, B]|BagTail], [Prob::Head, Body], Denominator) :-
    writeln(BagTail),
    retract(P::H :- B),
    round_third(P/Denominator, Rounded),
    assertz(Rounded::H :- B),
    change_prob(BagTail, [Prob::Head, Body], Denominator).

sum_remaining([], FailedP, Akk, Denominator) :-
    Denominator is Akk - FailedP.
sum_remaining([[P::_, _]|BagTail], FailedP, Akk, Denominator) :-
    Akknew is Akk + P,
    sum_remaining(BagTail, FailedP, Akknew, Denominator).


% TESTS
:- style_check(-singleton).

% sample_SC tree rewriting test:
% have:
% ├───½
% │   ├───⅓
% │   │   ├───½─⊸ fail             -> ¹⁄₁₂
% │   │   └───½─⊸                  -> ¹⁄₁₂
% │   ├───⅓─⊸ fail                -> ⅙
% │   └───⅓─⊸                     -> ⅙
% └───½─⊸                          -> ½
% want:
% ├───½
% │   ├───½
% │   │   ├───0─⊸ fail             -> 0
% │   │   └───1─⊸                  -> ¼
% │   ├───0─⊸ fail                 -> 0
% │   └───½─⊸                      -> ¼
% └───½─⊸                          -> ½
1/2 :: ssct0.
1/2 :: ssct0 :- ssct1.
1/3 :: ssct1 :- fail.
1/3 :: ssct1.
1/3 :: ssct1 :- ssct2.
1/2 :: ssct2 :- fail.
1/2 :: ssct2.
% after hitting fail twice:
% 1/2 :: ssct0.
% 1/2 :: ssct0 :- ssct1.
% 0 :: ssct1 :- fail.
% 1/3/0.6666666666666667 (===0.49) :: ssct1.
% 1/3/0.6666666666666667 (===0.49) :: ssct1 :- ssct2.
% 0 :: ssct2 :- fail.
% 1/2/0.5 (===1) :: ssct2.


% want: z((q(X), p(X)), W) === 0.46
0.6 :: p(a).
0.4 :: p(b).
0.3 :: q(a).
0.6 :: q(b).
0.1 :: q(c).

0.6 :: dq(X).
0.2 :: dq(a).

5/10 :: dqq(a).
3/10 :: dqq(b).

0.5 :: compound(X) :- p(X), q(X).

0.2 :: f(b).
0.6 :: f(X).
0.2 :: f(X) :- fail.

0.5 :: cmp1(X, Y) :- dq(X), dq(Y).

0.5 :: cmp(X) :- p(X), q(X).

0.1 :: st(a, b).
0.9 :: st(X, b) :- fail.

0.7 :: s(X, b) :- q(X).
0.1 :: s(a, c).
0.1 :: s(b, b).
0.05 :: s(b, a).
0.2 :: r(b, Z) :- p(Z).
0.7 :: r(a, b).
