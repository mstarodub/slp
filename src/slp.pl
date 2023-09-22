:- op(1199,xfx,::).
:- discontiguous (::)/2.
:- dynamic (::)/2.

% meta-assumptions:
%   only conjunctions
%   normalized SLP (all clauses forming a predicate add up to 1)
%   pure SLP (no non-prob. clauses)


% transferring initial goal to list
goal_to_list((G1, G2), [G1|GoalTail]) :- goal_to_list(G2, GoalTail).
goal_to_list(G, [G]) :- G \= (_ , _).
    
inference_SC(G, Prob) :-
    G \= (_, _),
    clause(_::G, _),
    % checking if variables are still free (e.g. X=X), then VarList won't be empty
    writeln('xxx'),
    term_variables(G, VarList),
    writeln('<<'),
    ( VarList \= [] -> writeln('true,'); true),
    writeln('sdfsd'),
    p(G, Prob),
    writeln('aaaaaaaaaaaa').

% doesnt work for ground goals:
% inference_SC((q(a), p(a)), P).
inference_SC((G1,G2), Prob) :-
    gensym(reserved_newgoal, X),
    term_variables((G1, G2), VarList),
    writeln('aaa'),
    NewHead =.. [X|VarList],
    writeln('bbb'),
    assertz((1::NewHead :- (G1, G2))),
    writeln('ccc'),
    inference_SC(NewHead, Prob),
    writeln('ddd'),
    writeln(1::NewHead),
    ( VarList = [] ->
        retract(1::NewHead) ;
        % https://stackoverflow.com/a/55948034
        retract((1::NewHead :- (G1, G2)))
    ).


% assumptions:
%   G is the goal with only free variables
%   G is non-compound; TODO: assert user input as clause and retract later
%   ArgList contains the instantiated parameters for G

% TODO: maybe this is better than our approach for replacing ground atoms with variables
% https://stackoverflow.com/questions/37260614/prolog-replacing-subterms/53145013#53145013
% replacee | replacement | term | res
replace(Subterm0, Subterm, Term0, Term) :-
    (Term0 == Subterm0
        -> Term = Subterm
        ; var(Term0)
            -> Term = Term0
            ; Term0 =.. [F|Args0],
            maplist(replace(Subterm0,Subterm), Args0, Args),
            Term =.. [F|Args]
    ).

replace_grounds(Term, [], [], Term) :- !. % no backtracking for base cases
replace_grounds(Term, [GroundHead|GroundTail], [VarHead|VarTail], FreeTerm) :-
    replace(GroundHead, VarHead, Term, ReplacedTerm),
    replace_grounds(ReplacedTerm, GroundTail, VarTail, FreeTerm).

% idea behind collect_grounds:
% Same bindings will be replaced with same variables --> first collecting all bindings in list and only then replacing them 
% destructure input term iteratively, ultimately reaching every ground atom that needs to be replaced by a free variable
% based on current term structure three processing methods:
%   variables: no replacement required --> ignored
%   ground atoms: replacement required --> appending atom to GroundList so that it gets replaced later
%   predicates: no replacement required --> destructuring with =.. and calling recursion on its arguments
%
% for compound goals: both depth and breadth recursion needed
%   depth recursion: decomposing a single goal
%   breadth recursion: recursively processing all subgoals, starting at the left-most

% comment on cuts: prevent calling clauses further down when backtracking and therefore fail
% breadth and depth base case: all subgoals of input goal have been processed
collect_grounds([], [], []) :- !.
% breadth recursion starting at depth base case:
collect_grounds([], [RemainingHead|RemainingTail], GroundList) :-
    collect_grounds([RemainingHead], RemainingTail, GroundList),
    !.
% depth recursion: handling variables
collect_grounds([SubGoalHead|SubGoalTail], RemainingGoals, GroundList) :-
    % SubGoalHead is a variable --> ignored
    var(SubGoalHead),
    !,
    collect_grounds(SubGoalTail, RemainingGoals, GroundList).
% depth recursion: handling ground atoms
collect_grounds([SubGoalHead|SubGoalTail], RemainingGoals, [Functor|GroundTail]) :-
    % SubGoalHead no variable as they were dealt with in previous clause (+!)
    SubGoalHead =.. [Functor|Args],
    % SubGoalHead is atomic and ground
    Args = [],
    !,
    collect_grounds(SubGoalTail, RemainingGoals, GroundTail).
% depth recursion: handling non-ground predicates
collect_grounds([SubGoalHead|_], RemainingGoals, GroundList) :-
    % SubGoalHead no variable as they were dealt with in previous clause (+!)
    SubGoalHead =.. [_|Args],
    Args \= [],
    collect_grounds(Args, RemainingGoals, GroundList).


free_bindings([FirstSubGoal], RemainingGoals, FreeGoals) :-
    collect_grounds([FirstSubGoal], RemainingGoals, GroundList),
    % list_to_set to obtain same variable name for same binding
    list_to_set(GroundList, GroundSet),
    % for each ground atom in GroundSet get one fresh free variable
    length(GroundSet, GroundLength),
    length(VarSet, GroundLength),
    % for every ground atom in input goal: replace it with free variable, respecting same values
    replace_grounds([FirstSubGoal|RemainingGoals], GroundSet, VarSet, FreeGoals).


p(G, RoundedResult) :-
    goal_to_list(G, [GHead|GTail]),
    free_bindings([GHead], GTail, GFreeList),
    goal_to_list(GFree, GFreeList),
    z(G, Numerator),
    z(GFree, Denominator),
    Result is Numerator / Denominator,
    round_third(Result, RoundedResult).

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


unifSet_rec(_, _, [], 0) :- !. % base case cut: prevents further backtracking
unifSet_rec(CurrentGoal, RemainingGoal, [UnifClause|UnifSetTail], Akk) :-
    % unifSet_rec recursion requires all subgoals to be as unbound as possible
    % free variable relations must be preserved, e.g. p(X), q(X) must become p(Y), q(Y)
    % -> copy everything but the current C (UnifClause)
    copy_term((CurrentGoal,RemainingGoal, UnifSetTail), (CurrentGoalFree,RemainingGoalFree, UnifSetTailFree)),

    nth0(0, UnifClause, ClauseProb),
    nth0(1, UnifClause, ClauseHead),
    nth0(2, UnifClause, ClauseBody),
    % UnifBag then has the instantiation of variables for the current C (UnifClause)
    % e.g. [X=Y, Y=b]
    unifiable(CurrentGoal, ClauseHead, UnifBag),
    unify_helper(RemainingGoal, UnifBag), % TODO: how should unify_helper behave if variables in UnifBag have more unification options?
    z((ClauseBody, RemainingGoal), Weight),
    unifSet_rec(CurrentGoalFree, RemainingGoalFree, UnifSetTailFree, Akknew),
    Akk is ClauseProb*Weight + Akknew.

substitSet_rec(_, _, [], 0) :- !. % base case cut: prevents further backtracking
substitSet_rec(CurrentGoal, RemainingGoal, [Substitutions|PairedVarBindingsTail], Akk) :-
    % substitSet_rec recursion requires all subgoals to be as unbound as possible
    % PairedVarBindings must also remain unbound, e.g. old: [X=a], [X=b] becomes [Y=b] instead of [a=b]
    % free variable relations must be preserved, e.g. p(X), q(X) must become p(Y), q(Y)
    copy_term((CurrentGoal,RemainingGoal, PairedVarBindingsTail), (CurrentGoalFree,RemainingGoalFree, PairedVarBindingsTailFree)),

    % here, the third argument of substitSet_rec are suitable substitutions, as opposed to clauses in unifSet_rec
    unify_helper(CurrentGoal, Substitutions),
    unify_helper(RemainingGoal, Substitutions),
    z(CurrentGoal, Weight1),
    z(RemainingGoal, Weight2),
    % sum over all possible splitting substitutions
    substitSet_rec(CurrentGoalFree, RemainingGoalFree, PairedVarBindingsTailFree, Akknew),
    Akk is Weight1*Weight2 + Akknew.

% base case
z(true, 1) :- !. % preventing backtracking to clauses further down

% compound base cases; simplifying conjunction
% preventing backtracking to clauses further down
z((G, true), Weight) :- z(G, Weight), !. % fires for G as body of a non-compound head
z((true, G), Weight) :- z(G, Weight), !.

% compound head
z((G1, G2), Weight) :-
    G1 \= true, % mutual exclusivity of goals
    %optimised z computation (with var Depth)
    % shared variable test
    sub_term_shared_variables(G1, (G1, G2), SharedVars),
    ( SharedVars = [] 
    % no shared variables --> decomposition
    ->  z(G1, Weight1),
        z(G2, Weight2),
        Weight is Weight1*Weight2
    % shared variables --> computation of splitting substitution set
    ;   % only ground terms make goals disjunct (e.g. we don't want Y=Y)
        % collect all possible values of SharedVars in matching clause heads
        % example: (G1, G2) === (s(X,Y), r(Y,Z))
        % ---> SharedVars = [Y]
        % ---> SubstitList = [[b],[c]]; in each entry list we have the bindings for all shared variables
        findall(SharedVars, (clause((_ :: G1), _), ground(SharedVars)), SubstitList),
        % SubstitSet is Theta, the set of splitting substitutions. in the (s(X,Y), r(Y,Z)) case, a substitution of Y= b or Y= c makes the Variables in G1, G2 disjoint
        list_to_set(SubstitList, SubstitSet),
        % put all possibilities for binding the shared variables into PairedVarBindings
        maplist(unifiable(SharedVars), SubstitSet, PairedVarBindings),
        substitSet_rec(G1, G2, PairedVarBindings, Weight)        
    ),
    !. % preventing backtracking to clauses further down

% non-compound head
z(G, Weight) :-
    % mutual exclusivity of goals
    G \= (_, _),
    G \= true,

    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    unifSet_rec(G, true, UnifSet, Weight).


% loglinear: ähnlich zum v1, nur ohne inference call
% unification-constrained: in der effizienz zwischen loglinear und backtrackable
% backtrackable: hier implementieren
% importance: wahrscheinlich ein improvement zum improved loglinear

% TODO: what is the expected result for sampling a goal that doesn't exist?
% unconstrained (loglinear) sampling
sample_UC(Head) :-
    findall([Prob::Head, Body], clause((Prob :: Head), Body), ClauseBag),
    % probabilisticly choosing a clause in ClauseBag --> binding Head and Body
    random_clause(Head, Body, ClauseBag),
    % we just sample once for now, i.e. sticking to the choice of random_clause
    !,
    sample_UC(Body).

% compound body
sample_UC((G1, G2)) :-
    !,
    sample_UC(G1),
    sample_UC(G2).

% base case: true or fail. returns "false" when encountering fail
sample_UC(G) :-
    % writeln(G),
    !,
    G. % executes "fail" when encountering failure, making sure we don't get spurious bindings through backtracking.

random_clause(Head, Body, ClauseBag) :-
    transform_probabilities(ClauseBag, ShiftedClauseBag),
    % generating random float between 0 and 1
    Rand is random_float,
    choose(ShiftedClauseBag, Rand, [Head, Body]).

choose([], _, false).
choose([[ShiftedProb::ShiftedHead, Body]|Tail], SampleProb, Sample) :-
    ( ShiftedProb >= SampleProb
    -> Sample = [ShiftedHead, Body]
    ; choose(Tail, SampleProb, Sample)).

% shift the probabilities so we can sample from a uniform distribution
% implicit failure/base case:
% probability of failure === 1 - sum of probabilities for successful cases
transform_probabilities([[P::H, B]], [[P::H, B], Failure]) :-
    % need a head with the same functor and arity, but all free variables as arguments
    functor(H, FailureName, FailureArity),
    length(K, FailureArity),
    FailureH =.. [FailureName|K],
    Failure = [1-P::FailureH, fail].
transform_probabilities([[P1::H1, B1],[P2::H2, B2]|Tail], L) :-
    TransfromedProb is P1 + P2,
    transform_probabilities([[TransfromedProb::H2, B2]|Tail], TempL),
    L = [[P1::H1, B1]|TempL].

%-----

sample_SC(Head) :-
    findall([Prob::Head, Body], clause((Prob :: Head), Body), ClauseBag),
    % probabilisticly choosing a clause in ClauseBag --> binding Head and Body
    random_clause(Head, Body, ClauseBag),
    % Head + Body ground; bind Prob
    clause((Prob :: Head), Body),
    !,
    ( sample_SC(Body)
    -> !
    % if we fail in the above, preprocess the tree, rewriting probabilities
    ;   writeln([Prob::Head, Body]),
        % sum of clause probabilities with current Head without the failed clause Prob::Head :- Body
        % recursively all failing clauses get removed --> sum decreasing continuously
        sum_remaining(ClauseBag, Prob, 0, Denominator),
        writeln(Denominator),
        % rewrite probabilities of remaining clauses proportional to the successful branches
        change_prob(ClauseBag, [Prob::Head, Body], Denominator)
    ).

% compound body
sample_SC((G1, G2)) :-
    sample_SC(G1),
    sample_SC(G2).

sample_SC(G) :-
    G.

change_prob([], [_::_, _], _).
% failed clause Prob::Head :- Body -> 0 probability
change_prob([[Prob::Head, Body]|BagTail], [Prob::Head, Body], Denominator) :-
    writeln([Prob::Head, Body]),
    retract(Prob::Head :- Body), % TODO: will it work for ground clauses, too?
    assertz(0::Head :- Body),
    change_prob(BagTail, [Prob::Head, Body], Denominator).
% otherwise -> adjust
% TODO: why no backtracking of failed case to this clause?
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

% p(X) :- q1(X), q2(X).
% q1(a).
% q2(X) :- fail.

% TESTS

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

0.6 :: qq(X).
0.2 :: qq(a).
0.1 :: qq(b).

0.5 :: compound(X) :- p(X), q(X).

0.2 :: f(b).
0.6 :: f(X).
0.2 :: f(X) :- fail.

% XXX: p(cmp1(b), P). -> zero divisor
0.5 :: cmp1(X, Y) :- qq(X), qq(Y).

0.5 :: cmp(X) :- p(X), q(X).

0.1 :: st(a, b).
0.9 :: st(X, b) :- fail.

0.7 :: s(X, b) :- q(X).
0.1 :: s(a, c).
0.1 :: s(b, b).
0.05 :: s(b, a).
0.2 :: r(b, Z) :- p(Z).
0.7 :: r(a, b).
