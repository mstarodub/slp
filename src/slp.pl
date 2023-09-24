:- op(1199,xfx,::).
:- discontiguous (::)/2.
:- dynamic (::)/2.

% assumptions:
%   only conjunctions
%   no nested functors [st(dqq(X))]
%   normalized SLP (all clauses forming a predicate add up to 1)
%   pure SLP (no non-prob. clauses)

% used for propagating bindings of CurrentGoal to RemainingGoal
% takes List in the form [X=a, Y=b, ...]
unify_list(_, []) :- !.
unify_list(Term, [Var=Binding|BagTail]) :-
    Var=Binding,
    unify_list(Term, BagTail).

% based on UnifyList generate new subsitutions
% e.g. SubstitUnground = [X,b], Unification = [X=a], SubstitCopy = [a,b]
generate_substits(SubstitUnground, Unification, SubstitCopy) :-
    copy_term((SubstitUnground, Unification), (SubstitCopy, UnifCopy)),
    unify_list(SubstitCopy, UnifCopy).

% other predicates analyzing and replacing (sub)terms operate on lists
% therefore: rewrite conjuncts to elements
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

% replacing ground atoms with variables
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
    % no duplicates to obtain same variable name for same binding
    list_to_set(GroundList, GroundSet),
    % for each ground atom in GroundSet get one fresh free variable
    length(GroundSet, GroundLength),
    length(VarSet, GroundLength),
    % for every distinct ground atom in input goal: replace with free variable
    replace_grounds(Goal, GroundSet, VarSet, FreeGoals).

% deep backtracking === bindings searched for throughout entire clause depth, recursively calling clause bodies if necessary
% shallow === bindings are only searched for on the "head level" of the current goal

% deep backtracking over possible bindings for free variables in goal
bind_goal([]).
bind_goal([GoalHead|GoalTail]) :-
    clause((_::GoalHead), Body),
    % recur into body
    term_variables(GoalHead, VarList),
    (   VarList \= []
    ->  goal_to_list(Body, BodyList),
        bind_goal(BodyList)
    ;   true
    ),
    bind_goal(GoalTail).

ground_substits([], _, []).
ground_substits([[SharedVars, SubstitArgs]|SubstitsArgsTail], [Functor|_], AllSubstits) :-
    % grounding remaining free SharedVars based on bindings the body of the head GoalSubstit can take
    % e.g. GoalSubstit = s(X,b)
    GoalSubstit =.. [Functor|SubstitArgs],
    % recursively finding all possible bindings for free SharedVars
    % e.g. BindingBag = [[a,b], [b,b], [c,b], [b,b]] for SharedVars X, Y with Y=b, i.e. SharedVars = [X,b]
    findall(SharedVars, bind_goal([GoalSubstit]), BindingBag),
    % pairing variables with corresponding binding
    % e.g. PairedVarBindings = [[X=a], [X=b], [X=c], [X=b]]
    maplist(unifiable(SharedVars), BindingBag, PairedVarBindings),
    % based on PairedVarBindings generate new subsitution lists
    % e.g. GeneratedSubstits = [[a,b], [b,b], [c,b], [b,b]]
    % note: BindingBag and Generated Substits differ if SubstitArgs contains variables or bindings of variables not shared
    maplist(generate_substits(SubstitArgs), PairedVarBindings, GeneratedSubstits),
    % processing further free or partially ground SubstitArgs
    ground_substits(SubstitsArgsTail, [Functor|_], MoreSubstits),
    append(GeneratedSubstits, MoreSubstits, AllSubstits).

% optimised inference using goal splitting:

inference_marginal(Goal, ProbRounded) :-
    goal_to_list(Goal, GoalList),
    bind_goal(GoalList),
    goal_to_list(GoalBound, GoalList),
    % for shallow backtracking: printing true for variable unifications X=X
    %term_variables(GoalBound, VarList),
    %( VarList \= [] -> writeln('true,'); true),
    z_copy(GoalBound, Prob),
    round_third(Prob, ProbRounded).

% example call: Goal = (s(a,b),r(b,X)), inference_SC(Goal, Prob).
inference_SC(Goal, ProbRounded) :-
    goal_to_list(Goal, GoalList),
    bind_goal(GoalList),
    goal_to_list(GoalBound, GoalList),
    % for shallow backtracking: printing true for variable unifications X=X
    %term_variables(GoalBound, VarList),
    %( VarList \= [] -> writeln('true,'); true),
    p(GoalBound, Prob),
    round_third(Prob, ProbRounded).

% example call: Goal = (s(a,b),r(b,X)), GoalFree = (s(X,Y),r(Y,X)), inference_SC(Goal, Prob).
inference_SC(Goal, GoalFree, ProbRounded) :-
    % preventing GoalFree from getting grounded by backtracking
    copy_term(GoalFree, GoalFreeCopy),
    goal_to_list(Goal, GoalList),
    bind_goal(GoalList),
    goal_to_list(GoalBound, GoalList),
    % for shallow backtracking: printing true for variable unifications X=X
    % shallow === bindings are only searched for on the "head level" of the current goal
    %term_variables(GoalBound, VarList),
    %( VarList \= [] -> writeln('true,'); true),
    p(GoalBound, GoalFreeCopy, Prob),
    round_third(Prob, ProbRounded).

% for denominator computation in p/3 bindings in G are automatically freed according to binding pattern
% e.g.  G = (s(a,b),r(b,a)) --> GFree = (s(X,Y),r(Y,X))
%       G = (s(a,b),r(b,b)) --> GFree = (s(X,Y),r(Y,Y))
% --> oftentimes different denominators in same inference_SC/2 call
p(G, Result) :-
    goal_to_list(G, GList),
    % variables of G and GFree must also differ, otherwise they are bound in first z call and no longer free in second one
    copy_term(GList, GListCopy),
    free_up_bindings(GListCopy, GFreeList),
    goal_to_list(GFree, GFreeList),
    p(G, GFree, Result).

% underlying variable pattern of G is given as additional parameter in GFree
% e.g.  G = (s(a,b),r(b,a)), GFree = (s(X,Y),r(Z,X))
%       G = (s(a,c),r(b,a)), GFree = (s(X,Y),r(Z,X))
% --> same denominator for every backtracking iteration in inference_SC/3 call
p(G, GFree, Result) :-
    z_copy(G, Numerator),
    z_copy(GFree, Denominator),
    % rounding to fourth decimal for optimised and unoptimised inference results to equal for three decimals 
    % e.g. s(a,b),r(b,b) would otherwise result in 0.263 and 0.262 respectively
    round_fourth(Numerator, NumeratorRounded),
    round_fourth(Denominator, DenominatorRounded),
    Result is NumeratorRounded / DenominatorRounded.

% rounds to third decimal
round_third(Float, RoundedFloat) :-
    RoundedScaled is round(Float*1000),
    RoundedFloat is RoundedScaled/1000.
% rounds to fourth decimal
round_fourth(Float, RoundedFloat) :-
    RoundedScaled is round(Float*10000),
    RoundedFloat is RoundedScaled/10000.

unifSet_rec(_, [], 0).
unifSet_rec(CurrentGoal, [[CProb, CHead, CBody]|UnifSetTail], Akk) :-
    % copy everything but the current C as for next iteration free variables must remain unbound
    % variable identifications must be preserved, e.g. p(X), q(X) --> p(Y), q(Y)
    copy_term((CurrentGoal,UnifSetTail), (CurrentGoalFree,UnifSetTailFree)),
    % binding variables according to current C in UnifSet (--> only one binding choice), e.g. [X=Y, Y=b]
    CurrentGoal = CHead,
    z((CBody, true), Weight),
    unifSet_rec(CurrentGoalFree, UnifSetTailFree, Akknew),
    Akk is CProb*Weight + Akknew.

% third argument are suitable substitutions, as opposed to clauses in unifSet_rec
substitSet_rec(_, _, [], 0).
substitSet_rec(CurrentGoal, RemainingGoal, [Substitutions|PairedVarBindingsTail], Akk) :-
    % for next iteration free variables in CurrentGoal, RemainingGoal and PairedVarBindingsTail must remain unbound --> copy_term
    % variable identifications must be preserved, e.g. p(X), q(X) --> p(Y), q(Y)
    % e.g. for PairedVarBindings old: [[X=a], [X=b]] becomes [[Y=b]] instead of [[a=b]]
    copy_term((CurrentGoal,RemainingGoal, PairedVarBindingsTail), (CurrentGoalFree,RemainingGoalFree, PairedVarBindingsTailFree)),
    % appropriate variable binding in CurrentGoal is propagated to variables in RemainingGoal --> calling unify_list on CurrentGoal suffices
    unify_list(CurrentGoal, Substitutions),
    z(CurrentGoal, Weight1),
    z(RemainingGoal, Weight2),
    % sum over all possible splitting substitutions
    substitSet_rec(CurrentGoalFree, RemainingGoalFree, PairedVarBindingsTailFree, Akknew),
    Akk is Weight1*Weight2 + Akknew.

% all variable binding outputs show come from backtracking in superlevel (either p or inference_marginal call)
% --> copying initial goal s.t. all processing bindings are performed on GCopy
% e.g. z(p(X), Prob): X = a, Prob = 1.0, vs. z_copy(p(X), Prob): Prob = 1.0
z_copy(G, Weight) :-
    copy_term(G, GCopy),
    z(GCopy, Weight).

% base cases, prevent backtracking to other clauses further down
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
    ;   % only ground terms make goals disjunct: first collect all possible ground values of SharedVars in matching clause heads
        % example: (G1, G2) = (s(X,Y), r(Y,X))
        % --> SharedVars = [X,Y]
        % --> SubstitListGround = [[a,c],[b,b],[b,a]]
        %   (in each list element we have the bindings for all shared variables)
        findall(SharedVars, (clause((_ :: G1), _), ground(SharedVars)), SubstitListGround),
        % collect substitutions containing free variables as well and bind them
        % --> SubstitListUnground = [[[X,b], [X,b]]]; note: Y in SharedVars entry was already bound to b
        findall([SharedVars, Args], (clause((_ :: G1), _), G1 =.. [_|Args], \+ ground(SharedVars)), SubstitListUnground),
        G1 =.. [Functor|_],
        % grounding remaining free shared variables
        % e.g. grounding X to a, b and c respectively
        % --> SubstitListGrounded =  [[a,b], [b,b], [c,b], [b,b]]
        ground_substits(SubstitListUnground, Functor, SubstitListGrounded),
        % concatenate previously ground and just grounded lists
        append(SubstitListGround, SubstitListGrounded, SubstitList),
        % SubstitSet is now Theta
        % in the case of (s(X,Y), r(Y,Z)), a substitution of Y=b or Y=c makes Vars in G1, G2 disjoint
        list_to_set(SubstitList, SubstitSet),
        % PairedVarBindings === all possibilities for binding the shared variables
        maplist(unifiable(SharedVars), SubstitSet, PairedVarBindings),
        substitSet_rec(G1, G2, PairedVarBindings, Weight)
    ).

% G non-compound and non-trivial head
z(G, Weight) :-
    % mutual exclusivity of goals
    G \= (_, _),
    G \= true,
    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    % always calling unifSet_rec with just one subgoal left
    % entire goal decomposition happened in z-call for compound goals and substitSet_rec
    unifSet_rec(G, UnifSet, Weight).

% unconstrained loglinear sampling
sample_UC(Head) :-
    findall([Prob::Head, Body], clause((Prob :: Head), Body), ClauseBag),
    % probabilistic clause selector binds Head and Body
    random_clause(Head, Body, ClauseBag),
    % sample once - stick to choice of random_clause
    !,
    % Head + Body ground; bind Prob
    (   clause((Prob :: Head), Body)
    ->  true
        % no such clause --> user asked for impossible compound case
        %   e.g. sample_UC((s(X,Y), r(Y,Z))).
    ;   fail
    ),
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
% impossible case
transform_probabilities([], []) :- fail.
% implicit failure/base case:
% probability of failure === 1 - sum of probabilities for successful cases
transform_probabilities([[P::H, B]], [[P::H, B], Failure]) :-
    % need head with same functor and arity, but all free variables as args
    functor(H, FailureName, FailureArity),
    length(K, FailureArity),
    FailureH =.. [FailureName|K],
    % need it in SC sampling for rewriting the tree
    assertz(1-P::FailureH :- fail),
    Failure = [1::FailureH, fail].
transform_probabilities([[P1::H1, B1],[P2::H2, B2]|Tail], L) :-
    TransfromedProb is P1 + P2,
    transform_probabilities([[TransfromedProb::H2, B2]|Tail], TempL),
    L = [[P1::H1, B1]|TempL].

% success-constrained backtrackable sampling
sample_SC(Head) :-
    findall([Prob::Head, Body], clause((Prob :: Head), Body), ClauseBag),
    random_clause(Head, Body, ClauseBag),
    !,
    % Head + Body ground; bind Prob
    (   clause((Prob :: Head), Body)
    ->  true
        % no such clause --> user asked for impossible compound case
        %   e.g. sample_SC((s(X,c), r(c,Z))).
    ;   fail
    ),
    % on failure, preprocess the tree, rewriting probabilities
    (   sample_SC(Body)
    ->  !
    ;   % need a fresh ClauseBag, failure might have been encountered + asserted
        findall([ProbNew::Head, BodyNew], clause((ProbNew :: Head), BodyNew), ClauseBagNew),
        % probabilities of current Head without the failed clause Prob::Head :- Body
        sum_remaining(ClauseBagNew, Prob, 0, Denominator),
        writeln(Denominator),
        % rewrite probabilities of remaining clauses proportional to remaining branches
        change_prob(ClauseBagNew, [Prob::Head, Body], Denominator)
    ).

sample_SC((G1, G2)) :-
    !,
    sample_SC(G1),
    sample_SC(G2).

sample_SC(G) :-
    !,
    G.

change_prob([], [_::_, _], _).
% failed clause Prob::Head :- Body --> 0 probability
change_prob([[Prob::Head, Body]|BagTail], [Prob::Head, Body], Denominator) :-
    retract(Prob::Head :- Body),
    % assertz(0::Head :- Body),
    change_prob(BagTail, [Prob::Head, Body], Denominator).
% otherwise --> adjust
% no backtracking of failed case to this because clause with that Prob was retracted
change_prob([[P::H, B]|BagTail], [Prob::Head, Body], Denominator) :-
    retract(P::H :- B),
    round_third(P/Denominator, Rounded),
    assertz(Rounded::H :- B),
    change_prob(BagTail, [Prob::Head, Body], Denominator).

sum_remaining([], FailedP, Akk, Res) :-
    Res is Akk - FailedP.
sum_remaining([[P::_, _]|BagTail], FailedP, Akk, Res) :-
    Akknew is Akk + P,
    sum_remaining(BagTail, FailedP, Akknew, Res).

aux_unitarity_sumfunctors([], _, _, []).
aux_unitarity_sumfunctors([[Prob::Head]|Tail], PrevFname, Akk, Res) :-
    Head =.. [FName|_],
    (   FName = PrevFname
    ->  Akknew is Akk + Prob,
        aux_unitarity_sumfunctors(Tail, FName, Akknew, Res)
    ;   round_third(Akk, RoundedAkk),
        aux_unitarity_sumfunctors(Tail, FName, Prob, Resnew),
        Res = [[RoundedAkk::PrevFname]|Resnew]
    ).

aux_unitarity_msg([P::Functor]) :-
    (   P > 1
    ->  ansi_format([bold,fg(red)], 'error', []),
        format(": probabilities over heads of functor '~w' don't sum to 1~n", [Functor])
    ;   true
    ).

check_unitarity :-
    findall([Prob::Head], clause((Prob :: Head), _), ClauseBag),
    % initial guard name
    gensym(reserved_oldhead, X),
    aux_unitarity_sumfunctors(ClauseBag, X, 0, [_|Res]),
    maplist(aux_unitarity_msg, Res).

:- initialization(check_unitarity).
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

% --------------------

% data and test calls showcasing functionality scope of code

0.5 :: imSC(a).
0.3 :: imSC(b).
% difference inference_marginal - inference_SC
% probabilites of all clauses making up predicate imSC add up to 0.8 < 1 --> implicit failure with prob 0.2
% inference_marginal(imSC(X), Prob). 
%   X = a, Prob = 0.5
%   X = b, Prob = 0.3
% inference_SC(imSC(X), Prob).
%   X = a, Prob = 0.5/0.8 = 0.625
%   X = b, Prob = 0.3/0.8 = 0.375

0.3 :: iSC23(a,a).
0.2 :: iSC23(a,b).
% difference inference_SC/2 - inference_SC/3
% automatic freeing of bindings for inference_SC/2 leads to different denominators for p quotient
% inference_SC(iSC23(X,Y), Prob).
%   X = Y, Y = a, Prob = 0.3/0.3 = 1      p/2 called with s(a,a) --> freed goal === s(X,X) --> Denominator = z(s(X,X), P), P = 0.3
%   X = a, Y = b, Prob = 0.2/0.5 = 0.4    p/2 called with s(a,b) --> freed goal === s(X,Y) --> Denominator = z(s(X,Y), P), P = 0.3 + 0.2 = 0.5
% inference_SC(iSC23(X,Y), iSC23(X,Y), Prob).
%   X = Y, Y = a, Prob = 0.3/0.5 = 0.6    p/3 called with s(a,a) and free goal s(X,Y) --> Denominator = z(s(X,Y), P), P = 0.3 + 0.2 = 0.5
%   X = a, Y = b, Prob = 0.2/0.5 = 0.4    p/3 called with s(a,b) and free goal s(X,Y) --> Denominator = z(s(X,Y), P), P = 0.3 + 0.2 = 0.5

0.6 :: p(a).
0.4 :: p(b).
0.3 :: q(a).
0.7 :: q(b).
% difference inference_SC_unoptim - inference_SC
% inference_SC_unoptim naively calls subgoals recursively --> subgoals may be computed more than once
% inference_SC computes set of splitting substitution first --> calling subgoals with no shared variables independently of each other sparing recursions
% inference_SC_unoptim((p(X), q(Y)), Prob).
%   p(X),q(Y) --> unifSet(p(X)) === {X = a, X = b}
%       X = a: p(a),q(Y) --> unifSet(q(Y)) === {Y = a, Y = b}
%           Y = a: q(a)
%           Y = b: q(b)
%       X = b: p(b),q(Y) --> unifSet(q(Y)) === {Y = a, Y = b}
%           Y = a: q(a)
%           Y = b: q(b)
% inference_SC((p(X), q(Y)), Prob).
%   sharedVariables(p(X), q(Y)) === [] --> p(X) and q(Y) are processed independently
%   p(X) --> unifSet(p(X)) === {X = a, X = b}
%       X = a: p(a)
%       X = b; p(b)
%   q(Y) --> unifSet(q(Y)) === {Y = a, Y = b}
%       Y = a; q(a)
%       Y = b; q(b)

% difference inference_SC - p or inference_marginal - z_copy
% inferences calls backtrack, i.e. variables get successively bound to all possible (ground) values
% p and z_copy calls do not backtrack, i.e. output is sum over results for all possible bindings of input variables
% inference_SC((p(X),q(X)), (p(X),q(Y)), Prob).
%   X = a, Prob = 0.18
%   X = b, Prob = 0.28
% p((p(X),q(X)), (p(X),q(Y)), Prob).
%   Prob = 0.18 + 0.28 = 0.46
% inference_marginal((p(X),q(X)), Prob).
%   X = a, Prob = 0.18
%   X = b, Prob = 0.28
% z_copy((p(X),q(X)), Prob).
%   Prob = 0.45999... === 0.46

0.5 :: ideepback(X) :- p(X).
0.2 :: ideepback(c).
% deep backtracking for variables in head
% backtracking in inference calls consideres:
%   bindings generated by all clause heads unifying with current goal
%   bindings generated by recursively calling bodies of unifying heads with free variables
% inference_SC(ideepback(X), Prob).
%   X = a, Prob = (0.5*0.6)/0.7 = 0.429 --> binding from body p(X)
%   X = b, Prob = (0.5*0.4)/0.7 = 0.286 --> binding from body p(X)
%   X = c, Prob = 0.2/0.7 = 0.286       --> binding from head ideepback(c)

0.2 :: u(a,b).
0.4 :: u(b,a).
0.3 :: u(c,c).
0.7 :: v(a).
0.3 :: w(b).
0.6 :: w(d).
% need for both unifSet_rec and substitSet_rec in optimised inference_SC
% z_copy((u(X,Y), v(Y)), Prob) call in inference_SC((u(X,Y), v(Y)), (u(X,Y), v(Y)), Prob).
%   sharedVariables(u(X,Y), v(Y)) = [Y]     --> substitSet(u(X,Y), v(Y)) === {Y = a} 
%   Y = a in substitSet_rec: u(X,a), v(a)   --> processed independently
%   u(X,a) --> unifSet(u(X,a)) === {X = b}
%       X = b in unifSet_rec: u(b,a)
%   v(a)

% handling both single and compound goals
% single goal: inference_SC(v(X)).
%   X = a, Prob = 1
% compound goal, i.e. conjunctions: inference_SC((v(X), u(X,Y), w(Z)), (v(X), u(X,Y), w(Z)), Prob).
%   X = a, Y = Z, Z = b, Prob = 0.333
%   X = a, Y = b, Z = d, Prob = 0.667
% similarly for all other inference versions

% handling ground, partially ground and free goals
% inference_SC((u(c,c), v(a)), (u(X,Y), v(Z)), Prob).
%   Prob = (0.3*0.7)/((0.2+0.4+0.3)*0.7) = 0.333
% inference_SC(v(b), Prob).
%   false --> equal to zero probability as no clause with head v(b) exists
% inference_SC((u(X,b), w(Y)), (u(X,Z), w(Y)), Prob).
%   X = a, Y = b, Prob = (0.2*0.3)/((0.2+0.4+0.3)*(0.3+0.6)) = 0.074
%   X = a, Y = d, Prob = (0.2*0.6)/(0.9*0.9) = 0.148 
% similarly for all other inference versions
% free goals already implicitely demonstrated in all inference_SC calls for denominator computation

0.4 :: imultBodies(X,Y) :- u(X,Y), w(X), v(Y).
% multiple bodies
% inference_marginal(imultBodies(X,Y), Prob). 
%   X = b, Y = a, Prob = 0.4*(0.4*0.3*0.7) = 0.034

0.7 :: s(X, b) :- q(X).
0.1 :: s(a, c).
0.1 :: s(b, b).
0.05 :: s(b, a).
0.2 :: r(b, Z) :- p(Z).
0.7 :: r(a, b).
% running example in code comments


0.2 :: f(b).
0.6 :: f(X).
0.2 :: f(X) :- fail.


0.1 :: st(a, b).
0.9 :: st(X, b) :- fail.

5/10 :: dqq(a).
3/10 :: dqq(b).
0.5 :: compound(X) :- p(X), q(X).