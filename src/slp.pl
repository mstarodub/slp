:- op(1199,xfx,::).
:- discontiguous (::)/2.
:- dynamic (::)/2.

% meta-assumptions:
%   only conjunctions
%   normalized SLP (all clauses forming a predicate add up to 1)
%   pure SLP (no non-prob. clauses)

% when the VarList is exhausted, set the result to the singe remaining entry in the weight, that entry is the probability
replace_left([], Remains, Remains).
replace_left([NewL|TailNewL], [_=R|Tail], [NewL=R|Res]) :-
    var(NewL),
    replace_left(TailNewL, Tail, Res).
% ignoring already globally bound variables s.t. lenght of binding list [_=R|Tail] equals list of new lefts [NewL|TailNewL]
replace_left([NewL|TailNewL], [_=R|Tail], Res) :-
    nonvar(NewL),
    replace_left(TailNewL, [_=R|Tail], Res).

% replacing ground atoms with free variables according to the unification pattern in UnifBag
ground_to_var([], _, []).
ground_to_var([GroundHead|GroundTail], UnifBag, [Var|VarListTail]) :-
    member((Var=GroundHead), UnifBag),
    ground_to_var(GroundTail, UnifBag, VarListTail).

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

% example call: inference_marginal((s(X,Y),r(Y,Z)), Prob)
% in the general case, one Variable (TODO: which?) is not part of the list in Weight but rather detemined by backtracking
inference_marginal(Goal, ProbList) :-
    % example goal: (s(X,Y), r(Y,Z))
    % ---> VarList === [X,Y,Z]
    % after z call: VarList === [X,b,Z]
    % because of that:
    % preserving variable names for pretty output
    % TODO: may order of vars in list differ from the order in the output list?
    term_variables(Goal, VarList),
    z(Goal, Weight, 0), 
    % for the example goal of (s(X,Y), r(Y,Z)), we currently have
    % Y=b,
    % Weight = [[b=b, _=X, 0.14], [c=c, _=a, 0], [b=b, _=b, 0.04]]
    % invariant: forall w in Weight. len(VarList - ground terms) === len(w - last element)
    % replace_left then takes the variables from VarList and replaces the left hand '=' sides with them in order (for each w in Weight [is a list])
    maplist(replace_left(VarList), Weight, ProbList).


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

collect_grounds(Goal, GoalsTail, Res).


% idea behind free_bindings:
% destructure input term iteratively, ultimately reaching every ground atom that needs to be replaced by a free variable
% based on current term structure three processing methods:
%   variables: no replacement required --> appending to result list as left-most element 
%   ground atoms: replacement required -->
%       appending atom to GroundList so that it gets replaced in the base case,
%       retrieving corresponding free variable from FreeList and append it as left-most element to result list
%   predicates: no replacement required --> 
%       destructuring with =.. and calling recursion on its arguments
%       reassembling predicate after all inner arguments have been processed
%       adding predicate (now containing only free variables) as left-most element to result list
%
% obstacles: Same bindings must be replaced with same variables --> first collecting all bindings in list and only then replacing them 
%
% for compound goals: both depth and breadth recursion needed
%   depth recursion: decomposing a single goal
%   breadth recursion: recursively processing all subgoals, starting at the left-most
%   second to last argument: list making up depth result
%   last argument: list making up breadth result === overall result  

% breadth and depth base case: replacing all ground atoms in Ground with free variables
free_bindings([], [], GroundList, FreeList, [], []) :- 
    % list_to_set to obtain same variable name for same binding
    list_to_set(GroundList, GroundSet),
    % for each ground atom in GroundSet get one fresh free variable
    length(GroundSet, GroundLength),
    length(FreeSet, GroundLength),
    unifiable(FreeSet, GroundSet, UnifBag),
    % change ground atoms to variables according to pairing in UnifBag
    ground_to_var(GroundList, UnifBag, FreeList).
% breadth recursion starting at depth base case:
free_bindings([], [RemainingHead|RemainingTail], GroundList, FreeList, [], BreadthResList) :-
    free_bindings([RemainingHead], RemainingTail, GroundList, FreeList, NewDepthResList, BreadthResList).
% depth recursion: handling variables
free_bindings([TermHead|TermTail], RemainingTerms, GroundList, FreeList, [TermHead|DepthResTail], BreadthResList) :-
    % TermHead is a variable
    var(TermHead),
    free_bindings(TermTail, RemainingTerms, GroundList, FreeList, DepthResTail, BreadthResList).
% depth recursion: handling ground atoms
free_bindings([TermHead|TermTail], RemainingTerms, GroundTail, FreeTail, [FreeHead|DepthResTail], BreadthResList) :-
    % TermHead no variable (otherwise instantiation errors in =..)
    nonvar(TermHead),
    TermHead =.. [Functor|TList],
    % TermHead is atomic and ground
    TList = [],
    free_bindings(TermTail, RemainingTerms, [Functor|GroundTail], [FreeHead|FreeTail], DepthResTail, BreadthResList).
% depth recursion: handling non-ground predicates
% result is appended to overall result list in right-most argument
free_bindings([TermHead|_], RemainingTerms, GroundList, FreeList, [Predicate], [Predicate|BreadthResTail]) :-
    % TermHead no variable (otherwise instantiation errors in =..)
    nonvar(TermHead),
    TermHead =.. [Functor|TList],
    % mutual exclusivity of clauses preventing false results via backtracking (e.g. for free_bindings([f(a)], [], _, Free))
    TList \= [],
    free_bindings(TList, RemainingTerms, GroundList, FreeList, DepthResTail, BreadthResTail),
    Predicate =.. [Functor|DepthResTail].


p(G, RoundedResult) :-
    goal_to_list(G, [GHead|GTail]),
    free_bindings([GHead], GTail, [], _, _, GFreeList),
    goal_to_list(GFree, GFreeList),
    z(G, Numerator, _),
    z(GFree, Denominator, _),
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

% Akk is the Weight, can be a float or a List. zero depth base case for concatenation: need empty lists. Depth gets increased in each z recursion, not per unifSet_rec recursion
unifSet_rec(_, _, [], [], Depth) :- nonvar(Depth), Depth = 0, !.
unifSet_rec(_, _, [], 0, _) :- !. % base case cut: prevents further backtracking and final output "false"
unifSet_rec(CurrentGoal, RemainingGoal, [UnifClause|UnifSetTail], Akk, Depth) :-
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
    % incrementing Depth value for marginal inference when reaching new level for z recursion
    ( nonvar(Depth) -> DepthNew is Depth+1; DepthNew = Depth),
    z((ClauseBody, RemainingGoal), Weight, DepthNew),
    unifSet_rec(CurrentGoalFree, RemainingGoalFree, UnifSetTailFree, Akknew, Depth),
    ( nonvar(Depth), Depth = 0
        % marginal inf toplevel
        ->  BindingProb is ClauseProb*Weight,
            round_third(BindingProb, BindingProbRound), % rounding probability occurring in output
            % [X=Y, Y=b] <> [0.3] === [X=Y, Y=b, 0.3]
            append(UnifBag, [BindingProbRound], AkkTemp),
            append([AkkTemp], Akknew, Akk) % for all but the last element in unif set Akknew will be a list
        % SC inf / marginal recursive
        ;   Akk is ClauseProb*Weight + Akknew).

substitSet_rec(_, _, [], 0, _) :- !. % base case cut: prevents further backtracking and final output "false"
substitSet_rec(CurrentGoal, RemainingGoal, [Substitutions|PairedVarBindingsTail], Akk, Depth) :-
    % substitSet_rec recursion requires all subgoals to be as unbound as possible
    % PairedVarBindings must also remain unbound, e.g. old: [X=a], [X=b] becomes [Y=b] instead of [a=b]
    % free variable relations must be preserved, e.g. p(X), q(X) must become p(Y), q(Y)
    copy_term((CurrentGoal,RemainingGoal, PairedVarBindingsTail), (CurrentGoalFree,RemainingGoalFree, PairedVarBindingsTailFree)),

    % here, the third argument of substitSet_rec are suitable substitutions, as opposed to clauses in unifSet_rec
    unify_helper(CurrentGoal, Substitutions),
    unify_helper(RemainingGoal, Substitutions),
    z(CurrentGoal, Weight1, Depth),
    z(RemainingGoal, Weight2, Depth),
    % sum over all possible splitting substitutions
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

% loglinear: ähnlich zum v1, nur ohne inference call
% unification-constrained: in der effizienz zwischen loglinear und backtrackable
% backtrackable: hier implementieren
% importance: wahrscheinlich ein improvement zum improved loglinear

% TODO: what is the expected result for sampling a goal that doesn't exist?
% unconstrained (loglinear) sampling
sample_UC(Head) :-
    findall([Prob::Head, Body], clause((Prob :: Head), Body), ClauseBag),
    random_clause(Head, Body, ClauseBag),
    % we just sample once for now
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
    Rand is random_float,
    choose(ShiftedClauseBag, Rand, [Head, Body]).

choose([], _, false).
choose([[ShiftedProb::ShiftedHead, Body]|Tail], SampleProb, Sample) :-
    ( ShiftedProb >= SampleProb
    -> Sample = [ShiftedHead, Body]
    ; choose(Tail, SampleProb, Sample)).

% shift the probabilities so we can sample from a uniform distribution
% implicit failure/base case:
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
    random_clause(Head, Body, ClauseBag),
    % Head + Body ground; bind Prob
    clause((Prob :: Head), Body),
    !,
    ( sample_SC(Body)
    -> !
    % if we fail in the above, preprocess the tree, rewriting probabilities
    ;   writeln([Prob::Head, Body]),
        sum_remaining(ClauseBag, Prob, 0, Denominator),
        writeln(Denominator),
        change_prob(ClauseBag, [Prob::Head, Body], Denominator)
    ).

% compound body
sample_SC((G1, G2)) :-
    sample_SC(G1),
    sample_SC(G2).

sample_SC(G) :-
    G.

change_prob([], [_::_, _], _).
% failure -> 0
change_prob([[Prob::Head, Body]|BagTail], [Prob::Head, Body], Denominator) :-
    writeln([Prob::Head, Body]),
    retract(Prob::Head :- Body),
    assertz(0::Head :- Body),
    change_prob(BagTail, [Prob::Head, Body], Denominator).
% otherwise -> adjust
change_prob([[P::H, B]|BagTail], [Prob::Head, Body], Denominator) :-
    writeln(BagTail),
    retract(P::H :- B),
    round_third(P/Denominator, Rounded).
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
