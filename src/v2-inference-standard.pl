% example call: Goal = (s(a,b),r(b,X)), GoalFree = (s(X,Y),r(Y,X)), inference_SC(Goal, Prob).
inference_SC_unoptim(Goal, GoalFree, ProbRounded) :-
    % preventing GoalFree from getting grounded by backtracking
    copy_term(GoalFree, GoalFreeCopy),
    goal_to_list(Goal, GoalList),
    bind_goal(GoalList),
    goal_to_list(GoalBound, GoalList),
    % for shallow backtracking: printing true for variable unifications X=X
    % shallow === bindings are only searched for on the "head level" of the current goal
    %term_variables(GoalBound, VarList),
    %( VarList \= [] -> writeln('true,'); true),
    p_unoptim(GoalBound, GoalFreeCopy, Prob),
    round_third(Prob, ProbRounded).

p_unoptim(G, Result) :-
    goal_to_list(G, GList),
    % variables of G and GFree must also differ, otherwise they are bound in first z call and no longer free in second one
    copy_term(GList, GListCopy),
    free_up_bindings(GListCopy, GFreeList),
    goal_to_list(GFree, GFreeList),
    p(G, GFree, Result).


p_unoptim(G, GFree, Result) :-
    z_copy_unoptim(G, Numerator),
    z_copy_unoptim(GFree, Denominator),
    % rounding to fourth decimal for optimised and unoptimised inference results to equal for three decimals
    % e.g. s(a,b),r(b,b) would otherwise result in 0.263 and 0.262 respectively
    round_fourth(Numerator, NumeratorRounded),
    round_fourth(Denominator, DenominatorRounded),
    Result is NumeratorRounded / DenominatorRounded.

unifSet_rec_unoptim(_, _, [], 0).
unifSet_rec_unoptim(CurrentGoal, RemainingGoal, [[CProb, CHead, CBody]|UnifSetTail], Akk) :-
    % copy everything but the current C as for next iteration free variables must remain unbound
    % variable identifications must be preserved, e.g. p(X), q(X) --> p(Y), q(Y)
    copy_term((CurrentGoal, RemainingGoal, UnifSetTail), (CurrentGoalFree, RemainingGoalFree, UnifSetTailFree)),
    % binding variables according to current C in UnifSet (--> only one binding choice), e.g. [X=Y, Y=b]
    % binding is propagated to variables in Remaining Goal
    CurrentGoal = CHead,
    z_unoptim((CBody, RemainingGoal), Weight),
    unifSet_rec_unoptim(CurrentGoalFree, RemainingGoalFree, UnifSetTailFree, Akknew),
    Akk is CProb*Weight + Akknew.

% all variable binding outputs show come from backtracking in superlevel (either p or inference_marginal call)
% --> copying initial goal s.t. all processing bindings are performed on GCopy
z_copy_unoptim(G, Weight) :-
    copy_term(G, GCopy),
    z_unoptim(GCopy, Weight).

% base cases, prevent backtracking to other clauses
z_unoptim(true, 1).
% fires when e.g. G is body of non-compound head
z_unoptim((G, true), Weight) :- z_unoptim(G, Weight), !.
z_unoptim((true, G), Weight) :- z_unoptim(G, Weight), !.

z_unoptim((G1, G2), Weight) :-
    % mutual exclusivity of goals
    G1 \= true,
    findall([Prob, G1, Body], clause((Prob :: G1), Body), UnifSet),
    unifSet_rec_unoptim(G1, G2, UnifSet, Weight).

% G non-compound and non-trivial head
z_unoptim(G, Weight) :-
    % mutual exclusivity of goals
    G \= (_, _),
    G \= true,
    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    unifSet_rec_unoptim(G, true, UnifSet, Weight).
