:- op(1199,xfx,::).

% case 'Rule = true'
% only with inference(true, Prob)
inference(true, 1).

% body of Rule === true, happens when Rule is atomic
% (e.g. 0.7 :: q(a), so when asking for a fact -
% in this case clause automatically sets the body to true)
% or as a base case of both recursions
inference(Rule, Prob) :-
    % clause: find a head and its corresponding body and unify
    clause(Prob :: Rule, true).

% head recursion
inference((Goal1, Goal2), ProbRes) :-
    inference(Goal1, Prob1),
    inference(Goal2, Prob2),
    ProbRes is Prob1*Prob2.

% head recursion
inference((Goal1; Goal2), ProbRes) :-
    inference(Goal1, Prob1),
    inference(Goal2, Prob2),
    ProbRes is (Prob1 + Prob2  - Prob1*Prob2).

% body recursion, compound
inference(Rule, ProbRes) :-
    % body is not yet bound, we bind it here
    clause((PRet :: Rule), Body),
    Body = (Goal1, Goal2), 
    inference(Goal1, Prob1),
    inference(Goal2, Prob2),
    ProbRes is PRet*Prob1*Prob2.

% body recursion, compound
inference(Rule, ProbRes) :-
    clause((PRet :: Rule), Body),
    Body = (Goal1; Goal2), 
    inference(Goal1, Prob1),
    inference(Goal2, Prob2),
    % this recursion exactly corresponds to the inclusion-exclusion-principle
    ProbRes is PRet*(Prob1 + Prob2 - Prob1*Prob2).

% body recursion, non-compound
inference(Rule, ProbRes) :-
    clause((PRet :: Rule), Body),

    % preventing above cases to fire again
    Body \= (Goal1, Goal2),
    Body \= (Goal1; Goal2),
    Body \= true,

    % now our body is the new goal
    inference(Body, Prob),
    ProbRes is PRet*Prob.

sampling(Head) :-
    % need to compute the actual probabilities for all probability-head pairs
    findall(Prob::Head, inference(Head, Prob), ProbHeadPairs),
    transform_probabilities(ProbHeadPairs, ShiftedProbHeadPairs),
    last(ShiftedProbHeadPairs, UpperUniformEnd :: _),
    % we just sample once for now
    !,
    SampleProb is random_float * UpperUniformEnd,
    select_head(ShiftedProbHeadPairs, SampleProb, Head).

select_head([], _, false).
select_head([ShiftedProb::ShiftedHead|Tail], SampleProb, Sample) :-
    ( ShiftedProb >= SampleProb
    -> Sample = ShiftedHead
    ; select_head(Tail, SampleProb, Sample)).

% shift the probabilities recursively so we can sample from a uniform distribution
transform_probabilities([], []).
transform_probabilities([P::B], [P::B]).
transform_probabilities([P1::B1,P2::B2|B], L) :-
    TransfromedProb is P1 + P2,
    transform_probabilities([TransfromedProb::B2|B], TempL),
    L = [P1::B1|TempL].

% TESTS

% seem to be all ok
0.5::roll_dice(2).

0.5::s(X) :- z(X).

0.4::t(X) :- q(X); r(X).

0.2::t(X) :- q(X), r(Y).

0.7 :: u(X) :- q(X), r(X), p(X).
0.3 :: u(X) :- q(X); r(X); p(X).

% API:
% inference(q(X), Prob).
% ===> zeige die Whrschktn für alle Belegungen an
0.2 :: q(a).
0.1 :: q(b).
0.7 :: q(c).

0.3 :: r(a).
0.9 :: r(b).

% maybe these should add up to 1 after all to make sense (but our sampling works regardless)
0.0 :: p(a).
0.1 :: p(b).
0.9 :: p(c).

0.5 :: d(X, Y) :- p(X), q(Y).

% sampling(z(X)) ===> eher b
% random testing: a: 5x, b: 72x
0.1 :: z(a).
0.9 :: z(b).

% TODO/extra:
% sampling(q(X), q(Z)) -> sampling(q(X)), sampling(q(Z)).
% sampling(q(X), p(Z)) -> sampling(q(X)), sampling(p(Z))
% sampling(q(X), p(X)) -> assert(1 :: neu(X) :- q(X), p(X).), sampling(neu(X)), retract(neu).
% sampling(q(X), q(X)) -> sampling(q(X))

