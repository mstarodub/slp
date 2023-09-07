:- op(1199,xfx,::).

% base case 'Rule = true'
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



% seem to be all ok
0.5::roll_dice(2).

0.5::s(X) :- q(X).

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

0.0 :: p(a).
0.1 :: p(b).
0.9 :: p(c).

0.5 :: d(X, Y) :- p(X), q(Y).

% want:
% inference((d(X, Y), u(X)), Prob).
% inference((d(X, Y); u(X)), Prob).
% strategy: assert(1 :: neu(X, Y) :- d(X, Y), u(X) bzw ; u(X)), sampling(neu(...)), retract(neu).



