:- op(1199,xfx,::).

% base case 'Rule = true'
inference(true, 1) :- !.

% base case 'body of Rule = true', i.e. Rule atomic and in particular not compound
inference(Rule, Prob) :-
    clause(Prob :: Rule, true).

% case 'compound body, conjunction'
inference(Rule, ProbRes) :-
    % check: Rule not compound
    ( Rule \= (Goal1, Goal2), Rule \= (Goal1; Goal2)
    % body is not yet bound, we bind it here
    -> clause((PRet :: Rule), Body),
        Body = (Goal1, Goal2), 
        inference(Goal1, Prob1),
        inference(Goal2, Prob2),
        ProbRes is PRet*Prob1*Prob2
    % cut guarantees single rule_rec call for current Rule; otherwise called again in following cases
    ; rule_rec(Rule, ProbRes), !).

% case 'compound body, disjunction'
inference(Rule, ProbRes) :-
    % check: Rule not compound
    ( Rule \= (Goal1, Goal2), Rule \= (Goal1; Goal2)
    -> clause((PRet :: Rule), Body),
        Body = (Goal1; Goal2), 
        inference(Goal1, Prob1),
        inference(Goal2, Prob2),
        % this recursion exactly corresponds to the inclusion-exclusion-principle!
        ProbRes is PRet*(Prob1 + Prob2 - Prob1*Prob2)
    ; rule_rec(Rule, ProbRes), !).

% case 'single predicate body'
inference(Rule, ProbRes) :-
    % check: Rule not compound
    ( Rule \= (Goal1, Goal2), Rule \= (Goal1; Goal2)
    -> clause((PRet :: Rule), Body),
        ( Body = true
        -> fail, !
        % preventing compound case from unifying with this more general case
        ; Body \= (Goal1, Goal2),
            % preventing compound case from unifying with this more general case
            Body \= (Goal1; Goal2),
            Body = Goal,
            inference(Goal, Prob),
            ProbRes is PRet*Prob)
    % cut guarantees single rule_rec call for current Rule; perhaps not necessary, but symmetric to above cases
    ; rule_rec(Rule, ProbRes), !).

rule_rec((Goal1, Goal2), ProbRes) :-
    inference(Goal1, Prob1),
    inference(Goal2, Prob2),
    ProbRes is Prob1*Prob2.

rule_rec((Goal1; Goal2), ProbRes) :-
    inference(Goal1, Prob1),
    inference(Goal2, Prob2),
    ProbRes is (Prob1 + Prob2  - Prob1*Prob2).

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



