% vim: filetype=prolog




% lesen von probabilities
:- op(1199,xfx,::).

inference(true, 1) :- !. % base case 'Rule = true'

inference(Rule, Prob) :- % base case 'body of Rule = true', i.e. Rule atomic and in particular not compound
    clause(Prob :: Rule, true).

inference(Rule, ProbRes) :- % case 'compound body, conjunction'
    ( Rule \= (Goal1, Goal2), Rule \= (Goal1; Goal2) % check: Rule not compound
    -> clause((PRet :: Rule), Body),
        Body = (Goal1, Goal2), 
        inference(Goal1, Prob1),
        inference(Goal2, Prob2),
        ProbRes is PRet*Prob1*Prob2
    ; rule_rec(Rule, ProbRes), !). % cut guarantees single rule_rec call for current Rule; otherwise called again in following cases

inference(Rule, ProbRes) :- % case 'compound body, disjunction'
    ( Rule \= (Goal1, Goal2), Rule \= (Goal1; Goal2) % check: Rule not compound
    -> clause((PRet :: Rule), Body),
        Body = (Goal1; Goal2), 
        inference(Goal1, Prob1),
        inference(Goal2, Prob2),
        ProbRes is PRet*(Prob1 + Prob2 - Prob1*Prob2)
    ; rule_rec(Rule, ProbRes), !). % cut guarantees single rule_rec call for current Rule; otherwise called again in following case

inference(Rule, ProbRes) :- % case 'single predicate body'
    ( Rule \= (Goal1, Goal2), Rule \= (Goal1; Goal2) % check: Rule not compound
    -> clause((PRet :: Rule), Body),
        ( Body = true
        -> fail, !
        ; Body \= (Goal1, Goal2), % preventing compound case from unifying with this more general case
            Body \= (Goal1; Goal2), % preventing compound case from unifying with this more general case
            Body = Goal,
            inference(Goal, Prob),
            ProbRes is PRet*Prob)
    ; rule_rec(Rule, ProbRes), !). % cut guarantees single rule_rec call for current Rule; perhaps not necessary, but symmetric to above cases

rule_rec((Goal1, Goal2), ProbRes) :-
    inference(Goal1, Prob1),
    inference(Goal2, Prob2),
    ProbRes is Prob1*Prob2.

rule_rec((Goal1; Goal2), ProbRes) :-
    inference(Goal1, Prob1),
    inference(Goal2, Prob2),
    ProbRes is (Prob1 + Prob2 - Prob1*Prob2).

% not yet tested

% seem to be all ok
0.5::roll_dice(2).

0.5::s(X) :- q(X).

0.4::t(X) :- q(X); r(X).

0.2::t(X) :- q(X), r(Y).

0.7 :: u(X) :- q(X), r(X), p(X).
0.3 :: u(X) :- q(X); r(X); p(X).

0.4 :: q(a).
0.5 :: q(b).
0.7 :: q(c).

0.3 :: r(a).
0.7 :: r(b).

0.6 :: p(a).
0.1 :: p(b).
0.9 :: p(c).
