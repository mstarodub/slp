% vim: filetype=prolog




% lesen von probabilities
:- op(1199,xfx,::).

demo(true, 1) :- !. % base case 'Rule = true'

demo(Rule, Prob) :- % base case 'body of Rule = true', i.e. Rule atomic
    clause(Prob :: Rule, true).

demo(Rule, ProbRes) :- % case 'compounded body, conjunction'
    clause((PRet :: Rule), Body),
    Body = (Goal1, Goal2), 
    !, % cut prevents unifying with 'single predicate body' case as well
    demo(Goal1, Prob1),
    demo(Goal2, Prob2),
    ProbRes is PRet*Prob1*Prob2.

demo(Rule, ProbRes) :- % case 'compounded body, disjunction'
    clause((PRet :: Rule), Body),
    Body = (Goal1; Goal2), 
    !, % cut prevents unifying with Body = Goal case as well
    demo(Goal1, Prob1),
    demo(Goal2, Prob2),
    ProbRes is PRet*(Prob1 + Prob2 - Prob1*Prob2).

demo(Rule, ProbRes) :- % case 'single predicate body'
    clause((PRet :: Rule), Body),
    ( Body = true
    -> fail, !
    ; Body = Goal,
    demo(Goal, Prob),
    ProbRes is PRet*Prob).

% not yet tested

% ok
0.5::roll_dice(2).

0.4 :: q(a).
0.5 :: q(b).
0.7 :: q(c).

% ok
0.5::s(X) :- q(X).

% not ok: not both answers t(a) and t(b) are provided
0.4::t(X) :- q(X), r(X).

0.3 :: r(a).
0.7 :: r(b).
