:- op(1199,xfx,::).
:- discontiguous (::)/2.

% SLP interpretation, collecting multiple clauses
inference(Rule, ProbLists_summed) :-
    findall(Prob::Rule, inference_(Rule, Prob), ProbList),
    group_by(Rule, Prob, member(Prob::Rule, ProbList), ProbLists),
    sum_list(ProbLists, ProbLists_summed).

collect_clauses(Rule, Body, PRet) :-
    findall(Prob::Rule, clause((Prob :: Rule), Body), ClauseList),
    group_by(Rule, Prob, member(Prob::Rule, ClauseList), ProbLists),
    sum_list(ProbLists, PRet).

% case 'Rule = true'
% only with inference_(true, Prob)
inference_(true, 1).

% body of Rule === true, happens when Rule is atomic
% (e.g. 0.7 :: q(a), so when asking for a fact -
% in this case clause automatically sets the body to true)
% or as a base case of both recursions
inference_(Rule, Prob) :-
    % clause: find a head and its corresponding body and unify
    collect_clauses(Rule, true, Prob).

% head recursion
inference_((Goal1, Goal2), ProbRes) :-
    inference_(Goal1, Prob1),
    inference_(Goal2, Prob2),
    ProbRes is Prob1*Prob2.

% head recursion
inference_((Goal1; Goal2), ProbRes) :-
    inference_(Goal1, Prob1),
    inference_(Goal2, Prob2),
    ProbRes is (Prob1 + Prob2  - Prob1*Prob2).

% body recursion, compound
inference_(Rule, ProbRes) :-
    % body is not yet bound, we bind it here
    collect_clauses(Rule, Body, PRet),
    nonvar(Body),
    Body = (Goal1, Goal2),
    inference_(Goal1, Prob1),
    inference_(Goal2, Prob2),
    ProbRes is PRet*Prob1*Prob2.

% body recursion, compound
inference_(Rule, ProbRes) :-
    collect_clauses(Rule, Body, PRet),
    nonvar(Body),
    Body = (Goal1; Goal2),
    inference_(Goal1, Prob1),
    inference_(Goal2, Prob2),
    % this recursion exactly corresponds to the inclusion-exclusion-principle
    ProbRes is PRet*(Prob1 + Prob2 - Prob1*Prob2).

% body recursion, non-compound
inference_(Rule, ProbRes) :-
    collect_clauses(Rule, Body, PRet),

    % preventing above cases to fire again
    Body \= (Goal1, Goal2),
    Body \= (Goal1; Goal2),
    Body \= true,

    % now our body is the new goal
    inference_(Body, Prob),
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

0.5::s(X) :- z(X).

% want(a): 0.4*(0.2+0.3*1 + 0.3 - (0.2+0.3*1)*0.3) + 0.2* (0.2+0.3*1)*1.2 = 0.38
0.4::t(X) :- q(X); r(X).
0.2::t(X) :- q(X), r(Y).

0.7 :: u(X) :- q(X), r(X), p(X).
0.3 :: u(X) :- q(X); r(X); p(X).

% API:
% inference(q(X), Prob).
% ===> zeige die Whrschktn für alle Belegungen an
0.2 :: q(a).
0.3 :: q(a) :- fact1.
0.1 :: q(b).
0.4 :: q(c).

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

% test: stupidgame
play(State) :- stop(State,State).
play(State) :-
    pay_entrance(State,State1),
    dice_reward(State1,State2),
    play(State2).

stop([Player,Banker],_) :-
    Player1 is Player,
    Banker1 is Banker,
    write('Player = '), write(Player1),
    write('Banker = '), write(Banker1).
pay_entrance([Player,Banker],[Player-4,Banker+4]).
dice_reward([Player,Banker],[Player+D,Banker-D]) :- roll_dice(D).

1/6::roll_dice(1).
1/6::roll_dice(1).
1/6::roll_dice(2).
1/6::roll_dice(3).
1/6::roll_dice(4).
1/6::roll_dice(5).
1/6::roll_dice(6).

% TODO/extra:
% sampling(q(X), q(Z)) -> sampling(q(X)), sampling(q(Z)).
% sampling(q(X), p(Z)) -> sampling(q(X)), sampling(p(Z))
% sampling(q(X), p(X)) -> assert(1 :: neu(X) :- q(X), p(X).), sampling(neu(X)), retract(neu).
% sampling(q(X), q(X)) -> sampling(q(X))

% q === rot
% p === König
% sampling(q(X), p(Z))
% P(X rot , Z ist ein König) = (1/4)*(1/13) = 1/52 = 13*4 / 52^2

% q === rot
% p === König
% sampling(q(X), p(X))
% P(X ist rot und ein König) = 1/52

% q === rot
% sampling(q(X), q(Z))
% P(X ist rot und Z ist rot) = 1/16

% q === rot
% sampling(q(X), q(X))
% P(X ist rot und X ist rot) = 1/4 * 1

1/4::karte(karo).
1/4::karte(herz).
1/4::karte(pik).
1/4::karte(kreuz).

1/4::herz(karte).
1/4::karo(karte).
1/4::pik(karte).
1/4::kreuz(karte).
1/13::koenig(karte).

% slp / plp?
% want: P === 1
1/2::goal :- fact1.
1/2::goal :- fact2.
1::fact1.
1::fact2.

% slp no sharing of subgoals between branches
% want: P === 0.25
1::goal1 :- left, right.
1::left :- fact.
1::right :- fact.
1/2::fact :- true.
1/2::fact :- fail.

% slp, nested subgoals
% want: P === 0.5^2* (0.25+3/8)  + 0.5 = 0.65625
0.5::goal2 :- left1, right1.
0.5::goal2 :- true.
3/4::left1 :- newfact.
1/4::left1 :- true.
1::right1 :- newfact.
1/2::newfact :- true.
1/2::newfact :- fail.

% slp, nested subgoals 2
% want: P === 1/2 + (1/3 + 1/3*(3/5+(1/5*2/5))*(2/5)) = 0.9240
1/2 :: gl0 :- true.
1/2 :: gl0 :- gl1.

1/3 :: gl1 :- true.
1/3 :: gl1 :- fail.
1/3 :: gl1 :- gl21, gl22.

1/5 :: gl21 :- true.
1/5 :: gl21 :- true.
1/5 :: gl21 :- true.
1/5 :: gl21 :- gl22.
1/5 :: gl21 :- fail.

1/5 :: gl22 :- true.
1/5 :: gl22 :- true.
1/5 :: gl22 :- fail.
1/5 :: gl22 :- fail.
1/5 :: gl22 :- fail.

% neuer randfall (und der grund wieso wir bei cussen's exact inference algorithmus den nenner brauchen / wieso er nicht immer 1 ist)
1/2 :: s(a) :- p(a).
1/2 :: s(a) :- q(a).
0.6 :: p(a).
0.4 :: p(b).
0.3 :: q(a).
0.7 :: q(b).

