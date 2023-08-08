% lesen von probabilities
:- op(1199,xfx,::).

demo((Prob :: Head) :- Body) :-
    demo((Prob :: Head) :- Body, 1).

demo(Prob :: Rule) :-
    demo((Prob :: Rule) :- true, 1).

demo(Prob :: true, Akk).

demo((Prob :: Head) :- Body, Akk) :-
    Akk1 is Akk * Prob,

    %Rule =.. [Head, Body],
    % :-(Prob::Rule, Body),
    clause(Prob :: Head, Body),

    get_prob(Body, P),
    demo(P :: Body, Akk1).

get_prob(true, 1) :- !.
get_prob(B, PRet) :-
    PRet :: B.

% ok
0.5::roll_dice(2).

% noch nicht ok
0.5::s(X) :- q(X).
0.4::q(a).
