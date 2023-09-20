% compound body
sample((G1, G2)) :-
    !,
    sample(G1),
    sample(G2).

% Should this case really be a subclause of sample or does it rather belong to the (toplevel) metainterpreter
sample(G) :-
    \+clause((Prob :: G), _),
    !,
    G.

sample(Head) :-
    findall([Prob, Head, Body], clause((Prob :: Head), Body), Bag),
    random_clause(Head, Body, Bag),
    !,
    sample(Body).

% probabilistic clause selector
random_clause(Head, Body, Bag) :-
    Rand is random_float,
    choose(Bag, Head, Body, 0, Rand, Sum).
choose([], _, _, _, _, 0).
choose([[Prob, Head, Body]|Tail], Head1, Body1, Akk, Rand, Rest) :-
    Akknew is Akk + Prob,
    choose(Tail, Head1, Body1, Akknew, Rand, Rest1),
    Rest is Rest1 + Prob,
    ((var(Body1),
        Prob1 is Akk/(Akk+Rest), Rand >= Prob1, Head1 = Head, Body1 = Body);
    true).
