% vim: filetype=prolog

:- op(601, xfx, <--).
:- op(600, xfx, ::).

sampling([]).
sampling([LAtom|Atoms]) :-
    findall(Prob :: Body, Prob :: LAtom <-- Body, TempSubs),
    transform_probabilities(TempSubs, Subs),
    last(Subs, ProbWeight),
    !,
    % Use clause?
    bagof(Prob :: Body, Prob :: LAtom <-- Body, SubCandidate),


    select_sub(Subs, Rand, 0, Sub),
    append(Sub,Atoms,NewAtoms),
    sampling(NewAtoms).

select_sub([LProb :: LSub|Subs], Rand, Akk, Sub) :-
    ChoiceValue is LProb + Akk,
    (ChoiceValue >= Rand
        -> Sub = LSub
        ; select_sub(Subs, Rand, ChoiceValue, Sub)).

transform_probabilities([], []).
transform_probabilities([P::B], [P::B]).
transform_probabilities([P1::B1,P2::B2|B], L) :-
    TransfromedProb is P1 + P2,
    transform_probabilities([TransfromedProb:B2|B], TempL),
    L = [P1::B1|TempL].

0.5 :: q(a) <-- [].
0.5 :: q(b) <-- [].
