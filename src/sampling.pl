:- op(600, xfx, ::).

% TODO: base case
sampling(Head) :-
    % get all probability-head pairs
    Head =.. [Functor|ArgsL],
    findall(Prob::Head, Prob::Head, ProbHeadPairs),
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

% sampling(q(X)) ===> eher b
% random testing: a: 5x, b: 72x

0.1 :: q(a).
0.9 :: q(b).
0.3 :: p(x).

