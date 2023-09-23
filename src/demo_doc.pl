% TODO
% R rounding inconsistent for s(a,b),r(b,b) between inference_SC and inference_SC_unoptim
% M take another look at substit_rec, unifset_rec - why does unifset_rec unification never happen but for true = true?
% M remove writeln calls
% M sample_UC sometimes errors for compound:
%   sample_UC((s(X,Y), r(Y,Z))).
% M sample_SC always errors for compound:
%   sample_SC((s(X,Y), r(Y,Z))).
% M sample_SC/UC(s(X,Y)). sometimes errors
% M test sample_SC for nonground + ground with arity >= 1
% M sample_SC may need cuts
% R inference may need reintroduction of previous cuts
% ? BUG: p(cmp1(b), P). -> zero divisor
% ? twice repeated output of P=1 for inference_SC_test(dq(a),P).
% ? no backtracking for inference_SC(cmp(X),P). (however, backtracking for G = s(X,Y), r(Y,Z) works...)
% ? motivate p/3 with a test case
% ? backtracking for inference: test functionality scope of current implementation
% R demo / tests
% M err if a functor's labels sum to >1'
% M sampling/inference (SC, UC): uniform output for goals that don't exist
% M special sampling with SC inference

% - nested functors: st(dqq(X)) : inference, sampling
% - impure
% - disjunction

0.6 :: dq(X).
0.2 :: dq(a).
% we have implicit failure, so, additionally:
% 0.2 :: dq(X) :- fail.
% each functor's probability labels must sum to 1
% <1: implicit failure
% >1: error out

5/10 :: dqq(a).
3/10 :: dqq(b).

0.5 :: st2(X) :- stt2(X).
0.5 :: st2(X) :- sst3(X).
1/2 :: sst2(X) :- fail.
1/2 :: sst2(a).
1/2 :: sst3(b).
1/2 :: sst3(c).



% --------------------

% inference: marginal
% forall X. what is P such that dq(X) terminates successfully
% implementation: summation over bindings yields the denominator z in Cussen's p (for ground queries; for non-ground it [check this] corresponds to the denominator)
% API: inference_marginal(dq(X), P).
% ---> X = <binding>, P = <number>
% inference_marginal(dq(X), P).
% ---> X = Omega - {a}, P = 0.6.
% ---> X = a, P = 0.8
% inference_marginal(dq(b), P).
% ---> X = b, P = 0.6
% inference_marginal(dqq(X), P).
% ---> X = a, P = 5/10.
% ---> X = b, P = 3/10.
% [inference_marginal(dq(a), P).
% ---> P = 0.8.] <- the case where the query is ground is always determined by the corresponding result in the non-ground case

% --------------------

% inference: success-constrained
% Given dq(X) terminates successfully, what is the probability distribution of X as a random variable
% this is just the P's for each variable binding.
% implementation: Cussen's p
%   the denominator z(dq(X), P) gives P = 0.8 because [check this] that is the required normalization weight for the correct final result
% inference_sc(dq(X), P).
% ---> X = a, P = 1
% inference_sc(dq(b), P).
% ---> X = b, P = 0.75
% inference_sc(dqq(X), P).
% ---> X = a, P = 5/8
% ---> X = b, P = 3/8

% --------------------

% sampling: unconstrained
% sampling_uc(st2(X)).
% ---> X = a, P = 1/2
% ---> X = b, P = 1/4
% ---> X = c, P = 1/4

% --------------------

% sampling: constrained
% sampling_sc(st2(X)).
% ---> X = a, P = 1/3
% ---> X = b, P = 1/3
% ---> X = c, P = 1/3
