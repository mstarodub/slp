% TODO
% M remove writeln calls
% M sample_UC sometimes errors for compound:
%   sample_UC((s(X,Y), r(Y,Z))).
% M sample_SC always errors for compound:
%   sample_SC((s(X,Y), r(Y,Z))).
% M sample_SC/UC(s(X,Y)). sometimes errors
% M test sample_SC for nonground + ground with arity >= 1
% M sample_SC may need cuts
% ? twice repeated output of P=1 for inference_SC_test(dq(a),P) --> too many choice points left

% wip/important
% * sample_SC sometimes errors for goals with shared vars:
%   sample_SC((s(X,Y), r(Y,Z))).
% solution: do those cases with retrying variant of loglinear UC sampling

% * sample_SC insufficiently binds outputs when denom gets recalculated
% * sample_SC has spurious backtracking in denom recalculation case
% ?- sample_SC((s(X,Y), r(Z,W))).
% 0.95
% Z = a,
% W = b .
% ?- sample_SC(r(b,W)).
% 0.19999999999999996 (===0.2)

% * sample_SC cant just assert / retract at will, it doesnt work
% sample_SC(r(b,W)).
% --> sum_remaining computes 0.2
% now we mustnt assert the below, because that changes semantics
% --> assertz((1::r(b, _292):-p(_292))
% instead, it now says r doesnt sum to 1 with check_unitarity!

% R demo / tests
% M remove denom writeln call
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

% Test for demo showcasing scope of project
%
% requiring both unifSet_rec and substitSet_rec for optimised inference
% compound and non-compound goals
% ground, partially ground and free goals
% dependent and independent goals
% backtracking only for top level; also backtracking for body level
%



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
