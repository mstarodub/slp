0.6 :: q(X).
0.2 :: q(a).
% we have implicit failure, so, additionally:
% 0.2 :: q(X) :- fail.
% each functor's probability labels must sum to 1
% <1: implicit failure
% >1: error out

5/10 :: qq(a).
3/10 :: qq(b).

0.5 :: st2(X) :- stt2(X).
0.5 :: st2(X) :- sst3(X).
1/2 :: sst2(X) :- fail.
1/2 :: sst2(a).
1/2 :: sst3(b).
1/2 :: sst3(c).

% --------------------

% inference: marginal
% forall X. what is P such that q(X) terminates successfully
% implementation: summation over bindings yields the denominator z in Cussen's p (for ground queries; for non-ground it [check this] corresponds to the denominator)
% API: inference_marginal(q(X), P).
% ---> X = <binding>, P = <number>
% inference_marginal(q(X), P).
% ---> X = Omega - {a}, P = 0.6.
% ---> X = a, P = 0.8
% inference_marginal(qq(X), P).
% ---> X = a, P = 5/10.
% ---> X = b, P = 3/10.
% [inference_marginal(q(a), P).
% ---> P = 0.8.] <- the case where the query is ground is always determined by the corresponding result in the non-ground case

% --------------------

% inference: success-constrained
% Given q(X) terminates successfully, what is the probability distribution of X as a random variable
% this is just the P's for each variable binding.
% implementation: Cussen's p
%   the denominator z(q(X), P) gives P = 0.8 because [check this] that is the required normalization weight for the correct final result
% inference_sc(q(X), P).
% ---> X = a, P = 1
% inference_sc(qq(X), P).
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
