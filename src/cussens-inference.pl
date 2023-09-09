:- op(1199,xfx,::).
:- discontiguous (::)/2.

% meta-assumptions:
%   only conjunctions
%   normalized SLP (all clauses forming a predicate add up to 1)
%   pure SLP (no non-prob. clauses)

% invariant helper
err(X) :-
    % TODO: print an error message
    write(user_error, "broken invariant"),
    halt.

% assumptions:
%   G is the goal with only free variables
%   G is non-compound; TODO: assert user input as clause and retract later
%   ArgList contains the instantiated parameters for G
p(G, ArgList, Result) :-
    functor(G, Functor, Arity),
    ( length(ArgList, Len), Len \= Arity -> err(Len) ; true ),
    GInstantiated =.. [Functor|ArgList],
    z(GInstantiated, Numerator),
    z(G, Denominator),
    Result is Numerator / Denominator.

z(G, Weight) :-
    ...
