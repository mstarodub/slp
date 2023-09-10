suess(Apfel) :- Apfel, rot(Apfel).

elstar.
boskop.
goldendelicious.
goldparmaene.

rot(elstar).
rot(goldparmaene).

p(a, b).
p(b, x).
q(b).
r(a, a).
r(c, d).



u(X, Y, Z) :- p(X, Y), q(X), r(Z, Z).

exists_member([], V2, noSharing).
exists_member([Head|Tail], V2, R) :-
    ( member(Head, V2)
    -> R = sharing
    ; exists_member(Tail, V2, R) ).


var_equal(G, RG13, RG12, RG23, RG2G3) :-
    numbervars(G, 0, End),
    (G1, G2, G3) = G,
    varnumbers(G1, G1Free),
    term_variables(G1Free, G1Vars),
    term_variables(G2, G2Vars),
    term_variables(G3, G3Vars),
    term_variables((G2,G3), G2G3Vars),
    exists_member(G1Vars, G3Vars, RG13),
    exists_member(G1Vars, G2Vars, RG12),
    exists_member(G2Vars, G3Vars, RG23),
    exists_member(G1Vars, G2G3Vars, RG2G3).

var_equal(G, G1Shared, G2Shared, G3Shared) :-
    (G1, G2, G3) = G,
    sub_term_shared_variables(G1, G, G1Shared),
    sub_term_shared_variables(G2, G, G2Shared),
    sub_term_shared_variables(G3, G, G3Shared).

% rough idea: If GxShared is empty, do recursive splitting as before, i.e. z(G1), z(G\G1) and multiply
% otherwise: work with list of subgoals!
%   append new (possibly instantiated) body to list (e.g. as head, order not relevant as we only consider conjunctions so far)
%   find all subgoals in list sharing the same variable and assign same instantiation to them
%   call z(transformed_goal) where transformed goal comprises the body replacement and instantiation changes

    



    
    