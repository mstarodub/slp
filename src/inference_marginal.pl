% when the VarList is exhausted, set the result to the singe remaining entry in the weight, that entry is the probability
replace_left([], Remains, Remains).
replace_left([NewL|TailNewL], [_=R|Tail], [NewL=R|Res]) :-
    var(NewL),
    replace_left(TailNewL, Tail, Res).
% ignoring already globally bound variables s.t. lenght of binding list [_=R|Tail] equals list of new lefts [NewL|TailNewL]
replace_left([NewL|TailNewL], [_=R|Tail], Res) :-
    nonvar(NewL),
    replace_left(TailNewL, [_=R|Tail], Res).


% example call: inference_marginal((s(X,Y),r(Y,Z)), Prob)
% in the general case, one Variable (TODO: which?) is not part of the list in Weight but rather detemined by backtracking
inference_marginal(Goal, ProbList) :-
% example goal: (s(X,Y), r(Y,Z))
% ---> VarList === [X,Y,Z]
% after z call: VarList === [X,b,Z]
% because of that:
% preserving variable names for pretty output
% TODO: may order of vars in list differ from the order in the output list?
term_variables(Goal, VarList),
z(Goal, Weight), 
% for the example goal of (s(X,Y), r(Y,Z)), we currently have
% Y=b,
% Weight = [[b=b, _=X, 0.14], [c=c, _=a, 0], [b=b, _=b, 0.04]]
% invariant: forall w in Weight. len(VarList - ground terms) === len(w - last element)
% replace_left then takes the variables from VarList and replaces the left hand '=' sides with them in order (for each w in Weight [is a list])
maplist(replace_left(VarList), Weight, ProbList).



findall([Prob, G1, Body], clause((Prob :: G1), Body), UnifSet),
        unifSet_rec(G1, G2, UnifSet, Weight, Depth)