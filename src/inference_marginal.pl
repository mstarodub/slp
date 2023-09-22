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


% base case
z(true, 1) :- !. % preventing backtracking to clauses further down

% compound base cases; simplifying conjunction
% preventing backtracking to clauses further down
z((G, true), Weight) :- z(G, Weight), !. % fires for G as body of a non-compound head
z((true, G), Weight) :- z(G, Weight), !.

% compound head
z((G1, G2), Weight) :-
    G1 \= true, % mutual exclusivity of goals
    %optimised z computation (with var Depth)
    % shared variable test
    sub_term_shared_variables(G1, (G1, G2), SharedVars),
    ( SharedVars = [] 
    % no shared variables --> decomposition
    ->  z(G1, Weight1),
        z(G2, Weight2),
        Weight is Weight1*Weight2
    % shared variables --> computation of splitting substitution set
    ;   % only ground terms make goals disjunct (e.g. we don't want Y=Y)
        % collect all possible values of SharedVars in matching clause heads
        % example: (G1, G2) === (s(X,Y), r(Y,Z))
        % ---> SharedVars = [Y]
        % ---> SubstitList = [[b],[c]]; in each entry list we have the bindings for all shared variables
        findall(SharedVars, (clause((_ :: G1), _), ground(SharedVars)), SubstitList),
        % SubstitSet is Theta, the set of splitting substitutions. in the (s(X,Y), r(Y,Z)) case, a substitution of Y= b or Y= c makes the Variables in G1, G2 disjoint
        list_to_set(SubstitList, SubstitSet),
        % put all possibilities for binding the shared variables into PairedVarBindings
        maplist(unifiable(SharedVars), SubstitSet, PairedVarBindings),
        substitSet_rec(G1, G2, PairedVarBindings, Weight)        
    ),
    !. % preventing backtracking to clauses further down

% non-compound head
z(G, Weight) :-
    % mutual exclusivity of goals
    G \= (_, _),
    G \= true,

    findall([Prob, G, Body], clause((Prob :: G), Body), UnifSet),
    unifSet_rec(G, true, UnifSet, Weight).


%findall([Prob, G1, Body], clause((Prob :: G1), Body), UnifSet),
%        unifSet_rec(G1, G2, UnifSet, Weight, Depth)