:- op(599, yfx, v).     % disyunción
:- op(400, yfx, &).     % conjunción
:- op(200, fy, not).     % negación

literal_(L) :- atom(L).
literal_(not L) :- atom(L).
compl_(not A,A) :- !.
compl_(A, not A).

% Treats the list where the element is inserted as a set
% where an atom and its negation cannot be in the set together.
addlit_(F,[],[F]) :- !.
addlit_(F,[F|L],[F|L]) :- !.
addlit_(F,[G|L],[G|L2]) :- \+ compl_(F,G), addlit_(F,L,L2).

%% tab_(+FormulaList, +AuxList, -ModelList)
% Applies the tabulation method to a list of formulas
% Obtains the list of models of the conjuction of all formulas in FormulaList
% AuxList should be an empty list
% The models are expressed as a list of literals
tab_([],B,B) :- !.
tab_([F|L],B,Bn) :- literal_(F),!,addlit_(F,B,B1),tab_(L,B1,Bn).
% Does not insert complementary literals in the B (B1) list.

tab_([not not F|L],B,Bn) :- tab_([F|L],B,Bn).  % not not
tab_([F v G|L],B,Bn) :- tab_([F|L],B,Bn); tab_([G|L],B,Bn).  %
tab_([not (F & G)|L],B,Bn) :- tab_([not F|L],B,Bn),!; tab_([not G|L],B,Bn).  % negated and is or of the negations
tab_([F & G|L],B,Bn) :- tab_([F,G|L],B,Bn).
tab_([not (F v G) |L],B,Bn) :- tab_([not F,not G|L],B,Bn).  % negated or is and of the negations


%%%% Obtains the dfn of a formula from a list of clauses
toclause([A],A):-!.
toclause([A|As],A & G):- toclause(As,G).

todnf([A],F) :- !, toclause(A,F).
todnf([A|As],F v G) :- toclause(A,F), todnf(As,G).


%% Example of use:
%?- F = (a v b) & (not b & (c v not a)) v (a & b), tab_([F], [], B), todnf([B], DNF).
%F = (a v b)&(not b&(c v not a))v a&b,
%B = [a, not b, c],
%DNF = a&(not b&c) ;
%F = (a v b)&(not b&(c v not a))v a&b,
%B = [a, b],
%DNF = a&b.

