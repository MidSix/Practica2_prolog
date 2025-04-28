%This was copied from the tab.pl file uploaded by the teacher.
%------------------------------------------------------------
%the implication is already defined in prolog "->" with a precedence of 1050. And we must use it.
%"yfx" asociatividad por la izquierda
:- op(599, yfx, v).       % disyunción
:- op(400, yfx, &).       % conjunción
:- op(200, fy, -).        % negación
:- op(670, yfx, <-->).    % bicondicional  - the precedence of the bicondicional must be highter than the implication to satisfy the order of execution of logical operators.

% '=' tiene una precedencia de 700, si a algún operador le pones una precedencia mayor entonces "="" se ejecutará primero, o sea, va a intentar igualar F a una estructura que aún
% no está definida, por eso todos están debajo de 700, aunque si quisiera ponerlos por encima se podría, pero habría que poner paréntesis para especificar qué quieres que
%se ejecute primero eso y luego igualar F a ello.

literal_(L) :- atom(L).
literal_(- L) :- atom(L).
compl_(- A,A) :- !.
compl_(A, - A).

% Treats the list where the element is inserted as a set
% where an atom and its negation can- be in the set together.
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
% Does - insert complementary literals in the B (B1) list.

tab_([- - F|L],B,Bn) :- tab_([F|L],B,Bn).  % - -
tab_([F v G|L],B,Bn) :- tab_([F|L],B,Bn); tab_([G|L],B,Bn).  %
tab_([- (F & G)|L],B,Bn) :- tab_([- F|L],B,Bn),!; tab_([- G|L],B,Bn).  % negated and is or of the negations
tab_([F & G|L],B,Bn) :- tab_([F,G|L],B,Bn).
tab_([- (F v G) |L],B,Bn) :- tab_([- F,- G|L],B,Bn).  % negated or is and of the negations


%%%% Obtains the dfn of a formula from a list of clauses
toclause([A],A):-!.
toclause([A|As],A & G):- toclause(As,G).

todnf([A],F) :- !, toclause(A,F).
todnf([A|As],F v G) :- toclause(A,F), todnf(As,G).


%% Example of use:
%?- F = (a v b) & (- b & (c v - a)) v (a & b), tab_([F], [], B), todnf([B], DNF).
%F = (a v b)&(- b&(c v - a))v a&b,
%B = [a, - b, c],
%DNF = a&(- b&c) ;
%F = (a v b)&(- b&(c v - a))v a&b,
%B = [a, b],
%DNF = a&b.
%------------------------------------------------------------

%from here is our code:

%first stage:
%Implementation of unfold/2 predicate
%------------------------------------------------------------
%usage example:
/*
    unfold(((a -> b) v (c <--> d) -> d), F)
    as first argument the raw formula and this will return F.
    Being F the unfolded formula(without implication and biconditional)
*/
unfold(F, Unfolded) :- %base-case and also manage the "-" operator because of the implementation of literal_/1 predicate.
    literal_(F),
    !,
    Unfolded = F.

%-:
unfold(F,Unfolded) :-
    F = -(A),
    unfold(A, A_unfolded),
    Unfolded = -(A_unfolded).

% or:
unfold(F, Unfolded) :-
    F = A v B,
    unfold(A, A_unfolded),
    unfold(B, B_unfolded),
    Unfolded = A_unfolded v B_unfolded. % This term won't execute until the previous terms of the body rule are unified/satisfied.

% and:
unfold(F, Unfolded) :-
    F = A & B,
    unfold(A, A_unfolded),
    unfold(B, B_unfolded),
    Unfolded = A_unfolded & B_unfolded.

% implication:
unfold(F, Unfolded) :-
    F = (A -> B),
    unfold(A, A_unfolded),
    unfold(B, B_unfolded),
    Unfolded = - A_unfolded v B_unfolded.

% biconditional
unfold(F, Unfolded) :-
    F = (A <--> B),
    unfold(A, A_unfolded),
    unfold(B, B_unfolded),
    Unfolded = (- A_unfolded v B_unfolded) & (- B_unfolded v A_unfolded).
%------------------------------------------------------------

%Second stage:
%is basically understand how to use tab_ and what returns exactly.

%------------------------------------------------------------
%summary:
/*
    returns the open branches of the semantic table related to the unfolded formula we passed.
    the open branches are the models of the formula.
    models are interpretations that makes the formula true.
    interpretations are every single row of a classic true table.

    example output:
    B = [a, -b, c, -d], B stands for branch. Inside the list we have every single literal that must be true
    in order that the formula becomes true.

    You can prove this either by asking chatgpt to make the semantic table of the formula step-by-step or
    just writing it by yourself.

    usage example:
    unfold(((a -> b) v (c <--> d) -> d), F), tab_([F], [], B).
    first unfold the formula that will be stored in F. and then pass F as an argument to tab_. That's all.

Second stage finished.
*/
%------------------------------------------------------------

%Third stage:
%implementation of the diabolical Quine-McCluskey. Seems hard.


