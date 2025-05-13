%Authors:
%Sebastián David Moreno Expósito; sebastian.exposito@udc.es
%Xoel Sánchez Dacoba; xoel.sanchez.dacoba@udc.es

%This was copied from the tab.pl file uploaded by the teacher.
%------------------------------------------------------------
%the implication is already defined in prolog "->" with a precedence of 1050. And we must use it.
%"yfx" asociatividad por la izquierda
:- op(599, yfx, v).       % disyunción
:- op(400, yfx, &).       % conjunción
:- op(200, fy, -).        % negación
:- op(1070, xfy, <-->).    % bicondicional  - the precedence of the bicondicional must be highter than the implication to satisfy the order of execution of logical operators.

% '=' tiene una precedencia de 700, si a algún operador le pones una precedencia mayor entonces "=" se ejecutará primero, o sea, va a intentar igualar F a una estructura que aún
% no está definida, para resolver este problema hemos de usar paréntesis en estos casos: F = (A -> B) por ejemplo.

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
tab_([F v G|L],B,Bn) :- tab_([F|L],B,Bn); tab_([G|L],B,Bn).
tab_([- (F & G)|L],B,Bn) :- tab_([- F|L],B,Bn); tab_([- G|L],B,Bn).  % negated and is or of the negations
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
unfold(F, Unfolded) :- %base-case and also manage the "-" (applied in literal) because of the implementation of literal_/1 predicate.
    literal_(F),
    !,
    Unfolded = F.

%-: 
unfold(F,Unfolded) :- %"A" could be a formula like: p -> q, so this rule is to address the problem when we have the negation of a non-literal like that.
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

:- dynamic minterm/3.
minterms([]).%quite simple function here
minterms([Model|Rest]) :-
    assertz(minterm([Model], Model, 1)), %As said in the material, this creates kind of a table with the models, 
    %all being minterm(ID,Model,size)
    %ID is the ID of the model, first model is itslf, as we proccess quine-mccluskey the id will merge with other ones for example:
    %the model with id[[a, -b, c, -d], [a, b, c, -d]] will contain the merge of the two models as [a,c,-d]
    %size refers to the amount of models it covers, firstly is 1, but when we merge two models, the size will be 2 and so on.
    minterms(Rest).

min_set_cover(MinimalSets) :- %This is the main predicate to get the minimum set of implicants that cover all the models.
    findall((Id, Implicant), minterm(Id, Implicant, _), PrimeImplicants),
    findall(Model, minterm([Model], _, _), Models),
    findall(Set, covers_all(PrimeImplicants, Models, Set), AllCovers),
    minimal_sets(AllCovers, MinimalSets).

covers_all(PrimeImplicants, Models, Set) :-%This is to generate the subsets of implicants that cover all the models
    subset(Set, PrimeImplicants), 
    covers(Set, Models).          

covers(Set, Models) :- % This is to check if the implicants cover all the models as to generate the subsets 
    findall(Model, (member((_, Implicant), Set), covers_model(Implicant, Model)), CoveredModels),
    sort(CoveredModels, CoveredModelsSorted),
    sort(Models, ModelsSorted),
    CoveredModelsSorted == ModelsSorted.

covers_model(Implicant, Model) :- %This is to check if the implicant covers the model, is the particular case of the previous predicate definition
    forall(member(Literal, Model), member(Literal, Implicant)).

minimal_sets(AllCovers, MinimalSets) :- %This is to filter the subsets by size(Remember that we are looking for the minimum ones as to try 
%to minimize the implicants that cover the most models possible)
    findall(Length-Set, (member(Set, AllCovers), length(Set, Length)), LengthSets),
    sort(LengthSets, [MinLength-_|_]),
    findall(Set, member(MinLength-Set, LengthSets), MinimalSets).



% filepath: ["c:/Users/usuario/Desktop/pract2.pl"].
% This is a test just for you to see Sebas, use it as you please and then delete it
%so yeah, this doesn't work, we'll figure somethiung out or else i'll just kill myself.
%Currently the output is:
/*
27 ?- test_min_set_cover.
FÃ³rmula desplegada:
- (-a v b v (-c v d)&(-d v c))v d
Modelos generados:
[a,-b,c,-d]
Implicantes primos:
[([a],a,1),([-b],-b,1),([c],c,1),([-d],-d,1),([a],a,1),([-b],-b,1),([c],c,1),([-d],-d,1),([a],a,1),([-b],-b,1),([c],c,1),([-d],-d,1),([a],a,1),([-b],-b,1),([c],c,1),([-d],-d,1)]
*/
test_min_set_cover :-
    Formula = ((a -> b) v (c <--> d) -> d),
    unfold(Formula, UnfoldedFormula),
    writeln('Fórmula desplegada:'),
    writeln(UnfoldedFormula),
    tab_([UnfoldedFormula], [], Models),
    writeln('Modelos generados:'),
    writeln(Models),
    minterms(Models),
    writeln('Implicantes primos:'),
    findall((Id, Implicant, Size), minterm(Id, Implicant, Size), PrimeImplicants),
    writeln(PrimeImplicants),
    min_set_cover(MinimalSets),
    writeln('Cobertura mínima:'),
    writeln(MinimalSets).
