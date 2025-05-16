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
%implementation of Quine-McCluskey.(Kind of)
%------------------------------------------------------------

:- dynamic minterm/3.

minterms([]). % Minterms will recieve a list of models, not directly from the tab_ predicate but from the remove_redundant predicate.
minterms([Model|Rest]) :-
    sort_lits(Model, SortedModel), % Sort the model to ensure consistent ordering
    length(SortedModel, Size), % Get the size of the model
    assertz(minterm([SortedModel], SortedModel, Size)), % As said in the material, this creates kind of a table with the models
    %all being minterm(ID,Model,size)
    %ID is the ID of the model, first model is itslf, as we proccess quine-mccluskey the id will merge with other ones for example:
    %the model with id[[a, -b, c, -d], [a, b, c, -d]] will contain the merge of the two models as [a,c,-d])
    %size refers to the amount of literals it contains, so we can use it to merge only with models that have the same size.
    minterms(Rest).

clear_minterms :-
    retractall(minterm(_, _, _)). % Clear the minterms database
% Sorts the literals in a model to ensure consistent ordering, as tab_ does not guarantee the order of literals o_o
sort_lits(Model, SortedModel) :-
    predsort(literal_compare, Model, SortedModel).

literal_compare(Order, X, Y) :-
    base_atom(X, BX),
    base_atom(Y, BY),
    compare(Order, BX, BY).

base_atom(-A, A) :- !.
base_atom(A, A).


remove_redundant([], []). % Removes redundant models: if a model is a superset of another, it is direcly removed.
remove_redundant([M|Ms], Clean) :-
    (member(N, Ms), subset(N, M)) -> remove_redundant(Ms, Clean)
    ; remove_redundant(Ms, Rest), Clean = [M|Rest].

can_merge(Model1, Model2) :- %Returns true if Model1 and Model2 only differ in one literal, and that literal is the same variable with opposite sign
    length(Model1, N),
    length(Model2, N),
    intersection(Model1, Model2, Common),
    length(Common, N1),
    N1 is N - 1,
    subtract(Model1, Common, [Diff1]),
    subtract(Model2, Common, [Diff2]),
    base_atom(Diff1, V),
    base_atom(Diff2, V),
    Diff1 \= Diff2.

merge_literals_set(M1, M2, Common) :- %fuses the two models leaving only the common literals
    intersection(M1, M2, Common).

merge_with_one((ID1, Model1, Size), Ms, (IDF, ModelF, SizeF)) :-%finds a model in the list that can be merged with the given one and returns the merged model
    member((ID2, Model2, Size), Ms),
    can_merge(Model1, Model2),
    merge_models((ID1, Model1, Size), (ID2, Model2, Size), (IDF, ModelF, SizeF)), !.

merge_round([], [], []). % Merging round, as the name says, it will merge the minterms that can be merged(same size and one literal difference)
merge_round([M|Ms], Merged, [M|Unmerged]) :-
    \+ merge_with_one(M, Ms, _), !,
    merge_round(Ms, Merged, Unmerged).
merge_round([M|Ms], [Fusion|Merged], Unmerged) :-
    merge_with_one(M, Ms, Fusion), !,
    Fusion = (IDF, ModelF, SizeF),
    select((ID2, Model2, Size2), Ms, MsRest),
    merge_models(M, (ID2, Model2, Size2), Fusion),
    merge_round(MsRest, Merged, Unmerged).

merge_models((ID1, Model1, _), (ID2, Model2, _), (IDF, ModelF, SizeF)) :-%Modifies the merge_models predicate to use merge_literals_set
    merge_literals_set(Model1, Model2, ModelF),
    append(ID1, ID2, IDF),
    length(ModelF, SizeF).
%------------------------------------------------------------
%summary:
/*
    Firtsly we pass what we got from the tab_ predicate to the remove_redundant predicate so we can introduce directly the models
    into the minterms predicate. The minterms predicate will create a table with the models and their size.
    Then we call the merge_round predicate, this will merge the models that can be merged, and return the merged models.
    
    The merge_round predicate will call the merge_with_one predicate, this will check if the model can be merged with another one.
    If it can be merged, it will call the merge_models predicate, which will merge the two models and return the merged model removing previous models
    from the dynamic predicate minterm/3.
    This process will be repeated until there are no more models that are compatible to be merged, leaving us with the prime implicants in
    the dynamic predicate minterm/3.
    
    Third stage finished.
*/
%------------------------------------------------------------

%Fourth stage:
%Implementation of the prime implicants to DNF conversion to obtain the minimal set cover
%------------------------------------------------------------


min_set_cover(DNF) :-% Translates each minterm in the dynamic table to a conjunction, and returns the DNF 
    findall(Model, minterm(_, Model, _), Models0),
    sort(Models0, Models1),% Sort the models to ensure duplicates are completely removed
    cover_minim(Models1, Models), % Last step to merge the models that are not prime
    maplist(list_to_conjunction, Models, Conjunctions),%Firtsly we convert the models to a list of conjunctions(maplist applies the predicate to each element of the list)
    disjunction_of_list(Conjunctions, DNF),%then we relate each conjunction with the disjunction operator, quite to the point
    clear_minterms.%To avoid problems with the dynamic predicate, we clear after the process


list_to_conjunction([L], LStr) :-% All below is to convert the models to a conjunction, they return a string with the conjunction of the literals
    literal_to_string(L, LStr).%this is because previously we got anidated formulas like a&(-b&(c& -d))v d instead of (a & -b & c & -d) v d,
list_to_conjunction(Lits, F) :-% Although this was correct by the associative property, we wanted the DNF to be more readable.
    maplist(literal_to_string, Lits, StrLits),
    atomic_list_concat(StrLits, ' & ', Inner),
    atom_concat('(', Inner, Temp),
    atom_concat(Temp, ')', F).

literal_to_string(-A, S) :- !,
    atom_string(A, SA),
    string_concat('-', SA, S).
literal_to_string(A, S) :-
    atom(A),
    atom_string(A, S).

disjunction_of_list(List, DNF) :-
    atomic_list_concat(List, ' v ', DNF).
%------------------------------------------------------------
    %Fourth stage finished.
%------------------------------------------------------------

%Fifth stage:
% Implementation of minimize/2 predicate, universal predicate that will be used to minimize the formula
%------------------------------------------------------------

minimize(F, Min) :-
    clear_minterms,
    unfold(F, UnfoldedFormula),
    findall(Model, tab_([UnfoldedFormula], [], Model), Models),
    remove_redundant(Models, CleanModels),
    minterms(CleanModels),
    findall((Id, Implicant, Size), minterm(Id, Implicant, Size), MintermsList),
    merge_round(MintermsList, Merged, Unmerged),
    clear_minterms,
    sort(Merged, MergedNoDup),
    sort(Unmerged, UnmergedNoDup),
    forall(member((Id, Implicant, _), MergedNoDup), (
    length(Implicant, Size),
    assertz(minterm(Id, Implicant, Size))
    )),
    forall(member((Id, Implicant, _), UnmergedNoDup), (
    length(Implicant, Size),
    assertz(minterm(Id, Implicant, Size))
    )),
    min_set_cover(Min), !.

% filepath: ["c:/Users/usuario/Desktop/pract2.pl"].
% This is a test just for you to see Sebas, use it as you please and then delete it(change F value to the one you want to test)
test_code :-
    clear_minterms,
    F = ((a -> b) & (b -> c) & (c <--> d)) v (-a & -d),
    unfold(F, UF),
    writeln('Unfolded: '), writeln(UF),
    findall(Model, tab_([UF], [], Model), Models),
    writeln('Modelos generados: '), writeln(Models),
    remove_redundant(Models, CleanModels),
    writeln('Modelos no redundantes: '), writeln(CleanModels),
    minterms(CleanModels),
    findall((Id, Implicant, Size), minterm(Id, Implicant, Size), MintermsList),
    writeln('Minterms iniciales: '), writeln(MintermsList),
    merge_round(MintermsList, Merged, Unmerged),
    writeln('Merges: '), writeln(Merged),
    writeln('No fusionados: '), writeln(Unmerged),
    clear_minterms,
    forall(member((Id, Implicant, Size), Merged), assertz(minterm(Id, Implicant, Size))),
    forall(member((Id, Implicant, Size), Unmerged), assertz(minterm(Id, Implicant, Size))),
    min_set_cover(Min),
    write('The minimized formula is: '), write(Min), nl.
