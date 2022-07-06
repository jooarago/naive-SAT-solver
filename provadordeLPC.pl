/* - - - - - - - - - - - - - - - - - - - - - - - - - - -
	    PREDICADOS DINAMICOS E OPERADORES
- - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- dynamic res/3.

:- dynamic clause/1.

:- dynamic resnum/1.

:- dynamic num/1.

:- dynamic clausenum/2.

:- op( 100, fy, ~ ).
:- op( 110, xfy, & ).
:- op( 120, xfy, v ).
:- op( 130, xfy, => ).
:- op( 140, xfy, <=>).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - -
	          PREDICADOS AUXILIARES
- - - - - - - - - - - - - - - - - - - - - - - - - - - */

%predicado retirado do stackoverflow para checar se duas listas possuem os mesmos elementos.

mesmos_elementos(X,Y) :- msort(X,S), msort(Y,S).


% assertclausenum/0 enumera clausulas novas

assertclausenum(Formula) :- clausenum(Formula,_), !.

assertclausenum(Formula) :- increasen(), num(Num), assert(clausenum(Formula,Num)).


% assertres/0 registra os pais de clausulas novas

assertres(_,_,R) :- res(_,_,R),!.

assertres(X,Y,R) :- assert(res(X,Y,R)).


% resnum/1 funciona como uma variavel global, e serve para contar quantas vezes a resolucao varre as clausulas

resnum(0).

increasern() :- resnum(X), Y is X+1, retractall(resnum(_)), assert(resnum(Y)).

resetrn() :- retractall(resnum(_)), assert(resnum(0)).


% num/1 funciona como uma variavel global, e serve para enumerar clausulas

num(0).

increasen() :- num(X), Y is X+1, retractall(num(_)), assert(num(Y)).

resetn() :- retractall(num(_)), assert(num(0)).


% reiniciar/0 retira fatos dinamicamente assertados ou os reseta

reiniciar() :- retractall(clause(_)), retractall(res(_,_,_)), resetn(), retractall(clausenum(_,_)).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - -
	    TRANSFORMACAO E ASSERCAO DE FORMULAS
- - - - - - - - - - - - - - - - - - - - - - - - - - - */

translate( F & G ) :- !,
    translate( F ),
    translate( G ).

translate(Formula) :-
    transform( Formula, NewFormula), !,
    translate( NewFormula).

translate( Formula) :-
     flnalon(Formula, L), list_to_set(L, NewL), msort(NewL, NewNewL), clause(NewNewL),!.

translate(Formula):-
	flnalon(Formula, L), list_to_set(L, NewL),taut(NewL),!.

%com assertclausenum tá dando problema.

translate(Formula):-
	flnalon(Formula, L), list_to_set(L, NewL), msort(NewL, NewNewL), assert(clause(NewNewL)), increasen(), num(Num), assert(clausenum(NewNewL, Num)),!.

translate(_).

% Eliminating double negations

transform( ~(~X), X) :- !.

% Eliminating implications

transform( X => Y, ~X v Y) :- !.

% Eliminating bi-implications.

transform( X <=> Y, (~X v Y) & (~Y v X) ) :- !.

% de Morgan

transform( ~( X & Y), ~X v ~Y) :- !.
transform( ~( X v Y), ~X & ~Y) :- !.

% Distribution

transform( X & Y v Z, (X v Z) & ( Y v Z)) :- !.
transform( X v Y & Z, ( X v Y) & ( X v Z) ) :- !.

% transforming sub-expressions:

transform( X v Y, X1 v Y) :-
    transform( X, X1), !.

transform( X v Y, X v Y1):-
    transform( Y, Y1), !.

transform( ~X, ~X1) :-
    transform( X, X1).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - -
     ALGORITMOS DE RESOLUCAO E VISUALIZACAO DE PROVA
- - - - - - - - - - - - - - - - - - - - - - - - - - - */

% flnalon/2 transforma clausulas em listas

flnalon(X,X) :- is_list(X),!. %listas são mantidas identicas

flnalon(X v Y, L):- flnalon(X,L2), flnalon(Y,L3), append(L2,L3,L).

flnalon(X, [X]).


% taut/1 checa se lista constitui tautologia

taut([]):-fail,!.

taut([~X|L]):-member(X,L),!.

taut([X|L]):-member(~X,L),!.

taut([_|L]):-taut(L).


% simplifica/2 simplifica listas (retira literais e suas negações) (não é usado no programa)

simplifica(L, L) :- not(taut(L)), !.

simplifica(L1, R) :-
	member(X, L1), member(~X, L1),!,subtract(L1, [X, ~X], Raux), simplifica(Raux, R).


% resolve/3 faz resolucao de duas clausulas

resolve(C1, C2, R) :-
	member(X, C1), member(~X, C2), append(C1, C2, Raux1), list_to_set(Raux1, Raux2), subtract(Raux2, [X, ~X], R).

resolve(C1, C2, R) :-
	member(~X, C1), member(X, C2), append(C1, C2, Raux1), list_to_set(Raux1, Raux2), subtract(Raux2, [X, ~X], R).


% resolucaoaux/0 aplica resolucao em largura em todas as clausulas ja assertadas. falha quando nao e mais possível fazer qualquer resolucao.

resolucaoaux() :- clause(X), clause(Y), append(X, Y, Raux1), taut(Raux1), resolve(X, Y, R), msort(R, NewR), not(clause(NewR)), not(taut(NewR)) ,translate(NewR), assertres(X,Y,NewR).


% resolucaoaux2/0 realiza resolucao ate nao ser mais possivel resolver qualquer duas clausulas. mostra quantas vezes resolucaoaux/0 foi chamado.

resolucaoaux2():- repeat, (resolucaoaux() -> increasern(), fail; resnum(X), write('a resolucao varreu as clausulas '), write(X), write(' vez(es)! e depois nao teve mais o que fazer!'), nl, resetrn(), !).


% resolucao/0 implementa o algoritmo de resolucao e diz se o conjunto de premissas e satisfativel ou nao.

resolucao() :- resolucaoaux2(), clause([]), write('O CONJUNTO DE PREMISSAS E INSATISFATIVEL.'),!.

resolucao() :- write('O CONJUNTO DE PREMISSAS E SATISFATIVEL').


% prova2/0 e predicado auxiliar para a visualizacao da linha de deducao

prova2() :-
    clause(R), not(res(_,_,R)), clausenum(R, Num), write(Num), write(' '), write(R), write(', premissa'), nl.

prova2() :-
	clause(R), res(X, Y, R), clausenum(X, NumX), clausenum(Y, NumY), clausenum(R, NumR), write(NumR), write(' '), write(R), write(', RES '), write(NumX), write(', '), write(NumY), nl.


% mostrarprova2/0 mostra uma linha de deducao baseada no que o algoritmo de resolucao fez

mostrarprova2() :- prova2(), fail.

mostrarprova2() :- true.


%solve/1 verifica se uma formula tomada isoladamente e satisfatível ou insatisfativel, e mostra prova.

solve(X) :- reiniciar(), translate(X),!, resolucao(), nl, mostrarprova2(),!.


/*

- - - - - - - - - - - - - - - - - - - - - - -
	     EXEMPLOS PARA TESTE
- - - - - - - - - - - - - - - - - - - - - - -

Copie e cole!

1 solve( ~(((p=>q)=>p)=>p) ).

2 solve( (p v ~ p) => (q & ~ q) ).

3 solve( ~( (p=>q) <=> (~q => ~p) ) ).

4 solve(  ~( (p=>q) <=> (q=>p) )      ).

*/
