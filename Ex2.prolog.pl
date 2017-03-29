% -------------   1º Exercício em Grupo  -------------------
% Grupo: João Coelho, José Silva, Luís Fernandes, Pedro Cunha
%         (A74859),    (A74601),    (A74748),      (A73958)


:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

:- op( 900,xfy,'::' ).
:- dynamic utente/5.
:- dynamic cuidadoPrestado/4.
:- dynamic atoMedico/4.
:- dynamic medico/5.
:- dynamic enfermeiro/5.
:- dynamic turno/3.
:- dynamic destacamento/3.
:- dynamic transplante/2.

% ----------------------------------------------------------
%  Extensão do predicado utente: IdUt, Nome, Idade, Sexo, Morada -> {V, F}

utente( 1, joao, 20, masculino, 'vila verde' ).
utente( 2, jose, 20, masculino, 'lousada' ).
utente( 3, josefina, 34, feminino, 'aveiro' ).
utente( 4, luis, 20, masculino, 'vila das aves' ).
utente( 5, pedro, 20, masculino, 'felgueiras' ).

excecao( utente( 6,ze,34,masculino,'santa cona do assobio' ) ).


% Invariante Estrutural (Alínea 1) e 9))
% Garantia de unicidade nos Ids dos utentes
+utente( IdUt,Nome,Idade,Sexo,Morada ) :: ( solucoes( (IdUt), utente(IdUt,N,I,Se,M), S ),
					                      comprimento( S,N ),
					                      N == 1 ).

% Invariante Referencial
% Não é possível a remoção de utentes se houver algum Ato Nédico para este
-utente( IdUt,Nome,Idade,Sexo,Morada ) :: ( solucoes( (IdUt), atoMedico( Data,IdUt,IdServ,Custo ), S ),
									      comprimento( S,N ),
									      N == 0 ).

% ----------------------------------------------------------
%  Extensão do predicado cuidadoPrestado: IdServ, Descrição, Instituição, Cidade -> {V, F}

cuidadoPrestado( 1, 'Medicina Familiar', 'Centro de Saude de Vila Verde', 'Vila Verde').
cuidadoPrestado( 2, 'Radiologia', 'Hospital Sao Joao', 'Porto').
cuidadoPrestado( 3, 'Medicina Familiar', 'Centro de Saude de Lousada', 'Lousada').
cuidadoPrestado( 4, 'Medicina Familiar', 'Centro de Saude de Felgueiras', 'Felgueiras').
cuidadoPrestado( 5, 'Ginecologia', 'Hospital de Braga', 'Braga').
cuidadoPrestado( 6, 'Obstetricia', 'Hospital de Braga', 'Braga').


% Invariante Estrutural (Alínea 1) e 9))

% Garantia de unicidade nos Ids dos Serviços
+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (IdServ), cuidadoPrestado(IdServ,D,I,C), S ),
					           comprimento( S,N ),
					           N == 1 ).

% Apenas é possível a inserção de um Serviço numa certa instituição uma vez
+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (Desc,Inst), cuidadoPrestado(V,Desc,Inst,C), S ),
							   comprimento( S, N),
							   N == 1 ).

% Invariante Referencial

% Não é possível a remoção de Serviços se houver algum Ato Nédico marcado que o use
-cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (IdServ), atoMedico( Data,IdUt,IdServ,Custo ), S ),
									        comprimento( S,N ),
									        N == 0 ).

% ----------------------------------------------------------
%  Extensão do predicado atoMedico: Data, IdUt, IdServ, Custo -> {V, F}

atoMedico( '14-03-2017', 1, 5, 30 ).
atoMedico( '12-03-2017', 3, 2, 20 ).
atoMedico( '13-12-2017', 4, 2, 10 ).
atoMedico( '13-03-2017', 5, 4, 5 ).
atoMedico( '14-03-2017', 2, 3, 5 ).
atoMedico( '04-04-2017', 1, 3, 7 ).

% Invariante Estrutural (Alínea 1) e 9))

% Apenas é possível inserir um atoMedico em que o IdUt esteja registado nos Utentes e
% o IdServ esteja registado nos Cuidados Prestados
+atoMedico( Data,IdUt,IdServ,Custo ) :: ( solucoes( (IdUt), utente( IdUt,Nome,Idade,Sexo,Morada ), S1 ),
										comprimento( S1,N1 ), 
										N1 == 1,
										solucoes( (IdServ), cuidadoPrestado( IdServ,Descricao,Instituicao,Cidade ), S2 ),
										comprimento( S2,N2 ),
										N2 == 1 ).


% --------------------- Predicados auxiliares ----------------------

% Predicado solucoes: F, Q, S -> {V,F}

solucoes(T,Q,S) :- Q, assert(tmp(T)), fail.
solucoes(T,Q,S) :- construir(S, []).

construir(S1, S2) :- retract(tmp(X)),
					 !,
					 construir(S1, [X|S2]).
construir(S, S).


comprimento( [], 0 ).
comprimento( [X|T], R ) :- comprimento(T,N),
						   R is N+1.

% evolucao: F -> {V,F,D}


% testar: L -> {V,F,D}
testar([]).
testar([I|Li]) :- I,
				  testar(Li).


% involucao: F -> {V,F}
involucao( F ) :- solucoes(I, -F::I, Li),
			      retract(F),
			      testar(Li).
involucao( F ) :- assert( F ),
				  !,
				  fail.

% Extensao do meta-predicado nao: Questao -> {V,F}

nao( Questao ) :-
    Questao, !, fail.
nao( Questao ).

% Extensao do meta-predicado demo: Questao,Resposta -> {V,F,D}

demo(Questao,verdadeiro) :-
    Questao.
demo(Questao, falso) :-
    -Questao.
demo(Questao,desconhecido) :-
    nao(Questao),
    nao(-Questao).


% Extensao do meta-predicado demoLista: [Questao],[Resposta] -> {V,F,D}

demoLista( [],[] ).
demoLista( [X|L],[R|S] ) :-
	demo( X,R ),
	demoLista( L,S ). 


demoConj( [],verdadeiro ).
demoConj( [Q1|Q2],R ) :- demo( Q1,R1 ),
					     demoConj( Q2,R2 ),
					     conjuncao( R1,R2,R ).

conjuncao( verdadeiro,verdadeiro,verdadeiro ).
conjuncao( verdadeiro,falso,falso ).
conjuncao( verdadeiro,desconhecido,desconhecido ).
conjuncao( falso,falso,falso ).
conjuncao( falso,verdadeiro,falso ).
conjuncao( falso,desconhecido,falso ).
conjuncao( desconhecido,verdadeiro,desconhecido ).
conjuncao( desconhecido,falso,falso ).
conjuncao( desconhecido,desconhecido,desconhecido ).


demoDisj( [],falso ).
demoDisj( [Q1|Q2],R ) :- demo( Q1,R1 ),
					     demoDisj( Q2,R2 ),
					     disjuncao( R1,R2,R ).

disjuncao( verdadeiro,verdadeiro,verdadeiro ).
disjuncao( verdadeiro,falso,verdadeiro ).
disjuncao( verdadeiro,desconhecido,verdadeiro ).
disjuncao( falso,falso,falso ).
disjuncao( falso,verdadeiro,verdadeiro ).
disjuncao( falso,desconhecido,desconhecido ).
disjuncao( desconhecido,verdadeiro,verdadeiro ).
disjuncao( desconhecido,falso,desconhecido ).
disjuncao( desconhecido,desconhecido,desconhecido ).


% ----------------------------------------------------------------------
% ----------------------- Trabalho de Grupo 2 --------------------------

% Admissão do pressuposto do mundo fechado para o predicado utente

-utente(Id,N,I,S,C) :- 
	nao(utente(Id,N,I,S,C)),
	nao(excecao(utente(Id,N,I,S,C))).


% Inserção de Conhecimento Negativo

%-cuidadoPrestado(  ).
%-cuidadoPrestado(  ).
%-cuidadoPrestado(  ).






