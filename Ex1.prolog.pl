% -------------   1º Exercício em Grupo  -------------------
% Grupo: João Coelho, José Silva, Luís Fernandes, Pedro Cunha
%         (A74859),    (A74601),    (A74748),      (A73958)


:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

:- op( 900,xfy,'::' ).
:- dynamic utente/4.

% ----------------------------------------------------------
%  Extensão do predicado utente: IdUt, Nome, Idade, Morada -> {V, F}

%utente( N, X, Y, Z ) :- nome( X ),
%						idade( X, Y ),
%						morada( X, Z ).

utente( 1,joao,20,'vila verde' ).
utente( 2,jose,20,'lousada' ).
utente( 3,luis,20,'vila das aves' ).
utente( 4,pedro,20,'felgueiras' ).


% Invariante Estrutural

+utente( Valor,Nome,Idade,Morada ) :: ( solucoes( (Valor), utente(Valor,N,I,M), S),
					                  comprimento( S,X ),
					                  X == 1).



% ----------------------------------------------------------
%  Extensão do predicado cuidadoPrestado: IdServ, Descrição, Instituição, Cidade -> {V, F}

cuidadoPrestado( 1, 'Medicina Familiar', 'Centro de Saude', 'Vila Verde').
cuidadoPrestado( 2, 'Radiologia', 'Hospital', 'Porto').
cuidadoPrestado( 3, 'Medicina Familiar', 'Centro de Saude', 'Lousada').
cuidadoPrestado( 4, 'Medicina Familiar', 'Centro de Saude', 'Felgueiras').
cuidadoPrestado( 5, 'Ginecologia', 'Hospital', 'Braga').


% Invariante Estrutural
+cuidadoPrestado( V,D,I,C ) :: ( solucoes( (V), cuidadoPrestado(V,D,I,C), S),
					           comprimento( S,X ),
					           X == 1).


% ----------------------------------------------------------
%  Extensão do predicado atoMedico: Data, IdUt, IdServ, Custo -> {V, F}

atoMedico( '14-03-2017', 1, 5, 30 ).
atoMedico( '12-03-2017', 3, 2, 20 ).
atoMedico( '13-03-2017', 4, 4, 5 ).
atoMedico( '14-03-2017', 2, 3, 5 ).


% Extensao do predicado nome: Nome -> {V, F}
%nome( joao ).
%nome( jose ).
%nome( luis ).
%nome( pedro ).

% Extensao do predicado idade: Nome, Idade -> {V, F}
%idade( joao, 20 ).
%idade( jose, 20 ).
%idade( luis, 20 ).
%idade( pedro, 20 ).

% Extensao do predicado morada: Nome, Morada -> {V, F}
%morada( joao, 'vila verde' ).
%morada( jose, 'lousada' ).
%morada( luis, 'vila das aves' ).
%morada( pedro, 'felgueiras' ).

% --------------------- Predicados auxiliares ----------------------

% Predicado solucoes: F, Q, S -> {V,F}

solucoes(T,Q,S) :- Q, assert(tmp(F)), fail.
solucoes(T,Q,S) :- construir(S, []).

construir(S1, S2) :- retract(tmp(X)),
					 !,
					 construir(S, [X|S2]).
construir(S, S).


comprimento( [], 0 ).
comprimento( [X|T], R ) :- comprimento(T,N),
						   R is N+1.

% evolucao: F -> {V,F}
evolucao( F ) :- solucoes(I, +F::I, Li),
			     assert(F),
			     testar(Li).
evolucao( F ) :- retract( F ),
				 !,
				 fail.

% inserir: F -> {V,F}
%inserir( F ) :- assert(F).
%inserir( F ) :- retract(F),
%			    insucesso.    % insucesso == !, fail

% testar: L -> {V,F}
testar([]).
testar([I|Li]) :- I,
				  testar(Li).

% involucao: F -> {V,F}
involucao( F ) :- solucoes(I, -F::I, Li),
			      retract(F),
			      testar(Li).