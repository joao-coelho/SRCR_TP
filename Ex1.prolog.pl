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

% ----------------------------------------------------------
%  Extensão do predicado utente: IdUt, Nome, Idade, Sexo, Morada -> {V, F}

utente( 1, joao, 20, masculino, 'vila verde' ).
utente( 2, jose, 20, masculino, 'lousada' ).
utente( 3, josefina, 34, feminino, 'aveiro' ).
utente( 4, luis, 20, masculino, 'vila das aves' ).
utente( 5, pedro, 20, masculino, 'felgueiras' ).


% Invariante Estrutural (Alínea 1) e 9))

+utente( IdUt,Nome,Idade,Sexo,Morada ) :: ( solucoes( (IdUt), utente(IdUt,N,I,Se,M), S ),
					                      comprimento( S,N ),
					                      N == 1 ).

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

+cuidadoPrestado( V,D,I,C ) :: ( solucoes( (V), cuidadoPrestado(V,D,I,C), S ),
					           comprimento( S,N ),
					           N == 1).

-cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (IdServ), atoMedico( Data,IdUt,IdServ,Custo ), S ),
									        comprimento( S,N ),
									        N == 0 ).

% ----------------------------------------------------------
%  Extensão do predicado atoMedico: Data, IdUt, IdServ, Custo -> {V, F}

atoMedico( '14-03-2017', 1, 5, 30 ).
atoMedico( '12-03-2017', 3, 2, 20 ).
atoMedico( '13-03-2017', 4, 4, 5 ).
atoMedico( '14-03-2017', 2, 3, 5 ).

% Invariante Estrutural (Alínea 1) e 9))

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

% evolucao: F -> {V,F}
evolucao( F ) :- solucoes(I, +F::I, Li),
			     assert(F),
			     testar(Li).
evolucao( F ) :- retract( F ),
				 !,
				 fail.

% testar: L -> {V,F}
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


% ----------------------- ALÍNEA 2) ------------------------
% ----------------------------------------------------------
%  Identificação dos utentes por Nome
%  Extensão do predicado utentesPorNome: Nome, [Utente] -> {V, F}

utentesPorNome( Nome, S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), utente(IdUt, Nome, Idade, Sexo, Morada), S ).

% ----------------------------------------------------------
%  Identificação dos utentes por Idade
%  Extensão do predicado utentesPorIdade: Idade, [Utente] -> {V, F}

utentesPorIdade( Idade, S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), utente(IdUt, Nome, Idade, Sexo, Morada), S ).

% ----------------------------------------------------------
%  Identificação dos utentes por Morada
%  Extensão do predicado utentesPorMorada: Morada, [Utente] -> {V, F}

utentesPorMorada( Morada, S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), utente(IdUt, Nome, Idade, Sexo, Morada), S ).

% ----------------------------------------------------------
%  Identificação dos utentes por Sexo
%  Extensão do predicado utentesPorSexo: Sexo, [Utente] -> {V, F}

utentesPorSexo( Sexo, S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), utente(IdUt, Nome, Idade, Sexo, Morada), S ).



% ---------------------- ALÍNEA 3) -------------------------
% ----------------------------------------------------------
%  Identificação das instituições prestadoras de cuidados de saúde;
%  Extensão do predicado listarInstComCuidadosDeSaude: [Instituição] -> {V, F}

listarInstComCuidadosDeSaude( S ) :-
	solucoes( (Instituicao, Descricao), cuidadoPrestado( IdServ, Descricao, Instituicao, Cidade), S ).


% 4ª ALINEA

% ----------------------------------------------------------
%  Identificação dos cuidados prestados por instituição
%  Extensão do predicado cuidadosPorInstituicao: Instituicao, [DescCuidado] -> {V, F}

cuidadosPorInstituicao( Instituicao, S ) :-
	solucoes( (DescCuidado), cuidadoPrestado( IdServ, DescCuidado, Instituicao, Cidade ), S ).

% ----------------------------------------------------------
%  Identificação dos cuidados prestados por cidade
%  Extensão do predicado cuidadosPorCidade: Cidade, [DescCuidado] -> {V, F}

cuidadosPorCidade( Cidade, S ) :-
	solucoes( (DescCuidado), cuidadoPrestado( IdServ, DescCuidado, Instituicao, Cidade ), S ).ade, Sexo, Morada ), S ).

% 5ª ALINEA

% ----------------------------------------------------------
%  Identificação dos utentes com atos médicos no cuidado com a Descrição apontada
%  Extensão do predicado utentesPorCuidado: DescCuidado, Utente -> {V, F}

utentesPorCuidado( DescCuidado, (IdUt, Nome, Idade, Sexo, Morada) ) :-
	cuidadoPrestado( IdServ, DescCuidado, Inst, Cidade ),
	atoMedico( Data, IdUt, IdServ, Custo ),
	utente( IdUt, Nome, Idade, Sexo, Morada ).

% ----------------------------------------------------------
%  Identificação dos utentes com atos médicos no cuidado com a Descrição apontada
%  Extensão do predicado listarUtentesPorCuidado: DescCuidado, [Utente] -> {V, F}

listarUtentesPorCuidado( DescCuidado, S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), utentesPorCuidado( DescCuidado, (IdUt, Nome, Idade, Sexo, Morada) ), S ).


% ----------------------------------------------------------
%  Identificação dos utentes com atos médicos na instituição apontada
%  Extensão do predicado utentesPorInstituicao: Instituicao, Utente -> {V, F}

utentesPorInstituicao( Instituicao, (IdUt, Nome, Idade, Sexo, Morada) ) :-
	cuidadoPrestado( IdServ, Desc, Instituicao, Cidade ),
	atoMedico( Data, IdUt, IdServ, Custo ),
	utente( IdUt, Nome, Idade, Sexo, Morada ).

% ----------------------------------------------------------
%  Identificação dos utentes com atos médicos na instituição apontada
%  Extensão do predicado listarUtentesPorInstituicao: Instituicao, [Utente] -> {V, F}

listarUtentesPorInstituicao( Instituicao, S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), utentesPorInstituicao( Instituicao, (IdUt, Nome, Idade, Sexo, Morada) ), S ).

% ----------------------------------------------------------
%  Identificação dos utentes com atos médicos na data apontada
%  Extensão do predicado utentesPorData: Data, Utente -> {V, F}

utentesPorData( Data, (IdUt, Nome, Idade, Sexo, Morada)) :-
	atoMedico( Data, IdUt, IdServ, Custo ),
	utente( IdUt, Nome, Idade, Sexo, Morada ).

%listarUtentesPorData( Data, S ) :-
%	findall( Nome, utentesPorData( Data, Nome ), S ).

% ----------------------------------------------------------
%  Identificação dos utentes com atos médicos na data apontada
%  Extensão do predicado listarUtentesPorData: Data, [Utente] -> {V, F}

listarUtentesPorData( Data, S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), utentesPorData( Data, (IdUt, Nome, Idade, Sexo, Morada) ), S ).


% ----------------------------------------------------------
%  Identificação dos utentes com idade de criança (<= 12) com atos médicos
%  Extensão do predicado criancaComAtoMedico: Utente -> {V, F}

criancaComAtoMedico( IdUt, Nome, Idade, Sexo, Morada ) :-
	atoMedico( Data, IdUt, IdServ, Custo ),
	utente( IdUt, Nome, Idade, Sexo, Morada ),
	Idade =< 12.

% ----------------------------------------------------------
%  Identificação das crianças com atos médicos
%  Extensão do predicado listarCriancasComAtoMedico: [Utente] -> {V, F}

listarCriancasComAtoMedico( S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), criancaComAtoMedico( IdUt, Nome, Idade, Sexo, Morada ), S ).

% ---------------------- ALÍNEA 6) -------------------------
% ----------------------------------------------------------
% Identificar os atos médicos realizados, por utente/instituição/serviço;

% Extensão do Predicado atoMedicoPorUtente: Ato Médico, Id Utente, Data, Instituição, Custo -> {V, F}
atoMedicoPorUtente( AtoMedico, IdUt, Data, Instituicao, Custo ) :-
	atoMedico( Data, IdUt, IdServ, Custo),
	cuidadoPrestado( IdServ, AtoMedico, Instituicao, Cid ).

% Extensão do Predicado listarAtoMedicoPorUtente: Id Utente, [Ato Médico] -> {V, F}
listarAtoMedicoPorUtente( IdUt, S ) :-
	solucoes( (AtoMedico, Data, Instituicao, Custo),
	atoMedicoPorUtente( AtoMedico, IdUt, Data, Instituicao, Custo), S ).

% Extensão do Predicado atoMedicoPorInstituicao: Ato Médico, Instituição, Id Utente, Nome, Data, Custo -> {V, F}
atoMedicoPorInstituicao( AtoMedico, Instituicao, IdUt, Nome, Data, Custo ) :-
	utente( IdUt, Nome, Idade, Sexo, Morada ),
	cuidadoPrestado( IdServ, AtoMedico, Instituicao, Cidade ),
	atoMedico( Data, IdUt, IdServ, Custo).

% Extensão do Predicado listarAtoMedicoPorInst: Instituição, [Ato Médico] -> {V, F}
listarAtoMedicoPorInst( Instituicao, S ) :-
	solucoes( (AtoMedico, IdUt, Nome, Data, Custo), 
	atoMedicoPorInstituicao(AtoMedico, Instituicao, IdUt, Nome, Data, Custo), S ).

% Extensão do Predicado atoMedicoPorservico: Ato Médico, Instituição, Id Utente, Nome, Data, Custo -> {V, F}
atoMedicoPorServico( AtoMedico, Instituicao, IdUt, Nome, Data, Custo ) :-
	utente( IdUt, Nome, Idade, Sexo, Morada ),
	cuidadoPrestado( IdServ, AtoMedico, Instituicao, Cidade ),
	atoMedico( Data, IdUt, IdServ, Custo).

% Extensão do Predicado listarAtoMedicoPorServ: Ato Médico, [Ato Médico] -> {V, F}
listarAtoMedicoPorServ( AtoMedico, S ) :-
	solucoes( (Instituicao, IdUt, Nome, Data, Custo), 
	atoMedicoPorInstituicao(AtoMedico, Instituicao, IdUt, Nome, Data, Custo), S ).