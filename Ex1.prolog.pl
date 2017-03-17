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

% Garantia de unicidade nos Ids dos Serviços
+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (IdServ), cuidadoPrestado(IdServ,D,I,C), S ),
					           comprimento( S,N ),
					           N == 1 ).

% Apenas é possível a inserção de um Serviço numa certa instituição uma vez
+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (Desc,Inst), cuidadoPrestado(V,Desc,Inst,C), S ),
							   comprimento( S, N),
							   N == 1 ).

% Não é possível a remoção de Serviços se houver algum Ato Nédico marcado que o use
-cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (IdServ), atoMedico( Data,IdUt,IdServ,Custo ), S ),
									        comprimento( S,N ),
									        N == 0 ).

% ----------------------------------------------------------
%  Extensão do predicado atoMedico: Data, IdUt, IdServ, Custo -> {V, F}

atoMedico( '14-03-2017', 1, 5, 30 ).
atoMedico( '12-03-2017', 3, 2, 20 ).
atoMedico( '13-03-2017', 4, 4, 5 ).
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


% ---------------------- ALÍNEA 4) -------------------------
% ----------------------------------------------------------
%  Identificação dos cuidados prestados por instituição
%  Extensão do predicado cuidadosPorInstituicao: Instituicao, [DescCuidado] -> {V, F}

cuidadosPorInstituicao( Instituicao, S ) :-
	solucoes( (DescCuidado), cuidadoPrestado( IdServ, DescCuidado, Instituicao, Cidade ), S ).

% ----------------------------------------------------------
%  Identificação dos cuidados prestados por cidade
%  Extensão do predicado cuidadosPorCidade: Cidade, [DescCuidado] -> {V, F}

cuidadosPorCidade( Cidade, S ) :-
	solucoes( (DescCuidado), cuidadoPrestado( IdServ, DescCuidado, Instituicao, Cidade ), S ).


% ---------------------- ALÍNEA 5) -------------------------
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

% ---------------------- ALÍNEA 7) -------------------------
% ----------------------------------------------------------

% Determinação de todas as instituições a que um utente já recorreu
% Extensão do Predicado instituicaoPorUtente: Utente, Instituicao -> {V, F}

instituicaoPorUtente( IdUt, Instituicao ) :-
	utente( IdUt, Nome, Idade, Sexo, Morada ),
	atoMedico( Data, IdUt, IdServ, Custo),
	cuidadoPrestado( IdServ, AtoMedico, Instituicao, Cidade ).

listarInstituicoesPorUtente( IdUt, S ) :-
	solucoes( (Instituicao), instituicaoPorUtente( IdUt, Instituicao ), S ).


% ----------------------------------------------------------

% Determinação de todas os serviços a que um utente já recorreu
% Extensão do Predicado serviçoPorUtente: Utente, Servico -> {V, F}

servicoPorUtente( IdUt, (IdServ, Servico, Instituicao) ) :-
	utente( IdUt, Nome, Idade, Sexo, Morada ),
	atoMedico( Data, IdUt, IdServ, Custo),
	cuidadoPrestado( IdServ, Servico, Instituicao, Cidade ).

listarServicosPorUtente( IdUt, S ) :-
	solucoes( (IdServ, Servico, Instituicao), servicoPorUtente( IdUt, (IdServ, Servico, Instituicao) ), S ).


% ---------------------- ALÍNEA 8) -------------------------
% ----------------------------------------------------------

% predicado auxiliar
somatorio([], 0).
somatorio([X | Y], R) :- somatorio(Y,Z),
						 R is X+Z.

% Cálculo do custo total dos atos médicos por utente
% Extensão do Predicado custosPorUtente: IdUt, Custo -> {V, F}

custosPorUtente( IdUt, Custo ) :-
	atoMedico( Data, IdUt, IdServ, Custo ).

listarCustosPorUtente( IdUt, [X|T], Total ) :-
	solucoes( (Custo), custosPorUtente( IdUt, Custo ), [X|T] ),
	somatorio( T, R ),
	Total is X + R. 


% Cálculo do custo total dos atos médicos por serviço/instituição/data
% Extensão do Predicado custosPorServico: IdServ, Custo -> {V, F}

custosPorServico( IdServ, Custo ) :-
	atoMedico( Data, IdUt, IdServ, Custo ).

listarCustosPorServico( IdServ, [X|T], Total ) :-
	solucoes( (Custo), custosPorServico( IdServ, Custo ), [X|T] ),
	somatorio( T, R ),
	Total is X + R. 


% Cálculo do custo total dos atos médicos por instituição/data
% Extensão do Predicado custosPorInstituicao: Instituicao, Custo -> {V, F}

custosPorInstituicao( Instituicao, Custo ) :-
	atoMedico( Data, IdUt, IdServ, Custo ),
	cuidadoPrestado( IdServ, DescCuidado, Instituicao, Cidade ).

listarCustosPorInstituicao( Instituicao, [X|T], Total ) :-
	solucoes( (Custo), custosPorInstituicao( Instituicao, Custo ), [X|T] ),
	somatorio( T, R ),
	Total is X + R. 


% Cálculo do custo total dos atos médicos por data
% Extensão do Predicado custosPorData: Data, Custo -> {V, F}

custosPorData( Data, Custo ) :-
	atoMedico( Data, IdUt, IdServ, Custo ).

listarCustosPorData( Data, [X|T], Total ) :-
	solucoes( (Custo), custosPorData( Data, Custo ), [X|T] ),
	somatorio( T, R ),
	Total is X + R. 



% -------------------- PREDICADOS EXTRA -------------------------
% ---------------------------------------------------------------

% Invariante Estrutural
+medico( IdMed,Nome,Idade,Sexo,IdServ ) :: ( solucoes( (IdMed), medico(IdMed,N,I,Se,Servico), S ),
					                      comprimento( S,N ),
					                      N == 1 ).


% Extensão do predicado medico: IdMed, Nome, Idade, Sexo, IdServ -> {V, F}

medico( 1, 'Antonio Lemos', 52, masculino, 3  ).
medico( 2, 'Anibal Mota', 59, masculino, 1 ).
medico( 3, 'Catarina Paiva', 35, feminino, 5 ).
medico( 4, 'Jose Garcia', 39, masculino, 2 ).
medico( 5, 'Carla Perez', 41, feminino, 6 ).


% Invariante Estrutural
+enfermeiro( IdEnf,Nome,Idade,Sexo,Instituicao ) :: ( solucoes( (IdEnf), enfermeiro(IdEnf,N,I,Se,Inst), S ),
					                      comprimento( S,N ),
					                      N == 1 ).

-enfermeiro( IdEnf,Nome,Idade,Sexo,Instituicao ) :: ( solucoes( (IdEnf), destacamento(Data,IdT,IdEnf), S ),
					                      comprimento( S,N ),
					                      N == 0 ).


% Extensão do predicado enfermeiro: IdEnf, Nome, Idade, Sexo, Instituicao -> {V, F}

enfermeiro(1, 'Catia Vanessa', 32, feminino, 'Centro de Saude de Lousada').
enfermeiro(2, 'Gabriela Soares', 26, feminino, 'Centro de Saude de Vila Verde').
enfermeiro(3, 'Renato Ribeiro' , 37, masculino, 'Hospital de Braga').
enfermeiro(4, 'Alexandra Cunha', 29, feminino, 'Hospital de Braga').
enfermeiro(5, 'Jorge Ferreira', 44, masculino, 'Hospital Sao Joao').

% Listar enfermeiros de uma dada Instituicao
% Extensão do predicado listarEnfermeirosPorInstituicao: Instituicao, [enfermeiro] -> {V, F}

listarEnfermeirosPorInstituicao( Instituicao, S ) :-
	solucoes( (IdEnf, Nome, Idade, Sexo), enfermeiro( IdEnf, Nome, Idade, Sexo, Instituicao ), S ).


% Invariante Estrutural
+turno( IdTurno,Horas,Instituicao ) :: ( solucoes( (IdTurno), turno(IdTurno,H,Inst), S ),
					              comprimento( S,N ),
					              N == 1 ).


% Extensão do predicado turno: IdTurno, Horas, Instituicao -> {V, F}

turno( 1, '19h-01h', 'Hospital de Braga' ).
turno( 2, '07h-13h', 'Hospital de Braga' ).
turno( 3, '13h-19h', 'Hospital de Braga' ).
turno( 4, '14h-19h', 'Hospital de Sao Joao' ).
turno( 5, '19h-01h', 'Centro de Saude de Vila Verde' ).

% Enfermeiro(a) destacado(a) para o dado turno em determinada data
% Extensão do predicado destacamento: Data, IdTurno, IdEnf -> {V, F}

destacamento( '13-03-2017', 2, 4 ).
destacamento( '19-03-2017', 1, 3 ).
destacamento( '5-04-2017', 3, 4 ).
destacamento( '1-04-2017', 5, 2 ).
destacamento( '19-02-2017', 4, 5 ).


% Enfermeiros destacados num dado dia
% Extensão do predicado enfermeiroPorData: Data, (IdEnf, Nome, IdTurno, Horas) -> {V, F}

enfermeiroPorData( Data, IdEnf, Nome, IdTurno, Horas ) :-
	destacamento( Data, IdTurno, IdEnf ),
	turno( IdTurno, Horas, Instituicao ),
	enfermeiro( IdEnf, Nome, Idade, Sexo, Instituicao ).

% Extensão do predicado listarEnfermeirosPorData: Data, [(IdEnf, Nome, IdTurno, Horas)] -> {V, F}

listarEnfermeirosPorData( Data, S ) :-
	solucoes( (IdEnf, Nome, IdTurno, Horas), enfermeiroPorData( Data, IdEnf, Nome, IdTurno, Horas), S ).

% Invariante Estrutural
+transplante( IdUt, Orgao ) :: ( solucoes( (IdUt, Orgao), transplante(IdUt, Orgao), S ),
					     comprimento( S,N ),
					     N == 1 ).


% Extensão do predicado transplante: IdUt, Orgao -> {V, F}

transplante( 3, 'Rim' ).
transplante( 1, 'Figado' ).
transplante( 2, 'Rim' ).

% Extensão do predicado listaDeEspera: Orgao, [Utentes] -> {V, F}

utenteEmEspera( Orgao, IdUt, Nome, Idade, Sexo, Morada ) :-
	transplante( IdUt, Orgao ),
	utente( IdUt, Nome, Idade, Sexo, Morada ).

listaDeEspera( Orgao, S ) :-
	solucoes( (IdUt, Nome, Idade, Sexo, Morada), utenteEmEspera( Orgao, IdUt, Nome, Idade, Sexo, Morada ), S ).

% Extensão do predicado medicoPorCuidado: Descricao, IdMed, Nome -> {V, F}

medicoPorCuidado( Descricao, IdMed, Nome ) :-
	medico( IdMed, Nome, Idade, Sexo, IdServ ),
	cuidadoPrestado( IdServ, Descricao, Inst, Cidade ).

% Extensão do predicado listarMedicosPorCuidado( Descricao, [(IdMed, Nome)] -> {V, F}
	
listarMedicosPorCuidado( Descricao, S ) :-
	solucoes( (IdMed, Nome), medicoPorCuidado( Descricao, IdMed, Nome ), S ).

% Extensão do predicado medicoPorInstituicao: Instituicao, IdMed, Nome -> {V, F}

medicoPorInstituicao( Instituicao, IdMed, Nome ) :-
	medico( IdMed, Nome, Idade, Sexo, IdServ ),
	cuidadoPrestado( IdServ, Descricao, Instituicao, Cidade ).

% Extensão do predicado listarMedicosPorInstituicao: Instituicao, [(IdMed, Nome)] -> {V, F}

listarMedicosPorInstituicao( Instituicao, S ) :-
	solucoes( ( IdMed, Nome ), medicoPorInstituicao( Instituicao, IdMed, Nome ), S ).