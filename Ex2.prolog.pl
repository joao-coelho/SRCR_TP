% -------------   1º Exercício em Grupo  -------------------
% Grupo: João Coelho, José Silva, Luís Fernandes, Pedro Cunha
%         (A74859),    (A74601),    (A74748),      (A73958)


:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

:- op( 900,xfy,'::' ).
:- dynamic utente/5.
:- dynamic '-'/1.
:- dynamic cuidadoPrestado/4.
:- dynamic atoMedico/4.
:- dynamic medico/5.
:- dynamic enfermeiro/5.
:- dynamic turno/3.
:- dynamic destacamento/3.
:- dynamic transplante/2.
:- dynamic excecao/1.

% ----------------------------------------------------------
%  Extensão do predicado utente: IdUt, Nome, Idade, Sexo, Morada -> {V, F}

utente( 1, joao, 20, masculino, 'Vila Verde' ).
utente( 2, jose, 20, masculino, 'Lousada' ).
utente( 3, josefina, 34, feminino, 'Aveiro' ).
utente( 4, luis, 20, masculino, 'Vila das Aves' ).
utente( 5, pedro, 20, masculino, 'Felgueiras' ).

-utente( 17, laura, 24, feminino, 'Faro' ).
-utente( 34, ricardo, 38, masculino, 'Guarda' ).
-utente( 72, alberto, 83, masculino, 'Setubal' ).

% Admissão do pressuposto do mundo fechado para o predicado utente

-utente(Id,N,I,S,C) :- 
    nao(utente(Id,N,I,S,C)),
    nao(excecao(utente(Id,N,I,S,C))).

% Invariante Estrutural (Alínea 1) e 9))
% Garantia de unicidade nos Ids dos utentes
+utente( IdUt,Nome,Idade,Sexo,Morada ) :: ( solucoes( (IdUt), utente(IdUt,No,I,Se,M), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Garante que não existe conhecimento positivo contraditótio
+(-utente( IdUt,Nome,Idade,Sexo,Morada )) :: ( solucoes( (IdUt), utente(IdUt,Nome,Idade,Sexo,Morada), S ),
                            comprimento( S,N ),
                            N == 0 ).


% Invariante Referencial
% Não é possível a remoção de utentes se houver algum Ato Médico para este
-utente( IdUt,Nome,Idade,Sexo,Morada ) :: ( solucoes( (IdUt), 
                            atoMedico( Data,IdUt,IdServ,Custo ), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Invariante que impede a inserção de conhecimento positivo ou negativo acerca de conhecimento interdito sobre a morada de utentes

+utente( Id,No,I,Se,C ) :: (solucoes( (Id,No,I,Se,C), (utente( Id,No,I,Se,xpto ), nulo(xpto)), S ),
                           comprimento( S,N ),
                           N == 0).

+(-utente( Id,No,I,Se,C )) :: (solucoes( (Id,No,I,Se,C), (utente( Id,No,I,Se,xpto ), nulo(xpto)), S ),
                              comprimento( S,N ),
                              N == 0).

% Garantir que não se adicionam exceções a conhecimento perfeito positivo.
+excecao( utente(Id,No,I,Se,M) ) :: ( nao( utente( Id,No,I,Se,M ) ) ).
 
% Garantia da não inserção de exceções repetidas.
+(excecao(utente(Id,No,I,Se,C))) :: ( solucoes( excecao( (utente(Id,No,I,Se,C))), excecao(utente(Id,No,I,Se,C)), S),
                                    comprimento(S,N),
                                    N < 2).

% Invariante de remoção que garante que não temos conhecimento Impreciso relativo à cidade do utente com menos de duas exceções
-(excecao(utente( Id,No,I,Se,C ))) :: ( ( solucoes( excecao(utente(Id,No,I,Se,Cidade)), excecao(utente( Id,No,I,Se,Cidade )), S ),
                                          comprimento( S,N ),
                                          N >= 2 );
                                        ( solucoes( ( Id ), utente( Id,No,I,Se,Cidade ), S ),
                                          comprimento( S,N ),
                                          N == 1 ) 
                                      ).

% ----------------------------------------------------------
%  Extensão do predicado cuidadoPrestado: IdServ, Descrição, Instituição, Cidade -> {V, F}

cuidadoPrestado( 1, 'Medicina Familiar', 'Centro de Saude de Vila Verde', 'Vila Verde').
cuidadoPrestado( 2, 'Radiologia', 'Hospital Sao Joao', 'Porto').
cuidadoPrestado( 3, 'Medicina Familiar', 'Centro de Saude de Lousada', 'Lousada').
cuidadoPrestado( 4, 'Medicina Familiar', 'Centro de Saude de Felgueiras', 'Felgueiras').
cuidadoPrestado( 5, 'Ginecologia', 'Hospital de Braga', 'Braga').
cuidadoPrestado( 6, 'Obstetricia', 'Hospital de Braga', 'Braga').

% Inserção de Conhecimento Negativo

-cuidadoPrestado( 30,'Medicina Familiar','Hospital Sao Joao','Porto' ).
-cuidadoPrestado( 45,'Obstetricia','Hospital do Algarve','Faro' ).
-cuidadoPrestado( 98,'Ginecologia','Centro de Saude de Felgueiras','Felgueiras' ).


% Invariante Estrutural (Alínea 1) e 9))

% Garantia de unicidade nos Ids dos Serviços
+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (IdServ), cuidadoPrestado(IdServ,D,I,C), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Apenas é possível a inserção de um Serviço numa certa instituição uma vez
+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (Desc,Inst), cuidadoPrestado(V,Desc,Inst,C), S ),
                            comprimento( S, N),
                            N == 0 ).

% Garantir que não existe conhecimento negativo contraditótio
+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (IdServ), -cuidadoPrestado(IdServ,Desc,Inst,Cid), S ),
                            comprimento( S, N ),
                            N == 0 ).

% Garantir que não existe conhecimento positivo contraditótio
+(-cuidadoPrestado( IdServ,Desc,Inst,Cid )) :: ( solucoes( (IdServ), cuidadoPrestado(IdServ,Desc,Inst,Cid), S ),
                            comprimento( S, N ),
                            N == 0 ).

% Garantia de unicidade nos Ids dos Serviços
+(-cuidadoPrestado( IdServ,Desc,Inst,Cid )) :: ( solucoes( (IdServ), -cuidadoPrestado(IdServ,D,I,C), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Garantir que nao se adicionaa excecoes a conhecimento perfeito positivo
+excecao( cuidadoPrestado(Id,D,I,C) ) :: ( nao( cuidadoPrestado( Id,D,I,C ) ) ).


% Garantia da não inserção de exceções repetidas.
+(excecao(cuidadoPrestado(IdServ,D,I,C))) :: (solucoes(excecao(cuidadoPrestado(IdServ,D,I,C)),excecao(cuidadoPrestado(IdServ,D,I,C)),S),
                    comprimento(S,N),
                    N < 2).


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

-atoMedico( '31-01-2017', 5, 3, 13).
-atoMedico( '12-07-2017', 3, 4, 43).
-atoMedico( '06-01-2018', 2, 1, 59).
-atoMedico( '24-12-2017', 6, 5, 2).

% Pressuposto Mundo Fechado para o predicado atoMedico

-atoMedico(D,Id,IdS,C) :-
    nao(atoMedico(D,Id,IdS,C)),
    nao(excecao(atoMedico(D,Id,IdS,C))).

% Invariante Estrutural (Alínea 1) e 9))

% Apenas é possível inserir um atoMedico em que o IdUt esteja registado nos Utentes e
% o IdServ esteja registado nos Cuidados Prestados
+atoMedico( Data,IdUt,IdServ,Custo ) :: ( solucoes( (IdUt), utente( IdUt,Nome,Idade,Sexo,Morada ), S1 ),
                    comprimento( S1,N1 ),  
                    N1 == 1,
                    solucoes( (IdServ), cuidadoPrestado( IdServ,Descricao,Instituicao,Cidade ), S2 ),
                    comprimento( S2,N2 ),
                    N2 == 1 ).

% Garantir que não existe conhecimento positivo repetido
+atoMedico( Data,IdUt,IdServ,Custo ) :: ( solucoes( (IdUt,IdServ), atoMedico( Data,IdUt,IdServ,Custo ), S ),
                                        comprimento( S, N ),
                                        N == 0 ).

% Garantir que não existe conhecimento positivo contraditótio
+(-atoMedico( Data,IdUt,IdServ,Custo ) ) :: ( solucoes( (IdUt,IdServ), atoMedico( Data,IdUt,IdServ,Custo ), S ),
                                            comprimento( S, N ),
                                            N == 0 ).

% Garantir que nao se adicionaa excecoes a conhecimento perfeito positivo
+excecao( atoMedico( D,I,Is,C ) ) :: nao( atoMedico( D,I,Is,C ) ).


% Garantia da não inserção de exceções repetidas.
+(excecao(atoMedico(D,IdUt,IdServ,C))) :: (solucoes(excecao(atoMedico(D,IdUt,IdServ,C)), excecao(atoMedico(D,IdUt,IdServ,C)),S),
                    comprimento(S,N),
                    N < 2).



% -------------------- PREDICADOS AUXILIARES EXERCICIO 2 --------------------------

% Extensao do meta-predicado demo: Questao,Resposta -> {V,F,D}

demo(Questao, verdadeiro) :- Questao.
demo(Questao, falso) :- -Questao.
demo(Questao, desconhecido) :- nao(Questao),
                              nao(-Questao).

% Extensao do meta-predicado myDemo: [Queries], Resposta -> {V, F, D} 

myDemo( [], verdadeiro ).
myDemo( [Q], Resposta ) :- demo( Q, Resposta ).
myDemo( [Q1, Op | T], Resposta ) :- Op == e,
                                    demo( Q1, V1 ),
                                    myDemo( T, V2 ),
                                    conjuncao( V1, V2, Resposta ).
myDemo( [Q1, Op | T], Resposta ) :- Op == ou,
                                    demo( Q1, V1 ),
                                    myDemo( T, V2 ),
                                    disjuncao( V1, V2, Resposta ).


conjuncao( verdadeiro, verdadeiro, verdadeiro ).
conjuncao( verdadeiro, desconhecido, desconhecido ).
conjuncao( desconhecido, verdadeiro, desconhecido ).
conjuncao( desconhecido, desconhecido, desconhecido ).
conjuncao( falso, _, falso ).
conjuncao( _, falso, falso ).

disjuncao( verdadeiro, _, verdadeiro ).
disjuncao( _, verdadeiro, verdadeiro ).
disjuncao( falso, falso, falso ).
disjuncao( falso, desconhecido, desconhecido ).
disjuncao( desconhecido, falso, desconhecido ).
disjuncao( desconhecido, desconhecido, desconhecido ).


% Extensao do meta-predicado demoLista: [Questao],[Resposta] -> {V,F,D}

demoLista( [],[] ).
demoLista( [X|L],[R|S] ) :- demo( X,R ),
                            demoLista( L,S ). 


% --------------------- PREDICADOS AUXILIARES ANTERIORES ----------------------

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
evolucao( F ) :- solucoes(I, +F::I, Li),
                 testar(Li),
                 assert(F).

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

nao( Questao ) :- Questao, !, fail.
nao( Questao ).


% ----------------------------------------------------------------------
% ----------------------- Trabalho de Grupo 2 --------------------------




% ---------------- INSERÇÃO DE CONHECIMENTO IMPERFEITO -----------------

% ------------------------- Imperfeito Incerto -------------------------

% --- Não se sabe a idade do utente Manuel, cujo IdUt é 6.

utente( 6, manuel, inc0001, masculino, 'Lisboa' ).
excecao( utente( Id,N,I,S,C ) ) :- utente( Id,N,inc0001,S,C ).

% --- Não se sabe a data em que o utente cujo IdUt é 3 foi submetido ao tratamento cujo IdServ é 5.

atoMedico( inc0002, 3, 5, 10 ).
excecao( atoMedico( D,IdUt,IdServ,C ) ) :- atoMedico( inc0002,IdUt,IdServ,C ).



% ------------------------- Imperfeito Impreciso -----------------------

% Não se sabe se o/a utente Dolores é do sexo masculino ou feminino.

excecao(utente( 7, dolores, 34, masculino, 'Amadora' )).
excecao(utente( 7, dolores, 34, feminino, 'Amadora' )).

% Não se sabe se o utente Zeca tem 36 ou 37 anos, nem se é da Amadora ou de Sintra.

excecao(utente( 8, zeca, 36, masculino, 'Sintra' )).
excecao(utente( 8, zeca, 37, masculino, 'Sintra' )).
excecao(utente( 8, zeca, 36, masculino, 'Amadora' )).
excecao(utente( 8, zeca, 37, masculino, 'Amadora' )).

% Não se sabe se o utente Alfredo é de Felgueiras ou Lousada.

excecao(utente( 7, alfredo, 22, masculino, 'felgueiras' )).
excecao(utente( 7, alfredo, 22, masculino, 'lousada' )).

% Não se sabe se a utente Alzira tem 23 ou 24 anos.

excecao(utente( 8, alzira, 23, feminino, 'braga' )).
excecao(utente( 8, alzira, 24, feminino, 'braga' )).

% Não se sabe o preço da consulta que ocorreu no dia 29 de Abril de 2017, cujo utente tem o
% IdUt 2 e o serviço prestado tem o IdServ 3, mas sabe-se que o preço foi
% entre os 3 e os 17 euros.

excecao(atoMedico('29-04-2017',2,3,C)) :- C>=3, C=<17.



% ------------------------- Imperfeito Interdito -----------------------

% Não se sabe nem é possível vir a saber a morada do utente António Costa.

utente(10, 'Antonio Costa', 55, masculino, int0001).
excecao( utente( Id,Nome,Idade,Sexo,Morada ) ) :- utente( Id,Nome,Idade,Sexo,int0001 ).
nulo( int0001 ).

% Não se sabe nem é possível vir a saber qual o serviço prestado ao utente cujo IdUt é 10
% no dia 20 de Março de 2017 e cujo preço foi 3000€.

atoMedico( '20-03-2017', 10, int0002, 3000 ).
excecao( atoMedico( Data,IdUt,IdServ,Custo ) ) :- atoMedico( Data,IdUt,int0002,Custo ).
nulo( int0002 ).



% ----------------------------------------------------------------------
