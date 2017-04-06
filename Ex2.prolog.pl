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

% ----------------------------------------------------------
%  Extensão do predicado utente: IdUt, Nome, Idade, Sexo, Morada -> {V, F}

utente( 1, joao, 20, masculino, 'vila verde' ).
utente( 2, jose, 20, masculino, 'lousada' ).
utente( 3, josefina, 34, feminino, 'aveiro' ).
utente( 4, luis, 20, masculino, 'vila das aves' ).
utente( 5, pedro, 20, masculino, 'felgueiras' ).


% Invariante Estrutural (Alínea 1) e 9))
% Garantia de unicidade nos Ids dos utentes
+utente( IdUt,Nome,Idade,Sexo,Morada ) :: ( solucoes( (IdUt), 
                            (utente(IdUt,No,I,Se,M),-utente(IdUt,No,I,Se,M)), S ),
                            comprimento( S,N ),
                            N == 1 ).

% Garante que não existe conhecimento negativo contraditório
+utente( IdUt,Nome,Idade,Sexo,Morada ) :: ( solucoes( (IdUt), 
                            -utente(IdUt,Nome,Idade,Sexo,Morada), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Garante que não existe conhecimento positivo contraditótio
+(-utente( IdUt,Nome,Idade,Sexo,Morada )) :: ( solucoes( (IdUt), 
                            utente(IdUt,Nome,Idade,Sexo,Morada), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Invariante Referencial
% Não é possível a remoção de utentes se houver algum Ato Médico para este
-utente( IdUt,Nome,Idade,Sexo,Morada ) :: ( solucoes( (IdUt), 
                            atoMedico( Data,IdUt,IdServ,Custo ), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Garantia de unicidade nos Ids dos utentes
+(-utente( IdUt,Nome,Idade,Sexo,Morada )) :: ( solucoes( (IdUt), 
                            (utente(IdUt,No,I,Se,M),-utente(IdUt,No,I,Se,M)), S ),
                            comprimento( S,N ),
                            N == 1 ).

% Invariante que impede a inserção de conhecimento positivo ou negativo acerca de conhecimento interdito sobre a morada de utentes

+utente( Id,N,I,S,C ) :: (solucoes( (Id,N,I,S,C), (utente( Id,N,I,S,xpto ), nulo(xpto)), S ),
                          comprimento( S,N ),
                          N == 1).

+(-utente( Id,N,I,S,C )) :: (solucoes( (Id,N,I,S,C), (utente( Id,N,I,S,xpto ), nulo(xpto)), S ),
                          comprimento( S,N ),
                          N == 1).

% Garantir que nao se adicionaa excecoes a conhecimento perfeito positivo
+excecao( utente(Id,N,I,S,M) ) :: nao( utente(Id,N,I,S,M) ).
 

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
                            N == 1 ).

% Garantir que nao se adicionaa excecoes a conhecimento perfeito positivo
+excecao( cuidadoPrestado(Id,D,I,C) ) :: nao( cuidadoPrestado(Id,D,I,C) ).

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

% pressuposto mundo fechado
-atoMedico(D,Id,IdS,C) :-
    nao(atoMedico(D,Id,IdS,C)),
    nao(excecao(atoMedico(D,Id,IdS,C))).

% Garantir que nao se adicionaa excecoes a conhecimento perfeito positivo
+excecao( atoMedico(D,I,Is,C) ) :: nao( atoMedico(D,I,Is,C) ).


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
evolucao( F ) :- solucoes(I, +F::I, Li),
                 assert(F),
                 testar(Li).
evolucao( F ) :- retract( F ),
                 !,
                 fail.

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

% Extensao do meta-predicado myDemo: [Queries], Resposta -> {V, F, D} 
myDemo( [], verdadeiro ).
myDemo( [Q], Resposta ) :-
    demo( Q, Resposta ).
myDemo( [Q1, Op | T], Resposta ) :-
    Op == e,
    demo(Q1, V1),
    myDemo(T, V2),
    conjuncao(V1, V2, Resposta).
myDemo( [Q1, Op | T], Resposta ) :-
    Op == ou,
    demo(Q1, V1),
    myDemo(T, V2),
    disjuncao(V1, V2, Resposta).


conjuncao( verdadeiro,verdadeiro,verdadeiro ).
conjuncao( verdadeiro,desconhecido,desconhecido ).
conjuncao( desconhecido,verdadeiro,desconhecido ).
conjuncao( desconhecido,desconhecido,desconhecido ).
conjuncao( falso,_,falso ).
conjuncao( _,falso,falso ).

disjuncao( verdadeiro,_,verdadeiro ).
disjuncao( _,verdadeiro,verdadeiro ).
disjuncao( falso,falso,falso ).
disjuncao( falso,desconhecido,desconhecido ).
disjuncao( desconhecido,falso,desconhecido ).
disjuncao( desconhecido,desconhecido,desconhecido ).


% Extensao do meta-predicado demoLista: [Questao],[Resposta] -> {V,F,D}

demoLista( [],[] ).
demoLista( [X|L],[R|S] ) :-
    demo( X,R ),
    demoLista( L,S ). 


demoConj( [],verdadeiro ).

demoConj( [X|Y], verdadeiro ) :-
    demo( X, verdadeiro ),
    demoConj( Y, verdadeiro ).

demoConj( [X|Y], falso ) :-
    demo( X, falso ),
    demoConj( Y, Z ).

demoConj( [X|Y], falso ) :-
    demo( X, Z ),
    demoConj(Y, falso).

demoConj( [X|Y], desconhecido ) :-
    demo( X, desconhecido ),
    nao(demoConj( Y, falso )).

demoConj( [X|Y], desconhecido ) :-
    nao(demo( X, falso )),
    demoConj( Y, desconhecido ).


demoDisj( [],falso ).

demoDisj( [X|Y], falso ) :-
    demo(X, falso ),
    demoDisj(Y, falso ).

demoDisj( [X|Y], verdadeiro ) :-
    demo( X, verdaderiro ),
    demoDisj( Y, Z ).

demoDisj( [X|Y], verdadeiro ) :-
    demo( X, Z ),
    demoDisj( Y, verdadeiro ).

demoDisj( [X|Y], desconhecido ) :-
    demo( X, desconhecido ),
    nao(demoDisj( Y, verdadeiro )).

demoDisj( [X|Y], desconhecido ) :-
    nao(demo( X, verdadeiro ),
    demoDisj( Y, desconhecido )).

% ----------------------------------------------------------------------
% ----------------------- Trabalho de Grupo 2 --------------------------

% Admissão do pressuposto do mundo fechado para o predicado utente

-utente(Id,N,I,S,C) :- 
    nao(utente(Id,N,I,S,C)),
    nao(excecao(utente(Id,N,I,S,C))).


% Inserção de Conhecimento Negativo

-cuidadoPrestado( Id,'Medicina Familiar','Hospital Sao Joao','Porto' ).
-cuidadoPrestado( Id,'Obstetricia','Hospital do Algarve','Faro' ).
-cuidadoPrestado( Id,'Ginecologia','Centro de Saúde de Felgueiras','Felgueiras' ).

% Inserção de conhecimento imperfeito Incerto

utente( 6, manuel, inc0001, masculino, 'Lisboa' ).
excecao( utente( Id,N,I,S,C ) ) :- utente( Id,N,inc0001,S,C ).

atoMedico( inc0002,3,5,10 ).
excecao( atoMedico( D,IdUt,IdServ,C ) ) :- atoMedico( inc0002,IdUt,IdServ,C ).


% Inserção de conhecimento imperfeito Impreciso

excecao(utente( 7,dolores,34,masculino,'Amadora' )).
excecao(utente( 7,dolores,34,feminino,'Amadora' )).

excecao(utente( 8,zeca,37,masculino,'Sintra' )).
excecao(utente( 8,zeca,36,masculino,'Amadora' )).

excecao(utente( 7,'Alfredo',22,masculino,'felgueiras' )).
excecao(utente( 7,'Alfredo',22,masculino,'lousada' )).

excecao(utente( 8,'Alzira',23,feminino,'braga' )).
excecao(utente( 8,'Alzira',24,feminino,'braga' )).

% Comentar
excecao(atoMedico('29-04-2017',2,3,C)) :- C>=3, C=<17.
