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
:- dynamic nulo/1.

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
+utente( IdUt,Nome,Idade,Sexo,Cidade ) :: ( solucoes( (IdUt), utente(IdUt,No,I,Se,Cid), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Garante que não existe conhecimento positivo contraditótio
+(-utente( IdUt,Nome,Idade,Sexo,Cidade )) :: ( solucoes( (IdUt), utente(IdUt,Nome,Idade,Sexo,Cidade), S ),
                            comprimento( S,N ),
                            N == 0 ).


% Invariante Referencial
% Não é possível a remoção de utentes se houver algum Ato Médico para este
-utente( IdUt,Nome,Idade,Sexo,Cidade ) :: ( solucoes( (IdUt), 
                            atoMedico( Data,IdUt,IdServ,Custo ), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Invariante que permite a inserção de conhecimento impreciso se não houver conhecimento incerto relativo à idade
+utente( IdUt,Nome,Idade,Sexo,Cidade ) :: ( solucoes( (excecao(utente(IdUt,Nome,Idd,Sexo,Cidade))),
                          excecao(utente(IdUt,Nome,Idd,Sexo,Cidade)), S ),
                                    comprimento( S,N ),
                                    N == 0 ).

% Invariante que permite a inserção de conhecimento impreciso se não houver conhecimento incerto relativo à cidade
+utente( IdUt,Nome,Idade,Sexo,Cidade ) :: ( solucoes( (excecao(utente(IdUt,Nome,Idade,Sexo,Cid))),
                          excecao(utente(IdUt,Nome,Idade,Sexo,Cid)), S ),
                                    comprimento( S,N ),
                                    N == 0 ).

% Invariante que impede a inserção de conhecimento positivo ou negativo acerca de conhecimento interdito sobre a idade de utentes

+utente( Id,No,I,Se,C ) :: (solucoes( (Id,No,I,Se,C), (utente( Id,No,xpto,Se,C ), nulo(xpto)), S ),
                           comprimento( S,N ),
                           N == 0).

+(-utente( Id,No,I,Se,C )) :: (solucoes( (Id,No,I,Se,C), (utente( Id,No,xpto,Se,C ), nulo(xpto)), S ),
                              comprimento( S,N ),
                              N == 0).

% Invariante que impede a inserção de conhecimento positivo ou negativo acerca de conhecimento interdito sobre a cidade de utentes

+utente( Id,No,I,Se,C ) :: (solucoes( (Id,No,I,Se,C), (utente( Id,No,I,Se,xpto ), nulo(xpto)), S ),
                           comprimento( S,N ),
                           N == 0).

+(-utente( Id,No,I,Se,C )) :: (solucoes( (Id,No,I,Se,C), (utente( Id,No,I,Se,xpto ), nulo(xpto)), S ),
                              comprimento( S,N ),
                              N == 0).

% Garantir que não se adicionam exceções relativas à idade a conhecimento perfeito positivo.
+excecao( utente(Id,No,I,Se,C) ) :: ( nao( utente( Id,No,Idd,Se,C ) ) ).

% Garantir que não se adicionam exceções relativas à cidade a conhecimento perfeito positivo.
+excecao( utente(Id,No,I,Se,C) ) :: ( nao( utente( Id,No,I,Se,Cidade ) ) ).
 
% Garantia da não inserção de exceções repetidas.
+(excecao(utente(Id,No,I,Se,C))) :: ( solucoes( (excecao(utente(Id,No,I,Se,C))), excecao(utente(Id,No,I,Se,C)), S),
                                    comprimento(S,N),
                                    N == 0).

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

% Invariante que permite a inserção de conhecimento impreciso se não houver conhecimento incerto relativo à instituição
+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: ( solucoes( (excecao(cuidadoPrestado(IdServ,Desc,I,Cid))),
                          excecao(cuidadoPrestado(IdServ,Desc,I,Cid)), S ),
                                    comprimento( S,N ),
                                    N == 0 ).

% Invariante que impede a inserção de conhecimento positivo ou negativo acerca de conhecimento interdito sobre a instituição

+cuidadoPrestado( IdServ,Desc,Inst,Cid ) :: (solucoes( (IdServ,Desc,Inst,Cid), (cuidadoPrestado( IdServ,Desc,xpto,Cid ), nulo(xpto)), S ),
                           comprimento( S,N ),
                           N == 0).

+(-cuidadoPrestado( IdServ,Desc,Inst,Cid )) :: (solucoes( (IdServ,Desc,Inst,Cid), (cuidadoPrestado( IdServ,Desc,xpto,Cid ), nulo(xpto)), S ),
                              comprimento( S,N ),
                              N == 0).

% Garantir que não existe conhecimento positivo contraditótio
+(-cuidadoPrestado( IdServ,Desc,Inst,Cid )) :: ( solucoes( (IdServ), cuidadoPrestado(IdServ,Desc,Inst,Cid), S ),
                            comprimento( S, N ),
                            N == 0 ).

% Garantia de unicidade nos Ids dos Serviços
+(-cuidadoPrestado( IdServ,Desc,Inst,Cid )) :: ( solucoes( (IdServ), -cuidadoPrestado(IdServ,D,I,C), S ),
                            comprimento( S,N ),
                            N == 0 ).

% Garantir que nao se adicionam excecoes a conhecimento perfeito positivo
+excecao( cuidadoPrestado(Id,D,I,C) ) :: ( nao( cuidadoPrestado( Id,D,Inst,C ) ) ).


% Garantia da não inserção de exceções repetidas.
+(excecao(cuidadoPrestado(IdServ,D,I,C))) :: ( solucoes( (excecao(cuidadoPrestado(IdServ,D,I,C))), excecao(cuidadoPrestado(IdServ,D,I,C)), S ),
                                             comprimento( S,N ),
                                             N == 0 ).


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

% Invariante que permite a inserção de conhecimento impreciso se não houver conhecimento incerto relativo ao custo
+atoMedico( Data,IdUt,IdServ,Custo ) :: ( solucoes( (excecao(atoMedico( Data,IdUt,IdServ,C ))),
                          excecao(atoMedico( Data,IdUt,IdServ,C )), S ),
                                    comprimento( S,N ),
                                    N == 0 ).

% Invariante que permite a inserção de conhecimento impreciso se não houver conhecimento incerto relativo ao serviço
+atoMedico( Data,IdUt,IdServ,Custo ) :: ( solucoes( (excecao(atoMedico( Data,IdUt,IdServico,Custo ))),
                          excecao(atoMedico( Data,IdUt,IdServico,Custo )), S ),
                                    comprimento( S,N ),
                                    N == 0 ).

% Invariante que impede a inserção de conhecimento positivo ou negativo acerca de conhecimento interdito sobre o serviço

+atoMedico( Data,IdUt,IdServ,C ) :: (solucoes( (Data,IdUt,IdServ,C), (atoMedico( Data,IdUt,xpto,C ), nulo(xpto)), S ),
                           comprimento( S,N ),
                           N == 0).

+(-atoMedico( Data,IdUt,IdServ,C )) :: (solucoes( (Data,IdUt,IdServ,C), (atoMedico( Data,IdUt,xpto,C ), nulo(xpto)), S ),
                              comprimento( S,N ),
                              N == 0).

% Invariante que impede a inserção de conhecimento positivo ou negativo acerca de conhecimento interdito sobre o custo

+atoMedico( Data,IdUt,IdServ,C ) :: (solucoes( (Data,IdUt,IdServ,C), (atoMedico( Data,IdUt,IdServ,xpto ), nulo(xpto)), S ),
                           comprimento( S,N ),
                           N == 0).

+(-atoMedico( Data,IdUt,IdServ,C )) :: (solucoes( (Data,IdUt,IdServ,C), (atoMedico( Data,IdUt,IdServ,xpto ), nulo(xpto)), S ),
                              comprimento( S,N ),
                              N == 0).

% Garantir que não existe conhecimento positivo contraditótio
+(-atoMedico( Data,IdUt,IdServ,Custo ) ) :: ( solucoes( (IdUt,IdServ), atoMedico( Data,IdUt,IdServ,Custo ), S ),
                                            comprimento( S, N ),
                                            N == 0 ).

% Garantir que nao se adicionaa excecoes a conhecimento perfeito positivo
+excecao( atoMedico( D,IdUt,IdServ,C ) ) :: nao( atoMedico( D,IdUt,IdS,C ) ).

% Garantir que nao se adicionaa excecoes a conhecimento perfeito positivo
+excecao( atoMedico( D,IdUt,IdServ,C ) ) :: nao( atoMedico( D,IdUt,IdServ,Custo ) ).


% Garantia da não inserção de exceções repetidas.
+(excecao(atoMedico(D,IdUt,IdServ,C))) :: ( solucoes( (excecao(atoMedico(D,IdUt,IdServ,C))), excecao(atoMedico(D,IdUt,IdServ,C)),S),
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

% Extensao do meta-predicado demoConj: [Questao], Resposta -> {V,F,D}

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

% Extensao do meta-predicado demoDisj: [Questao], Resposta -> {V,F,D}

demoDisj( [],falso ).
demoDisj( [X|Y], falso ) :-
    demo(X, falso ),
    demoDisj(Y, falso ).
 
demoDisj( [X|Y], verdadeiro ) :-
    demo( X, verdadeiro ),
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
% evolucao: F -> {V,F}
evolucao( F ) :- 
    solucoes(I, +F::I, Li),
    testar(Li),
    assert(F).

% evolucao: F, Type -> {V,F}
evolucao( F, Type ) :- 
    Type == positivo,
    solucoes(I, +F::I, Li),
    testar(Li),
    assert(F).

evolucao( F, Type ) :-
    Type == negativo,
    solucoes( I, +(-F)::I, Li ),
    testar(Li),
    assert(-F).

%permite idade desconhecida
evolucao( utente( Id,No,Idd,Se,Cid ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == idade,
    evolucao( utente( Id,No,Idd,Se,Cid ), positivo ),
    assert( (excecao(utente( IdUt,Nome,Idade,Sexo,Cidade )) :- 
                utente( IdUt,Nome,Idd,Sexo,Cidade ) ) ).

% permite cidade desconhecida
evolucao( utente( Id,No,Idd,Se,Cid ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == cidade,
    evolucao( utente( Id,No,Idd,Se,Cid ), positivo ),
    assert( (excecao(utente( IdUt,Nome,Idade,Sexo,Cidade )) :- 
                utente( IdUt,Nome,Idade,Sexo,Cid ) ) ).

% permite instituição desconhecida 
evolucao( cuidadoPrestado( Id,Desc,Inst,Cid ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == instituicao,
    evolucao( cuidadoPrestado( Id,Desc,Inst,Cid ), positivo ),
    assert( (excecao(cuidadoPrestado( IdServ,Descricao,Instituicao,Cidade )) :- 
                cuidadoPrestado( IdServ,Descricao,Inst,Cidade ) ) ).

% permite custos desconhecidos
evolucao( atoMedico( D,IdU,IdS,C ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == custo,
    evolucao( atoMedico( D,IdU,IdS,C ), positivo ),
    assert( (excecao(atoMedico( Data,IdUt,IdServ,Custo )) :- 
                atoMedico( Data,IdUt,IdServ,C ) ) ).

% permite serviços desconhecidos
evolucao( atoMedico( D,IdU,IdS,C ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == servico,
    evolucao( atoMedico( D,IdU,IdS,C ), positivo ),
    assert( (excecao(atoMedico( Data,IdUt,IdServ,Custo )) :- 
                atoMedico( Data,IdUt,IdS,Custo ) ) ).

evolucao( [OPT1 | R], Type ) :-
    Type == impreciso,
    solucoes( I, +(excecao(OPT1))::I, Li ),
    testar(Li),
    assert( (excecao( OPT1 )) ),
    evolucao( R,impreciso ).

evolucao( [], impreciso ).

evolucao( utente( Id,No,Idd,Se,Cid ), Type, Impreciso, MenorValor, MaiorValor ) :-
    Type == impreciso,
    Impreciso == idade,
    solucoes( I, +(excecao(utente( Id,No,Idd,Se,Cid )))::I, Li ),
    testar(Li),
    assert( (excecao( utente( Id,No,Idd,Se,Cid ) ) :-
                Idd >= MenorValor,
                Idd =< MaiorValor ) ).

evolucao( atoMedico( D,IdUt,IdServ,C ), Type, Impreciso, MenorValor, MaiorValor ) :-
    Type == impreciso,
    Impreciso == custo,
    solucoes( I, +(excecao(utente( Id,No,Idd,Se,Cid )))::I, Li ),
    testar(Li),
    assert( (excecao( atoMedico( D,IdUt,IdServ,C ) ) :-
                C >= MenorValor,
                C =< MaiorValor ) ).

% permite cidade interdita
evolucao( utente( Id,No,Idd,Se,Cid ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == cidade,
    evolucao( utente( Id,No,Idd,Se,Cid ),positivo ),
    assert( (excecao(utente( IdUt,Nome,Idade,Sexo,Cidade )) :-
                utente( IdUt,Nome,Idade,Sexo,Cid ) ) ),
    assert( (nulo(Cid)) ). 

% permite instituição interdita 
evolucao( cuidadoPrestado( Id,Desc,Inst,Cid ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == instituicao,
    evolucao( cuidadoPrestado( Id,Desc,Inst,Cid ), positivo ),
    assert( (excecao(cuidadoPrestado( IdServ,Descricao,Instituicao,Cidade )) :- 
                cuidadoPrestado( IdServ,Descricao,Inst,Cidade ) ) ), 
    assert( nulo(Inst) ).

% permite custos interditos
evolucao( atoMedico( D,IdU,IdS,C ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == custo,
    evolucao( atoMedico( D,IdU,IdS,C ), positivo ),
    assert( (excecao(atoMedico( Data,IdUt,IdServ,Custo )) :- 
                atoMedico( Data,IdUt,IdServ,C ) ) ), 
    assert( nulo(C) ).

% permite serviços interditos
evolucao( atoMedico( D,IdU,IdS,C ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == servico,
    evolucao( atoMedico( D,IdU,IdS,C ), positivo ),
    assert( (excecao(atoMedico( Data,IdUt,IdServ,Custo )) :- 
                atoMedico( Data,IdUt,IdS,Custo ) ) ),
    assert( nulo(IdS) ).

% testar: L -> {V,F}
testar([]).
testar([I|Li]) :- I,
                  testar(Li).

% involucao: F -> {V,F}
involucao( F ) :- solucoes(I, -F::I, Li),
                  testar(Li),
                  retract(F).

% involucao: F, Type -> {V,F}
involucao( F,Type ) :- 
    Type == positivo,
    solucoes(I, -F::I, Li),
        testar(Li),
        retract(F).

involucao( F,Type ) :- 
    Type == negativo,
    solucoes(I, -(-F)::I, Li),
        testar(Li),
        retract(-F).

% permite remover conhecimento incerto sobre idade de utentes
involucao( utente( Id,No,Idd,Se,Cid ),Type,Desconhecido ) :-
    Type == incerto,
    Desconhecido == idade,
    involucao( utente( Id,No,Idd,Se,Cid ), positivo ),
    retract( (excecao(utente( IdUt,Nome,Idade,Sexo,Cidade )) :- 
                utente( IdUt,Nome,Idd,Sexo,Cidade )) ).

% permite remover conhecimento incerto sobre cidade de utentes
involucao( utente( Id,No,Idd,Se,Cid ),Type,Desconhecido ) :-
    Type == incerto,
    Desconhecido == cidade,
    involucao( utente( Id,No,Idd,Se,Cid ), positivo ),
    retract( (excecao(utente( IdUt,Nome,Idade,Sexo,Cidade )) :- 
                utente( IdUt,Nome,Idade,Sexo,Cid )) ).
    
% permite instituição desconhecida 
involucao( cuidadoPrestado( Id,Desc,Inst,Cid ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == instituicao,
    involucao( cuidadoPrestado( Id,Desc,Inst,Cid ), positivo ),
    retract( (excecao(cuidadoPrestado( IdServ,Descricao,Instituicao,Cidade )) :- 
                cuidadoPrestado( IdServ,Descricao,Inst,Cidade ) ) ).

% permite custos desconhecidos
involucao( atoMedico( D,IdU,IdS,C ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == custo,
    involucao( atoMedico( D,IdU,IdS,C ), positivo ),
    retract( (excecao(atoMedico( Data,IdUt,IdServ,Custo )) :- 
                atoMedico( Data,IdUt,IdServ,C ) ) ).

% permite serviços desconhecidos
involucao( atoMedico( D,IdU,IdS,C ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == servico,
    involucao( atoMedico( D,IdU,IdS,C ), positivo ),
    retract( (excecao(atoMedico( Data,IdUt,IdServ,Custo )) :- 
                atoMedico( Data,IdUt,IdS,Custo ) ) ).

involucao( [OPT1 | R], Type ) :-
    Type == impreciso,
    solucoes( I, -OPT1::I, Li ),
    testar(Li),
    retract( (excecao( OPT1 )) ),
    involucao( R,impreciso ).

involucao( [], impreciso ).

involucao( utente( Id,No,Idd,Se,Cid ), Type, Impreciso, MenorValor, MaiorValor ) :-
    Type == impreciso,
    Impreciso == idade,
    solucoes( I, -(excecao(utente( Id,No,Idd,Se,Cid )))::I, Li ),
    testar(Li),
    retract( (excecao( utente( Id,No,Idd,Se,Cid ) ) :-
                Idd >= MenorValor,
                Idd =< MaiorValor ) ).

involucao( atoMedico( D,IdUt,IdServ,C ), Type, Impreciso, MenorValor, MaiorValor ) :-
    Type == impreciso,
    Impreciso == custo,
    solucoes( I, -(excecao(utente( Id,No,Idd,Se,Cid )))::I, Li ),
    testar(Li),
    retract( (excecao( atoMedico( D,IdUt,IdServ,C ) ) :-
                C >= MenorValor,
                C =< MaiorValor ) ).

% permite remover conhecimento interdito sobre a cidade de utentes
involucao( utente( Id,No,Idd,Se,Cid ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == cidade,
    retract( (nulo(Cid)) ),
    involucao( utente( Id,No,Idd,Se,Cid ),incerto,cidade ).

% permite remover instituição interdita 
involucao( cuidadoPrestado( Id,Desc,Inst,Cid ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == instituicao,
    retract( nulo(Inst) ),
    involucao( cuidadoPrestado( Id,Desc,Inst,Cid ),incerto,instituicao ).

% permite remover custos interditos
involucao( atoMedico( D,IdU,IdS,C ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == custo, 
    retract( nulo(C) ),
    involucao( atoMedico( D,IdU,IdS,C ), incerto,custo ).

% permite remover serviços interditos
involucao( atoMedico( D,IdU,IdS,C ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == servico,
    retract( nulo(IdS) ),
    involucao( atoMedico( D,IdU,IdS,C ), incerto, servico ).

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

% --- Não se sabe a cidade de onde a utente Paula é proveniente.

utente( 7, paula, 47, feminino, inc0002 ).
excecao( utente( Id,N,I,S,C ) ) :- utente( Id,N,I,S,inc0002 ).

% --- Não se sabe a instituição que disponibiliza o serviço de Neurocirurgia em Évora.

cuidadoPrestado( 7, 'Neurocirurgia', inc0003, 'Evora' ).
excecao( cuidadoPrestado( Id,Desc,Inst,Cid ) ) :- cuidadoPrestado( Id,Desc,inc0003,Cid ).

% --- Não se sabe a data em que o utente cujo IdUt é 3 foi submetido ao tratamento cujo IdServ é 5.

atoMedico( inc0004, 3, 5, 10 ).
excecao( atoMedico( D,IdUt,IdServ,C ) ) :- atoMedico( inc0004,IdUt,IdServ,C ).



% ------------------------- Imperfeito Impreciso -----------------------

% Não se sabe se o/a utente Dolores é do sexo masculino ou feminino.

excecao(utente( 8, dolores, 34, masculino, 'Amadora' )).
excecao(utente( 8, dolores, 34, feminino, 'Amadora' )).

% Não se sabe se o utente Zeca tem 36 ou 37 anos, nem se é da Amadora ou de Sintra.

excecao(utente( 9, zeca, 36, masculino, 'Sintra' )).
excecao(utente( 9, zeca, 37, masculino, 'Sintra' )).
excecao(utente( 9, zeca, 36, masculino, 'Amadora' )).
excecao(utente( 9, zeca, 37, masculino, 'Amadora' )).

% Não se sabe se o utente Alfredo é de Felgueiras ou Lousada.

excecao(utente( 10, alfredo, 22, masculino, 'felgueiras' )).
excecao(utente( 10, alfredo, 22, masculino, 'lousada' )).

% Não se sabe se a utente Alzira tem 23 ou 24 anos.

excecao(utente( 11, alzira, 23, feminino, 'braga' )).
excecao(utente( 11, alzira, 24, feminino, 'braga' )).

% Não se sabe o preço da consulta que ocorreu no dia 29 de Abril de 2017, cujo utente tem o
% IdUt 2 e o serviço prestado tem o IdServ 3, mas sabe-se que o preço foi
% entre os 3 e os 17 euros.

excecao(atoMedico('29-04-2017',2,3,C)) :- C>=3, C=<17.



% ------------------------- Imperfeito Interdito -----------------------

% Não se sabe nem é possível vir a saber a morada do utente António Costa.

utente(12, 'Antonio Costa', 55, masculino, int0001).
excecao( utente( Id,Nome,Idade,Sexo,Morada ) ) :- utente( Id,Nome,Idade,Sexo,int0001 ).
nulo( int0001 ).

% Não se sabe nem é possível vir a saber qual o serviço prestado ao utente cujo IdUt é 12
% no dia 20 de Março de 2017 e cujo preço foi 3000€.

atoMedico( '20-03-2017', 12, int0002, 3000 ).
excecao( atoMedico( Data,IdUt,IdServ,Custo ) ) :- atoMedico( Data,IdUt,int0002,Custo ).
nulo( int0002 ).



% ----------------------------------------------------------------------

% ------------------------- PREDICADOS EXTRA ---------------------------

% Invariante Estrutural
+medico( IdMed,Nome,Idade,Sexo,IdServ ) :: ( solucoes( (IdMed), medico(IdMed,N,I,Se,Servico), S ),
                                comprimento( S,N ),
                                N == 0 ).

+medico( IdMed,Nome,Idade,Sexo,IdServ ) :: ( solucoes( (IdServ), cuidadoPrestado( IdServ,Desc,Inst,Cid ) , S ),
                       comprimento( S,N ),
                       N == 0 ).

-medico( IdMed,Nome,Idade,Sexo,IdServ ) :: ( solucoes( (IdServ), medico( Id,N,I,S,IdServ ) , S ),
                       comprimento( S,N ),
                       N >= 2 ).

% Invariante que impede a inserção de conhecimento positivo ou negativo acerca de conhecimento interdito sobre a cidade de utentes

+medico( Id,No,I,Se,IdServ ) :: (solucoes( (Id,No,I,Se,IdServ), (medico( Id,No,xpto,Se,IdServ ), nulo(xpto)), S ),
                           comprimento( S,N ),
                           N == 0).

+(-medico( Id,No,I,Se,IdServ )) :: (solucoes( (Id,No,I,Se,IdServ), (medico( Id,No,xpto,Se,IdServ ), nulo(xpto)), S ),
                              comprimento( S,N ),
                              N == 0).

% Garantir que não se adicionam exceções relativas à idade a conhecimento perfeito positivo.
+excecao( medico(Id,No,I,Se,IdServ) ) :: ( nao( medico( Id,No,Idd,Se,IdServ ) ) ).

% Garantia da não inserção de exceções repetidas.
+(excecao(medico(Id,No,I,Se,IdServ))) :: ( solucoes( (excecao(medico(Id,No,I,Se,IdServ))), excecao(medico(Id,No,I,Se,IdServ)), S),
                                    comprimento(S,N),
                                    N == 0).

% Pressuposto do Mundo Fechado para o predicado medico
-medico(Id,N,I,S,IdServ) :- 
    nao(medico(Id,N,I,S,IdServ)),
    nao(excecao(medico(Id,N,I,S,IdServ))).


% Extensão do predicado medico: IdMed, Nome, Idade, Sexo, IdServ -> {V, F}

% Conhecimento Positivo

medico( 1, 'Antonio Lemos', 52, masculino, 3  ).
medico( 2, 'Anibal Mota', 59, masculino, 1 ).
medico( 3, 'Catarina Paiva', 35, feminino, 5 ).
medico( 4, 'Jose Garcia', 39, masculino, 2 ).
medico( 5, 'Carla Perez', 41, feminino, 6 ).

% Conhecimento Negativo

-medico( 39, 'Antonio Fernandes', 54, masculino, 4 ).
-medico( 62, 'Jose Azevedo', 61, masculino, 2 ).
-medico( 98, 'Cristina Lopes', 32, feminino, 5 ).

% Conhecimento Incerto

medico( 6, 'Abel Fonseca', inc0005, masculino, 6 ).
excecao( medico( Id,N,I,S,IdServ ) ) :- medico( Id,N,inc0005,S,IdServ ).

% Conhecimento Impreciso

excecao(medico( 7, 'Paulo Guimaraes', 22, masculino, 5 )).
excecao(medico( 7, 'Paulo Guimaraes', 23, masculino, 5 )).

% Conhecimento Interdito

utente(8, 'Rui Andrade', int0003, masculino, 2).
excecao( medico( Id,Nome,Idade,Sexo,IdServ ) ) :- medico( Id,Nome,int0003,Sexo,IdServ ).
nulo( int0003 ).

% Evoluções e Involuções

evolucao( medico( Id,No,Idd,Se,IdS ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == idade,
    evolucao( medico( Id,No,Idd,Se,IdS), positivo ),
    assert( (excecao(medico( IdMed,Nome,Idade,Sexo,IdServ )) :- 
                medico( IdMed,Nome,Idd,Sexo,IdServ ) ) ).

involucao( medico( Id,No,Idd,Se,IdS ), Type, Desconhecido ) :-
    Type == incerto,
    Desconhecido == idade,
    involucao( medico( Id,No,Idd,Se,IdS), positivo ),
    retract( (excecao(medico( IdMed,Nome,Idade,Sexo,IdServ )) :- 
                medico( IdMed,Nome,Idd,Sexo,IdServ ) ) ).

evolucao( medico( Id,No,Idd,Se,IdS ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == idade,
    evolucao( medico( Id,No,Idd,Se,IdS), positivo ),
    assert( (excecao(medico( IdMed,Nome,Idade,Sexo,IdServ )) :- 
                medico( IdMed,Nome,Idd,Sexo,IdServ ) ) ),
    assert( nulo(Idd) ).

involucao( medico( Id,No,Idd,Se,IdS ), Type, Desconhecido ) :-
    Type == interdito,
    Desconhecido == idade,
    retract( nulo(Idd) ),
    involucao( medico( Id,No,Idd,Se,IdS), incerto, idade ).