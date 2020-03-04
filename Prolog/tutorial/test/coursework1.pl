% NAME: YI ZHEN
% ID: s1563190
% Logic Programming : Coursework 1

% 1 prefixes/2
%accRev 原理类似C++ swap 需要一个第三方的值。python和函数式语言的变量交换抽象层次更高。
accRev([],A,A).
accRev([H|T], A, R) :-  accRev(T, [H|A], R).
prefixes(L, M) :- findall(K,append(K,_,L), M1), accRev(M1, [], M).

/* Test:
prefixes([1,2,3],M).
M = [[1,2,3],[1,2],[1],[]] ? ;
no
% source_info
| ?- prefixes([1,2,3],[[1,2,3],[1,2],[1],[]]).
yes
   */

%another way for prefixes/2, without append/3 for prefixes
naiveRev([],[]).
naiveRev([H|T], L) :- naiveRev(T, L2), append(L2, [H], L).
prefix([],_).
prefix([H|T1], [H|T2]) :- prefix(T1, T2).
prefixes2(L, M) :- findall(X, prefix(X, L), M1), naiveRev(M1, M).
/* Test:
prefixes2([1,2,3],M).
M = [[1,2,3],[1,2],[1],[]] ? ;
no
% source_info
| ?- prefixes2([1,2,3],[[1,2,3],[1,2],[1],[]]).
yes
   */

% another thing, not relevant to the coursework :-)
suffixes([], [[]]).
suffixes([H|T], [MH|MT]) :-
        suffixes(T, MT),
        findall(X, member(X, [H|T]), MH).

suffix([],_).
suffix(L, [H|T]):-
        L == [H|T]; suffix(L, T).

%2 square/0

square :-
        read(A),(
                   A == q,   %important, because prolog will try both
                   !;
                   B is A * A,
                   format("(~p)^2 is : ~p~n",[A, B]),
                   square
                   )
        .

%3 
%instead([],_,_,[]).

% mode(+,+,+,-), in this mode, only give ONE possible solution
instead(Term, From, To, H2):-
        nonvar(Term),(
        Term \= From ->                                      % check if we should instead or not 
        H2 = Term ; 
        H2 = To).

% mode(-,+,+,+), in this mode should slove ALL the possible solutions
instead(Term, From, To, H2):-
        var(Term),(
        instead(From, From, To, H2),                         % one possible, Term equals to Subterm
        Term = From ;                                        % cannot cut here
        instead(H2, From, To, H2),                           % another possible, Term dosent equal to Subterm
        Term = H2).


replace_sub([], _, _, []).
replace_sub(Term, Subterm, Subterm1, Term1) :-
        nonvar(Term) -> (                                     % if this isnt a var then replace_sub(+,+,+,-)
                           Term = [H|T], 
                           Term1 = [T1|T2],      
        (compound(H) -> replace(H, Subterm, Subterm1, T1);    % if H is a complex term, do recursion 
        instead(H, Subterm, Subterm1, T1)),                   %% otherwise, instead 
        replace_sub(T, Subterm, Subterm1, T2)), !;            % cut
                    
        (Term1 = [H|T],                                       % if this is a var then replace_sub(-,+,+,+)
         Term = [T1|T2],                       
         (compound(H) -> replace(T1, Subterm, Subterm1, H);   % same to above
          instead(T1, Subterm, Subterm1, H)),
         replace_sub(T2, Subterm, Subterm1, T)).

replace(Term, Subterm, Subterm1, Term1) :- 
        nonvar(Term) -> (                                      % if this isnt a var then replace(+,+,+,-)
        Term =.. [Fun|Args],
        (Term == Subterm -> 
         instead(Term, Subterm, Subterm1, Term1);             
                replace_sub(Args, Subterm, Subterm1, T),               % processing all other Args
                instead(Fun, Subterm, Subterm1, H),                    % processing Function name
                Term1 =.. [H|T])), !;                                  % cut 
        
        (Term1 =.. [Fun|Args],                                 % if this is a var then replace(-,+,+,+)
         (Term1 == Subterm1 ->
          instead(Term, Subterm, Subterm1, Term1);   %原来这里有CUT，会导致结果不完备；现在也不知道为何当初用了CUT
                instead(H, Subterm, Subterm1, Fun),
                replace_sub(T, Subterm, Subterm1, Args),               % same to above
                Term =.. [H|T])).


/*总结一下第一次作业的缺陷：1.审题能力不够，阅读需要加强，读多了，自然就开了。2.代码风格太差，耦合性太高。
   3.逻辑用的不够，思路停滞在面向过程上*/
/*总结一下第一次作业的优点：1.注释相对完整。2.思路清楚。
   3.注意深入挖掘原理。*/

/* test:
| ?- replace(plus(2,plus(3,2)),2,173,Z).
Z = plus(173,plus(3,173)) ? ;
no

| ?- replace(Z,2,173,plus(173,plus(3,173))).
Z = plus(2,plus(3,2)) ? ;
Z = plus(2,plus(3,173)) ? ;
Z = plus(173,plus(3,2)) ? ;
Z = plus(173,plus(3,173)) ? ;
no

| ?- replace(plus(2,plus(3,2)),plus(3,2),88,Z).
Z = plus(2,88) ? ;
no

| ?- replace(Z,plus(3,2),88,plus(2,88)).
Z = plus(2,plus(3,2)) ? ;
Z = plus(2,88) ? ;
no

| ?- replace(X,a,g(b),f(g(b),k(g(b)))).
X = f(a,k(a)) ? ;
X = f(a,k(g(b))) ? ;
X = f(g(b),k(a)) ? ;
X = f(g(b),k(g(b))) ? ;
no
   */

%4 
r(a,b). r(b,c). r(c,d).
r(d,a). r(d,e). r(d,f).
r(f,g).

:- dynamic memnode/1.
memn(A) :- memnode(A).

rep([],A,[[A]]).
rep([H|T],Paths,[H1|T1]):-
           H1 = [Paths|H],
           rep(T,Paths,T1).

paths2([],[]).
paths2([H|T], Ans) :- 
        (\+memnode(H) -> paths(H, H2); 
         H2 = []),
        paths2(T, T2),
        append(T2, H2, Ans).

paths([], []).
paths(F, Paths) :- 
        assert(memnode(F)),
        findall(X, r(F, X), L),                         %extend new nodes
        paths2(L, T),
        rep(T,F,Paths),
        retract(memnode(F)).                            %backtrack
        
/* test:
paths(a,Paths).
Paths = [[a,b,c,d,f,g],[a,b,c,d,f],[a,b,c,d,e],[a,b,c,d],[a,b,c],[a,b],[a]] ? ;
no

Because I used DFS, the order of elements of Paths is reversed.
*/