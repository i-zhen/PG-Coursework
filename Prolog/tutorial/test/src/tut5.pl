% 1
:- dynamic s/2.
s --> [].
s --> a,s,b.
a --> [a].
b --> [b,b].

t(L,L).
t([a|L1],T) :- t(L1,[b,b|T]).

s2 --> a(N),b(N),b(N). 
%表示有N个a，以及2N个b。
a(0) --> [].
a(succ(N)) --> [a], a(N).
%a(N) --> [a], a(M), {N is M + 1}.
b(0) --> [].
b(succ(N)) --> [b], b(N).
% succ是内置函数

%2

d --> [].
d --> [a],d.

xstar(_) --> [].
xstar(X) --> [X], star(X).

%3 Parsing
/*
e --> ee.
e --> ee, to, e.
ee --> n.
e --> ['('],e,[')'].

to --> [+];[-];[*];[/].
n --> [1];[2];[3];[4];[5];[6];[7];[8];[9];[0].
*/

%parser

ast(leaf(_)).
ast(node(Sym, LT, RT)) :- ast(LT), ast(RT).

/*
e(V) --> term(V).
e(V) --> term(V1), to('+'), e(V2), {V = node('+', V1, V2)}.
e(V) --> term(V1), to('-'), e(V2), {V = node('-', V1, V2)}.

term(V) --> fact(V).
term(V) --> fact(V1), to('*'), term(V2), {V = node('*', V1, V2)}.
term(V) --> fact(V1), to('/'), term(V2), {V = node('/', V1, V2)}.
fact(leaf(V)) --> n(V).
*/

e(V) --> ee(V).
e(V) --> ee(V1), to('+'), e(V2), {V = node('+', V1, V2)}.
e(V) --> ee(V1), to('-'), e(V2), {V = node('-', V1, V2)}.
e(V) --> ee(V1), to('*'), e(V2), {V = node('*', V1, V2)}.
e(V) --> ee(V1), to('/'), e(V2), {V = node('/', V1, V2)}.
ee(leaf(V)) --> n(V).

/*
e(V) --> ['('], e(V), [')'].
e(V) --> ['('], e(V1), [')'], to('+'), e(V2), {V = node('+', V1, V2)}.
e(V) --> ['('], e(V1), [')'], to('-'), e(V2), {V = node('-', V1, V2)}.
e(V) --> ['('], e(V1), [')'], to('*'), e(V2), {V = node('*', V1, V2)}.
e(V) --> ['('], e(V1), [')'], to('/'), e(V2), {V = node('/', V1, V2)}.
*/

to('*') --> ['*']. to('/') --> ['/'].
to('-') --> ['-']. to('+') --> ['+'].

n(9) --> [9]. n(8) --> [8]. n(7) --> [7].
n(6) --> [6]. n(5) --> [5]. n(4) --> [4].
n(3) --> [3]. n(2) --> [2]. n(1) --> [1].
n(0) --> [0].

%evaluation

comp(Sym, A, B, R) :-
        Sym == * -> R is A * B, !;
        Sym == + -> R is A + B, !;
        Sym == - -> R is A - B, !;
        Sym == / -> R is A / B.   

eval(leaf(Num), Num).

eval(node(Sym, A, B), R) :-
        eval(A, R1),
        eval(B, R2),
        comp(Sym, R1, R2, R).

start(R, S) :-
        e(R1, S, []),
        eval(R1, R).

%4 Generate
male(bob). male(charlie).
male(david). 
female(alice). female(eve).

neighbour(alice, bob).
neighbour(bob, charlie).
neighbour(charlie, david).
neighbour(david, eve).

%(a)
neighbour_sym(A, B) :- neighbour(A, B) ; neighbour(B, A).

%(b)
person(X) :- male(X); female(X).

test(Doc, Tea, Den, Law, Fir) :-
        Doc \= bob,
        male(Tea), male(Fir),
        neighbour_sym(Fir, Law),
        female(Y),
        neighbour_sym(Y, Den).


%(c)
/*
generate(Doc, Tea, Den, Law, Fir) :-
        person(Doc), 
        person(Tea),
        person(Den),
        person(Law),
        person(Fir),
        Doc \= Tea, Doc \= Den, Doc \= Law, Doc \= Fir,
        Tea \= Den, Tea \= Law, Tea \= Fir,
        Den \= Law, Den \= Fir,
        Law \= Fir.
        */
remove([X|Xs], X, Xs).
remove([X|Xs],Y,[X|Ys]) :- remove(Xs,Y,Ys).

gen([], []).
gen(Xs, [Y|Zs]) :- remove(Xs, Y, Ys), gen(Ys, Zs).

generate(A, B, C, D, E) :- 
        gen([alice,bob,charlie,david,eve], [A,B,C,D,E]).

%(d)
solve(As, Bs, Cs, Ds, Es) :-
        generate(As, Bs, Cs, Ds, Es),
        test(As, Bs, Cs, Ds, Es).


        