/*
s(X) :- np(Y), vp(Z), append(Y,Z,X).
np(Y) :- det(M), n(N), append(M,N,Y).
vp(Z) :- v(V), np(Y), append(V,Y,Z).
vp(Z) :- v(Z).

det([a]). det([the]).
n([woman]). n([man]).
v([shoots]).

s(X, Z) :- np(X, Y), vp(Y, Z).
np(X, Z) :- det(X, Y), n(Y,Z).
vp(X, Z) :- v(X, Y), np(Y, Z).
vp(X, Z) :- v(X, Z).

det([the|W], W).
det([a|W], W).

n([woman|W],W).
n([man|W],W).

v([shoots|W],W).

s --> np, vp.
np --> det, n.

vp --> v,np.
vp --> v.

det -->[the].
det -->[a].

n --> [woman].
n --> [man].

v --> [shoots].

reverse_dl([],T/T).
reverse_dl([X|Xs],T/Rs) :- 
        reverse_dl(Xs,[X|T]/Rs).
*/

s(a,b). s(b,c). s(c,d). s(d,a). s(d,e). s(e,f). s(d,g).

%reach the goal

goal(_).

bfs([[Node|Path]|_], [Node|Path]) :-  %Node就是队列中最后一个结点，这个队列的顺序是反着的，然后Path是从起始结点到达此节点的整条路径。
        goal(Node).                  %判断是否达到目标结点

extend([Node|Path], NewPath) :-                   %扩展的的过程中使用［Node｜Path］的形式装包
        bagof([Newnode, Node|Path],               %有个问题，如果无法扩展该怎么办呢？NewPath应当得到什么样的值呢。Ans：空表
              (s(Node, Newnode),
               \+member(Newnode, [Node|Path])),
              NewPath), ! .                       %论cut在prolog中的重要性
           % ; NewPath = [] 另一种写法

extend(_Path, []).                                %这个谓词的顺序一定要放在上个extend/2之后，这是因为prolog自身的搜索顺序问题。搜索顺序在Prolog中很重要。
                

bfs([Path|Paths], Solution) :-
        extend(Path, NewPath),              %从队列首部取出一个Path，没错，是一整条Path。在C++，BFS实现当中我们也需要记录整条Path，然后压成Hash用来判重。
        append(Paths, NewPath, Pathsnew),   %新的结点及其队列压入BFS对别的尾部。
        bfs(Pathsnew, Solution).            %开始验证，并决定是否继续迭代。

bfs_start(N, P) :- bfs([[N]], P).

bfs_dl([[Node|Path]|_], _, [Node|Path]) :-
        goal(Node).

bfs_dl([Path|Paths], Z, S) :-
        extend(Path, NewPath),
        append(NewPath, Z1, Z),
        Paths \== Z1,                       %要保证(Paths, Z1)不是空的差表才能继续扩展，否则会出现P = [_A|_B] ?这样的结果。
        bfs_dl(Paths, Z1, S).

bfs_start_dl(N,P) :- bfs_dl([[N] | X], X, P).


d(f(X),f(Y)):-d(X,Y).
d(f(X),Y) :-d(X,Y).
d(g(X),g(Y)):-d(X,Y).
d(a,a).

/*
flatten(X,[X]) :- var(X), !.
flatten([],[]) :- !.
flatten([H|T], L3) :-
        !,
        flatten(H, L1),
        flatten(T, L2),
        append(L1, L2, L3).
flatten(X,[X]).

p(a):- \+q(X).
q(a).
*/


%fla(Ls, Xs) :- findall(X, Y^(member(Y,Ls), member(X,Y)),Xs), nonempty(Ls).

flatten(Y,[X]) :- var(Y), atomic(X), Y = [[X]], !.
flatten([],[]).
flatten(A, B) :- var(A), !,
                 append(Hf, Tf, B), \+Hf==[],
                 flatten(T, Tf),
                 append([Hf],T,A).

nonempty(B) :- \+member([], B).
flatten(Ls, Xs) :- var(Xs), findall(X, Y^(member(Y,Ls), member(X,Y)),Xs), nonempty(Ls).
