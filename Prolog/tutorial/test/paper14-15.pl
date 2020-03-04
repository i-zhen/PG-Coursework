%problem 1

scale(_, [], []).
scale(X, [Xh | Xs], [Mx | Ms]) :-
        scale(X, Xs, Ms),
        Mx is Xh * X.

% write the comment during exam

%problem 2 

s --> [a], s, t, [z].
s --> [b], u.
s --> [c], t.

t --> [d].
t --> [d], t.

u --> [e].

% s/1 for this problem
s(L) :- s(L, []).


%problem 3 a
occurs(X, Y) :- X == Y.
% the first call of occurs_list that the 2nd argument must not be empty
occurs_list(X, [A | As]) :-
        occurs(X, A) , !;
        length(As, Len),
        Len =\= 0,
        occurs_list(X, As).
occurs(X, T) :-
        nonvar(T),
        T =.. [Fun | Args],
        occurs_list(X, Args).

%problem 3 b
weight(X, Y) :- var(X), Y is 0.
weight(X, Y) :- atomic(X), Y is 1.
weight_list([], Y) :- Y is 0.

weight_list([X | Xs], C) :-
        weight(X, A),
        weight_list(Xs, B),
        C is A + B.

weight(X, T) :-
        nonvar(X),
        X =.. [Fun | Args],
        weight_list(Args, H),
        T is 1 + H.

%problem 4 a
magic([[R11, R12, R13], [R21, R22, R23], [R31, R32, R33]]) :-
         A is R11 + R12 + R13,
         B is R21 + R22 + R23,
         C is R31 + R32 + R33,
         D is R11 + R21 + R31,
         E is R12 + R22 + R32,
         F is R13 + R23 + R33,
         A == B, B == C, C == D, D == E, E == F.

%problem 4 b
remove(X, [X|Xs], Xs).
remove(Y, [X|Xs], [X|Ys]) :- remove(Y, Xs, Ys).

gen([], []).
gen(Xs, [Y|Zs]) :- remove(Y, Xs, Ys), gen(Ys, Zs).

generate([[R11, R12, R13], [R21, R22, R23], [R31, R32, R33]]) :- 
        gen([1,2,3,4,5,6,7,8,9],[R11, R12, R13, R21, R22, R23, R31, R32, R33]).

solve([[R11, R12, R13], [R21, R22, R23], [R31, R32, R33]]) :-
        generate([[R11, R12, R13], [R21, R22, R23], [R31, R32, R33]]),
        magic([[R11, R12, R13], [R21, R22, R23], [R31, R32, R33]]).
