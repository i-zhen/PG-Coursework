%% Model solution to tutorial 4
%% James Cheney, Alan Smaill
%% Oct 2015

%%% Part 1 1

anb2n --> [].
anb2n --> [a], anb2n, [b,b].

%% Part 2(a)

astar --> [].
astar --> [a],astar.

%% Part 2(b).
star(_) --> [].
star(X) --> [X],star(X).


%% Part 3
%% (a): Naive grammar for fully parenthesized expressions

exp --> [N], {number(N)}.
exp --> ['('], exp, ['+'], exp,  [')'].
exp --> ['('], exp, ['-'], exp,  [')'].
exp --> ['('], exp, ['*'], exp,  [')'].
exp --> ['('], exp, ['/'], exp,  [')'].

%%(b): Naive grammar with evaluation

exp(N) --> [N], {number(N)}.
exp(V) --> ['('], exp(V1), ['+'], exp(V2),  [')'], {V is V1+V2}.
exp(V) --> ['('], exp(V1), ['-'], exp(V2),  [')'], {V is V1-V2}.
exp(V) --> ['('], exp(V1), ['*'], exp(V2),  [')'], {V is V1*V2}.
exp(V) --> ['('], exp(V1), ['/'], exp(V2),  [')'], {V is V1/V2}.
exp(V) --> ['('], exp(V1), ['^'], [N],  [')'], {number(N)}, {V is exp(V1,N)}.

%% Part 5
%%
%% important to recall that negation is safe only if called
%% on ground goals.

%% given facts

male(bob).
male(david).
male(charlie).

female(alice).
female(eve).

neighbour(alice, bob).
neighbour(charlie, david).
neighbour(bob, charlie).
neighbour(david, eve).

% (a)

neighbour_sym(X,Y) :- neighbour(X,Y); neighbour(Y,X).

% (b)

test(Doc,Tea,Den,Law,Fir) :-
	\+(Doc=bob),
	male(Fir), male(Tea),
	 neighbour_sym(Fir,Law),
	 neighbour_sym(Den,X), female(X).


%% generate ground candidates

remove([X|Xs],X,Xs).
remove([X|Xs],Y,[X|Ys]) :- remove(Xs,Y,Ys).

generate(A,B,C,D,E) :-
	gen([alice,bob,charlie,david,eve],[A,B,C,D,E]).

gen([],[]).
gen(Xs,[Y|Zs]) :- remove(Xs,Y,Ys), gen(Ys,Zs).

%% put it together;
%%  finds two solutions

solve(A,B,C,D,E) :- generate(A,B,C,D,E),
	    test(A,B,C,D,E).
