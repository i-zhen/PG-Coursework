%% Tutorial 4 (Week 6) sample solutions

%% 1.  Cut & negation quiz.

r(1). r(2).
s(1). s(3).

%% This is to give practice with following what happens 

% | ?- r(X),!,s(Y).
% X = 1,
% Y = 1 ? 
% yes
% | ?- r(X), s(Y), !.
% X = 1,
% Y = 1 ? ;
% no
% | ?- r(X), \+(s(X)).
% X = 2 ? ;
% no
% | ?- r(X), !, \+(s(X)).
% no
% | ?- r(X), \+(r(X)).
% no
% | ?- \+(\+(r(X))). 
% true ? ;
% no
% | ?- \+(\+(r(3))).
% no



%2 I/O

translate :- read(X),
	     rot13(X,Y),
	     nl,
	     write(Y),
	     nl,
	     translate.



%% 3 Using cut

%% without cut:

split([],[],[]).

split([H|T],[H|Pos],[Neg]) :-
	H >= 0, split(T,Pos,Neg).
split([H|T],[Pos],[H|Neg]) :-
	H <  0, split(T,Pos,Neg).

%% cut backtracking when first arithmetic goal succeeds;
%% do not omit second test, though.
%% cut can also be placed at end of clause.

split2([],[],[]).

split2([H|T],[H|Pos],Neg) :-
	H >= 0, !, split2(T,Pos,Neg).
split2([H|T],Pos,[H|Neg]) :-
	H <  0, split2(T,Pos,Neg).

%% 6 Tabling  caesar
:- dynamic rotA/2.

%% given code

% rot13:
% only for mode (+,?)
rot13(Str, SR) :- atom_codes(Str,SL),
	          maprot(SL, SL1),
                  atom_codes(SR,SL1).
maprot([],[]).
maprot([H|T],[HH|TT]) :- rot(H,HH),
                         maprot(T,TT).
rot(C, C1) :-
     ( member(C, "abcdefghijklmABCDEFGHIJKLM"), C1 is C+13, ! )
   ; ( member(C, "nopqrstuvwxyzNOPQRSTUVWXYZ"), C1 is C-13, ! )
   ; C1 = C.

%%  added memoisation:
%% --  remember to call buildrot/0 before testing!

%% assert default case at the *end* of the table.
buildrot :- caesartable(T), assertallpairs(T), assertz(rotA(C,C)).
caesartable(Table) :-
	setof((C1,C2), allrot(C1,C2),Table).

% version of rot that will backtrack
allrot(C, C1) :-
     ( member(C, "abcdefghijklmABCDEFGHIJKLM"), C1 is C+13)
   ; ( member(C, "nopqrstuvwxyzNOPQRSTUVWXYZ"), C1 is C-13).

assertallpairs([]).
assertallpairs([(X,Y)|T]) :- assert(rotA(X,Y)), assertallpairs(T).

caesarlist_2([],[]).
caesarlist_2([X|L],[Y|M]) :- rotA(X,Y), !, caesarlist_2(L,M).

caesar_2(X,Y) :- atom_codes(X,L),
        caesarlist_2(L,M),
        atom_codes(Y,M).

test :- read(X),
        caesar_2(X,Y),
        nl,
        write(Y),
        nl,
        test.



%% 5 a
%% some test data

person(fred).
person(peter).
person(ann).
person(beth).
person(tom).
person(talullah).
age(peter,10).
age(ann,5).
age(beth,10).
age(tom,8).

% (a)

unknownAge( People ) :- bagof( X, (person(X), \+(age(X,_Age))), People).

% (b) i

knownAge( People ) :- setof( X, Age^(person(X), age(X,Age)), People ).

% ii

knownAges( Ages ) :- setof( Age, X^(person(X), age(X,Age)), Ages ).


%% 5 b Setof/bagof

flatten(Ls,Xs) :- setof(X, Y^(member(Y,Ls), member(X,Y)),Xs).
flatten2(Ls,Xs) :- bagof(X, Y^(member(Y,Ls), member(X,Y)),Xs).
flatten3(Ls,Xs) :- findall(X, Y^(member(Y,Ls), member(X,Y)),Xs).

flatten4(Ls,Xs) :- setof(X, (member(Y,Ls), member(X,Y)),Xs).
flatten5(Ls,Xs) :- bagof(X, (member(Y,Ls), member(X,Y)),Xs).
flatten6(Ls,Xs) :- findall(X, (member(Y,Ls), member(X,Y)),Xs).


