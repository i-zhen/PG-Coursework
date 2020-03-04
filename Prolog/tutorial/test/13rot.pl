/* -*- Mode:Prolog; coding:UTF-8; -*- */

% rot13:  only for mode (+,?) 



rot13(Str, SR) :-
        atom_codes(Str,SL),
        maprot(SL, SL1),
        atom_codes(SR,SL1).

maprot([],[]).
maprot([H|T],[HH|TT]) :- rot2(H,HH),
                         maprot(T,TT).
 
rot(C, C1) :-
    (   member(C, "abcdefghijklmABCDEFGHIJKLM"), C1 is C+13, ! )
    ; ( member(C, "nopqrstuvwxyzNOPQRSTUVWXYZ"), C1 is C-13, ! )
    ; C1 = C.

%2 Using Term I/O

translate :- 
        read(Str),
        rot13(Str,Goal),
        nl,
        print(Goal),
        nl,
        translate.

%3

split([],[],[]).
split([H|T], P, N) :-
        H >= 0, P = [H1|T1], H1 = H, split(T,T1,N);
        H < 0, N = [H2|T2], H2 = H, split(T,P,T2).

split2([],[],[]).
split2([H|T], P, N) :-
        H >= 0, P = [H1|T1], H1 = H, split2(T,T1,N), !;
        H < 0, N = [H2|T2], H2 = H, split2(T,P,T2).

%4 没有惊叹号会不断的重复执行两个相同name的predicates

:- dynamic rotA/2.
rot2(C, C1) :- rotA(C, C1), !.

rot2(C, C1) :-
    ((   member(C, "abcdefghijklmABCDEFGHIJKLM"), C1 is C+13, ! )
    ; ( member(C, "nopqrstuvwxyzNOPQRSTUVWXYZ"), C1 is C-13, ! )
    ; C1 = C), assert(rotA(C, C1)).


buildrot :-
        atom_codes(abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ, TEMP),
        maprot(TEMP,TEMP2),        
        listing.
