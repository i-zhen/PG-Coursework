%% Model solution to tutorial 2
%% James Cheney, Alan Smaill
%% October 2015

%% Part 1a

node( leaf(4), node( leaf(6), leaf(8) )).

%% Part 1b

mirror(leaf(L),leaf(L)).
mirror(node(TL,TR),node(TL1,TR1)) :- mirror(TL,TR1), mirror(TR,TL1).

%% Part 1c

fringe( leaf(L), [L] ).
fringe( node(L,R), Fringe ) :-
    fringe(L, F1), fringe(R, F2), append(F1,F2, Fringe).

%%  Note that this is reversible (generates all trees for
%%  given fringe on backtracking when called in mode (-,+).
%%
%%  Complexity:  bad!, much repeated use of append.
%%  In terms of size of fringe, and worst case, when
%%  every subtree is of shape node(node(...),leaf(...)),
%%  T(0) = 1, T(n+1) = T(n) + 1 + T(n), so exponential.
%%  (same applies for complexity in number of nodes + leaves).


%% Part 1d

fringe2( leaf(L), [L] ).
fringe2( node( leaf(L), R ), [L|Rest] ) :-  fringe2( R, Rest ).
fringe2( node( node(L,R), R2 ), Fringe ) :-
        fringe2( node( L, node( R, R2 ) ), Fringe ).  

%% Part 2

simple_shuffle([],L,L).
simple_shuffle(L,[],L).
simple_shuffle([X|L],[Y|M],[X,Y|N]) :- simple_shuffle(L,M,N).

%% The problem with this simple shuffle predicate is that it's 
%% nondetermininstic: it produces two answers because of the overlapping 
%% clauses.

%% Here's a better way that picks a card from the first deck and then 
%% swaps the decks.

shuffle([],L,L).
shuffle([X|L],M,[X|N]) :- shuffle(M,L,N).

% Part 3
% A clunky solution

deal(Cards, H1, H2, H3, H4) :- deal1(Cards, H1, H2, H3, H4).

deal1([C|Cards], [C|H1], H2, H3, H4) :- deal2(Cards, H1, H2, H3, H4).
deal1([],[],[],[],[]).
deal2([C|Cards], H1, [C|H2], H3, H4) :- deal3(Cards, H1, H2, H3, H4).
deal2([],[],[],[],[]).
deal3([C|Cards], H1, H2, [C|H3], H4) :- deal4(Cards, H1, H2, H3, H4).
deal3([],[],[],[],[]).
deal4([C|Cards], H1, H2, H3, [C|H4]) :- deal1(Cards, H1, H2, H3, H4).
deal4([],[],[],[],[]).

% Jiansen's superior solution

deal0([],[],[],[],[]).
deal0([C1,C2,C3,C4|Cards],[C1|H1],[C2|H2],[C3|H3],[C4|H4]) :-
	deal0(Cards,H1,H2,H3,H4).

%Alex's even better solution

dealx([],[],[],[],[]).
dealx([C|Cards],[C|H1],H2,H3,H4) :- dealx(Cards, H2,H3,H4,H1).


%% Part 4

cut(Deck,Pile1,Pile2) :- append(Pile1,Pile2,Deck), equalsize(Pile1,Pile2).

same_length([],[]).
same_length([_|Xs],[_|Ys]) :- same_length(Xs,Ys).

