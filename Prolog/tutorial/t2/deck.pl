cards(ace).
cards(deuce).
cards(three).
cards(four).
cards(five).
cards(six).
cards(seven).
cards(eight).
cards(nine).
cards(ten).
cards(jack).
cards(queen).
cards(king).

suits(spades).
suits(hearts).
suits(clubs).
suits(diamonds).

deck([(ace,spades),(deuce,spades),(three,spades),(four,spades),
	(five,spades),(six,spades),(seven,spades),(eight,spades),
	(nine,spades),(ten,spades),(jack,spades),(queen,spades),
	(king,spades),
	(ace,hearts),(deuce,hearts),(three,hearts),(four,hearts),
	(five,hearts),(six,hearts),(seven,hearts),(eight,hearts),
	(nine,hearts),(ten,hearts),(jack,hearts),(queen,hearts),
	(king,hearts),
	(ace,clubs),(deuce,clubs),(three,clubs),(four,clubs),
	(five,clubs),(six,clubs),(seven,clubs),(eight,clubs),
	(nine,clubs),(ten,clubs),(jack,clubs),(queen,clubs),
	(king,clubs),
	(ace,diamonds),(deuce,diamonds),(three,diamonds),(four,diamonds),
	(five,diamonds),(six,diamonds),(seven,diamonds),(eight,diamonds),
	(nine,diamonds),(ten,diamonds),(jack,diamonds),(queen,diamonds),
	(king,diamonds)]).

%1
%(a)
node(leaf(4),node(leaf(6),leaf(8))).

%(b)
mirror(leaf(L), leaf(L)).
mirror(node(TL, TR), node(TR_2, TL_2)) :- mirror(TR, TR_2), mirror(TL, TL_2).

%(c)
fringe(leaf(L), [L]).
fringe(node(TL,TR), Fringe) :-
    fringe(TL, LF),
    fringe(TR, RF),
    append(LF, RF, Fringe).

%(d)

fringe2(leaf(L), [L]).
fringe2(node(leaf(L),R), [L|F]) :-
    fringe2(R,F).

fringe2(node(node(LL, LR),R),F) :-
    fringe2(node(LL,node(LR,R)), F).

%2

shuffle([], L, L).
shuffle([X|L], H, [X|N]) :-
    shuffle(H, L, N).

%3 
deal([X],[X],[],[],[]).
deal([X,Y],[X],[Y],[],[]).
deal([X,Y,Z],[X],[Y],[Z],[]).
deal([],[],[],[],[]).
deal(Cards, H1, H2, H3, H4) :-
    Cards = [X1, X2, X3, X4 | Tail],
    H1 = [X1 | T1],
    H2 = [X2 | T2],
    H3 = [X3 | T3],
    H4 = [X4 | T4],
    deal(Tail, T1, T2, T3, T4).

deal2([],[],[],[],[]).
deal2([X|Cards], [X|H1], H2, H3, H4) :-
    deal2(Cards, H2, H3, H4, H1).

%4
same_length([],[]).
same_length([X|L], [Y|L_2]) :-
    same_length(L,L_2).

cut([],[],[]).
cut(L, M, N) :- 
    append(M, N, L),
    same_length(M, N).

cut_2(L, M, N) :- 
    append(L1, L2, L),
    length(L1, Len1),
    length(L2, Len2),
    Len1 = Len2,
    M = L1,
    N = L2.
