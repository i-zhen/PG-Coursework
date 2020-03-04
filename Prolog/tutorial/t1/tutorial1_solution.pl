% Model answers to tutorial 1
% James Cheney
% Sept. 27, 2009

% Part 1: can just run these through Sictsus.

% Part 2:

person(X) :- male(X).
person(X) :- female(X).

employer(X) :- employs(X,_).

parent(X,Y) :- father(X,Y).
parent(X,Y) :- mother(X,Y).

classmate(X,Y) :- teaches(Z,X), teaches(Z,Y).

sibling(X,Y) :- parent(Z,X), parent(Z,Y).

grandparent(X,Z) :- parent(X,Y), parent(Y,Z).

query1(Employer) :- sibling(bart,Sibling), 
	teaches(Teacher,Sibling), 
	employs(Employer,Teacher).

% Part 3 

parent_disj(X,Y) :- father(X,Y); mother(X,Y).

% Part 4

% The naive approach to making friend/neighbor symmetric makes the proof
% search space infinite.
% One sensible way to avoid the infinite search is to use disjunction
% to define the symmetric closure of the friend/neighbor relations

friend_sym(X,Y) :- friend(X,Y); friend(Y,X).
neighbor_sym(X,Y) :- neighbor(X,Y); neighbor(Y,X).


query2(Catchphrase) :- friend_sym(milhouse, Friend),
	parent(Parent,Friend),
	neighbor_sym(Parent, Neighbor),
	catchphrase(Neighbor, Catchphrase).

% Part 5 
aunt(X,Y) :- female(X), parent(Z,Y), sibling(Z,X).
uncle(X,Y) :- male(X), parent(Z,Y), sibling(Z,X).

% Part 6a.

classmate_neq(X,Y) :- teaches(Z,X), teaches(Z,Y), X \= Y.
sibling_neq(X,Y) :- parent(Z,X), parent(Z,Y), X \= Y.

% We can also make aunt and uncle behave better using the
% irreflexive version of sibling.

aunt_neq(X,Y) :- female(X), parent(Z,Y), sibling_neq(Z,X).
uncle_neq(X,Y) :- male(X), parent(Z,Y), sibling_neq(Z,X).

% Part 6b.

people_with_no_catchphrase(X) :- person(X), \+(catchphrase(X,_)).
adults_with_no_catchphrase(X) :- people_with_no_catchphrase(X), \+(child(X)).

% Experimenting with ordering should suggest that it's better to have 
% positive goals first, that will bind the variables, then to 
% do the negated goals.  Doing things the other way around will 
% yield strange behavior.  We'll discuss this in more detail later
% in the class when we discuss cuts and negation.
