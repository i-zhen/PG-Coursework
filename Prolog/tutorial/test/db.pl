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

%5
flatten([],[]).
flatten(H,[H]):- 
        H\=[], H\=[_|_].
flatten([H|T], L) :- 
         flatten(H, Hf),
         flatten(T, Tf),
         findall(Ele,(member(Ele,Hf);member(Ele,Tf)),L).

% setof(Ele,(member(Ele,Hf);member(Ele,Tf)),L).
% bagof(Ele,(member(Ele,Hf);member(Ele,Tf)),L).

/*
flatten([H|T], L) :- 
         (H\=[], H\=[_|_],Hf=[H];
         flatten(H, Hf)),
         flatten(T, Tf),
         findall(Ele,(member(Ele,Hf);member(Ele,Tf)),L).   

flatten([], []).
flatten([H|T], L) :- 
         flatten(H, Hf),
         flatten(T, Tf),
         findall(Ele,(member(Ele,Hf);member(Ele,Tf)),L).
flatten([H|T1], [H|T2]) :-
        H \= [],
        H \= [_|_],
        flatten(T1,T2). 
        */

% H\=[] 和 H\=[_|_] 约束了H只能是单一元素

flat(LS, XS):- findall(X, (member(Y,LS), member(X,Y)),XS).