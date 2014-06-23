lookup(X,[p(X,Y)|Ys],Y).
lookup(X,[p(X1,Y1)|Ys],Y):-lookup(X,Ys,Y).
comp(X,X).
addelement(X,Y,[X|Y]).
get(1,[X|_],X).
get(I,[X|Xs],T):-I1 is I-1,get(I1,Xs,T).
append([X],Y,[X|Y]).
append([X|Xs],Y,[X|Zs]):-append(Xs,Y,Zs).

or(true,true,true).
or(true,false,true).
or(false,true,true).
or(false,false,false).
and(false,false,false).
and(false,true,false).
and(true,false,false).
and(true,true,true).
not(true,false).
not(false,true).
compare(X,Y,true):- X>Y.
compare(X,Y,false):- X<=Y.
checkequal(T1,T2,true):-T1=T2.
checkequal(T1,T2,false):-T1>T2.
checkequal(T1,T2,false):-T1<T2.

type(H,E,T):-lookup(E,H,T).
type(H,true,bool).
type(H,false,bool).
type(H,(),unit).
type(H,I,int):- integer(I).

type(H,add(E1,E2),T):-type(H,E1,T),type(H,E2,T),comp(T,int).
type(H,mult(E1,E2),T):-type(H,E1,T),type(H,E2,T),comp(T,int).
type(H,orr(E1,E2),T):-type(H,E1,T),type(H,E2,T),comp(T,bool).
type(H,andd(E1,E2),T):-type(H,E1,T),type(H,E2,T),comp(T,bool).
type(H,nott(E1),T):-type(H,E1,T),comp(T,bool).
type(H,greater(E1,E2),T):-type(H,E1,T1),type(H,E2,T1),comp(T1,int),comp(T,bool).
type(H,equals(E1,E2),T):-type(H,E1,T1),type(H,E2,T1),comp(T,bool).
type(H,if(E1,[then(E2),else(E3)]),T):-type(H,E1,bool),type(H,E2,T),type(H,E3,T).
type(H,tuple([E]),T):-type(H,E,T1),addelement(T1,[],T).
type(H,tuple([E|Es]),[T1|T]):-type(H,E,T1),type(H,tuple(Es),T).
type(H,proj(I,tuple([E|Es])),T):- type(H,tuple([E|Es]),T1),get(I,T1,T).
type(H,let(D,E),T):- tyass(H,D,T1),append(T1,H,H1),type(H1,E,T).


tyass(H,equal(X,E),[p(X,T)]):-type(H,E,T).
tyass(H,sequential([D]),T):- tyass(H,D,T).
tyass(H,sequential([D|Xs]),T):-tyass(H,D,T1),append(T1,H,H1),tyass(H1,sequential(Xs),T2),append(T1,T2,T).
tyass(H,parallel([D]),T):-tyass(H,D,T).
tyass(H,parallel([D|Xs]),T):-tyass(H,D,T1),tyass(H,parallel(Xs),T2),append(T1,T2,T).
tyass(H,local(D1,D2),T):-tyass(H,D1,T1),append(T1,H,H1),tyass(H1,D2,T).

value(H,E,T):-lookup(E,H,T).
value(H,true,true).
value(H,false,false).
value(H,(),unit).
value(H,I,I):-integer(I).

value(H,add(E1,E2),T):-value(H,E1,T1),value(H,E2,T2),T is T1+T2.
value(H,mult(E1,E2),T):-value(H,E1,T1),value(H,E2,T2),T is T1*T2.
value(H,orr(E1,E2),T):-value(H,E1,T1),value(H,E2,T2),or(T1,T2,T).
value(H,andd(E1,E2),T):-value(H,E1,T1),value(H,E2,T2),and(T1,T2,T).
value(H,nott(E1),T):-value(H,E1,T1),not(T1,T).
value(H,greater(E1,E2),T):-value(H,E1,T1),value(H,E2,T2),compare(T1,T2,T).
value(H,equals(E1,E2),T):-value(H,E1,T1),value(H,E2,T2),checkequal(T1,T2,T).
value(H,if(E1,[then(E2),else(E3)]),T):- value(H,E1,T1),comp(T1,true),value(H,E2,T).
value(H,if(E1,[then(E2),else(E3)]),T):- value(H,E1,T1),comp(T1,false),value(H,E3,T).
value(H,tuple([E]),T):-value(H,E,T1),addelement(T1,[],T).
value(H,tuple([E|Es]),[T1|T]):-value(H,E,T1),value(H,tuple(Es),T).
value(H,proj(I,tuple([E|Es])),T):- value(H,tuple([E|Es]),T1),get(I,T1,T).
value(H,let(D,E),T):- elab(H,D,T1),append(T1,H,H1),value(H1,E,T).

elab(H,equal(X,E),[p(X,T)]):-value(H,E,T).
elab(H,sequential([D]),T):- elab(H,D,T).
elab(H,sequential([D|Xs]),T):-elab(H,D,T1),append(T1,H,H1),elab(H1,sequential(Xs),T2),append(T1,T2,T).
elab(H,parallel([D]),T):-elab(H,D,T).
elab(H,parallel([D|Xs]),T):-elab(H,D,T1),elab(H,parallel(Xs),T2),append(T1,T2,T).
elab(H,local(D1,D2),T):-elab(H,D1,T1),append(T1,H,H1),elab(H1,D2,T).


























