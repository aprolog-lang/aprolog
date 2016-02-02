
v	: name_type.
exp	: type.
tp	: type.

lolli	: (tp, tp) -> tp.
tensor	: (tp,tp) -> tp.
one	: tp.
with	: (tp,tp) -> tp.
top	: tp.
plus	: (tp,tp) -> tp.
zero	: tp.
bang	: tp -> tp.

var	:  v -> exp.
lam	: v\exp -> exp.
app	: (exp,exp) -> exp.

pair	: (exp,exp) -> exp.
letpair	: (exp,v\v\exp) -> exp.

u	: exp.
letunit	: (exp,exp) -> exp.

withpair: (exp,exp) -> exp.
proj1	: exp -> exp.
proj2	: exp -> exp.

inl	: exp -> exp.
inr	: exp -> exp.
case	: (exp,v\exp,v\exp) -> exp.

lift	: exp -> exp.
letbang	: (exp,v\exp) -> exp.

pred tclookup ([(v,tp)],v,tp,[(v,tp)]).

tclookup([(A, T)|G],A,T,G).
tclookup([(B, U)|G1],Y,T,[(B,U)|G2]) :-  tclookup(G1,Y,T,G2).

pred tc	([(v,tp)], [(v,tp)],exp,tp,[(v,tp)]).
tc(D,G1,var X, T, G2) :- tclookup(G1,X,T,G2).
tc(D,G,var X, T, G) :- tclookup(D,X,T,D2).
tc(D,G1,lam (x\E), lolli(T1,T2), G2) :- x # D, x # G1, tc(D,[( x,T1)|G1],E,T2,G2), x # G2.
tc(D,G1,app(E1, E2), T, G3) :- 
	tc(D,G1,E1,lolli(T0,T),G2), tc(D,G2,E2,T0,G3).
tc(D,G1,pair(E1, E2), tensor(T1,T2),G3) :-  
	tc(D,G1,E1,T1,G2), tc(D,G2,E2,T2,G3).
tc(D,G1,letpair(E1,x\y\E2),T,G3) :- x # G, y # G,
	tc(D,G1,E1,tensor(T1,T2),G2),
	tc(D,[( x,T1),( y,T2)|G2], E2, T, G3),
	x # G3, y # G3.
tc(D,G1,u,one,G1).
tc(D,G1,letunit (E1,E2),T,G3) :- 
	tc(D,G1,E1,one,G2),
	tc(D,G2,E2,T,G3).
tc(D,G1,withpair(E1,E2), with(T1,T2),G2) :-
	tc(D,G1,E1,T1,G2),
	tc(D,G1,E2,T2,G2).
tc(D,G,proj1 E, T1, G2) :- tc(D,G,E,with(T1,T2),G2).
tc(D,G,proj2 E, T2, G2) :- tc(D,G,E,with(T1,T2),G2).
tc(D,G1,inl E, plus(T1,T2), G2) :- tc(D,G1,E,T1,G2).
tc(D,G1,inr E, plus(T1,T2), G2) :- tc(D,G1,E,T2,G2).
tc(D,G1,case(E,x\E1,y\E2),T,G3) :- x # D,x # G1, y # D, y # G1,
	tc(D,G1,E,plus(T1,T2),G2),
	tc(D,[( x,T1)|G2],E1,T,G3),
	tc(D,[( y,T2)|G2],E2,T,G3),
	x # G3,
	y # G3.
tc(D,G,lift E, bang T, G) :- tc(D,[],E,T,[]).
tc(D,G1,letbang (E1,x\E2), T, G3) :- x # D,x # G1,
	tc(D,G1,E1,bang T1, G2),
	tc([( x,T1)|D],G2,E2,T,G3).


(* Todo: Type inference in presence of top *)

?
tc([],G,lam(x\ letbang (var x,x\ pair (lift(proj1 (var  x)), lift(proj2 (var  x))))), T, G').

?
tc([],[],lam(x\ letpair (var x,x\y\ letbang (var x,x\ letbang (var  y,y\lift (withpair(var  x,var  y)))))),T,[]).

(* some impossible queries *)
?
tc([],[],lam(x\ letpair (var x,x\y\ pair(var  x, var x))),T,[]).
?
tc([],[],lam(x\ letpair (var x,x\y\ withpair(var  x, var y))),T,[]).

