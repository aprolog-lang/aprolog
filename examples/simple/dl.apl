
v	: name_type.
exp	: type.
test	: type.
o	: type.
prog	: type.
pterm	: type.

var	: v -> exp.
z	: exp.
s	: exp -> exp.
plus	: (exp, exp) -> exp.
times	: (exp,exp) -> exp.

eq	: (exp,exp) -> test.
leq	: (exp,exp) -> test.
neg	: test -> test.

f	: o.
imp	: (o,o) -> o.
box	: (prog,o) -> o.
tpred	: test -> o.
all	: v\o -> o.

assign	: (v,exp) -> prog.
seq	: (prog,prog) -> prog.
choose	: (prog,prog) -> prog.
star	: prog -> prog.
tprog	: test -> prog.

pv	: name_type.

seqi	: pterm -> pterm.
assigni	: pterm -> pterm.
choosei	: (pterm,pterm) -> pterm.
stari	: (pterm,o,pv\pterm,pv\pterm) -> pterm.
testi	: pterm -> pterm.
impe	: (pterm,pterm) -> pterm.
impi	: pv\pterm -> pterm.
alli	: pterm -> pterm.
alle	: (pterm,exp,pterm) -> pterm.
pvar	: pv -> pterm.


pred nd	([(pv,o)], pterm, o).
pred ad	([(pv,o)], pterm, o).

nd (G,seqi(E),box(seq(C1,C2),P)) :- nd(G,E,box(C1,box(C2,P))).

(* Incorrect: need to rename V in hypothesis and P to a fresh name *)
nd (G,assigni(E),box(assign(V,T),P))  :- 
	nd(G,E,imp(tpred(eq(var V,T)),P)).
nd (G,choosei(E1,E2),box(choose(C1,C2),P)) :- 
	nd(G,E1,box(C1,P)), nd(G,E2,box(C2,P)).
nd (G,stari(E1,I,p\E2,q\E3),box(star(C),P)) :- p # G, q # G,
	nd(G,E1,I), nd([(p,I)],E2,box(C,I)), nd([(q,I)],E3,P).
nd (G,testi(E),box(tprog(T),P)) :- nd(G,E,imp(tpred(T),P)).
nd (G,impi (p\E), imp(P1,P2)) :- p # G, nd([(p,P1)|G],E,P2).
nd (G,alli E, all(x\P)) :- x # G, nd(G,E,P).
nd (G, E, tpred(T)) :- ad(G,E, tpred(T)).
nd (G, E, f) :- ad(G,E,f).

ad ([(V,P)|G],pvar V,P).
ad ([(W,_)|G],pvar V,P) :- ad(G,pvar V,P).


?
nd([], E, all(x\ imp(tpred(eq(var x,s(z))),box (assign(x,z),tpred(eq(var x,z)))))).
