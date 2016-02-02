#use "list.apl".
#open List.

i	: type.
o	: type.
v	: name_type.
s	: name_type.

var	: v -> i.
app	: (s,[i]) -> i.

tt      : o.
ff      : o.
eq      : (i, i) -> o.
atom    : i -> o.
neg  	: o -> o.
and  	: (o,o) -> o.
or   	: (o,o) -> o.
all	: v\o -> o.
ex	: v\o -> o.


pred qf(o).
qf(tt).
qf(ff).
qf(atom A).
qf(eq(T,U)).
qf(neg P) :- qf(P).
qf(and(P,Q)) :- qf(P),qf(Q).
qf(or(P,Q)) :- qf(P),qf(Q).

pred pnf(o).
pnf(P) :- qf(P).
pnf(all(x\P)),pnf(ex(x\P)) :- pnf(P).

pred	skolem(o,o,[i]).
skolem(all(x\P),all(x\P1),Vs)  :- x # Vs,skolem(P,P1,[var x|Vs]).
skolem(and(P,Q),and(P1,Q1),Vs) :- skolem(P,P1,Vs),skolem(Q,Q1,Vs).
skolem(or(P,Q),or(P1,Q1),Vs)   :- skolem(P,P1,Vs),skolem(Q,Q1,Vs).
skolem(neg(P),neg(P'),Vs)      :- skolem(P,P1,Vs).
skolem(atom(A),atom(A),_).
skolem(eq(A,B),eq(A,B),_).
skolem(ex(x\P),P1,Vs)          :- F#P, P1 = P{app(F,Vs)/var x}.


% assumes "or" has been eliminated
pred pstep(o,o).
pstep(and(all(x\P),Q),all(x\and(P,Q))) :- x # Q.
pstep(and(ex(x\P),Q),ex(x\and(P,Q))) :- x # Q.
pstep(and(Q,all(x\P)),all(x\and(P,Q))) :- x # Q.
pstep(and(Q,ex(x\P)),ex(x\and(P,Q))) :- x # Q.
pstep(neg(ex(x\P)),all(x\neg(P))) :- x # Q.
pstep(neg(all(x\P)),ex(x\neg(P))) :- x # Q.

pstep(and(P,Q),and(P',Q)):- pstep(P,P').
pstep(and(Q,P),and(Q,P')):- pstep(P,P').
pstep(neg(P),neg(P')):- pstep(P,P').
pstep(all(x\P),all(x\P')):- pstep(P,P').
pstep(ex(x\P),ex(x\P')) :- pstep(P,P').

pred prenex_norm(o,o).
prenex_norm(P,P') :- (pstep(P,P'') -> prenex_norm(P'',P') | P = P').


?
P = and(all(x\ex(y\eq(var x,var y))), 
	ex(x\all(y\eq(var x,var y)))),
prenex_norm(P,Q),pnf(Q).

?
P = and (all(x\ex(y\atom(app(p,[var x,var y])))),
       all(y\atom(app(q,[var y])))),
prenex_norm (P, Q),pnf(Q).


? P = and (all(x\ex(y\atom(app(p,[var x,var y])))),
       all(y\atom(app(q,[var y])))),
prenex_norm(P,Q), 
skolem(Q,R,[]).


/*Old

pred	quantifier_free	o.
pred	prenex_normal	o.
quantifier_free t.
quantifier_free f.
quantifier_free (prop P).
quantifier_free (pred1 P T).
quantifier_free (pred2 P T U).
quantifier_free (eq T U).
quantifier_free (neg P) :-  quantifier_free P.
quantifier_free (and P Q) :- quantifier_free P, quantifier_free Q.
quantifier_free (or P Q) :- quantifier_free P, quantifier_free Q.

prenex_normal t.
prenex_normal f.
prenex_normal (prop P).
prenex_normal (pred1 P T).
prenex_normal (pred2 P T U).
prenex_normal (eq T U).
prenex_normal (neg P) :-  quantifier_free P.
prenex_normal (and P Q) :- quantifier_free P, quantifier_free Q.
prenex_normal (or P Q) :- quantifier_free P, quantifier_free Q.
prenex_normal (all (x\P)) :- prenex_normal P.
prenex_normal (ex (x\P)) :- prenex_normal P.


pred	subst (v\A) i A.
subst (a\E) T U :- U is E{T/var a}.

pred	rewrite	o  o .
rewrite A A :- quantifier_free A.
rewrite (neg (all (x\P))) (ex (x\neg Q))
	:- rewrite P Q.
rewrite (neg (ex(x\P))) (all (x\neg Q))
	:- rewrite P Q.

rewrite (and (all (x\Q)) P) (all (x\R)) 
	:- x # P,
	rewrite (and Q P) R.

rewrite (and P (all (x\Q))) (all (x\R)) 
	:- x # P,
	rewrite (and P Q) R.
rewrite (and (ex (x\Q)) P) (ex (x\R)) 
	:- x # P,
	rewrite (and Q P) R.
rewrite (and P (ex (x\Q))) (ex (x\R)) 
	:- x # P,
	rewrite (and P Q) R.
rewrite (or (all (x\Q)) P) (all (x\R)) 
	:- x # P,
	rewrite (or Q P) R.
rewrite (or P (all (x\Q))) (all (x\R)) 
	:- x # P,
	rewrite (or P Q) R.
rewrite (or (ex (x\Q)) P) (ex (x\R)) 
	:- x # P,
	rewrite (or Q P) R.
rewrite (or P (ex (x\Q))) (ex (x\R)) 
	:- x # P,
	rewrite (or P Q) R.

rewrite (ex (y\P)) (ex (y\Q)) :- rewrite P Q.
rewrite (all (x\P)) (all (x\Q)) :- rewrite P Q.

?
rewrite (and (all (x\ ex (y\ eq (var x) (var y)))) 
	     (ex (x\ all (y\ eq (var x) (var y))))) P.

pred	rewrite'	o o.
	
rewrite' (and (all (x\P)) (all (x\Q))) (all (x\and P Q)).

?
rewrite' (and (all (x\ (ex (y\ pred2  p (var  x) (var  y))))) (all (y\ pred1  q (var y)))) Q.

?
skolem (all (x\ ex (y\ pred2  p (var  x) (var  y)))) Q.

type seq = ([o],[o]).

pred infer(seq,[seq]).
infer((G,D),[(P::Q::G,D)]) :- mem ((and P Q),G).
infer((G,D),[(P::G,D),(Q::G,D)]) :- mem ((and P Q),D).
infer((G,D),[(P::G,D),(Q::G,D)]) :- mem ((or P Q),G).
infer((G,D),[(G,P::Q::D)]) :- mem ((or P Q),D).
infer((G,D),[(G,P::D)]) :- mem ((neg P),G).
infer((G,D),[(P::G,D)]) :- mem ((neg P),D).

infer((G,D),[]) :- mem(A,G), mem(A,D).
*/


?P = ex(x\ eq(var(x),var(y))),
 Q = all(y\and(P,P)),
Q' = all (x1\and ((eq (var x37,var x1){app (F38,[var x1])/var x37}),(eq (var x65,var x1){app (F66,[var x1])/var x65}))),
 skolem(Q,Q',[]).
