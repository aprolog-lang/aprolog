nm	: name_type.
proc	: type.

par	: (proc,proc) -> proc.
sum	: (proc,proc) -> proc.
res	: (nm\proc) -> proc.
rep	: proc -> proc.
out	: (nm,nm, proc) -> proc.
in 	: (nm,nm\proc) -> proc.
tau	: proc -> proc.
ina	: proc.

pred 	renamec	(nm\nm, nm, nm).
renamec (n\M,X,Y) :- Y is M{X/n}.

pred 	rename	(nm\proc,nm,proc).
rename(n\P,X,Q) :- Q is P{X/n}.

(* tau 0 *)
?rename(a\tau ina, c, P').

(* in a.<b>0 *)
?rename(a\in(a,b\ina), c, P').
?rename(a\in(a,b\ina), c, P').


(* nu a. c!a | c?b.b!c *)
?rename(a\res(a\par(out(c,a,ina),in(c,b\out(b,c,ina)))), d, P').


act	: type.

tau_a	: act.
out_a	: (nm,nm) -> act.
in_a	: (nm,nm) -> act.


pred 	step	proc act proc.
pred	step'	proc (nm\act) (nm\proc).

step (tau P) tau_a P.
step (sum (P, Q)) A (P') :- step P A P'.
step (sum (P, Q)) A (Q') :- step Q A Q'.
step (par (P, Q)) A (par (P', Q)) :- step P A P'.
step (par (P, Q)) A (par (P, Q')) :- step Q A Q'.
step (par (ina,P)) tau_a P.
step (par (P,ina)) tau_a P.
step (par (P,Q)) tau_a (res (n\par(P',Q'))) 
	:- step' P (n\in_a(X,n)) (n\P'), step' Q (n\out_a(X,n)) (n\Q').
step (par (P,Q)) tau_a (res (n\par(P',Q'))) 
	:- step' P (n\out_a(X,n)) (n\P'), step' Q (n\in_a(X,n)) (n\Q').

step (res (n\P)) A (res (n\P')) :- step P A P', n # A.
step (out (X, Y, P)) (out_a (X, Y)) P.
step (par (P,Q)) tau_a (par (P'',Q'))  :- 
	step' P (y\in_a(X,Y)) (y\P'), 
	step Q (out_a(X,Z)) Q', 
	rename (y\P',Z,P'').
step (par (P,Q)) tau_a (par (P',Q''))  :- 
	step' Q (y\in_a(X,y)) (y\Q'), 
	step P (out_a(X,Z)) P', 
	rename (y\Q',Z,Q'').

step (rep P) A P' :- step (par (P, (rep P))) A P'.

step' (sum (P, Q)) A P' :- step' P A P'.
step' (sum (P, Q)) A Q' :- step' Q A Q'.
step' (par (P, Q)) A (m\par (P', Q)) :- step' P A (m\P').
step' (par (P, Q)) A (m\par (P, Q')) :- step' Q A (m\Q').
step' (in (X, (y\P))) (y\in_a (X,y)) (y\P).
step' (res (n\P)) A (m\res (n\P'))  
	:- n # A,
	   step' P A (m\P').
step' (res (y\M)) (y\out_a (X, y)) (y\res (n\M'))
	:- y # X, step M (out_a(X,y)) M'.


?step (res(a\par(out(c,a,ina),in(c,b\out(b,c,ina))))) A P.
?step (par(out(c,a,ina),in(c,b\out(b,c,ina)))) A P.
?step (res(b\in(a,b\out (a,b,ina)))) A P.
?step (par(res(x\out (a,x,in(x,y\ina))),in(a,x\out(x,a,ina)))) A P.

?step (res(a\par(out(c,a,ina),in(c,b\out(b,c,ina))))) A P.
?step (res(b\in(b,a\out (a,b,ina)))) A P.
?step (par(res(x\out(a,x,in(x,y\ina))),in(a,x\out(x,a,ina)))) A P.



