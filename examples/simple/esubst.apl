exp	: type.
var	: type.
sub	: type.

lam	: exp -> exp.
app	: exp -> exp -> exp.
one	: exp.
subst	: exp -> sub -> exp.

id	: sub.
lift	: sub.
cons	: exp -> sub -> sub.
comp	: sub -> sub -> sub.


pred 	eq	exp exp.
pred 	eq'	sub sub.

eq (app (lam A) B) (subst A (cons B id)).
eq (subst one id) one.
eq (subst one (cons A S)) A.
eq (subst (app B A) S) (app (subst B S) (subst A S)).
eq (subst (lam A) S) (lam (subst A (cons one (comp S lift)))).
eq (subst A (comp S T)) (subst (subst A S) T).

eq' (comp id S) S.
eq' (comp lift id) lift.
eq' (comp lift (cons A S)) S.
eq' (comp (cons A S) T) (cons (subst A T) (comp S T)).
eq' (comp (comp S T) U) (comp S (comp T U)).

pred 	step	exp exp.
pred	step'	sub sub.

step E E' :- eq E E'.
step (app E1 E2) (app E1' E2) :- step E1 E1'.
step (app E1 E2) (app E1 E2') :- step E2 E2'.
step (subst E S) (subst E' S) :- step E E'.
step (subst E S) (subst E S') :- step' S S'.

step' S S' :- eq' S S'.

?step (app (lam (lam one)) (lam one)) E.
