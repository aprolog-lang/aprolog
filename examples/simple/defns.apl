(* Tests for definitional equality *)

a : name_type.
i : type.


var : a -> i.
app : i -> i -> i.
lam : a\i -> i.
f : i -> i.
g : i -> i -> i.
c : i.

func two = i.
two = lam (x\ lam (y\ app (var x) (app (var x) (var y)))).
func comp = i.
comp = lam (x\ lam (y\ lam (z\app (var x) (app (var y) (var z))))).

func subst i a i = i.
subst E X (var X) = E.
subst E X (var Y) = (var Y) :- not(X = Y).
subst E X (app E1 E2) = app (subst E X E1) (subst E X E2).
subst E X (lam (y\E')) = lam (y\(subst E X E')).
subst E X c = c.
subst E X (f E') = f (subst E X E'). 
subst E X (g E1 E2) = g (subst E X E1) (subst E X E2).

?subst (lam (y\var x)) y (lam (x\var y)) = E.

func eval i = i.
eval (var X) = (var X).
eval (app E1 E2) = eval (subst E2 x E1')
	:- eval E1 = lam (x\E1').
eval (lam E) = lam E.
eval (f E) = f (eval E).
eval c = c.
eval (g E1 E2) = g (eval E1) (eval E2).

func id = i.
id = lam (a\ var a).

func ff = i.
ff = lam (x\ f(var x)).

func apps i [i] = i.
apps H [] = H.
apps H (T::TS) = apps (app H T) TS.

type plist A = list (A, A).
 
pred foo (plist int).

foo [(1,1)].

