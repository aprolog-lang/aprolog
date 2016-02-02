id	: name_type.
cid	: name_type.
exp	: type.

var	: id -> exp.
lam	: id\exp -> exp.
app	: exp -> exp -> exp.
mu	: cid\exp -> exp.
pass	: cid -> exp -> exp.

pred	member	A [A].
member X (X::L).
member X (Y::L) :- member X L.

pred	subst	(id\exp) exp exp.
subst(a\E) T E' :- E' is E{T/var a}.

pred	napp	(cid\exp) exp exp.
(* Note that this is just performing the rewriting rule:
   pass a E1 -> pass a (app E1 E)
   uniformly everywhere.  *)
napp (a\var Y) E (var Y).
napp (a\app E1 E2) E (app E1' E2')
	:- napp (a\E1) E E1', napp (a\E2) E E2'.
napp (a\lam (y\E1)) E (lam (y\E1')) :- y # E,
	napp (a\E1) E E1'.
napp (a\mu (a\C)) E (mu (a\C')) :- a # E,
	napp (a\C) E C'.
napp (a\pass a E1) E (pass a (app E1' E))
	:- napp (a\E1) E E1'.
napp (a\pass B E1) E (pass B E1) :- a # B.

ty	: type.
==>	: ty -> ty -> ty.
infixr  ==> 	3.
bot	: ty.

type 	ctx A = [(A,ty)].

pred	tc	(ctx id) exp ty (ctx cid).

tc G (var X) T D :- member (X,T) G.
tc G (lam (x\E)) (T1 ==> T2) D :- x#G,
	 tc ((x,T1)::G) E T2 D.
tc G (app E1 E2) T2 D
	:- tc G E1 (T1 ==> T2) D,
	   tc G E2 T1 D.
tc G (mu (x\E)) T D :- x#D,
	 tc G E bot ((x,T)::D).
tc G (pass A E) bot D 
	:- member (A,T) D, 
	   tc G E T D.


?tc [] (lam (x\ (lam (y\ app (var y) (var x))))) T [].

?tc [] (mu (a\ (pass a (lam (x\ lam (y\ app (var x) (var y))))))) T [].

?tc [] (lam (x\ mu (a\ pass a (var x)))) T [].

(*? tc [] (app (mu (a\ pass a (lam (x\ pass a (lam (z.var z)))))) (lam (z.var z))) T [].*)

?tc [] (lam (y\ mu (b\ pass b (app (var y) (lam (x\ mu (a\ pass b (var x)))))))) T [].

?tc [] (lam (x\ mu (a\ app (var x) (lam (y\ pass a (var y)))))) T [].

