(* zeta-calculus *)
(* does not work well without equivariance *)
#use "list.apl".

id : name_type.

namespace z (
	nm : name_type.
	exp : type.

	type zeta = id\exp.
        type obj = [(nm,zeta)].
	var : id -> exp.
	obj : obj -> exp.
	sel : exp -> nm -> exp.
	upd : nm\exp -> zeta -> exp.

	func fv exp = [id].
	func fvz zeta = [id].
	func fvs obj = [id].

	fv (var X) = [X].
	fv (obj L) = fvs L.
	fv (sel A _) = fv A.
	fv (upd (x\A) Z) = L' :- List.append ( fv(A),fvz Z,L').
	fvz (y\B) = L :- List.remove(y,fv B,L).
	fvs [] = [].
	fvs ((_,Z)::L) = L' :- List.append(fvz Z,fvs L, L').


	func subst (id\A,exp)  = A.
	subst(x\A,E) = A' :- A' is A{E/var x}.
	
	func update ([(A,B)],A,B) =  [(A,B)].
	update ((A,_)::L,A, B) = (A,B)::L.
	update ((A',B')::L,A, B) =  (A',B')::(update(L,A,B)) :- A # A'.

	func step exp = exp.
        step (sel (obj O) L) = subst(y\B,obj O) :- List.mem((L,y\B),O).
	step (upd (l\obj O) Z) = obj (update(O,l,Z)).

	pred eval exp exp.
	eval (obj O) (obj O).
	eval (sel A L) V 
		:- eval A (obj O),
	           List.mem ((L,y\B), O),
		   eval (subst (y\B,obj O)) V.
	eval (upd (l\A) Z) (obj (update (O,l,Z)))
		:- eval A (obj O).
        eval (var V) (var V).


	pred nf exp.
	nf E :- eval E E.

	func t1 = exp.
	t1 = sel (obj [(l,(x\obj []))]) l.


	func field_upd (nm\exp) exp = exp.
	field_upd (l\A) B = upd (l\A) (x\B) :- x # B.

	?X = subst (z\obj [(y,w\var z)],obj []).

).

(* From lambda calculus to objects *)

namespace lam (

	exp : type.

	var : id -> exp.
	lam : id\exp -> exp.
	app : exp -> exp -> exp.

).


func do_app z.exp z.exp = z.exp.
do_app P Q = z.sel (z.field_upd (arg\P) Q) val.

#open lam.

pred trans exp z.exp.
trans (var X) (z.var X).
trans (app B A) (do_app B' A') :- trans B B', trans A A'.
trans (lam (x\B)) E
	:- trans B B',
	   E = (z.obj [(arg,(x\z.sel (z.var x) arg)),
	                  (val,x\z.subst (x\B',z.sel (z.var x) arg))]).


?X = lam (x\var x), trans X Z.
