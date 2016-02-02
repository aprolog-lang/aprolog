namespace d (
exp 	: type.
var 	: type.

lam 	: exp -> exp.
app 	: exp -> exp -> exp.
zero 	: var.
succ 	: var -> var.
var 	: var -> exp.

tp 	: type.
arrow	: tp -> tp -> tp.

pred tc_v [tp] var tp.
tc_v [T|L] zero T.
tc_v [T'|L] (succ V) T :- tc_v L V T.

pred tc [tp] exp tp.
tc G (var V) T :- tc_v G V T.
tc G (app E1 E2) T2 :- tc G E1 (arrow T1 T2), tc G E2 T1.
tc G (lam E) (arrow T1 T2) :- tc (T1::G) E T2.

? tc [] (lam (var zero)) T.
? tc [] (lam (lam (app (var (succ zero)) (var (succ zero))))) T.
).

(* Explicit names *)

namespace e (

exp : type.
var : name_type.
lam : var\exp -> exp.
app : exp -> exp -> exp.
var : var -> exp.

).

(* When is an exp similar to an e? *)
pred sim d.exp e.exp.
pred sim_e [e.var] d.exp e.exp.
pred sim_v [e.var] d.var e.var.

sim E E' :- sim_e [] E E'.

sim_v (X::_) d.zero X.
sim_v (_::L) (d.succ V) X :- sim_v L V X.

sim_e L (d.var V) (e.var X) :- sim_v L V X.
sim_e L (d.app E1 E2) (e.app E1' E2') :- sim_e L E1 E1', sim_e L E2 E2'.
sim_e L (d.lam E) (e.lam (x\E')) :- x # L, sim_e (x::L) E E'.

#check "sim" 5 : sim E E', sim E E'' => E' = E''.

(* TODO: Check that this specification finds counterexample if freshness condition is dropped *)