#use "list.apl".

id	: name_type.
exp	: type.


lam	: id\exp -> exp.
app	: exp -> exp -> exp.
var	: id -> exp.
del	: id\exp -> exp.
dapp	: exp -> exp -> exp.
c	: int -> exp.

ty	: type.
arrow	: ty -> ty -> ty.
lolli	: ty -> ty -> ty.
i	: ty.
ans	: ty.

pred	typeof	[(id,ty)] exp ty.
typeof Gamma (var V) T 	:- List.mem((V,T), Gamma).
typeof Gamma (app E1 E2) T 
			:- typeof Gamma E1 (arrow T0 T), 
        		   typeof Gamma E2 T0.
typeof Gamma (lam(b\E)) (arrow T1 T2) :-  b # Gamma,
			typeof (( b,T1):: Gamma) E T2.
typeof Gamma (dapp E1 E2) T 
			:- typeof Gamma E1 (lolli T0 T), 
        		   typeof Gamma E2 T0.
typeof Gamma (del(b\E)) (lolli T1 T2) :- b # Gamma,
			typeof (( b,T1)::Gamma) E T2.
typeof Gamma (c I) i.


func t1 = exp.
t1 			= (lam (x\  var  x)).

func	cps1 exp exp = exp.
cps1 (var V) K 		= (app K (var V)).
cps1 (c I) K   		= (app K (c I)).
cps1 (lam (x\M)) K 	= (app K (del (k'\lam (x\ cps1 M (var k')))))
			:-  k'#M.
cps1 (app M N) K       = (cps1 M (lam (m\ 
			   cps1 N (lam (n\
			   app (dapp (var  m) K) (var  n)))))) 
			:- n#N'.


pred 	ok 		exp ty exp ty ty.
ok E T E' T' T0 	:- k # E,
			   typeof [] E T,
			   E' = cps1 E (var k),
			   typeof [] (del (k\E')) (lolli T0 ans).

? ok t1 T E T' T0.


#check "trans_pres_ty" 2 :
  typeof G E T, typeof G K (arrow T ans), E' = (cps1 E K) => typeof G E' ans.

(*
(* Translation preserves typing *)
(* note this is not a valid program clause because of the exists.  
thus, to prove this automagically, we do need to specify how T' is
constructed from T.  *)
?forall G, E, T, E'.
typeof G E T, cps1 E E' => exists T'. typeof G E' T'.

(* Specializations *)

?new x: id. forall G : list ( id * ty), T : ty.
mem ( x,T) G, cps1 (var  x) (del (k\app (var  k) (var  x))) => exists T'. typeof G (del (k\app (var  k) (var  x))) T'.

*)
