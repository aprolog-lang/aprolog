#use "list.apl".
id	: name_type.


namespace s (
	tm	: type.
	ty	: type.

	var	: id -> tm.
	z	: tm.
	app	: tm -> tm -> tm.
	lam	: id\tm -> tm.
	pair	: tm -> tm -> tm.
	proj1	: tm -> tm.
	proj2	: tm -> tm.

	intTy	: ty.
	times	: ty -> ty -> ty.
	arrow	: ty -> ty -> ty.

	pred tc	[(id,ty)] tm ty.

	tc G (var V) T :- List.mem((V,T),G).
	tc G z intTy.
	tc G (app E1 E2) T :- tc G E1 (arrow T1 T2), tc G E2 T1.
	tc G (lam (x\E)) (arrow T1 T2) 
		:- x # G,
		tc (( x,T1)::G) E T2.
	tc G (pair E1 E2) (times T1 T2) :- tc G E1 T1, tc G E2 T2.
	tc G (proj1 E) T1 :- tc G E (times T1 T2).
	tc G (proj2 E) T2 :- tc G E (times T1 T2).
).	

namespace l (

	tid	: name_type.
	tm	: type.
	ty	: type.


	z	: tm.
	var	: id -> tm.
	app	: tm -> tm -> tm.
	lam	: id\tm -> tm.
	pair	: tm -> tm -> tm.
	letpair	: tm -> id\id\tm -> tm.
	seq	: tm -> tm -> tm.
	pack	: ty -> tm -> ty -> tm.
	unpack	: tm -> tid\id\tm -> tm.
	let	: tm -> id\tm -> tm.

	tvar	: tid -> ty.
	intTy	: ty.
	arrow	: ty -> ty -> ty.
	times	: ty -> ty -> ty.
	existsTy: tid\ty -> ty.
	bad	: ty.


	pred 	flatten	ty ty.
	flatten (arrow T1 T2) (arrow T1 T2).
	flatten intTy intTy.
	flatten (times _ _) bad.
	flatten (existsTy _) bad.
	flatten (tvar _ ) bad.
	(* can't flatten lbad. *)

	pred 	flatten_ctx	[(id,ty)] [(id,ty)].
	flatten_ctx ((X,T)::G) ((X,T')::G') :- flatten T T', flatten_ctx G G'.
	flatten_ctx [] [].

	pred 	tsubst	(tid\ty) ty ty.
	tsubst (a\T) U V :- V is T{U/tvar a}.

	pred 	tc	[(id,ty)] tm ty [(id,ty)].
	tc G z intTy G.
	tc ((X,T)::G) (var X) T ((X,T')::G) :- flatten T T'.
	tc ((Y,T')::G) (var X) T ((Y,T')::G') :- tc G (var X) T G'.
	tc G (app E1 E2) T2 G2 
	  :- tc G E1 (arrow T1 T2) G1,
	     tc G1 E2 T1 G2.
	tc G (lam (x\E)) (arrow T1 T2) G
	  :- x # G,
	   flatten_ctx G G',
	     flatten T1 T1',
	     tc (( x,T1)::G') E T2 (( x,T1')::G').
	tc G (pair E1 E2) (times T1 T2) G2
	  :- tc G E1 T1 G1,
	     tc G1 E2 T2 G2.
	tc G (letpair E1 (x\y\E2)) T G2
	  :- x#G, y # G,
	   tc G E1 (times T1 T2) G1,
	     flatten T1 T1',
	     flatten T2 T2',
	     tc (( x,T1)::( y,T2)::G1) E2 T (( x,T1')::( y,T2')::G2).
	tc G (seq E1 E2) T G2 
	  :- tc G E1 l.intTy G1, tc G1 E2 T G2.
	tc G (let E1 (x\E2)) T G2
	  :- x # G,
	  tc G E1 T1 G1, flatten T1 T1', tc (( x,T1)::G1) E2 T (( x,T1')::G2).
	tc G (pack T E (existsTy (a\T'))) (existsTy (a\T')) G'
	  :- a # G,
	  tsubst (a\T') T T'',
	     tc G E T'' G'.
	tc G (unpack E1 (a\x\E2)) T G2
	  :- a#G, x # G,
	  tc G E1 (existsTy (a\T1)) G1,
	     flatten T1 T1',
	     tc (( x,T1)::G1) E2 T (( x,T1')::G2).

	func 	appty	ty ty ty = ty.
	appty T1 T2 Te = (arrow (times T1 Te) T2).

	func 	copyty	ty = ty.
	copyty Te = (arrow Te (times Te Te)).
	
	func	freety	ty = ty.
	freety Te = (arrow Te intTy).

	func 	closurety ty ty = ty.
	closurety T1 T2 = 
	  (existsTy (a\
	    times (tvar a) 
           (times (appty T1 T2 (tvar a))
           (times (copyty (tvar a)) 
                  (freety (tvar a))))))
		:- a # T1, a # T2.

	func 	closure	ty ty ty tm tm tm tm = tm.
	closure T1 T2 Te Env App Copy Free =
	  (pack Te (pair Env (pair App (pair Copy Free)))
	         (closurety T1 T2)).

	func 	letclosure	tm (tid\id\id\id\id\tm) = tm.
	letclosure E1 (a\env\app0\copy\free\E2) 
	  = (unpack E1 
	    (a\x\letpair (var x)
	    (env\x\letpair (var x)
	    (app0\x\letpair (var x)
	    (copy\free\E2)))))
	  :- x#E2.
).



func sty2lty s.ty = l.ty.
sty2lty s.intTy = l.intTy.
sty2lty (s.times T1 T2) = (l.times T1' T2') 
	:- T1' = sty2lty T1, 
	   T2' = sty2lty T2.
sty2lty (s.arrow T1 T2) = (l.closurety T1' T2')
	:- T1' = sty2lty T1, 
	   T2' = sty2lty T2.

func 	ctxty2sty	[(id, s.ty)] = s.ty.
ctxty2sty [] = s.intTy.
ctxty2sty ((_,T)::G) = (s.times T (ctxty2sty G)).

func 	copyt	s.ty  l.tm = l.tm.
copyt s.intTy X = (l.pair X X).
copyt (s.times T1 T2) X =
  (l.letpair X (x\y\
   l.letpair E1 (x1\x2\
   l.letpair E2 (y1\y2\
   l.pair(l.pair (l.var x1) (l.var y1)) 
	 (l.pair (l.var x2) (l.var y2))))))
      :- E1 = copyt T1 (l.var x), 
	 E2 = copyt T2 (l.var y).

copyt (s.arrow T1 T2) X = 
    l.letclosure X 
	(a\env\app0\copy\free\ 
	  l.letpair (l.app(l.var copy) (l.var env)) (env1\env2\ 
          l.pair E1 E2))
     :- 
     T1' = sty2lty T1,
     T2' = sty2lty T2,
     E1  = l.closure T1' T2' 
		(l.tvar a) (l.var env1) (l.var app0) (l.var copy) (l.var free),
     E2  = l.closure T1' T2' 
		(l.tvar a) (l.var env2) (l.var app0) (l.var copy) (l.var free).
     


func 	freet	s.ty l.tm = l.tm.
freet s.intTy X = l.z.
freet (s.times T1 T2) X = 
  (l.letpair X 
    (x\y\l.seq E1 E2))
      :- x#E1,y#E2,
       E1 = freet T1 (l.var x), 
	 E2 = freet T2 (l.var y).
freet (s.arrow T1 T2) X = 
  l.letclosure X (a\env\app0\copy\free\l.app(l.var free) (l.var env)).
 

func 	svar2ltm	[(id, s.ty)] id s.ty l.tm = l.tm.
svar2ltm ((X,T)::G) X T Env =
  (l.letpair Env (x\env'\
  l.letpair CopyX (x1\x2\
  l.pair(l.var x1) (l.pair (l.var x2) (l.var env')))))
    :- x# G,y# G,x1# G,x2# G,env' # G,
     CopyX = (copyt T (l.var x)).
svar2ltm ((Y,T')::G) X T Env =
  (l.letpair Env (y\env'\
  l.letpair GetX (x\env''\
  l.pair(l.var x) (l.pair (l.var y) (l.var env'')))))
  :- x# G,y# G,env# G,env'# G,env'' # G,
   GetX = svar2ltm G X T (l.var env').



func 	stm2ltm	[(id, s.ty)] s.tm s.ty l.tm = l.tm.
stm2ltm G (s.var X) T Env = svar2ltm G X T Env.
stm2ltm G s.z T Env = (l.pair l.z Env).
stm2ltm G (s.pair E1 E2) (s.times T1 T2) Env =
  (l.letpair GetE1 (x\env1\
  (l.letpair GetE2 (y\env2\
  (l.pair (l.pair (l.var x)(l.var x)) (l.var env2))))))
  :- x# G,y# G,env1# G,env2 # G,
   GetE1 = stm2ltm G E1 T1 Env,
     GetE2 = stm2ltm G E2 T2 (l.var env1).

stm2ltm G (s.proj1 E) T1 Env =
  (l.letpair GetE (p\env\
  (l.letpair (l.var p) (x\y\
  l.seq FreeY (l.pair (l.var x) (l.var env))))))
  :- x# G,y# G,env# G,p # G,
   GetE = stm2ltm G E (s.times T1 T2) Env,
     FreeY = freet T2 (l.var y).

stm2ltm G (s.proj2 E) T1 Env =
  (l.letpair GetE (p\env\
  (l.letpair (l.var p) (x\y\
  l.seq FreeX (l.pair (l.var y) (l.var env))))))
  :- GetE = stm2ltm G E (s.times T1 T2) Env,
     FreeX = freet T1 (l.var y).

stm2ltm G (s.lam (x\E)) (s.arrow T1 T2) Env =
  (l.letpair CopyEnv' (env1\env2\
  (l.let (l.lam (env\CopyEnv)) (copy\
  (l.let (l.lam (env\FreeEnv)) (free\
  (l.let (l.lam (xenv\ 
           l.letpair App (r\xenv\
           l.letpair (l.var xenv) (x\env\
           l.seq FreeEnv (l.seq FreeX (l.var r)))))) (app0\
  (l.pair (l.closure T1' T2' Te' (l.var env1) (l.var app0) (l.var copy) (l.var free)) (l.var env2))))))))))
  :- Te = ctxty2sty G,
     T1' = sty2lty T1,
     T2' = sty2lty T2,
     Te' = sty2lty Te,
     CopyEnv' = copyt Te Env,
     CopyEnv = copyt Te (l.var env),
     FreeEnv = freet Te (l.var env),
     FreeX = freet T1 (l.var x),
     App = stm2ltm (( x,T1)::G) E T2 (l.var xenv).

stm2ltm G (s.app E1 E2) T2 Env =
  (l.letpair GetE1 (c\env\
  (l.letpair GetE2 (x\env\
  LetClosure))))
  :- GetE1 = stm2ltm G E1 (s.arrow T1 T2) Env,
     GetE2 = stm2ltm G E2 T1 (l.var env),
     LetClosure = l.letclosure (l.var c) (a\cenv\app0\copy\free\
       (l.pair 
       (l.app (l.var app0) (l.pair (l.var x) (l.var env)))
       (l.var env))).

?
E = stm2ltm [] (s.lam (x\s.var x)) T Env.


pred 	ok	s.tm s.ty l.tm l.ty.
ok E T E' T' 
	:- s.tc [] E T,
        E' = stm2ltm [] E T (l.var env),
        T' = sty2lty T,
        l.tc [( env,l.intTy)] E' (l.times T' l.intTy) [( env,l.intTy)].

?
l.tc []  (l.lam (x\l.unpack (l.var x) (a\w\l.pair(l.z) (l.var w))))
	 T [].

?ok s.z T E T'.
?ok (s.pair s.z s.z) T E T'.

?
ok (s.proj2 (s.pair s.z s.z)) T E T'.


pred	ok'	s.tm s.ty l.tm l.ty.
ok' E T E' T'
	:- s.tc [] E T,
        E' = stm2ltm [] E T (l.var env),
        T' = sty2lty T .

?
ok' (s.lam (x\(s.var x))) T E T'.

