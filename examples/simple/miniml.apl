#use "list.apl".
#open List.

v 	: name_type.
exp	: type.

tv	: name_type.
tp 	: type.
ptp	: type.

intTy 	: tp.
arrow	: (tp,tp)-> tp.
times	: (tp,tp) -> tp.
tvar	: tv -> tp.

monotp	: tp -> ptp.
all	: tv\ptp -> ptp.

var  	: v -> exp.
let  	: (exp,v\exp) -> exp.
app  	: (exp,exp) -> exp.
fn  	: v\exp -> exp.
letfun	: v\(v\exp,exp) -> exp.
plus 	: (exp,exp) -> exp.
z   	: exp.
s   	: exp -> exp.
case 	: (exp,exp,v\exp) -> exp.
pair 	: (exp,exp) -> exp.
letpair	: (exp,v\v\exp) -> exp.

pred 	subst	 (v\exp,exp,exp).
subst(a\E,T,E') :- E' is E{T/var a}.

pred 	beta	(exp,exp).
beta (app(fn(a\ E), E'), E'') :- subst(a\E, E', E'').
 	
?subst (a\fn (a\ fn (c\ var a)),var a, E).
?subst (a\ var a, z, E).

pred 	value	exp.
value(z).
value(s V) :- value V.
value(fn (a\ E)).
value(pair (V1,V2)) :- value V1, value V2.

pred 	byname	 ([(v,v\exp)],exp,exp).
byname(S,app (E1, E2), V) :- 
	byname (S,E1,fn (a\ E)), subst (a\E,E2,E3), byname (S, E3, V).
byname(S,fn(a\ E), fn(a\ E)).
byname(S,z,z).
byname(S,s(E), s(V)) :- byname(S,E,V).
byname(S,plus(E1,E2), V) :- byname(S,E1,z), byname(S,E2,V).
byname(S,plus(E1,E2), s(V)) :- byname(S,E1,s(V1)), byname(S,plus(V1,E2),V).
byname(S,let (E1,x\ E2),V) :- subst (x\E2,E1,E3), byname(S,E3,V).
byname(S,case(E1,E2,x\E3),V) :- byname(S,E1,z), byname(S,E2,V).
byname(S,case(E1,E2,x\E3),V) :- 
	byname(S,E1,s(V1)), subst(x\E3,V1,E4), byname(S,E4,V).
byname(S,letfun (f\(x\E1, E2)), V) :- f # S,
	byname([( f,x\E1)|S],E2,V).
byname(S,var A, V) :- mem((A,F),S), byname(S, fn F, V).
byname(S,pair(E1,E2),pair(E1,E2)).
byname(S,letpair(E1,b\c\E2),V) :- b#S, c#S ,
   byname(S,E1,pair(E1',E2')), subst (b\E2,E1',E2''), subst(c\E2'',E2',E2'''),
     byname(S,E2''',V).

?byname([],app((fn(a\ s(var a))),s(z)),V), 
 value V.

?byname([],letfun(f\ (x\ case(var x,z,y\s (var y)), app(var f,s(z)))),V), 
 value V.

?byname([],letfun(f\(x\ app(var f,var x), let (app(var f, z),y\z))),V), 
 value V.

pred 	byval	 ([(v,v\exp)],exp,exp).
byval(S,app (E1, E2), V) :- 
	byval (S,E1,fn (a\ E)), 
	byval (S,E2, V2), 
	subst (a\E,V2,E3), 
	byval (S,E3, V).
byval(S,fn(a\ E), fn(a\ E)).
byval(S,z,z).
byval(S,s(E), s(V)) :- byval(S,E,V).
byval(S,plus(E1,E2), V) :- byval(S,E1,z), byval(S,E2,V).
byval(S,plus(E1,E2), s(V)) :- byval(S,E1,s(V1)), byval(S,plus(V1,E2),V).
byval(S,let (E1,x\ E2), V) :- 
	byval (S,E1,V1), 
	subst (x\E2,V1,E3), 
	byval(S,E3,V).
byval(S,case(E1,E2,x\E3),V) :- byval(S,E1,z), byval(S,E2,V).
byval(S,case(E1,E2,x\E3),V) :- 
	byval(S,E1,s(V1)), subst(x\E3,V1,E4), byval(S,E4,V).
byval(S,letfun (f\(x\E1, E2)), V) :- f # S,
	byval([( f,x\E1)|S],E2,V).
byval(S,var A, V) :- mem((A,F),S), byval(S, fn F, V).
byval(S,pair(E1,E2),pair(V1,V2)) 
   :- byval(S,E1,V1), byval(S,E2,V2).
byval(S,letpair(E1,b\c\E2),V) :- b#S, c#S,
        byval(S,E1,pair(V1,V2)), 
	subst (b\E2,V1,E2'), 
	subst(c\E2',V2,E2''),
	byval(S,E2'',V).

?byval(S,let (z, (x\ plus(z, var x))),V), value V.


(* too slow *)
?byval([],letfun (f\(x\ case(var x,z,y\plus(app(var f,var y),var x)), app(var f,s(s(z))))),V), value V.

?byval([], (letfun (f\(a\ (case(var a,s(z),b\ (plus(var a,app(var f,var b))))),
	app(var f,s(s(z)))))), V ), value V .


pred 	tp	([(v,tp)],exp,tp).

tp(G, var X,T) :- mem((X,T),G).
tp(G, z, intTy).
tp(G, s(E), intTy) :- tp(G,E,intTy).
tp(G, plus(E1,E2), intTy) :- tp(G, E1, intTy) , tp (G,E2,intTy).
tp(G, fn (a\ E), arrow (T1,T2)) :- a # G, tp([( a,T1)|G], E, T2).
tp(G, let (E1, a\E2), T) :- a # G, tp(G,E1,T1), tp([( a,T1)|G], E2, T2).
tp(G, letfun (f\(a\ E1, E2)), T) :- f # G, a # G,
	tp([(a,T1),(f,arrow(T1,T2))|G],E1,T2), 
	tp([(f,arrow(T1,T2))|G], E2, T).
tp(G, app(E1,E2), T) :- 
	tp(G,E1,arrow(T0,T)), tp(G,E2,T0).
tp(G, case(E1,E2,a\E3), T) :- a # G,
	tp(G,E1,intTy),
    tp(G,E2,T),
	tp([(a,intTy)|G],E3,T).
tp(G, pair(E1,E2), times(T1,T2)) :- tp(G,E1,T1), tp(G,E2,T2).
tp(G, letpair(E1,a\b\E2), T) :- a#G, b#G,
   tp(G,E1,times(T1,T2)), tp([(a,T1),(b,T2)|G],E2,T).

?tp([], fn(x\ app(var x,var x)), T) .
?tp([( a,intTy)],var a,T2) .

?tp([( a,T)],var a,T) .


?tp([], letfun (f\(x\ s(app(var f,s(var x))), app(var f,z))), T) .

?tp([], fn (x\ fn (y\ (var x))), T) .
?tp([], fn (x\ fn (y\ (var y))), T) .
?tp([], fn (x\ fn (y\ (var x))), T) .
?tp([], fn (x\ fn (y\ fn (x\ (var x)))), T) .
?tp([], fn (x\ (app (var x,var x))), T) .


?tp([], (letfun (f\(a\ (case(var a,s(z),b\ (plus(var a,app(var f,var b))))),
	app(var f,s(s(z)))))), T ) .


?fn(y\Y) = fn(x\Y).


?fn(a\ fn(b\ app (X1, (var b)))) = fn(b\ fn(a\ app ((var a), X1))).
?fn(a\ fn(b\ app (X2, (var b)))) = fn(b\ fn(a\ app ((var a), X3))).
?fn(a\ fn(b\ app ((var b), X4))) = fn(b\ fn(a\ app ((var a), X5))).
?fn(a\ fn(b\ app ((var b), X6))) = fn(a\ fn(a\ app ((var a), X7))).

(* Let-bound polymorphism does not quite work. *)

?tp ([], 
   letfun (f\(a\ var a, pair (app(var f,z), app(var f,fn(a\var a))))), 
   T).

type subst = [(tv,tp)].
type eqns = [(tp,tp)].

pred 	apply	subst tp tp.
apply S (tvar A) T :- mem((A,T),S).
apply S (tvar A) (tvar A).
apply S (arrow (T, U)) (arrow (T',U')) :- apply S T T', apply S U U'.
apply S (times (T, U)) (times (T',U')) :- apply S T T', apply S U U'.
apply S intTy intTy.

pred applys	subst eqns eqns.
applys S [] [].
applys S ((T,U)::Ts) ((T',U')::Ts' )
    :- apply S T T',
     apply S U U',
     applys S Ts Ts'.



pred 	unify	[tv] tp tp subst subst.
pred 	unifys	[tv] eqns subst subst.
(* BUG: This doesn't work with a -> A, b -> B as variables! Why? *)
unify Uvars intTy intTy S S.
unify Uvars (tvar a) (tvar a) S S.
unify Uvars (tvar b) T S [(b,T)|S] :- mem(b,Uvars), b # T, b # S.
unify Uvars T (tvar b) S [(b,T)|S] :- mem(b,Uvars), b # T, b # S.
unify Uvars (arrow (T, U)) (arrow (T',U')) S S'
   :- unifys Uvars [(T, T'),(U,U')] S S'.
unify Uvars (times (T, U)) (times (T',U')) S S'
   :- unifys Uvars [(T, T'),(U,U')] S S'.
unifys Uvars [] S S.
unifys Uvars ((T,T')::Es) S S''
    :- unify Uvars T T' S S',
	 applys S' Es Es',
	 unifys Uvars Es' S' S''.


pred 	specialize	ptp [tv] tp.
specialize (monotp T) [] T.
specialize (all (a\T)) (a::Uvars) U :- specialize T Uvars U.


pred 	ftvs	tp [tv] [tv].
ftvs intTy L L.
ftvs (tvar a) L (a::L) :- a # L.
ftvs (tvar a) L L :- mem(a, L).
ftvs (arrow(T,U)) L N :- ftvs T L M, ftvs U M N.
ftvs (times(T,U)) L N :- ftvs T L M, ftvs U M N.



pred 	gen	[(v,ptp)] exp [tv] eqns tp.

gen Gamma (var X) Uvars [] T :- mem((X,Pt), Gamma), specialize Pt Uvars T.
gen Gamma (app (E1, E2)) (a::Uvars) ((T1,arrow (T2,tvar a))::Es) (tvar a) 
  :- a # Es, a # Uvars,
  gen Gamma E1 Uvars1 Es1 T1,
    gen Gamma E2 Uvars2 Es2 T2,
    append(Uvars1, Uvars2, Uvars),
    append(Es1, Es2, Es).
gen Gamma (fn (x\E)) (a::Uvars) Es (arrow (tvar a,T)) 
  :- x # Gamma, a # Uvars,
  gen (( x,monotp (tvar a))::Gamma) E Uvars Es T.
gen Gamma z [] [] intTy.
gen Gamma (s E) Uvars ((T,intTy)::Es) intTy 
  :- gen Gamma E Uvars Es T.
    
gen Gamma (letfun (f\(x\E1,E2))) Uvars Es T 
  :- f # Gamma, x # Gamma, a # Uvars, b # Uvars,
  gen (  (f,monotp (arrow (tvar a, tvar b)))
          ::( x, monotp(tvar a))
	  ::Gamma) E1 Uvars1 Es1 T',
    unifys (a::b::Uvars1) ((tvar b, T')::Es1) [] S,
    apply S (arrow (tvar a, tvar b)) U,
    ftvs U [] Ftvs,
    specialize PT Ftvs U,
    gen (( f, PT)::Gamma) E2 Uvars Es T.

pred 	ti	[(v,ptp)] exp ptp.
ti Gamma E PT
  :- gen Gamma E Uvars Es T,
   unifys Uvars Es [] S,
   apply S T T',
   ftvs T' [] Ftvs,
   specialize PT Ftvs T'.
    
    
  
?ti [] (fn (x\s (var x))) PT.
   
 
 
?gen [] (fn (x\ app (var x, s z))) Uvars Es T,
   unifys Uvars Es [] S,
   apply S T T',
   ftvs T' [] Ftvs,
   specialize PT Ftvs T'.

?ti [] (fn (x\ app (var x, z))) PT.


?ti [] (fn (x\ app (var x, s(var x)))) PT.


?ti [] (letfun (f\ (x\(var x), app (var f, z)))) T.