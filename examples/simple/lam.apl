#use "list.apl".
#open List.

id : name_type.
tm : type.
ty : type.

var : id -> tm.
app : tm -> tm -> tm.
lam : id\tm -> tm.
==> : ty -> ty -> ty.
infixr ==> 5.


pred fvs tm [id].
fvs (var V) [V].
fvs (app E1 E2) L3 :- fvs E1 L1, fvs E2 L2, append (L1,L2,L3).
fvs (lam (x\E)) L2 :- fvs E L1, remove(x,L1,L2).

pred freshen tm tm.
freshen (var X) (var X).
freshen (app E1 E2) (app E1' E2') :- freshen E1 E2, freshen E1' E2'.
freshen (lam (x\E)) (lam (y\E'')) :- y # E, freshen E E', E'' = (x~y) E'.

pred eq tm tm.
eq (var X) (var X).
eq (app E1 E2) (app E1' E2') :- eq E1 E2, eq E1' E2'.
eq (lam (x\E)) (lam (x\E')) :- eq E E'.

pred subst (id\tm) tm tm.
subst(x\T) E U :- U is T{E/var x}.

(* declarative substitution *)
pred subst2 id tm tm tm.
subst2 a (var a) E E.
subst2 a (var b) E (var b).
subst2 a (app E1 E2) E (app E1' E2') :- subst2 a E1 E E1', subst2 a E2 E E2'.
subst2 a (lam (b\E1)) E (lam(b\E1')) :- b # E, subst2 a E1 E E1'.

pred beta tm tm.
beta (app (lam (b\E)) E') E'' :- subst(b\E) E' E''.

pred beta' tm tm.
beta' (app (lam (b\E)) E') E'' :- subst2 b E E'  E''.

(* Using built-in substitution eventually *)
(*pred beta'' tm tm.
beta'' (app (lam (b\E)) E') (E{E'/b}).*)

%?beta (app (lam (a\ lam (b\ var a))) (var b)) (lam (c\var b)).
%?beta (app (lam (a\ lam (b\ var a))) (var b)) (lam (b\var b)).
%?beta (app (lam (a\ lam (b\ var a))) (var b)) (lam (b\var a)).
%?beta' (app (lam (a\ lam (b\ var a))) (var b)) (lam (c\var b)).
%?beta' (app (lam (a\ lam (b\ var a))) (var b)) (lam (b\var b)).
%?beta' (app (lam (a\ lam (b\ var a))) (var b)) (lam (b\var a)).

? X = lam(a\var(b)), Y= app(var(a))(var(b)), Z is X{Y/var(b)}.

pred eta tm tm.
eta (lam (x\app E (var x))) E :- x # E.


type ctx = [(id,ty)].

pred typeof ctx tm ty.
typeof Gamma (var V) T :- mem((V,T),Gamma).
typeof Gamma (app E1 E2) T 
	:- typeof Gamma E1 (T0 ==> T), 
           typeof Gamma E2 T0.
typeof Gamma (lam(x\E)) (T1 ==> T2) :- x # Gamma,
	typeof ((x,T1)::Gamma) E T2.

(* single step reduction *)
pred step tm tm.
step M M' :- beta M M'.
step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- step N N'.
step (lam (x\M)) (lam (x\M')) :- step M M'.

pred steps tm tm.
steps M M' :- beta M M'.
steps (var X) (var X).
steps (app M N) (app M' N') :- steps M M', steps N N'.
steps (lam (x\M)) (lam (x\M')) :- steps M M'.

%?lam(y\Y) = lam(x\Y).

%?lam(a\ lam(b\ app X1 (var b))) = lam(b\ lam(a\ app (var a) X1)).
%?lam(a\ lam(b\ app X2 (var b))) = lam(b\ lam(a\ app (var a) X3)).
%?lam(a\ lam(b\ app (var b) X4)) = lam(b\ lam(a\ app (var a) X5)).
%?lam(a\ lam(b\ app (var b) X6)) = lam(a\ lam(a\ app (var a) X7)).

%?typeof [] (lam(x\lam(x\var x))) T.

%?typeof [] (lam (f\(lam (x\ app(var x) (lam (y\ var y)))))) T.

%?typeof [] (lam (x\ app(var x) (var x)))T.

%?typeof [(x,T)] (app (var x) (var x)) T.


pred beta_reduce tm tm.
beta_reduce E E' :- beta E E'.
beta_reduce (app E1 E2) (app E1' E2) :- beta_reduce E1 E1'.
beta_reduce (app E1 E2) (app E1 E2') :- beta_reduce E2 E2'.
beta_reduce (lam (x\E)) (lam (x\E')) :- beta_reduce E E'.

pred beta_nf tm tm.
beta_nf E1 E3 :- beta_reduce E1 E2, !, beta_nf E2 E3.
beta_nf E E :- !.

pred beta_expand tm tm.
beta_expand E' E :- beta_reduce E E'.

(*?
X1 = app (lam (x\ app (var x) (var x))) (lam (y\app (var y) (lam (z\var z)))),
beta_reduce X1 X2, 
X2 = app (lam (x\ app (var x) (lam (y\var y)))) (lam (z\app (var z) (lam (w\var w)))),
beta_reduce X2 X3, 
X3 = app (lam (x\ app (var x) (lam (y\var y)))) (lam (z\var z)),
beta_reduce X3 X4,
X4 = app (lam (x\var x)) (lam (y\var y)),
beta_reduce X5 X4,
X5 = app (lam (x\app (var x) (var x))) (lam (y\var y))
.
*)
(*
( (\x. (x x)) (\y. (y (\z. z))) )
= beta-reduce
( (\x. (x (\y. y))) (\z. (z (\w. w))) )
= beta-reduce
( (\x. (x (\y. y))) (\z. z) )
= beta-reduce
( (\x. x) (\y.y) )
= beta-expand
( (\x. (x x)) (\y.y) )
*)


pred tm ([id],tm,int).
tm(L,lam(x\E),N) :- N > 0, M is N - 1, tm(x::L,E,M).
tm(L,app E1 E2,N) :- N > 0, M is N - 1, tm(L,E1,M), tm(L,E2,M).
tm(L,var V,N) :- List.mem(V,L).


pred neq(tm,tm).
neq(var(X),var(Y)) :- X # Y.
neq(app E1 E2 ,app E1' E2' ) :- neq(E1,E1'); neq(E2,E2').
neq(lam(x\E),lam(x\E')) :- neq(E,E').
neq(var _, lam _).
neq(var _, app _ _).
neq(app _ _, var _).
neq(app _ _, lam _).
neq(lam _, var _).
neq(lam _, app _ _).


%?E = lam (x\app(var x)(var x)),
%E' = app E E,
%step E' E''.


%?tm([],E,3), step E  E, typeof [] E T .
%?tm([],E,5), step E  E,typeof [] E T. 




% TODO: Fix the bug causing the following goal to succeed.
%? new a. forall X. new b. (a~b)X = X.
