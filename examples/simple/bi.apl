#use "list.apl".
#open List.

v 	: name_type.
cv	: name_type.
tm	: type.
ty	: type.
ctx	: type.
hctx	: type.

i	: tm.
t	: tm.
lseq	: tm -> tm -> tm.
seq	: tm -> tm -> tm.

vr	: v -> tm.
lapp	: tm -> tm -> tm.
lam	: v\tm -> tm.
lpair	: tm -> tm -> tm.
lletpair: tm -> v\v\tm -> tm.
app	: tm -> tm -> tm.
alpha	: v\tm -> tm.
pair	: tm -> tm -> tm.
proj1	: tm -> tm.
proj2	: tm -> tm.
let	: tm -> v\tm -> tm.

emp_c	: ctx.
top_c	: ctx.
comma_c	: ctx -> ctx -> ctx.
semi_c	: ctx -> ctx -> ctx.
bind_c	:  v -> ty -> ctx.

hole_h	: hctx.
semi1_h	: hctx -> ctx -> hctx.
semi2_h	: ctx -> hctx -> hctx.
comma1_h	: hctx -> ctx -> hctx.
comma2_h	: ctx -> hctx -> hctx.

pred	ctx_sub	hctx ctx ctx.
ctx_sub hole_h G G.
ctx_sub (semi1_h H G2) G1 (semi_c G1' G2) :- ctx_sub H G1 G1' .
ctx_sub (semi2_h G1 H) G2 (comma_c G1 G2') :- ctx_sub H G2 G2' .
ctx_sub (comma1_h H G2) G1 (semi_c G1' G2) :- ctx_sub H G1 G1' .
ctx_sub (comma2_h G1 H) G2 (comma_c G1 G2') :- ctx_sub H G2 G2' .

emp_t	: ty.
top_t	: ty.
star	: ty -> ty -> ty.
times	: ty -> ty -> ty.
magic	: ty -> ty -> ty.
arrow	: ty -> ty -> ty.


pred mem (v,ty) ctx.
mem (V,T) (bind_c V T).
mem B (semi_c G1 G2) :- mem B G1.
mem B (semi_c G1 G2) :- mem B G2.
mem B (comma_c G emp_c) :- mem B G.
mem B (comma_c emp_c G) :- mem B G.

pred empty ctx.
empty top_c.
empty emp_c.

pred tc ctx tm ty.
tc G (vr V) T :- mem (V,T) G.
tc G i emp_t :- empty G.
tc G (lseq E1 E2) T :-
	tc G1 E1 emp_t,
	ctx_sub H G1 G,
	ctx_sub H emp_c G',
	tc G' E2 T.
tc G t top_t.
tc G (seq E1 E2) T :-
	tc G1 E1 top_t,
	ctx_sub H G1 G,
	ctx_sub H top_c G',
	tc G' E2 T.
tc (comma_c G1 G2) (lpair E1 E2) (star T1 T2) :- 
	tc G1 E1 T1,
	tc G2 E2 T2.
tc G (lletpair E1 (x\y\E2)) T :- 
	tc G1 E1 (star T1 T2),
	ctx_sub H G1 G,
	ctx_sub H (comma_c (bind_c  x T1) (bind_c  y T2)) G',
	tc G' E2 T.
tc (semi_c G1 G2) (pair E1 E2) (times T1 T2) :- 
	tc G1 E1 T1,
	tc G2 E2 T2.
tc G (proj1 E) T1 :- 
	tc G E (times T1 T2).
tc G (proj2 E) T2 :- 
	tc G E (times T1 T2).
	
tc G (lam (x\E)) (magic T1 T2) :- x # G,
	tc (comma_c G (bind_c  x T1)) E T2.
tc (comma_c G1 G2) (lapp E1 E2) T2 :-
	tc G1 E1 (magic T1 T2),
	tc G2 E2 T1.
tc G (alpha (x\E)) (arrow T1 T2) :- x # G,
	tc (semi_c G (bind_c  x T1)) E T2.
tc (semi_c G1 G2) (lapp E1 E2) T2 :-
	tc G1 E1 (arrow T1 T2),
	tc G2 E2 T1.
tc G (let E1 (x\E2)) T :- 
	tc G1 E1 T1,
	ctx_sub H G1 G,
	ctx_sub H (bind_c  x T1) G',
	tc G' E2 T.


(*
tc G E T :-
	ctx_sub H G' G,
	ctx_sub H (semi_c G' G') G'',
	tc G'' E T.
tc G E T :- 
	ctx_sub H (semi_c G1 G2) G,
	ctx_sub H G1 G''',
	tc G' E T.
tc G E T :- 
	ctx_sub H (semi_c G1 G2) G,
	ctx_sub H G2 G',
	tc G' E T.
*)

?
tc emp_c 
  (lam (x\
   alpha (y\ 
    pair (vr x) (vr y))))
T.

?
tc emp_c 
  (lam (x\ 
   alpha (f\
    app(app (vr f) (vr x)) (vr x))))
T.


e	: type.
ve	: v -> e.
plus	: e -> e -> e.
times	: e -> e -> e.
one	: e.
zero	: e.

pred 	constrs	tm [(e,e)] e.
constrs (vr X) [] (ve X).
constrs i [] one.
constrs (lseq E1 E2) [(one,C1)|L] C2 
	:- constrs E1 L1 C1, constrs E2 L2 C2, append(L1, L2, L).
constrs (lam (x\E)) [(C,times C' (ve  x))|L] C'
	:- 
	   constrs E L C.
constrs (lapp E1 E2) L (times C1 C2) 
	:- constrs E1 L1 C1, constrs E2 L2 C2, append(L1,L2,L).
constrs (lpair E1 E2) L (times C1 C2) 
	:-  constrs E1 L1 C1, constrs E2 L2 C2, append(L1,L2,L).
constrs (lletpair E1 (x\y\E2)) [(C1, times (ve  x) (ve  y))|L] C2 
	:-
	constrs E1 L1 C1, constrs E2 L2 C2, append(L1,L2,L).

constrs t [] zero.
constrs (lseq E1 E2) [(zero, C1)|L] C2 
	:- constrs E1 L1 C1, constrs E2 L2 C2, append(L1,L2,L).
constrs (alpha (x\E)) [(C,plus C' (ve  x))|L] C'
	:-
	constrs E L C.
constrs (app E1 E2) L (plus C1 C2) 
	:- constrs E1 L1 C1, constrs E2 L2 C2, append(L1,L2,L).
constrs (pair E1 E2) L (plus C1 C2) 
	:-  constrs E1 L1 C1, constrs E2 L2 C2, append(L1,L2,L).
constrs (proj1 E) L C
	:- constrs E L C.
constrs (proj2 E) L C
	:- constrs E L C.


pred solve e e.
solve one one.
solve zero zero.
solve (ve V) (ve V).
solve (times C D) (times C' D') :- solve C C', solve D D'.
solve (plus C D) (plus C' D') :- solve C C', solve D D'.
solve (plus zero C) D :- solve C D.
solve (plus C zero) D :- solve C D.
solve D (plus zero C) :- solve C D.
solve D (plus C zero) :- solve C D.
solve (times one C) D :- solve C D.
solve (times C one) D :- solve C D.
solve D (times one C) :- solve C D.
solve D (times C one) :- solve C D.


pred solveall [(e,e)].
solveall [].
solveall [(C,D)|L] :- solve C D, solveall L.

pred go	tm e.
go T C :- constrs T L C, solveall L.

pred solveall' [(e,e)].
solveall' [].
solveall' [(C,D)|L] :- C = D, solveall' L.

pred go' tm e.
go' T C :- constrs T L C, solveall' L.

?constrs (lam (x\vr x)) L C.