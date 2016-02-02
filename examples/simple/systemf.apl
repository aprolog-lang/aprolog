% System F
#use "list.apl".
#open List.

id : name_type.
tid : name_type.
exp : type.
ty : type.

v : id -> exp.
app : (exp,exp) -> exp.
lam : (ty,id\exp) -> exp.

tlam : (tid\exp) -> exp.
tapp : (exp,ty) -> exp.
c : int -> exp.
plus : (exp,exp) -> exp.

all : (tid\ty) -> ty.
arr : (ty,ty) -> ty.
tv : tid -> ty.
intTy : ty.

type tctx = [tid].
type ctx = [(id,ty)].

pred wfty(tctx,ty).
wfty(D,tv(A)) :- mem(A,D).
wfty(D,arr(T,U)) :- wfty(D,T), wfty(D,U).
wfty(D,all(a\T)) :- wfty(a::D,T).
wfty(D,intTy).

pred wf(tctx,ctx,exp,ty).
wf(D,G,v(X),T) :- mem((X,T),G).
wf(D,G,app(E,E'),U) :- wf(D,G,E,arr(T,U)), wf(D,G,E',U).
wf(D,G,lam(T,x\E),arr(T,U)) :- x # G, wf(D,(x,T)::G,E,U).
wf(D,G,tlam(a\E),all(a\T)) :- a # G, wf(a::D,G,E,T).
wf(D,G,tapp(E,T),U') :- wfty(D,T), wf(D,G,E,all(a\U)), U' is U{T/tv(a)}.
wf(D,G,c(I),intTy).
wf(D,G,plus(E1,E2),intTy) :- wf(D,G,E1,intTy), wf(D,G,E2,intTy).

? wfty([],all(a\tv(a))).

? wf([],[],app(tapp(tlam(a\lam(tv(a),x\v(x))),intTy),c(2)),T).
