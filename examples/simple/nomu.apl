#use "list.apl".
#open List.

var  : name_type.
nm   : name_type.
sym  : name_type.
term : type.
type perm = [(nm,nm)].

var : (perm, var) -> term.
u : term.
fun : (sym,term) -> term.
pair : (term,term) -> term.
name : nm -> term.
abs : (nm, term) -> term.


prob : type.
eqn : (term,term) -> prob.
fresh : (nm,term) -> prob.

func inv perm = perm.
inv P = P' :- reverse(P,P').

func perm (perm,term) = term.
func perm0 (perm,nm) = nm.
func perm00 ((nm,nm),nm) = nm.
perm (P,var(P',X)) = var(P'',X) :- append(P,P',P'').
perm (P,pair(T,U)) = pair(perm(P,T),perm(P,U)).
perm (P,fun(F,T)) = fun(F,perm(P,T)).
perm (P,name N) = name(perm0(P,N)).
perm (P,abs(N,T)) = abs(perm0(P,N), perm(P,T)).
perm (P,u) = u.
perm0 ([],A) = A.
perm0 ([P|Ps],A) = perm00 (P,perm0(Ps,A)).
perm00 ((A,B),A) = B.
perm00 ((A,B),B) = A.
perm00 ((A,B),C) = C :- C # A, C # B.


type subst = (var,term).
func apply (subst,term) = term.
func applyp (subst,prob) = prob.
func applyps (subst,[prob]) = [prob].
apply (S,u)= u.
apply ((V,T),var (P,V))= perm (P,T).
apply ((W,T),var (P,V)) = var (P,V) :- V # W.
apply (S,fun(f,T)) = fun(f,apply(S,T)).
apply(S,pair(T,U)) = pair(apply(S,T),apply(S,U)).
applyp(S,eqn (T,U)) = eqn(apply(S,T),apply(S,U)).
applyp(S,fresh(A,T)) = fresh(A,apply(S,T)).
applyps (S,[])        = [].
applyps (S,[P1|P]) = [applyp (S,P1)|applyps(S,P)].

pred zipeqn ([term],[term],[prob]).
zipeqn ([], [], []).
zipeqn ([A|L],[B|M],[eqn(A,B)|N]) :- zipeqn (L,M,N).

pred unify ([prob],[subst]).
unify([],[]).

% =? cases

unify([eqn(name A, name A)|P],S)
  :- unify(P,S).
unify([eqn(fun(f,T),fun(f,U))|P],S) 
  :- unify([eqn(T,U)|P],S).
unify([eqn(pair(T,U),pair(T',U'))|P],S) 
  :- unify([eqn(T,T'),eqn(U,U')|P],S).
unify([eqn(var (Pi1,V), var (Pi2,V))|P],S) 
  :- unify(P,S). % TODO: Difference set
unify([eqn(var (Pi,V), T)| P], [(V,perm(inv Pi,T))|S])  
  :- v # T, unify(applyps((v,perm (inv Pi,T)),P),S).
unify([eqn(T, var (Pi,V))| P], [(V,perm(inv Pi,T))|S])  
  :- V # T, unify(applyps((v,perm (inv Pi,T)),P),S).
unify([eqn(abs(A,T),abs(A,U))|P],S) 
  :- unify([eqn(T,U)|P],S).
unify([eqn(abs(A,T),abs(B,U))|P],S) 
  :- A # B, unify([eqn(T,perm([(A,B)],U)),fresh(A,U)|P],S).
unify([eqn(u,u)|P],S)
  :- unify(P,S).

% #? cases

unify([fresh(A,var(Pi,X))|P],S):- unify(P,S).
unify([fresh(A,name B)|P],S) :- A # B, unify(P,S).
unify([fresh(A,u)|P],S) :- unify (P,S).
unify([fresh(A,pair(T,U))|P],S)
  :- unify([fresh(A,T),fresh(A,U)|P],S).
unify([fresh(A,fun(F,T))|P],S)
  :- unify([fresh(A,U)|P],S).
unify([fresh(A,abs(A,T))|P],S):- unify (P,S).
unify([fresh(A,abs(B,T))|P],S):- A # B, unify ([fresh(A,T)|P],S).




? X = perm([(a,b),(b,c)],pair(name(a),pair(name(b),name(c)))).

? X = applyps(S,[]).


? unify([eqn(fun(f,var ([],v)),var ([(a,b)],v))],S). 

? unify([eqn(var ([(a,b)],w),fun(f,name b))],S).

? unify([eqn(abs(a,name(a)), abs(b,var([],x)))],S).

? unify([eqn(var ([(a,b)],w),fun(f,var([(c,v)],w)))],S).

? P is applyps((v,perm(inv [],u)),[eqn(var([],v),u)]).

? unify([eqn(name a,var([],w)),eqn(var([],z),name b)],S).

? unify([eqn(var([],z),name b)],S).

? unify([eqn(name a,var([],w))],S).

? unify([eqn(u,var([(a,b)],w))],S).

? unify([eqn(fun(g,var([],v)), fun(g,name a))],S).

? unify([eqn(fun(g,u),var([],w)),eqn(var([],z),fun(h,u))],S).

? T is fun(g,u), Pi is [], V is w, P is [eqn(var([],z),fun(h,u))],
  V # T, unify(applyps((V,perm (inv Pi,T)),P),S).

? X is apply((w,perm (inv [],fun(g,u))),var([],z)).

? X is apply((w,perm (inv [],fun(g,u))),fun(h,u)).
