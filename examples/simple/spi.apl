%%% Spi calculus
 
tm   : type.
nm : name_type.
var  : name_type.
pr   : type.

nm   : nm -> tm.
pair : (tm,tm) -> tm.
zero : tm.
suc  : tm -> tm.
var  : var -> tm.
encrypt : (tm,nm) -> tm.

out  : (nm,tm,pr) -> pr.
in   : (nm,var\pr) -> pr.
par  : (pr,pr) -> pr.
nu   : nm\pr -> pr.
rep  : pr -> pr.
match: (tm,tm,pr) -> pr.
ina  : pr.
let  : (tm,var\var\pr) -> pr.
case : (tm,pr,var\pr) -> pr.
decrypt : (tm,nm,var\pr) -> pr.



act	: type.
tau_a	: act.
out_a	: ([nm],nm,tm) -> act.
in_a	: (nm,var) -> act.



func ren_c(nm,nm,nm) = nm.
ren_c(A,A,C)         = C.
ren_c(B,A,_)         = B :- A # B.

func ren_t(tm,nm,nm) = tm.
ren_t(nm M,A,B)      = nm(ren_c(M,A,B)).
ren_t(pair(M,N),A,B) = pair(ren_t(M,A,B),ren_t(N,A,B)).
ren_t(zero,A,_)      = zero.
ren_t(suc(M),A,B)    = suc(ren_t(M,A,B)).
ren_t(var(X),A,B)    = var(X).
ren_t(encrypt(M,K),A,B) 
                     = encrypt(ren_t(M,A,B),ren_c(K,A,B)).

func ren_p(pr,nm,nm) = pr.
ren_p(ina,A,_)          = ina.
ren_p(par(P,Q),A,C)     = par(ren_p(P,A,C),ren_p(Q,A,C)).
ren_p(in(X,b\P),A,C)    = in(ren_c(X,A,C),b\ren_p(P,A,C)) :- b # C.
ren_p(out(X,Y,P),A,C)   = out(ren_c(X,A,C),ren_t(Y,A,C),ren_p(P,A,C)).
ren_p(match(X,Y,P),A,C) = match(ren_t(X,A,C),ren_t(Y,A,C),ren_p(P,A,C)).
ren_p(nu(b\P),A,C)      = nu(b\ren_p(P,A,C)) :- b # C.
ren_p(let(T,x\y\P),A,C) = let(ren_t(T,A,C),x\y\ren_p(P,A,C)).
ren_p(case(T,P1,x\P2),A,C)  = case(ren_t(T,A,C), ren_p(P1,A,C), x\ren_p(P2,A,C)).
ren_p(decrypt(T,K,x\P),A,C) = decrypt(ren_t(T,A,C),ren_c(K,A,C), x\ren_p(P,A,C)).

func sub_t(tm,tm,var) = tm.
sub_t(nm M,_,_)         = nm(M).
sub_t(pair(M,N),T,X)    = pair(sub_t(M,T,X),sub_t(N,T,X)).
sub_t(zero,_,_)         = zero.
sub_t(suc(M),T,X)       = suc(sub_t(M,T,X)).
sub_t(var(X),T,X)       = T.
sub_t(var(Y),T,X)       = var(Y) :- X # Y.
sub_t(encrypt(M,K),T,X) = encrypt(sub_t(M,T,X),K).

func sub_p(pr,tm,var) = pr.
sub_p(ina,T,_)            = ina.
sub_p(par(P,Q),T,X)       = par(sub_p(P,T,X),sub_p(Q,T,X)).
sub_p(in(C,b\P),T,X)      = in(C,b\sub_p(P,T,X)) :- b # T, b # X.
sub_p(out(C,Y,P),T,X)     = out(C,sub_t(Y,T,X),sub_p(P,T,X)).
sub_p(match(T1,T2,P),T,X) = match(sub_t(T1,T,X),sub_t(T2,T,X),sub_p(P,T,X)).
sub_p(nu(b\P),T,X)        = nu(b\sub_p(P,T,X)) :- b # T, b # X.
sub_p(let(M,x\y\P),T,X)   = let(sub_t(M,T,X),x\y\sub_p(P,T,X)) 
                          :- x # (T,X), y # (T,X).
sub_p(case(M,P1,x\P2),T,X)  
                          = case(sub_t(M,T,X), sub_p(P1,T,X), x\sub_p(P2,T,X)) 
                          :- x # (T,X).
sub_p(decrypt(M,K,x\P),T,X) 
                          = decrypt(sub_t(M,T,X),K, x\sub_p(P,T,X)) 
                          :- x # (T,X).

pred red(pr,pr).
red(rep(P),par(P,rep(P))).
red(match(M,M,P),P).
red(let(pair(M,N),x\y\P),P') :- y#M, P' =  sub_p(sub_p(P,M,x),N,y).
red(case(zero,P,_),P).
red(case(suc(N),_,x\P), P') :- P' = sub_p(P,N,x).
red(decrypt(encrypt(M,K),K,x\P),P') :- P' = sub_p(P,M,x).



pred all_fresh([nm],pr).
all_fresh([],P).
all_fresh(X::Xs,P) :- X#P, all_fresh (Xs,P).

pred safe (act,pr).
safe(tau_a,P).
safe(out_a(Bs,_,_),P) :- all_fresh(Bs,P).
safe(in_a(_,X),P)   :- X # P.

func nus([nm],pr) = pr.
nus([],P) = P.
nus(X::Xs,P) = nu(x\P'') 
  :- P' = nus(Xs,P),
     x # P',
     P'' = ren_p(P',X,x).

pred step (pr,act,pr).
step(P,tau_a,Q)                          :- red(P,Q).
step(par(P,Q),A,par(P',Q))               :- step(P,A,P'), safe(A,Q).
step(par(P,Q),A,par(P,Q'))               :- step(Q,A,Q'), safe(A,P).
step(par(P,Q),tau_a,nus(Bs,par(P',Q''))) :- step(P,out_a(Bs,X,T),P'), 
                                              step(Q,in_a(X,Y),Q'),
					      Q'' = sub_p(Q',T,Y).
step(par(P,Q),tau_a,nus(Bs,par(P'',Q'))) :- step(P,in_a(X,Y),P'), 
                                              step(Q,out_a(Bs,X,T),Q'),
					      P'' = sub_p(P',T,Y).
step(out(X,T,P),out_a([],X,T), P).
step(in(X,z\P), in_a(X,z),P). 
step(match(X,X,P),A,P')                   :- step(P,A,P').
step(nu(y\P),A,nu(y\P'))                  :- y # A, step(P,A,P').
step(nu(y\P),out_a(y::Bs,X,T),P')         :- step(P,out_a(Bs,X,T),P'), y # X.



% Examples

func a1(tm,nm,nm) = pr.
a1(M,C_ab,K_ab) = out(C_ab, encrypt(M,K_ab),ina).

func b1(nm,nm,var\pr) = pr.
b1(C_ab,K_ab,P) = in(C_ab, x\decrypt(var x, K_ab,P)).

func inst1(tm,var\pr) = pr.
inst1(M,P) = nu(k_ab\ par(a1(M,c_ab,k_ab), b1(c_ab,k_ab,P))) :- k_ab # M.


? Q = nu(k_ab\ par(a1(M,c_ab,k_ab), b1(c_ab,k_ab,P))), k_ab # M.

? Q = nu(k\a1(var x,c,k)).
? Q = nu(k\b1(c,k,y\out(print,var y,ina))).
? Q = par(a1(var x,c,k),b1(c,k,y\ina)), step(Q,A,Q').

? Q = decrypt(encrypt(var x, k),k, y\out(print,var y,ina)), step(Q,A,Q').

pred steps(pr,[act],pr).
steps(P,[],P) :- not(step(P,A,P')).
steps(P,A::As,P'') :- step(P,A,P'), steps(P',As,P'').




/*
new c_ab.new k_ab.forall M.forall P.
(forall tmp5.forall tmp6.
((inst_bug (nu (k_ab\(par (pair id.tmp5[*] id.tmp6[*])))) 
(pair id.M[*] id.P[*])) :- 
((a1 id.tmp5[*] (pair id.M[*] (pair c_ab k_ab))), 
(b1 id.tmp6[*] (pair c_ab (pair k_ab id.P[*]))))) :- k_ab # id.M[*])
*/
