(* ND calculus for pure nominal logic *)
#use "list.apl".

o 	: type.
at 	: type.
a 	: name_type.

r 	: a -> at.
s 	: a -> a -> at.
at 	: at -> o.
equiv	: at -> at -> o.
nu 	: a\o -> o.
and 	: o -> o -> o.
or 	: o -> o -> o.
neg 	: o -> o.
imp 	: o -> o -> o.
t	: o.
f 	: o.



pred pf  	[o] o.

pf Gamma (at A) :- List.mem(at A, Gamma).
pf Gamma (and P1 P2) :- pf Gamma P1, pf Gamma P2.
pf Gamma (or P1 P2) :- pf Gamma P1; pf Gamma P2.
pf Gamma (neg P) :- pf (P::Gamma) f.
pf Gamma (nu (x\T)) :- x # Gamma, pf Gamma T.
pf Gamma (imp A B) :- pf (A::Gamma) B.
pf Gamma t.
pf Gamma C :- pf Gamma f.
pf Gamma C :- pf Gamma (neg A), pf Gamma A.
pf Gamma C :- pf Gamma (and A B), pf (A::B::Gamma) C.
pf Gamma C :- pf Gamma (or A B), pf (A::Gamma) C, pf (B::Gamma) C.
pf Gamma C :- x # Gamma, x#C, pf Gamma (nu (x\T)), pf (T::Gamma) C.
pf Gamma B :- pf Gamma (imp A B), pf Gamma A.

pred npf  	[o] o.
pred apf 	[o] o.

npf Gamma (and P1 P2) :- npf Gamma P1, npf Gamma P2.
npf Gamma (or P1 P2) :- npf Gamma P1; npf Gamma P2.
npf Gamma (neg P) :- npf (P::Gamma) f.
npf Gamma (nu (x\T)) :- x # Gamma, npf Gamma T.
npf Gamma (imp A B) :- npf (A::Gamma) B.
npf Gamma t.
npf Gamma A :- apf Gamma A.
npf Gamma C :- apf Gamma f.
npf Gamma C :- apf Gamma (neg A), npf Gamma A.
npf Gamma C :- apf Gamma (and A B), npf (A::B::Gamma) C.
npf Gamma C :- apf Gamma (or A B), npf (A::Gamma) C, npf (B::Gamma) C.
npf Gamma C :- x#Gamma, x#C , apf Gamma (nu (x\T)), npf (T::Gamma) C.
apf Gamma A :- List.mem(A, Gamma).
apf Gamma B :- apf Gamma (imp A B), npf Gamma A.

pred upf 	[o] o.
pred focus 	o at o.

upf Gamma (and P1 P2) :- upf Gamma P1, upf Gamma P2.
upf Gamma (or P1 P2) :- upf Gamma P1; upf Gamma P2.
upf Gamma (nu (x\T)) :- x # Gamma, upf Gamma T.
upf Gamma (imp A B) :- upf (A::Gamma) B.
upf Gamma (at A) :- List.mem(D, Gamma), focus D A G, upf Gamma G.
(* Equivariant unification NYI 
upf Gamma (equiv A B) :- A ~= B.
*)
focus (and D1 D2) A (or G1 G2) 
	:- focus D1 A G1, focus D2 A G2.
focus (imp A B) C (and G A) :- focus B C G.
focus (nu (x\D)) A (nu (x\G)) :- x # A, focus D A G.
focus (at A) B (equiv A B).

?upf [] (nu (a\ imp (at (r a)) (at (r a)))).
?upf [] (nu (b\ nu (a\ imp (at (r a)) (at (r b))))).
?upf [] ( imp( nu (a\ at (r a))) (nu (a\at (r a)))).
?upf [] ( imp( nu (b\ nu (a\ at (s a b)))) (nu (a\at (s a a)))).
?upf [] ( imp( nu (a\at (s a a))) (nu (b\ nu (a\ at (s a b)))) ).

