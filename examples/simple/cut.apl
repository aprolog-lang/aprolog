
pred mem_cut 	A [A].
mem_cut A (A::L) :- !.
mem_cut B (A::L) :- mem_cut B L.

