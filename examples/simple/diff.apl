exp : type.
id : name_type.

const : int -> exp.
var : id -> exp.
plus : exp -> exp -> exp.
times : exp -> exp -> exp.
sin : exp -> exp.
cos : exp -> exp.
neg : exp -> exp.
integ : (id\exp,exp,exp) -> exp.

pred 	diff	id exp exp.

diff X (const C) (const 0).
diff X (var X) (const 1).
diff X (var Y) (var Y) :- X # Y.
diff X (plus E1 E2) (plus E1' E2') 
	:- diff X (E1) (E1'), diff X (E2) (E2').
diff X (times E1 E2) ( plus (times E1' E2) (times E1 E2')) 
	:- diff X (E1) (E1'), diff X (E2) (E2').
diff X (sin E) ( times (cos E) E') :- diff X (E) (E').
diff X (cos E) ( times (neg (sin E)) E') :- diff X (E) (E').
diff X (neg E) ( neg E') :- diff X (E) (E').

?diff x (times (var x) (var x)) E .
