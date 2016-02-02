#use "list.apl".
#open List.

id : name_type.
exp : type.
ty : type.

const : int -> exp.
var : id -> exp.
app : (exp,exp) -> exp.
lam : id\exp -> exp.
let : (exp,id\exp) -> exp.
seq : (exp,exp) -> exp.
unit : exp.

new_ref : exp -> exp.
deref : exp -> exp.
assign : (exp,exp) -> exp.

ref : name_type.
type cell = (ref,exp).
type mem = [cell].

% internal reference
ref : ref -> exp.

type config = (mem,exp).

pred update((A,B), [(A,B)], [(A,B)]).
update((A,B),[(A,_)|L],[(A,B)|L]).
update((A,B),[(A',B')|L],[(A',B')|L']) 
  :- A # A', update((A,B),L,L').

pred beta (exp,exp).
beta (app(lam(b\E),E'),E'') :- E'' is E{E'/var b}.

% A call-by-value semantics
pred eval(config,config).
eval((M,const I),(M,const I)).
eval((M,app(E1,E2)),(M,V)) :- eval((M,E1),(M1,lam(x\V1))),
                                       eval((M1,E2),(M2,V2)),
                                       beta(app(V1,V2),V).
eval((M,unit), (M,unit)).
eval((M,seq(E1,E2)),(M',V2)) :- eval((M,E1),(M1,unit)), eval((M1,E2),(M',V2)).
eval((M,ref(A)), (M,ref(A))).
eval((M,new_ref(E)), ([(a,V)|M1],ref a)) :- eval((M,E),(M1,V)), a # V, a#M1.
eval((M,assign(E1,E2)),(M3, unit))  :- eval((M,E1), (M1,ref A)),
                                        eval((M1, E2),(M2,V)),
                                        update((A,V),M2,M3).
eval((M,deref(E)),(M',V))             :- eval((M,E),(M',ref A)), 
                                        mem((A,V),M').
eval((M,let(E1,x\E2)),(M',V))             :- eval((M,E1),(M1,V1)), 
					  E2' is E2{V1/var x},
                                          eval((M1,E2'),(M',V)).
? E = let(new_ref(const 17),x\
      seq(assign(var(x),const 42),
	var(x))),
eval(([],E),(M,E')).

? E = let(new_ref(const 17),x\
      let(var(x),y\
      seq(assign(var(x),const 42),
	var(y)))),
eval(([],E),(M,E')).


? E = let(new_ref(const 0),x\
      let(new_ref(var(x)),y\
          seq(assign(var(x),var(y)),
	  var(x)))),
eval(([],E),(M,E')).
