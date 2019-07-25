open Types;;
open Perm;;
open Internal;;
open Subst;;
open Printer;;
open Util;;

type 'a constrs = ('a term * var) list;;

type 'a answer = ('a subst * 'a constrs );;
type 'a sc = 'a -> unit

val pp_constrs : 'a printer -> 'a constrs printer;;
val pp_answer  : Tcenv.sg -> Tcenv.tcenv -> var list ->  
                 (Isym.term_sym answer) printer;;
val pp_answer_term  : Tcenv.sg -> Tcenv.tcenv -> var list ->  
                 (Isym.term_sym answer) printer;;
(*val pp_evconstrs : 'a term printer -> 'a evconstrs printer;;*)


type 'a sc_transform = 'a sc -> 'a sc;;

val unify_fresh : 'a term -> 'a term -> ('a answer) sc_transform;;
val constrain_fresh : var -> var list -> ('a answer) sc_transform;;
val unify       : 'a equal -> 'a term -> 'a term -> ('a answer) sc_transform;;
val unifys      : 'a equal -> ('a term * 'a term) list -> 
                  ('a answer) sc_transform;;
(*val eunify : 'a Util.equal -> 'a term -> 'a term -> 'a answer sc_transform*)

