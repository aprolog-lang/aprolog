
open Absyn;;
open Tcenv;;
open Monad;;

exception TcFail of string;;

type 'a tcm = (sg,tcenv,'a) scmonad;;

val reflect_ty : Var.var list -> ty -> ty list -> ty;;

(** [check_ty ty higher_order kind] 
    checks that a type has a given kind
    higher_order is a flag, initially false, which indicates whether 
    we are on the LHS of an arrow 
**)

val check_ty   : ty -> bool -> tyk -> ty tcm;;
val check_term : term -> ty -> term tcm;;
val infer_term : term -> (term * ty) tcm;;
val check_goal : term -> term tcm;;
val check_prog : term -> term tcm;;

val check_hyp : term -> term tcm;;
val check_test : term -> term tcm;;
