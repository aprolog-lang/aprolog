(* varset.mli *)
(* Sets of variables *)
open Var;;
open Printer;;



type elt = Var.var;;
type t;;

val empty     : t;;
val add       : elt -> t -> t;;
val singleton : elt -> t;;
val remove    : elt -> t -> t;;

val is_empty : t -> bool;;
val mem      : elt -> t -> bool;;

val union  : t -> t -> t;;
val inter  : t -> t -> t;;
val diff   : t -> t -> t;;
val unions : t list -> t;;

val compare : t -> t -> int;;
val equal   : t -> t -> bool;;
val subset  : t -> t -> bool;;

val iter    : (elt -> unit) -> t -> unit;;
val fold    : (elt -> 'a -> 'a) -> t -> 'a -> 'a;;
val for_all : (elt -> bool) -> t -> bool;;
val exists  : (elt -> bool) -> t -> bool;;

val filter    : (elt -> bool) -> t -> t;;
val partition : (elt -> bool) -> t -> t * t;;

val cardinal : t -> int;;
val elements : t -> elt list;;
val min_elt  : t -> elt;;
val max_elt  : t -> elt;;

val choose : t -> elt;;

val from_list : elt list -> t;;
 
val pp_varset : t printer;;
