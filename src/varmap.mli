(* varmap.mli *)
(* Variable Maps *)
open Var;;

type elt = var;;
type 'a t;;

val empty  : 'a t;;
val add    : elt -> 'a -> 'a t -> 'a t;;
val find   : elt -> 'a t -> 'a;;
val remove : elt -> 'a t -> 'a t;;

val is_empty : 'a t -> bool;;
val mem : elt -> 'a t -> bool;;

val iter : (elt -> 'a -> unit) -> 'a t -> unit;;
val map  : ('a -> 'b) -> 'a t -> 'b t;;
val mapi : (elt -> 'a -> 'b) -> 'a t -> 'b t;;
val fold : (elt -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b;;

val to_list : 'a t -> (elt * 'a) list;;

val pp_map : 'a Printer.printer -> ('a t) Printer.printer;;
