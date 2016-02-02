(* Term indexing for proof search *)
open Internal;;


type 'a t;;

val create : int -> 'a t;;
val add : Isym.term_sym t -> Isym.term_sym prog -> unit;;
val lookup : Isym.term_sym t -> Isym.term_sym term -> Isym.term_sym prog;;

