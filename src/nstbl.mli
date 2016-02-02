(* Namespace tables *)

type sym = 
    Child of string * sym
  | Base of string
;;


type path = 
    Root of sym 
  | Rel of sym

type 'a t;;

val pp_sym : sym Printer.printer;;
val ns2s : sym -> string;;
val pp_path : path Printer.printer;;
val p2s : path -> string;;
val get_base : sym -> string;;

val create : int -> 'a t;;
val find : 'a t -> path -> 'a;;
val add : 'a t -> path -> 'a -> unit;;
val resolve : 'a t -> path -> sym;;
val mem : 'a t -> path -> bool;;

val enter_ns : 'a t -> string -> unit;;
val exit_ns : 'a t -> unit;;
val open_ns : 'a t -> path -> unit;;
val resolve_path : 'a t -> path -> string list;;
val abbrev_path : 'a t -> string list -> string -> unit;;

val to_list : 'a t -> (sym * 'a) list;;
