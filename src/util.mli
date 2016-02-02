(* Alpha Prolog *)
(* Utilities: exceptions and debugging *)
exception NYI;;
exception Error of string;;
exception RuntimeError of string;;
exception Impos of string;;


type 'a equal = 'a -> 'a -> bool;;


val nyi   : unit -> 'a;;
val error : string -> 'a
val runtime_error : string -> 'a
val impos : string -> 'a
val do_trace : int -> (unit -> unit) -> unit
val warning : string -> unit

val nl : unit -> unit;;

val split : (char -> bool) -> string -> string list;;

val zip : 'a list -> 'b list -> ('a * 'b) list;;
val unzip : ('a * 'b) list -> 'a list * 'b list;;

val allpairs : 'a list -> 'b list -> ('a * 'b) list;;

val collect : ('a -> 'b list) -> 'a list -> 'b list;;

val map_partial : ('a -> 'b option) -> 'a list -> 'b list;;

val tabulate : (int -> 'a) -> int -> 'a list;;
