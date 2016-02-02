(* alphaProlog *)
(* Unique Identifiers *)

type uniq 

val reset : unit -> unit;;
val get   : unit -> uniq;;
val eq    : uniq -> uniq -> bool;;

val pp_uniq : uniq Printer.printer;;
