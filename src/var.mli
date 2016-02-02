(* var.mli *)
(* Variables: plain strings, and uniquified var's. *)
open Printer;;

type var;;

val mkvar' : string -> var;;
val mkvar  : string -> var;;
val mkvar0 : unit -> var;;

val reset_var : unit -> unit;;

val rename  : var -> var;;
val rename' : var -> var;;

val compare : var -> var -> int;;
val eq      : var -> var -> bool;;

val to_string  : var -> string;;
val to_string' : var -> string;;

val root : var -> string;;

val pp_var : var printer;;
