(* alphaProlog *)
(* Line/character positions (for error messages) *)

type pos;;

(* Currently line numbers only. *)
val mk_pos : string -> int -> pos;;
val pp_pos : pos Printer.printer;;
val pos2s : pos -> string;;
