(* alphaProlog *)
(* Line/character positions (for error messages) *)
open Printer;;

type pos = string * int;;


let mk_pos s i = (s,i);;

let pp_pos (s,i) = text s <:> colon <:> num i;;

let pos2s p = pp pp_pos p;;

