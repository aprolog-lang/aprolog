(* alphaProlog *)
(* Unique Identifiers *)

open Printer;;


type uniq = int;;


let counter = ref 0;;


let reset () = counter := 0;;


let get () = 
  let i = !counter in 
  incr counter; 
  i
;;


let eq (u1) (u2) = 
  u1 = u2
;;


let pp_uniq (u) = text "$" <:> num u;;
