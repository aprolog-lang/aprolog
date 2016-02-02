(* var.mli *)
(* Variables: plain strings, and uniquified var's. *)
open Printer;;



type var = {name:string;uid:int};;


let uniq = ref 1;;


let reset_var () = uniq := 1;;


let mkvar s = 
  let i = !uniq in
  let _ = (uniq := !uniq+1) in
  {name=s;uid=i}
;;


let mkvar' s = {name=s;uid= 0};;


let mkvar0 () = mkvar "tmp";;


let to_string s = s.name ^ "$" ^ (string_of_int s.uid);;


let to_string' s = 
  if(s.uid = 0) 
  then s.name 
  else s.name ^ (string_of_int s.uid)
;;


let root s = s.name;;


let compare v w = 
  let x = w.uid - v.uid in
  if x = 0 then String.compare v.name w.name else x
;;


let eq v w = v.uid = w.uid  && v.name = w.name;;


let rename v = mkvar v.name;;


let rename' v = 
  let v' = mkvar v.name in 
  let n' = v'.name^"'" in
  {name = n'; uid = v'.uid};;


let pp_var v = 
  text (to_string' v)
