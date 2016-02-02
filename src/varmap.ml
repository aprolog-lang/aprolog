open Var;;
open Printer;;
module VarMap = Map.Make(struct type t = var let compare = compare end)

type elt = Var.var;;


type 'a t = 'a VarMap.t;;


let empty = VarMap.empty;;


let add  = VarMap.add;;


let find = VarMap.find;;


let remove = VarMap.remove;;


let mem = VarMap.mem;;


let iter = VarMap.iter;;


let map = VarMap.map;;


let mapi = VarMap.mapi;;


let fold = VarMap.fold;;


let is_empty m = 
  VarMap.fold (fun k v emp -> false) m true
;;


let to_list m = 
  fold (fun v a l -> (v,a)::l) m [] 
;;


let pp_map pp_a m = 
  bracket (sep (text ", ") 
	     (List.map (fun (v, a) -> 
	       text (Var.to_string' v) <+> 
	       text "->" <+> 
	       pp_a a) (to_list m)));;


    
  
