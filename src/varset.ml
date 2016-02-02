(* varset.mli *)
(* Sets of variables *)
open Var;;
open Printer;;
module VarSet = Set.Make(struct type t = var let compare = compare end);;


type elt = Var.var;;


type t = VarSet.t;;


let empty = VarSet.empty;;


let is_empty = VarSet.is_empty;;


let mem = VarSet.mem ;;


let add = VarSet.add;;


let singleton = VarSet.singleton;;


let remove = VarSet.remove;;


let union = VarSet.union;;


let inter = VarSet.inter;;


let diff = VarSet.diff;;


let compare = VarSet.compare;;


let equal = VarSet.equal;;


let subset = VarSet.subset;;


let iter = VarSet.iter;;


let fold = VarSet.fold;;


let for_all = VarSet.for_all;;


let exists = VarSet.exists ;;


let filter = VarSet.filter ;;


let partition = VarSet.partition;;


let cardinal = VarSet.cardinal;;


let elements = VarSet.elements;;


let min_elt = VarSet.min_elt;;


let max_elt = VarSet.max_elt ;;


let choose = VarSet.choose;;


let unions ss = List.fold_right (fun s t -> union s t) ss VarSet.empty;;


let from_list es = List.fold_right VarSet.add es VarSet.empty;;


let pp_varset s = 
  braces (fold (fun x d -> pp_var x <:> text "," <+> d) s Printer.emp )
