(* Term graphs for internal unification representation *)
(* James Cheney, 1/2006 *)
open Types;;
open Printer;;

type 'a node = App of 'a * 'a node ref list
  | Var of var * 'a node ref option ref
;;

let rec pp_noderef sym_pp nr = pp_node sym_pp (!nr)
    
and pp_node sym_pp n = 
  match n with
    App(sym,nrs) ->
      sym_pp sym <:> paren (sep comma (List.map (pp_noderef sym_pp) nrs))
  | Var(v,nror) -> 
    (match !nror with
      None -> Var.pp_var v
    | Some nr -> pp_noderef sym_pp nr)
;;
    

let mk_app sym nodes = ref (App(sym,nodes));;
let mk_var var = ref(Var(var,ref None));;


type  edge = (string node ref * string node ref);;
module EdgeSet = Set.Make(struct type t = edge let compare = compare end);;

let empty = EdgeSet.empty;;
let add = EdgeSet.add;;

type  edgeset =  EdgeSet.t;;
type  answer = {unsolved: edgeset; solved:  edgeset};;

exception Unify;;


let rec zip l m = 
  match l,m with
    [],[] -> []
  | x::l,y::m -> (x,y)::zip l m
;;

let from_list es = List.fold_right EdgeSet.add es EdgeSet.empty;;

let unify1 (u,v) ans = 
  match (!u,!v) with
    (App(f,nrs), App (g,nrs')) -> 
      if f = g && List.length nrs = List.length nrs'
      then {unsolved=EdgeSet.union (from_list (zip nrs nrs')) ans.unsolved;
	    solved= ans.solved}
      else raise Unify
  | (Var(x,xnr),Var(y,ynr)) ->
      if Var.eq x y then {unsolved=ans.unsolved;
	   solved= ans.solved}
      else 
	(match !xnr,!ynr with
	  None,_ -> 
	    xnr := Some v;
	    {unsolved=ans.unsolved;
	     solved= ans.solved}
	| _,None -> 
	    ynr := Some u;
	    {unsolved=ans.unsolved;
	     solved=ans.solved}
	| Some u', Some v' -> {unsolved= EdgeSet.add (u',v') ans.unsolved;
			       solved= ans.solved})
  | (Var(x,xnr),t) -> 
      (match !xnr with
	None -> 
	  xnr := Some v;
	  {unsolved=ans.unsolved;
	   solved=ans.solved}
      | Some u' -> {unsolved=EdgeSet.add (u',v) ans.unsolved;
		    solved= ans.solved})
  | (t,Var(x,xnr)) -> 
      (match !xnr with
	None -> 
	  xnr := Some u;
	  {unsolved=ans.unsolved;
	   solved=ans.solved}
      | Some v' -> {unsolved=EdgeSet.add (u,v') ans.unsolved;
		    solved=ans.solved})
;;


let reverse (u,v) = (v,u);;


let rec unify ans = 
  if EdgeSet.is_empty ans.unsolved
  then ans
  else 
    let e = EdgeSet.choose ans.unsolved in
    let unsolved' = EdgeSet.remove e ans.unsolved in
    if EdgeSet.mem e ans.solved || EdgeSet.mem (reverse e) ans.solved
    then unify {unsolved=unsolved';
		solved=ans.solved}
    else unify (unify1 e {unsolved=unsolved';
			  solved=EdgeSet.add e ans.solved})
;;

