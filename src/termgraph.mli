(* Term graphs for internal unification representation *)
(* James Cheney, 1/2006 *)

open Types;;
open Printer;;

type 'a node = App of 'a * 'a node ref list
  | Var of var * 'a node ref option ref
;;

val pp_node : ('a -> doc) -> 'a node -> doc;;
val pp_noderef : ('a -> doc) -> 'a node ref -> doc;;

(* Term constructors *)
val mk_app : 'a -> 'a node ref list -> 'a node ref;;
val mk_var : var -> 'a node ref;;
	

(* A constraint graph is a collection of edges on the termgraph. 
   Each edge can be either Unsolved or Solved.*)

type  edge = (string node ref * string node ref);;
type  edgeset;;
val empty : edgeset;;
val add : edge -> edgeset -> edgeset;;
type  answer = {unsolved: edgeset; solved:  edgeset};;

val unify1 :  edge ->  answer ->  answer;;
val unify : answer ->  answer;;


exception Unify;;
