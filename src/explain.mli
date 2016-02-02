(* Alp[ha Prolog *)
(* Explains why two terms do not unify. Raises an exception if they do. *)
open Types;;
open Perm;;
open Internal;;
open Subst;;
open Printer;;

type 'a constrs = ('a term * var) list;;
type 'a answer  = ('a subst * 'a constrs);;
type 'a fc_transform = ('a -> string) -> ('a -> string);;
type 'a equal = 'a -> 'a -> bool;;

val explain_fresh : 'a term -> 'a term -> ('a answer) fc_transform;;
val explain       : 'a printer -> 'a equal -> 'a term -> 'a term -> ('a answer) fc_transform;;
val explains      : 'a printer -> 'a equal -> ('a term * 'a term) list -> ('a answer) fc_transform;;
