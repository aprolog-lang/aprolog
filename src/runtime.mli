(* Runtime interface *) 
open Isym;;
open Internal;;
open Unique;;

val apply : term_sym -> term_sym term list -> term_sym term;;

val bind : uniq -> (term_sym term list -> term_sym term) -> unit;;

val decls : Absyn.decl list;;
