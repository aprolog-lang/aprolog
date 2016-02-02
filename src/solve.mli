(* Solve *)
(* Solves a goal using depth-first proof search *)

open Types;;
open Internal;;
open Unify;;

type 'a answer = 'a Unify.answer;;

val solve : Isym.term_sym Printer.printer -> 
            Isym.term_sym Index.t ->  
	    Isym.term_sym goal -> 
            (Isym.term_sym answer -> unit) -> unit;;

val solve_wrap : Isym.term_sym Printer.printer -> 
            Isym.term_sym Index.t ->  
	    Isym.term_sym prog -> 
	    Isym.term_sym goal -> 
	    var list -> 
	    (Isym.term_sym answer -> unit) ->
	    Isym.term_sym answer -> unit;;

