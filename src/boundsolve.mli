(* Solve *)
(* Solves a goal using depth-first proof search *)

open Types;;
open Internal;;
open Unify;;

type 'a answer = 'a Unify.answer;;

(* Exception raised if solving fails because of exhausting the depth bound. *)
exception DepthBound;;

(** |boundsolve printer sg index prog goal sc i a|
   Solves |goal| using signature |sg|, program |prog|, and index |idx|.
   Use |printer| to print any terms/logging messages
   Initial depth bound is |i| and initial (partial solution) answer is |a|
   On success, call success continuation |sc|. *)

val boundsolve : 
    Isym.term_sym Printer.printer -> 
      Tcenv.sg -> 
	Isym.term_sym Index.t ->  
	  Isym.term_sym prog -> 
	    Isym.term_sym goal -> 
	      var list -> 
	      (int -> Isym.term_sym answer -> unit) ->
		int -> Isym.term_sym answer -> unit;;

