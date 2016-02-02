(* Check *)
(* Checks for bugs in a specification by searching for counterexamples *)

open Types;;
open Internal;;
open Unify;;
open Solve;;

val check : Isym.term_sym Printer.printer -> 
            Tcenv.sg -> 
            Isym.term_sym Index.t ->  
	    Isym.term_sym test -> 
	    (int -> Isym.term_sym answer -> unit) -> int -> unit;;

val check_ne : Isym.term_sym Printer.printer -> 
            Tcenv.sg -> 
            Isym.term_sym Index.t ->  
	    Isym.term_sym test -> 
	    (int -> Isym.term_sym answer -> unit) -> int -> unit;;

