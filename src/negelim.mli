(* Negation elimination *)

open Absyn;;
open Tcenv;;

(* Basic idea: 
   XXX 1.  Define inequality for every type.
   XXX 2.  Define non-freshness (staleness?) for every type.
   5.  Define complement of a single Horn rule A(t) :- B1,...,Bn using 
       neq, nfresh, pattern complement, and forall*
   6.  Define complement of a collection of Horn clauses by complementing 
       each rule and then taking the conjunction.
   3.  Define "pattern complement" for every type.
   4.  Define forall* for every type.
*)

(* Given a signature, define term generator for each data type. *)
val generate_terms : Tcenv.sg -> Absyn.decl list;;

(* Create a call to gen_[[ty]] with argument t *)
val call_term_generator : Absyn.ty -> Absyn.term -> Absyn.term;;

(* Given a signature, define inequality predicates for each data type. *)
val generate_neqs : Tcenv.sg -> Absyn.decl list;;

(* Given a signature, define non-freshness predicates for each name type and data type. *)
val generate_nfreshs : Tcenv.sg -> Absyn.decl list;;

(* Given a signature, define forallstar predicates for each data type *)
val generate_forallstars : Tcenv.sg -> Absyn.decl list;;


(* Given a signature, negate all of the predicates in it *)
val generate_negation : Tcenv.sg -> Absyn.decl list;;

(* Givein a goal, define its negation in terms of negated predicates generated above *) 
val negate_goal : Absyn.term -> Absyn.term;;

(* [pattern_complement sg pat ty] : 
   produces list of patterns that defines complement of given pattern *)
val pattern_complement : Tcenv.sg -> Absyn.term -> Absyn.ty -> Absyn.term list;;

(* Given a test, it returns the negative version of the test *)
val negate_test : Absyn.term -> Absyn.term;;

(* Given a test, it returns a new test where all free vars in conclusion are made ground *)
val add_generators: Tcenv.sg -> Tcenv.tcenv -> Absyn.term -> Absyn.term;;
