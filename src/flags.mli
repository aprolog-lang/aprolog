(* Command line flags *)

val new_goal_only : bool ref;;
val horn_clauses_only : bool ref;;
val strict_new_occurs : bool ref;;
val debug : bool ref;;
val trace : int ref;;
val quit_early : bool ref;;
val tc_only : bool ref;;
val suspensions : bool ref;;
val depth_first_bound : int option ref;;
val forbid_prop : bool ref;;
val forbid_higher_order : bool ref;;
val restrict_name_type : bool ref;;
val do_checks : bool ref;;
val consistency_check : bool ref;;
val extensional_forall : bool ref;;
val generate_terms : bool ref;;
val generate_negation : bool ref;;
val negelim : bool ref;;
val simplify_clauses : bool ref;;
val linearize : bool ref;; 
val quantify : bool ref;;
val skip_occurs_check : bool ref;;
val ne_simpl : bool ref;;
val custom_check : bool ref;;

