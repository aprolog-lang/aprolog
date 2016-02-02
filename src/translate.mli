(* Alpha Prolog *)
(* Translate: translate the results of unification back into 
   human-readable absyn terms.
*)
open Tcenv;;

val translate_ty   : sg -> tcenv -> Absyn.ty -> Isym.ty_sym Internal.term;;
val untranslate_ty : sg -> tcenv -> Isym.ty_sym Internal.term -> Absyn.ty;;

val translate_goal : sg -> tcenv -> Absyn.term -> Isym.term_sym Internal.goal;;
val translate_prog : sg -> tcenv -> Absyn.term -> Isym.term_sym Internal.prog;;
val translate_test : sg -> tcenv -> Absyn.term -> Isym.term_sym Internal.test;;
val translate_hyp  : sg -> tcenv -> Absyn.term -> Isym.term_sym Internal.hyp;;
val untranslate_tm : sg -> tcenv -> Isym.term_sym Internal.term -> Absyn.term;;
