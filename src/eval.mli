(* alphaProlog *)
(* Evaluation: functions at base types *)

(* Preconditions: Term must be ground relative to subst. *)

val eval : ('a -> 'a Internal.term list -> 'a Internal.term) -> 
           'a Subst.subst -> 'a Internal.term -> 'a Internal.term;;

