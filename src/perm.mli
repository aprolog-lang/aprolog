(* Alpha-Prolog *)
(* Permutations *)
open Types;;
open Printer;;

type perm;;
type orbits;;


val id    : perm;;
val trans : name -> name -> perm;;
val comp  : perm -> perm -> perm;;
val inv   : perm -> perm;;
val eq    : perm Util.equal;;

val lookup : perm -> name -> name;;
val lookup_inv : perm -> name -> name;;
val domain : perm -> name list;;
val apply  : perm -> perm -> perm;;
val subst  : name -> name -> perm -> perm;;

val disagreement_set : perm -> perm -> name list;;
val supp : perm -> name list;;

val pp_perm : perm printer;;
val p2s : perm -> string;;

val from_list : (name * name) list -> perm;;
val to_list : perm -> (name*name) list;;

val solve : name list -> perm -> perm -> perm;;

val reduce : perm -> orbits;;
val expand : orbits -> perm;;
val normalize : perm -> perm;;
