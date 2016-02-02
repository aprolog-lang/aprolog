open Types;;
open Internal;;
open Printer;;

type 'a subst;;

val id   : 'a subst;;
val join : var -> 'a term -> 'a subst -> 'a subst;;
val sub1 : var -> 'a term -> 'a subst;;
val comp : 'a subst -> 'a subst -> 'a subst;;

val lookup    : 'a subst -> var -> 'a term option;;
val finish    : 'a subst -> var -> 'a term option;;
val apply_s   : 'a subst -> 'a term -> 'a term;;
val apply_s_g : 'a subst -> 'a goal -> 'a goal;;
val apply_s_p : 'a subst -> 'a prog -> 'a prog;;
val apply_p_s : perm -> 'a subst -> 'a subst;;
val apply_s_t : 'a subst -> 'a test -> 'a test;;
val apply_s_h : 'a subst -> 'a hyp -> 'a hyp;;

val pp_term_subst : 'a printer -> 'a subst -> 'a term printer;;

val to_list : 'a subst -> (var * 'a term) list;;

val pp_subst : 'a printer -> 'a subst printer;;


val compress : 'a term -> 'a subst -> 'a term;;
