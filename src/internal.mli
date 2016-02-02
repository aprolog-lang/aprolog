(* Alpha Prolog *)
(* Internal representation of untyped terms, goals, and program clauses. *)

open Types;;
open Printer;;
open Util;;

type perm = Perm.perm;;


type bconstr = Toplevel
             | Constrained of var list
;;

val bconstr_leq : bconstr -> bconstr -> bool;;
val bconstr_satisfies : var -> bconstr -> bool;;

type bind = Exist of bconstr
          | Univ
;;


type 'a term = App of 'a * 'a term list
  | Abs of  name * 'a term
  | Name of name
  | Susp of perm * bind * var 
  | Lam of var * 'a term 
  | Apply of 'a term * 'a term
;;


type 'a goal = 
(* propositions *)
    Gtrue
  | Gfalse
  | Gatomic of 'a term
  | Gand of 'a goal * 'a goal
  | Gor of 'a goal * 'a goal
  | Gimplies of 'a prog * 'a goal
(* first-order quantifiers *)
  | Gforall of var * 'a goal
  | Gforallstar of var * Types.ty * 'a goal
  | Gexists of var * 'a goal
  | Gnew of name * 'a goal
(* term predicates *)
  | Gfresh of 'a term * 'a term
  | Gequals of 'a term * 'a term
  | Gis of 'a term * 'a term 
  | Geunify of 'a term * 'a term
(* control *)
  | Gcut
  | Guard of 'a goal * 'a goal * 'a goal
  | Gnot of 'a goal

and 'a prog = 
(* first-order program clauses *)
    Dtrue
  | Datomic of 'a term
  | Dimplies of 'a goal * 'a prog
  | Dforall of var * 'a prog
  | Dand of 'a prog * 'a  prog
(* "new" quantifier *)
  | Dnew of name * 'a prog
;;


type 'a test = Ttrue 
  | Tfalse
  | Tequals of Types.ty * 'a term * 'a term
  | Tfresh of Types.ty * Types.ty * 'a term * 'a term
  | Tatomic of ('a term * Types.ty) list * 'a term
  | Timplies of 'a hyp * 'a test
  | Tforall of var * 'a test
  | Tnew of name * 'a test
and 'a hyp = Hatomic of 'a term
  | Hequals of 'a term * 'a term
  | Hfresh of 'a term * 'a term
  | Hand of 'a hyp * 'a hyp
  | Htrue
  | Hexists of var * 'a hyp
  | Hnew of name * 'a hyp

val mk_var : var -> 'a term;;
val find_head : Isym.term_sym term -> Unique.uniq;;

val pp_bconstr : bconstr printer;;
val pp_term : 'a printer -> 'a term printer;;
val pp_goal : 'a printer -> 'a goal printer;;
val pp_prog : 'a printer -> 'a prog printer;;

val pp_test : 'a printer -> 'a test printer;;
val pp_hyp : 'a printer -> 'a hyp printer;;


val supp : 'a term -> Varset.t;;
val fas  : 'a term -> Varset.t;;
val fas_g : 'a goal -> Varset.t;;
val fas_p : 'a prog -> Varset.t;;
val fas_t : 'a test -> Varset.t;;
val fas_h : 'a hyp -> Varset.t;;

val fvs  : 'a term -> Varset.t;;
val fvs_g : 'a goal -> Varset.t;;
val fvs_p : 'a prog -> Varset.t;;
val fvs_t : 'a test -> Varset.t;;
val fvs_h : 'a hyp -> Varset.t;;

val apply_p'  : perm -> 'a term -> 'a term;; (* no suspensions *)
val apply_p   : perm -> 'a term -> 'a term;;
val apply_p_g : perm -> 'a goal -> 'a goal;;
val apply_p_p : perm -> 'a prog -> 'a prog;;

val subst_name : name -> name -> 'a term -> 'a term;;
val subst_name_g : name -> name -> 'a goal -> 'a goal;;
val subst_name_p : name -> name -> 'a prog -> 'a prog;;
val subst_name_t : name -> name -> 'a test -> 'a test;;
val subst_name_h : name -> name -> 'a hyp -> 'a hyp;;

val eq : 'a equal -> 'a term equal;;
