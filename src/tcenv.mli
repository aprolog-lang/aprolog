open Absyn;;
open Types;;

type symk = VarS of ty | NameS of ty;;
val pp_symk : symk Printer.printer;;

type tyk  = DataKd | NameKd | TypeKd;;
val pp_tyk : tyk Printer.printer;;

type ctx  = symk Varmap.t;;
type tctx = tyk Varmap.t;;
type ty_abbrev = ty list -> ty;;
type ksg  = (kind*Unique.uniq*ty_abbrev option) Nstbl.t;;
type tsg_entry = {is_def:bool; is_abbrev : bool; sym_id:Unique.uniq; sym_ty:ty};;
type tsg  = tsg_entry Nstbl.t;; 
type sg   = {ksg:ksg; 
	     tsg:tsg;
	     stbl:(Unique.uniq, Nstbl.sym) Hashtbl.t;
             kdecls : (Nstbl.sym * kind) list ref;
             tdecls : (Nstbl.sym * ty) list ref;
             clauses : term list ref};;

val init_sg : unit -> sg;;

type eqns = (Types.var * Absyn.ty) list;;
type tcenv = Varset.t * tctx * ctx * eqns;;

val empty_env : tcenv;;
val lookup_env : Varmap.elt -> tcenv -> ty;;

(** [add_kind_decl signature name is_def kind] **)
val add_kind_decl : sg -> sym -> kind -> ty_abbrev option -> sg * Unique.uniq;;

(** [add_sym_decl signature name is_def is_abbrev is_con ty] **)
val add_sym_decl : sg -> sym -> bool -> bool -> bool -> ty -> sg * Unique.uniq;;

(** [add_clause_decl signature term] **)
val add_clause_decl : sg -> term -> sg

(** [ enter_namespace signature sym] **)
val enter_namespace : sg -> sym -> unit;;

(** [ exit_namespace signature sym] **)
val exit_namespace : sg -> unit;;

