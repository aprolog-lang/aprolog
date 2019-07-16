open Types;;
open Perm;;
open Printer;;
open Fixity;;

type ty = Types.ty;;
type kind = Types.kind;;

type constr = (name*var) list;;

type atomic = Nstbl.path * term list
and term = Atomic of atomic
  | Var of var
  | Name of name
  | Transpose of name * name * term
  | Subst of term * term * term
  | Nil
  | Cons of term * term
  | Unit
  | Pair of term * term
  | Abs of name * term
  | Conc of term * name
  | True
  | False
  | Fresh of (ty*ty) option * term * term
  | Eq of ty option * term * term
  | EUnify of term * term
  | Is of term * term
  | Implies of term * term
  | Or of term * term
  | And of term * term
  | Forall of var * ty * term
  | Exists of var * ty * term
  | New of var * ty * term 
  | Lambda of var * ty * term
  | App of term * term
  | Cut 
  | Guard of term * term * term
  | Not of term
  | Underscore
  | IntC of int
  | CharC of char
  | BoolC of bool
;;


type decl = {pos:Pos.pos option; rdecl:rdecl}
and rdecl = KindDecl of sym * kind
  | SymDecl of sym * ty
  | FuncDecl of sym * ty list * ty
  | PredDecl of sym * ty list * bool * bool
  | ClauseDecl of term 
  | Query of term
  | UseDirective of string
  | TraceDirective of int
  | InfixDecl of direction * string * int
  | NamespaceDecl of sym * decl list
  | TypeDefn of sym * var list * ty 
  | BuiltinFuncDecl of sym * ty list * ty 
	* (Isym.term_sym Internal.term list -> Isym.term_sym Internal.term)
  | TypeQuery of term
  | QuitDirective
  | OpenDirective of Nstbl.path
  | HelpDirective of Nstbl.path option
  | CheckDirective of string * int * bool option * term
  | SaveDirective of string * string * decl
(* Controls the generation of negation code for equality, freshness, and other predicates *)
  | GenerateDirective of string
;;


val pp_kind : kind printer;;
val pp_term : term printer;;
val pp_ty : ty printer;;
val pp_decl : decl printer;;

val k2s : kind -> string;;
val t2s : term -> string;;
val ty2s : ty -> string;;
val d2s : decl -> string;;
  
val ftvs    : ty -> Varset.t;;

val fvs : term -> Varset.t;;
val supp : term -> Varset.t;;

val freshen    : ty -> ty;;

(* it freshens all free vars *)
val freshen_fvs : term -> term;;
(* it creates a new var for each underscore found *)
val fill_holes : term -> term;;
  
val apply_tysub : ty Varmap.t -> ty -> ty;;
val apply_tysub_term : ty Varmap.t -> term -> term;;

val apply_tmsub : term Varmap.t -> term -> term;;
  
val unpack_ty : ty -> (ty list * ty);;


val is_linear : term -> bool;;

(* check whether a clause is purely first order: no names, swappings, abstractions or concretions *)
val is_firstorder : term -> bool;;

(* check whether a clause is well-quantified: every variable free in body is free in head *)
val is_well_quantified : term -> bool;;

val linearize_prog : term -> term;;

val well_quantify_prog : term -> term;;

(* apply basic simplifications to goals and clauses *)
val simplify : term -> term;;
val simplify_goal : term -> term;;

(* unify two linear, first order terms that share no variables *)
val unify_linear : term -> term -> term Varmap.t option;;


