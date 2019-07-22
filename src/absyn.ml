(* Alpha Prolog *)
(* Abstract syntax *)
open Types;;
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
  | SaveDirective of string * string * rdecl
  | GenerateDirective of string
;;

let rec pp_kind k = 
  match k with
    NameK -> text "name_type"
  | TypeK -> text "type"
  | ArrowK(k1,k2) -> pp_kind k1 <+> arrow <+> pp_kind k2
;;




(* TODO: Make associativity less of a hack. *)
let toplevel_prec = 0;;
let forall_prec = 0;;
let exists_prec = 0;;
let lambda_prec = 0;;
let new_prec = 0;;
let guard_prec = 0;;
let implies_prec = 1;;
let arrow_prec = 1;;
let constr_prec = 1;;
let or_prec = 2;;
let and_prec = 3;;
let pair_prec = 3;;
let eq_prec = 4;;
let fresh_prec = 4;;
let is_prec = 4;;
let plus_prec = 5;;
let minus_prec = 5;;
let cons_prec = 6;;
let abs_prec = 7;;
let conc_prec = 8;;
let subst_prec = 9;;
let trans_prec = 10;;
let app_prec = 10;;
let not_prec = 10;;


let pp_ty s = 
  let rec pp prec s =
    let paren p d = if p <= prec then Printer.paren(d) else d in
    match s with
      NameTy s -> Nstbl.pp_path s
    | DataTy (ds,ss) -> 
	paren app_prec 
	  (Nstbl.pp_path ds <:> 
	   (hcat (List.map (fun s -> space <:> pp app_prec s) ss)))
    | VarTy v -> text (Var.to_string' v)
    | ListTy s -> bracket(pp toplevel_prec s)
    | AbsTy (_,_) -> paren abs_prec (pp_abss s)
    | PairTy(_,_) -> Printer.paren (pp_pairs s)
    | IdTy s -> Nstbl.pp_path s
    | UnitTy -> text "unit"
    | UnderscoreTy -> underscore
    | IntTy -> text "int"
    | CharTy -> text "char"
    | PropTy -> text "prop"
    | BoolTy -> text "bool"
    | ArrowTy(_,_) -> paren arrow_prec (pp_arrows s)
  and pp_abss s = 
    match s with 
      AbsTy(s1,s2) -> pp abs_prec s1 <:> backslash <:> pp_abss s2
    | s -> pp and_prec s
  and pp_pairs s = 
    match s with 
      PairTy(s1,s2) -> pp and_prec s1 <:> comma <:> pp_pairs s2
    | s -> pp and_prec s
  and pp_arrows s = 
    match s with 
      ArrowTy(s1,s2) -> pp arrow_prec s1 <+> arrow <+> pp_arrows s2
    | s -> pp arrow_prec s
  in pp toplevel_prec s
;;


let rec pp_constr c = 
  match c with
    [] -> emp
  | (a,v)::c -> 
      Var.pp_var (a) 
	<+> hash
	<+> Var.pp_var (v) 
	<:> newline
	<:> pp_constr c

and pp_term term = 
  let _pp_clause prec (p,cs,p') = 
    pp_term p <+>
    if not(cs = []) 
    then 
      (slash <+> 
       sep (comma) 
	 (List.map (fun (a,tm) -> 
	   text (Var.to_string' a)  <+> 
	   hash <+> 
	   pp_term tm) cs))
	<+>
      (larrow <+> 
     pp_term p')
    else emp
  in	
  let rec pp_atomic (h,tl) = 
(*     (sep space ((Nstbl.pp_path h) :: (List.map (pp app_prec) tl)))*)
   (Nstbl.pp_path h) <:> (hcat ( (List.map (fun x -> Printer.paren (pp_pair x)) tl)))
  and pp prec term = 
    let paren p d = if p <= prec then Printer.paren(d) else d in
    match term with
      Unit -> text "()"
    | Name a -> Var.pp_var a 
    | Var v -> Var.pp_var v
    | Transpose(a,b,(Transpose(_,_,_) as t)) -> 
	Printer.paren (Var.pp_var a <:> tilde <:> Var.pp_var b) 
	  <:> pp toplevel_prec t
    | Transpose(a,b,t) -> 
	Printer.paren (Var.pp_var a <:> tilde <:> Var.pp_var b) 
	  <:> pp trans_prec t
    | Subst(Subst(_,_,_) as t,u,v) -> 
	Printer.paren (pp toplevel_prec t <:> braces(pp toplevel_prec u <:> slash <:> pp toplevel_prec v))
    | Subst(t,u,v) -> 
	Printer.paren (pp subst_prec t <:> braces(pp toplevel_prec u <:> slash <:> pp toplevel_prec v))
    | Atomic (a,[]) -> (Nstbl.pp_path a)
    | Atomic (a,[t1;t2]) -> (* maybe infix... TODO: fix for overlapping op's *)
	let sym = 
	  match a with
	    Nstbl.Root(s) -> Nstbl.get_base s
	  | Nstbl.Rel(s) -> Nstbl.get_base s
	in
	if List.mem_assoc sym !Fixity.symtbl 
	then let (a_prec,dir) = List.assoc sym !Fixity.symtbl in
	paren a_prec (pp_assoc a_prec dir a term)
	else paren app_prec (pp_atomic (a,[t1;t2]))
    | Atomic (h,tl) -> paren app_prec (pp_atomic (h,tl))
    | Pair (b,c) -> Printer.paren(pp_pair (Pair(b,c)))
    | Nil -> text "[]" (* Can't tell whether it's the empty string ... *)
    | Cons (CharC _,_) -> 
        (* Try to print as a string constant if it's ground *)
	(match pp_literal term with
	  Some doc -> quotes (doc)
	| None -> bracket (pp_list term))
    | Cons (b,c) -> bracket (pp_list term)
    | Abs (a,c) -> 
	paren abs_prec (Var.pp_var (a) <:> backslash <:> pp abs_prec c)
    | Conc(t,a) -> paren conc_prec (pp conc_prec t <:> amp <:> Var.pp_var a)
    | Fresh (_,t1,t2) -> 
	paren fresh_prec (pp fresh_prec t1 <+> hash <+> pp fresh_prec t2)
(*    | Fresh (Some(ty1,ty2),t1,t2) -> 
	paren fresh_prec (pp fresh_prec t1 <+> hash <+> comment(pp_ty ty1 <:> comma <:> pp_ty ty2) <+> pp fresh_prec t2)*)
    | Eq(_,t1,t2) -> 
	paren eq_prec (pp eq_prec t1 <+> eq <+> pp eq_prec t2)
(*    | Eq(Some ty,t1,t2) -> 
	paren eq_prec (pp eq_prec t1 <+> eq <+> comment(pp_ty ty) <+> pp eq_prec t2)*)
    | EUnify(t1,t2) -> 
	paren eq_prec (pp eq_prec t1 <+> text "~=" <+> pp eq_prec t2)
    | Is(t1,t2) -> 
	paren is_prec (pp is_prec t1 <+> text "is" <+> pp is_prec t2)
    | Cut -> cut
    | True -> text "true"
    | False -> text "false"
    | Implies(t1,t2) -> 
	paren implies_prec 
	  (pp implies_prec  t1 <+> darrow <+> pp implies_prec t2)
    | Or(t1,t2) -> 
	paren or_prec (pp or_prec t1 <+> semi <+> pp or_prec t2)
    | And(t1,t2) -> 
	paren and_prec(pp and_prec t1 <:> comma <+> pp and_prec t2)
    | Forall(v,s,t) -> 
	paren forall_prec 
	  (text "forall" <+> Var.pp_var v <:> colon <:> pp_ty s <:> dot 
	     <+> pp forall_prec  t)
    | Exists(v,s,t) -> 
	paren exists_prec 
	  (text "exists" <+> Var.pp_var v <:> colon <:> pp_ty s <:> dot 
	     <+> pp exists_prec t)
    | New(a,s,t) -> 
	paren new_prec 
	  (text "new" <+> Var.pp_var a <:> colon <:> pp_ty s <:> dot 
	     <+> pp new_prec t)
    | Lambda(x,s,t) -> 
	paren lambda_prec 
	  (text "lambda" <+> Var.pp_var x <:> colon <:> pp_ty s <:> dot 
	     <+> pp lambda_prec t)
    | App (t1,t2) -> paren app_prec (pp app_prec t1 <+> text "$" <+> pp app_prec t2)
    | Guard(t1,t2,t3) -> 
	paren guard_prec 
	  (pp guard_prec t1 <+> arrow <+> pp guard_prec t2  
	     <+>  bar <+> pp guard_prec t3)
    | Not(t) -> paren not_prec (text "not" <+> pp not_prec t)
    | Underscore -> underscore
    | IntC i -> num i
    | BoolC c -> if c then text "true" else text "false"
    | CharC c -> squotes(escaped_char c)
  and pp_literal t = 
    match t with
      Nil -> Some emp
    | Cons (CharC c, tl) -> 
	(match pp_literal tl with 
	  Some doc -> Some (escaped_char c <:> doc)
	| None -> None)
    | _ -> None
  and pp_pair t = 
    match t with
      Pair(b,c) -> 
	pp pair_prec b <:> text "," <:> pp_pair c
    | t -> pp pair_prec t
  and pp_list t = 
    match t with 
      Nil -> emp
    | Cons (b,Nil) -> 
	pp pair_prec b
    | Cons (b,(Cons (_,_) as c)) ->
	pp pair_prec b <:> text "," <:> pp_list c
    | Cons (b,t) -> pp pair_prec b <:> bar <:> pp pair_prec t
    | t ->  pp pair_prec t
  and pp_assoc prec dir a term = 
    match dir,term with 
      Left,Atomic(b,[t1;t2]) -> 
	if a = b then pp_assoc prec dir a t1 
	    <+> Nstbl.pp_path a 
	    <+> pp prec t2
	else pp prec term
    | Right,Atomic(b,[t1;t2]) -> 
	if a = b then pp prec t1 
	    <+> Nstbl.pp_path a
	    <+> pp_assoc prec dir a t2
	else pp prec term
    | Non,_| _,_  -> pp prec term
  in 
  pp toplevel_prec term
;;

let pp_ty0 ty = 
  match ty with
    UnderscoreTy | IdTy _ | VarTy _ | ListTy _ | UnitTy
  | NameTy _ | IntTy | CharTy | BoolTy | PropTy -> pp_ty ty
  | _ -> paren (pp_ty ty)
;;


let rec pp_subst s = 
  sep newline (List.map 
    (fun (v, e) -> 
      text (Var.to_string' v) 
	<+> arrow 
	<+> pp_term e 
	<:> newline)
    (Varmap.to_list s))
;;

let tab = 8;;

let rec pp_rdecl decl = 
  match decl with
    KindDecl(s,k) -> text s <+> colon <+> pp_kind k <:> dot
  | SymDecl (sym,st) -> 
      text sym <+> colon <+> pp_ty st <:> dot
  | FuncDecl (s,[],ty) ->
    text "cnst" <+> text s <+> eq <+> pp_ty ty <:> dot 
  | FuncDecl (s,tys,ty) ->
    text "func" <+> text s 
	<+> (sep space (List.map pp_ty0 tys)) 
	<+> eq <+> pp_ty ty <:> dot 
  | PredDecl (s,tys,_,_) ->
    text "pred" <+> text s <+> 
    (sep space (List.map pp_ty0 tys))<:> dot 
  | ClauseDecl t  -> pp_term t  <:> dot
  | Query (t) -> 
      pp_term t
  | UseDirective(f) -> 
      text "#use" <+> quotes(text f) <:> dot
  | TraceDirective(i) -> 
      text "#trace" <+> quotes(num i) <:> dot 
  | InfixDecl(Left,s,i) -> 
      text "infixl" <+> text s <+> num i <:> dot 
  | InfixDecl(Right,s,i) -> 
      text "infixr" <+> text s <+> num i <:> dot 
  | InfixDecl(Non,s,i) -> 
      text "infixn" <+> text s <+> num i <:> dot 
  | TypeDefn(s,vs,ty) -> 
      text "type" <+> text s <+> (sep space (List.map Var.pp_var vs)) 
	<+> eq <+> pp_ty ty <:> dot 
  | NamespaceDecl (sym,ds) -> 
      text "namespace" <+> text sym 
	<+> paren (indent 8 (sep newline (List.map pp_decl ds))) <:> dot
  | BuiltinFuncDecl (s,[],ty,f) ->
    text "cnst" <+> text s <+> eq <+> pp_ty ty <:> dot 
  | BuiltinFuncDecl (sym,tys,ty,f) -> 
      text "func" <+> text sym 
	<+> (sep space (List.map pp_ty0 tys)) 
	<+> eq <+> pp_ty ty <:> dot 
  | TypeQuery(term) -> 
      text "#type" <+> pp_term term <:> dot
  | QuitDirective -> text "#quit"
  | OpenDirective s -> text "#open" <+> Nstbl.pp_path s
  | HelpDirective(None) -> text "#help"
  | HelpDirective(Some p) -> text "#help"<+> Nstbl.pp_path p
  | CheckDirective(ty,b,None,t) -> 
      text "#check" <+> quotes(text ty) <+> num b 
	<+> colon <+> pp_term t <:>dot
  | CheckDirective(ty,b,Some true,t) -> 
      text "#validate" <+> quotes(text ty) <+> num b 
	<+> colon <+> pp_term t <:>dot
  | CheckDirective(ty,b,Some false,t) -> 
      text "#invalidate" <+> quotes(text ty) <+> num b 
	<+> colon <+> pp_term t <:>dot
  | _ -> Util.impos "Absyn.pp_rdecl"
and pp_decl decl = pp_rdecl decl.rdecl
;;


let rec ftvs s = 
  let (+++) = Varset.union in 
  let e = Varset.empty in
  match s with 
    IdTy _ -> Util.impos "ftvs expects ids to have been resolved"
  | DataTy (_,ss) -> Varset.unions (List.map ftvs ss)
  | PairTy(s1,s2) | AbsTy (s1,s2) | ArrowTy(s1,s2) 
    -> ftvs s1 +++ ftvs s2
  | ListTy s -> ftvs s
  | VarTy v -> Varset.singleton v
  | UnitTy | NameTy _ | UnderscoreTy | IntTy 
  | CharTy | PropTy | BoolTy 
    -> e
;;


let k2s = Printer.print_to_string pp_kind;;


let ty2s = Printer.print_to_string pp_ty;;


let t2s = Printer.print_to_string pp_term;;

let d2s = Printer.print_to_string pp_decl;;
  
let rec apply_tysub sb ty = 
  let h = apply_tysub sb in
  match ty with
    NameTy s -> NameTy s
  | DataTy (ds,ss) -> DataTy (ds,List.map h ss)
  | VarTy v -> (try (Varmap.find v sb) with Not_found -> ty)
  | ListTy s -> ListTy(h s)
  | AbsTy (a,s) -> AbsTy(h a, h s)
  | PairTy (s1,s2) -> PairTy (h s1, h s2)
  | IdTy s -> IdTy s
  | UnitTy -> UnitTy
  | UnderscoreTy -> UnderscoreTy
  | IntTy -> IntTy
  | BoolTy -> BoolTy
  | CharTy -> CharTy
  | PropTy -> PropTy
  | ArrowTy(s1,s2) -> ArrowTy(h s1, h s2)
;;

let rec apply_tysub_term sb tm = 
  let h = apply_tysub_term sb in 
  let h' = apply_tysub sb in 
  match tm with 
    Atomic (sym,tms) -> Atomic(sym,List.map h tms)
  | Var (v) -> Var(v)
  | Name (n) -> Name(n)
  | Transpose (a,b,t) -> Transpose(a,b,h t)
  | Subst (t1,t2,t3) -> Subst(h t1, h t2, h t3)
  | Nil -> Nil
  | Cons (t1,t2) -> Cons(h t1, h t2)
  | Unit -> Unit
  | Pair (t1,t2) -> Pair(h t1, h t2)
  | Abs(a,tm) -> Abs(a,h tm)
  | Conc(tm,a) -> Conc(h tm, a)
  | True -> True
  | False -> False
  | Fresh (None, tm1, tm2) -> Fresh(None,h tm1,h tm2)
  | Fresh (Some (ty1,ty2), tm1, tm2) -> Fresh(Some (h' ty1, h' ty2),h tm1,h tm2)
  | Eq (None,tm1,tm2) -> Eq(None, h tm1,h tm2)
  | Eq (Some ty,tm1,tm2) -> Eq(Some (h' ty), h tm1,h tm2)
  | EUnify(t1,t2) -> EUnify(h t1, h t2)
  | Is (t1,t2) -> Is(h t1, h t2)
  | Implies (t1,t2) -> Implies(h t1, h t2)
  | Or (t1,t2) -> Or(h t1, h t2)
  | And (t1,t2) -> And(h t1, h t2)
  | Forall (v,ty,tm) -> Forall(v,h' ty, h tm)
  | Exists  (v,ty,tm) -> Exists(v,h' ty, h tm)
  | New  (v,ty,tm) -> New(v,h' ty, h tm)
  | Lambda  (v,ty,tm) -> Lambda(v,h' ty, h tm)
  | App(t1,t2) -> App(h t1, h t2)
  | Cut -> Cut
  | Guard (t1,t2,t3) -> Guard(h t1, h t2, h t3)
  | Not (t) -> Not(h t)
  | Underscore -> Underscore
  | _ -> tm
;;

let rec apply_tmsub (sub : term Varmap.t) term =
  match term with
    Atomic (sym,terms) -> Atomic(sym,List.map (apply_tmsub sub) terms)
  | Implies(body,head) -> Implies(apply_tmsub sub body,apply_tmsub sub head)
  | Var v -> if Varmap.mem v sub then Varmap.find v sub else term
  | Pair (t1,t2) -> Pair (apply_tmsub sub t1,apply_tmsub sub t2)
  | True -> True
  | False -> False
  | Or (t1,t2) -> Or(apply_tmsub sub t1, apply_tmsub sub t2)
  | And (t1,t2) -> And(apply_tmsub sub t1, apply_tmsub sub t2)
  | Nil -> Nil
  | Cons (t1,t2) -> Cons(apply_tmsub sub t1, apply_tmsub sub t2)
  | Unit -> Unit
  | Name n -> Name n (* not sure *)
  | Eq (ty,t1,t2) -> Eq(ty,apply_tmsub sub t1,apply_tmsub sub t2)
  | Underscore -> Underscore
  | Not (t) -> Not(apply_tmsub sub t)					   
  | Subst (t1,t2,t3) -> Subst(apply_tmsub sub t1,apply_tmsub sub t2,apply_tmsub sub t3)
  | Fresh (None, tm1, tm2) -> Fresh (None,apply_tmsub sub tm1,apply_tmsub sub tm2)
  | Fresh (Some (ty1,ty2), tm1, tm2) -> Fresh (Some (ty1,ty2),apply_tmsub sub tm1,apply_tmsub sub tm2)
  | EUnify(t1,t2) -> EUnify (apply_tmsub sub t1, apply_tmsub sub t2)
  | Is (t1,t2) -> Is (apply_tmsub sub t1, apply_tmsub sub t2)
  | Forall (v,ty,tm) ->
     let sub' = Varmap.remove v sub in
     Forall(v,ty,apply_tmsub sub' tm)
  | Exists  (v,ty,tm) ->
     let sub' = Varmap.remove v sub in
     Exists(v,ty,apply_tmsub sub' tm)
  | New  (v,ty,tm) ->
     let sub' = Varmap.remove v sub in
     New(v,ty,apply_tmsub sub' tm)
  | Lambda  (v,ty,tm) ->
     let sub' = Varmap.remove v sub in
       Lambda(v, ty, apply_tmsub sub' tm)
  | App(t1,t2) -> App(apply_tmsub sub t1, apply_tmsub sub t2)
  | Cut -> Cut
  | Guard (t1,t2,t3) -> Guard (apply_tmsub sub t1, apply_tmsub sub t2, apply_tmsub sub t3)
  | Transpose (a,b,t) -> Transpose (a,b,apply_tmsub sub t) (* not sure *)
  | Abs(a,tm) -> Abs (a,apply_tmsub sub tm) (* not sure *)
  | Conc(tm,a) -> Conc (apply_tmsub sub tm,a) (* not sure *)
  | _ -> Util.impos "Absyn.apply_tmsub"
;;			   

  
let freshen s = 
  let f = ftvs s in
  let m = Varset.fold 
      (fun v m -> Varmap.add v (VarTy (Var.rename v)) m) f Varmap.empty in
  apply_tysub m s
;;

(* support list all atoms in the "support" of a term,  excluding new-bound and abstracted *)

let rec supp t = 
  let (+++) = Varset.union in 
  let e = Varset.empty in
  match t with
    Atomic(sym,ts) -> Varset.unions (List.map supp ts)
  | Name a -> Varset.singleton a
  | Transpose(a,b,ts) -> Varset.from_list [a;b]
  | Subst(t,u,v) -> supp t +++ supp u +++ supp v
  | New(a,_,t) -> Varset.remove a (supp t)
  | Abs(a,t) | Conc(t,a) -> supp t +++ (Varset.singleton a)
  | Nil|Unit|True|False|Cut|Underscore|IntC _|Var _ | CharC _ | BoolC _
    -> e
  | Not t |Forall(_,_,t)|Exists(_,_,t) |Lambda(_,_,t) 
    -> supp t
  | Cons(t1,t2)|Pair(t1,t2)|Fresh (_,t1,t2)|Eq(_,t1,t2)|Is(t1,t2)|Implies(t1,t2)
  | EUnify(t1,t2)| Or(t1,t2) | And(t1,t2) | App(t1,t2)
    -> (supp t1) +++ (supp t2)
  | Guard(t1,t2,t3) -> (supp t1) +++ (supp t2) +++ (supp t3)
;;


(* free atoms: list all atoms appearing free in a term, including abstraction/concretion but excluding new-bound *)
let rec fas t = 
  let (+++) = Varset.union in 
  let e = Varset.empty in
  match t with
    Atomic(sym,ts) -> Varset.unions (List.map fas ts)
  | Name a -> Varset.singleton a
  | Transpose(a,b,ts) -> Varset.from_list [a;b]
  | Subst(t,u,v) -> fas t +++ fas u +++ fas v
  | Abs(a,t) |New(a,_,t) -> Varset.remove a (fas t)
  | Conc(t,a) -> fas t +++ (Varset.singleton a)
  | Nil|Unit|True|False|Cut|Underscore|IntC _|Var _ | CharC _ | BoolC _
    -> e
  | Not t |Forall(_,_,t)|Exists(_,_,t) |Lambda(_,_,t) 
    -> fas t
  | Cons(t1,t2)|Pair(t1,t2)|Fresh (_,t1,t2)|Eq(_,t1,t2)|Is(t1,t2)|Implies(t1,t2)
  | EUnify(t1,t2)| Or(t1,t2) | And(t1,t2) | App(t1,t2)
    -> (fas t1) +++ (fas t2)
  | Guard(t1,t2,t3) -> (fas t1) +++ (fas t2) +++ (fas t3)
;;


let rec fvs t = 
  let (+++) = Varset.union in 
  let e = Varset.empty in
  match t with
    Atomic(sym,ts) -> Varset.unions (List.map fvs ts)
  | Name a -> Varset.empty
  | Transpose(a,b,ts) -> Varset.empty
  | Subst(t,u,v) -> fvs t +++ fvs u +++ fvs v
  | Abs(a,t) |New(a,_,t) -> fvs t
  | Conc(t,a) -> fvs t
  | Var v -> Varset.singleton v
  | Nil|Unit|True|False|Cut|Underscore|IntC _| CharC _ | BoolC _
    -> e
  | Not t -> fvs t
  | Forall(x,_,t) | Exists(x,_,t) | Lambda(x,_,t) 
    -> Varset.remove x (fvs t)
  | Cons(t1,t2)|Pair(t1,t2)|Fresh (_,t1,t2)|Eq(_,t1,t2)|Is(t1,t2)|Implies(t1,t2)
  | EUnify(t1,t2)| Or(t1,t2) | And(t1,t2) | App(t1,t2)
    -> (fvs t1) +++ (fvs t2)
  | Guard(t1,t2,t3) -> (fvs t1) +++ (fvs t2) +++ (fvs t3)
;;

let freshen_fvs term =
  let free_vars = fvs term in
  let map = Varset.fold 
	      (fun var map ->
	       Varmap.add var (Var (Var.rename var)) map) free_vars Varmap.empty in
  apply_tmsub map term  
;;

let fvas t = Varset.union (fvs t) (fas t);;

let rec fill_holes term =
  match term with
    Underscore -> Var (Var.mkvar "X")
  | Atomic(sym,ts) -> Atomic (sym, List.map fill_holes ts)
  | Transpose(a,b,t) -> Transpose(a,b,fill_holes t)
  | Subst(t,u,v) -> Subst(fill_holes t,fill_holes u,fill_holes v)
  | Cons(t1,t2) -> Cons(fill_holes t1,fill_holes t2)
  | Pair(t1,t2) -> Pair(fill_holes t1,fill_holes t2)
  | Abs(a,t) -> Abs(a,fill_holes t)
  | Conc(t,a) -> Conc(fill_holes t,a)
  | Fresh(tys,t1,t2) -> Fresh(tys,fill_holes t1,fill_holes t2)
  | Eq(ty,t1,t2) -> Eq(ty,fill_holes t1,fill_holes t2)
  | EUnify(t1,t2) -> EUnify(fill_holes t1,fill_holes t2)
  | Is(t1,t2) -> Is(fill_holes t1,fill_holes t2)
  | Implies(t1,t2) -> Implies(fill_holes t1,fill_holes t2)
  | Or(t1,t2) -> Or(fill_holes t1,fill_holes t2)
  | And(t1,t2) -> And(fill_holes t1,fill_holes t2)
  | Forall(v,ty,tm) -> Forall(v,ty,fill_holes tm)
  | Exists(v,ty,tm) -> Exists(v,ty,fill_holes tm)
  | New(v,ty,tm) -> New(v,ty,fill_holes tm)
  | Lambda(v,ty,tm) -> Lambda(v,ty,fill_holes tm)
  | App(t1,t2) -> App(fill_holes t1,fill_holes t2)
  | Guard(t1,t2,t3) -> Guard(fill_holes t1,fill_holes t2,fill_holes t3)
  | Not(t) -> Not(fill_holes t)
  |  _ -> term
;;

let rec unpack_ty ty = 
  match ty with
    ArrowTy(ty1,ty2) -> 
      let (tys',ty') = unpack_ty ty2 in 
      (ty1::tys',ty')
  | _ -> ([],ty)
;;



(* Makes a nonlinear term into a linear pattern + constraint *)
(* TODO: Avoid linearizing  variables that only appear once; pass set of 
variables through monadically and either add to set or generate an equational constraint *)
let linearize_atomic (f,ts) = 
  let rec lin term vs eqns = 
    match term with
      Underscore -> (Underscore,vs,eqns)
    | Pair(t1,t2) -> 
	let (p1,vs1,eqs1) = lin t1 vs eqns in
	let (p2,vs2,eqs2) = lin t2 vs1 eqs1 in
      (Pair(p1,p2),vs2,eqs2)
    | Cons(t1,t2) -> 
	let (p1,vs1,eqs1) = lin t1 vs eqns in
	let (p2,vs2,eqs2) = lin t2 vs1 eqs1 in
	(Cons(p1,p2),vs2,eqs2)
    | Unit -> (Unit,vs,eqns)
    | Nil -> (Nil, vs,eqns)
    | True -> (True, vs,eqns)
    | False -> (False, vs, eqns)
    | Atomic(f,ts) -> 
      let (ts',vs',eqns') = lins ts vs eqns
      in (Atomic(f,ts'),vs',eqns')
    | Var(x) -> 
	if Varset.mem x vs 
	then 
	  let y = Var.mkvar "X" in
	  (Var(y), vs, And(Eq(None,Var(x),Var(y)),eqns))
	else (Var x, Varset.add x vs, eqns) 
    | term -> 
	let y = Var.mkvar "X" in
	(Var(y), Varset.add y vs, And(Eq(None,term,Var(y)),eqns))
  and lins terms vs eqns = 
    match terms with 
      [] -> ([],vs,eqns)
    | t::ts -> 
	let (p,vs1,eqs1) = lin t vs eqns in
	let (ps,vs2,eqs2) = lins ts vs1 eqs1 in
	(p::ps,vs2,eqs2)
  in 
  let (ts',vs,eqns) = lins ts Varset.empty True
  in ((f,ts'),eqns)
  ;;

let rec linearize_prog p = 
  match p with
    Atomic(sym,ts) -> 
      let (sym',ts'),g = linearize_atomic (sym,ts) 
      in Implies(g,Atomic(sym',ts'))
  | Implies(g,p) -> Implies(g, linearize_prog p)
  | Pair(p1,p2)|And(p1,p2) -> And(linearize_prog p1, linearize_prog p2)
  | Forall(x,ty,p) -> Forall(x,ty,linearize_prog p)
  | New(a,ty,p) -> New(a,ty,linearize_prog p)
  | Eq(ty,t1,t2) -> Eq(ty,t1,t2)
  | True -> True
  | _ -> Util.error "linearize_prog: applied to something that is not a program clause"
;;
  
let is_linear t = 
  let combine x y = 
    match x,y with
      Some vs1, Some vs2 -> 
	if Varset.is_empty(Varset.inter vs1 vs2) then Some (Varset.union vs1 vs2)
	else None
    | _,_ -> None
  in
  let rec linear_fvs t = 
    match t with 
      Underscore -> Some (Varset.empty)
    | Unit|Nil|True|False -> Some (Varset.empty)
    | Transpose(_,_,t)|Abs(_,t)|Conc(t,_) -> linear_fvs t
    | Pair(t1,t2)|Cons(t1,t2)|App(t1,t2) -> 
	combine (linear_fvs t1) (linear_fvs t2)
    | Atomic(f,ts) -> 
	List.fold_left combine (Some (Varset.empty)) (List.map linear_fvs ts)
    | Var(x) -> 
	Some (Varset.singleton x)
    | Name(a) -> Some(Varset.empty)
    | _ -> Util.error "unexpected construct in is_linear"
  in 
  match linear_fvs t with Some _ -> true | None -> false
;;

let rec is_firstorder t = 
  match t with 
    Underscore -> true
  | Unit|Nil|True|False -> true
  | Transpose(_,_,_)|Abs(_,_)|Conc(_,_)|App(_,_) -> false
  | Pair(t1,t2)|Cons(t1,t2) -> 
      is_firstorder t1 && is_firstorder t2
  | Atomic(f,ts) -> 
	List.for_all is_firstorder ts
  | Var(x) -> true
  | _ -> false
;;

(* Unify two terms, assuming that both sides are linear, have no 
   shared variables, and have no nominal features. *)

let unify_linear t1 t2 =
  let rec unify t1 t2 s = 
    match t1,t2 with 
      Var(x), t -> Varmap.add x t s 
    | t, Var(x) -> Varmap.add x t s 
    | Underscore,_ -> s
    | _,Underscore -> s
    | Unit, Unit -> s
    | Name a, Name b -> if Var.eq a b then s else raise Not_found
    | Pair(t1,t2),Pair(u1,u2) -> unify t1 u1 (unify t2 u2 s)
    | Nil, Nil -> s
    | Cons(t1,t2) , Cons(u1,u2) -> unify t1 u1 (unify t2 u2 s)
    | Atomic(f,ts), Atomic(g,ts') -> 
	if f = g && List.length ts = List.length ts'
	then unifys ts ts' s
	else raise Not_found
    | _,_ -> raise Not_found
  and unifys ts1 ts2 s = 
    match ts1, ts2 with 
      [],[] -> s
    | t1::ts1, t2::ts2 -> 
	unify t1 t2 (unifys ts1 ts2 s)
    | _,_ -> Util.impos "Absyn.unifys"
  in try Some(unify t1 t2 Varmap.empty) with Not_found -> None
;;


let rec simplify clause = 
  match clause with 
    And(d1,d2) -> (
      match (simplify d1, simplify d2) with 
	True,d'|d',True -> d'
      |	d1',d2' -> And(d1',d2')
	    )
  | Implies(g,d) -> (
      match simplify_goal g with
	False -> True 
      |	True -> simplify d
      |	g' -> Implies(g',simplify d)
	    )
  | d' -> d'
and simplify_goal g = 
  match g with 
    And(g1,g2) -> (
      match (simplify_goal g1, simplify_goal g2) with 
	True,g'|g',True -> g'
      |	False,_|_,False -> False 
      |	g1',g2' -> And(g1',g2')
	    )
  | Or(g1,g2) -> (
      match (simplify_goal g1, simplify_goal g2) with 
	True,_|_,True -> True
      |	False,g'|g',False -> g'
      |	g1',g2' -> Or(g1',g2')
  )
  | Exists(v,ty,g') -> (
    match simplify_goal g' with
      True -> True
    | False -> False
    | g'' -> Exists(v,ty,g'')
  )
  | New(v,ty,g') -> (
    match simplify_goal g' with
      True -> True
    | False -> False
    | g'' -> New(v,ty,g'')
  )
  (* HH extension *)                      
  | Implies(g1,g2) -> (
      match (simplify_goal g1, simplify_goal g2) with 
	True,_|_,True -> True
      |	False,g'|g',False -> g'
      |	g1',g2' -> Implies(g1',g2')
  )
  | Forall(v,ty,g') -> (
    match simplify_goal g' with
      True -> True
    | False -> False
    | g'' -> Forall(v,ty,g'')
  )
  |  g' -> g'	    
      
;; 

(* A Horn program clause is well-quantified if every variable or name appearing in a subgoal also appears in every possible clause head.  *)


let is_well_quantified prog = 
  let rec iswq vs p = 
    match p with 
      True -> true
    | And(p1,p2) -> iswq vs p1 && iswq vs p2
    | Forall (x,ty,p) -> if Varset.mem x vs then false else iswq vs p
    | New (a,ty,p) -> if Varset.mem a vs then false else iswq vs p
    | Implies(g,p) -> 
	let vs' = fvas g in 
(*	print_endline "Implication" ;
	print_endline (Printer.pp Varset.pp_varset vs'); *)
	iswq (Varset.union vs vs') p
    | Eq(_,t1,t2) -> 
	let vs' = Varset.union (fvas t1) (fvas t2) in
(*	print_endline "Atomic=" ;
	print_endline ((Printer.pp Varset.pp_varset vs)^" <= " ^ (Printer.pp Varset.pp_varset vs')); *)
	Varset.subset vs vs'
    | Atomic(_,ts) -> 
	let vs' = Varset.unions (List.map fvas ts) in
(*	print_endline "Atomic" ;
	print_endline ((Printer.pp Varset.pp_varset vs)^" <= " ^ (Printer.pp Varset.pp_varset vs')); *)
	Varset.subset vs vs'
    |  _ -> Util.error "Unexpected construct in is_well_quantified"
  in 
  iswq Varset.empty prog


(* This is tricky because of the possibility of conjunction in heads of clauses:
e.g. to well-quantify something like 

(p(X,Y);p(Y,Z)) :- q(X,Y,Z).

there is no way to do this with a single implication instead the result should be:

(p(X,Y) :- exists Z. q(X,Y,Z)) , (p(Y,Z) :- exists X. q(X,Y,Z))

This doesn't really affect the common case of Horn clauses but can happen.

So, what we do is crawl over the program and build a list of the possible heads and their free vars and free names.
Whenever we encounter an implication we quantify all fvs or free names from the outside inso that fvs and free names not appearing in the head get quantified as late as possible.
*)

(* First, convert program clause into a list of "simple clauses" with only one head i..e no conjunction or "true" *)
let normalize_prog prog = 
  let rec traverse p = 
    match p with 
      True -> []
    | And(p1,p2) -> traverse p1 @ traverse p2
    | Forall(x,ty,p) ->
	Util.nyi()
    | New(a,ty,p) -> 
	Util.nyi()
    | Implies(g,p) -> 
	List.map (fun (vs,p',g') -> vs, p',And(g,g')) (traverse p)
    | Atomic(f,ts) -> 
	[Varset.unions (List.map fvas ts), Atomic(f,ts), True]
    | Eq(tyopt, t1, t2) -> [Varset.union (fvas t1) (fvas t2), Eq(tyopt, t1, t2),True]
    |  _ -> Util.error "Unexpected program clause construct in normalize_prog"
  in traverse prog
;;


let well_quantify_prog prog = 
  let progs = normalize_prog prog in
  let rec wqp (vs, p, g) = 
    (* get the vars present in g but not in head *)
    let vars = Varset.diff (fvs g) vs in 
	(* quantify them *)
    let g' = Varset.fold (fun x g0 -> Exists(x,UnderscoreTy,g0)) vars g in 
	(* get the vars present in g but not in head *)
    let atoms = Varset.diff (fas g) vs in 
	(* quantify them too - these will be quantified outside the foralls. *)
    let g'' = Varset.fold (fun a g0 -> New(a,UnderscoreTy,g0)) atoms g' in 
    Implies(g'',p)
  in List.fold_left (fun g vspg  -> And(g,wqp vspg)) True progs 
  ;;
