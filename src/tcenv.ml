open Absyn;;
open Types;;
module N = Nstbl;;

type symk = VarS of ty | NameS of ty;;


let pp_symk symk = 
  match symk with
    NameS s -> pp_ty s
  | VarS s -> pp_ty s
;;


type tyk = DataKd | NameKd | TypeKd;;


let pp_tyk symk = 
  match symk with
    DataKd -> Printer.text "data"
  | NameKd -> Printer.text "atom"
  | TypeKd -> Printer.text "type"
;;


type ctx = symk Varmap.t;;


type tctx = tyk Varmap.t;;


type ty_abbrev = ty list -> ty;;


type ksg = (kind*Unique.uniq*ty_abbrev option) Nstbl.t;;



(* bool is whether it's a definition *)
type tsg_entry = {is_def:bool; is_abbrev : bool; sym_id:Unique.uniq; sym_ty:ty};;


type tsg = tsg_entry N.t;; 


type sg = {ksg:ksg; 
           tsg:tsg; 
           stbl:(Unique.uniq, Nstbl.sym) Hashtbl.t;
           kdecls : (Nstbl.sym * kind) list ref;
           tdecls : (Nstbl.sym * ty) list ref;
           clauses : term list ref};;


let init_sg () = 
  let sg = {ksg=Nstbl.create 100;
            tsg=Nstbl.create 100;
            stbl=Hashtbl.create 100;
            kdecls = ref [];
            tdecls = ref [];
            clauses = ref []} in
  sg

type eqns = (Types.var * Absyn.ty) list;;


type tcenv = Varset.t * tctx * ctx* eqns;;







let get_definition sg dty_sym = 
  let tsg = sg.tsg in
  let ksg = sg.ksg in
  let rec return_ty_matches ty = 
    match ty with
      DataTy(dty',[]) -> dty_sym = Nstbl.resolve ksg dty'
    | ArrowTy(_,ty) -> return_ty_matches ty
    | _ -> false
  in 
  let rec flatten_ty ty = 
    match ty with
      ArrowTy(ty,ty') -> ty::flatten_ty ty'
    | _ -> []
  in   
  let entries = Nstbl.to_list tsg in 
  let relevant_entries = 
    List.filter 
      (fun (sym,entry) -> entry.is_def = false && 
	return_ty_matches entry.sym_ty) 
      entries in
  List.map 
    (fun (sym,entry) -> 
      (sym,flatten_ty entry.sym_ty)) 
    relevant_entries
;;


let add_kind_decl sg s k abbrev_opt = 
  let u = Unique.get() in
  Nstbl.add sg.ksg (Nstbl.Rel(Nstbl.Base(s))) (k,u,abbrev_opt);
  let s' = Nstbl.resolve sg.ksg (Nstbl.Rel (Nstbl.Base s)) in
  Hashtbl.add sg.stbl u s';
  if abbrev_opt = None then sg.kdecls := (s',k)::!(sg.kdecls);
  sg,u
;;


let add_sym_decl sg f is_def is_abbrev is_con ty = 
  let u = Unique.get() in
  let entry = {is_def=is_def;is_abbrev = is_abbrev;sym_id = u;sym_ty = ty} in
  Nstbl.add sg.tsg (Nstbl.Rel(Nstbl.Base(f))) entry;
  let f' = Nstbl.resolve sg.tsg (Nstbl.Rel (Nstbl.Base f)) in
  Hashtbl.add sg.stbl u f';
  if is_con then sg.tdecls := (f',ty)::!(sg.tdecls);
  sg,u
;;

let add_clause_decl sg t = 
  sg.clauses := t::!(sg.clauses);
  sg
;;

let enter_namespace sg sym = 
  Nstbl.enter_ns sg.tsg sym;
  Nstbl.enter_ns sg.ksg sym
;;

let exit_namespace sg = 
  Nstbl.exit_ns sg.tsg;
  Nstbl.exit_ns sg.ksg
;;


(* Add built-in symbols *)
let empty_env = 
  let vs = Varset.empty in
  let tctx = Varmap.empty in
  let ctx = Varmap.empty in
  let eqns = [] in
  (vs,tctx,ctx,eqns)
;;

let lookup_env v (vs,tctx,ctx,eqns) =
  let ty0 = match Varmap.find v ctx with
    VarS ty -> ty
  | NameS ty -> ty
  in
  ty0
;;
