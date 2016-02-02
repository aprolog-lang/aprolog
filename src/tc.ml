(* Alpha Prolog *)
(* Typechecking and translation to internal representation *)
open Absyn;;
open Monad;;
module N = Nstbl;;
open Printer;;
open Tcenv;;
open Types;;



type 'a tcm = (sg,tcenv,'a) scmonad;;


(* Fields *)
let sgF = (fun sg -> sg), (fun _ sg -> sg);;


let vsF = (fun (vs,tctx,ctx,eqns) -> vs),
  (fun (_,tctx,ctx,eqns) vs -> (vs,tctx,ctx,eqns));;


let tctxF = (fun (vs,tctx,ctx,eqns) -> tctx),
  (fun (vs,_,ctx,eqns) tctx -> (vs,tctx,ctx,eqns));;


let ctxF = (fun (vs,tctx,ctx,eqns) -> ctx),
  (fun (vs,tctx,_,eqns) ctx -> (vs,tctx,ctx,eqns));;


let eqnsF = (fun (vs,tctx,ctx, eqns) -> eqns),
  (fun (vs,tctx,ctx,_) eqns -> (vs,tctx,ctx, eqns));;

exception TcFail of string;;


let tcfail msg = raise (TcFail msg);;


let incompatible s1 s2 =
  tcfail ("types "^ty2s s1^" and "^ty2s s2^" are incompatible")
;;


let force_namek ksg s =
  try match N.find ksg s with 
    NameK,_,None -> ()
  | _ -> tcfail ("expected type "^N.p2s s^" to be an name type")
  with Not_found -> tcfail ("unknown type identifier '"^N.p2s s^"'")
;;


let resolve_sg sg s = 
  match N.find sg s with
    x -> let sym = N.resolve sg s in (x,sym)
;;


let lookup_sg sg s = 
  try resolve_sg sg s
  with Not_found -> tcfail ("unknown identifier '"^N.p2s s^"'")
;;


let do_subst v s = 
  get vsF >>= fun vs -> 
  if Varset.mem v vs
  then 
    update eqnsF (fun x -> (v,s)::x) >>
    return true
  else return false
;;


let rec check_ty_eq s1 s2 = 
  match s1, s2 with
    NameTy (ats), NameTy (ats') -> 
      return (ats = ats')
  | DataTy (dts,ss), DataTy (dts',ss') -> 
      if List.length ss != List.length ss' 
      then return false
      else 
	fold_left2 (fun b s1 s2 -> 
	    check_ty_eq s1 s2 >>= (fun b' -> 
	    return (b && b')))
	  true ss ss' >>= (fun b' -> 
        return (b' && dts = dts'))
  | IdTy(_),_ -> Util.impos "unexpected IdTy"
  | _,IdTy(_) -> Util.impos "unexpected IdTy"
  | UnitTy, UnitTy -> 
      return true
  | PairTy(s1,s2), PairTy(s1',s2') -> 
      check_ty_eq s1 s1' >>= (fun b -> 
      check_ty_eq s2 s2' >>= (fun c -> 
      return (b && c)))
  | AbsTy(ats,s), AbsTy(ats',s') -> 
      check_ty_eq ats ats' >>= (fun b -> 
      check_ty_eq s s' >>= (fun c -> 
	return (b && c)))
  | ListTy s, ListTy s' -> 
      check_ty_eq s s'
  | VarTy v, VarTy w -> 
      if Var.eq v w then return true
      else (* TODO: bug due to generating two equations? *)
	do_subst v (VarTy w) >>= (fun b -> 
	do_subst w (VarTy v) >>= (fun c -> 
	return (b || c)))
  | PropTy,PropTy -> return true
  | IntTy, IntTy -> return true
  | BoolTy,BoolTy -> return true
  | CharTy, CharTy -> return true
  | ArrowTy(s1,s2), ArrowTy(s1',s2') ->  
      check_ty_eq s1 s1' >>= (fun b -> 
      check_ty_eq s2 s2' >>= (fun c -> 
      return (b && c)))
  | UnderscoreTy, s 
  | s, UnderscoreTy -> return true
  | VarTy v, s 
  | s, VarTy v -> do_subst v s
  | _,_ -> return false
;;


let is_var' s =
  if String.length s < 1 
  then Util.impos "empty identifier"
  else 
    let c = String.get s 0 in
    c = Char.uppercase c
;;


let is_var sym =
  match sym with
    N.Rel(t) -> 
      let s = N.get_base t in
      is_var' s
  | _ -> false
;;


let get_var sym =
  match sym with
    N.Rel(t) -> 
      let s = N.get_base t in
      Var.mkvar' s
  | _ -> Util.impos "not a var"
;;

let kd2s k = 
  match k with 
    TypeKd -> "type"
  | DataKd -> "data"
  | NameKd -> "name"
;;


let kd_leq k1 k2 = 
  match k1, k2 with
    _,TypeKd -> true
  | DataKd,DataKd -> true
  | NameKd,NameKd -> true
  | _,_ -> false
;;


let check_kd_leq k1 k2 = 
  if kd_leq k1 k2 then return ()
  else tcfail ("expected "^kd2s k2^", but found "^kd2s k1)
;;


let kd_min k1 k2 = 
  match k1,k2 with
    TypeKd,k2 -> k2
  | k1,TypeKd -> k1
  | NameKd,NameKd -> NameKd
  | DataKd,DataKd -> DataKd
  | _,_ -> tcfail ("type variable used at incompatible kinds "^kd2s k1^" and "^kd2s k2)
;;


let reflect_ty vs ty tys = 
    let vts = 
      try List.combine vs tys 
      with Invalid_argument _ -> 
	tcfail ("Too "^(if List.length vs < List.length tys 
	                then "many" 
	                else "few")^" arguments to type abbreviation")
    in
    let rec h ty =
      match ty with
	IdTy _ -> Util.impos "reflect_ty: unexpected IdTy"
      | NameTy ats -> NameTy ats
      | DataTy (dts,ss) -> DataTy(dts,List.map h ss)
      | UnitTy -> UnitTy
      | PairTy (t1,t2) -> PairTy(h t1, h t2)
      | AbsTy (t1,t2) -> AbsTy(h t1, h t2)
      | ListTy t -> ListTy (h t)
      | VarTy v -> 
	  (try 
	    List.assoc v vts 
	  with Not_found -> 
	    tcfail ("unbound type variable "^(Var.to_string' v)
		    ^" in abbreviation"))
      | ArrowTy (t1,t2) -> ArrowTy(h t1, h t2)
      | UnderscoreTy -> UnderscoreTy
      | IntTy -> IntTy 
      | PropTy -> PropTy
      |	BoolTy -> BoolTy
      |	CharTy -> CharTy
    in h ty
;;


let check_disjoint_vars vs = 
  let rec chk s vs = 
    match vs with 
      [] -> ()
    | (VarTy v)::vs -> 
	if Varset.mem v s 
	then tcfail ("Repeated variable "^Var.to_string' v^" in datatype constructor declaration")
	else chk (Varset.add v s) vs
    | t::vs -> tcfail ("Datatype constructor definition must be a sequence of distinct variables")
  in chk Varset.empty vs
;;

    
let check_ty s0 arrow tyk = 
  let rec check_ty' s arrow tyk = 
  let check_ty s tyk = check_ty' s arrow tyk in (* patch *)
    using (fun {ksg=ksg;tsg=_} -> 
    match s with 
    IdTy sid -> 
      (* lookup sid in sg *)
      (try match N.find ksg sid with 
	NameK,_,None -> 
	  check_kd_leq NameKd tyk >>
	  let ats' = N.resolve ksg sid in
	  return (NameTy(N.Root(ats')))
      | NameK,_,Some f -> 
	  check_kd_leq NameKd tyk >>
	  return (f [])
      | TypeK,_,None -> 
	  check_kd_leq DataKd tyk >>
	  let dts' = N.resolve ksg sid in
	  return (DataTy(N.Root(dts'),[]))
      | TypeK,_,Some f -> 
	  check_kd_leq DataKd tyk >>
	  return (f [])
      | ArrowK(_,_),_,_ -> tcfail ("type "^ty2s s^" is not well-formed")
      with Not_found -> 
	(* If it's a var, proceed using the varname. *)
	if is_var sid 
	then 
	  let v = get_var sid in
	  check_ty (VarTy v) tyk
	else tcfail ("unknown type identifier '"^N.p2s sid^"'"))
  | UnitTy -> 
      check_kd_leq TypeKd tyk >>
      return s
  | NameTy(ats) -> 
      check_kd_leq NameKd tyk >>
      (force_namek ksg ats;
       get sgF >>= fun sg -> 
       let ats' = N.resolve ksg ats in
       return (NameTy(N.Root(ats'))))
  | DataTy(dts,ss) -> 
      check_kd_leq DataKd tyk >>
      (try 
	let k,_,abbrev = (N.find ksg dts) in
	check_tys' dts ss arrow k >>= fun ss' -> 
(* TODO: Get rid of this check when grd-style datatypes implemented *)
	if tyk = DataKd 
	then check_disjoint_vars ss';
	match abbrev with 
	  None -> let dts' = N.resolve ksg dts in
	  return (DataTy(N.Root(dts'),ss'))
	| Some f -> return (f ss')
      with Not_found -> tcfail ("unknown type identifier '"^N.p2s dts^"'")
      )
  | PairTy(s1,s2) -> (* pair : any -> any -> any *)
      check_kd_leq TypeKd tyk >>
      check_ty s1 TypeKd >>= fun s1' ->
      check_ty s2 TypeKd >>= fun s2' -> 
      return (PairTy(s1',s2'))
  | AbsTy(s,t) ->  (* abs : atom -> data -> data *)
      check_kd_leq TypeKd tyk >>
      check_ty s NameKd >>= fun s' -> 
      check_ty t TypeKd >>= fun t' -> 
      return (AbsTy(s',t'))
  | ListTy s -> 
      check_kd_leq TypeKd tyk >>
      check_ty s TypeKd >>= fun s' -> 
      return (ListTy s')
  | VarTy(v) -> 
      get tctxF >>= fun tctx ->
	(try 
	  let k = Varmap.find v tctx in
	  set tctxF (Varmap.add v (kd_min k tyk) tctx)
	with Not_found -> 
	  set tctxF (Varmap.add v tyk tctx)) >>
        return (VarTy v)
  | UnderscoreTy -> 
      let v = Var.mkvar "_" in
      update vsF (fun vs -> Varset.add v vs) >>
      check_ty (VarTy v) tyk
  | IntTy ->       
      check_kd_leq TypeKd tyk >>
      return IntTy 
  | BoolTy -> 
      check_kd_leq TypeKd tyk >>
      return BoolTy 
  | CharTy -> 
      check_kd_leq TypeKd tyk >>
      return CharTy
  | PropTy -> 
      if !Flags.forbid_prop && arrow 
      then tcfail ("higher-order type "^ty2s s0^" not allowed")
      else 
	check_kd_leq TypeKd tyk >>
	return PropTy
  | ArrowTy(s1,s2) ->
      if !Flags.forbid_higher_order && arrow 
      then tcfail ("higher-order type "^ty2s s0^" not allowed")
      else 
        check_kd_leq DataKd tyk >>
	check_ty' s1 true TypeKd >>= fun s1' ->
	check_ty s2 tyk >>= fun s2' -> 
	return (ArrowTy(s1',s2')))

  and check_tys' sym ss arrow k = 
    let check_ty sym tyk  = check_ty' sym arrow tyk in
    let check_tys sym ss k = check_tys' sym ss arrow k in
    let do_kind k = 
      match k with
	TypeK -> TypeKd
      | NameK -> NameKd
      | _ -> tcfail ("kind "^k2s k^" is not allowed here")
    in
    match ss,k with
      [], TypeK -> return []
    | [], NameK -> 
	if !Flags.restrict_name_type 
	then tcfail ("in kind declaration of "^N.p2s sym
		     ^", return type cannot be nominal")
	else return []
    | s::ss, ArrowK(k,k') -> 
	check_ty s (do_kind k) >>= fun s' -> 
	check_tys sym ss k' >>= fun ss' -> 
	return (s'::ss')
    | [],_ -> tcfail ("too few arguments to type constructor "^N.p2s sym)
    | _::_,_ -> tcfail ("too many arguments to type constructor "^N.p2s sym)
  in
  check_ty' s0 arrow tyk

;;

let bind_tvar v is_exist tyk = 
   (if is_exist then update vsF (Varset.add v) else skip) >>
   update tctxF (Varmap.add v tyk)
;;

  
let bind_fresh_name x = 
   let v = Var.rename x in
   let s = VarTy v in
   bind_tvar v true NameKd >>
   update ctxF (Varmap.add x (NameS s)) >>
   return s
;;


let bind_fresh_var x = 
   let v = Var.rename x in
   let s = VarTy v in
   bind_tvar v true TypeKd >>
   update ctxF (Varmap.add x (VarS s)) >>
   return s
;;

      
let infer_id_ty x  =
  get ctxF >>= fun ctx -> 
  try 
    match Varmap.find x ctx with
      VarS s -> return (Var x,s)
    | NameS s -> return (Name x,s)
  with Not_found -> 
  if is_var' (Var.to_string' x)
  then 
    bind_fresh_var x >>= fun s -> 
    return (Var x,s)
  else 
    bind_fresh_name x >>= fun s -> 
    return (Name x, s)
;;


let check_id_ty x s =
  infer_id_ty x >>= (fun (tm,s') -> 
  check_ty_eq s s' >>= (fun b -> 
  if not b 
  then tcfail ("identifier '"^Var.to_string' x
	       ^"' has type "^ty2s s'
	       ^" which is incompatible with expected type "^ty2s s)
  else return (tm)))
;;


let infer_name_ty sym  =
  using (fun sg -> 
    if N.mem (sg.tsg) (N.Rel(N.Base (Var.to_string' sym)))
    then tcfail ("constant/function symbol "^Var.to_string' sym
		 ^" used as a name");
    get ctxF >>= fun ctx -> 
    try 
      match Varmap.find sym ctx with
      | NameS s -> return (sym,s)
      | _ -> tcfail ("variable symbol "
		     ^(Var.to_string'  sym)^" used as a name")
    with Not_found -> 
      if is_var' (Var.to_string' sym)
      then tcfail ("variable "^(Var.to_string'  sym)^" used as a name")
      else 
	bind_fresh_name sym >>= fun s -> 
	return (sym,s))  
;;


let check_quantifier check x ty t k = 
    check_ty ty true k >>= fun ty -> 
    let symk = 
      match k with
	NameKd -> NameS ty
      | _ -> VarS ty
    in 
    update ctxF (Varmap.add x symk) >>
    check t >>= fun p -> 
    update ctxF (Varmap.remove x) >>
    return (x,ty,p)
;;



let rec infer_list_ty sym tms ty = 
    match tms,ty with
      [],ArrowTy(_,_) -> 
        if !Flags.forbid_higher_order
        then tcfail("too few arguments to constructor "^N.ns2s sym)
        else return([],ty)
    | [],ty -> return ([],ty)
    | t::tms, ArrowTy(ty1,ty2) -> 
	check_term t ty1 >>= fun (tm) -> 
	infer_list_ty sym tms ty2 >>= fun (tms,ty) -> 
	return (tm::tms,ty)
    | t::tms,_  -> tcfail("too many arguments to constructor "^N.ns2s sym)

and check_list_ty sym tms ty ty'  = 
  infer_list_ty sym tms ty >>= fun (tms,ty'') -> 
  check_ty_eq ty' ty'' >>= fun b ->  
  if not(b) 
  then tcfail ("constructor "^N.ns2s sym
	       ^" has result type "^ty2s ty''
	       ^" which is incompatible with expected type "^ty2s ty')
  else return (tms)

and infer_term tm = 
  match tm with
    Atomic(path,ts) -> 
      let is_single = (ts = []) in
      using (fun sg -> 
	try let (entry,sym) = resolve_sg (sg.tsg) path in
	let ty = freshen entry.sym_ty in
	check_ty ty false TypeKd >>= fun ty -> 
	let vs = ftvs ty in
	update vsF (Varset.union vs) >>
	infer_list_ty sym ts ty >>= fun (tms,ty') -> 
	return (Atomic(N.Root(sym), tms),ty')
	with Not_found -> 
	  if is_single 
	  then 
	    infer_id_ty (get_var path) >>= fun (tm,s) -> 
	    return (tm,s)
	  else tcfail ("unknown identifier '"^Nstbl.p2s path^"'"))
  | Transpose(a,b,t) -> 
      infer_name_ty a >>= fun (a',ty1) -> 
      infer_name_ty b >>= fun (b',ty2) -> 
      check_ty_eq ty1 ty2 >>= fun c -> 
      if not(c) then tcfail ("transposition swaps atoms of different types "
			     ^ty2s ty1^" and "^ty2s ty2);
      infer_term t >>= fun (tm, ty) -> 
      return (Transpose(a',b',tm), ty)
  | Subst(t1,t2,t3) -> 
      infer_term t1 >>= fun (t1,ty1) -> 
      infer_term t2 >>= fun (t2,ty2) -> 
      check_term t3 ty2 >>= fun (t3) -> 
      return (Subst(t1,t2,t3),ty1)
  | Unit -> return (Unit,UnitTy)
  | IntC i -> return (IntC i, IntTy)
(* TODO: This is out of date. *)
  | True -> return (BoolC true, BoolTy)
  | False -> return (BoolC false, BoolTy)
  | BoolC s -> return (BoolC s, BoolTy)
  | CharC c -> return (CharC c, CharTy)
  | Pair(t1,t2) ->
      infer_term t1 >>= (fun (t1,s1) ->
      infer_term t2 >>= (fun (t2,s2) ->
      return (Pair(t1,t2),PairTy (s1,s2))))
  | Abs(sym,tm) -> 
      infer_name_ty sym >>= fun (a,ats) -> 
      infer_term tm >>= fun (tm,s2) ->
      return (Abs(a,tm),AbsTy(ats,s2))
  | Conc(tm,sym) -> 
      infer_name_ty sym >>= fun (a,ats) -> 
      let y = Var.mkvar0() in 
      bind_tvar y true TypeKd >>
      check_term tm (AbsTy(ats,VarTy y)) >>= fun tm' -> 
      return (Conc(tm',a), VarTy y)
  | Lambda (x,ty,tm) -> 
      check_quantifier infer_term x ty tm TypeKd >>= fun (x',ty1,(tm',ty2)) -> 
      return (Lambda(x',ty1,tm'),ArrowTy(ty1,ty2))
  | App(t1,t2) -> 
      let x = Var.mkvar0() in 
      bind_tvar x true TypeKd >>
      let y = Var.mkvar0() in 
      bind_tvar y true TypeKd >>
      check_term t1 (ArrowTy(VarTy x,VarTy y)) >>= fun t1' -> 
      check_term t2 (VarTy x) >>= fun t2' -> 
       return (App(t1',t2'), VarTy y)
  | Underscore -> 
      let v = Var.mkvar "_" in
      infer_id_ty v >>= fun (tm,ty) -> 
      return (tm,ty)
  | Nil -> 
      let v = Var.mkvar "_" in
      let s = VarTy v in
      bind_tvar v true TypeKd >>
      return (Nil,ListTy(s))
  | Cons(t1,t2) -> 
      infer_term t1 >>= fun (t1,s) -> 
      check_term t2 (ListTy s) >>= fun (t2) -> 
      return (Cons(t1,t2),ListTy s)
  | Var v -> 
      get ctxF >>= fun ctx -> 
      (try 
	match Varmap.find v ctx with
	  VarS s -> return (Var v,s)
	| NameS s -> tcfail ("Name symbol '"^Var.to_string' v
			     ^"' used as variable")
      with Not_found -> 
	bind_fresh_var v >>= fun s -> 
	return (Var v,s))
  | Name v -> 
      get ctxF >>= fun ctx -> 
      (try 
	match Varmap.find v ctx with
	  VarS s -> tcfail("Variable symbol '"^Var.to_string' v
			   ^"' used as atom")
	| NameS s -> return (Name v,s)
      with Not_found -> 
	bind_fresh_name v >>= fun s -> 
	return (Name v,s))
  | tm -> tcfail ("term "^t2s tm^" is not well-formed") (* TODO: Better reporting here *)

and check_term tm s = 
  infer_term tm >>= fun (tm',s') -> 
  check_ty_eq s s' >>= fun b ->
  if not(b) then tcfail ("term \n\t"^t2s tm
			 ^"\nhas type\n\t"^ty2s s'
			 ^"\nwhich is incompatible with type\n\t"^ty2s s);
  return tm'
      



let rec check_prog prop = 
   match prop with 
    Atomic(p,tms) -> 
      using (fun sg -> 
      let (entry,sym) = lookup_sg sg.tsg p in
      let ty = freshen entry.sym_ty in
      check_ty ty false TypeKd >>= fun ty -> 
(* TODO: Use instantiable type variables and check that the inferred 
type ultimately is polymorphic enough, instead of forcing the type to 
be maximally polymorphic by treating the freshned names as constants. *)
      check_list_ty sym tms ty PropTy >>= fun ts' -> 
      return (Atomic(N.Root(sym),ts')))
  | True -> return True
  | Eq(_,Atomic(f,tms),tm) -> 
      using (fun sg -> 
      let (entry,sym) = lookup_sg sg.tsg f in
      if not entry.is_def
      then tcfail ("attempt to define an atomic symbol "^N.p2s f^ "\n(likely cause: used '=' instead of ':-')")
      else 
	infer_list_ty sym tms entry.sym_ty >>= fun (tms',s1) -> 
        infer_term tm >>= fun (tm',s2) -> 
        check_ty_eq s1 s2 >>= fun b -> 
        if not b 
        then tcfail ("defined term has type "
		     ^ty2s s1^", which is incompatible with body type "^ty2s s2)
        else return (Eq(Some s1,Atomic(N.Root( sym),tms'),tm')))
  | Implies(t1,t2) -> 
      check_goal t1 >>= fun g -> 
      check_prog t2 >>= fun p -> 
      return (Implies(g,p))
  | And(t1,t2) -> 
      check_prog t1 >>= fun p1 -> 
      check_prog t2 >>= fun p2 -> 
      return (And(p1,p2))
  | Pair(t1,t2) -> 
      check_prog t1 >>= fun p1 -> 
      check_prog t2 >>= fun p2 -> 
      return (And(p1,p2))
  | Forall(v,s,t) -> 
      check_quantifier check_prog v s t TypeKd >>= fun (x,ty,p) -> 
      return (Forall(x,ty,p))
  | New(v,s,t) -> 
      if !Flags.new_goal_only
      then tcfail ("term "^t2s prop^" is not a well-formed clause")
      else check_quantifier check_prog v s t NameKd >>= fun (x,ty,p) -> 
      return (New(x,ty,p))
  | _ -> tcfail ("term "^t2s prop^" is not a well-formed program")

and check_goal goal = 
  match goal with
    Atomic(path,ts) ->   
      using (fun sg -> 
      let (entry,sym) = lookup_sg (sg.tsg) path in
      let ty = freshen entry.sym_ty in
      check_ty ty false TypeKd >>= fun ty -> 
      let vs = ftvs ty in
      update vsF (Varset.union vs) >>
      infer_list_ty sym ts ty >>= fun (tms,ty) -> 
	(match ty with 
	  PropTy -> return (Atomic(N.Root(sym), tms))
	| BoolTy -> return (Is(BoolC true,Atomic(N.Root(sym), tms)))
	| ty -> incompatible ty PropTy
	))
  | Fresh(_,t1,t2) -> 
      infer_term t1 >>= fun (t1',nty) -> 
      let _ = check_ty nty true NameKd in
      infer_term t2 >>= fun (t2',ty) -> 
      (match t1' with
	Name _ | Var _ | Transpose _ -> return (Fresh (Some (nty,ty),t1',t2')) 
	    (* TODO: Do check that transpose eventually around a var. *)
      | _ -> tcfail "left side of # must be a name or variable")
  | Eq(_,t1,t2) -> 
      infer_term t1 >>= (fun (t1,s1) -> 
      infer_term t2 >>= (fun (t2,s2) -> 
      check_ty_eq s1 s2 >>= (fun b -> 
      if not b 
      then tcfail ("in equality test, types "
		   ^ty2s s1^" and "^ty2s s2^" are incompatible") 
      else return (Eq(Some s1, t1,t2)))))
  | EUnify(t1,t2) -> 
      infer_term t1 >>= (fun (t1,s1) -> 
      infer_term t2 >>= (fun (t2,s2) -> 
      check_ty_eq s1 s2 >>= (fun b -> 
      if not b 
      then tcfail ("in equivariant unification, types "
		   ^ty2s s1^" and "^ty2s s2^" are incompatible") 
      else return (EUnify(t1,t2)))))
  | Is(t1,t2) ->  (* TODO: Mode/groundness checking *)
      infer_term t1 >>= (fun (t1,s1) -> 
      infer_term t2 >>= (fun (t2,s2) -> 
      check_ty_eq s1 s2 >>= (fun b -> 
      if not b 
      then tcfail ("in evaluation, types "
		   ^ty2s s1^" and "^ty2s s2^" are incompatible") 
      else return (Is(t1,t2)))))
  | Cut -> return Cut
  | True -> return True
  | False -> return False
  | And(t1,t2)| Pair(t1,t2) -> 
      check_goal t1 >>= fun g1 -> 
      check_goal t2 >>= fun g2 -> 
      return (And (g1, g2))
  | Or(t1,t2) -> 
      check_goal t1 >>= fun g1 -> 
      check_goal t2 >>= fun g2 -> 
      return (Or (g1,g2))
  | Implies(t1,t2) -> 
      if !Flags.horn_clauses_only || !Flags.new_goal_only 
      then tcfail ("term "^t2s goal^" is not a well-formed goal")
      else check_prog t1 >>= fun p1 ->
      check_goal t2 >>= fun g2 ->
      return (Implies(p1,g2))
  | Guard (t1,t2,t3) -> 
      check_goal t1 >>= fun g1 -> 
      check_goal t2 >>= fun g2 -> 
      check_goal t3 >>= fun g3 -> 
      return (Guard (g1,g2,g3))
  | Not(t) -> check_goal t >>= fun g -> 
      return (Not(g))
  | Forall(v,s,t) -> 
      if !Flags.horn_clauses_only || !Flags.new_goal_only 
      then tcfail ("term "^t2s goal^" is not a well-formed goal")
      else 
	check_quantifier check_goal v s t TypeKd >>= fun (x,ty,g) ->
	return (Forall(x,ty,g))
  | Exists(v,s,t) -> 
      check_quantifier check_goal v s t TypeKd >>= fun (x,ty,g) ->
      return (Exists(x,ty,g))
  | New(v,s,t) -> 
      check_quantifier check_goal v s t NameKd >>= fun (x,ty,g) ->
      return (New(x,ty,g))
  | Var v -> 
      if !Flags.forbid_prop 
      then tcfail ("term "^t2s (Var v)^" is not a well-formed goal")
      else check_term (Var v) PropTy
  | g -> tcfail ("term "^t2s g^" is not a well-formed goal")
;;

(* TODO: How to handle type inference here? *)
let rec check_hyp hyp = 
  match hyp with
    Atomic(path,ts) -> 
      using (fun sg -> 
      let (entry,sym) = lookup_sg (sg.tsg) path in
      let ty = freshen entry.sym_ty in
      check_ty ty false TypeKd >>= fun ty -> 
      let vs = ftvs ty in
      update vsF (Varset.union vs) >>
      infer_list_ty sym ts ty >>= fun (tms,ty) -> 
	(match ty with 
	  PropTy -> return (Atomic(N.Root(sym), tms))
	| ty -> incompatible ty PropTy
	))
  | And(t1,t2)|Pair(t1,t2) -> 
      check_hyp t1 >>= fun h1 -> 
      check_hyp t2 >>= fun h2 -> 
      return (And(h1,h2))
  | Fresh(_,t1,t2) -> 
      infer_term t1 >>= fun (t1',nty) -> 
      let _ = check_ty nty true NameKd in
      infer_term t2 >>= fun (t2',ty) -> 
      (match t1' with
	Name _ | Var _ | Transpose _ -> return (Fresh (Some (nty,ty),t1',t2')) 
	    (* TODO: Do check that transpose eventually around a var. *)
      | _ -> tcfail "left side of # must be a name or variable")
  | Eq(_,t1,t2) -> 
      infer_term t1 >>= (fun (t1,s1) -> 
      infer_term t2 >>= (fun (t2,s2) -> 
      check_ty_eq s1 s2 >>= (fun b -> 
      if not b 
      then tcfail ("in equality test, types "
		   ^ty2s s1^" and "^ty2s s2^" are incompatible") 
      else return (Eq(Some s1,t1,t2)))))
  | Exists(v,s,t) -> 
      check_quantifier check_hyp v s t TypeKd >>= fun (x,ty,h) ->
      return (Exists(x,ty,h))
  | New(v,s,t) -> 
      check_quantifier check_hyp v s t NameKd >>= fun (x,ty,h) ->
      return (New(x,ty,h))
  | True -> return True
  | _ -> tcfail "Not a well-formed hypothesis"
;;


let rec check_test test = 
  match test with
    Atomic(path,ts) -> 
      using (fun sg -> 
      let (entry,sym) = lookup_sg (sg.tsg) path in
      let ty = freshen entry.sym_ty in
      check_ty ty false TypeKd >>= fun ty -> 
      let vs = ftvs ty in
      update vsF (Varset.union vs) >>
      infer_list_ty sym ts ty >>= fun (tms,ty) -> 
	(match ty with 
	  PropTy -> return (Atomic(N.Root(sym), tms))
	| ty -> incompatible ty PropTy
	))
  | Fresh(_,t1,t2) -> 
      infer_term t1 >>= fun (t1',nty) -> 
      let _ = check_ty nty true NameKd in
      infer_term t2 >>= fun (t2',ty) -> 
      (match t1' with
	Name _ | Var _ | Transpose _ -> return (Fresh (Some(nty,ty),t1',t2')) 
	    (* TODO: Do check that transpose eventually around a var. *)
      | _ -> tcfail "left side of # must be a name or variable")
  | Eq(_,t1,t2) -> 
      infer_term t1 >>= (fun (t1,s1) -> 
      infer_term t2 >>= (fun (t2,s2) -> 
      check_ty_eq s1 s2 >>= (fun b -> 
      if not b 
      then tcfail ("in equality test, types "
		   ^ty2s s1^" and "^ty2s s2^" are incompatible") 
      else return (Eq(Some s1,t1,t2)))))
  | Implies(p1,p2) -> 
      check_hyp p1 >>= fun h1 ->
      check_test p2 >>= fun t2 ->
      return (Implies(h1,t2))
  | Forall(v,s,t) -> 
      check_quantifier check_test v s t TypeKd >>= fun (x,ty,g) ->
      return (Forall(x,ty,g))
  | New(v,s,t) -> 
      check_quantifier check_test v s t NameKd >>= fun (x,ty,g) ->
      return (New(x,ty,g))
  | True -> return True
  | False -> return False
  | _ -> tcfail "Not a well-formed test"
      
;;



(*
let safe_negation_as_failure goal = 
  get_state >>= (fun ctx -> 
    let vs = Varset.elements (fvs goal) in
    (* look up the types and add "gen_type" predicates for the free variables *) 
    let goals = List.fold_left (fun g v -> 
      And(g, Negelim.call_term_generator(Varmap.find v ctx) (Var v))) 
	True  vs in
    return (And(goals,Not(goal))))
  ;;

let negation_elimination goal = 
  return (Negelim.negate_goal goal)
;;
*)

exception Success of  Isym.ty_sym Explain.answer;;

let unify_eqns = 
  using (fun sg -> 
   get eqnsF >>= fun eqns -> 
   get vsF >>= fun vs -> 
   get_state >>= fun tcenv -> 
   let eqns' = 
     List.map (fun (a,t) -> 
       Translate.translate_ty sg tcenv (VarTy a),
       Translate.translate_ty sg tcenv t) eqns in
   let sc ans = raise (Success ans) in
   try 
     let msg = Explain.explains Isym.pp_ty_sym Isym.ty_sym_eq  eqns' sc (Subst.id,[]) in
     tcfail (msg)
   with Success ans -> 
     let (subst,_) = ans in 
     return subst)
;;

let check_subst_ty subst : (sg,tcenv,unit) scmonad = 
  let l = Subst.to_list subst in 
  iter (fun (x,t) -> 
    using (fun sg -> 
      get_state >>= fun (tcenv:tcenv) -> 
      let s = Translate.untranslate_ty sg tcenv t in 
      get tctxF >>= fun (tctx:tctx) -> 
      let k = 
	try Varmap.find x tctx 
	with Not_found -> 
	  print_string ("Warning: No kind for "^Var.to_string' x^", assuming Type\n");
	  TypeKd
      in
      check_ty s true k >> 
      return ()))
    l
;;

let subst_to_map subst : (ty Varmap.t) tcm = 
  let l = Subst.to_list subst in 
  using (fun sg -> 
    get_state >>= fun (tcenv) -> 
    let l = List.map (fun (x,_) -> 
      let Some t = (Subst.finish subst x) in 
      (x,Translate.untranslate_ty sg tcenv t)) l 
    in 
    let m = List.fold_left (fun m (x,t) -> Varmap.add x t m) Varmap.empty l in
    return m)
;;

let apply_tysub_ctx m = Varmap.map (function VarS ty -> VarS (Absyn.apply_tysub m ty)
                                            | NameS ty -> NameS(Absyn.apply_tysub m ty))

let infer_term t = 
  get sgF >>= fun sg -> 
  infer_term t >>= fun (t',ty) -> 
  unify_eqns >>= fun subst -> 
  check_subst_ty subst >>
  subst_to_map subst >>= fun m -> 
  update ctxF (apply_tysub_ctx m) >>
  return (t',Absyn.apply_tysub m ty)


let check_prog t = 
  get sgF >>= fun sg -> 
  check_prog t >>= fun p -> 
  unify_eqns >>= fun subst ->
  check_subst_ty subst >>
  subst_to_map subst >>= fun m -> 
  update ctxF (apply_tysub_ctx m) >>
  return (Absyn.apply_tysub_term m p)
;;


let check_goal t = 
  get sgF >>= fun sg -> 
  check_goal t >>= fun g -> 
  unify_eqns >>= fun subst ->
  check_subst_ty subst >>
  subst_to_map subst >>= fun m -> 
  update ctxF (apply_tysub_ctx m) >>
  return (Absyn.apply_tysub_term m g)
;;

let check_hyp t = 
  get sgF >>= fun sg -> 
  check_hyp t >>= fun p -> 
  unify_eqns >>= fun subst ->
  check_subst_ty subst >>
  subst_to_map subst >>= fun m -> 
  update ctxF (apply_tysub_ctx m) >>
  return (Absyn.apply_tysub_term m p)
;;


let check_test t = 
  get sgF >>= fun sg -> 
  check_test t >>= fun g -> 
  unify_eqns >>= fun subst ->
  check_subst_ty subst >>
  subst_to_map subst >>= fun m -> 
  update ctxF (apply_tysub_ctx m) >>
  return (Absyn.apply_tysub_term m g)
;;

