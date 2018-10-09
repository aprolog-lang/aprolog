open Absyn;;
open Tcenv;;
open Nstbl;;
open Types;;
module I = Internal;;

let call_goal p = Atomic(Rel(Base("call")),[p]);;

let exists ty f = 
  let v = Var.mkvar "X" in
  Exists (v,ty,f(Var v))
;;

let forall ty f = 
  let v = Var.mkvar "X" in
  Forall (v,ty,f(Var v))
;;
let lambda ty f = 
  let v = Var.mkvar "X" in
  Lambda (v,ty,f(Var v))
;;


let new_quant nty f = 
  let a = Var.mkvar "a" in
  New (a,nty,f(Name a))
;;

let forall_quantifys = 
  List.fold_right (fun (x,ty) g -> Forall(x,UnderscoreTy,g));;
let exists_quantifys = 
  List.fold_right (fun (x,ty) g -> Exists(x,UnderscoreTy,g));;
let and_list = List.fold_left (fun g h -> And(g,h)) True;;


let make_pred_decl sym tys = 
    {pos=None;rdecl=PredDecl(sym, tys,false,false )};;
let make_abbrev_decl sym tys = 
    {pos=None;rdecl=PredDecl(sym, tys,false,true )};;
let make_clause_decl term = 
    {pos=None;rdecl=ClauseDecl(term)};;

let rec remove_duplicates(l) = 
  match l with
    [] -> []
  | ty::tys -> if List.mem ty tys then remove_duplicates(tys) else ty::remove_duplicates(tys)
;;


let get_list_types sg = 
  let rec list_types ty = 
    match ty with 
    | UnderscoreTy | VarTy _ | IdTy _ | NameTy _ | UnitTy | IntTy | CharTy | BoolTy | PropTy -> []
    | DataTy (_,tys) -> List.concat (List.map list_types tys)
    | PairTy (ty1,ty2) | AbsTy (ty1,ty2) | ArrowTy(ty1,ty2) ->
	list_types ty1 @ list_types ty2
    | ListTy ty -> (ListTy ty)::list_types(ty)
  in 
  let tdecls = !(sg.tdecls) in
  let types = List.concat (List.map (fun (sym,ty) -> list_types ty) tdecls) in
  remove_duplicates(types)
;;

let get_datatype_syms sg = 
  let decls = !(sg.kdecls) in
  let decls' = List.filter (fun (sym,kind) -> kind = TypeK) decls in
  List.map (fun (sym,_) -> sym) decls'
;;

let get_nametype_syms sg = 
  let decls = !(sg.kdecls) in
  let decls' = List.filter (fun (sym,kind) -> kind = NameK) decls in
  List.map (fun (sym,_) -> sym) decls'
;;


let rec rename_sym prefix sym = 
  match sym with
    Child(s,sym) -> Child(s,rename_sym prefix sym)
  | Base(s) -> Base( prefix^s)
;;




(* Get the function declarations defining each type, grouped by type name *)
let get_constructors sg dtys = 
  let rec ty_match dty ty = 
    match ty with
      DataTy(Root(dty'),[]) -> dty = dty'
    | ArrowTy(_,ty') -> ty_match dty ty'
    | _ -> false in
  let rec flatten_ty ty = 
    match ty with
      ArrowTy(ty,ty') -> ty::flatten_ty ty'
    | _ -> []
  in   
  let decls = !(sg.tdecls) in
  let collect dty = 
    Util.map_partial 
      (fun (sym,ty) -> 
	if ty_match dty ty then Some (sym,flatten_ty ty) else None) 
      decls in
  List.map (fun dty -> (dty, collect dty)) dtys
;;




(* Generates patterns which complement a given pattern *)


(* Generates subgoal gen[[ty]](X) with f used to name the recursive calls *)



let rec termgen (gen_f: Types.ty -> Nstbl.sym) ty vX = 
  match ty with
    NameTy nty -> True
  | BoolTy -> Or(Eq(Some BoolTy, vX,BoolC true),
		 Eq(Some BoolTy, vX,BoolC false))
  | IntTy|CharTy -> True
  | UnitTy -> Eq(None,vX,Unit)
  | PairTy(t1,t2) -> 
      exists t1 (fun vX1 -> 
        exists t2 (fun vX2 -> 
          And(Eq(None,vX,Pair(vX1,vX2)),
              And(termgen gen_f  t1 vX1, termgen gen_f  t2 vX2))))
  | AbsTy(nty,ty) -> 
      new_quant nty (fun nA -> 
        match nA with
	  Name nm -> termgen gen_f ty (Conc(vX, nm))
	| _ -> raise (Util.Impos "generate_term"))
  | DataTy(Root(ds),[]) -> Atomic(Root(gen_f ty),[vX])
  | ListTy _ -> Atomic(Root(gen_f ty),[vX])
  | _ -> Util.impos ("termgen: impossible type "^(ty2s ty))
;;

(* Generates gen[[ty1...tyn]](X1,...,Xn) for a list of types and terms *)
let rec termgens gen_f tys vXs = 
  match tys,vXs with 
    [],[] -> True
  | [ty],[vX] -> termgen gen_f  ty vX
  | ty::tys,vX::vXs -> And(termgen gen_f  ty vX,  termgens gen_f tys vXs)
  | _ -> Util.impos "termgens"
;;



(* not being careful about namespaces *)
let rec ty_symbol ty =
  match ty with 
    NameTy (Root(n)) -> get_base n
  | DataTy (Root(d),[]) -> get_base d
  | UnitTy -> "unit"
  | PairTy (ty1,ty2) -> "pair_X_"^ty_symbol ty1^"_Y_"^ty_symbol ty2^"_Z"
  | AbsTy (ty1,ty2) -> "abs_X_"^ty_symbol ty1^"_Y_"^ty_symbol ty2^"_Z"
  | ArrowTy (ty1,ty2) -> "fun_X_"^ty_symbol ty1^"_Y_"^ty_symbol ty2^"_Z"
  | ListTy ty -> "list_X_"^ty_symbol ty^"_Z"
  | IntTy -> "int"
  | BoolTy -> "bool"
  | CharTy -> "char"
  | PropTy -> "prop"
  | _ -> raise (Util.Impos ("ty_symbol undefined for "^ty2s ty))

let rename_type prefix ty = 
  Base(prefix^ty_symbol ty)

let rename_termgen = rename_sym "gen_";;

let call_term_generator ty tm = termgen (rename_type "gen_") ty tm;;


let generate_terms sg = 
  let make_gen_decl dty = 
    make_pred_decl (get_base (rename_termgen dty)) [DataTy(Root(dty),[])] in
  let make_gen_clause (dty,constrs) = 
    List.map 
      (fun (fsym,tys) -> 
	let vXs = List.map (fun _ -> Var (Var.mkvar "X")) tys in 
	make_clause_decl 
	  (Implies(termgens (rename_type "gen_") tys vXs, 
		   Atomic(Root(rename_termgen dty),
			  [Atomic(Root(fsym),vXs)]))))  constrs
  in
  let dtys = get_datatype_syms sg in
  let decls : Absyn.decl list = List.map make_gen_decl dtys in
  let cons = get_constructors sg dtys in 
  let clauses : Absyn.decl list= List.concat (List.map make_gen_clause cons) in 

(* Handle lists *)
  let make_list_gen_decl lty = 
    make_pred_decl (get_base (rename_type "gen_" lty)) [lty] in
  let make_list_gen_clause (ListTy ty) =
    let vX = Var(Var.mkvar "X") in 
    let vY = Var(Var.mkvar "Y") in 
    let predname = Root(rename_type "gen_" (ListTy ty)) in 
    List.map make_clause_decl 
      [Atomic(predname,[Nil]);
	Implies(termgens (rename_type "gen_") [ty;ListTy ty] [vX;vY],
		Atomic(predname,[Cons(vX,vY)]))]
  in
  let ltys = get_list_types sg in
  let decls' = List.map make_list_gen_decl ltys in
  let clauses' = List.concat (List.map make_list_gen_clause ltys) in 
  
  decls @ decls' @ clauses @ clauses'
;;

(* Given a test, it returns the pair hypothesis,conclusion *)
let get_hyps_cls = function 
    Implies(hyps,cls) -> hyps,cls
  | cls -> True,cls

(* Given a test conclusion, it return the generators needed to make
   ground all its free variables *)
let get_gens tcenv g =
  let vXs = Varset.elements (fvs g) in
  let tys = List.map (fun var -> lookup_env var tcenv) vXs in
  let tms = List.map (fun var -> Var var) vXs in
  termgens (rename_type "gen_") tys tms 

(* Given an And(t1,t2) and a function f, it return the And expression 
   with the f applied on the rightest term in the And's AST *)
let rec and_append f = function
    And(h1,h2) -> And(h1,and_append f h2)
  | a -> f a

(* Given a predicate name |pred| and a signature |sg|, 
it returns the number of clauses that define |pred| *)
let count_clauses sg pred =
  let rec count pred clause =
  match clause with
    True -> 0
  | Atomic(Root(sym),_) | Atomic(Rel(sym),_) when sym = pred -> 1
  | Forall(_,_,h) | New(_,_,h) -> count pred h
  | Implies(g,h) -> count pred h
  | And(g1,g2) -> (count pred g1) + (count pred g2)
  | _ -> 0 in
  (* let res = *) List.fold_left (fun prev clause -> prev + count pred clause) 0 !(sg.clauses) (* in *)
  (* print_endline ("pred " ^ (ns2s pred) ^  " is defined by " ^ (string_of_int res) ^  " clauses"); *)
  (* res *)

let sort_gens sg gens =
  let rec helper gens =
    match gens with 
    Atomic(Root(sym),_) | Atomic(Rel(sym),_) -> [(count_clauses sg sym,gens)]
  | And(gen,gens) -> (helper gen) @ (helper gens)
  | _ -> []
  in
  let sorted_list = List.stable_sort
    (fun (n1,gen1) (n2,gen2) -> compare n1 n2)
    (helper gens) in
  and_list (List.map (fun (_,gen) -> gen) sorted_list)
  
(* Given a test, it adds the generators needed to make ground every free 
   vars in the conclusion *)
let add_generators sg tcenv test =
  let hyps,cls = get_hyps_cls test in
  let gens = get_gens tcenv cls in
  let gens' = sort_gens sg gens in
  let hyps' = and_append (fun last -> And(last,gens')) hyps in
  Implies(hyps',cls)


let rename_neq = rename_sym "neq_";;

let rename_fresh = rename_sym "fresh_";;
  
let rec neq_call ty tX tY = 
  match ty with
    NameTy (Root sym) -> Atomic(Root(rename_fresh sym),[Pair(tX,tY)])
  | UnitTy -> False
  | IntTy| BoolTy | CharTy -> False (* TODO: Fix *)
  | PairTy(t1,t2) -> 
      exists t1 (fun vX1 -> 
        exists t1 (fun vY1 -> 
          exists t2 (fun vX2 -> 
            exists t2 (fun vY2 -> 
	      And(Eq(None,tX,Pair(vX1,vX2)),
		  And(Eq(None,tY,Pair(vY1,vY2)),
		      Or(neq_call t1 vX1 vY1,
			   neq_call t2 vX2 vY2)))))))
  | AbsTy(nty,ty) -> 
      new_quant nty 
	(fun nA -> 
          match nA  with
	    Name nm -> neq_call ty (Conc (tX, nm)) (Conc (tY, nm))
	  | _ -> raise (Util.Impos "generate_neq"))
  | DataTy(Root(ds),[]) -> Atomic(Root(rename_neq ds),[Pair(tX,tY)])
  | ListTy _ -> Atomic(Root(rename_type "neq_" ty),[Pair(tX,tY)])
  | _ -> Util.impos ("neq: unhandled type "^ty2s ty)
;;


let rec neq_calls tys vXs vYs = 
  match tys,vXs,vYs with 
    [],[],[] -> False
  | [ty],[vX],[vY] -> neq_call ty vX vY
  | ty::tys,vX::vXs,vY::vYs -> Or(neq_call ty vX vY,  neq_calls tys vXs vYs) 
  | _ -> Util.impos "neqs"
;;


let generate_neqs sg = 
  let make_neq_decl dty = 
    make_pred_decl (get_base (rename_neq dty)) 
      [PairTy(DataTy(Root(dty),[]),DataTy(Root(dty),[]))] in
  let make_neq_clause dty ((s,tys),(t,tys')) = 
    if s = t 
    then 
      let vXs = List.map (fun _ -> Var (Var.mkvar "X")) tys in 
      let vYs = List.map (fun _ -> Var (Var.mkvar "Y")) tys in 
      make_clause_decl
	(Implies(neq_calls tys vXs vYs, 
		 Atomic(Root(rename_neq dty),
			[Pair(Atomic(Root(s),vXs),Atomic(Root(s),vYs))])))
    else 
      make_clause_decl
	(Atomic(Root(rename_neq dty),
	     [Pair(Atomic(Root(s),
			  List.map (fun _ -> Underscore) tys),
		   Atomic(Root(t),List.map (fun _ -> Underscore) tys'))]))
  in 
  let make_neq_clauses (dty,clauses) = 
    let clausepairs = Util.allpairs clauses clauses in 
    List.map (make_neq_clause dty) clausepairs  
  in 
  let dtys = get_datatype_syms sg in
  let decls = List.map make_neq_decl dtys in
  let cons = get_constructors sg dtys in 
  let clauses = List.concat (List.map make_neq_clauses cons) in 
(* Handle lists *)
  let make_list_neq_decl lty = 
    make_pred_decl (get_base (rename_type "neq_" lty)) [PairTy(lty,lty)] in
  let make_list_neq_clause (ListTy ty) =
    let vX1 = Var(Var.mkvar "X1") in 
    let vX2 = Var(Var.mkvar "X2") in 
    let vY1 = Var(Var.mkvar "Y1") in 
    let vY2 = Var(Var.mkvar "Y2") in 
    let predname = Root(rename_type "neq_" (ListTy ty)) in 
    List.map make_clause_decl 
      [Atomic(predname,[Pair(Nil,Cons(Underscore,Underscore))]);
	Atomic(predname,[Pair(Cons(Underscore,Underscore),Nil)]);
	Implies(neq_calls [ty;ListTy ty] [vX1;vX2] [vY1;vY2],
		Atomic(predname,[Pair(Cons(vX1,vX2),Cons(vY1,vY2))]))]
  in
  let ltys = get_list_types sg in
  let decls' = List.map make_list_neq_decl ltys in
  let clauses' = List.concat (List.map make_list_neq_clause ltys) in 
  decls @ decls' @ clauses @ clauses'
;;

let rename_eq = rename_sym "eq_";;
  
let rec nfresh_call f nty ty vX vY = 
  match ty with
  | NameTy (Root nty') ->
     if nty = nty' then Atomic(Root(rename_eq nty),[Pair(vX,vY)])
     else False
  | UnitTy -> False
  | IntTy| BoolTy | CharTy -> False
  | PairTy(t1,t2) -> 
      exists t1 (fun vY1 -> 
        exists t2 (fun vY2 -> 
          And(Eq(None,vY,Pair(vY1,vY2)),
              Or(nfresh_call f nty t1 vX vY1,
		 nfresh_call f nty t2 vX vY2))))
  | AbsTy(nty',ty) -> 
      new_quant nty' (fun nA -> 
        match nA with
	  Name nm -> nfresh_call f nty ty vX (Conc(vY, nm))
	| _ -> raise (Util.Impos "generate_nfresh"))
  | DataTy(Root(ds),[]) -> Atomic(Root(f nty ty),[Pair(vX,vY)])
  | ListTy _ -> Atomic(Root(f nty ty),[Pair(vX,vY)])
  | ty -> Util.impos ("nfresh: unhandled type " ^ ty2s ty)
;;


let rec nfresh_calls f nty tys vX vYs = 
  match tys,vYs with 
    [],[] -> False
  | [ty],[vY] -> nfresh_call f nty ty vX vY
  | ty::tys,vY::vYs -> Or(nfresh_call f nty ty vX vY,  nfresh_calls f nty tys vX vYs) 
  | _ -> Util.impos "nfresh_calls"
;;


let rename_nfresh nty ty = Base("nfresh_"^(get_base nty)^"_"^(ty_symbol ty)) ;;

let generate_nfreshs sg =
  let make_nfresh_decl (nty, dty) = 
    make_pred_decl (get_base (rename_nfresh nty (DataTy(Root(dty),[]))))
      [PairTy(NameTy(Root(nty)),DataTy(Root(dty),[]))] in
  let make_nfresh_clause (nty,(dty,constrs)) = 
   let vX = Var(Var.mkvar("X")) in 
   List.map 
      (fun (sym,tys) -> 
	let vYs = List.map (fun _ -> Var (Var.mkvar "Y")) tys in 
	make_clause_decl
	  (Implies(nfresh_calls rename_nfresh nty tys vX vYs, 
		   Atomic(Root(rename_nfresh nty (DataTy(Root(dty),[]))),
			  [Pair(vX,Atomic(Root(sym),vYs))])))) constrs
  in
  let dtys = get_datatype_syms sg in
  let ntys = get_nametype_syms sg in 
  let decls = List.map make_nfresh_decl (Util.allpairs ntys dtys) in
  let cons = get_constructors sg dtys in 
  let clauses =
    List.concat 
      (List.map make_nfresh_clause (Util.allpairs ntys cons)) in 
(* handle list cases *)
  let make_list_nfresh_decl (nty,lty) = 
    make_pred_decl (get_base (rename_nfresh nty lty)) [PairTy(NameTy (Root nty),lty)] in
  let make_list_nfresh_clause (nty,ListTy ty) =
    let vX = Var(Var.mkvar "X") in 
    let vY1 = Var(Var.mkvar "Y1") in 
    let vY2 = Var(Var.mkvar "Y2") in 
    let predname = Root(rename_nfresh nty (ListTy ty)) in 
    [make_clause_decl 
      (Implies(nfresh_calls rename_nfresh nty [ty;ListTy ty] vX [vY1;vY2],
		Atomic(predname,[Pair(vX,Cons(vY1,vY2))])))]
  in
  let ltys = get_list_types sg in
  let nltys =  (Util.allpairs ntys ltys) in
  let decls' = List.map make_list_nfresh_decl nltys in
  let clauses' = List.concat (List.map make_list_nfresh_clause nltys) in 

  decls @ decls' @ clauses @ clauses'
;;

let generate_freshs sg =
  let make_fresh_decl nty =
    let nT = NameTy(Root(nty)) in
    make_pred_decl (get_base (rename_fresh nty)) [PairTy(nT,nT)] in
  let make_fresh_clause nty = 
    let vX = Var(Var.mkvar("X")) in
    let vY = Var(Var.mkvar("Y")) in
    let nT = NameTy(Root(nty)) in
    make_clause_decl (Implies(Fresh(Some(nT,nT),vX,vY),Atomic(Root(rename_fresh nty),[Pair(vX,vY)])))
  in
  let ntys = get_nametype_syms sg in 
  let decls = List.map make_fresh_decl ntys in
  let clauses = List.map make_fresh_clause ntys in
  decls @ clauses

let generate_eqs sg =
  let make_eq_decl nty =
    let nT = NameTy(Root(nty)) in
    make_pred_decl (get_base (rename_eq nty)) [PairTy(nT,nT)] in
  let make_eq_clause nty = 
    let vX = Var(Var.mkvar("X")) in
    let vY = Var(Var.mkvar("Y")) in
    let nT = NameTy(Root(nty)) in
    make_clause_decl (Implies(Eq(Some(nT),vX,vY),Atomic(Root(rename_eq nty),[Pair(vX,vY)])))
  in
  let ntys = get_nametype_syms sg in 
  let decls = List.map make_eq_decl ntys in
  let clauses = List.map make_eq_clause ntys in
  decls @ clauses

            
(* Generates subgoal forallstar[[ty]](P)  *)

let rename_forallstar = rename_sym "forallstar_";;

let rec forallstar ty vP = 
  match ty with
    NameTy _ |IntTy|CharTy -> forall ty (fun vX -> call_goal(App(vP,vX)))
  | BoolTy -> And(App(vP,BoolC true),
		  App(vP,BoolC false))
  | UnitTy -> App(vP,Unit)
  | PairTy(t1,t2) -> 
      forallstar t1 (lambda t1 (fun vX1 -> 
      forallstar t2 (lambda t2 (fun vX2 -> 
      App(vP,Pair(vX1,vX2))))))
  | AbsTy(nty,ty) -> 
      new_quant nty (fun nA -> 
        match nA with
	  Name nm -> forallstar ty (lambda ty (fun vX -> App(vP,Abs(nm,vX))))
	| _ -> raise (Util.Impos "generate_forallstar"))
  | DataTy(Root(ds),[]) -> Atomic(Root(rename_forallstar ds),[vP])
  | _ -> Util.impos ("forallstar: impossible type "^(ty2s ty))
;;

(* Generates gen[[ty1...tyn]](P) for a list of types and P : ty1 -> ... tyn -> o *)
let rec forallstars tys vP = 
  match tys with 
    [] -> vP
  | ty::tys -> forallstar ty (lambda ty (fun vX -> forallstars tys (App(vP,vX))))
;;



let generate_forallstars sg = 
  let make_forallstar_decl dty = 
    make_pred_decl (get_base (rename_forallstar dty)) [ArrowTy(DataTy(Root(dty),[]),PropTy)] in
  let make_forallstar_clauses (dty,constrs) = 
    let vP = Var(Var.mkvar "P") in
    let forallstar_clause1 = 
      make_clause_decl 
	    (Implies(forall (DataTy(Root(dty),[])) 
		       (fun vX -> call_goal(App(vP,vX))),
	      Atomic(Root(rename_forallstar dty),[vP]))) in
    let goals = (* TODO generalize *)
      List.map 
	(fun (fsym,tys) -> 
	  match tys with
	    [] -> call_goal(App(vP,Atomic(Root(fsym),[])))
	  | [ty] -> forallstar ty (lambda ty (fun vX -> call_goal(App(vP,Atomic(Root(fsym),[vX])))))
	  | _ -> Util.nyi())
	constrs
    in 
    let forallstar_clause2 = 
      make_clause_decl 
	    (Implies(and_list goals, Atomic(Root(rename_forallstar dty),[vP]))) in
    [forallstar_clause1;forallstar_clause2] in
  let dtys = get_datatype_syms sg in
  let decls = List.map make_forallstar_decl dtys in
  let cons = get_constructors sg dtys in 
  let clauses = List.concat (List.map make_forallstar_clauses cons) in 
  decls @ clauses
;;


(* Pattern complement *)


let pattern_complement_maker dtys constrs = 
  let rec compl pat ty = 
    match pat,ty with
      Underscore,_|Var(_),_ -> []
    | Pair(p1,p2),PairTy(ty1,ty2) -> 
	let p1comp = compl p1 ty1 in
	let p2comp = compl p2 ty2 in
	List.map (fun p -> Pair(p,Underscore)) p1comp @
	List.map (fun p -> Pair(Underscore,p)) p2comp
    | Unit,UnitTy -> []
    | Atomic(Root(f),ts),DataTy(Root(dty),[]) -> 
	let compl_atomic (g,tys) =
	  if f = g 
	  then List.map (fun ps -> Atomic(Root(f),ps)) (compls ts tys)
	  else [Atomic(Root(g),List.map (fun _ -> Underscore) tys)] in
	let (_,cons) = List.find (fun (dty',_) -> dty = dty') constrs in
	Util.collect compl_atomic cons
    | Nil, ListTy _ -> [Cons(Underscore,Underscore)]
    | Cons(p1,p2), ListTy ty -> 
	[Nil] @
	List.map (fun p -> Cons(p,Underscore)) (compl p1 ty) @
	List.map (fun p -> Cons(Underscore,p)) (compl p2 (ListTy ty))
    | _ -> Util.impos ("pattern_complement: unhandled  " ^ t2s pat ^ " : "^ty2s ty)
  and compls pats tys = 
    match pats, tys with
      [], [] -> []
    | pat'::pats',ty'::tys' -> 
	let pcomp = compl pat' ty' in 
	let pcomps = compls pats' tys' in
	List.map (fun p -> p::(List.map (fun _ -> Underscore) tys')) pcomp @
	List.map (fun ps -> Underscore::ps) pcomps
    | _ -> Util.impos "pattern_complement: type and argument list mismatch"
  in compl,compls
;;


let pattern_complement sg pat ty = 
  let dtys = get_datatype_syms sg in
  let constrs = get_constructors sg dtys in
  let (compl,_) = pattern_complement_maker dtys constrs in
  compl pat ty
;;

let pattern_complements sg pats tys = 
  let dtys = get_datatype_syms sg in
  let constrs = get_constructors sg dtys in
  let (_,compls) = pattern_complement_maker dtys constrs in
  compls pats tys
;;


(* Negation elimination *)

let rename_not = rename_sym "not_";;

let message msg = if !Flags.linearize then Util.error msg else Util.warning msg;;


let rec get_clauses p vs sg clause = 
  match clause with
    Implies(g,h) -> get_clauses p vs (And (sg,g)) h 
  | Forall(x,ty,h) -> get_clauses p ((x,ty)::vs) sg h
  | Atomic(Root(sym),ts) -> 
      if p = sym 
      then (
	if not (is_linear clause)
	then message ("Definition of "^ns2s p^" is nonlinear");
	if not (is_firstorder clause) 
	then message ("Definition of "^ns2s p^" uses names, abstraction or concretion which are not supported by negation elimination");
        [(vs,ts,sg)] 
	  )
      else [] 
  | And(g1,g2) -> get_clauses p vs sg g1 @ get_clauses p vs sg g2
  | New(a,ty,h) -> get_clauses p vs sg h
  | True -> []
  | Eq(_,_,_) -> []  (*TODO: Negation of defined clauses?? *)
  | _ -> Util.impos "get_clauses: impossible program clause"
;;



let rec negate_goal g = 
  match g with
    True -> False
  | False -> True
  | And(g1,g2) -> Or(negate_goal g1, negate_goal g2)
  | Or(g1,g2) -> And(negate_goal g1, negate_goal g2)
  | New(a,ty,g) -> New(a,ty,negate_goal g)
  | Exists(x,ty,g) ->  Forall(x,ty,negate_goal g) 
(*	  forallstar ty (Lambda(x,ty, negate_goal g))*)
  | Atomic(Root(sym),ts) -> Atomic(Root(rename_not sym),ts)
  | Atomic(Rel(sym),ts) -> Atomic(Rel(rename_not sym),ts)
  | Eq(Some(ty),t1,t2) -> neq_call ty t1 t2
  | Eq(None,_,_) -> failwith "not yet handled"
  | Fresh(Some(NameTy(Root(nty)),ty),t1,t2) -> nfresh_call rename_nfresh nty ty t1 t2
  | Guard(g,g1,g2) -> And(Or(negate_goal g, negate_goal g1),Or(g,negate_goal g2))
  | _ -> Util.impos "generate_not"
;;

let rec negate_test = function
  | Implies(h,g) -> Implies(h,negate_goal g)
  | g -> negate_goal g                    
;;

let check_well_quantified clauses = 
  let check_well_quantified clause = 
    if not (is_well_quantified clause) 
    then message ("The clause "^t2s clause^" is not well-quantified, as required by negation elimination")
  in 
  List.iter check_well_quantified clauses
;;
  
let useful_clause clause =
  match clause.rdecl with
    ClauseDecl(True) -> false
  | _ -> true
;;  

let print_sub sub =
  print_string " unify res: ";
  Printer.print_to_channel (Varmap.pp_map pp_term) sub stdout
;;		     
			   
let unify_term_pair (t1,t2) =
  let t1' = freshen_fvs t1 |> fill_holes in
  let t2' = freshen_fvs t2 |> fill_holes in
  (if !Flags.debug then
       (Printer.print_to_channel pp_term t1' stdout;
     	print_string " @ ";
     	Printer.print_to_channel pp_term t2' stdout));
  match t1',t2' with
  | Implies(g1,h1),Implies(g2,h2) ->
     (match unify_linear h1 h2 with
	Some(sub) -> if !Flags.debug then print_sub sub;
		     Some (apply_tmsub sub (Implies(And(g1,g2),h1)))
      | None -> None)
  | atom, Implies(g,h) | Implies(g,h), atom ->
     (match unify_linear atom h with
	Some(sub) -> if !Flags.debug then print_sub sub;
		     Some (apply_tmsub sub (Implies(g,h)))
      | None -> None)
  | atom1, atom2 ->
     (match unify_linear atom1 atom2 with
       Some(sub) -> if !Flags.debug then print_sub sub; Some (apply_tmsub sub atom1)
      | None -> None)       
;;
		
let unify_clause_pair (c1,c2) =
  match (c1.rdecl,c2.rdecl) with
    ClauseDecl(t1),ClauseDecl(t2) ->
    match unify_term_pair (t1,t2) with
      Some t -> Some {pos=None;rdecl=ClauseDecl t}
    | None -> None
;;	       

exception Success						
exception Failure

let empty_index = Index.create 1			     

(* type stats = {tot_cls: int; sub_cls: int} *)

let sub_counter = ref 0

let reset_sub_counter () = sub_counter := 0                    
                    
(* let init_stats () = ref {tot_cls = 0; sub_cls = 0} *)

let incr_sub_counter () = sub_counter := !sub_counter + 1

let unwrap_clause clause =
  match clause.rdecl with
    ClauseDecl(term) -> term
  
exception Not_equivalent of string

(* TODO: I'm not sure about = *)
let are_equiv_ty ty1 ty2 =
  let rec h (type1,type2) var_ctx =
    match type1,type2 with
    | VarTy(x),VarTy(y) ->
      if Varmap.mem x var_ctx then
        if Var.eq (Varmap.find x var_ctx) y then var_ctx
        else raise (Not_equivalent ("type mismatch: " ^ (Var.to_string x) ^ " != "
                                    ^ (Var.to_string y)))
      else Varmap.add x y var_ctx
    | IdTy(id),IdTy(id') ->
       if id = id' then var_ctx
       else raise (Not_equivalent ("type mismatch: " ^ (p2s id) ^ " != " ^ (p2s id')))
    | NameTy(ns),NameTy(ns') ->
       if ns = ns' then var_ctx
       else raise (Not_equivalent ("type mismatch: " ^ (p2s ns) ^ " != " ^ (p2s ns')))
    | DataTy(ds,tys),DataTy(ds',tys') ->
       if ds = ds' then
         List.fold_left (fun vctx (t,u) -> h (t,u) vctx) var_ctx (List.combine tys tys')
       else raise (Not_equivalent ("type mismatch: " ^ (p2s ds) ^ " != " ^ (p2s ds')))
    | UnderscoreTy,UnderscoreTy 
    | IntTy,IntTy 
    | CharTy,CharTy
    | BoolTy,BoolTy
    | PropTy,PropTy
    | UnitTy,UnitTy -> var_ctx
    | ArrowTy(ty1,ty2),ArrowTy(ty1',ty2')
    | PairTy(ty1,ty2),PairTy(ty1',ty2') 
    | AbsTy(ty1,ty2),AbsTy(ty1',ty2') -> h (ty1,ty1') var_ctx |> h (ty2,ty2')
    | ListTy(ty),ListTy(ty') -> h (ty,ty') var_ctx
    | _ -> raise (Not_equivalent "type mismatch") 
  in
  try
    let _ = h (ty1,ty2) Varmap.empty in
    true
  with
    Not_equivalent msg -> (* print_string msg; print_newline; *) false
;;
                            
let rec are_equiv_cl c1 c2 =
  let c1 = unwrap_clause c1 in
  let c2 = unwrap_clause c2 in
  let h2 x y map =
    if Varmap.mem x map then
      if Var.eq (Varmap.find x map) y then map
      else raise (Not_equivalent ("names/vars " ^ Var.to_string x ^ " != " ^ Var.to_string y))
    else Varmap.add x y map in
  let rec h1 (c1,c2) (var_ctx,name_ctx) =
    (* print_string ("h1: " ^ (t2s c1) ^ " " ^ (t2s c2) ^ "\n"); *)
    match c1,c2 with
      Var x, Var y -> (h2 x y var_ctx,name_ctx)
    | Name a, Name b -> (var_ctx,h2 a b name_ctx)
    | Abs(a,t),Abs(b,u) | Conc(t,a),Conc(u,b) -> h1 (Name a,Name b) (var_ctx,name_ctx) |> h1 (t,u)
    | Unit,Unit | Nil,Nil | True,True | False,False | Cut,Cut -> (var_ctx,name_ctx)
    | Atomic(f,ts), Atomic(g,us) ->
       (* TODO: sym_eq f g *)
     if f = g && List.length ts = List.length us
     then
       List.combine ts us |>
         List.fold_left
           (fun ctxs tu -> h1 tu ctxs)
           (var_ctx,name_ctx)
     else raise (Not_equivalent ("atomic: " ^ (t2s c1) ^ " != " ^ (t2s c2)))
  | Not(t1),Not(t2) -> h1 (t1,t2) (var_ctx,name_ctx)
  | Pair(t1,t2),Pair(u1,u2)
  | Cons(t1,t2),Cons(u1,u2)
  | And(t1,t2),And(u1,u2)
  | Or(t1,t2),Or(u1,u2)
  | Is(t1,t2),Is(u1,u2)
  | App(t1,t2),App(u1,u2)
  | EUnify(t1,t2),EUnify(u1,u2)
  | Fresh (None,t1,t2),Fresh (None,u1,u2) 
  | Implies(t1,t2),Implies(u1,u2) -> h1 (t1,u1) (var_ctx,name_ctx) |> h1 (t2,u2)
  | Guard(t1,t2,t3),Guard(u1,u2,u3)
  | Subst(t1,t2,t3),Subst(u1,u2,u3) ->
     h1 (t1,u1) (var_ctx,name_ctx) |> h1 (t2,u2) |>  h1 (t3,u3)
  | Forall(v1,ty1,t),Forall(v2,ty2,u)
  | Exists(v1,ty1,t),Exists(v2,ty2,u)
  | Lambda(v1,ty1,t),Lambda(v2,ty2,u) ->
     if are_equiv_ty ty1 ty2 then h1 (Var v1,Var v2) (var_ctx,name_ctx) |> h1 (t,u)
     else raise (Not_equivalent "type mismatch")
  | New(v1,ty1,t),New(v2,ty2,u) -> 
     if are_equiv_ty ty1 ty2 then h1 (Name v1,Name v2) (var_ctx,name_ctx) |> h1 (t,u)
     else raise (Not_equivalent "type mismatch")
  | Fresh(Some(ty1,ty2),t1,t2),Fresh(Some(ty1',ty2'),u1,u2)
       when are_equiv_ty ty1 ty1' && are_equiv_ty ty2 ty2' -> h1 (t1,u1) (var_ctx,name_ctx) |> h1 (t2,u2)
  | Eq(Some ty,t1,t2),Eq(Some ty',u1,u2) when are_equiv_ty ty ty' ->
     h1 (t1,u1) (var_ctx,name_ctx) |> h1 (t2,u2)
  | Transpose (a1,b1,t),Transpose(a2,b2,u) ->
     h1 (Name a1,Name a2) (var_ctx,name_ctx) |> h1 (Name b1,Name b2) |> h1 (t,u)
  | _ -> raise (Not_equivalent ("catchall " ^ (t2s c1) ^ " " ^ (t2s c2)))
  in
  try
    let _ = h1 (c1,c2) (Varmap.empty,Varmap.empty) in
    if !Flags.debug then print_endline ((t2s c1) ^ " is equivalent to\n" ^ (t2s c2));
    incr_sub_counter ();
    true
  with
    Not_equivalent msg -> (* print_string msg; print_newline (); *) false
;;


let rec contains_disgiunction = function
      Atomic(_) | True | False -> false
    | Or(_) -> true
    | And(t,u)
    | Fresh(_,t,u)
    | Implies(t,u) -> contains_disgiunction u || contains_disgiunction u
    | Forall(_,_,tm) | Exists(_,_,tm) | New(_,_,tm) -> contains_disgiunction tm
    (* TODO: add other cases *)
    | _ -> false                                                                  
;;

exception Prepare_exc of string;;  
  
let prepare4subsumption tm =
  let rec inner = function
      Atomic(x) -> [Atomic(x)]
    | Or(g1,g2) -> (inner g1) @ (inner g2)
    | And(g1,g2) -> Util.allpairs (inner g1) (inner g2) |>
		      List.map (fun (x,y) -> And(x,y))
    | Forall(v,ty,t) ->
       if contains_disgiunction t
       then raise (Prepare_exc "Impossible to remove disgiunction from forall in body")
       else List.map (fun x -> Forall(v,ty,x)) (inner t)
    | New(v,ty,t) -> raise (Prepare_exc "inner: new quantifier not yet handled")
    | Exists(v,ty,t) -> raise (Prepare_exc "inner: exists quantifier not yet handled")
    | t -> raise (Prepare_exc ("inner: not allowed in subsumption: " ^ (t2s t)))
  in
  match tm with 
    Atomic _ -> tm
  | Implies(b,h) -> List.map (fun g -> Implies(g,h)) (inner b) |> and_list
  | Forall(v,ty,t) -> List.map (fun g -> Forall(v,ty,g)) (inner t) |> and_list
  | _ -> raise (Prepare_exc (" unexpected case " ^ (t2s tm)))
;; 

                                              
let rec is_subsumed sg clause clauses =
  let bound = 10 in
  let report exc goal =
    print_endline ("\nSUBSUMPTION: " ^ (Printexc.to_string exc) ^
                     " goal:\n" ^ (t2s goal) ^ ".")
  in
  let tc_and_translate_g goal =
    let (tcenv,g) = Monad.run sg empty_env (Tc.check_goal goal) in
    Translate.translate_goal sg tcenv g
  in
  let solve goal =
    Var.reset_var();
    let names = Varset.elements (I.fas_g goal) in
    Boundsolve.boundsolve Isym.pp_term_sym sg empty_index Dtrue goal names
                          (fun _ _ -> raise Success) bound (Subst.id,[]);
  in
  let clause = unwrap_clause clause in
  let clauses = List.map unwrap_clause clauses in
  let prog = and_list clauses in
  try
    let goal = tc_and_translate_g (Implies (prog,prepare4subsumption clause))
               |> I.add_forall_right in
    if !Flags.debug then print_endline ("subsumption goal\n" ^
                                          (Printer.print_to_string
                                             (I.pp_goal Isym.pp_term_sym) goal));
    solve goal;
    raise Failure
  with
  | Success -> if !Flags.debug then
                 (print_endline ((t2s clause) ^ " is subsumed by:");
                  List.iter (fun cl1 -> print_endline (t2s cl1)) clauses);
               incr_sub_counter (); true
  | Failure -> false
  | (Prepare_exc msg) as e-> if !Flags.debug then report e clause; false
  | e -> report e clause; false
;;

let rec smart_add_clause sg clause = function
    [] -> [clause]
  | clauses ->
     if is_subsumed sg clause clauses then clauses
     else clause ::
            (List.filter
               (fun cl ->
                not (is_subsumed sg cl [clause] || are_equiv_cl cl clause)) clauses)
;;

let rec unify_clause_pairs sg = function
    [] -> []
  | (c1,c2) :: xs ->
      match unify_clause_pair (c1,c2) with
	Some c -> (if !Flags.debug then
		    (print_string " new clause: ";
		    Printer.print_to_channel pp_decl c stdout;
		    print_newline ()));
		  smart_add_clause sg c (unify_clause_pairs sg xs)
		   (* c :: (unify_clause_pairs sg xs) *)
	| None -> (if !Flags.debug then print_string " failed. \n");
		  unify_clause_pairs sg xs
;;

let make_not_decl (p,tys) = 
  make_pred_decl (get_base (rename_not p)) tys
;;

let get_pred_decl (p,ty) = 
  let (tys,rty) = unpack_ty ty in
  if rty = PropTy
  then Some (p,tys)
  else None
;;

(* TODO: adapt main call to generate_negative_{decls,defns} and remove the function above *)
(* Generates clauses not_p1...not_pn and then defines not_p as conjunction of the not_pi's *)
let generate_negation sg = 
  let make_not_decl (p,tys) = 
    make_pred_decl (get_base (rename_not p)) tys in
  let get_pred_decl (p,ty) = 
    let (tys,rty) = unpack_ty ty in
    if rty = PropTy
    then Some (p,tys)
    else None in
  let _ = check_well_quantified !(sg.clauses) in 
  let get_definition (p,tys) = 
    (p,tys,Util.collect (get_clauses p [] True) !(sg.clauses)) in
  let predicate_decls = Util.map_partial get_pred_decl !(sg.tdecls) in
  (* Check that the clauses are first-order and linear! *)
  let negate_predicate (p,tys,clauses) = 
    let negate_clause (notpi,(vs,ts,g)) = 
      [make_abbrev_decl notpi tys]
      @(List.map (fun pat -> make_clause_decl (Atomic(Root(Base(notpi)),pat)))
	  (pattern_complements sg ts tys))
      @[make_clause_decl (Implies(negate_goal g,Atomic(Root(Base(notpi)),ts)))]
    in
    let notpis = 
      Util.tabulate 
	(fun i -> get_base (rename_not p) ^ string_of_int i)
	(List.length clauses) in
    let named_clauses = Util.zip notpis clauses in
    let vXs = List.map (fun _ -> Var (Var.mkvar "X")) tys in 
    let combined_head = 
      make_clause_decl
	(Implies(and_list 
		   (List.map 
		      (fun name -> Atomic(Root(Base(name)),vXs))
		      notpis),
		 Atomic(Root(rename_not p), vXs))) 
    in
    Util.collect negate_clause named_clauses@[combined_head]
  in
  let decls = List.map make_not_decl predicate_decls in
  let defns = List.map get_definition predicate_decls in 
  let decls' = Util.collect negate_predicate defns in
  decls@decls'
;;


  
let generate_negative_decls sg positive_preds =
  let predicate_decls = Util.map_partial get_pred_decl !(sg.tdecls) in
  let decls = List.filter (fun (p,ty) -> List.mem (get_base p) positive_preds) predicate_decls in
  List.map make_not_decl decls
            
let generate_negative_defns sg positive_preds =
  let stats_buffer = ref "" in
  let _ = check_well_quantified !(sg.clauses) in 
  let get_definition (p,tys) = 
    (p,tys,List.rev (Util.collect (get_clauses p [] True) !(sg.clauses))) in
  let predicate_decls = Util.map_partial get_pred_decl !(sg.tdecls) in
  let negate_predicate (p,tys,clauses) =
    reset_sub_counter ();
    let not_p = rename_not p in
    (if !Flags.debug then print_string ("\nNEGATING " ^ (Printer.print_to_string pp_sym p) ^ "\n"));
    let negate_clause (_,pats,g) =
      let negated_clauses =
	(List.map
	   (fun pat -> make_clause_decl (Atomic(Root(Base(get_base not_p)),pat)))
	   (pattern_complements sg pats tys))
	@[make_clause_decl (Implies(negate_goal g,Atomic(Root(Base(get_base not_p)),pats)))]
      in
      (List.map (fun clause ->
		match clause.rdecl with
		| ClauseDecl(c) -> {pos=None;rdecl=ClauseDecl (simplify c)}
		| _ -> clause) negated_clauses) |> List.filter useful_clause 
    in
    let clauses_list = List.map negate_clause clauses in
    let minimal_clauses = List.fold_left
                            (fun l1 l2 ->
		             if !Flags.debug then print_string "ITERATION\n";
		             let cpair = Util.allpairs l1 l2 in
		             let res = unify_clause_pairs sg cpair in
		             if !Flags.debug then
		               (print_string "ITER RES:\n";
			        List.iter (fun decl ->
				           print_endline (d2s decl))
				          res);
                             res)
		            (List.hd clauses_list) (List.tl clauses_list)
    in
    stats_buffer := !stats_buffer ^ "STATS pred " ^ (get_base not_p) ^ " :\n" ^
                      "clauses subsumed: " ^ (string_of_int !sub_counter) ^ "\n" ^ 
                        "resulting clause number: " ^
                          (string_of_int (List.length minimal_clauses)) ^ "\n";
    minimal_clauses
  in
  let decls = List.filter (fun (p,ty) -> List.mem (get_base p) positive_preds) predicate_decls in
  let defns = List.map get_definition decls in
  (Util.collect negate_predicate defns),!stats_buffer
;;  
