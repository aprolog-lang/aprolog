open Util;;
open Internal;;
open Subst;;
open Types;;
open Unify;;
open Tcenv;;
module P = Perm;;
module S = Subst;;

type 'a answer =  'a Unify.answer;;


exception DepthBound;;

let overflow = ref false;;

let remove_name_dependences a (subst,constrs) = 
  (subst, List.filter (fun (av,v) -> 
    match av with
      Name b -> if Var.eq a b then false else true
    | _ -> true) constrs)
;;


let remove_var_dependences x (subst,constrs) = 
  (subst, List.filter (fun (av,v) -> 
    if Var.eq x v then false else 
    match av with
      Susp(_,_,w) -> if Var.eq x w then false else true
    | _ -> true) constrs)
;;


let check_for_var_dependences x (subst,constrs) = 
  List.exists (fun (av,v) -> 
    if Var.eq x v then true 
    else match av with
      Susp(_,_,w) -> Var.eq x w
    | _ -> false) constrs
;;


let boundsolve pp sg idx prog goal names sc steps ans  = 
  let rec solve_goal prog goal uvars names cexn sc steps ans = 
    do_trace 2 (fun () -> 
      if goal != Gtrue then 
	let (subst,_) = ans in
	print_string ("Solving goal\n"^
		      Printer.print_to_string (pp_goal pp) 
			(Subst.apply_s_g subst goal)^
		      "\n"));
    let b = (match goal with
      Gtrue -> sc steps ans
    | Gfalse -> ()
    | Gand(g1,g2) ->  
	solve_goal prog g1 uvars names cexn 
	  (solve_goal prog g2 uvars names cexn sc) 
	  steps ans
    | Gor(g1,g2) -> 
	solve_goal prog g1 uvars names cexn sc steps ans;
	solve_goal prog g2 uvars names cexn sc steps ans
    | Gatomic(t) -> 
	(let module M = struct exception NewCut end in 
	try (match_atomic t prog uvars names M.NewCut sc steps ans)
	with M.NewCut -> ())
    | Gexists(x,g) -> 
	let y = Var.rename x in
	let t = Susp(Perm.id,Exist(Constrained (names@uvars)),y) in
	solve_goal prog (S.apply_s_g (S.sub1 x t) g) uvars names cexn 
	  sc steps ans
    | Gforall(x,g) -> 
	let x' = Var.rename x in
	solve_goal 
	  prog (S.apply_s_g (S.sub1 x (Susp(Perm.id,Univ,x'))) g) 
          (x'::uvars) names cexn 
	  (fun steps ans -> 
	    if check_for_var_dependences x' ans then () else sc steps ans)
	  steps ans
	(* TODO: limit names available to evars also! *)
    | Gforallstar(x,ty,g) -> 
	solve_goal prog (Gforall(x,g)) uvars names cexn sc steps ans;
	(let module M = struct exception NewCut end in 
	try (do_extensional_forall prog x ty g uvars names cexn sc steps ans)
	with M.NewCut -> ())
    | Gnew(a,g) ->  
	let b = Var.rename a in
	(* BUG: filtering out constraints is unsound *)
	(* solve_goal  prog (subst_name_g a b g) uvars (b::names) cexn 
	  (fun steps ans -> sc steps (remove_name_dependences b ans)) steps ans *)
	(* Solve/impose freshness constraints *)
	let fvs = Varset.elements (fvs_g g) in
        constrain_fresh b fvs (solve_goal prog (subst_name_g a b g) uvars (b::names) cexn sc steps) ans
    | Gimplies(d,g) -> 
	solve_goal (Dand(d,prog)) g uvars names cexn sc steps ans
    | Gequals(t1,t2) -> 
	unify Isym.term_sym_eq t1 t2 (sc steps) ans
    | Gis(t1,t2) -> 
	let (subst,constrs) = ans in
	let v = Eval.eval Runtime.apply subst t2 in 
	unify Isym.term_sym_eq t1 v (sc steps) ans
    | Gfresh (t1,t2) -> 
	unify_fresh t1 t2 (sc steps) ans
    | Gnot g -> 
	let module M = struct exception Not_success end in
	let new_sc = (fun ans -> raise M.Not_success) in
	(try 
	  solve_goal prog g uvars names cexn new_sc steps ans;
	  if !overflow then overflow := false else sc steps ans
	with M.Not_success -> ()) 
    | Guard(g1,g2,g3) -> 
	let module M = 
	  struct exception Guard_success of int * Isym.term_sym answer end in
	let new_sc = (fun steps ans -> raise (M.Guard_success (steps,ans))) in
	(try (
	  solve_goal prog g1 uvars names cexn new_sc steps ans;
	  solve_goal prog g3 uvars names cexn sc steps ans
	    )
	with M.Guard_success (steps,ans) ->
	  if !overflow 
 	  then overflow := false 
	  else 
	    solve_goal prog g2 uvars names cexn sc steps ans)
    | Gcut -> 
	let _ = sc steps ans in
	raise cexn
    | Geunify(t,u) -> 
	nyi ()
	    )
    in
    do_trace 2 (fun () -> 
      print_string "Backtracking solve_goal\n");
    b
      
  and match_atomic t prog uvars names cexn sc steps ((subst,_) as ans) = 
    if steps <= 0
    then overflow := true
    else
      let t' = S.compress t subst in
      let prog' = Index.lookup idx t' in
      let rec rmatch p subgoal names = 
	match p with 
	  Dtrue -> ()
	| Dand(d1,d2) -> 
	    rmatch d1 subgoal names; 
	    rmatch d2 subgoal names
	| Dimplies(g,s) -> 
	    rmatch s (Gand(g,subgoal)) names
	| Datomic(s) -> 
	    do_trace 3 (fun () -> 
	      let (subst,_) = ans in 
	      print_string "Unifying with clause head\n";
	      Printer.print_to_channel 
		(pp_term pp) 
		(Subst.apply_s subst s) stdout;
	      print_string "\n");
	    let head = Internal.find_head s in
	    let sym = Hashtbl.find sg.stbl head in
	    let steps' = 
	      if (Nstbl.find sg.tsg (Nstbl.Root(sym))).is_abbrev 
	      then steps else steps-1 in
	    Unify.unify Isym.term_sym_eq s t 
	      (solve_goal prog subgoal uvars names cexn sc steps') ans;
	    do_trace 3 (fun () -> 
	      print_string "Unification failed.\n")
	| Dforall(x,d) -> 
	    rmatch 
	      (S.apply_s_p 
	       (S.sub1 x 
		  (Susp(Perm.id,Exist(Constrained (names@uvars)),Var.rename x))) d) 
	      subgoal names
	| Dnew(a,d) -> 
	    (* TODO: Make this behave like Gnew.  Filter out freshness 
               constraints.  *)
	    let b = Var.rename a in
	    rmatch (subst_name_p a b d) subgoal (b::names)
      in
      do_trace 1 (fun () -> 
	let (subst,_) = ans in
	print_string "Solving atomic goal\n";
	Printer.print_to_channel (pp_term pp) (Subst.apply_s subst t) stdout;
	print_string "\n");
      rmatch (Dand (prog',prog)) Gtrue names;
      do_trace 1 (fun () -> 
	print_string "Backtracking match_atomic\n")
	
  and do_extensional_forall prog x ty g uvars names cexn sc steps ans =
    do_trace 1 (fun () -> 
	print_string ("Expanding extensional forall quantifier at "^(Absyn.ty2s ty)^" (n="^string_of_int steps^"\n"));
    match ty with
      UnitTy -> 
	let unit_exp = App(Isym.Unit,[]) in
	solve_goal prog (S.apply_s_g (S.sub1 x unit_exp) g) uvars names cexn sc steps ans
    | PairTy(ty1,ty2) -> 
	let x1 = Var.rename x in
	let x2 = Var.rename x in
	let pair_exp = App(Isym.Pair,[Internal.mk_var(x1);Internal.mk_var(x2)]) in
	solve_goal prog (Gforallstar(x1,ty1,
			 Gforallstar(x2,ty2,
			 S.apply_s_g (S.sub1 x pair_exp) g))) uvars names cexn sc steps ans
    | AbsTy(nty,ty) -> 
	let a = Var.mkvar "a" in
	let x0 = Var.rename x in
	let abs_exp = Abs(a,Internal.mk_var(x0)) in
	solve_goal prog (Gnew(a,Gforallstar(x0,ty,
			 S.apply_s_g (S.sub1 x abs_exp) g))) uvars names cexn sc steps ans
    | NameTy(ty) -> ()
    | DataTy(dty,[]) -> do_extensional_forall_data prog x dty g uvars names cexn sc steps ans
    | ListTy(ty) -> 
	if steps <= 0
	then overflow := true
	else
	  let nil_exp = App(Isym.Nil,[]) in
	  let x1 = Var.rename x in
	  let x2 = Var.rename x in
	  let cons_exp = App(Isym.Cons,[Internal.mk_var(x1);Internal.mk_var(x2)]) in
	  solve_goal prog (Gand(S.apply_s_g (S.sub1 x nil_exp) g, 
			       Gforallstar(x1,ty,
					   Gforallstar(x2,ListTy ty,
			     S.apply_s_g (S.sub1 x cons_exp) g)))) 
	    uvars names cexn sc (steps-1) ans
    | _ -> (
	Util.do_trace 1 (fun () -> print_endline ("do_extensional_forall: unhandled type "^(Absyn.ty2s ty)));
	())
  and do_extensional_forall_data prog x dty g uvars names cexn sc steps ans = 
    if steps <= 0
    then overflow := true
    else
      let decls = !(sg.tdecls) in
      let relevant_decls = 
	Util.map_partial 
	  (fun (sym,ty) -> 
	    let (args,result_ty) = Absyn.unpack_ty ty in
	    if result_ty = DataTy(dty,[]) then Some (Nstbl.Root(sym),args) else None)
	  decls
      in
      let make_con_goal (sym,argtys) = 
	let vars = List.map (fun ty -> Var.mkvar "X") argtys in
	let entry = Nstbl.find sg.tsg sym in 
	let sym' = Isym.Symb (entry.sym_id,Nstbl.p2s sym) in
	let rec mkgoal tys vs = 
	  match tys,vs with 
	    [],[] -> 
	      let sym_exp = App(sym',List.map Internal.mk_var vars) in
	      S.apply_s_g (S.sub1 x sym_exp) g
	  | ty'::tys',v'::vs' ->  
	      Gforallstar(v',ty',mkgoal tys' vs' )
	  | _ -> Util.impos "do_extensional_forall"
	in mkgoal argtys vars
      in
      let goals = List.map make_con_goal relevant_decls in 
      let goal = List.fold_left (fun g h -> Gand(g,h)) Gtrue goals in
      solve_goal prog goal uvars names cexn sc (steps-1) ans
  in 
  overflow := false;
  let module M = struct exception Cut end in
  (try (solve_goal prog goal [] names M.Cut sc steps ans)
  with M.Cut -> ()
 )
;;
  






