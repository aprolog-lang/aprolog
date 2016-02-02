open Util;;
open Internal;;
open Subst;;
open Types;;
open Unify;;
module P = Perm;;
module S = Subst;;

type 'a answer =  'a Unify.answer;;


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
      Susp(pi,_,w) -> Var.eq x w
    | _ -> false) constrs
;;



let solve_wrap pp idx prog goal names sc ans  = 
  let rec solve_goal prog goal uvars names cexn sc ans = 
    do_trace 2 (fun () -> 
      if goal != Gtrue then 
	let (subst,_) = ans in
	print_string ("Solving goal\n"^
		      Printer.print_to_string (pp_goal pp) 
			(Subst.apply_s_g subst goal)^
		      "\n"));
    let b = (match goal with
      Gtrue -> sc ans
    | Gfalse -> ()
    | Gand(g1,g2) ->  
	solve_goal prog g1 uvars names cexn 
	  (solve_goal prog g2 uvars names cexn sc) 
	  ans
    | Gor(g1,g2) -> 
	solve_goal prog g1 uvars names cexn sc ans;
	solve_goal prog g2 uvars names cexn sc ans
    | Gatomic(t) -> 
	(let module M = struct exception NewCut end in 
	try (match_atomic t prog uvars names M.NewCut sc ans)
	with M.NewCut -> ())
    | Gexists(x,g) -> 
	let y = Var.rename x in
	let t = Susp(Perm.id,Exist(Constrained (names@uvars)),y) in
	solve_goal prog (S.apply_s_g (S.sub1 x t) g) uvars names cexn 
	  sc ans
    | Gforall(x,g) -> 
	let x' = Var.rename x in
	solve_goal 
	  prog (S.apply_s_g (S.sub1 x (Susp(Perm.id,Univ,x'))) g) 
          (x'::uvars) names cexn 
	  (fun ans -> 
	    if check_for_var_dependences x' ans then () else sc ans)
	  ans
	(* TODO: limit names available to evars also! *)
    | Gforallstar(x,s,g) -> runtime_error "Extensional forall (as used in negation elimination) is not supported in ordinary execution."
    | Gnew(a,g) ->  
	let b = Var.rename a in
	(*solve_goal prog (subst_name_g a b g) uvars (b::names) cexn 
	  (fun ans -> sc (remove_name_dependences b ans)) ans *)
	(* The above version seems to have a bug if we remove a freshness constraint 
	   that involves a name that appears elsewhere in the answer, e.g. in a delayed 
	   permuatation. *)
	(* Solve/impose freshness constraints *)
	let fvs = Varset.elements (fvs_g g) in
        constrain_fresh b fvs (solve_goal prog (subst_name_g a b g) uvars (b::names) cexn sc) ans
    | Gimplies(d,g) -> 
	solve_goal (Dand(d,prog)) g uvars names cexn sc ans
    | Gequals(t1,t2) -> 
	unify Isym.term_sym_eq t1 t2 sc ans
    | Gis(t1,t2) -> 
	let (subst,constrs) = ans in
	let v = Eval.eval Runtime.apply subst t2 in 
	unify Isym.term_sym_eq t1 v sc ans
    | Gfresh (t1,t2) -> 
	unify_fresh t1 t2 sc ans
    | Gnot g -> 
	let module M = struct exception Not_success end in
	let new_sc = (fun ans -> raise M.Not_success) in
	(try 
	  solve_goal prog g uvars names cexn new_sc ans;
	  sc ans
	with M.Not_success -> ()) 
    | Guard(g1,g2,g3) -> 
	let module M = 
	  struct exception Guard_success of Isym.term_sym answer end in
	let new_sc = (fun ans -> raise (M.Guard_success ans)) in
	(try (
	  solve_goal prog g1 uvars names cexn new_sc ans;
	  solve_goal prog g3 uvars names cexn sc ans
	    )
	with M.Guard_success ans ->
	  solve_goal prog g2 uvars names cexn sc ans)
    | Gcut -> 
	let _ = sc ans in
	raise cexn
    | Geunify(t,u) -> 
	nyi ()
	    )
    in
    do_trace 2 (fun () -> 
      print_string "Backtracking solve_goal\n");
    b
      
  and match_atomic t prog uvars names cexn sc ((subst,_) as ans) = 
    let t' = S.compress t subst in
    let prog' = Index.lookup idx t' in
    let rec rmatch p sg names = 
      match p with 
	Dtrue -> ()
      | Dand(d1,d2) -> 
	  rmatch d1 sg names; 
	  rmatch d2 sg names
      | Dimplies(g,s) -> 
	  rmatch s (Gand(g,sg)) names
      | Datomic(s) -> 
	  do_trace 3 (fun () -> 
	    let (subst,_) = ans in 
	    print_string "Unifying with clause head\n";
	    Printer.print_to_channel 
	      (pp_term pp) 
	      (Subst.apply_s subst s) stdout;
	    print_string "\n");
	  Unify.unify Isym.term_sym_eq s t 
	    (solve_goal prog sg uvars names cexn sc) ans;
	  do_trace 3 (fun () -> 
	    print_string "Unification failed.\n")
      | Dforall(x,d) -> 
	  rmatch 
	    (S.apply_s_p 
	       (S.sub1 x 
		  (Susp(Perm.id,Exist(Constrained (names@uvars)),Var.rename x))) d) 
	    sg names
      | Dnew(a,d) -> 
	  (* TODO: Make this behave like Gnew.  Check freshness constraints.  *)
	let b = Var.rename a in
	rmatch (subst_name_p a b d) sg (b::names)
    in
    do_trace 1 (fun () -> 
      let (subst,_) = ans in
      print_string "Solving atomic goal\n";
      Printer.print_to_channel (pp_term pp) (Subst.apply_s subst t) stdout;
      print_string "\n");
    rmatch (Dand (prog',prog)) Gtrue names;
    do_trace 1 (fun () -> 
      print_string "Backtracking match_atomic\n")
    
  in 
  let module M = struct exception Cut end in
  (try (solve_goal prog goal [] names M.Cut sc ans)
  with M.Cut -> ())
;;
  
(* TODO: Use varset instead of var list for names and evars! *)

let solve pp idx goal sc = 
  Var.reset_var();
  let names = Varset.elements (fas_g goal) in 
  solve_wrap pp idx Dtrue goal names sc (S.id,[])
;;




