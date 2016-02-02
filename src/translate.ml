(* Alpha Prolog *)
(* Translate: translate the results of unification back into 
   human-readable absyn terms.
*)
module A = Absyn;;
open Internal;;
open Isym;;
open Nstbl;;
open Tcenv;;
module T = Types;;

let rec translate_ty sg env s = 
  let h = translate_ty sg env in
  match s with
    T.IdTy _ -> Util.impos "unexpected IdTy"
  | T.NameTy (Root(ats)) -> 
      let (_,u,_) = Nstbl.find sg.ksg (Root ats) in 
      App(NameTy (u,Nstbl.ns2s ats),[])
  | T.DataTy (Root(ds),ss) -> 
      let (_,u,_) = Nstbl.find sg.ksg (Root ds) in 
      App(DataTy (u,Nstbl.ns2s ds),List.map h ss)
  | T.UnitTy -> App(UnitTy,[])
  | T.PairTy(s1,s2) ->  App(PairTy, [h s1; h s2])
  | T.AbsTy(s1,s2) -> App(AbsTy,[h s1; h s2])
  | T.ListTy (s) -> App(ListTy,[h s])
  | T.VarTy v -> let (vs,_,_,_) = env in 
    if Varset.mem v vs 
    then Susp(Perm.id, Exist Toplevel, v) 
    else Susp(Perm.id, Univ, v) 
  | T.UnderscoreTy -> 
      let v = Var.mkvar "$_" in
      Susp(Perm.id, Exist Toplevel, v) 
  | T.IntTy -> App(IntTy,[])
  | T.CharTy -> App(CharTy,[])
  | T.BoolTy -> App(BoolTy,[])
  | T.PropTy -> App(PropTy,[]) 
  | T.ArrowTy(s1,s2) -> App (ArrowTy, [h s1; h s2])
  | _ -> Util.impos "impossible case in translate_ty"
;;


let rec untranslate_ty sg env s = 
  let h = untranslate_ty sg env in 
  match s with 
    App(IntTy,[]) -> T.IntTy
  | App(BoolTy,[]) ->  T.BoolTy
  | App(CharTy,[]) -> T.CharTy
  | App(UnitTy,[]) -> T.UnitTy
  | App(PropTy,[]) -> T.PropTy
  | App(ListTy,[s]) -> T.ListTy(h s)
  | App(ArrowTy,[s1;s2]) -> T.ArrowTy(h s1, h s2)
  | App(PairTy,[s1;s2]) -> T.PairTy(h s1, h s2)
  | App(AbsTy,[s1;s2]) -> T.AbsTy(h s1, h s2)
  | Susp(p,_,v) -> 
      if p = Perm.id then T.VarTy (v) 
      else Util.impos "impossible case in untranslate_ty"
  | App(NameTy (u,_), []) -> 
      let s = Hashtbl.find sg.stbl u in
      T.NameTy(Root s)
  | App(DataTy (u,_), ts) -> 
      let s = Hashtbl.find sg.stbl u in
      T.DataTy(Root s,List.map h ts)
  | _ -> Util.impos "impossible case in untranslate_ty"
;;


let gand (g1,g2) = 
  match g1,g2 with
    Gtrue,_ -> g2
  | _,Gtrue -> g1
  | Gfalse,_ -> Gfalse
  | _, Gfalse -> Gfalse
  | _,_ -> Gand(g1,g2)
;;


let rec gimplies (d1,g2) = 
  match d1 with
    Dtrue -> g2
  | _ -> Gimplies(d1,g2)
;;

let dimplies (g1,d2) =
  match g1 with
    Gtrue -> d2
  | _ -> Dimplies(g1,d2)
;;

(* |translate_gm sg env t|
   Translates a term to internal syntax plus additional goals and existentially quantified variables.
   Occurrences of concretion are translated into new subgoals which eventually constrain the 
   goal/program clause in which the concretion appears
*)

let rec translate_tm sg env t = 
  let h = translate_tm sg env in
  let hs l = List.fold_right 
      (fun t (ts,gs,vs) -> 
	let t,g,v = h t in (t::ts,gand (g,gs),v@vs)) l ([],Gtrue,[]) in
  match t with
    A.Unit -> (App(Unit,[]),Gtrue,[])
  | A.Pair(t1,t2) -> 
      let t1,g1,vs1 = h t1 in
      let t2,g2,vs2 = h t2 in
      (App(Pair,[t1;t2]),gand(g1,g2),vs1@vs2)
  | A.Abs(a,t) -> 
      let t,g,vs = h t in
      (Abs(a,t),g,vs)
  | A.Conc(t,a) -> 
      let u,g,vs = h t in 
      let x = Var.mkvar "$_" in
      let vx = Susp(Perm.id, Exist Toplevel, x) in
      (vx, gand(g,Gequals(u,Abs(a,vx))), x::vs)
  | A.Atomic(Root hd,tl) -> 
      (* TODO: Add "is_var" to tenv, use it here *)
      let ts,g,vs = hs tl in 
      let entry = Nstbl.find sg.tsg (Root hd) in 
      if entry.is_def 
      then 
	let x = Var.mkvar "$_" in
	let tm = Susp(Perm.id,Exist Toplevel, x) in
	(tm, gand (g,Gatomic(App(Symb (entry.sym_id,Nstbl.ns2s hd ), 
				 tm::ts))),x::vs)
      else (App(Symb (entry.sym_id,Nstbl.ns2s hd), ts),g,vs)
  | A.Nil -> (App(Nil,[]),Gtrue,[])
  | A.Cons(t1,t2) -> 
      let t1,g1,vs1 = h t1 in
      let t2,g2,vs2 = h t2 in
      (App(Cons,[t1;t2]),gand(g1,g2),vs1@vs2)
  | A.IntC i -> (App (Int i,[]),Gtrue,[])
  | A.CharC s -> (App (Char s,[]),Gtrue,[])
  | A.BoolC b -> (App (Bool b, []), Gtrue, [])
  | A.Var v -> (Susp(Perm.id,Exist Toplevel, v),Gtrue,[])
  | A.Name a -> (Name a, Gtrue,[])
  | A.Transpose(a,b,t) -> 
      let t,g,vs = h t in
      (apply_p (Perm.trans a b) t, g, vs)
  | A.Subst(t1,t2,t3) -> 
      let t1,g1,vs1 = h t1 in
      let t2,g2,vs2 = h t2 in
      let t3,g3,vs3 = h t3 in
      (App(Sigma,[t1;t2;t3]),Gand(g1,Gand(g2,g3)),vs1@vs2@vs3)
  | A.Lambda(x,_,t) -> 
      (* Functions ignored inside lambda *)
      let t1,_,_ = h t in
      (Lam(x,t1),Gtrue,[])
  | A.App(t1,t2) -> 
      let t1,g1,vs1 = h t1 in
      let t2,g2,vs2 = h t2 in
      (Apply(t1,t2),gand(g1,g2),vs1@vs2)
  | _ -> Util.impos "impossible case in translate_tm"
	;; 


let rec untranslate_tm sg env t = 
  let h = untranslate_tm sg env in
  match t with
    App(Unit,[]) -> A.Unit
  | App(Pair,[t1;t2]) -> A.Pair(h t1, h t2)
  | Abs(a,t) -> A.Abs(a, h t)
  | Name(a) -> A.Name(a)
  | App(Nil,[]) -> A.Nil
  | App(Cons,[t1;t2]) -> A.Cons(h t1, h t2)
  | Susp(p,_,v) -> 
      let l = Perm.to_list p in 
      let tm = A.Var(v) in
      List.fold_right (fun (a,b) t -> A.Transpose(a,b,t)) l tm
  | App(Int i,[]) -> A.IntC(i)
  | App(Bool b, []) -> A.BoolC b
  | App(Char s,[]) -> A.CharC(s)
  | App(Symb(u,_),t) -> 
      let s = Hashtbl.find sg.stbl u in
      A.Atomic(Root s,List.map h t)
  | App(Sigma,[u1;u2;u3]) -> 
      A.Subst(h u1, h u2, h u3)
  | Apply(u1,u2) -> 
      A.App (h u1, h u2)
  | Lam(x,u2) -> 
      A.Lambda (x, Types.UnderscoreTy,h u2)
  | _ -> Util.impos "ill-formed term representation"
;;



(* |translate_goal sg tcenv g| 
   |translate_prog sg tcenv p|
Translates a goal / program to internal representation 
Freshens all variables and translates occurrences of Forall to Gforall or Gforallstar 
depending on whether extensional_forall is set. 
Extra goals inserted by translate_tm to handle e.g. concretion are added to goals. *)

let rec translate_goal sg tcenv g = 
  let tg = translate_goal sg tcenv in 
  let tt = translate_tm sg tcenv in 
  let tp = translate_prog sg tcenv in 
  let tts l = List.fold_right 
      (fun t (ts,gs,vs) -> 
	let t,g,v = tt t in 
	(t::ts,gand (g,gs),v@vs)) l ([],Gtrue,[]) in
  let exists_quantify vs l = 
    List.fold_right (fun v p -> Gexists(v,p)) vs l in
  match g with
    A.Atomic(Root(sym),ts) -> 
      let ts,g,vs = tts ts in 
      let entry = Nstbl.find sg.tsg (Root sym) in 
      let u = entry.sym_id in 
      exists_quantify vs (gand (g,Gatomic(App(Symb (u,Nstbl.ns2s sym),ts))))
  | A.Fresh(_,t1,t2) -> 
      let t1,g1,vs1 = tt t1 in
      let t2,g2,vs2 = tt t2 in
      exists_quantify (vs1@vs2) (gand(g1,gand(g2,Gfresh(t1,t2))))
  | A.Eq(_,t1,t2) -> 
      let t1,g1,vs1 = tt t1 in
      let t2,g2,vs2 = tt t2 in
      exists_quantify (vs1@vs2) (gand(g1,gand(g2,Gequals(t1,t2))))
  | A.EUnify(t1,t2) -> 
      let t1,g1,vs1 = tt t1 in
      let t2,g2,vs2 = tt t2 in
      exists_quantify (vs1@vs2) (gand(g1,gand(g2,Geunify(t1,t2))))
  | A.Is(t1,t2) -> 
      let t1,g1,vs1 = tt t1 in
      let t2,g2,vs2 = tt t2 in
      exists_quantify (vs1@vs2) (gand(g1,gand(g2,Gis(t1,t2))))
  | A.Cut -> Gcut
  | A.True -> Gtrue
  | A.False -> Gfalse
  | A.And(g1,g2) -> gand(tg g1, tg g2)
  | A.Or(g1,g2) -> Gor(tg g1, tg g2)
  | A.Implies(d1,g2) -> gimplies(tp d1, tg g2)
  | A.Guard(g1,g2,g3) -> Guard(tg g1, tg g2, tg g3)
  | A.Not(g) -> Gnot(tg g)
  | A.Forall(v,s,g) -> (* TODO: ALlow forall* in programs? or abstract syntax?*) 
      if !Flags.extensional_forall
      then Gforallstar(v,s,tg g)
      else Gforall(v,tg g)
  | A.Exists(v,s,g) -> Gexists(v,tg g)
  | A.New(v,s,g) -> Gnew(v,tg g)
  | A.Var(v) -> Gatomic(mk_var(v))
  | _ -> Util.impos "impossible case in translate_goal"



and translate_prog sg tcenv p = 
  let tg = translate_goal sg tcenv in 
  let tt = translate_tm sg tcenv in 
  let tp = translate_prog sg tcenv in 
  let tts l = List.fold_right 
      (fun t (ts,gs,vs) -> 
	let t,g,v = tt t in 
	(t::ts,gand (g,gs),v@vs)) l ([],Gtrue,[]) in
  let forall_quantify vs l = 
    List.fold_right (fun v p -> Dforall(v,p)) vs l in
  match p with
    A.Atomic(Root(sym),ts) -> 
      let ts,g,vs = tts ts in
      let entry = Nstbl.find sg.tsg (Root sym) in 
      let u = entry.sym_id in 
      forall_quantify vs (dimplies(g,Datomic(App(Symb (u,Nstbl.ns2s sym),ts))))
  | A.True -> Dtrue
  | A.Eq(_,A.Atomic(Root(sym),tms),tm) -> 
      let tms,g1,vs1 = tts tms in
      let tm,g2,vs2 = tt tm in
      let entry = Nstbl.find sg.tsg (Root sym) in 
      let u = entry.sym_id in 
      forall_quantify (vs1@vs2) (dimplies(gand(g1,g2),Datomic(App(Symb (u,Nstbl.ns2s sym), tm::tms))))
  | A.Implies(g1,p2) -> 
      dimplies(tg g1, tp p2)
  | A.And(p1,p2) -> 
      Dand(tp p1, tp p2)
  | A.Forall(v,ty,p) -> 
      Dforall(v,tp p)
  | A.New(v,ty,p) ->
      Dnew(v,tp p)
  | _ -> Util.impos "impossible case in translate_prog"
;;


let rec goal2hyp g =
  match g with 
    Gtrue -> Htrue
  | Gfresh(t,u) -> Hfresh(t,u)
  | Gequals(t,u) -> Hequals(t,u)
  | Gatomic(t) -> Hatomic(t)
  | Gand(g1,g2) -> Hand(goal2hyp g1, goal2hyp g2) 
  | Gexists(v,g) -> Hexists(v, goal2hyp g) 
  | _ -> Util.impos("Goal cannot be translated to hypothesis")
;;


let rec translate_hyp sg tcenv h =
  let ttm = translate_tm sg tcenv in 
  let th = translate_hyp sg tcenv in 
  let tts l = List.fold_right 
      (fun t (ts,gs,vs) -> 
	let t,g,v = ttm t in 
	(t::ts,gand (g,gs),v@vs)) l ([],Gtrue,[]) in
  let exists_quantify vs l = 
    List.fold_right (fun v p -> Hexists(v,p)) vs l in
  match h with 
    A.True -> Htrue
  | A.And(t1,t2) -> Hand(th t1, th t2)
  | A.Exists(var,ty,t) -> Hexists(var,th t)
  | A.New(var,ty,t) -> Hnew(var,th t)
  | A.Atomic(Root(sym),ts) -> 
      let ts,g,vs = tts ts in
      let h = goal2hyp(g) in
      let entry = Nstbl.find sg.tsg (Root sym) in 
      let u = entry.sym_id in 
      exists_quantify vs (Hand(h,Hatomic(App(Symb (u,Nstbl.ns2s sym),ts))))
  | A.Fresh(_,t1,t2) -> 
      let t1,g1,vs1 = ttm t1 in
      let t2,g2,vs2 = ttm t2 in
      exists_quantify (vs1@vs2) (Hand(goal2hyp g1,Hand(goal2hyp g2,Hfresh(t1,t2))))
  | A.Eq(_,t1,t2) -> 
      let t1,g1,vs1 = ttm t1 in
      let t2,g2,vs2 = ttm t2 in
      exists_quantify (vs1@vs2) (Hand(goal2hyp g1,Hand(goal2hyp g2,Hequals(t1,t2))))
  | _ -> Util.impos "impossible case in translate_hyp"
;;


let rec translate_test sg tcenv t = 
  let tt = translate_test sg tcenv in 
  let ttm = translate_tm sg tcenv in 
  let tts l = List.fold_right 
      (fun t (ts,gs,vs) -> 
	let t,g,v = ttm t in 
	(t::ts,gand (g,gs),v@vs)) l ([],Gtrue,[]) in
  let forall_quantify vs l = 
    List.fold_right (fun v p -> Tforall(v,p)) vs l in
  let th = translate_hyp sg tcenv in 
  match t with 
    A.True -> Ttrue
  | A.False -> Tfalse
  | A.Implies(hyp,test) -> Timplies(th hyp, tt test)
  | A.Forall(var,ty,t) -> Tforall(var,tt t)
  | A.New(name,ty,t) -> Tnew(name, tt t)
  | A.Fresh(Some(ty1,ty2),t1,t2) -> 
      let t1,g1,vs1 = ttm t1 in
      let t2,g2,vs2 = ttm t2 in
      forall_quantify (vs1@vs2) (Timplies(goal2hyp g1,Timplies(goal2hyp g2,Tfresh(ty1,ty2,t1,t2))))
  | A.Eq(Some ty,t1,t2) -> 
      let t1,g1,vs1 = ttm t1 in
      let t2,g2,vs2 = ttm t2 in
      forall_quantify (vs1@vs2) (Timplies(goal2hyp g1,Timplies(goal2hyp g2,Tequals(ty,t1,t2))))
  | A.Atomic(Root(sym),ts) -> 
(* Fill in list of variable/type pairs *)
      let vs0 = Varset.elements (Varset.unions (List.map A.fvs ts)) in	
      let vtys = List.map (fun v -> (Susp(Perm.id, Exist Toplevel, v), Tcenv.lookup_env v tcenv)) vs0 in 
(* Translate and expand recursively *)
      let ts,g,vs = tts ts in
      let h = goal2hyp(g) in
      let entry = Nstbl.find sg.tsg (Root sym) in 
      let u = entry.sym_id in 
      forall_quantify vs (Timplies(h,Tatomic(vtys,App(Symb (u,Nstbl.ns2s sym),ts))))
  | _ -> Util.impos "impossible case in translate_test"
;;
