(* Alpha Prolog *)
open Types;;
open Internal;;
module P = Perm;;
module S = Subst;;
open Printer;;
    
(* TODO: Use a faster version of unification such as using reference cells *)
    
(* TODO: Implement "complete" unification for arbitrary terms. *)
    
(* TODO: Interleave freshness constraint solving with unification whenever a 
    substitution is performed (solve constraints "eagerly" *)

(* TODO: Generalize constraint solving architecture.
   Design goals: 
   1.  Space-efficient, Graph based implementation of constraint state
   2.  Efficient backtracking management via (functional or backtrackable)
       UF data structure.
   3.  SUpport for EV unification, user-defined constraints, equational unification?
   4.  Future: support for "boxes", efficient handling of separation 
       constraints? 
 *)
    
type 'a constrs = ('a term * var) list;;


type 'a answer = ('a S.subst * 'a constrs );;


type 'a sc = 'a -> unit;;
type 'a sc_transform = 'a sc -> 'a sc;;


let (|||) sc1 sc2 = fun ans -> sc1 ans ; sc2 ans;;
let (&&&) sct1 sct2 = fun sc -> sct1(sct2 sc);;
let succeed sc = sc;;
let fail sc = fun ans -> ()




let rec unify_fresh1 t1 t2 sub sc constrs = 
  match S.compress t1 sub, S.compress t2 sub with
  | Name a,Name b -> 
      if Var.eq a b 
      then ()
      else sc constrs
  | Name a,Abs(b,e) -> 
      if Var.eq a b 
      then sc constrs
      else 
	unify_fresh1 t1 e sub sc constrs
  | Susp(p,b,v), Abs (a,t) -> 
      let c = Var.rename a in
      unify_fresh1 t1 (apply_p (P.trans a c) t) sub 
        (fun constrs -> 
          sc (List.filter (fun (t',_) -> not(t' = Name c)) constrs))
        constrs
  | _,App(c,es) -> 
      unifys_fresh (List.map (fun t2 -> (t1,t2)) es) sub sc constrs
  | Susp(p,Univ,x), Name a 
  | Name a, Susp(p,Univ,x) ->  
      (* Utter hack *)
      if Var.compare x a > 0 
      then sc constrs 
      else 
	let a' = (P.lookup (P.inv p) a) in
	sc ((Name a', x)::constrs)
  | Susp(p,b,x), Name a 
  | Name a, Susp(p,b,x) ->  
      let a' = (P.lookup (P.inv p) a) in
      sc ((Name a', x)::constrs)
  | Susp(p,b,x), Susp(q,c,y) -> 
    let pi' = Perm.normalize (Perm.comp (Perm.inv q) p) in
    if Var.eq x y  
       && Perm.eq p q
    then ()
    else 
      (sc ((Susp(pi', b,x), y)::constrs)) 
  | _,_ -> Util.impos "illegal case in freshness unification"

and unifys_fresh fs sub = 
  match fs with
    [] -> succeed
  | (a,e)::fs -> unify_fresh1 a e sub &&& unifys_fresh fs sub
;;


let do_susp p1 p2 x sc (sub,fs) = 
  let ds = P.disagreement_set p1 p2 in
  let new_fs = List.map (fun a -> (Name a,x)) ds in
  sc (sub, new_fs@fs)
;;





(* Extended occurs check: check that x does not occur in t, that
   all Uvars in t are permitted for x, and constrain all Evars in 
   t to be as constrained as x is.  *)
let rec occurs_check x c t sc subst = 
  match S.compress t subst with
    Name a -> 
      if !Flags.strict_new_occurs
      then (
        if bconstr_satisfies a c
        then sc (t,subst)
        else ()
	    )
      else sc (t,subst)
  | Abs(a,e) -> 
      occurs_check x c e (fun (t',subst) -> 
      sc (Abs(a,t'), subst)) subst
  | App(f,es) -> 
      occurs_checks x c es (fun (ts,subst) -> 
      sc (App(f,es),subst)) subst
  | Susp(p,Univ,y) -> 
      if bconstr_satisfies y c
      then sc (t,subst)
      else ()
  | Susp(p,Exist c',y) -> 
      if Var.eq x y 
      then ()
      else 
        if bconstr_leq c' c (* If lhs more constrained than rhs *)
	then sc (t,subst) (* continue *)
	else (sc (Susp(p,Exist c, y),subst)) 
  | Apply(e1,e2) -> 
      occurs_check x c e1 (fun (t1',subst) -> 
      occurs_check x c e2 (fun (t2',subst) -> 
	sc (Apply(t1',t2'),subst)) subst) subst
  | Lam(x,e2) -> sc (Lam(x,e2),subst)
(* TODO: Handle correctly *)
(*      occurs_check x c e2 (fun (t1',subst) -> 
	sc (Lam(x,t1'),subst)) subst*)
and occurs_checks x c ts sc subst = 
  match ts with
    [] -> sc ([],subst)
  | t::ts -> 
      occurs_check x c t (fun (t',subst) -> 
      occurs_checks x c ts (fun (ts',subst) -> 
      sc (t'::ts',subst)) subst) subst
;;


let skippable_occurs_check x b t sc subst = 
  if !Flags.skip_occurs_check then sc (t,subst)
  else occurs_check x b t sc subst
;;

let rec is_relevant_f x f = 
  match f with 
    (Susp(_,_,y),y')  -> Var.eq x y || Var.eq x y' 
  | (t,y') -> Var.eq x y' 
;;
  

	
let rec unify_wrap eq t1 t2 sc ans = 
  let rec do_subst t p b x sc (subst,constrs) = 
    match S.lookup subst x with
      None -> 
        skippable_occurs_check x b t (fun (t',subst) -> 
          let subst' = S.join x (apply_p (Perm.inv p) t') subst in
	  let constrs = 
	    List.map (fun (t,x) -> (t,Susp(Perm.id,Exist Toplevel,x))) constrs in
          unifys_fresh constrs subst' (fun constrs' -> 
            sc (subst',constrs')) []) subst
    | Some t' -> 
        unify1 t (apply_p (Perm.inv p) t') sc (subst, constrs) 
          
  and do_EE_subst (p1,c1,x) (p2,c2,y) sc ans = 
(* seems potentially buggy... *)
    do_subst (Susp(p2,Exist c2,y)) p1 c1 x sc ans 
      
  and unify1 t1 t2 sc ans = 
   let (subst,_) = ans in 
    match S.compress t1 subst, S.compress t2 subst with
      (Name a, Name b) -> 
	if Var.eq a b 
	then sc ans
	else ()
    | (App(c,es),App(d,es')) -> 
	if eq c d 
	then unifys eq es es' sc ans
	else ()
        (* If parameters are equal and disagree only on new names  then they unify, otherwise not *)
    | (Susp(p1,Univ,x),Susp(p2,Univ,y)) -> 
	if Var.eq x y && List.for_all (fun a -> Var.compare x a > 0) (P.disagreement_set p1 p2)
	then sc ans 
	else ()
    | (Susp(p1,Exist b1,x),Susp(p2,Exist b2,y)) -> 
	if Var.eq x y 
        then do_susp p1 p2 x sc ans
	else do_EE_subst (p1,b1,x) (p2,b2,y) sc ans
    | (Susp(p,Exist b,x), t)
    | (t,Susp(p,Exist b,x)) -> 
	do_subst t p b x sc ans
    | (Abs(a,e), Abs(b,e')) -> 
	if Var.eq a b 
	then unify1 e e' sc ans
	else 
	  unify1 e (apply_p (P.trans a b) e') (fun (s,c) -> 
	  unify_fresh1 (Name a) e' s (fun c' -> 
	  sc (s,c')) c) ans
    | _,_ -> ()
  in 
  unify1 t1 t2 sc ans
and unifys aeq es es' = 
    match es, es' with
      [],[] -> succeed
    | e::es,e'::es' -> 
	unify_wrap aeq e e' &&& unifys aeq es es'
    | _,_ -> fail
;;


let unify_fresh a t sc (sub,constrs) =
   unify_fresh1 a t sub (fun constrs' -> sc (sub,constrs')) constrs
;;


let unify = unify_wrap;;


let rec unifys eq es = 
  match es with
    [] -> succeed
  | (t1,t2)::es -> unify eq t1 t2 &&& unifys eq es
;;

let rec constrain_fresh b fvs sc ans =
  match fvs with 
    [] -> sc ans
		(* how to compute the binding constraints of the fvs? *)
  | x::fvs' -> unify_fresh (Name b) (Susp(Perm.id, Exist(Toplevel), x)) (constrain_fresh b fvs' sc) ans
;;	


let rec pp_constrs pp constrs = 
  match constrs with
    [] -> emp
  | (t,x)::constrs -> 
      Internal.pp_term pp t <+>
      text "#" <+>
      text (Var.to_string' x) <:>
      newline <:>
      pp_constrs pp constrs
;;

	



let rec pp_answer sg env fvs (subst,constrs) =
  match fvs with
   [] ->
     pp_constrs Isym.pp_term_sym constrs
   | x::xs ->
     match S.finish subst x with
       None -> pp_answer sg env xs (subst,constrs)
     | Some t ->
         let t' = Translate.untranslate_tm sg env t in
         text (Var.to_string' x) <+>
         text "=" <+>
         Absyn.pp_term t' <+>
         newline <:>
         pp_answer sg env xs (subst, constrs)
;;


let rec pp_constr pp (t,x) =
  Internal.pp_term pp t <+>
  text "#" <+>
  text (Var.to_string' x)
;;


let rec pp_answer_subst sg env (x,Some t) =
  let t' = Translate.untranslate_tm sg env t in
  text (Var.to_string' x) <+>
  text "=" <+>
  Absyn.pp_term t'
;;

let pp_answer_term sg env fvs (subst,constrs) =
  let substs = List.map (fun x -> (x,S.finish subst x)) fvs in
  let substs = List.filter (fun (x,ot) -> ot <> None) substs in
  let answerdocs = List.map (pp_answer_subst sg env) substs in
  let constrdocs = List.map (pp_constr Isym.pp_term_sym) constrs in 
  bracket (sep (comma <:> newline) (answerdocs @ constrdocs))
;;
