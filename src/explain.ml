(* Alpha Prolog *)
open Types;;
open Internal;;
module P = Perm;;
module S = Subst;;
open Printer;;

type 'a constrs = ('a term * var) list;;


type 'a fprobs = ('a term * 'a term) list;;


type 'a answer = ('a S.subst * 'a constrs);;


type 'a fc_transform = ('a -> string) -> ('a -> string);;


type 'a equal = 'a -> 'a -> bool;;


let rec compress t sub = 
  match t with
    Susp(p,Exist b,x) -> 
      (match S.lookup sub x with 
	  None -> t
	| Some t' -> compress (apply_p p t') sub)
  | t -> t
;;


let rec explain_fresh1 t1 t2 sub sc constrs = 
  match compress t1 sub, compress t2 sub with
    Name a,Name b -> 
      if Var.eq a b 
      then ("freshness constraint "^Var.to_string' a^" # "^Var.to_string' b^" is unsolvable")
      else sc constrs
  | Name a,Abs(b,e) -> 
      if Var.eq a b 
      then sc constrs
      else 
	explain_fresh1 t1 e sub sc constrs
  | Susp(p,b,v), Abs (a,t) -> 
      (* try the "good" (non-substitution inducing) case: A # t. *)
      explain_fresh1 t1 t sub sc constrs
  | _,App(c,es) -> 
      explains_fresh (List.map (fun t2 -> (t1,t2)) es) sub sc constrs
  | Susp(p,b,x), Name a 
  | Name a, Susp(p,b,x) ->  
      let a' = (P.lookup (P.inv p) a) in
      sc ((Name a', x)::constrs)
  | Susp(p,b,x), Susp(q,c,y) -> 
      (sc ((Susp(Perm.comp (Perm.inv q) p, b,x), y)::constrs))
  | _,_ -> Util.impos "Internal error: illegal case in freshness unification"

and explains_fresh fs sub sc constrs = 
  match fs with
    [] -> sc constrs 
  | (a,e)::fs -> explain_fresh1 a e sub (explains_fresh fs sub sc) constrs
;;


let do_susp p1 p2 x sc (sub,fs) = 
  let ds = P.disagreement_set p1 p2 in
  sc (sub, (List.map (fun a -> (Name a,Susp(P.id,Univ,x))) ds)@fs)
;;




(* Extended occurs check: check that x does not occur in t, that
   all Uvars in t are permitted for x, and constrain all Evars in 
   t to be as constrained as x is.  *)
let rec occurs_check x c t sc subst : string = 
  match compress t subst with
    Name _ -> sc (t,subst)
  | Abs(a,e) -> 
      occurs_check x c e (fun (t',subst) -> 
      sc (Abs(a,t'), subst)) subst
  | App(f,es) -> 
      occurs_checks x c es (fun (ts,subst) -> 
      sc (App(f,es),subst)) subst
  | Susp(p,Univ,y) -> 
      if bconstr_satisfies y c
      then sc (t,subst)
      else ("universal variable "^Var.to_string y^" escapes into older existential variable "^Var.to_string x)
  | Susp(p,Exist c',y) -> 
      if Var.eq x y 
      then ("circular occurrence of variable "^Var.to_string' x)
      else 
        if bconstr_leq c' c (* If lhs more constrained than rhs *)
	then sc (t,subst) (* continue *)
	else (sc (Susp(p,Exist c, y),subst)) 
and occurs_checks x c ts sc subst = 
  match ts with
    [] -> sc ([],subst)
  | t::ts -> 
      occurs_check x c t (fun (t',subst) -> 
      occurs_checks x c ts (fun (ts',subst) -> 
	sc (t'::ts',subst)) subst) subst
;;


let explain_wrap pp eq t1 t2 sc ans = 
  
  let rec do_subst t p b x sc (subst,constrs) = 
    match S.lookup subst x with
      None -> 
	occurs_check x b t (fun (t',subst) -> 
	  sc (S.join x (apply_p (P.inv p) t') subst, constrs))
	  subst
    | Some t' -> 
	explain1 t (apply_p p t') sc (subst, constrs) 
	  
  and do_EE_subst (p1,c1,x) (p2,c2,y) sc ans = 
    do_subst (Susp(p2,Exist c2,y)) p1 c1 x sc ans 
      
  and explain1 t1 t2 sc ans = 
    match compress t1 (fst ans), compress t2 (fst ans) with
      (Name a, Name b) -> 
	if Var.eq a b 
	then sc ans
	else ("names "^Var.to_string' a^" and "^Var.to_string' b^" differ")
    | (Abs(a,e), Abs(b,e')) -> 
	if Var.eq a b 
	then explain1 e e' sc ans
	else 
	  explain1 e (apply_p (P.trans a b) e') 
	    (fun (s,c) -> sc (s,(Name a,e')::c)) ans
    | (App(c,es),App(d,es')) -> 
	if not(eq c d )
	then ("symbols "^Printer.pp pp c^" and "^Printer.pp pp d^" differ")
	else explains es es' sc ans
    | (Susp(p1,Univ,x),Susp(p2,Univ,y)) -> 
	(* TODO: This is less general than it could be: if we know a # X 
           then it's ok if a in ds(p,p') *)
	if Var.eq x y 
	then 
          if P.disagreement_set p1 p2 = []
          then sc ans 
          else ("Universal variable "^Var.to_string' x
		^" used with incompatible suspensions "
		^Perm.p2s p1^" and "^Perm.p2s p2)
	else ("Universal variables "^Var.to_string' x
	    ^" and "^Var.to_string' y^" are distinct")
    | (Susp(p1,Exist b1,x),Susp(p2,Exist b2,y)) -> 
	if Var.eq x y 
	then do_susp p1 p2 x sc ans
	else do_EE_subst (p1,b1,x) (p2,b2,y) sc ans
    | (Susp(p,Exist b,x), t) -> 
	do_subst t p b x sc ans
    | (t,Susp(p,Exist b,x)) -> 
	do_subst t p b x sc ans
    | t1,t2 -> (Printer.print_to_string (Internal.pp_term pp) t1
		^" and "
		^Printer.print_to_string (Internal.pp_term pp) t2
		^" are incompatible")	  
  and explains es es' sc ans = 
    match es, es' with
      [],[] -> sc ans
    | e::es,e'::es' -> 
	explain1 e e' (fun ans -> 
	explains es es' sc ans) ans
    | _,_ -> "different length argument lists"
	  
  in 
  explain1 t1 t2 sc ans
;;


let explain_fresh a t sc (sub,constrs) = 
  explain_fresh1 a t sub (fun constrs' -> sc (sub,constrs')) constrs
;;


let explain pp eq e1 e2 sc (sub,constrs) = 
  explain_wrap pp eq e1 e2 
    (fun (sub,fs) -> 
      explains_fresh fs sub 
	(fun constrs' -> sc (sub,constrs'))
	constrs) (sub,[])
;;


let rec explains pp eq es sc = 
  match es with
    [] -> sc
  | (t1,t2)::es -> explain pp eq t1 t2 (explains pp eq es sc)
;;

