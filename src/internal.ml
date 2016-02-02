(* Alpha Prolog *)
(* Internal representation of untyped terms *)
open Types;;
open Printer;;


type perm = Perm.perm;;


type bconstr = Toplevel
             | Constrained of var list
;;

let bconstr_leq c1 c2 = 
  match c1,c2 with
    _,Toplevel -> true
  | Constrained l, Constrained l' ->
   List.length l <= List.length l'
  | _,_ -> false
;;


let bconstr_satisfies x c = 
  match c with
    Toplevel -> true
  | Constrained l -> List.exists (Var.eq x) l
;;

type bind = Exist of bconstr
          | Univ
;;





type 'a term = App of 'a * 'a term list
  | Abs of  name * 'a term
  | Name of name
  | Susp of perm * bind * var 
  | Lam of var * 'a term 
  | Apply of 'a term * 'a term
;;


type 'a goal = 
(* propositions *)
    Gtrue
  | Gfalse
  | Gatomic of 'a term
  | Gand of 'a goal * 'a goal
  | Gor of 'a goal * 'a goal
  | Gimplies of 'a prog * 'a goal
(* first-order quantifiers *)
  | Gforall of var * 'a goal
  | Gforallstar of var * Types.ty * 'a goal
  | Gexists of var * 'a goal (* bool for toplevel exists *)
  | Gnew of name * 'a goal
(* term predicates *)
  | Gfresh of 'a term * 'a term
  | Gequals of 'a term * 'a term
  | Gis of 'a term * 'a term 
  | Geunify of 'a term * 'a term
(* control *)
  | Gcut
  | Guard of 'a goal * 'a goal * 'a goal
  | Gnot of 'a goal

and 'a prog = 
(* first-order program clauses *)
    Dtrue
  | Datomic of 'a term
  | Dimplies of 'a goal * 'a prog
  | Dforall of var * 'a prog
  | Dand of 'a prog * 'a  prog
(* "new" quantifier *)
  | Dnew of name * 'a prog
;;

type 'a test = Ttrue
  | Tfalse
  | Tequals of Types.ty * 'a term * 'a term
  | Tfresh of Types.ty * Types.ty * 'a term * 'a term
  | Tatomic of ('a term * Types.ty) list * 'a term
  | Timplies of 'a hyp * 'a test
  | Tforall of var * 'a test
  | Tnew of name * 'a test
and 'a hyp = Hatomic of 'a term
  | Hequals of 'a term * 'a term
  | Hfresh of 'a term * 'a term
  | Hand of 'a hyp * 'a hyp
  | Htrue
  | Hexists of var * 'a hyp
  | Hnew of name * 'a hyp


let mk_var v = Susp(Perm.id,Univ,v);;
let rec find_head term = 
  match term with
    App(Isym.Symb (u,_),t2) -> u
  | _ -> Util.impos("index.ml: ill-formed program head clause")
;;

let pp_bconstr c = 
  match c with 
    Toplevel -> bracket (text "*")
  | Constrained l -> bracket (sep (text " ") (List.map Var.pp_var l))
;;

let pp_bind b = 
  match b with 
    Exist c -> pp_bconstr c
  | Univ -> emp

let pp_term pp t = 
  let rec pp_term t =
  match t with 
    Name a -> Var.pp_var a
  | Abs(a,t) -> paren (Var.pp_var a <:> text "\\" <:> pp_term t)
  | App(c,es) -> paren ( sep space ((pp c)::(List.map pp_term es)))
  | Apply(e1,e2) -> paren (pp_term e1 <+> text "$" <+> pp_term e2)
  | Lam(v,e) -> paren (text "lambda" <+> Var.pp_var v <:> dot <+> pp_term e)
  | Susp(p,b,x) -> 
      Perm.pp_perm p 
	<:> text "."
	<:> Var.pp_var x
	<:> pp_bind b
  in pp_term t
;;


let rec pp_goal pp g0 = 
  let pp_g g0 = pp_goal pp g0 in

  match g0 with 
    Gtrue -> text "true"
  | Gfalse -> text "false"
  | Gatomic t -> pp_term pp t
  | Gand (g1,g2) -> 
      paren (pp_g g1 <:> text "," <+> pp_g g2)
  | Gor (g1,g2) -> 
      paren (pp_g g1 <:> text ";" <+> pp_g g2)
  | Gforall (x,g) -> 
      text "forall" <+> 
      text (Var.to_string' x) <:>
      text "." <:>
      pp_g g
  | Gforallstar (x,_,g) -> 
      text "forall*" <+> 
      text (Var.to_string' x) <:>
      text "." <:>
      pp_g g
  | Gexists (x,g) -> 
      text "exists" <+> 
      text (Var.to_string' x) <:>
      text "." <:>
      pp_g g
  | Gnew (x,g) -> 
      text "new" <+> 
      text (Var.to_string' x) <:>
      text "." <:>
      pp_g g
  | Gimplies (p,g) -> 
      paren (
      pp_prog pp p <+>
      text "=>" <+>
      pp_g g
     )
  | Gfresh (t1,t2) -> 
      pp_term pp t1 <+>
      text "#" <+>
      pp_term pp t2
  | Gequals (t1,t2) ->
      pp_term pp t1 <+>
      text "=" <+>
      pp_term pp t2
  | Geunify (t1,t2) ->
      pp_term pp t1 <+>
      text "~=" <+>
      pp_term pp t2
  | Gis (t1,t2) -> 
      pp_term pp t1 <+>
      text "is" <+>
      pp_term pp t2
  | Gcut -> text "!"
  | Guard (g1,g2,g3) -> 
      paren (
      pp_g g1 <+>
      text "->" <+>
      pp_g g2 <+>
      text "|" <+>
      pp_g g3
     )
  | Gnot(g) -> text "not" <:> paren (pp_g g)
and pp_prog pp p0 = 
  let pp_p p0 = pp_prog pp p0 in
  match p0 with
    Dtrue -> text "true"
  | Datomic (t) -> pp_term pp  t
  | Dimplies (g,p) -> 
      paren (
      pp_p p <+>
      text ":-" <+>
      pp_goal pp g
     )
  | Dand (p1,p2) -> 
      paren (
      pp_p p1 <:>
      text "," <+>
      pp_p p2
     )
  | Dforall (x,p) -> 
      text "forall" <+> 
      text (Var.to_string' x) <:>
      text "." <:>
      pp_p p
  | Dnew (a,p) -> 
      text "new" <+> 
      text (Var.to_string' a) <:>
      text "." <:>
      pp_p p
;;

let rec pp_test pp p0 = 
  let pp_t x = pp_test pp x in
  match p0 with    
    Ttrue -> text "true"
  | Tfalse -> text "false"
  | Tatomic (_,t) -> pp_term pp  t
  | Timplies (h,t) -> 
      paren (
      pp_hyp pp h <+>
      text "=>" <+>
      pp_t t
     )
  | Tforall (x,p) -> 
      text "forall" <+> 
      text (Var.to_string' x) <:>
      text "." <:>
      pp_t p
  | Tnew (a,p) -> 
      text "new" <+> 
      text (Var.to_string' a) <:>
      text "." <:>
      pp_t p
  | Tfresh (_,_,t1,t2) -> 
      pp_term pp t1 <+>
      text "#" <+>
      pp_term pp t2
  | Tequals (_,t1,t2) ->
      pp_term pp t1 <+>
      text "=" <+>
      pp_term pp t2

and pp_hyp pp h0 = 
  let pp_h h = pp_hyp pp h in
  match h0 with 
    Htrue -> text "true"
  | Hatomic t -> pp_term pp t
  | Hfresh (t1,t2) -> 
      pp_term pp t1 <+>
      text "#" <+>
      pp_term pp t2
  | Hequals (t1,t2) ->
      pp_term pp t1 <+>
      text "=" <+>
      pp_term pp t2
  | Hand (h1,h2) -> 
      paren (pp_h h1 <:> text "," <+> pp_h h2)
  | Hexists (x,h) -> 
      text "exists" <+> 
      text (Var.to_string' x) <:>
      text "." <:>
      pp_h h
  | Hnew (x,h) -> 
      text "new" <+> 
      text (Var.to_string' x) <:>
      text "." <:>
      pp_h h
;;

let t2s t = Printer.print_to_string (pp_term Nstbl.pp_sym) t


let rec supp t = 
  match t with 
    App(c,ts) -> Varset.unions (List.map supp ts)
  | Abs(a,t) -> Varset.remove a (supp t) 
  | Name a -> Varset.singleton a
  | Susp (p,b,v) -> Varset.from_list (Perm.disagreement_set p Perm.id)
  | Lam(x,e) -> supp(e)
  | Apply(e1,e2) -> Varset.union(supp e1)(supp e2)
;;


let rec fas t = 
  match t with 
    App(c,ts) -> Varset.unions (List.map fas ts)
  | Abs(a,t) -> Varset.union (Varset.singleton a) (fas t) 
  | Name a -> Varset.singleton a
  | Susp (p,b,v) -> Varset.from_list (Perm.disagreement_set p Perm.id)
  | Lam(x,e) -> fas(e)
  | Apply(e1,e2) -> Varset.union (fas e1) (fas e2)
;;



let rec fas_g g = 
  match g with 
    Gtrue|Gfalse -> Varset.empty 
  | Gatomic (t) -> fas t
  | Gand(g1,g2) -> Varset.union (fas_g g1) (fas_g g2)
  | Gor(g1,g2) -> Varset.union (fas_g g1) (fas_g g2)
  | Gimplies(p1,g2) -> Varset.union (fas_p p1) (fas_g g2)
  | Gforall(v,g) -> fas_g g
  | Gforallstar(v,_,g) -> fas_g g
  | Gexists (v,g) -> fas_g g
  | Gnew (a,g) -> Varset.remove a (fas_g g)
  | Gfresh(t1,t2) -> Varset.union (fas t1) (fas t2)
  | Gequals(t1,t2) -> Varset.union (fas t1) (fas t2)
  | Geunify(t1,t2) -> Varset.union (fas t1) (fas t2)
  | Gis(t1,t2) -> Varset.union (fas t1) (fas t2)
  | Gcut -> Varset.empty
  | Guard(g1,g2,g3) -> Varset.unions [fas_g g1;fas_g g2;fas_g g3]
  | Gnot(g) -> fas_g g

and fas_p p = 
  match p with 
    Dtrue -> Varset.empty 
  | Datomic t -> fas t
  | Dimplies (g1,p2) -> Varset.union (fas_g g1) (fas_p p2)
  | Dforall (v,p) -> fas_p p
  | Dand (p1,p2) -> Varset.union (fas_p p1) (fas_p p2)
(* "new" quantifier *)
  | Dnew (a,p) -> Varset.remove a (fas_p p)
;;

let rec fas_t t = 
  match t with
    Ttrue|Tfalse -> Varset.empty
  | Tatomic(_,t) -> fas t
  | Tfresh(_,_,t1,t2) -> Varset.union (fas t1) (fas t2)
  | Tequals(_,t1,t2) -> Varset.union (fas t1) (fas t2)
  | Timplies(h,t) -> Varset.union (fas_h h) (fas_t t)
  | Tforall (v,t) ->  (fas_t t)
  | Tnew (a,t) -> Varset.remove a (fas_t t)
and fas_h h = 
  match h with
    Htrue -> Varset.empty
  | Hfresh(t1,t2) -> Varset.union (fas t1) (fas t2)
  | Hequals(t1,t2) -> Varset.union (fas t1) (fas t2)
  | Hatomic t -> fas t
  | Hand (h1,h2) -> Varset.union (fas_h h1) (fas_h h2)
  | Hexists(v,h) ->   fas_h h
  | Hnew (a,h) -> Varset.remove a (fas_h h)
;;

let rec fvs t = 
  match t with 
    App(c,ts) -> Varset.unions (List.map fvs ts)
  | Abs(a,t) -> fvs t 
  | Name a -> Varset.empty
  | Susp (p,b,v) -> Varset.singleton v
  | Apply(e1,e2) -> Varset.union (fvs e1) (fvs e2)
  | Lam(x,t) -> Varset.remove x (fvs t) 
;;


let rec fvs_g g = 
  match g with 
    Gtrue|Gfalse -> Varset.empty 
  | Gatomic (t) -> fvs t
  | Gand(g1,g2) -> Varset.union (fvs_g g1) (fvs_g g2)
  | Gor(g1,g2) -> Varset.union (fvs_g g1) (fvs_g g2)
  | Gimplies(p1,g2) -> Varset.union (fvs_p p1) (fvs_g g2)
  | Gforall(v,g) -> Varset.remove v (fvs_g g)
  | Gforallstar(v,_,g) -> Varset.remove v (fvs_g g)
  | Gexists (v,g) -> Varset.remove v (fvs_g g)
  | Gnew (v,g) -> fvs_g g
  | Gfresh(t1,t2) -> Varset.union (fvs t1) (fvs t2)
  | Gequals(t1,t2) -> Varset.union (fvs t1) (fvs t2)
  | Geunify(t1,t2) -> Varset.union (fvs t1) (fvs t2)
  | Gis(t1,t2) -> Varset.union (fvs t1) (fvs t2)
  | Gcut -> Varset.empty
  | Guard(g1,g2,g3) -> Varset.unions [fvs_g g1;fvs_g g2;fvs_g g3]
  | Gnot(g) -> fvs_g g

and fvs_p p = 
  match p with 
    Dtrue -> Varset.empty 
  | Datomic t -> fvs t
  | Dimplies (g1,p2) -> Varset.union (fvs_g g1) (fvs_p p2)
  | Dforall (v,p) -> Varset.remove v (fvs_p p)
  | Dand (p1,p2) -> Varset.union (fvs_p p1) (fvs_p p2)
(* "new" quantifier *)
  | Dnew (a,p) -> fvs_p p
;;

let rec fvs_t t = 
  match t with
    Ttrue|Tfalse -> Varset.empty
  | Tatomic(_,t) -> fvs t
  | Tfresh(_,_,t1,t2) -> Varset.union (fvs t1) (fvs t2)
  | Tequals(_,t1,t2) -> Varset.union (fvs t1) (fvs t2)
  | Timplies(h,t) -> Varset.union (fvs_h h) (fvs_t t)
  | Tforall (v,t) -> Varset.remove v (fvs_t t)
  | Tnew (v,t) -> (fvs_t t)
and fvs_h h = 
  match h with
    Htrue -> Varset.empty
  | Hfresh(t1,t2) -> Varset.union (fvs t1) (fvs t2)
  | Hequals(t1,t2) -> Varset.union (fvs t1) (fvs t2)
  | Hatomic t -> fvs t
  | Hand (h1,h2) -> Varset.union (fvs_h h1) (fvs_h h2)
  | Hexists(v,h) ->   Varset.remove v (fvs_h h)
  | Hnew (a,h) -> (fvs_h h)
;;


let rec apply_p p t =
  let h = apply_p p in
  match t with
    Name a -> Name(Perm.lookup p a)
  | Abs (a,e) -> Abs(Perm.lookup p a, h e)
  | App(c,es) -> App(c, List.map h es)
  | Susp(p',vs,x) -> 
      Susp(Perm.comp p p', vs, x)
  | Apply(e1,e2) -> Apply(h e1, h e2)
  | Lam(x,e1) -> Lam(x,h e1)
;;


(* applies a permutation to names but not to suspensions *)
let rec apply_p' p t =
  let h = apply_p' p in
  match t with
    Name a -> Name(Perm.lookup p a)
  | Abs (a,e) -> Abs(Perm.lookup p a, h e)
  | App(c,es) -> App(c,List.map h es)
  | Susp(p',vs,x) -> Susp(Perm.apply p p', vs, x)
  | Apply(e1,e2) -> Apply(h e1, h e2)
  | Lam(x,e1) -> Lam(x,h e1)
;;


let rec apply_p_g p g = 
  let h0 =   
    if !Flags.suspensions 
    then apply_p p  
    else apply_p' p in
  let h1 = apply_p_g p in
  let h2 = apply_p_p p in
  match g with
    Gtrue -> Gtrue
  | Gfalse -> Gfalse
  | Gatomic(t) -> Gatomic(h0 t)
  | Gand(g1,g2) -> Gand(h1 g1, h1 g2)
  | Gor(g1,g2) -> Gor(h1 g1, h1 g2)
  | Gforall(x,g) -> Gforall(x, h1 g) 
  | Gforallstar(x,ty,g) -> Gforallstar(x, ty,h1 g) 
  | Gnew(x,g) -> Gnew(Perm.lookup p x, h1 g) 
  | Gexists(x,g) -> Gexists(x, h1 g)
  | Gimplies(d,g) -> Gimplies(h2 d, h1 g)
  | Gfresh(t1,t2) -> Gfresh(h0 t1,h0 t2)
  | Gequals(t1,t2) -> Gequals(h0 t1, h0 t2)
  | Geunify(t1,t2) -> Geunify(h0 t1, h0 t2)
  | Gis(t1,t2) -> Gis(h0 t1, h0 t2)
  | Gcut -> Gcut
  | Guard (g1,g2,g3) -> Guard(h1 g1, h1 g2, h1 g3)
  | Gnot(g) -> Gnot(h1 g)

and apply_p_p p q = 
  let h0 =   
    if !Flags.suspensions 
    then apply_p p  
    else apply_p' p
  in 
  let h1 = apply_p_g p in
  let h2 = apply_p_p p in
  match q with
    Dtrue -> Dtrue
  | Datomic(t) -> Datomic(h0 t)
  | Dimplies(g,t) -> Dimplies(h1 g, h2 t)
  | Dforall (x,p) -> Dforall (x, h2 p)
  | Dand(p1,p2) -> Dand(h2 p1,h2 p2)
  | Dnew(a,p') -> Dnew(Perm.lookup p a,h2 p') 
;;



(* substitutes one name for another... experimental *)
let rec subst_name a b t =
  let h = subst_name a b in
  match t with
    Name c -> if Var.eq a c then Name b else Name c
  | Abs (c,e) -> Abs((if Var.eq a c then b else c), h e)
  | App(c,es) -> App(c,List.map h es)
  | Susp(p,vs,x) -> Susp(Perm.subst a b p, vs, x)
  | Apply(e1,e2) -> Apply(h e1, h e2)
  | Lam(x,e1) -> Lam(x,h e1)
;;


let rec subst_name_g a b g = 
  let h0 = subst_name a b in
  let h1 = subst_name_g a b in
  let h2 = subst_name_p a b in
  match g with
    Gtrue -> Gtrue
  | Gfalse -> Gfalse
  | Gatomic(t) -> Gatomic(h0 t)
  | Gand(g1,g2) -> Gand(h1 g1, h1 g2)
  | Gor(g1,g2) -> Gor(h1 g1, h1 g2)
  | Gforall(x,g) -> Gforall(x, h1 g) 
  | Gforallstar(x,ty,g) -> Gforallstar(x, ty,h1 g) 
  | Gnew(x,g) -> Gnew(x, h1 g) 
  | Gexists(x,g) -> Gexists(x, h1 g)
  | Gimplies(d,g) -> Gimplies(h2 d, h1 g)
  | Gfresh(t1,t2) -> Gfresh(h0 t1,h0 t2)
  | Gequals(t1,t2) -> Gequals(h0 t1, h0 t2)
  | Geunify(t1,t2) -> Geunify(h0 t1, h0 t2)
  | Gis(t1,t2) -> Gis(h0 t1, h0 t2)
  | Gcut -> Gcut
  | Guard (g1,g2,g3) -> Guard(h1 g1, h1 g2, h1 g3)
  | Gnot(g) -> Gnot(h1 g)

and subst_name_p a b q = 
  let h0 = subst_name a b in
  let h1 = subst_name_g a b in
  let h2 = subst_name_p a b in
  match q with
    Dtrue -> Dtrue
  | Datomic(t) -> Datomic(h0 t)
  | Dimplies(g,t) -> Dimplies(h1 g, h2 t)
  | Dforall (x,p) -> Dforall (x, h2 p)
  | Dand(p1,p2) -> Dand(h2 p1,h2 p2)
  | Dnew(a,p') -> Dnew(a,h2 p') 
;;



let rec subst_name_t a b t = 
  let h0 = subst_name a b in
  let h1 = subst_name_t a b in
  let h2 = subst_name_h a b in
  match t with
    Ttrue -> Ttrue
  | Tfalse -> Tfalse
  | Tatomic(vtys,t) -> Tatomic(vtys,h0 t)
  | Tforall(x,t) -> Tforall(x, h1 t) 
  | Tnew(x,t) -> Tnew(x, h1 t) 
  | Timplies(h,t) -> Timplies(h2 h, h1 t)
  | Tfresh(ty1,ty2,t1,t2) -> Tfresh(ty1,ty2,h0 t1,h0 t2)
  | Tequals(ty,t1,t2) -> Tequals(ty,h0 t1, h0 t2)
 
and subst_name_h a b h = 
  let h0 = subst_name a b in
  let h1 = subst_name_t a b in
  let h2 = subst_name_h a b in
  match h with
    Htrue -> Htrue
  | Hatomic(t) -> Hatomic(h0 t)
  | Hexists (x,p) -> Hexists (x, h2 p)
  | Hnew (x,p) -> Hnew (x, h2 p)
  | Hand(p1,p2) -> Hand(h2 p1,h2 p2)
  | Hfresh(t1,t2) -> Hfresh(h0 t1,h0 t2)
  | Hequals(t1,t2) -> Hequals(h0 t1, h0 t2)
;;



let rec eq aeq t u = 
  match t,u with 
    App (a,ts),App(a',ts') -> 
      aeq a a' && List.fold_left2 (fun v t u -> eq aeq t u && v) true ts ts'
  | Abs(n,t),Abs(n',t') -> Var.eq n n' && eq aeq t t'
  | Name(n), Name(n') -> Var.eq n n'
  | Susp(pi,_,v),Susp(pi',_,v') -> Perm.eq pi pi' && Var.eq v v'
  | _ -> false
;;
