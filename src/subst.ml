open Types;;
open Internal;;
open Printer;;



type 'a subst = ('a term) Varmap.t;;


let id = Varmap.empty;;


let lookup s x = 
  if Varmap.mem x s then Some(Varmap.find x s)
  else None
;;



let join x t s = Varmap.add x t s;;


let sub1 x t = join x t id;;




let rec apply_s s t = 
  let h = apply_s s in
  match t with
    Name a -> Name a
  | Abs (a,e) -> Abs(a, h e)
  | App(c,es) -> App(c, List.map h es)
  | Susp(p,vs,x) -> (match lookup s x with 
	Some tm -> apply_p p tm
      | None -> Susp(p,vs,x))
  | Apply(e1,e2) -> Apply(h e1, h e2)
  | Lam(x,e1) ->       
      let x' = Var.rename x in 
      Lam(x',apply_s (join x (Susp(Perm.id,Univ,x')) s) e1)
;;


let rec apply_s_g s g = 
  let h1 = apply_s_g s in
  let h2 = apply_s_p s in
  match g with
    Gtrue -> Gtrue
  | Gfalse -> Gfalse
  | Gatomic(t) -> Gatomic(apply_s s t)
  | Gand(g1,g2) -> Gand(h1 g1, h1 g2)
  | Gor(g1,g2) -> Gor(h1 g1, h1 g2)
  | Gforall(x,g) -> 
      let x' = Var.rename x in 
      Gforall(x',apply_s_g (join x (Susp(Perm.id,Univ,x')) s) g)
  | Gforallstar(x,ty,g) -> 
      let x' = Var.rename x in 
      Gforallstar(x',ty,apply_s_g (join x (Susp(Perm.id,Univ,x')) s) g)
  | Gnew(a,g) -> 
      let a' = Var.rename a in 
      Gnew(a',  apply_p_g (Perm.trans a a') (apply_s_g s g))
  | Gexists(x,g) -> 
      let x' = Var.rename x in 
      Gexists(x', apply_s_g (join x (Susp(Perm.id,Univ,x')) s) g)
  | Gimplies(d,g) -> Gimplies(h2 d, h1 g)
  | Gfresh(t1,t2) -> Gfresh(apply_s s t1, apply_s s t2)
  | Gequals(t1,t2) -> Gequals(apply_s s t1, apply_s s t2)
  | Geunify(t1,t2) -> Geunify(apply_s s t1, apply_s s t2)
  | Gis(t1,t2) -> Gis(apply_s s t1, apply_s s t2)
  | Gcut -> Gcut
  | Guard (g1,g2,g3) -> Guard(h1 g1, h1 g2, h1 g3)
  | Gnot(g) -> Gnot(h1 g)

and apply_s_p s p = 
  let h1 = apply_s_g s in
  let h2 = apply_s_p s in
  match p with
    Dtrue -> Dtrue
  | Datomic(t) -> Datomic(apply_s s t)
  | Dimplies(g,t) -> Dimplies(h1 g, h2 t)
  | Dforall (x,p) -> 
      let x' = Var.rename x in 
      Dforall (x', apply_s_p (join x (Susp(Perm.id,Univ,x')) s) p)
  | Dand(p1,p2) -> Dand(h2 p1,h2 p2)
  | Dnew(a,p) -> 
      let a' = Var.rename a in 
      Dnew(a',  apply_p_p (Perm.trans a a') (apply_s_p s p))
;;


let rec apply_s_t s t = 
  let h1 = apply_s_t s in
  let h2 = apply_s_h s in
  match t with
    Ttrue -> Ttrue
  | Tfalse -> Tfalse
  | Tatomic(ttys,t) -> 
      let ttys' = List.map (fun (t,ty) -> (apply_s s t, ty)) ttys in 
      Tatomic(ttys',apply_s s t)
  | Tforall(x,g) -> 
      let x' = Var.rename x in 
      Tforall(x', apply_s_t (join x (Susp(Perm.id,Univ,x')) s) g)
  | Tnew(a,g) -> 
      let a' = Var.rename a in 
      Tnew(a',subst_name_t  a a'(apply_s_t s g))
  | Timplies(d,g) -> Timplies(h2 d, h1 g)
  | Tfresh(ty1,ty2,t1,t2) -> Tfresh(ty1,ty2,apply_s s t1, apply_s s t2)
  | Tequals(ty,t1,t2) -> Tequals(ty,apply_s s t1, apply_s s t2)

and apply_s_h s p = 
  let h2 = apply_s_h s in
  match p with
    Htrue -> Htrue
  | Hatomic(t) -> Hatomic(apply_s s t)
  | Hexists (x,p) -> 
      let x' = Var.rename x in 
      Hexists (x', apply_s_h (join x (Susp(Perm.id,Univ,x')) s) p)
  | Hand(p1,p2) -> Hand(h2 p1,h2 p2)
  | Hfresh(t1,t2) -> Hfresh(apply_s s t1, apply_s s t2)
  | Hequals(t1,t2) -> Hequals(apply_s s t1, apply_s s t2)
;;


let rec pp_term_subst pp subst t0 = 
    match t0 with 
    Name a -> text (Var.to_string' a)
  | Abs(a,t) -> 
      paren (text (Var.to_string' a) <:> text "." <:> pp_term_subst pp subst t)
  | App(c,es) -> 
      paren ( sep space ((pp c)::(List.map (pp_term_subst pp subst) es)))
  | Susp(p,vs,x) -> (
      match (lookup subst x) with
	None -> Perm.pp_perm p <:> dot <:>  text (Var.to_string' x)
      | Some t -> pp_term_subst pp subst (apply_p p t)
     )
  | Apply(e1,e2) -> pp_term_subst pp subst e1 <+> text "$" <+>pp_term_subst pp subst e2
  | Lam(x,e) -> text "lambda" <+> text (Var.to_string' x) <:> dot <+> pp_term_subst pp subst e
;;


let to_list s = Varmap.to_list s;;


let finish s x = 
  let rec finish_t t = 
    match t with
      Name a -> Name a
    | Abs(a,t) -> Abs (a,finish_t t)
    | App(c,es) -> App(c, List.map finish_t es)
    | Susp(p,vs,x) -> (
	match (lookup s x) with
	  None -> Susp(p,vs,x)
	| Some t -> finish_t (apply_p p t)
       )
    | Apply(e1,e2) -> Apply(finish_t e1, finish_t e2)
    | Lam(x,e) -> 
	let x' = Var.rename x in 
	Lam(x', finish_t (apply_s (sub1 x (Internal.mk_var x')) e))
  in
  match lookup s x with
    Some t -> Some (finish_t t)
  | None -> None
;;


let comp s1 s2 = 
  let s2' = Varmap.map (apply_s s1) s2 in
  Varmap.fold (fun v a s -> if Varmap.mem v s then s else Varmap.add v a s) s1 s2'


let pp_subst pp = Varmap.pp_map (Internal.pp_term pp);;

let apply_p_s p s = 
  Varmap.map (Internal.apply_p p) s


let rec compress t sub = 
  match t with
    Susp(p,Exist b,x) -> 
      (match lookup sub x with 
	  None -> t
	| Some t' -> compress (apply_p p t') sub)
  | Apply(e1,e2) -> 
      (match compress e1 sub with 
	Lam(x,e1') -> compress (apply_s (sub1 x e2) e1') sub
      | _ -> Util.impos "compress")
  | t -> t
;;

