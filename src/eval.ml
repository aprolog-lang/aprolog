(* alphaProlog *)
(* Evaluation: functions at base types *)
(* Just pushes the do_app function everywhere and complains if term 
   is non-ground. *)

open Internal;;
open Subst;;

let rec eval do_app subst t = 
  let h = eval do_app subst in
  match t with
    App(c,es) -> do_app c (List.map h es)
  | Name(a) -> Name(a)
  | Abs(a,t) -> Abs(a, h t)
  | Susp(p,b,v) -> 
      (match lookup subst v with
	None -> Util.runtime_error "The right-hand side of an \"is\" expression must be ground when evaluated"
      | Some t' -> h (apply_p p t')
      )
  | Apply(e1,e2) -> (
      match h e1 with
	Lam(x,e1') -> h (apply_s (sub1 x e2) e1')
      | _ -> Util.impos "eval"
     )
  | Lam(x,e1) -> Lam(x,e1)
;;
