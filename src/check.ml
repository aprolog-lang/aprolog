(* Check *)
(* Checks for counterexamples to a specification *)
open Util;;
open Internal;;
open Subst;;
open Types;;
open Unify;;
open Boundsolve;;
open Solve;;
module P = Perm;;
module S = Subst;;



let check_wrap pp sg idx test sc bound ans = 
  let names = Varset.elements (fas_t test) in
  let rec falsify_test test  sc depth ans = 
    match test with
      Ttrue -> ()
    | Tfalse -> sc depth ans
    | Timplies(h,t) -> solve_hyp  h (falsify_test  t sc) depth ans
    | Tfresh(_,_,t1,t2) -> 
        solve_wrap pp idx Dtrue (Gnot(Gfresh(t1,t2))) names (sc depth) ans
    | Tequals(_,t1,t2) -> 
	solve_wrap pp idx Dtrue (Gnot(Gequals(t1,t2))) names (sc depth) ans
    | Tatomic(_,a) when !Flags.negelim && not !Flags.custom_check ->
	if bound < 0
	then solve_wrap pp idx Dtrue (Gatomic(a)) names (sc depth) ans
	else boundsolve pp sg idx Dtrue (Gatomic(a)) names sc bound ans
    | Tatomic(_,a) ->
	if bound < 0
	then solve_wrap pp idx Dtrue (Gnot(Gatomic(a))) names (sc depth) ans
	else boundsolve pp sg idx Dtrue (Gnot(Gatomic(a))) names sc (3*bound+10) ans
    (*| Tatomic(a) -> 
	solve_wrap pp idx Dtrue (Gnot(Gatomic(a))) sc ans*)
    | Tforall(x,t) -> 
	falsify_test 
	  (S.apply_s_t 
	     (S.sub1 x 
		(Susp(Perm.id,Exist(Toplevel),Var.rename x))) t) 
	  sc depth ans
(* TODO: Add bound names and evars to set *)
    | Tnew(a,t) -> 
	falsify_test (subst_name_t a (Var.rename a) t) sc depth ans
  and solve_hyp h sc depth ans = 
    match h with
      Htrue -> sc  depth ans
    | Hand(h1,h2) -> solve_hyp  h1 (solve_hyp  h2 sc)  depth ans
    | Hexists(x,t) ->    solve_hyp 
	  (S.apply_s_h 
	     (S.sub1 x 
		(Susp(Perm.id,Exist(Toplevel),Var.rename x))) t) sc depth ans
    | Hnew(a,h) ->  (* TODO: is this correct? *)
	let b = Var.rename a in
	solve_hyp (subst_name_h a b h) sc depth ans    
    | Hequals(t1,t2) -> unify Isym.term_sym_eq t1 t2 (sc depth) ans
    | Hfresh(t1,t2) -> unify_fresh t1 t2 (sc depth) ans
    | Hatomic(a) -> 
	if bound < 0
	then solve_wrap pp idx Dtrue (Gatomic(a)) names (sc depth) ans
	else boundsolve pp sg idx Dtrue (Gatomic a) names sc bound ans
  in falsify_test test sc bound ans
;; 

let check pp sg idx bound test sc = 
  Var.reset_var();
  check_wrap pp sg idx bound test sc (S.id,[])
;;


let check_ne pp sg idx bound test sc = 
  Var.reset_var();
  check_wrap pp sg idx bound test sc (S.id,[])
;;
