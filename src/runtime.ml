(* Declarations and code for builtin types, props, functions. *)
open Absyn;;
module I = Isym;;
open Internal;;
open Nstbl;;
open Types;;

(* Abbreviations matching built-in types with their absyn forms. *)
let prop_ty_decl = TypeDefn("prop",[],PropTy);;
let unit_ty_decl = TypeDefn("unit",[],UnitTy);;
let int_ty_decl = TypeDefn("int",[],IntTy);;
let char_ty_decl = TypeDefn("char", [], CharTy);;
let bool_ty_decl = TypeDefn("bool", [], BoolTy);;
(*
let bool_tt_decl1 = FuncDecl("tt",[],BoolTy);;
let bool_tt_decl2 = ClauseDecl(Eq(None,Atomic(Rel(Base("tt")),[]), BoolC true));;
let bool_ff_decl1 = FuncDecl("false",[],BoolTy);;
let bool_ff_decl2 = ClauseDecl(Eq(None,Atomic(Rel(Base("false")),[]), BoolC false));;
*)
let string_ty_decl = TypeDefn("string", [], ListTy (CharTy));;
let b = Var.mkvar' "B";;
let vB = VarTy b;;
let a = Var.mkvar' "A";;
let vA = VarTy a;;
let list_ty_decl = TypeDefn("list", [a], ListTy(vA));;
let list_nil_decl1 = FuncDecl("nil",[],ListTy (vA));;
let list_nil_decl2 = ClauseDecl(Eq(None,Atomic(Rel(Base("nil")),[]), Nil));;
let list_cons_decl1 = FuncDecl("cons",[vA;ListTy(vA)], ListTy(vA));;
let list_cons_decl2 = 
  let x = Var.mkvar' "X" in
  let y = Var.mkvar' "Y" in
  ClauseDecl(Eq(None,Atomic(Rel(Base("cons")),[Var x; Var y]), 
		Cons(Var x, Var y)));;

let binop ty = ArrowTy(ty,ArrowTy(ty,ty));;
let binrel ty = ArrowTy(ty,ArrowTy(ty,PropTy));;


let one_arg f h l = 
  match l with 
    [t] -> 
      h (f t)
  | _ -> Util.impos "expected one argument"
;;

let two_args f1 f2 h l = 
  match l with 
    [t1;t2] -> 
      h (f1 t1) (f2 t2)
  | _ -> Util.impos "dynamic type error: expected two arguments"
;;

let name_arg t = 
  match t with
    Name a -> a
  | _ -> Util.impos "dynamic type error: expected name argument"
;;

let int_arg t = 
  match t with
    App(I.Int i,[]) -> i
  | _ -> Util.impos "dynamic type error: expected integer argument"
;;

let char_arg t = 
  match t with
    App(I.Char i,[]) -> i
  | _ -> Util.impos "dynamic type error: expected integer argument"
;;

let bool_arg t = 
  match t with
    App(I.Bool i,[]) -> i
  | _ -> Util.impos "dynamic type error: expected integer argument"
;;

let unit_arg t = 
  match t with
    App(I.Unit,[]) -> ()
  | _ -> Util.impos"dynamic type error: expected integer argument"
;;


let rec list_arg a_arg t = 
  match t with
    App(I.Nil,[]) -> []
  | App(I.Cons,[t1;t2]) -> (a_arg t1)::(list_arg a_arg t2)
  | _ -> Util.impos "dynamic type error: expected list argument"
;;

let rec abs_arg b_arg t = 
  match t with
    Abs(a,t) -> ( a, b_arg t)
  | _ -> Util.impos "dynamic type error: expected abstraction argument"
;;


let name_result a = Name a;;
let int_result x = App(I.Int x,[]);;
let char_result x = App(I.Char x,[]);;
let bool_result x = App(I.Bool x,[]);;
let unit_result x = App(I.Unit,[]);;
let list_result a_result x = 
  let rec f l = 
    match l with
      [] -> App(I.Nil,[])
    | x::xs -> App(I.Cons,[a_result x;f xs])
  in f x
;;

let abs_result b_result (x,y) = 
  Abs(x, b_result y);;



let list_result a_result x = 
  List.fold_right (fun h t -> App(I.Cons,[a_result h;t])) x (App(I.Nil,[]))
;;


type 'a ty_rec = {arg : I.term_sym term -> 'a; result:'a -> I.term_sym term; ty: ty};;

let name_rec nty = {arg=name_arg;result=name_result;ty=nty};;
let int_rec = {arg=int_arg;result=int_result;ty=IntTy};;
let char_rec = {arg=char_arg;result=char_result;ty=CharTy};;
let unit_rec = {arg=unit_arg;result=unit_result;ty=UnitTy};;
let bool_rec = {arg=bool_arg;result=bool_result;ty=BoolTy};;
let list_rec a_rec = {arg=list_arg a_rec.arg; 
		      result=list_result a_rec.result;
		      ty=ListTy(a_rec.ty)};;
let abs_rec a_rec b_rec = {arg=abs_arg b_rec.arg; 
		      result=abs_result b_rec.result;
		      ty=AbsTy(a_rec.ty,b_rec.ty)};;
let var_rec ty = {arg=(fun x -> x); 
		      result=(fun x -> x);
		      ty=ty};;

let list_rec r = 
  { arg=list_arg r.arg;
    result=list_result r.result;
    ty=ListTy r.ty}
;;


let string_rec = list_rec char_rec;;

let ( ** ) f g x = f (g x);;


let do_unop t1 t s f = 
  BuiltinFuncDecl(s,[t1.ty],t.ty,
		  t.result ** (one_arg t1.arg (f)))
;;


let do_binop t1 t2 t s f = 
  BuiltinFuncDecl(s,[t1.ty;t2.ty],t.ty,
		  t.result ** (two_args t1.arg t2.arg (f)))
;;


let do_bool_unop s f = do_unop bool_rec bool_rec s f;;
let do_bool_binop s f = do_binop bool_rec bool_rec bool_rec s f;;
let do_string_binop s f = do_binop string_rec string_rec string_rec s f;;
let do_int_unop s f = do_unop int_rec int_rec s f;;
let do_int_binop s f = do_binop int_rec int_rec int_rec s f;;
let do_int_binrel s f = do_binop int_rec int_rec bool_rec s f;;

let random_decl = do_int_unop "random" (Random.int);;
let plus_decl = do_int_binop "+" (+);;
Fixity.add_sym "+" 6 Fixity.Right;;
let minus_decl = do_int_binop "-" (-);;
Fixity.add_sym "-" 6 Fixity.Right;;
let times_decl = do_int_binop "*" ( * );;
Fixity.add_sym "*" 7 Fixity.Right;;
let div_decl = do_int_binop "div" (/);;
let mod_decl = do_int_binop "mod" (mod);;
let min_decl = do_int_binop "min" min;;
let max_decl = do_int_binop "max" max;;
let lt_decl = do_int_binrel "<" (<);;
Fixity.add_sym "<" 5 Fixity.Right;;
let leq_decl = do_int_binrel "<=" (<=);;
Fixity.add_sym "<=" 5 Fixity.Right;;
let gt_decl = do_int_binrel ">" (>);;
Fixity.add_sym ">" 5 Fixity.Right;;
let geq_decl = do_int_binrel ">=" (>=);;
Fixity.add_sym ">=" 5 Fixity.Right;;

let and_decl = do_bool_binop "&&" (&&);;
Fixity.add_sym "&&" 4 Fixity.Right;;
let or_decl = do_bool_binop "||" (||);;
Fixity.add_sym "||" 4 Fixity.Right;;
let not_decl = do_bool_unop "neg" (not);;


(* "Impossible" Predicate *)

let fail_prop_decl = PredDecl("fail",[],false,false);;

(* "Call" Predicate *)

let call_prop_decl = PredDecl("call",[PropTy],false,false);;
let call_prop_defn = 
  let vP = Var(Var.mkvar("P")) in 
  ClauseDecl(Implies(vP,Atomic(Rel(Base("call")),[vP])));;

let random_prop_decl = PredDecl("rand",[PairTy(IntTy,IntTy)],false,false);;
let random_prop_defn = 
  let vN = Var(Var.mkvar("N")) in 
  let vX = Var(Var.mkvar("X")) in 
  ClauseDecl(Implies(Is(vX, Atomic(Rel(Base("random")),[vN])),Atomic(Rel(Base("rand")),[Pair(vN,vX)])));;



(* "App" Function *)

let app_func_decl = 
    BuiltinFuncDecl("app",
                    [PairTy(ArrowTy(vA,vB),vA)],vB,
                    (fun [App(I.Pair,[App(sym,ts);x])] -> App(sym,ts@[x])));;


(* Abstraction builder *)

let mk_abs_decl = 
  let vA = VarTy(Var.mkvar("A")) in
  let vB = VarTy(Var.mkvar("B")) in
  BuiltinFuncDecl("mk_abs",[vA;vB],AbsTy(vA,vB),
		  (fun [Name a;t] -> Abs(a,t)));;

let split_abs_decl = 
  let vA = VarTy(Var.mkvar("A")) in
  let vB = VarTy(Var.mkvar("B")) in
  BuiltinFuncDecl("split_abs",[AbsTy(vA,vB)],PairTy(vA,vB),
		  (fun [Abs(a,t)] -> App(I.Pair,[Name a;t]) ));;


let explode s = 
  let n = String.length s in
  let rec expl i = 
    if i < n then 
      String.get s i :: expl (i+1)
    else []
  in expl 0
;;


let implode cs = 
  let n = List.length cs in 
  let s = String.create n in
  let rec impl i cs = 
    if i < n 
    then 
      (String.set s i (List.hd cs); impl (i+1) (List.tl cs))
    else ()
  in impl 0 cs; s
;;



(* Names to strings *)

let name_to_string_decl = 
  let vA = VarTy(Var.mkvar("A")) in
  do_unop (name_rec vA) string_rec "to_string" 
    (fun a -> (explode ((Var.to_string a))))
;;

(* Names from strings *)

let string_to_name_decl = 
  let vA = VarTy(Var.mkvar("A")) in
  do_unop  string_rec  (name_rec vA) "from_string"
    (fun s ->(Var.mkvar' (implode s)))
;;

(* Name comparison *)
let name_compare_decl = 
  let vA = VarTy(Var.mkvar("A")) in
  do_binop (name_rec vA) (name_rec vA) int_rec "names"
    (fun a b -> Var.compare a b)
;;

let name_lt_decl = 
  let vA = VarTy(Var.mkvar("A")) in
  do_binop (name_rec vA) (name_rec vA) bool_rec "lt"
    (fun a b -> Var.compare a b < 0)
;;


(* Getting rid of this impure kind of side-effecting *)
(*
let print_decl = do_unop string_rec unit_rec "print" (fun l -> print_string(implode(l)));;

let read_ln_decl = do_unop unit_rec string_rec "read_line" (fun () -> explode(read_line()));;

let nl_decl = do_unop unit_rec unit_rec "nl" Util.nl;;
*)

let mk_decl rd = {pos = None; rdecl = rd};;

let name_decls = 
    NamespaceDecl("Name",
		   List.map mk_decl 
		     [ name_to_string_decl;
		       string_to_name_decl;
		       name_compare_decl;
		       name_lt_decl;
		     ]
		  );;

let prelude_decls = 
  NamespaceDecl("Prelude",
		List.map mk_decl 
		  [ prop_ty_decl;
		    fail_prop_decl;
		    call_prop_decl;
		    call_prop_defn;
		    app_func_decl;
		    mk_abs_decl;
		    split_abs_decl;
		    unit_ty_decl;
		    string_ty_decl;
		    bool_ty_decl;
(* bool_tt_decl1;
   bool_tt_decl2;*)
(*		    bool_ff_decl1;
   bool_ff_decl2;*)
		    and_decl;
		    or_decl;
		    not_decl;
		    char_ty_decl;
		    list_ty_decl;
		    list_nil_decl1;
		    list_nil_decl2;
		    list_cons_decl1;
		    list_cons_decl2;
		    int_ty_decl;
		    plus_decl;
		    minus_decl;
		    times_decl;
		    random_decl;
		    random_prop_decl;
		    random_prop_defn;
		    div_decl;
		    min_decl;
		    max_decl;
		    lt_decl;
		    leq_decl;
		    gt_decl;
		    geq_decl;
(*		       print_decl;
		       read_ln_decl;
		       nl_decl;*)
		  ]
	       )

let decls = List.map mk_decl 
    [prelude_decls;
     name_decls;
     OpenDirective(Rel(Base("Prelude")));
			     ];;





let bindings = Hashtbl.create 100;;
open Printer;;

let bind u f = Hashtbl.add bindings u f;;


(* Assumes  is ground ( no Susp ) *)
let rec do_sigma t u v = 
  if Internal.eq Isym.term_sym_eq t v then u
  else 
    match t with 
      App(c',ts') -> 
	App(c',List.map (fun t' -> do_sigma t' u v) ts')
    | Name a -> Name a
    | Abs(a,t') -> 
	let a' = Var.rename a in 
	Abs(a',do_sigma (apply_p (Perm.trans a a') t') u v)
    | _ -> Util.impos "ill-formed substitution term"
;;

      

let apply c ts = 
  match c with
    I.Symb (u,_) -> 
      if Hashtbl.mem bindings u 
      then (Hashtbl.find bindings u) ts
      else App(c,ts)
  | I.Sigma -> 
      (match ts with 
	[t; u; v] -> do_sigma t u v
      | _ -> Util.impos "ill-formed substitution term") 
  | c -> App(c,ts)
;;
