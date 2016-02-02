(* alphaProlog *)
(* Internal symbols *)

open Printer;;

type ty_sym = IntTy
  | BoolTy
  | CharTy
  | DataTy of Unique.uniq * string
  | NameTy of Unique.uniq * string
  | ArrowTy
  | PairTy 
  | AbsTy 
  | PropTy
  | UnitTy
  | ListTy
;;


type term_sym = Int of int
  | Bool of bool
  | Char of char
  | Symb of Unique.uniq * string
  | Nil
  | Cons 
  | Unit
  | Pair
  | Sigma
;;


let ty_sym_eq ts1 ts2 = 
  match (ts1,ts2) with
    DataTy(u1,_),DataTy(u2,_) -> Unique.eq u1 u2
  | NameTy(u1,_),NameTy(u2,_) -> Unique.eq u1 u2
  | _,_ -> ts1 = ts2
;;


let term_sym_eq ts1 ts2 = 
  match (ts1,ts2) with
    Symb(u1,_),Symb(u2,_) -> Unique.eq u1 u2
  | _,_ -> ts1 = ts2
;;



let pp_ty_sym s = 
  match s with
    IntTy -> text "int"
  | BoolTy -> text "bool"
  | CharTy -> text "char"
  | PropTy -> text "prop"
  | DataTy (u,s) -> text s
  | NameTy (u,s) -> text s
  | ArrowTy -> text "->"
  | PairTy -> text "*"
  | AbsTy -> text "<>"
  | UnitTy -> text "()"
  | ListTy -> text "list"
;;


let pp_term_sym s = 
  match s with 
    Int i -> num i
  | Bool b -> if b then text "true" else text "false"
  | Char c -> squotes(escaped_char c)
  | Symb (u,s) -> text s 
  | Sigma -> text "sigma"
  | Nil -> text "nil"
  | Cons -> text "cons"
  | Unit -> text "unit"
  | Pair -> text "pair"
;;

