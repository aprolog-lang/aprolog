(* alphaProlog *)
(* Internal symbols *)

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

val ty_sym_eq : ty_sym -> ty_sym -> bool;;
val term_sym_eq : term_sym -> term_sym -> bool;;

val pp_ty_sym : ty_sym Printer.printer;;
val pp_term_sym : term_sym Printer.printer;;
