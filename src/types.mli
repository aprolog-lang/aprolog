(* Alpha-Prolog *)
(* Basic type definitions shared among several modules *)

type var  = Var.var;;
type name = Var.var;;
type sym  = string;;

type name_sort = Nstbl.path;;
type data_sort = Nstbl.path;;

type kind = TypeK
  | NameK (* illegal as result kind *)
  | ArrowK of kind * kind
;;

type ty = IdTy of Nstbl.path
  | NameTy of name_sort
  | DataTy of data_sort * ty list 
  | UnitTy
  | PairTy of ty * ty
  | AbsTy of ty * ty
  | ListTy of ty
  | VarTy of var
  | UnderscoreTy
  | IntTy
  | CharTy
  | BoolTy
  | PropTy 
  | ArrowTy of ty * ty
;;
