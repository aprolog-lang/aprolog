(* Alpha-Prolog *)
(* Permutations *)
open Types;;
open Printer;;

type perm = (name*name) list;;
type orbits = name list list;;

let id = [];;


let trans a b = [(a,b)];;


let comp p q = p @ q;;


let inv p = List.rev p;;


let rec domain p = 
  match p with 
    [] -> []
  | (a,b)::p -> a::b::domain p
;;


let rec swap (a,b) c = 
  if Var.eq c a then b
  else if Var.eq c b then a
  else c
;;


let exch f x y = f y x


let rec lookup p a = List.fold_right swap p a;;


let rec lookup_inv p a = List.fold_left (exch swap) a p;;


let apply p p' = 
  List.map (fun (a,b) -> (lookup p a, lookup p b)) p'
;;


let subst a b p = 
  let subst_name a b c = 
    if Var.eq a c then b else c
  in
  List.map (fun (c,d) -> (subst_name a b c, subst_name a b d)) p
;;


let disagreement_set p1 p2 = 
  let dom1 = domain p1 in
  let dom2 = domain p2 in
  let dom = dom1 @ dom2 in
  let rng = List.map 
      (fun x -> x, lookup p1 x, lookup p2 x) dom in
  List.map (fun (x,y,z) -> x) 
    (List.filter (fun (x,y,z) -> not(Var.eq y z)) rng)
;;


let supp p = disagreement_set p id;;
  

let eq p q = disagreement_set p q = [];;


let rec pp_perm p = 
  match p with 
    [] -> text "id"
  | [(a,b)] -> text "(" <:> 
      text (Var.to_string' a) <:> 
      text " " <:>
      text (Var.to_string' b) <:>
      text ")"
  | (a,b)::p -> text "(" <:> 
      text (Var.to_string' a) <:> 
      text " " <:>
      text (Var.to_string' b) <:>
      text ")" <:>
      pp_perm p
;;


let from_list l = l;;


let to_list p = p;;


let p2s p = Printer.print_to_string pp_perm p;;


  
(* Calculates reduced form of p 
   reduce : perm -> name list list 
   s.t. result list is a partition of supp(p) *)

exception PermError;;

let impos _ = raise PermError;;

let rec pivot a l = 
  match l with
    [] -> impos "pivot"
  | b::l' -> 
      if a = b 
      then [],l' 
      else 
	let l1,l2 = pivot a l' in 
	b::l1,l2
;;


let rec print_reduced p = 
  match p with 
    [] -> ()
  | o::os -> print_string "(";
      List.iter (fun i -> print_string(string_of_int i); print_string " ") o;
      print_string ")";
      print_reduced os
;;

let reduce p = 
  let swap_reduced a b p = 
    match List.partition (fun l -> List.mem a l || List.mem b l) p with
      [],p -> [a;b]::p (* easy: add new orbit *)
    | [o],p -> 
	(* cases: a and b in o; a in o, b fixed; b in o, a fixed *)
      (match (List.mem a o,List.mem b o) with 
	  true,true -> 
	    let x,y = pivot a o in
	    let z,w = pivot b (y@x) in 
	    (a::z)::(b::w)::p
	| true,false -> 
	    let x,y = pivot a o in 
	    (x@(b::a::y))::p
	| false,true -> 
	    let x,y = pivot b o in 
	    (x@(a::b::y))::p
	| false,false -> impos "reduce")
    | [o1;o2],p -> (* cases: a in o1, b in o2; a in o2, b in o1 *)
	if List.mem a o1 && List.mem b o2 then 
	  let x,y = pivot a o1 in
	  let z,w = pivot b o2 in
	  (x@(b::w))::(z@(a::y))::p
	else if List.mem a o2 && List.mem b o1 then 
	  let x,y = pivot a o2 in
	  let z,w = pivot b o1 in
	  (x@(b::w))::(z@(a::y)) :: p
	else impos "reduce"
    | _ -> impos "reduce"
  in
  let rec reduce' p = 
    match p with
      [] -> []
    | (a,b)::p -> 
       List.filter (fun l -> List.length l > 1) (swap_reduced a b (reduce' p))
   in reduce' p
;;	      

(* expands a reduced-form perm out as a transposition sequence *)
let expand p = 
  let rec expand_orbit l = 
    match l with 
      [] -> []
    | [a] -> []
    | a::b::l -> (a,b)::expand_orbit (b::l)
  in 
  List.concat (List.map expand_orbit p)
;;
  
  
let invert_reduced p = List.map List.rev p;;

let comp_reduced p1 p2 = reduce ((expand p1)@(expand p2));;

(* Finds the "closest" reduced permutation to r.p. p that fixes s. *)
let factor_support s p = 
  let p = List.map (List.filter (fun x -> not(List.mem x s))) p in
  List.filter (fun l -> List.length l > 1) p
;;
  
(* Claim this is most general solution to 
   the equivariant unification problem for pX = qX fixing s. *)
let solve s p q = 
  let qpi = comp_reduced q (invert_reduced p) in
  let p1 = factor_support s qpi in
  (p1);;
  
  
  
let solve s p q = expand (solve s (reduce p) (reduce q));;

let normalize p = expand(reduce p);;
