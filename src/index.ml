(* Very simple term indexing for proof search *)

(* For each toplevel program clause, we parse it to find the clause head 
   symbol and add it to the program maintained for that symbol.  That
   program is just a conjunction of all such programs seen so far.
   We optimize out "true", which is a pretty pointless top-level goal anyway.
   Compound programs constructed with "and" are factored out.  Quantifiers 
   are ignored, we'll determine whether quantification is correct through
   unification.
*)

open Internal;;
open Types;;


type 'a t = (Unique.uniq,'a prog) Hashtbl.t;;


let create i = Hashtbl.create i;;


let rec add idx p0 = 
  (* Find head clause symbol.  If it's an And clause, break down into parts. *)
  let rec index_prog p = 
    match p with 
      Dtrue -> () (* no action needed *)
    | Datomic(t) ->  
	let sym = find_head t in
	if Hashtbl.mem idx sym
	then 
	  let p' = Hashtbl.find idx sym in
	  Hashtbl.add idx sym (Dand (p', p0))
	else Hashtbl.add idx sym p0
    | Dimplies(g,p) -> index_prog p
    | Dforall(x,p) -> index_prog p
    | Dand(p1,p2) -> add idx p1; add idx p2
    | Dnew(a,p) -> index_prog p
  in index_prog p0
;;


let lookup idx t = 
  let sym = find_head t in
  if Hashtbl.mem idx sym 
  then Hashtbl.find idx sym
  else Dtrue
;;


