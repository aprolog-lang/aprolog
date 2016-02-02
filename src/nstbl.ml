(* Namespace tables *)
open Printer;;

type sym = 
    Child of string * sym
  | Base of string
;;

type path = 
    Root of sym
  | Rel of sym 
;;

type 'a entry = Entry of 'a
              | Ref of 'a * sym
;;

type 'a tval = { abs_path:string list;
		 table:'a tbl;
		 value:(string,'a entry) Hashtbl.t
	       }
and 'a tbl = (string,'a tval) Hashtbl.t;;
type 'a t = {tbl : 'a tval;
             mutable current : string list}
;;

let rec pp_sym s = 
  match s with 
    Child(s,t) -> text s <:> dot <:> pp_sym t
  | Base(t) -> text t
;;

let pp_path s = 
  match s with 
    Root t -> pp_sym t
  | Rel t -> pp_sym t
;;


let ns2s sym = Printer.print_to_string pp_sym sym;;
let p2s sym = Printer.print_to_string pp_path sym;;


let rec get_base sym = 
  match sym with 
    Child(s,t) -> get_base t
  | Base t -> t
;;


let rec sym_concat ss t = 
  match ss with
    [] -> t
  | s::ss -> Child(s,sym_concat ss t)
;;


let rec create_sym tbl s0 c = 
  let rec create' tbl s = 
    match s with
      [] -> 
	Hashtbl.add tbl.table c ({abs_path=s0@[c];
				  table=Hashtbl.create 1;
				  value=Hashtbl.create 1})
    |  (s::t) -> 
	create' (Hashtbl.find tbl.table s) t
  in create' tbl s0
;;


let rec mem_sym tbl s = 
  match s with
    Base x -> 
      Hashtbl.mem tbl.value x
  | Child (s,t) -> 
      try 
	mem_sym (Hashtbl.find tbl.table s) t
      with Not_found -> false
;;


let rec mem_ns tbl s = 
  match s with
    Base x -> 
      Hashtbl.mem tbl.table x 
  | Child (s,t) -> 
      mem_ns (Hashtbl.find tbl.table s) t
;;


let rec find_sym tbl s = 
  match s with
    Base x -> 
      Hashtbl.find tbl.value x
  | Child (s,t) -> 
      find_sym (Hashtbl.find tbl.table s) t
;;


let rec find_ns tbl s = 
  match s with
    Base x -> 
      Hashtbl.find tbl.table x 
  | Child (s,t) -> 
      find_ns (Hashtbl.find tbl.table s) t
;;


let rec add_sym tbl s v = 
  match s with
    Base x ->
      Hashtbl.add tbl.value x v
  | Child (s,t) -> 
      add_sym (Hashtbl.find tbl.table s) t v
;;


let rec add_ns tbl s v = 
  match s with
    Base x ->
      Hashtbl.add tbl.table x v
  | Child (s,t) -> 
      add_ns (Hashtbl.find tbl.table s) t v
;;


let get_abs_path ap e x = 
  match e with 
    Entry _ -> sym_concat ap (Base x)
  | Ref (_,p) -> p


(* Lookup the symbol.  Assuming it exists, return the canonical absolute
  pathname. May succeed if the symbol is not in the table sometimes.  *)
let rec resolve_sym tbl s = 
  match s with
    Base x -> 
      let e = Hashtbl.find tbl.value x in
      get_abs_path tbl.abs_path e x
  | Child (s,t) -> 
      resolve_sym (Hashtbl.find tbl.table s) t
;;


let create i = {tbl = {abs_path = [];
		       value = Hashtbl.create i; 
		       table = Hashtbl.create i};
		current = []}
;;


let rec suffixes l = 
  match l with
    [] -> [[]]
  | x::xs -> l::(suffixes xs)
;;


let prefixes l = suffixes (List.rev l);;
  


let resolve t sym = 
  let handle_path tbl s = 
    if mem_sym tbl s
    then resolve_sym tbl s
     else (raise Not_found)
  in 
  match sym with
    Root s -> handle_path t.tbl s
  | Rel s -> 
      let rec search ps = 
	match ps with
	  [] -> handle_path t.tbl (sym_concat t.current s)
	| p::ps -> 
	    try (handle_path t.tbl (sym_concat p s))
	    with Not_found -> search ps
      in search (prefixes t.current)
;;


let rec sym2list s = 
  match s with
    Child(s,t) -> s::sym2list t
  | Base c -> [c]
;;


let resolve_path t sym = 
  match sym with
    Root s -> 
      if mem_ns t.tbl s 
      then (find_ns (t.tbl) s).abs_path
      else (raise Not_found)
  | Rel s -> 
      let rec search ps = 
	match ps with
	  [] -> 
	    let s' = sym_concat t.current s in 
	    if mem_ns t.tbl s'
	    then (find_ns (t.tbl) s').abs_path
	    else (raise Not_found)
	| p::ps -> 
	    let s' = (sym_concat p s) in
	    if mem_ns t.tbl s' 
	    then (find_ns (t.tbl) s').abs_path
	    else search ps
      in search (prefixes t.current)
;;


let get_sym e = 
  match e with
    Entry a -> a
  | Ref (a,_) -> a

let find t sym = 
  let s = resolve t sym in
  get_sym (find_sym t.tbl s)
;;


let add t sym v = 
  let s' = match sym with 
    Root s -> s 
  | Rel s -> sym_concat t.current s in
  add_sym t.tbl s' (Entry v)
;;


let mem t sym = 
  try let _ = resolve t sym in true
  with Not_found -> false
;;


let enter_ns t c = 
  create_sym t.tbl t.current c;
  t.current <- c::t.current;;


let exit_ns t = 
  match t.current with
    [] -> Util.impos "can't exit toplevel namespace";
  | x::c -> 
      t.current <- c
;;


let abbrev_path t ps n = 
  let rec find_ns tbl ps = 
    match ps with 
      [] -> tbl
    | p::ps -> 
	find_ns (Hashtbl.find tbl.table p) ps 
  in 
  let tval = find_ns t.tbl ps in
  let sym = sym_concat t.current (Base n) in
  add_ns t.tbl sym tval
;;


let rec sym_to_list sym = 
  match sym with
    Base s -> [s]
  | Child (s,sym) -> s::sym_to_list sym
;;


let rec path_to_list current path = 
  match path with 
    Root sym -> sym_to_list sym
  | Rel sym -> sym_to_list (sym_concat current sym)
;;


let rec find_tbls t ss = 
  match ss with 
    [] -> t.table, t.value
  | s::ss -> 
      find_tbls (Hashtbl.find t.table s) ss
      
;;

    
let open_ns t path = 
  let (symtbl,symval),syms = 
    try 
      let p = (path_to_list t.current path) in 
      find_tbls t.tbl p, p
    with Not_found -> 
      let p = (path_to_list [] path) in
      find_tbls t.tbl p, p
  in
  let currtbl,currval = find_tbls t.tbl t.current in
  let mk_ref name v = 
    match v with
      Entry a -> Ref(a,sym_concat syms (Base name))
    | Ref(a,s) -> Ref(a,s)
  in
  Hashtbl.iter (fun name tbl -> Hashtbl.add currtbl name tbl) symtbl;
  Hashtbl.iter (fun name v -> Hashtbl.add currval name (mk_ref name v)) symval
;;




let to_list t = 
  let rec to_list' tbl = 
  Hashtbl.fold (fun b v l -> 
    match v with 
      Entry e -> (sym_concat tbl.abs_path (Base b),e)::l
    | _ -> l) tbl.value []
  (*@ Hashtbl.fold (Util.nyi()) tbl.table []*)
  in to_list' t.tbl
