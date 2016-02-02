(* alphaProlog *)
(* Tries (for namespaces) *)

type ('a,'b) trie = Trie of ('b option ref * ('a,('a,'b) trie) Hashtbl.t);;


let create i = Trie (ref None,Hashtbl.create i);;


let rec add (Trie (vr,t)) l v = 
  match l with
    [] -> vr := Some v
  | x::l -> 
      if not(Hashtbl.mem t x)
      then Hashtbl.add t x (create 1);
      add (Hashtbl.find t x) l v
;;


let rec remove (Trie (vr,t)) l = 
  match l with
    [] -> vr := None
  | x::l -> 
      if not(Hashtbl.mem t x)
      then ()
      else remove (Hashtbl.find t x) l
;;


let rec mem (Trie (vr,t)) l = 
  match l with
    [] -> 
      (match !vr with 
	Some t -> true
      | None -> false)
  | x::l -> Hashtbl.mem t x && mem (Hashtbl.find t x) l
;;


let rec find_opt (Trie (vr,t)) l = 
  match l with
    [] -> !vr
  | x::l -> find_opt (Hashtbl.find t x) l
;;


let find t l = 
  match find_opt t l with 
    None -> raise Not_found
  | Some t -> t
;;


