
module A = Absyn

type t = (bool * String_set.t) String_map.t
  
let empty = String_map.empty

let add_node pred dep_graph =
  if String_map.mem pred dep_graph
  then dep_graph
  else String_map.add pred (false,String_set.empty) dep_graph
;;
            
let add_directed_edge pred dep dep_graph =
  if String_map.mem pred dep_graph
  then
    let dep_graph = add_node dep dep_graph in
    let (already_gen,prev_deps) = String_map.find pred dep_graph in
    let updated_deps = String_set.add dep prev_deps in
    String_map.add pred (already_gen,updated_deps) dep_graph
  else String_map.add pred (false,(String_set.singleton dep)) dep_graph
;;

(* let rec get_deps pred dep_graph = *)
(*   let deps = String_map.find pred dep_graph in *)
(*   String_set.fold (fun pred' deps' -> get_deps pred' dep_graph |> String_set.union deps') deps deps *)
(* ;; *)
                         
let get_required_preds pred_set dep_graph =
  let rec helper pred (dep_graph,res) = 
    match String_map.lookup pred dep_graph with
    | None 
    | Some (true,_) -> (dep_graph,res)
    | Some (false,deps) ->
       let res = String_set.add pred res in
       let dep_graph = String_map.add pred (true,deps) dep_graph in
       String_set.fold helper deps (dep_graph,res)
  in                       
  let (dep_graph,required_preds) = String_set.fold helper pred_set (dep_graph,String_set.empty) in
  (dep_graph,String_set.elements required_preds)
;;
                      
let print_all_deps dep_graph =
  String_map.iter
    (fun p (is_already_generated,deps) ->
     print_string (p ^ " (already_gen: " ^ (string_of_bool is_already_generated)  ^ ")\n");
     String_set.iter
       (fun elt -> print_string (" ---> " ^ elt ^ "\n")) deps) dep_graph
           
let rec get_negative_preds term =
  match term with
    A.Atomic(Root(sym),_) | A.Atomic(Rel(sym),_) ->
                           let pred_name = Nstbl.get_base sym in 
                           if Str.string_partial_match (Str.regexp "not_") pred_name 0
                           then String_set.singleton pred_name
                           else String_set.empty
  | A.Implies(t1,t2) | A.Pair(t1,t2) | A.And(t1,t2) | A.Or(t1,t2) ->
                                   String_set.union
                                     (get_negative_preds t1) (get_negative_preds t2)
  | A.New(_,_,t) -> get_negative_preds t
  | _ -> String_set.empty                           
                            

let add_clause_deps clause dep_graph =
  let rec add_deps pred goal dep_graph1 =
    match goal with
      A.Atomic(Root(sym),_)
    | A.Atomic(Rel(sym),_) when pred <> Nstbl.get_base sym ->
       add_directed_edge pred (Nstbl.get_base sym) dep_graph1
    | A.And(g1,g2)
    | A.Or(g1,g2)
    | A.Pair(g1,g2) -> add_deps pred g2 (add_deps pred g1 dep_graph1)
    | A.Forall(_,_,tm)
    | A.Exists(_,_,tm)
    | A.New(_,_,tm) -> add_deps pred tm dep_graph1
    | _ -> (* print_string ("CatchAll2: " ^ (A.t2s goal) ^ "\n");  *)dep_graph1 in  
  match clause with
  | A.Implies(g,Atomic(Root(sym),_))
  | A.Implies(g,Atomic(Rel(sym),_)) ->
     let p = Nstbl.get_base sym in
     let dep_graph = add_node p dep_graph in
     add_deps p g dep_graph
  | _ -> (* print_string ("CatchAll: " ^ (Absyn.t2s clause) ^ "\n"); *) dep_graph
                      
  
  
                  
