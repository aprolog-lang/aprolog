
(* Dependency graph's type. *)
type t

(* An empty dependency graph. *)       
val empty : t

(* Given a predicate name |pred| and a dependency graph |dep_graph|, 
in case node |pred| is not already present in the graph, it adds |pred| node and 
return the updated graph. *)
val add_node : string -> t -> t

(* Given two predicate name |pred| |dep| and a dependency graph, it adds a directed edge
between |pred| and |dep| and it returns the updated graph. *)
val add_directed_edge : string -> string -> t -> t

(* Given a set of predicate names |pred_set| and a dependency graph, it returns 
an updated dependency graph and the predicate names to negate required for NE. 
Note that the returned list doesn't contain predicates already negated; it is 
possible because the graph is labelled and it is the reason why a new graph is returned.*)
val get_required_preds : String_set.t -> t -> (t * string list)

(* Given a test, it returns the negative predicate names in it. *)
val get_negative_preds : Absyn.term -> String_set.t

(* Give a clause and a dependency graph, it takes predicate name in the head |phead| 
and all predicate names in the body |deps|, in case there is not a node for them 
in the graph it adds it, adds an edge for each pair (|phead|,|dep|) in
case |dep|<>|phead| and finally return the updated graph. *)
val add_clause_deps : Absyn.term -> t -> t                                         

(* Print every node in the graph with its relative dependencies *)
val print_all_deps : t -> unit
                                     
                                     

              
