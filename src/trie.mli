(* alphaProlog *)
(* Tries (for namespaces) *)

type ('a,'b) trie;;

val create : int -> ('a,'b) trie;;
val add    : ('a,'b) trie -> 'a list -> 'b -> unit;;
val remove : ('a,'b) trie -> 'a list -> unit;;
val mem    : ('a,'b) trie -> 'a list -> bool;;

val find     : ('a,'b) trie -> 'a list -> 'b;;
val find_opt : ('a,'b) trie -> 'a list -> 'b option;;

