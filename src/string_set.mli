
type elt = String.t

type t = Set.Make(String).t

val empty : t

val mem : elt -> t -> bool

val add : elt -> t -> t

val singleton : elt -> t

val remove : elt -> t -> t

val union : t -> t -> t

val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a

val elements : t -> elt list                                             

val iter : (elt -> unit) -> t -> unit                        
