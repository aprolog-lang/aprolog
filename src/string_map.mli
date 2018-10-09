
type key = String.t

type 'a t = (bool * String_set.t) Map.Make(String).t

val empty : (bool * String_set.t) t

val mem : key -> (bool * String_set.t) t -> bool

val add : key -> (bool * String_set.t) -> (bool * String_set.t) t -> (bool * String_set.t) t

val remove : key -> (bool * String_set.t) t -> (bool * String_set.t) t

val fold : (key -> (bool * String_set.t) -> (bool * String_set.t) -> (bool * String_set.t)) -> (bool * String_set.t) t ->
           (bool * String_set.t) -> (bool * String_set.t)

val find : key -> (bool * String_set.t) t -> (bool * String_set.t)

val lookup : key -> (bool * String_set.t) t -> (bool * String_set.t) option
                                               
val iter : (key -> (bool * String_set.t) -> unit) -> (bool * String_set.t) t -> unit
