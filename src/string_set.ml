module String_set = Set.Make(String)

type elt = String.t

type t = Set.Make(String).t

let empty = String_set.empty

let mem = String_set.mem

let add = String_set.add

let remove = String_set.remove
            
let singleton = String_set.singleton

let union = String_set.union

let fold = String_set.fold    

let elements = String_set.elements             

let iter = String_set.iter                 
