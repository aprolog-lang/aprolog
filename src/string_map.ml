module String_map = Map.Make(String)

type key = String.t
             
type 'a t = (bool * String_set.t) Map.Make(String).t
               
let empty = String_map.empty
               
let mem = String_map.mem

let add = String_map.add
            
let remove = String_map.remove

let fold = String_map.fold

let find = String_map.find

let lookup key map =
  match mem key map with
    true -> Some (find key map)
  | false -> None
             
let iter = String_map.iter             
