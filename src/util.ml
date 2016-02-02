
exception Impos of string;;
exception Error of string;;
exception RuntimeError of string;;
exception NYI;;


type 'a equal = 'a -> 'a -> bool;;


let warning msg = print_endline ("Warning: "^msg);;


let error msg = raise (Error msg);;


let runtime_error msg = raise (RuntimeError msg);;


let nyi () = raise NYI;;


let impos s = raise (Impos s);;


let debug = ref false;;


let do_trace i f = if !Flags.trace >= i then f();;


let nl () = print_string "\n";;


let split p s = 
  let n = String.length s in
  let rec tokenize i j = (* 0 <= i <= j <= n *)
    if j = n || p(String.get s i)
    then (String.sub s i (j-i))::skip j
    else (* j < n*) tokenize i (j+1)
  and skip j = (* 0 <= j <= n *)
    if j = n then []
    else if p(String.get s j) then skip(j+1)
    else tokenize j j
  in tokenize 0 0
;;


let rec zip l m = 
  match l,m with
    [],[] -> []
  | x::l,y::m -> (x,y)::zip l m
  | _,_ -> impos "zip: lists must have same length"
;;


let rec unzip l = 
  match l with 
    [] -> [],[]
  | (x,y)::l ->
      let l1,l2 = unzip l in 
      x::l1,y::l2
;;


let rec allpairs l m = 
  match l with 
    [] -> [] 
  | x::xs -> (List.map (fun y -> (x,y)) m)@(allpairs xs m)
;;


let collect f l = List.concat (List.map f l);;

let map_partial f l = 
  List.concat 
    (List.map (fun x -> 
      match f x with None -> [] | Some y -> [y]) l)
;;


let rec tabulate f n = 
  if n <= 0 then []
  else tabulate f (n-1) @ [f n]
