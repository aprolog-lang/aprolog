
let lineno_stack = ref (1,[]);;


let incr () = 
  let (lineno,s) = !lineno_stack in
  lineno_stack := (lineno+1, s)
;;


let reset () = lineno_stack := (1,[]);;


let enter_file filename = 
  let (lineno,s) = !lineno_stack in
  lineno_stack := (1,(filename,lineno)::s);;


let exit_file () = 
  match !lineno_stack with
    (_,(_,lineno)::s) -> lineno_stack := (lineno,s)
  | _ -> Util.impos "exit_file: not inside a file"
;;


let filename () = 
  let (lineno,s) = !lineno_stack in 
  match s with
    [] -> "<input>"
  | (f,_)::_ -> f
;;


let lineno () = 
  let (lineno,s) = !lineno_stack in 
  lineno
;;

