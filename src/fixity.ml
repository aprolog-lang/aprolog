(* Alpha Prolog *)
(* Fixity declarations and state *)

type direction = Left | Right | Non

(* maps names to fixity * direction *)
let symtbl = ref [];;


let add_sym s prec fixity = 
  symtbl := (s,(prec,fixity))::!symtbl
;;

