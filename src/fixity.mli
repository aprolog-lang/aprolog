type direction = Left | Right | Non

val symtbl : (string * (int * direction)) list ref;;
val add_sym : string -> int -> direction -> unit;;
