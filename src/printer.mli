(* Alpha Prolog *)
(* Device-independent printers *)

type doc;;
type 'a printer = 'a -> doc;;

val emp   : doc;;
val (<+>) : doc -> doc -> doc;;
val (<:>) : doc -> doc -> doc;;
val sep   : doc -> doc list -> doc;;
val hcat  : doc list -> doc;;
val vcat  : doc list -> doc;;

val indent : int -> doc -> doc;;

val newline : doc;;
val space   : doc;;

val text  : string -> doc;;
val escaped_text : string -> doc;;
val num   : int -> doc;;
val escaped_char  : char -> doc;;

val arrow      : doc;;
val dot        : doc;;
val eq         : doc;;
val eqeq       : doc;;
val defeq      : doc;;
val bar        : doc;;
val comma      : doc;;
val darrow     : doc;;
val larrow     : doc;;
val question   : doc;;
val cut        : doc;;
val colon      : doc;;
val amp        : doc;;
val semi       : doc;;
val star       : doc;;
val hash       : doc;;
val slash      : doc;;
val backslash  : doc;;
val underscore : doc;;
val space      : doc;;
val tilde      : doc;;

val paren   : doc -> doc;;
val angle   : doc -> doc;;
val bracket : doc -> doc;;
val braces  : doc -> doc;;
val quotes  : doc -> doc;;
val squotes  : doc -> doc;;
val comment  : doc -> doc;;

val doc_to_string  : doc -> string;;
val doc_to_channel : out_channel -> doc -> unit;;

val print_to_string  : 'a printer -> 'a -> string;;
val print_to_channel : 'a printer -> 'a -> out_channel -> unit;;
val pp               : 'a printer -> 'a -> string;;
