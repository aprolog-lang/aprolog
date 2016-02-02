(* Alpha Prolog *)
(* Device-independent printers *)

type out_interface = {out : string -> unit;
		      in_space : bool;
		      indent_level : int};;


type doc = out_interface -> out_interface;;


type 'a printer = 'a -> doc;;


let set_in_space b oi = 
  {out=oi.out;
    in_space=b;
    indent_level=oi.indent_level}
;;


let set_indent_level i oi = 
  {out = oi.out;
    in_space=oi.in_space;
    indent_level=i}
;;
    


let escaped_text s oi = 
  oi.out (String.escaped s);
  set_in_space false oi
;;


let text s oi = 
  oi.out s;
  set_in_space false oi
;;


let escaped_char c oi = 
  oi.out (Char.escaped c);
  set_in_space false oi
;;

(* Common symbols *)
let arrow = text "->";;
let dot = text ".";;
let eq = text "=";;
let eqeq = text "==";;
let defeq = text ":=";;
let bar = text "|";;
let comma = text ",";;
let darrow = text "=>";;
let larrow = text ":-";;
let question = text "?";;
let cut = text "!";;
let amp = text "@";;
let colon = text ":";;
let semi = text ";";;
let star = text "*";;
let hash = text "#";;
let slash = text "/";;
let backslash = text "\\";;
let underscore = text "_";;
let space = text " ";;
let tilde = text "~";;


let num i = text (string_of_int i);;


let (<+>) d1 d2 oi = 
  let oi = d1 oi in 
  if oi.in_space 
  then 
    d2 (set_in_space false oi)
  else (oi.out " "; 
        d2 (set_in_space true oi))
;;


let (<:>) d1 d2 oi = 
  d2(d1(oi))
;;


let indent i d oi = 
  set_indent_level oi.indent_level (d (set_indent_level (oi.indent_level+i) oi))
;;


let newline oi = (text "\n" <:> text (String.make oi.indent_level ' ')) oi;;

  
let emp oi = oi;;


let paren d = 
  text "(" <:>
  d <:>
  text ")"
;;


let angle d = 
  text "<" <:>
  d <:>
  text ">"
;;


let bracket d = 
  text "[" <:>
  d <:>
  text "]"
;;


let braces d = 
  text "{" <:>
  d <:>
  text "}"
;;
 

let quotes d = 
  text "\"" <:>
  d <:>
  text "\""
;;
 

let squotes d = 
  text "\'" <:>
  d <:>
  text "\'"
;;
 

let comment d = 
  text "(*" <:>
  d <:>
  text "*)"
;;
 

let rec sep d ds = 
  match ds with 
    [] -> emp
  | [d1] -> d1
  | d'::ds' -> d' <:> d <:> (sep d ds')
;;


let rec hcat ds = 
  match ds with 
    [] -> emp
  | d'::ds' -> d' <:> (hcat ds')
;;


let rec vcat ds = 
  match ds with 
    [] -> emp
  | d'::ds' -> d' <:> newline <:> (vcat ds')
;;


let doc_to_channel  oc doc = 
  doc {out = output_string oc; 
	in_space = false;
	indent_level = 0};
  ()
;;


let doc_to_string doc = 
  let s = ref "" in
  doc {out = (fun t -> s := !s^t);
       in_space = false;
	indent_level = 0};
  !s
;;


let print_to_channel pr a oc = doc_to_channel oc (pr a);;


let print_to_string pr a = doc_to_string (pr a);;


let pp = print_to_string;;
