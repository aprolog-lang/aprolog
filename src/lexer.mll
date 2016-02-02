{
open Fixity;;
open Parser;;
open Lineno;;
open Nstbl;;

let cdepth = ref 0;;
let lit = ref "";;

let lex_sym s = 
  try 
    match List.assoc s !symtbl with
      1,Right-> INFIXR1 s
    | 2,Right-> INFIXR2 s
    | 3,Right-> INFIXR3 s
    | 4,Right-> INFIXR4 s
    | 5,Right-> INFIXR5 s
    | 6,Right-> INFIXR6 s
    | 7,Right-> INFIXR7 s
    | 8,Right-> INFIXR8 s
    | 9,Right-> INFIXR9 s

    | 1,Left -> INFIXL1 s
    | 2,Left -> INFIXL2 s
    | 3,Left -> INFIXL3 s
    | 4,Left -> INFIXL4 s
    | 5,Left -> INFIXL5 s
    | 6,Left -> INFIXL6 s
    | 7,Left -> INFIXL7 s
    | 8,Left -> INFIXL8 s
    | 9,Left -> INFIXL9 s

    | 1,Non -> INFIXN1 s
    | 2,Non -> INFIXN2 s
    | 3,Non -> INFIXN3 s
    | 4,Non -> INFIXN4 s
    | 5,Non -> INFIXN5 s
    | 6,Non -> INFIXN6 s
    | 7,Non -> INFIXN7 s
    | 8,Non -> INFIXN8 s
    | 9,Non -> INFIXN9 s

    | _ -> Util.impos "Expected number between 1 and 9 for fixity"
  with 
    Not_found -> ID(s)
;;

let lex_qual_id s =
  let n = String.length s in
  let rec id i j  = 
    if j = n then Base(String.sub s i (j-i))
    else if String.get s j = '.' then Child(String.sub s i (j-i),id (j+1) (j+1))
    else id i (j+1)
  in id 0 0
;;

exception LexFail of string
}

let alpha = ['A'-'Z' 'a'-'z']
let upper = ['A'-'Z']
let lower = ['a'-'z']
let digit = ['0'-'9']

let id = (alpha|'_')(alpha|digit|'''|'_')*
let infix_id = (('|'|'*'|'+'|'<'|'>'|'='|'-'|'&'
               |'^'|'$'|'#'|'@'|'!'|'~'|'?'|'\\')+)
let qual_id = ((id)'.')+((id|infix_id))
let ws = [' ''\t''\r']
let char = (alpha)|(digit)|(infix_id)|'('|')'|'{'|'}'|'['|']'|'.'|' '|','|'_'|'-'|'/'|'\\'|':'

rule lex =
  parse
        ['/']['*']            { flat_comment lexbuf }
      | ['*']['/']            { raise (LexFail "unmatched close comment")}
      |	['(']['*']            { cdepth := !cdepth + 1;
				comment lexbuf }
      | ['*'][')']            { raise (LexFail "unmatched close comment")}
      | ['\n']                { Lineno.incr (); lex lexbuf }
      |	['%'][^'\n']*         { lex lexbuf }
      | ws+                   { lex lexbuf }
      | digit+                { INT(int_of_string(Lexing.lexeme lexbuf)) }
      | "-"digit+             { INT(int_of_string(Lexing.lexeme lexbuf)) }
      | "="                   { EQ }
      | "~="                  { EUNIFY }
      | "is"                  { IS }
      | "|"                   { BAR }
      | "["                   { LBRACK }
      | "]"                   { RBRACK }
      | "{"                   { LBRACE }
      | "}"                   { RBRACE }
      | "("                   { LPAREN }
      | ")"                   { RPAREN }
      | "."                   { DOT }
      | ","                   { COMMA }
      | "=>"                  { DARROW }
      | "->"                  { ARROW }
      | "-->"                 { DCG_ARROW }
      | "@"                   { AMP }
      | ":-"                  { LARROW }
      | "?"                   { QUESTION } 
      | "!"                   { CUT }
      | ":"                   { COLON }
      | ";"                   { SEMI }
      | "#"                   { HASH }
      | "\\"                  { BACKSLASH }
      | "/"                   { SLASH }
      | "::"                  { CONS }
      | "_"                   { UNDERSCORE }
      | "~"                   { TILDE }
      | "$"                   { DOLLAR }

      | "namespace"           { NAMESPACE }
      | "infixl"              { INFIXL }
      | "infixn"              { INFIXN }
      | "infixr"              { INFIXR }
      | "type"                { TYPE }
      |	"name_type"           { NAME_TYPE }
      |	"cnst"                { CNST }
      |	"func"                { FUNC }
      |	"pred"                { PRED }
      | "prop"                { PROP }
      | "#use"                { USE }
      | "#trace"              { TRACE }
      |	"#type"               { TYPEQ }
      |	"#quit"               { QUIT }
      |	"#open"               { OPEN }
      |	"#help"               { HELP }
      | "#check"              { CHECK }
      | "#validate"           { VALIDATE }
      | "#invalidate"         { INVALIDATE }
(*      | "#gen"                { GEN_DIR }*)

      | "lambda"              { LAMBDA }
      | "forall"              { FORALL }
      | "exists"              { EXISTS }
      | "new"                 { NEW }
      | "true"                { TRUE }
      | "false"               { FALSE }
      | "not"                 { NOT }
      |	"\'"char"\'"          { CHAR(String.get (Lexing.lexeme lexbuf) 1) }
      | "\'\\\"\'"            { CHAR('\"') }
      | "\'\\n\'"             { CHAR('\n') }
      | "\'\\t\'"             { CHAR('\t') }
      | "\'\\\\\'"            { CHAR('\\') }
      | "\'\\\'\'"            { CHAR('\'') }
      | "\""                  { literal lexbuf }
      |	qual_id               { let s = Lexing.lexeme lexbuf in
	                        QUAL_ID(Rel(lex_qual_id s)) }
      | id                    { ID(Lexing.lexeme lexbuf) }
      |	'('(infix_id)')'      { let s = Lexing.lexeme lexbuf in 
	                        ID(String.sub s 1 (String.length s - 2)) }
      | infix_id              { lex_sym (Lexing.lexeme lexbuf) }
      | eof                   { EOF }
      | _                     { raise (LexFail "illegal character")}

and flat_comment =
parse
         
        ['*']['/']            { lex lexbuf } 
      | ['\n']                { Lineno.incr (); flat_comment lexbuf }
      | _                     { flat_comment lexbuf }
      | eof                   { raise (LexFail "unclosed comment") } 
      
and comment =
parse
        ['(']['*']            { cdepth := !cdepth + 1; comment lexbuf }
      |	['*'][')']            { cdepth := !cdepth - 1;
				if !cdepth = 0 
				then lex lexbuf
				else comment lexbuf} 
      | ['\n']                { Lineno.incr (); comment lexbuf }
      | _                     { comment lexbuf }
      | eof                   { raise (LexFail "unclosed comment") } 
      



and literal = 
parse 
        char                  { lit := !lit ^ Lexing.lexeme lexbuf;
			        literal lexbuf }
      |	"\\\n"                { literal lexbuf }
      | "\\\""                { lit := !lit ^ "\"" ; literal lexbuf }
      | "\\n"                 { lit := !lit ^ "\n" ; literal lexbuf }
      | "\\t"                 { lit := !lit ^ "\t" ; literal lexbuf }
      | "\\\\"                { lit := !lit ^ "\\" ; literal lexbuf }
      | "\\\'"                { lit := !lit ^ "\'" ; literal lexbuf }
      | "\""                  { let s = !lit in  lit := ""; LITERAL(s) }

{
}
