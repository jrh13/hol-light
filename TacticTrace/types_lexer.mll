{
  open Types_parser

  exception LexError of string
}

let whitespace = [' ' '\t' '\n' '\r']
let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let identifier = letter (letter | digit | '_' | '.')*
let type_var = '\'' letter (letter | digit | '_' | '.')*

rule token = parse
  | whitespace+        { token lexbuf }
  | "->"               { ARROW }
  | "("                { LPAREN }
  | "*"                { STAR }
  | ")"                { RPAREN }
  | ","                { COMMA }
  | ":"                { COLON }
  | "?"                { QUESTION_MARK }
  | type_var as s      { TYPEVAR s }
  | identifier as s    { IDENT s }
  | eof                { EOF }
  | _ as c             { raise (LexError ("Unexpected character: " ^ String.make 1 c)) }
