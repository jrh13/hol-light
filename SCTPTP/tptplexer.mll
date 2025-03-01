{
  open Tptpparser
  open Tptphelpers
  exception EOF
}

(* Lexing rules *)

rule tokenize = parse
  (* whitespace and comments *)

  | '\n' { Lexing.new_line lexbuf ; tokenize lexbuf }
  | [' ' '\t'] { tokenize lexbuf }
  | '%' { line_comment lexbuf }
  | "/*" { block_comment lexbuf }

  (* delimiters *)
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | ',' { COMMA }
  | '.' { DOT }
  | ':' { COLON }
  
  (* operators *)
  | '+' { PLUS }
  | '*' { TIMES }
  | '/' { DIVIDE }
  | '-' { MINUS }
  
  (* operators: logical *)
  | '&' { AND }
  | '|' { OR }
  | '~' { NOT }
  | '!' { BANG }
  | '?' { QUESTION }
  | '#' { HASH }
  | "<=>" { IFF }
  | "=>" { IMPLIES }
  | "<=" { IMPLIEDBY }
  | "<~>" { NIFF }
  | "~|" { NOR }
  | "~&" { NAND }
  | "-->" { GENTZEN_ARROW }

  (* equality *)
  | '=' { EQUAL }
  | "!=" { NOTEQUAL }

  (* keywords *)
  | "fof" { FOF }
  | "inference" { INFERENCE }
  | "introduced" { INTRODUCED }
  | "file"  { FILE }
  | "theory" { THEORY }
  | "creator" { CREATOR }
  | "unknown" { UNKNOWN }
  | "$fof" { DOLLAR_FOF }
  | "$fot" { DOLLAR_FOT }

  (* numerics *)
  | ['0' - '9']+ { NAT (int_of_string (Lexing.lexeme lexbuf)) }
  | ['0' - '9']+ '.' ['0' - '9']* { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }

  (* identifiers *)
  | "$$" ['a'-'z' 'A'-'Z' '0'-'9' '_']* as s { DOLLAR_DOLLAR_WORD s }
  | "$" ['a'-'z' 'A'-'Z' '0'-'9' '_']* as s { DOLLAR_WORD s }
  | "'" [^'\'']* "'" as s {
      let inner = remove_quotes s in
      SINGLE_QUOTED inner
    }
  | "\"" _* "\"" as s {
      let inner = remove_quotes s in
      DOUBLE_QUOTED inner
  }
  | ['a' -'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as id {LOWER_WORD id}
  | ['A' -'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as id {UPPER_WORD id}

  | eof { EOF }

and line_comment = parse
  | '\n'  { Lexing.new_line lexbuf ; tokenize lexbuf }
  | eof   { EOF }
  | _     { line_comment lexbuf }

and block_comment = parse
  | "*/"  { tokenize lexbuf }
  | eof   { EOF }
  | _     { block_comment lexbuf }
 