open OcamlTypes

let parse_string s =
  let lexbuf = Lexing.from_string s in
  try
    Types_parser.typ_expr Types_lexer.token lexbuf
  with
  | Parsing.Parse_error ->
      let pos = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "Parse error at line %d, character %d\n"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
      exit 1
  | Types_lexer.LexError msg ->
      Printf.eprintf "Lexer error: %s\n" msg;
      exit 1

let () =
  let test_cases = [
    "'a -> 'b";
    "('x -> 'y) -> 'z";
    "int -> string";
    "'a -> 'b -> 'c";
    "('a -> 'b) -> ('c -> 'd)";
    "'a * 'b";
    "'a * 'b -> 'c";
    "('a * 'b) -> 'c";
    "myarg:string -> unit";
    "?myarg:string -> unit";
    "'a list";
    "'a list -> 'b list";
    "int * string -> bool";
    "'a -> ('a * 'b) list -> 'b";
    "('a, 'b) func";
    "(int -> int, int, int) pp";
    "int * int * int";
    "int * (int * int)";
    "(int * int) * int";
  ] in

  List.iter (fun s ->
    Printf.printf "Input: %s\n" s;
    let typ = parse_string s in
    Printf.printf "Parsed: %s\n" (string_of_typ typ);
    Printf.printf "---\n"
  ) test_cases
