
(* Just a way to independently run the TPTP parser for testing *)

let parse_file filename = 
  let file = In_channel.open_text filename in
  let lexbuf = Lexing.from_channel file in
  try
    Tptpparser.tptp_file Tptplexer.tokenize lexbuf
  with
  | _ ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Printf.eprintf "Parse error at line %d, column %d\n"
        pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol);
      [];;
let test () = 
  parse_file "test.p";;
