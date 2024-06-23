(* camlp5r pa_extend.cmo q_MLast.cmo *)
(* $Id: pa_o.ml 1271 2007-10-01 08:22:47Z deraugla $ *)
(* Copyright (c) INRIA 2007 *)

open Pcaml;

Pcaml.syntax_name.val := "OCaml";
Pcaml.no_constructors_arity.val := True;

(* camlp5r pa_lexer.cmo *)
(* $Id: plexer.ml 1402 2007-10-14 02:50:31Z deraugla $ *)
(* Copyright (c) INRIA 2007 *)

(* ------------------------------------------------------------------------- *)
(* Added by JRH as a backdoor to change lexical conventions.                 *)
(* ------------------------------------------------------------------------- *)

value jrh_lexer = ref False;

value no_quotations = ref False;
value error_on_unknown_keywords = ref False;

value dollar_for_antiquotation = ref True;
value specific_space_dot = ref False;

value force_antiquot_loc = ref False;

(* The string buffering machinery *)

value rev_implode l =
  let s = String.create (List.length l) in
  loop (String.length s - 1) l where rec loop i =
    fun
    [ [c :: l] -> do { String.unsafe_set s i c; loop (i - 1) l }
    | [] -> s ]
;

(* The lexer *)

type context =
  { after_space : mutable bool;
    dollar_for_antiquotation : bool;
    specific_space_dot : bool;
    find_kwd : string -> string;
    line_cnt : int -> char -> unit;
    set_line_nb : unit -> unit;
    make_lined_loc : (int * int) -> string -> Ploc.t }
;

value err ctx loc msg =
  Ploc.raise (ctx.make_lined_loc loc "") (Plexing.Error msg)
;

(* ------------------------------------------------------------------------- *)
(* JRH's hack to make the case distinction "unmixed" versus "mixed"          *)
(* ------------------------------------------------------------------------- *)

value is_uppercase s = String.uppercase s = s;
value is_only_lowercase s = String.lowercase s = s && not(is_uppercase s);

value jrh_identifier find_kwd id =
  let jflag = jrh_lexer.val in
  if id = "set_jrh_lexer" then
    (let _ = jrh_lexer.val := True in ("",find_kwd "true"))
  else if id = "unset_jrh_lexer" then
    (let _ = jrh_lexer.val := False in ("",find_kwd "false"))
  else
  try ("", find_kwd id) with
   [ Not_found ->
        if not(jflag) then
          if is_uppercase (String.sub id 0 1) then ("UIDENT", id)
          else ("LIDENT", id)
        else if is_uppercase (String.sub id 0 1) &&
        is_only_lowercase (String.sub id 1 (String.length id - 1))
(***** JRH: Carl's alternative version
        then ("UIDENT", id)
        else if is_uppercase (String.sub id 0 1) then ("LIDENT", "__uc_"^id)
        else ("LIDENT", id)];
 *****)
        then ("UIDENT", id) else ("LIDENT", id)];

(* ------------------------------------------------------------------------- *)
(* Back to original file with the mod of using the above.                    *)
(* ------------------------------------------------------------------------- *)

value keyword_or_error ctx loc s =
  try ("", ctx.find_kwd s) with
  [ Not_found ->
      if error_on_unknown_keywords.val then
        err ctx loc ("illegal token: " ^ s)
      else ("", s) ]
;

value stream_peek_nth n strm =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some x else None
    | [_ :: l] -> loop (n - 1) l ]
;

value rec ident =
  lexer
  [ [ 'A'-'Z' | 'a'-'z' | '0'-'9' | '_' | ''' | '\128'-'\255' ] ident! | ]
;
value rec ident2 =
  lexer
  [ [ '!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
      '%' | '.' | ':' | '<' | '>' | '|' | '$' ]
      ident2!
  | ]
;

value rec ident3 =
  lexer
  [ [ '0'-'9' | 'A'-'Z' | 'a'-'z' | '_' | '!' | '%' | '&' | '*' | '+' | '-' |
      '.' | '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '|' | '~' | ''' |
      '$' | '\128'-'\255' ] ident3!
  | ]
;

value binary = lexer [ '0' | '1' ];
value octal = lexer [ '0'-'7' ];
value decimal = lexer [ '0'-'9' ];
value hexa = lexer [ '0'-'9' | 'a'-'f' | 'A'-'F' ];

value end_integer =
  lexer
  [ "l"/ -> ("INT_l", $buf)
  | "L"/ -> ("INT_L", $buf)
  | "n"/ -> ("INT_n", $buf)
  | -> ("INT", $buf) ]
;

value rec digits_under kind =
  lexer
  [ kind (digits_under kind)!
  | "_" (digits_under kind)!
  | end_integer ]
;

value digits kind =
  lexer
  [ kind (digits_under kind)!
  | -> raise (Stream.Error "ill-formed integer constant") ]
;

value rec decimal_digits_under =
  lexer [ [ '0'-'9' | '_' ] decimal_digits_under! | ]
;

value exponent_part =
  lexer
  [ [ 'e' | 'E' ] [ '+' | '-' | ]
    '0'-'9' ? "ill-formed floating-point constant"
    decimal_digits_under! ]
;

value number =
  lexer
  [ decimal_digits_under "." decimal_digits_under! exponent_part ->
      ("FLOAT", $buf)
  | decimal_digits_under "." decimal_digits_under! -> ("FLOAT", $buf)
  | decimal_digits_under exponent_part -> ("FLOAT", $buf)
  | decimal_digits_under end_integer! ]
;

value rec char_aux ctx bp =
  lexer
  [ "'"/
  | _ (char_aux ctx bp)!
  | -> err ctx (bp, $pos) "char not terminated" ]
;

value char ctx bp =
  lexer
  [ "\\" _ (char_aux ctx bp)!
  | "\\" -> err ctx (bp, $pos) "char not terminated"
  | ?= [ _ '''] _! "'"/ ]
;

value any ctx buf =
  parser bp [: `c :] -> do { ctx.line_cnt bp c; $add c }
;

value rec string ctx bp =
  lexer
  [ "\""/
  | "\\" (any ctx) (string ctx bp)!
  | (any ctx) (string ctx bp)!
  | -> err ctx (bp, $pos) "string not terminated" ]
;

value rec qstring ctx bp =
  lexer
  [ "`"/
  | (any ctx) (qstring ctx bp)!
  | -> err ctx (bp, $pos) "quotation not terminated" ]
;

value comment ctx bp =
  comment where rec comment =
    lexer
    [ "*)"
    | "*" comment!
    | "(*" comment! comment!
    | "(" comment!
    | "\"" (string ctx bp)! [ -> $add "\"" ] comment!
    | "'" (char ctx bp) comment!
    | "'" comment!
    | (any ctx) comment!
    | -> err ctx (bp, $pos) "comment not terminated" ]
;

value rec quotation ctx bp =
  lexer
  [ ">>"/
  | ">" (quotation ctx bp)!
  | "<<" (quotation ctx bp)! [ -> $add ">>" ]! (quotation ctx bp)!
  | "<:" ident! "<" (quotation ctx bp)! [ -> $add ">>" ]! (quotation ctx bp)!
  | "<:" ident! (quotation ctx bp)!
  | "<" (quotation ctx bp)!
  | "\\"/ [ '>' | '<' | '\\' ] (quotation ctx bp)!
  | "\\" (quotation ctx bp)!
  | (any ctx) (quotation ctx bp)!
  | -> err ctx (bp, $pos) "quotation not terminated" ]
;

value less ctx bp buf strm =
  if no_quotations.val then
    match strm with lexer
    [ [ -> $add "<" ] ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
  else
    match strm with lexer
    [ "<"/ (quotation ctx bp) -> ("QUOTATION", ":" ^ $buf)
    | ":"/ ident! [ -> $add ":" ]! "<"/ ? "character '<' expected"
      (quotation ctx bp) ->
        ("QUOTATION", $buf)
    | [ -> $add "<" ] ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
;

value rec antiquot_rest ctx bp =
  lexer
  [ "$"/
  | "\\"/ (any ctx) (antiquot_rest ctx bp)!
  | (any ctx) (antiquot_rest ctx bp)!
  | -> err ctx (bp, $pos) "antiquotation not terminated" ]
;

value rec antiquot ctx bp =
  lexer
  [ "$"/ -> ":" ^ $buf
  | [ 'a'-'z' | 'A'-'Z' | '0'-'9' | '_' ] (antiquot ctx bp)!
  | ":" (antiquot_rest ctx bp)! -> $buf
  | "\\"/ (any ctx) (antiquot_rest ctx bp)! -> ":" ^ $buf
  | (any ctx) (antiquot_rest ctx bp)! -> ":" ^ $buf
  | -> err ctx (bp, $pos) "antiquotation not terminated" ]
;

value antiloc bp ep s = Printf.sprintf "%d,%d:%s" bp ep s;

value rec antiquot_loc ctx bp =
  lexer
  [ "$"/ -> antiloc bp $pos (":" ^ $buf)
  | [ 'a'-'z' | 'A'-'Z' | '0'-'9' | '_' ] (antiquot_loc ctx bp)!
  | ":" (antiquot_rest ctx bp)! -> antiloc bp $pos $buf
  | "\\"/ (any ctx) (antiquot_rest ctx bp)! -> antiloc bp $pos (":" ^ $buf)
  | (any ctx) (antiquot_rest ctx bp)! -> antiloc bp $pos (":" ^ $buf)
  | -> err ctx (bp, $pos) "antiquotation not terminated" ]
;

value dollar ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    ("ANTIQUOT", antiquot ctx bp buf strm)
  else if force_antiquot_loc.val then
    ("ANTIQUOT_LOC", antiquot_loc ctx bp buf strm)
  else
    match strm with lexer
    [ [ -> $add "$" ] ident2! -> ("", $buf) ]
;

(* ANTIQUOT - specific case for QUESTIONIDENT and QUESTIONIDENTCOLON
    input         expr        patt
    -----         ----        ----
    ?$abc:d$      ?abc:d      ?abc
    ?$abc:d$:     ?abc:d:     ?abc:
    ?$d$          ?:d         ?
    ?$d$:         ?:d:        ?:
*)

(* ANTIQUOT_LOC - specific case for QUESTIONIDENT and QUESTIONIDENTCOLON
    input         expr             patt
    -----         ----             ----
    ?$abc:d$      ?8,13:abc:d      ?abc
    ?$abc:d$:     ?8,13:abc:d:     ?abc:
    ?$d$          ?8,9::d          ?
    ?$d$:         ?8,9::d:         ?:
*)

value question ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    match strm with parser
    [ [: `'$'; s = antiquot ctx bp $empty; `':' :] ->
        ("ANTIQUOT", "?" ^ s ^ ":")
    | [: `'$'; s = antiquot ctx bp $empty :] ->
        ("ANTIQUOT", "?" ^ s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else if force_antiquot_loc.val then
    match strm with parser
    [ [: `'$'; s = antiquot_loc ctx bp $empty; `':' :] ->
        ("ANTIQUOT_LOC", "?" ^ s ^ ":")
    | [: `'$'; s = antiquot_loc ctx bp $empty :] ->
        ("ANTIQUOT_LOC", "?" ^ s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else
    match strm with lexer
    [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
;

value tilde ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    match strm with parser
    [ [: `'$'; s = antiquot ctx bp $empty; `':' :] ->
        ("ANTIQUOT", "~" ^ s ^ ":")
    | [: `'$'; s = antiquot ctx bp $empty :] ->
        ("ANTIQUOT", "~" ^ s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else if force_antiquot_loc.val then
    match strm with parser
    [ [: `'$'; s = antiquot_loc ctx bp $empty; `':' :] ->
        ("ANTIQUOT_LOC", "~" ^ s ^ ":")
    | [: `'$'; s = antiquot_loc ctx bp $empty :] ->
        ("ANTIQUOT_LOC", "~" ^ s)
    | [: :] ->
        match strm with lexer
        [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ] ]
  else
    match strm with lexer
    [ ident2! -> keyword_or_error ctx (bp, $pos) $buf ]
;

value tildeident =
  lexer
  [ ":"/ -> ("TILDEIDENTCOLON", $buf)
  | -> ("TILDEIDENT", $buf) ]
;

value questionident =
  lexer
  [ ":"/ -> ("QUESTIONIDENTCOLON", $buf)
  | -> ("QUESTIONIDENT", $buf) ]
;

value rec linedir n s =
  match stream_peek_nth n s with
  [ Some (' ' | '\t') -> linedir (n + 1) s
  | Some ('0'..'9') -> linedir_digits (n + 1) s
  | _ -> False ]
and linedir_digits n s =
  match stream_peek_nth n s with
  [ Some ('0'..'9') -> linedir_digits (n + 1) s
  | _ -> linedir_quote n s ]
and linedir_quote n s =
  match stream_peek_nth n s with
  [ Some (' ' | '\t') -> linedir_quote (n + 1) s
  | Some '"' -> True
  | _ -> False ]
;

value rec any_to_nl =
  lexer
  [ "\r" | "\n"
  | _ any_to_nl!
  | ]
;

value next_token_after_spaces ctx bp =
  lexer
  [ 'A'-'Z' ident! ->
      let id = $buf in
      jrh_identifier ctx.find_kwd id
(********** JRH: original was
      try ("", ctx.find_kwd id) with [ Not_found -> ("UIDENT", id) ]
 *********)
  | [ 'a'-'z' | '_' | '\128'-'\255' ] ident! ->
      let id = $buf in
      jrh_identifier ctx.find_kwd id
(********** JRH: original was
      try ("", ctx.find_kwd id) with [ Not_found -> ("LIDENT", id) ]
 *********)
  | '1'-'9' number!
  | "0" [ 'o' | 'O' ] (digits octal)!
  | "0" [ 'x' | 'X' ] (digits hexa)!
  | "0" [ 'b' | 'B' ] (digits binary)!
  | "0" number!
  | "'"/ (char ctx bp) -> ("CHAR", $buf)
  | "'" -> keyword_or_error ctx (bp, $pos) "'"
  | "\""/ (string ctx bp)! -> ("STRING", $buf)
(*** Line added by JRH ***)
  | "`"/ (qstring ctx bp)! -> ("QUOTATION", "tot:" ^ $buf)
  | "$"/ (dollar ctx bp)!
  | [ '!' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' | '%' ] ident2! ->
      keyword_or_error ctx (bp, $pos) $buf
  | "~"/ 'a'-'z' ident! tildeident!
  | "~" (tilde ctx bp)
  | "?"/ 'a'-'z' ident! questionident!
  | "?" (question ctx bp)!
  | "<"/ (less ctx bp)!
  | ":]" -> keyword_or_error ctx (bp, $pos) $buf
  | "::" -> keyword_or_error ctx (bp, $pos) $buf
  | ":=" -> keyword_or_error ctx (bp, $pos) $buf
  | ":>" -> keyword_or_error ctx (bp, $pos) $buf
  | ":" -> keyword_or_error ctx (bp, $pos) $buf
  | ">]" -> keyword_or_error ctx (bp, $pos) $buf
  | ">}" -> keyword_or_error ctx (bp, $pos) $buf
  | ">" ident2! -> keyword_or_error ctx (bp, $pos) $buf
  | "|]" -> keyword_or_error ctx (bp, $pos) $buf
  | "|}" -> keyword_or_error ctx (bp, $pos) $buf
  | "|" ident2! -> keyword_or_error ctx (bp, $pos) $buf
  | "[" ?= [ "<<" | "<:" ] -> keyword_or_error ctx (bp, $pos) $buf
  | "[|" -> keyword_or_error ctx (bp, $pos) $buf
  | "[<" -> keyword_or_error ctx (bp, $pos) $buf
  | "[:" -> keyword_or_error ctx (bp, $pos) $buf
  | "[" -> keyword_or_error ctx (bp, $pos) $buf
  | "{" ?= [ "<<" | "<:" ] -> keyword_or_error ctx (bp, $pos) $buf
  | "{|" -> keyword_or_error ctx (bp, $pos) $buf
  | "{<" -> keyword_or_error ctx (bp, $pos) $buf
  | "{:" -> keyword_or_error ctx (bp, $pos) $buf
  | "{" -> keyword_or_error ctx (bp, $pos) $buf
  | ".." -> keyword_or_error ctx (bp, $pos) ".."
  | "." ->
      let id =
        if ctx.specific_space_dot && ctx.after_space then " ." else "."
      in
      keyword_or_error ctx (bp, $pos) id
  | ";;" -> keyword_or_error ctx (bp, $pos) ";;"
  | ";" -> keyword_or_error ctx (bp, $pos) ";"
  | "\\"/ ident3! -> ("LIDENT", $buf)
  | (any ctx) -> keyword_or_error ctx (bp, $pos) $buf ]
;

value rec next_token ctx buf =
  parser bp
  [ [: `('\n' | '\r' as c); s :] ep -> do {
      incr Plexing.line_nb.val;
      Plexing.bol_pos.val.val := ep;
      ctx.set_line_nb ();
      ctx.after_space := True;
      next_token ctx ($add c) s
    }
  | [: `(' ' | '\t' | '\026' | '\012' as c); s :] -> do {
      ctx.after_space := True;
      next_token ctx ($add c) s
    }
  | [: `'#' when bp = Plexing.bol_pos.val.val; s :] ->
      if linedir 1 s then do {
        let buf = any_to_nl ($add '#') s in
        incr Plexing.line_nb.val;
        Plexing.bol_pos.val.val := Stream.count s;
        ctx.set_line_nb ();
        ctx.after_space := True;
        next_token ctx buf s
      }
      else
        let loc = ctx.make_lined_loc (bp, bp + 1) $buf in
        (keyword_or_error ctx (bp, bp + 1) "#", loc)
  | [: `'(';
       a =
         parser
         [ [: `'*'; buf = comment ctx bp ($add "(*") !; s :] -> do {
             ctx.set_line_nb ();
             ctx.after_space := True;
             next_token ctx buf s
           }
         | [: :] ep ->
             let loc = ctx.make_lined_loc (bp, ep) $buf in
             (keyword_or_error ctx (bp, ep) "(", loc) ] ! :] -> a
  | [: tok = next_token_after_spaces ctx bp $empty :] ep ->
      let loc = ctx.make_lined_loc (bp, max (bp + 1) ep) $buf in
      (tok, loc)
  | [: _ = Stream.empty :] ->
      let loc = ctx.make_lined_loc (bp, bp + 1) $buf in
      (("EOI", ""), loc) ]
;

value next_token_fun ctx glexr (cstrm, s_line_nb, s_bol_pos) =
  try do {
    match Plexing.restore_lexing_info.val with
    [ Some (line_nb, bol_pos) -> do {
        s_line_nb.val := line_nb;
        s_bol_pos.val := bol_pos;
        Plexing.restore_lexing_info.val := None
      }
    | None -> () ];
    Plexing.line_nb.val := s_line_nb;
    Plexing.bol_pos.val := s_bol_pos;
    let comm_bp = Stream.count cstrm in
    ctx.set_line_nb ();
    ctx.after_space := False;
    let (r, loc) = next_token ctx $empty cstrm in
    match glexr.val.Plexing.tok_comm with
    [ Some list ->
        if Ploc.first_pos loc > comm_bp then
          let comm_loc = Ploc.make_unlined (comm_bp, Ploc.last_pos loc) in
          glexr.val.Plexing.tok_comm := Some [comm_loc :: list]
        else ()
    | None -> () ];
    (r, loc)
  }
  with
  [ Stream.Error str ->
      err ctx (Stream.count cstrm, Stream.count cstrm + 1) str ]
;

value func kwd_table glexr =
  let ctx =
    let line_nb = ref 0 in
    let bol_pos = ref 0 in
    {after_space = False;
     dollar_for_antiquotation = dollar_for_antiquotation.val;
     specific_space_dot = specific_space_dot.val;
     find_kwd = Hashtbl.find kwd_table;
     line_cnt bp1 c =
       match c with
       [ '\n' | '\r' -> do {
           incr Plexing.line_nb.val;
           Plexing.bol_pos.val.val := bp1 + 1;
         }
       | c -> () ];
     set_line_nb () = do {
       line_nb.val := Plexing.line_nb.val.val;
       bol_pos.val := Plexing.bol_pos.val.val;
     };
     make_lined_loc loc comm =
       Ploc.make line_nb.val bol_pos.val loc}
  in
  Plexing.lexer_func_of_parser (next_token_fun ctx glexr)
;

value rec check_keyword_stream =
  parser [: _ = check $empty; _ = Stream.empty :] -> True
and check =
  lexer
  [ [ 'A'-'Z' | 'a'-'z' | '\128'-'\255' ] check_ident!
  | [ '!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' | '%' |
      '.' ]
      check_ident2!
  | "$" check_ident2!
  | "<" ?= [ ":" | "<" ]
  | "<" check_ident2!
  | ":]"
  | "::"
  | ":="
  | ":>"
  | ":"
  | ">]"
  | ">}"
  | ">" check_ident2!
  | "|]"
  | "|}"
  | "|" check_ident2!
  | "[" ?= [ "<<" | "<:" ]
  | "[|"
  | "[<"
  | "[:"
  | "["
  | "{" ?= [ "<<" | "<:" ]
  | "{|"
  | "{<"
  | "{:"
  | "{"
  | ";;"
  | ";"
  | _ ]
and check_ident =
  lexer
  [ [ 'A'-'Z' | 'a'-'z' | '0'-'9' | '_' | ''' | '\128'-'\255' ]
    check_ident! | ]
and check_ident2 =
  lexer
  [ [ '!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' | '%' |
      '.' | ':' | '<' | '>' | '|' ]
    check_ident2! | ]
;

value check_keyword s =
  try check_keyword_stream (Stream.of_string s) with _ -> False
;

value error_no_respect_rules p_con p_prm =
  raise
    (Plexing.Error
       ("the token " ^
          (if p_con = "" then "\"" ^ p_prm ^ "\""
           else if p_prm = "" then p_con
           else p_con ^ " \"" ^ p_prm ^ "\"") ^
          " does not respect Plexer rules"))
;

value error_ident_and_keyword p_con p_prm =
  raise
    (Plexing.Error
       ("the token \"" ^ p_prm ^ "\" is used as " ^ p_con ^
          " and as keyword"))
;

value using_token kwd_table ident_table (p_con, p_prm) =
  match p_con with
  [ "" ->
      if not (Hashtbl.mem kwd_table p_prm) then
        if check_keyword p_prm then
          if Hashtbl.mem ident_table p_prm then
            error_ident_and_keyword (Hashtbl.find ident_table p_prm) p_prm
          else Hashtbl.add kwd_table p_prm p_prm
        else error_no_respect_rules p_con p_prm
      else ()
  | "LIDENT" ->
      if p_prm = "" then ()
      else
        match p_prm.[0] with
        [ 'A'..'Z' -> error_no_respect_rules p_con p_prm
        | _ ->
            if Hashtbl.mem kwd_table p_prm then
              error_ident_and_keyword p_con p_prm
            else Hashtbl.add ident_table p_prm p_con ]
  | "UIDENT" ->
      if p_prm = "" then ()
      else
        match p_prm.[0] with
        [ 'a'..'z' -> error_no_respect_rules p_con p_prm
        | _ ->
            if Hashtbl.mem kwd_table p_prm then
              error_ident_and_keyword p_con p_prm
            else Hashtbl.add ident_table p_prm p_con ]
  | "TILDEIDENT" | "TILDEIDENTCOLON" | "QUESTIONIDENT" |
    "QUESTIONIDENTCOLON" | "INT" | "INT_l" | "INT_L" | "INT_n" | "FLOAT" |
    "CHAR" | "STRING" | "QUOTATION" |
    "ANTIQUOT" | "ANTIQUOT_LOC" | "EOI" ->
      ()
  | _ ->
      raise
        (Plexing.Error
           ("the constructor \"" ^ p_con ^
              "\" is not recognized by Plexer")) ]
;

value removing_token kwd_table ident_table (p_con, p_prm) =
  match p_con with
  [ "" -> Hashtbl.remove kwd_table p_prm
  | "LIDENT" | "UIDENT" ->
      if p_prm <> "" then Hashtbl.remove ident_table p_prm else ()
  | _ -> () ]
;

value text =
  fun
  [ ("", t) -> "'" ^ t ^ "'"
  | ("LIDENT", "") -> "lowercase identifier"
  | ("LIDENT", t) -> "'" ^ t ^ "'"
  | ("UIDENT", "") -> "uppercase identifier"
  | ("UIDENT", t) -> "'" ^ t ^ "'"
  | ("INT", "") -> "integer"
  | ("INT", s) -> "'" ^ s ^ "'"
  | ("FLOAT", "") -> "float"
  | ("STRING", "") -> "string"
  | ("CHAR", "") -> "char"
  | ("QUOTATION", "") -> "quotation"
  | ("ANTIQUOT", k) -> "antiquot \"" ^ k ^ "\""
  | ("EOI", "") -> "end of input"
  | (con, "") -> con
  | (con, prm) -> con ^ " \"" ^ prm ^ "\"" ]
;

value eq_before_colon p e =
  loop 0 where rec loop i =
    if i == String.length e then
      failwith "Internal error in Plexer: incorrect ANTIQUOT"
    else if i == String.length p then e.[i] == ':'
    else if p.[i] == e.[i] then loop (i + 1)
    else False
;

value after_colon e =
  try
    let i = String.index e ':' in
    String.sub e (i + 1) (String.length e - i - 1)
  with
  [ Not_found -> "" ]
;

value after_colon_except_last e =
  try
    let i = String.index e ':' in
    String.sub e (i + 1) (String.length e - i - 2)
  with
  [ Not_found -> "" ]
;

value tok_match =
  fun
  [ ("ANTIQUOT", p_prm) ->
      if p_prm <> "" && (p_prm.[0] = '~' || p_prm.[0] = '?') then
        if p_prm.[String.length p_prm - 1] = ':' then
          let p_prm = String.sub p_prm 0 (String.length p_prm - 1) in
          fun
          [ ("ANTIQUOT", prm) ->
              if prm <> "" && prm.[String.length prm - 1] = ':' then
                if eq_before_colon p_prm prm then after_colon_except_last prm
                else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
        else
          fun
          [ ("ANTIQUOT", prm) ->
              if prm <> "" && prm.[String.length prm - 1] = ':' then
                raise Stream.Failure
              else if eq_before_colon p_prm prm then after_colon prm
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
      else
        fun
        [ ("ANTIQUOT", prm) when eq_before_colon p_prm prm -> after_colon prm
        | _ -> raise Stream.Failure ]
  | tok -> Plexing.default_match tok ]
;

value gmake () =
  let kwd_table = Hashtbl.create 301 in
  let id_table = Hashtbl.create 301 in
  let glexr =
    ref
     {Plexing.tok_func = fun []; tok_using = fun []; tok_removing = fun [];
      tok_match = fun []; tok_text = fun []; tok_comm = None}
  in
  let glex =
    {Plexing.tok_func = func kwd_table glexr;
     tok_using = using_token kwd_table id_table;
     tok_removing = removing_token kwd_table id_table; tok_match = tok_match;
     tok_text = text; tok_comm = None}
  in
  do { glexr.val := glex; glex }
;

do {
  let odfa = dollar_for_antiquotation.val in
  dollar_for_antiquotation.val := False;
  Grammar.Unsafe.gram_reinit gram (gmake ());
  dollar_for_antiquotation.val := odfa;
  Grammar.Unsafe.clear_entry interf;
  Grammar.Unsafe.clear_entry implem;
  Grammar.Unsafe.clear_entry top_phrase;
  Grammar.Unsafe.clear_entry use_file;
  Grammar.Unsafe.clear_entry module_type;
  Grammar.Unsafe.clear_entry module_expr;
  Grammar.Unsafe.clear_entry sig_item;
  Grammar.Unsafe.clear_entry str_item;
  Grammar.Unsafe.clear_entry expr;
  Grammar.Unsafe.clear_entry patt;
  Grammar.Unsafe.clear_entry ctyp;
  Grammar.Unsafe.clear_entry let_binding;
  Grammar.Unsafe.clear_entry type_declaration;
  Grammar.Unsafe.clear_entry constructor_declaration;
  Grammar.Unsafe.clear_entry match_case;
  Grammar.Unsafe.clear_entry with_constr;
  Grammar.Unsafe.clear_entry poly_variant;
  Grammar.Unsafe.clear_entry class_type;
  Grammar.Unsafe.clear_entry class_expr;
  Grammar.Unsafe.clear_entry class_sig_item;
  Grammar.Unsafe.clear_entry class_str_item
};

Pcaml.parse_interf.val := Grammar.Entry.parse interf;
Pcaml.parse_implem.val := Grammar.Entry.parse implem;

value neg_string n =
  let len = String.length n in
  if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1) else "-" ^ n
;

value mkumin loc f arg =
  match arg with
  [ <:expr< $int:n$ >> -> <:expr< $int:neg_string n$ >>
  | <:expr< $flo:n$ >> -> <:expr< $flo:neg_string n$ >>
  | _ ->
      let f = "~" ^ f in
      <:expr< $lid:f$ $arg$ >> ]
;

value mklistexp loc last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Some e -> e
        | None -> <:expr< [] >> ]
    | [e1 :: el] ->
        let loc =
          if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc
        in
        <:expr< [$e1$ :: $loop False el$] >> ]
;

value mklistpat loc last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Some p -> p
        | None -> <:patt< [] >> ]
    | [p1 :: pl] ->
        let loc =
          if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc
        in
        <:patt< [$p1$ :: $loop False pl$] >> ]
;

(*** JRH pulled this outside so user can add new infixes here too ***)

value ht = Hashtbl.create 73;

(*** And JRH added all the new HOL Light infixes here already ***)

value is_operator = do {
  let ct = Hashtbl.create 73 in
  List.iter (fun x -> Hashtbl.add ht x True)
    ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"; "o"; "upto";
     "F_F"; "THENC"; "THEN"; "THENL"; "ORELSE"; "ORELSEC";
     "THEN_TCL"; "ORELSE_TCL"];
  List.iter (fun x -> Hashtbl.add ct x True)
    ['!'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '='; '>'; '@'; '^'; '|'; '~';
     '?'; '%'; '.'; '$'];
  fun x ->
    try Hashtbl.find ht x with
    [ Not_found -> try Hashtbl.find ct x.[0] with _ -> False ]
};

(*** JRH added this so parenthesised operators undergo same mapping ***)

value translate_operator =
  fun s ->
   match s with
    [ "THEN" -> "then_"
    | "THENC" -> "thenc_"
    | "THENL" -> "thenl_"
    | "ORELSE" -> "orelse_"
    | "ORELSEC" -> "orelsec_"
    | "THEN_TCL" -> "then_tcl_"
    | "ORELSE_TCL" -> "orelse_tcl_"
    | "F_F" -> "f_f_"
    | _ -> s];

(*** And JRH inserted it in here ***)

value operator_rparen =
  Grammar.Entry.of_parser gram "operator_rparen"
    (fun strm ->
       match Stream.npeek 2 strm with
       [ [("", s); ("", ")")] when is_operator s -> do {
           Stream.junk strm;
           Stream.junk strm;
           translate_operator s
         }
       | _ -> raise Stream.Failure ])
;

value check_not_part_of_patt =
  Grammar.Entry.of_parser gram "check_not_part_of_patt"
    (fun strm ->
       let tok =
         match Stream.npeek 4 strm with
         [ [("LIDENT", _); tok :: _] -> tok
         | [("", "("); ("", s); ("", ")"); tok] when is_operator s -> tok
         | _ -> raise Stream.Failure ]
       in
       match tok with
       [ ("", "," | "as" | "|" | "::") -> raise Stream.Failure
       | _ -> () ])
;

value symbolchar =
  let list =
    ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '.'; '/'; ':'; '<'; '='; '>'; '?';
     '@'; '^'; '|'; '~']
  in
  loop where rec loop s i =
    if i == String.length s then True
    else if List.mem s.[i] list then loop s (i + 1)
    else False
;

value prefixop =
  let list = ['!'; '?'; '~'] in
  let excl = ["!="; "??"; "?!"] in
  Grammar.Entry.of_parser gram "prefixop"
    (parser
       [: `("", x)
           when
             not (List.mem x excl) && String.length x >= 2 &&
             List.mem x.[0] list && symbolchar x 1 :] ->
         x)
;

value infixop0 =
  let list = ['='; '<'; '>'; '|'; '&'; '$'] in
  let excl = ["<-"; "||"; "&&"] in
  Grammar.Entry.of_parser gram "infixop0"
    (parser
       [: `("", x)
           when
             not (List.mem x excl) && String.length x >= 2 &&
             List.mem x.[0] list && symbolchar x 1 :] ->
         x)
;

value infixop1 =
  let list = ['@'; '^'] in
  Grammar.Entry.of_parser gram "infixop1"
    (parser
       [: `("", x)
           when
             String.length x >= 2 && List.mem x.[0] list &&
             symbolchar x 1 :] ->
         x)
;

value infixop2 =
  let list = ['+'; '-'] in
  Grammar.Entry.of_parser gram "infixop2"
    (parser
       [: `("", x)
           when
             x <> "->" && String.length x >= 2 && List.mem x.[0] list &&
             symbolchar x 1 :] ->
         x)
;

value infixop3 =
  let list = ['*'; '/'; '%'] in
  Grammar.Entry.of_parser gram "infixop3"
    (parser
       [: `("", x)
           when
             String.length x >= 2 && List.mem x.[0] list &&
             symbolchar x 1 :] ->
         x)
;

value infixop4 =
  Grammar.Entry.of_parser gram "infixop4"
    (parser
       [: `("", x)
           when
             String.length x >= 3 && x.[0] == '*' && x.[1] == '*' &&
             symbolchar x 2 :] ->
         x)
;

value test_constr_decl =
  Grammar.Entry.of_parser gram "test_constr_decl"
    (fun strm ->
       match Stream.npeek 1 strm with
       [ [("UIDENT", _)] ->
           match Stream.npeek 2 strm with
           [ [_; ("", ".")] -> raise Stream.Failure
           | [_; ("", "(")] -> raise Stream.Failure
           | [_ :: _] -> ()
           | _ -> raise Stream.Failure ]
       | [("", "|")] -> ()
       | _ -> raise Stream.Failure ])
;

value stream_peek_nth n strm =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some x else None
    | [_ :: l] -> loop (n - 1) l ]
;

(* horrible hack to be able to parse class_types *)

value test_ctyp_minusgreater =
  Grammar.Entry.of_parser gram "test_ctyp_minusgreater"
    (fun strm ->
       let rec skip_simple_ctyp n =
         match stream_peek_nth n strm with
         [ Some ("", "->") -> n
         | Some ("", "[" | "[<") ->
             skip_simple_ctyp (ignore_upto "]" (n + 1) + 1)
         | Some ("", "(") -> skip_simple_ctyp (ignore_upto ")" (n + 1) + 1)
         | Some
             ("",
              "as" | "'" | ":" | "*" | "." | "#" | "<" | ">" | ".." | ";" |
              "_") ->
             skip_simple_ctyp (n + 1)
         | Some ("QUESTIONIDENT" | "LIDENT" | "UIDENT", _) ->
             skip_simple_ctyp (n + 1)
         | Some _ | None -> raise Stream.Failure ]
       and ignore_upto end_kwd n =
         match stream_peek_nth n strm with
         [ Some ("", prm) when prm = end_kwd -> n
         | Some ("", "[" | "[<") ->
             ignore_upto end_kwd (ignore_upto "]" (n + 1) + 1)
         | Some ("", "(") -> ignore_upto end_kwd (ignore_upto ")" (n + 1) + 1)
         | Some _ -> ignore_upto end_kwd (n + 1)
         | None -> raise Stream.Failure ]
       in
       match Stream.peek strm with
       [ Some (("", "[") | ("LIDENT" | "UIDENT", _)) -> skip_simple_ctyp 1
       | Some ("", "object") -> raise Stream.Failure
       | _ -> 1 ])
;

value test_label_eq =
  Grammar.Entry.of_parser gram "test_label_eq"
    (test 1 where rec test lev strm =
       match stream_peek_nth lev strm with
       [ Some (("UIDENT", _) | ("LIDENT", _) | ("", ".")) ->
           test (lev + 1) strm
       | Some ("ANTIQUOT_LOC", _) -> ()
       | Some ("", "=") -> ()
       | _ -> raise Stream.Failure ])
;

value test_typevar_list_dot =
  Grammar.Entry.of_parser gram "test_typevar_list_dot"
    (let rec test lev strm =
       match stream_peek_nth lev strm with
       [ Some ("", "'") -> test2 (lev + 1) strm
       | Some ("", ".") -> ()
       | _ -> raise Stream.Failure ]
     and test2 lev strm =
       match stream_peek_nth lev strm with
       [ Some ("UIDENT" | "LIDENT", _) -> test (lev + 1) strm
       | _ -> raise Stream.Failure ]
     in
     test 1)
;

value constr_arity = ref [("Some", 1); ("Match_Failure", 1)];

value rec is_expr_constr_call =
  fun
  [ <:expr< $uid:_$ >> -> True
  | <:expr< $uid:_$.$e$ >> -> is_expr_constr_call e
  | <:expr< $e$ $_$ >> -> is_expr_constr_call e
  | _ -> False ]
;

value rec constr_expr_arity loc =
  fun
  [ <:expr< $uid:c$ >> ->
      try List.assoc c constr_arity.val with [ Not_found -> 0 ]
  | <:expr< $uid:_$.$e$ >> -> constr_expr_arity loc e
  | _ -> 1 ]
;

value rec constr_patt_arity loc =
  fun
  [ <:patt< $uid:c$ >> ->
      try List.assoc c constr_arity.val with [ Not_found -> 0 ]
  | <:patt< $uid:_$.$p$ >> -> constr_patt_arity loc p
  | _ -> 1 ]
;

value get_seq =
  fun
  [ <:expr< do { $list:el$ } >> -> el
  | e -> [e] ]
;

value mem_tvar s tpl = List.exists (fun (t, _) -> Pcaml.unvala t = s) tpl;

value choose_tvar tpl =
  let rec find_alpha v =
    let s = String.make 1 v in
    if mem_tvar s tpl then
      if v = 'z' then None else find_alpha (Char.chr (Char.code v + 1))
    else Some (String.make 1 v)
  in
  let rec make_n n =
    let v = "a" ^ string_of_int n in
    if mem_tvar v tpl then make_n (succ n) else v
  in
  match find_alpha 'a' with
  [ Some x -> x
  | None -> make_n 1 ]
;

EXTEND
  GLOBAL: sig_item str_item ctyp patt expr module_type module_expr class_type
    class_expr class_sig_item class_str_item let_binding type_declaration
    constructor_declaration match_case with_constr poly_variant;
  module_expr:
    [ [ "functor"; "("; i = V UIDENT "uid" ""; ":"; t = module_type; ")";
        "->"; me = SELF ->
          <:module_expr< functor ( $_uid:i$ : $t$ ) -> $me$ >>
      | "struct"; st = V (LIST0 [ s = str_item; OPT ";;" -> s ]); "end" ->
          <:module_expr< struct $_list:st$ end >> ]
    | [ me1 = SELF; me2 = SELF -> <:module_expr< $me1$ $me2$ >> ]
    | [ i = mod_expr_ident -> i
      | "("; me = SELF; ":"; mt = module_type; ")" ->
          <:module_expr< ( $me$ : $mt$ ) >>
      | "("; me = SELF; ")" -> <:module_expr< $me$ >> ] ]
  ;
  mod_expr_ident:
    [ LEFTA
      [ i = SELF; "."; j = SELF -> <:module_expr< $i$ . $j$ >> ]
    | [ i = V UIDENT -> <:module_expr< $_uid:i$ >> ] ]
  ;
  str_item:
    [ "top"
      [ "exception"; (_, c, tl) = constructor_declaration; b = rebind_exn ->
          <:str_item< exception $_uid:c$ of $_list:tl$ = $_list:b$ >>
      | "external"; i = V LIDENT "lid" ""; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ->
          <:str_item< external $_lid:i$ : $t$ = $_list:pd$ >>
      | "external"; "("; i = operator_rparen; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ->
          <:str_item< external $lid:i$ : $t$ = $_list:pd$ >>
      | "include"; me = module_expr -> <:str_item< include $me$ >>
      | "module"; r = V (FLAG "rec"); l = V (LIST1 mod_binding SEP "and") ->
          <:str_item< module $_flag:r$ $_list:l$ >>
      | "module"; "type"; i = V UIDENT "uid" ""; "="; mt = module_type ->
          <:str_item< module type $_uid:i$ = $mt$ >>
      | "open"; i = V mod_ident "list" "" ->
          <:str_item< open $_:i$ >>
      | "type"; tdl = V (LIST1 type_declaration SEP "and") ->
          <:str_item< type $_list:tdl$ >>
      | "let"; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and"); "in";
        x = expr ->
          let e = <:expr< let $_flag:r$ $_list:l$ in $x$ >> in
          <:str_item< $exp:e$ >>
      | "let"; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and") ->
          match l with
          [ <:vala< [(p, e)] >> ->
              match p with
              [ <:patt< _ >> -> <:str_item< $exp:e$ >>
              | _ -> <:str_item< value $_flag:r$ $_list:l$ >> ]
          | _ -> <:str_item< value $_flag:r$ $_list:l$ >> ]
      | "let"; "module"; m = V UIDENT; mb = mod_fun_binding; "in"; e = expr ->
          <:str_item< let module $_uid:m$ = $mb$ in $e$ >>
      | e = expr -> <:str_item< $exp:e$ >> ] ]
  ;
  rebind_exn:
    [ [ "="; sl = V mod_ident "list" -> sl
      | -> <:vala< [] >> ] ]
  ;
  mod_binding:
    [ [ i = V UIDENT; me = mod_fun_binding -> (i, me) ] ]
  ;
  mod_fun_binding:
    [ RIGHTA
      [ "("; m = UIDENT; ":"; mt = module_type; ")"; mb = SELF ->
          <:module_expr< functor ( $uid:m$ : $mt$ ) -> $mb$ >>
      | ":"; mt = module_type; "="; me = module_expr ->
          <:module_expr< ( $me$ : $mt$ ) >>
      | "="; me = module_expr -> <:module_expr< $me$ >> ] ]
  ;
  (* Module types *)
  module_type:
    [ [ "functor"; "("; i = V UIDENT "uid" ""; ":"; t = SELF; ")"; "->";
        mt = SELF ->
          <:module_type< functor ( $_uid:i$ : $t$ ) -> $mt$ >> ]
    | [ mt = SELF; "with"; wcl = V (LIST1 with_constr SEP "and") ->
          <:module_type< $mt$ with $_list:wcl$ >> ]
    | [ "sig"; sg = V (LIST0 [ s = sig_item; OPT ";;" -> s ]); "end" ->
          <:module_type< sig $_list:sg$ end >>
      | i = mod_type_ident -> i
      | "("; mt = SELF; ")" -> <:module_type< $mt$ >> ] ]
  ;
  mod_type_ident:
    [ LEFTA
      [ m1 = SELF; "."; m2 = SELF -> <:module_type< $m1$ . $m2$ >>
      | m1 = SELF; "("; m2 = SELF; ")" -> <:module_type< $m1$ $m2$ >> ]
    | [ m = V UIDENT -> <:module_type< $_uid:m$ >>
      | m = V LIDENT -> <:module_type< $_lid:m$ >> ] ]
  ;
  sig_item:
    [ "top"
      [ "exception"; (_, c, tl) = constructor_declaration ->
          <:sig_item< exception $_uid:c$ of $_list:tl$ >>
      | "external"; i = V LIDENT "lid" ""; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ->
          <:sig_item< external $_lid:i$ : $t$ = $_list:pd$ >>
      | "external"; "("; i = operator_rparen; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ->
          <:sig_item< external $lid:i$ : $t$ = $_list:pd$ >>
      | "include"; mt = module_type ->
          <:sig_item< include $mt$ >>
      | "module"; rf = V (FLAG "rec");
        l = V (LIST1 mod_decl_binding SEP "and") ->
          <:sig_item< module $_flag:rf$ $_list:l$ >>
      | "module"; "type"; i = V UIDENT "uid" ""; "="; mt = module_type ->
          <:sig_item< module type $_uid:i$ = $mt$ >>
      | "module"; "type"; i = V UIDENT "uid" "" ->
          <:sig_item< module type $_uid:i$ = 'abstract >>
      | "open"; i = V mod_ident "list" "" ->
          <:sig_item< open $_:i$ >>
      | "type"; tdl = V (LIST1 type_declaration SEP "and") ->
          <:sig_item< type $_list:tdl$ >>
      | "val"; i = V LIDENT "lid" ""; ":"; t = ctyp ->
          <:sig_item< value $_lid:i$ : $t$ >>
      | "val"; "("; i = operator_rparen; ":"; t = ctyp ->
          <:sig_item< value $lid:i$ : $t$ >> ] ]
  ;
  mod_decl_binding:
    [ [ i = V UIDENT; mt = module_declaration -> (i, mt) ] ]
  ;
  module_declaration:
    [ RIGHTA
      [ ":"; mt = module_type -> <:module_type< $mt$ >>
      | "("; i = UIDENT; ":"; t = module_type; ")"; mt = SELF ->
          <:module_type< functor ( $uid:i$ : $t$ ) -> $mt$ >> ] ]
  ;
  (* "with" constraints (additional type equations over signature
     components) *)
  with_constr:
    [ [ "type"; tpl = V type_parameters "list"; i = V mod_ident ""; "=";
        pf = V (FLAG "private"); t = ctyp ->
          <:with_constr< type $_:i$ $_list:tpl$ = $_flag:pf$ $t$ >>
      | "module"; i = V mod_ident ""; "="; me = module_expr ->
          <:with_constr< module $_:i$ = $me$ >> ] ]
  ;
  (* Core expressions *)
  expr:
    [ "top" RIGHTA
      [ e1 = SELF; ";"; e2 = SELF ->
          <:expr< do { $list:[e1 :: get_seq e2]$ } >>
      | e1 = SELF; ";" -> e1
      | el = V e_phony "list" -> <:expr< do { $_list:el$ } >> ]
    | "expr1"
      [ "let"; o = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and"); "in";
        x = expr LEVEL "top" ->
          <:expr< let $_flag:o$ $_list:l$ in $x$ >>
      | "let"; "module"; m = V UIDENT; mb = mod_fun_binding; "in";
        e = expr LEVEL "top" ->
          <:expr< let module $_uid:m$ = $mb$ in $e$ >>
      | "function"; OPT "|"; l = V (LIST1 match_case SEP "|") ->
          <:expr< fun [ $_list:l$ ] >>
      | "fun"; p = patt LEVEL "simple"; e = fun_def ->
          <:expr< fun [$p$ -> $e$] >>
      | "match"; e = SELF; "with"; OPT "|";
        l = V (LIST1 match_case SEP "|") ->
          <:expr< match $e$ with [ $_list:l$ ] >>
      | "try"; e = SELF; "with"; OPT "|"; l = V (LIST1 match_case SEP "|") ->
          <:expr< try $e$ with [ $_list:l$ ] >>
      | "if"; e1 = SELF; "then"; e2 = expr LEVEL "expr1"; "else";
        e3 = expr LEVEL "expr1" ->
          <:expr< if $e1$ then $e2$ else $e3$ >>
      | "if"; e1 = SELF; "then"; e2 = expr LEVEL "expr1" ->
          <:expr< if $e1$ then $e2$ else () >>
      | "for"; i = V LIDENT; "="; e1 = SELF; df = V direction_flag "to";
        e2 = SELF; "do"; e = V SELF "list"; "done" ->
          let el = Pcaml.vala_map get_seq e in
          <:expr< for $_lid:i$ = $e1$ $_to:df$ $e2$ do { $_list:el$ } >>
      | "while"; e1 = SELF; "do"; e2 = V SELF "list"; "done" ->
          let el = Pcaml.vala_map get_seq e2 in
          <:expr< while $e1$ do { $_list:el$ } >> ]
    | [ e = SELF; ","; el = LIST1 NEXT SEP "," ->
          <:expr< ( $list:[e :: el]$ ) >> ]
    | ":=" NONA
      [ e1 = SELF; ":="; e2 = expr LEVEL "expr1" ->
          <:expr< $e1$.val := $e2$ >>
      | e1 = SELF; "<-"; e2 = expr LEVEL "expr1" -> <:expr< $e1$ := $e2$ >> ]
    | "||" RIGHTA
      [ e1 = SELF; "or"; e2 = SELF -> <:expr< $lid:"or"$ $e1$ $e2$ >>
      | e1 = SELF; "||"; e2 = SELF -> <:expr< $e1$ || $e2$ >> ]
    | "&&" RIGHTA
      [ e1 = SELF; "&"; e2 = SELF -> <:expr< $lid:"&"$ $e1$ $e2$ >>
      | e1 = SELF; "&&"; e2 = SELF -> <:expr< $e1$ && $e2$ >> ]
    | "<" LEFTA
      [ e1 = SELF; "<"; e2 = SELF -> <:expr< $e1$ < $e2$ >>
      | e1 = SELF; ">"; e2 = SELF -> <:expr< $e1$ > $e2$ >>
      | e1 = SELF; "<="; e2 = SELF -> <:expr< $e1$ <= $e2$ >>
      | e1 = SELF; ">="; e2 = SELF -> <:expr< $e1$ >= $e2$ >>
      | e1 = SELF; "="; e2 = SELF -> <:expr< $e1$ = $e2$ >>
      | e1 = SELF; "<>"; e2 = SELF -> <:expr< $e1$ <> $e2$ >>
      | e1 = SELF; "=="; e2 = SELF -> <:expr< $e1$ == $e2$ >>
      | e1 = SELF; "!="; e2 = SELF -> <:expr< $e1$ != $e2$ >>
      | e1 = SELF; op = infixop0; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "^" RIGHTA
      [ e1 = SELF; "^"; e2 = SELF -> <:expr< $e1$ ^ $e2$ >>
      | e1 = SELF; "@"; e2 = SELF -> <:expr< $e1$ @ $e2$ >>
      | e1 = SELF; op = infixop1; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | RIGHTA
      [ e1 = SELF; "::"; e2 = SELF -> <:expr< [$e1$ :: $e2$] >> ]
    | "+" LEFTA
      [ e1 = SELF; "+"; e2 = SELF -> <:expr< $e1$ + $e2$ >>
      | e1 = SELF; "-"; e2 = SELF -> <:expr< $e1$ - $e2$ >>
      | e1 = SELF; op = infixop2; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "*" LEFTA
      [ e1 = SELF; "*"; e2 = SELF -> <:expr< $e1$ * $e2$ >>
      | e1 = SELF; "/"; e2 = SELF -> <:expr< $e1$ / $e2$ >>
      | e1 = SELF; "%"; e2 = SELF -> <:expr< $lid:"%"$ $e1$ $e2$ >>
      | e1 = SELF; "land"; e2 = SELF -> <:expr< $e1$ land $e2$ >>
      | e1 = SELF; "lor"; e2 = SELF -> <:expr< $e1$ lor $e2$ >>
      | e1 = SELF; "lxor"; e2 = SELF -> <:expr< $e1$ lxor $e2$ >>
      | e1 = SELF; "mod"; e2 = SELF -> <:expr< $e1$ mod $e2$ >>
      | e1 = SELF; op = infixop3; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "**" RIGHTA
      [ e1 = SELF; "**"; e2 = SELF -> <:expr< $e1$ ** $e2$ >>
      | e1 = SELF; "asr"; e2 = SELF -> <:expr< $e1$ asr $e2$ >>
      | e1 = SELF; "lsl"; e2 = SELF -> <:expr< $e1$ lsl $e2$ >>
      | e1 = SELF; "lsr"; e2 = SELF -> <:expr< $e1$ lsr $e2$ >>
      | e1 = SELF; op = infixop4; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "unary minus" NONA
      [ "-"; e = SELF -> <:expr< $mkumin loc "-" e$ >>
      | "-."; e = SELF -> <:expr< $mkumin loc "-." e$ >> ]
    | "apply" LEFTA
      [ e1 = SELF; e2 = SELF ->
          let (e1, e2) =
            if is_expr_constr_call e1 then
              match e1 with
              [ <:expr< $e11$ $e12$ >> -> (e11, <:expr< $e12$ $e2$ >>)
              | _ -> (e1, e2) ]
            else (e1, e2)
          in
          match constr_expr_arity loc e1 with
          [ 1 -> <:expr< $e1$ $e2$ >>
          | _ ->
              match e2 with
              [ <:expr< ( $list:el$ ) >> ->
                  List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>) e1 el
              | _ -> <:expr< $e1$ $e2$ >> ] ]
      | "assert"; e = SELF -> <:expr< assert $e$ >>
      | "lazy"; e = SELF -> <:expr< lazy ($e$) >> ]
    | "." LEFTA
      [ e1 = SELF; "."; "("; e2 = SELF; ")" -> <:expr< $e1$ .( $e2$ ) >>
      | e1 = SELF; "."; "["; e2 = SELF; "]" -> <:expr< $e1$ .[ $e2$ ] >>
      | e = SELF; "."; "{"; el = V (LIST1 expr SEP ","); "}" ->
          <:expr< $e$ .{ $_list:el$ } >>
      | e1 = SELF; "."; e2 = SELF -> <:expr< $e1$ . $e2$ >> ]
    | "~-" NONA
      [ "!"; e = SELF -> <:expr< $e$ . val>>
      | "~-"; e = SELF -> <:expr< ~- $e$ >>
      | "~-."; e = SELF -> <:expr< ~-. $e$ >>
      | f = prefixop; e = SELF -> <:expr< $lid:f$ $e$ >> ]
    | "simple" LEFTA
      [ s = V INT -> <:expr< $_int:s$ >>
      | s = V INT_l -> <:expr< $_int32:s$ >>
      | s = V INT_L -> <:expr< $_int64:s$ >>
      | s = V INT_n -> <:expr< $_nativeint:s$ >>
      | s = V FLOAT -> <:expr< $_flo:s$ >>
      | s = V STRING -> <:expr< $_str:s$ >>
      | c = V CHAR -> <:expr< $_chr:c$ >>
      | UIDENT "True" -> <:expr< $uid:" True"$ >>
      | UIDENT "False" -> <:expr< $uid:" False"$ >>
      | i = expr_ident -> i
      | "false" -> <:expr< False >>
      | "true" -> <:expr< True >>
      | "["; "]" -> <:expr< [] >>
      | "["; el = expr1_semi_list; "]" -> <:expr< $mklistexp loc None el$ >>
      | "[|"; "|]" -> <:expr< [| |] >>
      | "[|"; el = V expr1_semi_list "list"; "|]" ->
          <:expr< [| $_list:el$ |] >>
      | "{"; test_label_eq; lel = V lbl_expr_list "list"; "}" ->
          <:expr< { $_list:lel$ } >>
      | "{"; e = expr LEVEL "."; "with"; lel = V lbl_expr_list "list"; "}" ->
          <:expr< { ($e$) with $_list:lel$ } >>
      | "("; ")" -> <:expr< () >>
      | "("; op = operator_rparen -> <:expr< $lid:op$ >>
      | "("; el = V e_phony "list"; ")" -> <:expr< ($_list:el$) >>
      | "("; e = SELF; ":"; t = ctyp; ")" -> <:expr< ($e$ : $t$) >>
      | "("; e = SELF; ")" -> <:expr< $e$ >>
      | "begin"; e = SELF; "end" -> <:expr< $e$ >>
      | "begin"; "end" -> <:expr< () >>
      | x = QUOTATION ->
          let x =
            try
              let i = String.index x ':' in
              (String.sub x 0 i,
               String.sub x (i + 1) (String.length x - i - 1))
            with
            [ Not_found -> ("", x) ]
          in
          Pcaml.handle_expr_quotation loc x ] ]
  ;
  e_phony:
    [ [ -> raise Stream.Failure ] ]
  ;
  let_binding:
    [ [ p = val_ident; e = fun_binding -> (p, e)
      | p = patt; "="; e = expr -> (p, e) ] ]
  ;
(*** JRH added the "translate_operator" here ***)

  val_ident:
    [ [ check_not_part_of_patt; s = LIDENT -> <:patt< $lid:s$ >>
      | check_not_part_of_patt; "("; s = ANY; ")" ->
               let s' = translate_operator s in <:patt< $lid:s'$ >> ] ]
  ;
  fun_binding:
    [ RIGHTA
      [ p = patt LEVEL "simple"; e = SELF -> <:expr< fun $p$ -> $e$ >>
      | "="; e = expr -> <:expr< $e$ >>
      | ":"; t = ctyp; "="; e = expr -> <:expr< ($e$ : $t$) >> ] ]
  ;
  match_case:
    [ [ x1 = patt; w = V (OPT [ "when"; e = expr -> e ]); "->"; x2 = expr ->
          (x1, w, x2) ] ]
  ;
  lbl_expr_list:
    [ [ le = lbl_expr; ";"; lel = SELF -> [le :: lel]
      | le = lbl_expr; ";" -> [le]
      | le = lbl_expr -> [le] ] ]
  ;
  lbl_expr:
    [ [ i = patt_label_ident; "="; e = expr LEVEL "expr1" -> (i, e) ] ]
  ;
  expr1_semi_list:
    [ [ e = expr LEVEL "expr1"; ";"; el = SELF -> [e :: el]
      | e = expr LEVEL "expr1"; ";" -> [e]
      | e = expr LEVEL "expr1" -> [e] ] ]
  ;
  fun_def:
    [ RIGHTA
      [ p = patt LEVEL "simple"; e = SELF -> <:expr< fun $p$ -> $e$ >>
      | "->"; e = expr -> <:expr< $e$ >> ] ]
  ;
  expr_ident:
    [ RIGHTA
      [ i = V LIDENT -> <:expr< $_lid:i$ >>
      | i = V UIDENT -> <:expr< $_uid:i$ >>
      | i = V UIDENT; "."; j = SELF ->
          let rec loop m =
            fun
            [ <:expr< $x$ . $y$ >> -> loop <:expr< $m$ . $x$ >> y
            | e -> <:expr< $m$ . $e$ >> ]
          in
          loop <:expr< $_uid:i$ >> j
      | i = V UIDENT; "."; "("; j = operator_rparen ->
          <:expr< $_uid:i$ . $lid:j$ >> ] ]
  ;
  (* Patterns *)
  patt:
    [ LEFTA
      [ p1 = SELF; "as"; i = LIDENT -> <:patt< ($p1$ as $lid:i$) >> ]
    | LEFTA
      [ p1 = SELF; "|"; p2 = SELF -> <:patt< $p1$ | $p2$ >> ]
    | [ p = SELF; ","; pl = LIST1 NEXT SEP "," ->
          <:patt< ( $list:[p :: pl]$) >> ]
    | NONA
      [ p1 = SELF; ".."; p2 = SELF -> <:patt< $p1$ .. $p2$ >> ]
    | RIGHTA
      [ p1 = SELF; "::"; p2 = SELF -> <:patt< [$p1$ :: $p2$] >> ]
    | LEFTA
      [ p1 = SELF; p2 = SELF ->
          let (p1, p2) =
            match p1 with
            [ <:patt< $p11$ $p12$ >> -> (p11, <:patt< $p12$ $p2$ >>)
            | _ -> (p1, p2) ]
          in
          match constr_patt_arity loc p1 with
          [ 1 -> <:patt< $p1$ $p2$ >>
          | n ->
              let p2 =
                match p2 with
                [ <:patt< _ >> when n > 1 ->
                    let pl =
                      loop n where rec loop n =
                        if n = 0 then [] else [<:patt< _ >> :: loop (n - 1)]
                    in
                    <:patt< ( $list:pl$ ) >>
                | _ -> p2 ]
              in
              match p2 with
              [ <:patt< ( $list:pl$ ) >> ->
                  List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>) p1 pl
              | _ -> <:patt< $p1$ $p2$ >> ] ] ]
    | LEFTA
      [ p1 = SELF; "."; p2 = SELF -> <:patt< $p1$ . $p2$ >> ]
    | "simple"
      [ s = V LIDENT -> <:patt< $_lid:s$ >>
      | s = V UIDENT -> <:patt< $_uid:s$ >>
      | s = V INT -> <:patt< $_int:s$ >>
      | s = V INT_l -> <:patt< $_int32:s$ >>
      | s = V INT_L -> <:patt< $_int64:s$ >>
      | s = V INT_n -> <:patt< $_nativeint:s$ >>
      | "-"; s = INT -> <:patt< $int:"-" ^ s$ >>
      | "-"; s = FLOAT -> <:patt< $flo:"-" ^ s$ >>
      | s = V FLOAT -> <:patt< $_flo:s$ >>
      | s = V STRING -> <:patt< $_str:s$ >>
      | s = V CHAR -> <:patt< $_chr:s$ >>
      | UIDENT "True" -> <:patt< $uid:" True"$ >>
      | UIDENT "False" -> <:patt< $uid:" False"$ >>
      | "false" -> <:patt< False >>
      | "true" -> <:patt< True >>
      | "["; "]" -> <:patt< [] >>
      | "["; pl = patt_semi_list; "]" -> <:patt< $mklistpat loc None pl$ >>
      | "[|"; "|]" -> <:patt< [| |] >>
      | "[|"; pl = V patt_semi_list "list"; "|]" ->
          <:patt< [| $_list:pl$ |] >>
      | "{"; lpl = V lbl_patt_list "list"; "}" ->
          <:patt< { $_list:lpl$ } >>
      | "("; ")" -> <:patt< () >>
      | "("; op = operator_rparen -> <:patt< $lid:op$ >>
      | "("; pl = V p_phony "list"; ")" -> <:patt< ($_list:pl$) >>
      | "("; p = SELF; ":"; t = ctyp; ")" -> <:patt< ($p$ : $t$) >>
      | "("; p = SELF; ")" -> <:patt< $p$ >>
      | "_" -> <:patt< _ >>
      | x = QUOTATION ->
          let x =
            try
              let i = String.index x ':' in
              (String.sub x 0 i,
               String.sub x (i + 1) (String.length x - i - 1))
            with
            [ Not_found -> ("", x) ]
          in
          Pcaml.handle_patt_quotation loc x ] ]
  ;
  p_phony:
    [ [ -> raise Stream.Failure ] ]
  ;
  patt_semi_list:
    [ [ p = patt; ";"; pl = SELF -> [p :: pl]
      | p = patt; ";" -> [p]
      | p = patt -> [p] ] ]
  ;
  lbl_patt_list:
    [ [ le = lbl_patt; ";"; lel = SELF -> [le :: lel]
      | le = lbl_patt; ";" -> [le]
      | le = lbl_patt -> [le] ] ]
  ;
  lbl_patt:
    [ [ i = patt_label_ident; "="; p = patt -> (i, p) ] ]
  ;
  patt_label_ident:
    [ LEFTA
      [ p1 = SELF; "."; p2 = SELF -> <:patt< $p1$ . $p2$ >> ]
    | RIGHTA
      [ i = UIDENT -> <:patt< $uid:i$ >>
      | i = LIDENT -> <:patt< $lid:i$ >> ] ]
  ;
  (* Type declaration *)
  type_declaration:
    [ [ tpl = type_parameters; n = type_patt; "="; pf = V (FLAG "private");
        tk = type_kind; cl = V (LIST0 constrain) ->
          {MLast.tdNam = n; MLast.tdPrm = <:vala< tpl >>;
           MLast.tdPrv = pf; MLast.tdDef = tk; MLast.tdCon = cl}
      | tpl = type_parameters; n = type_patt; cl = V (LIST0 constrain) ->
          {MLast.tdNam = n; MLast.tdPrm = <:vala< tpl >>;
           MLast.tdPrv = <:vala< False >>;
           MLast.tdDef = <:ctyp< '$choose_tvar tpl$ >>; MLast.tdCon = cl} ] ]
  ;
  type_patt:
    [ [ n = V LIDENT -> (loc, n) ] ]
  ;
  constrain:
    [ [ "constraint"; t1 = ctyp; "="; t2 = ctyp -> (t1, t2) ] ]
  ;
  type_kind:
    [ [ test_constr_decl; OPT "|";
        cdl = LIST1 constructor_declaration SEP "|" ->
          <:ctyp< [ $list:cdl$ ] >>
      | t = ctyp ->
          <:ctyp< $t$ >>
      | t = ctyp; "="; "{"; ldl = V label_declarations "list"; "}" ->
          <:ctyp< $t$ == { $_list:ldl$ } >>
      | t = ctyp; "="; OPT "|"; cdl = LIST1 constructor_declaration SEP "|" ->
          <:ctyp< $t$ == [ $list:cdl$ ] >>
      | "{"; ldl = V label_declarations "list"; "}" ->
          <:ctyp< { $_list:ldl$ } >> ] ]
  ;
  type_parameters:
    [ [ -> (* empty *) []
      | tp = type_parameter -> [tp]
      | "("; tpl = LIST1 type_parameter SEP ","; ")" -> tpl ] ]
  ;
  type_parameter:
    [ [ "'"; i = V ident "" -> (i, (False, False))
      | "+"; "'"; i = V ident "" -> (i, (True, False))
      | "-"; "'"; i = V ident "" -> (i, (False, True)) ] ]
  ;
  constructor_declaration:
    [ [ ci = cons_ident; "of"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*") ->
          (loc, ci, cal)
      | ci = cons_ident -> (loc, ci, <:vala< [] >>) ] ]
  ;
  cons_ident:
    [ [ i = V UIDENT "uid" "" -> i
      | UIDENT "True" -> <:vala< " True" >>
      | UIDENT "False" -> <:vala< " False" >> ] ]
  ;
  label_declarations:
    [ [ ld = label_declaration; ";"; ldl = SELF -> [ld :: ldl]
      | ld = label_declaration; ";" -> [ld]
      | ld = label_declaration -> [ld] ] ]
  ;
  label_declaration:
    [ [ i = LIDENT; ":"; t = poly_type -> (loc, i, False, t)
      | "mutable"; i = LIDENT; ":"; t = poly_type -> (loc, i, True, t) ] ]
  ;
  (* Core types *)
  ctyp:
    [ [ t1 = SELF; "as"; "'"; i = ident -> <:ctyp< $t1$ as '$i$ >> ]
    | "arrow" RIGHTA
      [ t1 = SELF; "->"; t2 = SELF -> <:ctyp< $t1$ -> $t2$ >> ]
    | "star"
      [ t = SELF; "*"; tl = LIST1 (ctyp LEVEL "apply") SEP "*" ->
          <:ctyp< ( $list:[t :: tl]$ ) >> ]
    | "apply"
      [ t1 = SELF; t2 = SELF -> <:ctyp< $t2$ $t1$ >> ]
    | "ctyp2"
      [ t1 = SELF; "."; t2 = SELF -> <:ctyp< $t1$ . $t2$ >>
      | t1 = SELF; "("; t2 = SELF; ")" -> <:ctyp< $t1$ $t2$ >> ]
    | "simple"
      [ "'"; i = V ident "" -> <:ctyp< '$_:i$ >>
      | "_" -> <:ctyp< _ >>
      | i = V LIDENT -> <:ctyp< $_lid:i$ >>
      | i = V UIDENT -> <:ctyp< $_uid:i$ >>
      | "("; t = SELF; ","; tl = LIST1 ctyp SEP ","; ")";
        i = ctyp LEVEL "ctyp2" ->
          List.fold_left (fun c a -> <:ctyp< $c$ $a$ >>) i [t :: tl]
      | "("; t = SELF; ")" -> <:ctyp< $t$ >> ] ]
  ;
  (* Identifiers *)
  ident:
    [ [ i = LIDENT -> i
      | i = UIDENT -> i ] ]
  ;
  mod_ident:
    [ RIGHTA
      [ i = UIDENT -> [i]
      | i = LIDENT -> [i]
      | i = UIDENT; "."; j = SELF -> [i :: j] ] ]
  ;
  (* Miscellaneous *)
  direction_flag:
    [ [ "to" -> True
      | "downto" -> False ] ]
  ;
  (* Objects and Classes *)
  str_item:
    [ [ "class"; cd = V (LIST1 class_declaration SEP "and") ->
          <:str_item< class $_list:cd$ >>
      | "class"; "type"; ctd = V (LIST1 class_type_declaration SEP "and") ->
          <:str_item< class type $_list:ctd$ >> ] ]
  ;
  sig_item:
    [ [ "class"; cd = V (LIST1 class_description SEP "and") ->
          <:sig_item< class $_list:cd$ >>
      | "class"; "type"; ctd = V (LIST1 class_type_declaration SEP "and") ->
          <:sig_item< class type $_list:ctd$ >> ] ]
  ;
  (* Class expressions *)
  class_declaration:
    [ [ vf = V (FLAG "virtual"); ctp = class_type_parameters; i = V LIDENT;
        cfb = class_fun_binding ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = i; MLast.ciExp = cfb} ] ]
  ;
  class_fun_binding:
    [ [ "="; ce = class_expr -> ce
      | ":"; ct = class_type; "="; ce = class_expr ->
          <:class_expr< ($ce$ : $ct$) >>
      | p = patt LEVEL "simple"; cfb = SELF ->
          <:class_expr< fun $p$ -> $cfb$ >> ] ]
  ;
  class_type_parameters:
    [ [ -> (loc, <:vala< [] >>)
      | "["; tpl = V (LIST1 type_parameter SEP ","); "]" -> (loc, tpl) ] ]
  ;
  class_fun_def:
    [ [ p = patt LEVEL "simple"; "->"; ce = class_expr ->
          <:class_expr< fun $p$ -> $ce$ >>
      | p = patt LEVEL "simple"; cfd = SELF ->
          <:class_expr< fun $p$ -> $cfd$ >> ] ]
  ;
  class_expr:
    [ "top"
      [ "fun"; cfd = class_fun_def -> cfd
      | "let"; rf = V (FLAG "rec"); lb = V (LIST1 let_binding SEP "and");
        "in"; ce = SELF ->
          <:class_expr< let $_flag:rf$ $_list:lb$ in $ce$ >> ]
    | "apply" LEFTA
      [ ce = SELF; e = expr LEVEL "label" ->
          <:class_expr< $ce$ $e$ >> ]
    | "simple"
      [ "["; ct = ctyp; ","; ctcl = LIST1 ctyp SEP ","; "]";
        ci = class_longident ->
          <:class_expr< $list:ci$ [ $list:[ct :: ctcl]$ ] >>
      | "["; ct = ctyp; "]"; ci = class_longident ->
          <:class_expr< $list:ci$ [ $ct$ ] >>
      | ci = class_longident -> <:class_expr< $list:ci$ >>
      | "object"; cspo = V (OPT class_self_patt);
        cf = V class_structure "list"; "end" ->
          <:class_expr< object $_opt:cspo$ $_list:cf$ end >>
      | "("; ce = SELF; ":"; ct = class_type; ")" ->
          <:class_expr< ($ce$ : $ct$) >>
      | "("; ce = SELF; ")" -> ce ] ]
  ;
  class_structure:
    [ [ cf = LIST0 class_str_item -> cf ] ]
  ;
  class_self_patt:
    [ [ "("; p = patt; ")" -> p
      | "("; p = patt; ":"; t = ctyp; ")" -> <:patt< ($p$ : $t$) >> ] ]
  ;
  class_str_item:
    [ [ "inherit"; ce = class_expr; pb = V (OPT [ "as"; i = LIDENT -> i ]) ->
          <:class_str_item< inherit $ce$ $_opt:pb$ >>
      | "val"; mf = V (FLAG "mutable"); lab = V label "lid" "";
        e = cvalue_binding ->
          <:class_str_item< value $_flag:mf$ $_lid:lab$ = $e$ >>
      | "method"; "private"; "virtual"; l = V label "lid" ""; ":";
        t = poly_type ->
          <:class_str_item< method virtual private $_lid:l$ : $t$ >>
      | "method"; "virtual"; "private"; l = V label "lid" ""; ":";
        t = poly_type ->
          <:class_str_item< method virtual private $_lid:l$ : $t$ >>
      | "method"; "virtual"; l = V label "lid" ""; ":"; t = poly_type ->
          <:class_str_item< method virtual $_lid:l$ : $t$ >>
      | "method"; "private"; l = V label "lid" ""; ":"; t = poly_type; "=";
        e = expr ->
          <:class_str_item< method private $_lid:l$ : $t$ = $e$ >>
      | "method"; "private"; l = V label "lid" ""; sb = fun_binding ->
          <:class_str_item< method private $_lid:l$ = $sb$ >>
      | "method"; l = V label "lid" ""; ":"; t = poly_type; "="; e = expr ->
          <:class_str_item< method $_lid:l$ : $t$ = $e$ >>
      | "method"; l = V label "lid" ""; sb = fun_binding ->
          <:class_str_item< method $_lid:l$ = $sb$ >>
      | "constraint"; t1 = ctyp; "="; t2 = ctyp ->
          <:class_str_item< type $t1$ = $t2$ >>
      | "initializer"; se = expr -> <:class_str_item< initializer $se$ >> ] ]
  ;
  cvalue_binding:
    [ [ "="; e = expr -> e
      | ":"; t = ctyp; "="; e = expr -> <:expr< ($e$ : $t$) >>
      | ":"; t = ctyp; ":>"; t2 = ctyp; "="; e = expr ->
          <:expr< ($e$ : $t$ :> $t2$) >>
      | ":>"; t = ctyp; "="; e = expr ->
          <:expr< ($e$ :> $t$) >> ] ]
  ;
  label:
    [ [ i = LIDENT -> i ] ]
  ;
  (* Class types *)
  class_type:
    [ [ test_ctyp_minusgreater; t = ctyp LEVEL "star"; "->"; ct = SELF ->
          <:class_type< [ $t$ ] -> $ct$ >>
      | cs = class_signature -> cs ] ]
  ;
  class_signature:
    [ [ "["; tl = LIST1 ctyp SEP ","; "]"; id = clty_longident ->
          <:class_type< $list:id$ [ $list:tl$ ] >>
      | id = clty_longident -> <:class_type< $list:id$ >>
      | "object"; cst = V (OPT class_self_type);
        csf = V (LIST0 class_sig_item); "end" ->
          <:class_type< object $_opt:cst$ $_list:csf$ end >> ] ]
  ;
  class_self_type:
    [ [ "("; t = ctyp; ")" -> t ] ]
  ;
  class_sig_item:
    [ [ "inherit"; cs = class_signature ->
          <:class_sig_item< inherit $cs$ >>
      | "val"; mf = V (FLAG "mutable"); l = V label "lid" ""; ":"; t = ctyp ->
          <:class_sig_item< value $_flag:mf$ $_lid:l$ : $t$ >>
      | "method"; "private"; "virtual"; l = V label "lid" ""; ":";
        t = poly_type ->
          <:class_sig_item< method virtual private $_lid:l$ : $t$ >>
      | "method"; "virtual"; "private"; l = V label "lid" ""; ":";
        t = poly_type ->
          <:class_sig_item< method virtual private $_lid:l$ : $t$ >>
      | "method"; "virtual"; l = V label "lid" ""; ":"; t = poly_type ->
          <:class_sig_item< method virtual $_lid:l$ : $t$ >>
      | "method"; "private"; l = V label "lid" ""; ":"; t = poly_type ->
          <:class_sig_item< method private $_lid:l$ : $t$ >>
      | "method"; l = V label "lid" ""; ":"; t = poly_type ->
          <:class_sig_item< method $_lid:l$ : $t$ >>
      | "constraint"; t1 = ctyp; "="; t2 = ctyp ->
          <:class_sig_item< type $t1$ = $t2$ >> ] ]
  ;
  class_description:
    [ [ vf = V (FLAG "virtual"); ctp = class_type_parameters; n = V LIDENT;
        ":"; ct = class_type ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = ct} ] ]
  ;
  class_type_declaration:
    [ [ vf = V (FLAG "virtual"); ctp = class_type_parameters; n = V LIDENT;
        "="; cs = class_signature ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = cs} ] ]
  ;
  (* Expressions *)
  expr: LEVEL "simple"
    [ LEFTA
      [ "new"; i = V class_longident "list" -> <:expr< new $_list:i$ >>
      | "object"; cspo = V (OPT class_self_patt);
        cf = V class_structure "list"; "end" ->
          <:expr< object $_opt:cspo$ $_list:cf$ end >> ] ]
  ;
  expr: LEVEL "."
    [ [ e = SELF; "#"; lab = V label "lid" -> <:expr< $e$ # $_lid:lab$ >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; e = SELF; ":"; t = ctyp; ":>"; t2 = ctyp; ")" ->
          <:expr< ($e$ : $t$ :> $t2$) >>
      | "("; e = SELF; ":>"; t = ctyp; ")" -> <:expr< ($e$ :> $t$) >>
      | "{<"; ">}" -> <:expr< {< >} >>
      | "{<"; fel = V field_expr_list "list"; ">}" ->
          <:expr< {< $_list:fel$ >} >> ] ]
  ;
  field_expr_list:
    [ [ l = label; "="; e = expr LEVEL "expr1"; ";"; fel = SELF ->
          [(l, e) :: fel]
      | l = label; "="; e = expr LEVEL "expr1"; ";" -> [(l, e)]
      | l = label; "="; e = expr LEVEL "expr1" -> [(l, e)] ] ]
  ;
  (* Core types *)
  ctyp: LEVEL "simple"
    [ [ "#"; id = V class_longident "list" ->
         <:ctyp< # $_list:id$ >>
      | "<"; ml = V meth_list "list"; v = V (FLAG ".."); ">" ->
          <:ctyp< < $_list:ml$ $_flag:v$ > >>
      | "<"; ".."; ">" ->
         <:ctyp< < .. > >>
      | "<"; ">" ->
          <:ctyp< < > >> ] ]
  ;
  meth_list:
    [ [ f = field; ";"; ml = SELF -> [f :: ml]
      | f = field; ";" -> [f]
      | f = field -> [f] ] ]
  ;
  field:
    [ [ lab = LIDENT; ":"; t = poly_type -> (lab, t) ] ]
  ;
  (* Polymorphic types *)
  typevar:
    [ [ "'"; i = ident -> i ] ]
  ;
  poly_type:
    [ [ test_typevar_list_dot; tpl = LIST1 typevar; "."; t2 = ctyp ->
          <:ctyp< ! $list:tpl$ . $t2$ >>
      | t = ctyp -> t ] ]
  ;
  (* Identifiers *)
  clty_longident:
    [ [ m = UIDENT; "."; l = SELF -> [m :: l]
      | i = LIDENT -> [i] ] ]
  ;
  class_longident:
    [ [ m = UIDENT; "."; l = SELF -> [m :: l]
      | i = LIDENT -> [i] ] ]
  ;
  (* Labels *)
  ctyp: AFTER "arrow"
    [ NONA
      [ i = V LIDENT; ":"; t = SELF -> <:ctyp< ~$_:i$: $t$ >>
      | i = V QUESTIONIDENTCOLON; t = SELF -> <:ctyp< ?$_:i$: $t$ >>
      | i = V QUESTIONIDENT; ":"; t = SELF -> <:ctyp< ?$_:i$: $t$ >> ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "["; OPT "|"; rfl = V (LIST1 poly_variant SEP "|"); "]" ->
          <:ctyp< [ = $_list:rfl$ ] >>
      | "["; ">"; "]" -> <:ctyp< [ > $list:[]$ ] >>
      | "["; ">"; OPT "|"; rfl = V (LIST1 poly_variant SEP "|"); "]" ->
          <:ctyp< [ > $_list:rfl$ ] >>
      | "[<"; OPT "|"; rfl = V (LIST1 poly_variant SEP "|"); "]" ->
          <:ctyp< [ < $_list:rfl$ ] >>
      | "[<"; OPT "|"; rfl = V (LIST1 poly_variant SEP "|"); ">";
        ntl = V (LIST1 name_tag); "]" ->
          <:ctyp< [ < $_list:rfl$ > $_list:ntl$ ] >> ] ]
  ;
  poly_variant:
    [ [ "`"; i = V ident "" -> <:poly_variant< ` $_:i$ >>
      | "`"; i = V ident ""; "of"; ao = V (FLAG "&");
        l = V (LIST1 ctyp SEP "&") ->
          <:poly_variant< `$_:i$ of $_flag:ao$ $_list:l$ >>
      | t = ctyp -> MLast.PvInh t ] ]
  ;
  name_tag:
    [ [ "`"; i = ident -> i ] ]
  ;
  expr: LEVEL "expr1"
    [ [ "fun"; p = labeled_patt; e = fun_def -> <:expr< fun $p$ -> $e$ >> ] ]
  ;
  expr: AFTER "apply"
    [ "label"
      [ i = V TILDEIDENTCOLON; e = SELF -> <:expr< ~$_:i$: $e$ >>
      | i = V TILDEIDENT -> <:expr< ~$_:i$ >>
      | i = V QUESTIONIDENTCOLON; e = SELF -> <:expr< ?$_:i$: $e$ >>
      | i = V QUESTIONIDENT -> <:expr< ?$_:i$ >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "`"; s = V ident "" -> <:expr< ` $_:s$ >> ] ]
  ;
  fun_def:
    [ [ p = labeled_patt; e = SELF -> <:expr< fun $p$ -> $e$ >> ] ]
  ;
  fun_binding:
    [ [ p = labeled_patt; e = SELF -> <:expr< fun $p$ -> $e$ >> ] ]
  ;
  patt: LEVEL "simple"
    [ [ "`"; s = V ident "" -> <:patt< ` $_:s$ >>
      | "#"; t = V mod_ident "list" "" -> <:patt< # $_list:t$ >>
      | p = labeled_patt -> p ] ]
  ;
  labeled_patt:
    [ [ i = V TILDEIDENTCOLON; p = patt LEVEL "simple" ->
           <:patt< ~$_:i$: $p$ >>
      | i = V TILDEIDENT ->
           <:patt< ~$_:i$ >>
      | "~"; "("; i = LIDENT; ")" ->
           <:patt< ~$i$ >>
      | "~"; "("; i = LIDENT; ":"; t = ctyp; ")" ->
           <:patt< ~$i$: ($lid:i$ : $t$) >>
      | i = V QUESTIONIDENTCOLON; j = LIDENT ->
           <:patt< ?$_:i$: ($lid:j$) >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt; "="; e = expr; ")" ->
          <:patt< ?$_:i$: ( $p$ = $e$ ) >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt; ":"; t = ctyp; ")" ->
          <:patt< ?$_:i$: ( $p$ : $t$ ) >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt; ":"; t = ctyp; "=";
        e = expr; ")" ->
          <:patt< ?$_:i$: ( $p$ : $t$ = $e$ ) >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt; ")" ->
          <:patt< ?$_:i$: ( $p$ ) >>
      | i = V QUESTIONIDENT -> <:patt< ?$_:i$ >>
      | "?"; "("; i = LIDENT; "="; e = expr; ")" ->
          <:patt< ? ( $lid:i$ = $e$ ) >>
      | "?"; "("; i = LIDENT; ":"; t = ctyp; "="; e = expr; ")" ->
          <:patt< ? ( $lid:i$ : $t$ = $e$ ) >>
      | "?"; "("; i = LIDENT; ")" ->
          <:patt< ?$i$ >>
      | "?"; "("; i = LIDENT; ":"; t = ctyp; ")" ->
          <:patt< ? ( $lid:i$ : $t$ ) >> ] ]
  ;
  class_type:
    [ [ i = LIDENT; ":"; t = ctyp LEVEL "apply"; "->"; ct = SELF ->
          <:class_type< [ ~$i$: $t$ ] -> $ct$ >>
      | i = V QUESTIONIDENTCOLON; t = ctyp LEVEL "apply"; "->"; ct = SELF ->
          <:class_type< [ ?$_:i$: $t$ ] -> $ct$ >>
      | i = V QUESTIONIDENT; ":"; t = ctyp LEVEL "apply"; "->"; ct = SELF ->
          <:class_type< [ ?$_:i$: $t$ ] -> $ct$ >> ] ]
  ;
  class_fun_binding:
    [ [ p = labeled_patt; cfb = SELF -> <:class_expr< fun $p$ -> $cfb$ >> ] ]
  ;
  class_fun_def:
    [ [ p = labeled_patt; "->"; ce = class_expr ->
          <:class_expr< fun $p$ -> $ce$ >>
      | p = labeled_patt; cfd = SELF ->
          <:class_expr< fun $p$ -> $cfd$ >> ] ]
  ;
END;

(* Main entry points *)

EXTEND
  GLOBAL: interf implem use_file top_phrase expr patt;
  interf:
    [ [ si = sig_item_semi; (sil, stopped) = SELF -> ([si :: sil], stopped)
      | "#"; n = LIDENT; dp = OPT expr; ";;" ->
          ([(<:sig_item< # $lid:n$ $opt:dp$ >>, loc)], True)
      | EOI -> ([], False) ] ]
  ;
  sig_item_semi:
    [ [ si = sig_item; OPT ";;" -> (si, loc) ] ]
  ;
  implem:
    [ [ si = str_item_semi; (sil, stopped) = SELF -> ([si :: sil], stopped)
      | "#"; n = LIDENT; dp = OPT expr; ";;" ->
          ([(<:str_item< # $lid:n$ $opt:dp$ >>, loc)], True)
      | EOI -> ([], False) ] ]
  ;
  str_item_semi:
    [ [ si = str_item; OPT ";;" -> (si, loc) ] ]
  ;
  top_phrase:
    [ [ ph = phrase; ";;" -> Some ph
      | EOI -> None ] ]
  ;
  use_file:
    [ [ si = str_item; OPT ";;"; (sil, stopped) = SELF ->
          ([si :: sil], stopped)
      | "#"; n = LIDENT; dp = OPT expr; ";;" ->
          ([<:str_item< # $lid:n$ $opt:dp$ >>], True)
      | EOI -> ([], False) ] ]
  ;
  phrase:
    [ [ sti = str_item -> sti
      | "#"; n = LIDENT; dp = OPT expr ->
          <:str_item< # $lid:n$ $opt:dp$ >> ] ]
  ;
END;

Pcaml.add_option "-no_quot" (Arg.Set no_quotations)
  "Don't parse quotations, allowing to use, e.g. \"<:>\" as token";

(* ------------------------------------------------------------------------- *)
(* Added by JRH ***                                                          *)
(* ------------------------------------------------------------------------- *)

EXTEND
  expr: AFTER "<"
   [[ f = expr; "o"; g = expr -> <:expr< ((o $f$) $g$) >>
    | f = expr; "upto"; g = expr -> <:expr< ((upto $f$) $g$) >>
    | f = expr; "F_F"; g = expr -> <:expr< ((f_f_ $f$) $g$) >>
    | f = expr; "THENC"; g = expr -> <:expr< ((thenc_ $f$) $g$) >>
    | f = expr; "THEN"; g = expr -> <:expr< ((then_ $f$) $g$) >>
    | f = expr; "THENL"; g = expr -> <:expr< ((thenl_ $f$) $g$) >>
    | f = expr; "ORELSE"; g = expr -> <:expr< ((orelse_ $f$) $g$) >>
    | f = expr; "ORELSEC"; g = expr -> <:expr< ((orelsec_ $f$) $g$) >>
    | f = expr; "THEN_TCL"; g = expr -> <:expr< ((then_tcl_ $f$) $g$) >>
    | f = expr; "ORELSE_TCL"; g = expr -> <:expr< ((orelse_tcl_ $f$) $g$) >>
]];
END;

EXTEND
  top_phrase:
   [ [ sti = str_item; ";;" ->
         match sti with
         [ <:str_item< $exp:e$ >> -> Some <:str_item< value it = $e$ >>
         | x -> Some x ] ] ]
  ;
END;
