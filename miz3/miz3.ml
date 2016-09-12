needs "Examples/holby.ml";;

let horizon = ref 1;;
let timeout = ref 1;;
let default_prover = ref ("HOL_BY", CONV_TAC o HOL_BY);;
let renumber_labels = ref true;;
let extra_labels = ref 0;;
let start_label = ref 1;;
let growth_mode = ref true;;
let proof_indent = ref "  ";;
let proof_width = ref 72;;
let grow_haves = ref true;;
let grow_duplicates = ref 0;;
let indent_continued = ref false;;
let sketch_mode = ref false;;
let silent_server = ref 1;;
let explain_errors = ref 1;;
let miz3_pid = ref "/tmp/miz3_pid";;
let miz3_filename = ref "/tmp/miz3_filename";;

let ERRORS =
  ["1: inference error";
   "2: inference time-out";
   "3: skeleton error";
   "4: unknown label";
   "5: error ocaml (or justification)";
   "6: underspecified types hol";
   "7: unbound free variables hol";
   "8: syntax or type error hol";
   "9: syntax error mizar"];;

let mizar_step_words =
  ["assume"; "cases"; "case"; "consider"; "end"; "let"; "now"; "proof";
   "qed"; "set"; "suppose"; "take"; "thus"];;

let mizar_step_words = mizar_step_words @
  ["exec"];;

let mizar_words = mizar_step_words @
  ["be"; "being"; "by"; "from"; "such"; "that"];;

let mizar_skip_bracketed =
  [","; ";"; "["];;

reserve_words (subtract mizar_words (reserved_words()));;

type by_item =
| Label of string
| Thm of string * thm
| Tactic of string * (thm list -> tactic)
| Grow of string * (thm list -> tactic)
| Hole;;

type step =
  int * (string * lexcode * string) list list * substep

and substep =
| Have of term * string list * just
| Now of string list * just
| Let of term list
| Assume of term * string list
| Thus of term * string list * just
| Qed of just
| Bracket_proof
| Bracket_end
| Take of term
| Consider of term list * term * string list * just
| Set of term * string list
| Cases of just * just list
| Bracket_case
| Suppose of term * string list
| Exec of string * tactic
| Error of string * just
| Error_point
| Empty_step

and just =
| By of by_item list * by_item list * bool
| Proof of step option * step list * step option
| Proof_expected of bool
| No_steps;;

unset_jrh_lexer;;

let system_ok = Unix.WEXITED 0;;
let wronly = Unix.O_WRONLY;;
let usr2_handler = ref (fun () -> print_string "usr2_handler\n");;
Sys.signal Sys.sigusr2 (Sys.Signal_handle (fun _ -> !usr2_handler ()));;

set_jrh_lexer;;

let rawtoken =
  let collect (h,t) = end_itlist (^) (h::t) in
  let stringof p = atleast 1 p >> end_itlist (^) in
  let simple_ident = stringof(some isalnum) ||| stringof(some issymb) in
  let undertail = stringof (a "_") ++ possibly simple_ident >> collect in
  let ident = (undertail ||| simple_ident) ++ many undertail >> collect in
  let septok = stringof(some issep) in
  let stringchar =
      some (fun i -> i <> "\\" && i <> "\"")
  ||| (a "\\" ++ some (fun _ -> true) >> fun (_,x) -> "\\"^x) in
  let string = a "\"" ++ many stringchar ++ ((a "\"" >> K 0) ||| finished) >>
        (fun ((_,s),_) -> "\""^implode s^"\"") in
  (string ||| some isbra ||| septok ||| ident ||| a "`");;

let rec whitespace e i =
  let non_newline i =
    if i <> [] && hd i <> "\n" then hd i,tl i else raise Noparse in
  let rest_of_line = many non_newline ++ (a "\n" ||| (finished >> K "")) >>
    fun x,y -> itlist (^) x y in
  let comment_string =
    match !comment_token with
    | Resword t -> t
    | Ident t -> t in
  match i with
  | [] -> if e then "",i else raise Noparse
  | (" " as c)::rst | ("\t" as c)::rst | ("\r" as c)::rst ->
      let s,rst1 = whitespace true rst in c^s,rst1
  | ("\n" as c)::rst -> c,rst
  | _ ->
      let t,rst = rawtoken i in
      if t = comment_string then (rest_of_line >> fun x -> t^x) rst
      else if String.length t >= 2 && String.sub t 0 2 = "::" then
        (rest_of_line >> fun x -> if e then t^x else "") rst
      else if e then "",i else raise Noparse;;

let lex1 =
  let reserve1 n =
    if is_reserved_word n then Resword n else Ident n in
  let rec tokens i =
    try (many (whitespace false) ++ rawtoken ++ whitespace true
        ++ tokens >>
      fun (((x,y),z),w) -> (implode x,reserve1 y,z)::w) i
    with Noparse -> [],i in
  fun l ->
    let (toks,rst) = tokens l in
    let rst',rst'' = many (whitespace false) rst in
    if rst'' <> [] then failwith "lex1" else
    if toks = [] then toks else
    let (x,y,z) = last toks in
    butlast toks@[x,y,z^implode rst'];;

let lex2 = lex1 o explode;;

let middle (_,x,_) = x;;

let a' t toks =
  match toks with
  | ((_,Resword t',_) as tok)::rst when t = t' -> tok,rst
  | ((_,Ident t',_) as tok)::rst when t = t' -> tok,rst
  | _ -> raise Noparse;;

let a_semi = a' ";";;

let ident' toks =
  match toks with
  | (_,Ident s,_)::rst -> s,rst
  | (_,Resword "(",_)::(_,Ident s,_)::(_,Resword ")",_)::rst -> s,rst
  | _ -> raise Noparse;;

let unident' s =
  if parses_as_binder s || can get_infix_status s || is_prefix s
    then ["",Resword "(",""; "",Ident s,""; "",Resword ")",""]
    else ["",Ident s,""];;

let rec cut_to b n c l toks =
  match toks with
  | [] -> if b then [],[] else raise Noparse
  | tok::rst ->
     (match tok with
      | _,Resword s,_ | _,Ident s,_ ->
          let x = not (n > 0 && mem s mizar_skip_bracketed) in
          if mem s c && x then [tok],rst else
          if b && mem s l && x then [],toks else
          let stp1,rst1 =
           (match s with
            | "(" | "[" -> cut_to true (n + 1) c l rst
            | ")" | "]" -> cut_to true (if n > 0 then n - 1 else 0) c l rst
            | _ -> cut_to true n c l rst) in
          (tok::stp1),rst1);;

let cut_step toks =
  match toks with
  | (_,Resword "proof",_ as tok)::rst -> [tok],rst
  | (_,Resword "now",_)::rst ->
      (a' "now" ++
        (many (a' "[" ++ cut_to false 0 ["]"] mizar_step_words >>
          fun x,y -> x::y)) >> fun x,y -> x::(itlist (@) y [])) toks
  | _ -> cut_to false 0 [";"] mizar_step_words toks;;

let rec cut_steps toks =
  let steps,rst = many cut_step toks in
  if rst = [] then steps else steps@[rst];;

let strings_of_toks toks =
  let rec string_of_toks1 toks =
    match toks with
    | [] -> "",""
    | [x,Ident y,z] | [x,Resword y,z] -> x^y,z
    | (x,Ident y,z)::rst | (x,Resword y,z)::rst  ->
        let u,v = string_of_toks1 rst in x^y^z^u,v in
  match toks with
  | [] -> "","",""
  | [x,Ident y,z] | [x,Resword y,z] -> x,y,z
  | (x,Ident y,z)::rst | (x,Resword y,z)::rst ->
      let u,v = string_of_toks1 rst in x,y^z^u,v;;

let string_of_toks = middle o strings_of_toks;;

let split_string = map string_of_toks o cut_steps o lex2;;

let tok_of_toks toks =
  let x,y,z = strings_of_toks toks in
  x,Ident y,z;;

let exec_phrase b s =
  let lexbuf = Lexing.from_string s in
  let ok = Toploop.execute_phrase b Format.std_formatter
    (!Toploop.parse_toplevel_phrase lexbuf) in
  Format.pp_print_flush Format.std_formatter ();
  (ok,
   let i = lexbuf.Lexing.lex_curr_pos in
   String.sub lexbuf.Lexing.lex_buffer
     i (lexbuf.Lexing.lex_buffer_len - i));;

let exec_thm_out = ref TRUTH;;

let exec_thm s =
  try
    let ok,rst = exec_phrase false
      ("exec_thm_out := (("^s^") : thm);;") in
    if not ok || rst <> "" then raise Noparse;
    !exec_thm_out
  with _ -> raise Noparse;;

let exec_thmlist_tactic_out = ref REWRITE_TAC;;

let exec_thmlist_tactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_thmlist_tactic_out := (("^s^") : thm list -> tactic);;") in
    if not ok || rst <> "" then raise Noparse;
    !exec_thmlist_tactic_out
  with _ -> raise Noparse;;

let exec_thmtactic_out = ref MATCH_MP_TAC;;

let exec_thmtactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_thmtactic_out := (("^s^") : thm -> tactic);;") in
    if not ok || rst <> "" then raise Noparse;
    !exec_thmtactic_out
  with _ -> raise Noparse;;

let exec_tactic_out = ref ALL_TAC;;

let exec_tactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_tactic_out := (("^s^") : tactic);;") in
    if not ok || rst <> "" then raise Noparse;
    !exec_tactic_out
  with _ -> raise Noparse;;

let exec_conv_out = ref NUM_REDUCE_CONV;;

let exec_conv s =
  try
    let ok,rst = exec_phrase false
      ("exec_conv_out := (("^s^") : conv);;") in
    if not ok || rst <> "" then raise Noparse;
    !exec_conv_out
  with _ -> raise Noparse;;

let (MP_ALL : tactic -> thm list -> tactic) =
  fun tac ths ->
    MAP_EVERY MP_TAC ths THEN tac;;

let use_thms tac =
  fun ths -> tac ORELSE MP_ALL tac ths;;

let by_item_cache = ref undefined;;

let rec by_item_of_toks toks =
  match toks with
  | [_,Ident "#",_] -> Hole
  | (_,Ident "#",_)::toks' ->
     (match by_item_of_toks toks' with
      | Tactic(s,tac) -> Grow(s,tac)
      | _ -> failwith "by_item_of_toks")
  | [_,Ident "*",_] -> Label "*"
  | _ ->
  let s = string_of_toks toks in
  try apply (!by_item_cache) s with _ ->
  let i =
    try Thm (s, exec_thm s) with _ ->
    try Tactic (s, exec_thmlist_tactic s) with _ ->
    try Tactic (s, (exec_thmtactic s) o hd) with _ ->
    try Tactic (s, use_thms (exec_tactic s)) with _ ->
    try Tactic (s, use_thms (CONV_TAC (exec_conv s))) with _ ->
    match toks with
    | [_,Ident s,_] -> Label s
    | _ -> failwith "by_item_of_toks" in
  by_item_cache := (s |-> i) !by_item_cache;
  i;;

let parse_by =
  let parse_by_item toks =
    match toks with
    | (_,Ident "#",_ as tok1)::(_,Ident s,_ as tok2)::toks when s <> "," ->
        [tok1;tok2],toks
    | (_,Ident _,_ as tok)::toks -> [tok],toks
    | _ -> raise Noparse in
  let parse_by_part =
     ((a' "by" ++ many (parse_by_item ++ a' "," >> fst) >> snd) ++
       parse_by_item) >>
          (fun (x,y) -> x@[y])
  ||| (nothing >> K [])
  and parse_from_part =
     ((a' "from" ++ many (parse_by_item ++ a' "," >> fst) >> snd) ++
       parse_by_item) >>
          (fun (x,y) -> (x@[y]),true)
  ||| (nothing >> K ([],false)) in
  let rec will_grow l =
    match l with
    | [] -> false
    | Tactic _::_ -> false
    | Grow _::_ -> true
    | _::l' -> will_grow l'
  in
     ((parse_by_part ++ parse_from_part) ++ a_semi ++ finished >>
        fun (((x,(y,z)),_),_) ->
          let x' = map by_item_of_toks x in
          let y' = map by_item_of_toks y in
          By(x',y',z || will_grow (x'@y')))
  ||| (finished >> K (Proof_expected true));;

let rec parse_labels toks =
  match toks with
  | [] -> []
  | (_,Resword "[",_)::(_,Ident s,_)::(_,Resword "]",_)::rst ->
      s::(parse_labels rst)
  | _ -> raise Noparse;;

let rec type_of_pretype1 ty =
  match ty with
    Stv n -> failwith "type_of_pretype1"
  | Utv(v) -> mk_vartype(v)
  | Ptycon(con,args) -> mk_type(con,map type_of_pretype1 args);;

let term_of_preterm1 =
  let rec term_of_preterm1 ptm =
    match ptm with
      Varp(s,pty) -> mk_var(s,type_of_pretype1 pty)
    | Constp(s,pty) -> mk_mconst(s,type_of_pretype1 pty)
    | Combp(l,r) -> mk_comb(term_of_preterm1 l,term_of_preterm1 r)
    | Absp(v,bod) -> mk_gabs(term_of_preterm1 v,term_of_preterm1 bod)
    | Typing(ptm,pty) -> term_of_preterm1 ptm in
  fun ptm -> term_of_preterm1 ptm;;

let term_of_hol b =
  let error = mk_var("error",`:error`) in
  let term_of_hol1 env toks =
    let env' = ("thesis",Ptycon("bool",[]))::
      (map ((fun (s,ty) -> s,pretype_of_type ty) o dest_var) env) in
    try
      let ptm,l = (parse_preterm o map middle) toks in
      if l <> [] then (8,error) else
      try
        let tm = (term_of_preterm1 o retypecheck env') ptm in
        if not (subset
           (filter
             (fun v -> not (mem (fst (dest_var v)) ["..."; "thesis"]))
             (frees tm)) env)
          then (7,error) else
        if b && type_of tm <> bool_ty then (8,error) else
        (0,tm)
      with _ ->
        let tiw = !type_invention_warning in
        type_invention_warning := false;
        let tm =
          try (term_of_preterm o retypecheck env') ptm
          with e -> type_invention_warning := tiw; raise e in
        type_invention_warning := tiw;
        if not (subset (frees tm) env) then (7,error) else (6,error)
    with _ -> (8,error) in
  fun env toks ->
    match toks with
    | (x,Ident ".=",y)::rest ->
        term_of_hol1 env ((x,Ident "..."," ")::("",Ident "=",y)::rest)
    | _ -> term_of_hol1 env toks;;

let type_of_hol =
  let error = `:error` in
  fun toks ->
    try (0,(parse_type o middle o strings_of_toks) toks)
    with _ -> (8,error);;

let split_step toks =
  let cut_semi toks =
    match toks with
    | (_,Resword ";",_ as tok)::rst -> rev rst,[tok]
    | _ -> rev toks,[] in
  let rec cut_by_part rev_front toks =
    match toks with
    | [] | (_,Resword "by",_)::_ | (_,Resword "from",_)::_ -> rev_front,toks
    | tok::rst -> cut_by_part (tok::rev_front) rst in
  let rec group_by_items toks =
    match toks with
    | [] -> []
    | (_,Resword "by",_ as tok)::rst
    |   (_,Resword "from",_ as tok)::rst
    |   (_,Ident ",",_ as tok)::rst
    |   (_,Resword ";",_ as tok)::rst -> tok::group_by_items rst
    | (_,Ident "#",_ as tok)::toks' ->
        let toks1,toks2 =
          if toks' = [] then [],[]
            else cut_to false 0 [] ([","; ";"]@mizar_words) toks' in
        tok::(if toks1 = [] then [] else [tok_of_toks toks1])@
          group_by_items toks2
    | tok::rst ->
        let toks1,toks2 = cut_to false 0 [] ([","; ";"]@mizar_words) toks in
        if toks1 = [] then tok::group_by_items rst else
        (tok_of_toks toks1)::group_by_items toks2 in
  let rec cut_labs toks labs =
    match toks with
    | (_,Resword "]",_ as tok1)::(_,Ident _,_ as tok2)::
      (_,Resword "[",_ as tok3)::rst ->
        cut_labs rst (tok3::tok2::tok1::labs)
    | _ -> toks,labs in
  let rec cut_front toks tail =
    match toks with
    | [] -> [],tail
    | (_,Resword s,_)::rst when mem s mizar_words -> rev toks,tail
    | tok::rst -> cut_front rst (tok::tail) in
  let toks1,semi_part = cut_semi (rev toks) in
  let toks2,by_part = cut_by_part [] toks1 in
  let toks3,labs_part = cut_labs toks2 [] in
  let front_part,hol_part = cut_front toks3 [] in
  if front_part <> [] && middle (hd front_part) = Resword "exec" then
    let ml_tok = tok_of_toks ((tl front_part)@hol_part@labs_part@by_part) in
    [[hd front_part]; [ml_tok]; []; []; semi_part]
  else
    [front_part; hol_part; labs_part; group_by_items by_part; semi_part];;

let parse_step env toks =
  let src = split_step toks in
  try
    match src with
    | [front_part; hol_part; labs_part; by_part; semi_part] ->
        let labs = parse_labels labs_part in
        let just,_ = parse_by (by_part@semi_part) in
       (match front_part with
        | [] ->
           (match toks with
            | [_,Resword ";",_] ->
                -1,src,Empty_step
            | _ ->
                let n,t = term_of_hol true env hol_part in
                if n <> 0 then n,src,Error(string_of_toks toks,just) else
                -1,src,Have(t,labs,just))
        | (_,Resword key,_)::_ ->
           (match key,(tl front_part),(string_of_toks semi_part) with
            | "now",[],"" ->
                if hol_part <> [] || by_part <> [] then raise Noparse else
                -1,src,Now(labs,Proof_expected false)
            | "let",rst,";" ->
                if labs_part <> [] || by_part <> [] then raise Noparse else
                let x = (fst o fst o fst o
                  many ident' ++ a' "be" ++ finished) rst in
                let n,t = type_of_hol hol_part in
                if n <> 0 then n,src,Error(string_of_toks toks,No_steps) else
                -1,src,Let(map (fun s -> mk_var(s,t)) x)
            | "assume",[],";" ->
                if by_part <> [] then raise Noparse else
                let n,t = term_of_hol true env hol_part in
                if n <> 0 then n,src,Error(string_of_toks toks,No_steps) else
                -1,src,Assume(t,labs)
            | "thus",[],_ ->
                let n,t = term_of_hol true env hol_part in
                if n <> 0 then n,src,Error(string_of_toks toks,just) else
                -1,src,Thus(t,labs,just)
            | "qed",[],_ ->
                if hol_part <> [] || labs_part <> [] then raise Noparse else
                -1,src,Qed just
            | "proof",[],"" ->
                if hol_part <> [] || labs_part <> [] || by_part <> [] then
                  raise Noparse else
                -1,src,Bracket_proof
            | "end",[],";" ->
                if hol_part <> [] || labs_part <> [] || by_part <> [] then
                  raise Noparse else
                -1,src,Bracket_end
            | "take",[],";" ->
                if labs_part <> [] || by_part <> [] then raise Noparse else
                let n,t = term_of_hol false env hol_part in
                if n <> 0 then n,src,Error(string_of_toks toks,No_steps) else
                -1,src,Take t
            | "consider",rst,_ ->
                let cut_suchthat toks =
                  match toks with
                  | (_,Resword "that",_)::(_,Resword "such",_)::rst -> rst
                  | _ -> raise Not_found in
                let rec cut_being toks tail =
                  match toks with
                  | [] -> raise Not_found
                  | (_,Resword "being",_)::rst -> (rev rst),(rev tail)
                  | tok::rst -> cut_being rst (tok::tail) in
               (try
                  let rst1,rst2 = cut_being (cut_suchthat (rev rst)) [] in
                  let n,t = type_of_hol rst2 in
                  if n <> 0 then n,src,Error(string_of_toks toks,just) else
                  let x = (fst o fst o many ident' ++ finished) rst1 in
                  let vars = map (fun s -> mk_var(s,t)) x in
                  let n,tm' = term_of_hol true (vars@env) hol_part in
                  if n <> 0 then n,src,Error(string_of_toks toks,just) else
                  -1,src,Consider(vars,tm',labs,just)
                with Not_found ->
                  let x = (fst o fst o fst o fst o
                    many ident' ++ a' "such" ++ a' "that" ++ finished) rst in
                  let xy = (("",Ident "?","")::((flat (map unident' x))@
                    (("",Resword ".","")::hol_part))) in
                  let n,tm = term_of_hol true env xy in
                  if n <> 0 then n,src,Error(string_of_toks toks,just) else
                  let vars,tm' = nsplit dest_exists x tm in
                  -1,src,Consider(vars,tm',labs,just))
            | "set",[],";" ->
                if by_part <> [] then raise Noparse else
                let (w,_),rst = (ident' ++ a' "=") hol_part in
                let n,t = term_of_hol false env rst in
                if n <> 0 then n,src,Error(string_of_toks toks,No_steps) else
                -1,src,Set(mk_eq(mk_var(w,type_of t),t),labs)
            | "cases",[],_ ->
                if hol_part <> [] || labs_part <> [] then raise Noparse else
                -1,src,Cases(just,[])
            | "case",[],";" ->
                if hol_part <> [] || labs_part <> [] || by_part <> [] then
                  raise Noparse else
                -1,src,Bracket_case
            | "suppose",[],";" ->
                if by_part <> [] then raise Noparse else
                let n,t = term_of_hol true env hol_part in
                if n <> 0 then
                  n,src,Error(string_of_toks toks,Proof_expected false) else
                -1,src,Suppose(t,labs)
            | "exec",[],";" ->
                let s = string_of_toks hol_part in
                -1,src,Exec(s,exec_tactic s)
            | _ -> raise Noparse)
        | _ -> raise Noparse)
    | _ -> raise Noparse
  with
  | Failure "by_item_of_toks" -> 5,src,Error(string_of_toks toks,No_steps)
  | _ -> 9,src,Error(string_of_toks toks,No_steps);;

let rec steps_of_toks1 q e env toks =
  let prefix x (y,w,z) = (x@y),w,z in
  if toks = [] then
    if e then [9,[],Error_point],None,[] else [],None,[]
  else
    let stoks,rst = cut_step toks in
    let (status,src,substep as step) = parse_step env stoks in
    match substep with
    | Have (tm, labs, Proof_expected _) ->
        let just,rst1 = just_of_toks env rst in
        let step,rst2 =
         (match just with
          | Proof(_, _, _) -> (status,src,Have (tm, labs, just)),rst1
          | _ -> (9,src,Error(string_of_toks stoks, No_steps)),rst) in
        prefix [step] (steps_of_toks1 q e env rst2)
    | Thus (tm, labs, Proof_expected _) ->
        let just,rst1 = just_of_toks env rst in
        let step,rst2 =
         (match just with
          | Proof(_, _, _) -> (status,src,Thus (tm, labs, just)),rst1
          | _ -> (9,src,Error(string_of_toks stoks, No_steps)),rst) in
        prefix [step] (steps_of_toks1 q e env rst2)
    | Let vars -> prefix [step] (steps_of_toks1 q e ((rev vars)@env) rst)
    | Now (labs, Proof_expected _) ->
        let just,rst1 = now_of_toks env rst in
        prefix [status,src,Now (labs, just)] (steps_of_toks1 q e env rst1)
    | Consider (vars, _, _, By _) ->
        prefix [step] (steps_of_toks1 q e ((rev vars)@env) rst)
    | Consider (vars, tm, labs, Proof_expected _) ->
        let just,rst1 = just_of_toks env rst in
        let step,rst2 =
         (match just with
          | Proof(_, _, _) -> (status,src,Consider(vars, tm, labs, just)),rst1
          | _ -> (9,src,Error(string_of_toks stoks, No_steps)),rst) in
        prefix [step] (steps_of_toks1 q e ((rev vars)@env) rst2)
    | Set (tm, _) ->
        prefix [step] (steps_of_toks1 q e ((fst (dest_eq tm))::env) rst)
    | Cases ((By _ as just), []) ->
       (try
          let justs,rst1 = many (case_of_toks env q) rst in
          let final,step1,rst2 = steps_of_toks1 false e env rst1 in
          let cases = status,src,Cases(just, justs) in
          if final <> [] then
            prefix [cases; 9,[],Error_point]
              (steps_of_toks1 q e env rst1)
          else [cases],step1,rst2
        with Noparse ->
          prefix [9,src,Error(string_of_toks stoks, No_steps)]
            (steps_of_toks1 q e env rst))
    | Qed just ->
        if q then [step],None,rst else
        prefix [(if e then 3 else 9),src,Error(string_of_toks stoks, No_steps)]
          (steps_of_toks1 q e env rst)
    | Bracket_end ->
        if e then [],Some step,rst else
        prefix [9,src,Error(string_of_toks stoks, No_steps)]
          (steps_of_toks1 q e env rst)
    | Bracket_proof | Cases (_, _) | Bracket_case | Suppose (_, _) ->
        prefix [9,src,Error(string_of_toks stoks, No_steps)]
          (steps_of_toks1 q e env rst)
    | Error (s, Proof_expected true) ->
        let just,rst1 = just_of_toks env rst in
       (match just with
        | Proof(_, _, _) ->
            prefix [status,src,Error(s, just)] (steps_of_toks1 q e env rst1)
        | _ ->
            prefix [status,src,Error(string_of_toks stoks, No_steps)]
              (steps_of_toks1 q e env rst))
    | Error (s, Proof_expected false) ->
        let steps,step1,rst1 = steps_of_toks1 true true env rst in
        prefix [status,src,Error(s, Proof(None,steps,step1))]
          (steps_of_toks1 q e env rst)
    | Error (_, By _) ->
        prefix [status,src,Error(string_of_toks stoks, No_steps)]
          (steps_of_toks1 q e env rst)
    | _ -> prefix [step] (steps_of_toks1 q e env rst)

and just_of_toks env toks =
  try
    let stoks,rst = cut_step toks in
    let (_,_,substep as step) = parse_step env stoks in
    if substep = Bracket_proof then
      let steps,step1,rst1 = steps_of_toks1 true true env rst in
      (Proof(Some step,steps,step1)),rst1
    else (No_steps),toks
  with Noparse -> (No_steps),toks

and now_of_toks env toks =
  let steps,step1,rst = steps_of_toks1 false true env toks in
  (Proof(None,steps,step1)),rst

and case_of_toks env q toks =
  let stoks,rst = cut_step toks in
  let (_,_,substep as step) = parse_step env stoks in
  match substep with
  | Bracket_case ->
      let steps,step1,rst1 = steps_of_toks1 q true env rst in
      (Proof(Some step,steps,step1)),rst1
  | Suppose (_, _) ->
      let steps,step1,rst1 = steps_of_toks1 q true env rst in
      (Proof(None,step::steps,step1)),rst1
  | _ -> raise Noparse;;

let steps_of_toks toks =
  let proof,_,rst = steps_of_toks1 false false [] toks in
  if rst = [] then proof else
    proof@[9,[rst],Error (string_of_toks rst, No_steps)];;

let fix_semi toks =
  if toks = [] then toks else
  match last toks with
  | _,Resword ";",_ -> toks
  | _ -> toks@["\n",Resword ";",""];;

let parse_proof = steps_of_toks o fix_semi o lex2;;

exception Timeout;;

Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout));;

let TIMED_TAC n tac g =
  let _ = Unix.alarm n in
  try
    let gs = tac g in
    let _ = Unix.alarm 0 in
    gs
  with x ->
    let _ = Unix.alarm 0 in
    raise x;;

let FAKE_TAC : bool -> thm list -> tactic =
  fun fake thl (asl,w as g) ->
    if fake then
      let tm' = itlist (curry mk_imp) (map concl thl) w in
      let vl = frees tm' in
      let tm = itlist (curry mk_forall) vl tm' in
      let th = itlist (C MP) (rev thl) (itlist SPEC (rev vl) (ASSUME tm)) in
      null_meta,[],(fun i _ -> INSTANTIATE_ALL i th)
    else NO_TAC g;;

let MIZAR_NEXT : (goal -> step * goalstate) -> (goal -> step * goalstate) =
  let t = `T` in
  fun tac (asl,_ as g) ->
    let e,((mvs,insts),gls,just as gs) = tac g in
    match gls with
    | [] -> e,((mvs,insts),[asl,t],(fun _ _ -> just null_inst []))
    | [gl] -> e,gs
    | _ -> failwith "MIZAR_NEXT";;

let MIZAR_NEXT' : tactic -> tactic =
  let t = `T` in
  fun tac (asl,_ as g) ->
    let ((mvs,insts),gls,just as gs) = tac g in
    match gls with
    | [] ->
        ((mvs,insts),[asl,t],(fun _ _ -> just null_inst []))
    | [gl] -> gs
    | _ -> failwith "MIZAR_NEXT'";;

let fix_dots prevs tm =
  try
    let lhs,_ = dest_eq (hd prevs) in
    vsubst [lhs, mk_var("...",type_of lhs)] tm
  with _ -> tm;;

let fix_dots' asl tm =
  try
    let th = snd (hd asl) in
    let lhs,_ = dest_eq (concl th) in
    let dots = mk_var("...",type_of lhs) in
    let rec fix_dots1 tm =
     (match tm with
      | Var _ when tm = dots -> th
      | Comb(t1,t2) -> MK_COMB(fix_dots1 t1,fix_dots1 t2)
      | Abs(x,t) -> ABS x (fix_dots1 t)
      | _ -> REFL tm) in
    if vfree_in dots tm then fix_dots1 tm else REFL tm
  with _ -> REFL tm;;

let rec terms_of_step prevs (_,_,substep) =
  match substep with
  | Have (tm, _, _) -> [fix_dots prevs tm]
  | Now (_, just) -> [term_of_now just]
  | Assume (tm, _) -> [fix_dots prevs tm]
  | Thus (tm, _, _) -> [fix_dots prevs tm]
  | Consider (_, tm, _, _) -> [fix_dots prevs tm]
  | Set (tm, _) -> [fix_dots prevs tm]
  | Suppose (tm, _) -> [fix_dots prevs tm]
  | _ -> []

and term_of_now =
  let t = `T` in
  let rec term_of_steps prevs steps =
    match steps with
    | [] -> t
    | (_,_,substep as step)::rst ->
        let tm' = term_of_steps ((terms_of_step prevs step)@prevs) rst in
       (match substep with
        | Let vars -> list_mk_forall(vars,tm')
        | Assume (tm, _) -> mk_imp(fix_dots prevs tm,tm')
        | Thus (tm, _, _) -> mk_conj(fix_dots prevs tm,tm')
        | Take tm ->
            let var = genvar (type_of tm) in mk_exists(var,subst [var,tm] tm')
        | Consider (vars, _, _, _) ->
            if intersect (frees tm') vars <> [] then failwith "term_of_now"
            else tm'
        | Cases (_, _) -> failwith "term_of_now"
        | _ -> tm') in
  fun just ->
    match just with
    | Proof(_, steps, _) ->
        (rand o concl o PURE_REWRITE_CONV[AND_CLAUSES])
          (term_of_steps [] steps)
    | _ -> failwith "term_of_now";;

let terms_of_cases =
  let f = `F` in
  let rec terms_of_cases cases =
    match cases with
    | [] -> [],f
    | case::rst ->
      let l',tm' = terms_of_cases rst in
     (match case with
      | (_,_,Suppose (tm, _))::_ -> (()::l'),mk_disj(tm,tm')
      | _ -> failwith "terms_of_cases") in
  terms_of_cases o (map
    (fun just ->
       match just with
       | Proof(_, case, _) -> case
       | _ -> failwith "terms_of_cases"));;

let print_to_string1 printer =
  let sbuff = ref "" in
  let output s m n = sbuff := (!sbuff)^(String.sub s m n) and flush() = () in
  let fmt = make_formatter output flush in
  ignore(pp_set_max_boxes fmt 100);
  fun prefix' n i ->
    let prefix = prefix'^(implode (replicate " " n)) in
    let m = String.length prefix in
    pp_set_margin fmt ((!proof_width) - m);
    ignore(printer fmt i);
    ignore(pp_print_flush fmt ());
    let s = !sbuff in sbuff := "";
    implode (map (fun x -> if x = "\n" then "\n"^prefix else x) (explode s));;

let string_of_term1 = print_to_string1 pp_print_term;;
let string_of_type1 = print_to_string1 pp_print_type;;

let string_of_substep prefix substep =
  let string_of_vars tl = implode (map (fun v -> " "^fst (dest_var v)) tl) in
  let string_of_labs l = implode (map (fun s -> " ["^s^"]") l) in
  let rec string_of_by_items x l =
    match l with
    | [] -> ""
    | i::l' -> x^(match i with
        | Label s | Thm(s,_) | Tactic(s,_) | Grow(s,_) -> s
        | Hole -> "#")^string_of_by_items "," l' in
  let string_of_just just =
    match just with
    | By(l,l',_) ->
        (if l = [] then "" else " by"^string_of_by_items " " l)^
        (if l' = [] then "" else " from"^string_of_by_items " " l')^";"
    | _ -> "" in
  prefix^
 (match substep with
  | Have(tm,l,just) ->
      string_of_term1 prefix
        (if !indent_continued then String.length !proof_indent else 0) tm^
      string_of_labs l^string_of_just just
  | Now(l,just) -> "now"^string_of_labs l
  | Let(tl) ->
      let s = "let"^string_of_vars tl^" be " in
      s^string_of_type1 prefix (String.length s) (type_of (hd tl))^";"
  | Assume(tm,l) ->
      let s = "assume " in
      s^string_of_term1 prefix (String.length s) tm^string_of_labs l^";"
  | Thus(tm,l,just) ->
      let s = "thus " in
      s^string_of_term1 prefix (String.length s) tm^string_of_labs l^
      string_of_just just
  | Qed(just) -> "qed"^string_of_just just
  | Bracket_proof -> "proof"
  | Bracket_end -> "end;"
  | Take(tm) ->
      let s = "take " in
      s^string_of_term1 prefix (String.length s) tm^";"
  | Consider(tl,tm,l,just) ->
      let s = "consider"^string_of_vars tl^" such that " in
      s^string_of_term1 prefix (String.length s) tm^
      string_of_labs l^string_of_just just
  | Set(tm,l) ->
      let s = "set " in
      s^string_of_term1 prefix (String.length s) tm^string_of_labs l^";"
  | Cases(just,_) -> "cases"^string_of_just just
  | Bracket_case -> "case;"
  | Suppose(tm,l) ->
      let s = "suppose " in
      s^string_of_term1 prefix (String.length s) tm^string_of_labs l^";"
  | Exec(s,_) -> "exec "^s^";"
  | Error(s,_) -> s
  | Empty_step -> ""
  | Error_point -> "")^
  "\n";;

let step_of_substep prefix substep =
  (-1,split_step (lex2 (string_of_substep prefix substep)),substep :step);;

let step_of_obligation prefix lab tl ass tm =
  let hole = By([Hole],[],false) in
  let prefix' = prefix^ !proof_indent in
  let rec lets l =
    match l with
    | [] -> []
    | t::_ -> let l',l'' = partition ((=) (type_of t) o type_of) l in
        step_of_substep prefix' (Let l')::lets l'' in
  step_of_substep prefix
    (if tl = [] && ass = [] then Have(tm,[lab],hole) else
    let ll = lets tl in
    let intros = ll@(map (fun a ->
         step_of_substep prefix' (Assume(a,[]))) ass) in
      if !grow_haves then
        Have(list_mk_forall(flat
            (map (function (_,_,Let l) -> l | _ -> []) ll),
          itlist (curry mk_imp) ass tm), [lab],
        Proof (Some (step_of_substep prefix Bracket_proof),
          intros@
        [step_of_substep prefix (Qed(hole))], None))
      else
        Now([lab], Proof (None,
          intros@
          [step_of_substep prefix' (Thus(tm,[],hole))],
        Some (step_of_substep prefix Bracket_end))));;

let steps_of_goals (asl,w :goal) (_,gl,_ :goalstate) prefix n =
  let ass = map (concl o snd) asl in
  let fv = union (flat (map frees ass)) (frees w) in
  let rec extra_ass l l' =
    if subset l ass then l' else extra_ass (tl l) ((hd l)::l') in
  let rec steps_of_goals1 n gl =
    match gl with
    | [] -> [],[],n
    | (asl',w')::gl' ->
        let ass' = map (concl o snd) asl' in
        let steps',labs',n' = steps_of_goals1 (n + 1) gl' in
        let lab = string_of_int n in
        ((step_of_obligation prefix lab
          (subtract (union (flat (map frees ass')) (frees w')) fv)
          (extra_ass ass' []) w')::steps'),lab::labs',n' in
  steps_of_goals1 n gl;;

let next_growth_label = ref 0;;

let connect_step (step:step) labs =
  let comma = "",Ident ",","" in
  let from_key = " ",Resword "from"," " in
  let rec ungrow_by src l =
    match l with
    | [] -> src,[]
    | Grow(name,tac)::l' ->
       (match src with
        | tok1::(_,Ident "#",_)::tok2::src' ->
            let src'',l'' = ungrow_by src' l' in
            (tok1::tok2::src''),(Tactic(name,tac)::l')
        | _ -> failwith "ungrow_by")
    | x::l' -> let toks,src' = chop_list 2 src in
        let src'',l'' = ungrow_by src' l' in
        (toks@src''),(x::l'') in
  let rec extra_from sep labs =
    match labs with
    | [] -> []
    | lab::labs' -> sep::("",Ident lab,"")::extra_from comma labs' in
  let connect_just src4 just =
    match just with
    | By(l,l',b) ->
        let src4',l'' = ungrow_by src4 l in
        let src4'',l''' = ungrow_by src4' l' in
        (src4''@if labs = [] then [] else
          extra_from (if l' = [] then from_key else comma) labs),
        By(l'',(l'''@map (fun s -> Label s) labs),b)
    | _ -> src4,just in
  match step with
  | (e,[src1; src2; src3; src4; src5],substep) ->
     (match substep with
      | Have(x,y,just) ->
          let src4',just' = connect_just src4 just in
          (e,[src1; src2; src3; src4'; src5],Have(x,y,just'))
      | Thus(x,y,just) ->
          let src4',just' = connect_just src4 just in
          (e,[src1; src2; src3; src4'; src5],Thus(x,y,just'))
      | Qed just ->
          let src4',just' = connect_just src4 just in
          (e,[src1; src2; src3; src4'; src5],Qed just')
      | Consider(x,y,z,just) ->
          let src4',just' = connect_just src4 just in
          (e,[src1; src2; src3; src4'; src5],Consider(x,y,z,just'))
      | Cases(just,x) ->
          let src4',just' = connect_just src4 just in
          (e,[src1; src2; src3; src4'; src5],Cases(just',x))
      | _ -> failwith "connect_step" :step)
  | _ -> failwith "connect_step";;

let add_width n s =
  let rec add_width1 n s =
    match s with
    | [] -> n
    | "\t"::s' -> add_width1 ((n/8 + 1)*8) s'
    | "\n"::s' -> add_width1 0 s'
    | _::s' -> add_width1 (n + 1) s' in
  add_width1 n (explode s);;

let rewrap_step (e,src,substep as step:step) =
  let rec rewrap_from x1 src4a src4b =
    match src4b with
    | [] -> rev src4a
    | (x,y,z)::(x',(Resword "from" as y'),z')::rst ->
        (rev src4a)@(x,y,"\n")::(x1,y',z')::rst
    | tok::rst -> rewrap_from x1 (tok::src4a) rst in
  match src with
  | [src1; src2; src3; src4; src5] ->
      if src4 = [] then step else
      let src123 = src1@src2@src3 in
      let x,y,z = strings_of_toks src123 in
      let x',y',_ = strings_of_toks src4 in
      if add_width 0 (x^y^z^x'^y') > !proof_width then
        let a,b,_ = last src123 in
        let src123' = (butlast src123)@[a,b,"\n"] in
        let src1',src23' = chop_list (length src1) src123' in
        let src2',src3' = chop_list (length src2) src23' in
        let _,b',c' = hd src4 in
        let x1 = x^ !proof_indent in
        let src4' = (x1,b',c')::tl src4 in
        let src4'' =
          if add_width 0 (x1^y') > !proof_width then
            rewrap_from x1 [] src4' else src4' in
        (e,[src1'; src2'; src3'; src4''; src5],substep)
      else (step:step)
  | _ -> failwith "rewrap_step";;

let rec pp_step prefix step =
  let (e,_,substep) = step in
  let (_,src,substep') =
    rewrap_step (step_of_substep prefix substep) in
  let substep'' =
   (match substep' with
    | Have(x,y,just) -> Have(x,y,pp_just prefix just)
    | Now(x,just) -> Now(x,pp_just prefix just)
    | Thus(x,y,just) -> Thus(x,y,pp_just prefix just)
    | Qed(just) -> Qed(pp_just prefix just)
    | Consider(x,y,z,just) -> Consider(x,y,z,pp_just prefix just)
    | Cases(just,justl) ->
        Cases(pp_just prefix just,map (pp_just prefix) justl)
    | Error(x,just) -> Error(x,pp_just prefix just)
    | _ -> substep') in
  (e,src,substep'')
and pp_just prefix just =
  let pp_step' step' =
    match step' with
    | Some step -> Some (pp_step prefix step)
    | None -> None in
  let prefix' = (!proof_indent)^prefix in
  let pp_step'' step =
    match step with
    | (_,_,Qed _) -> pp_step prefix step
    | (_,_,Suppose _) -> pp_step prefix step
    | _ -> pp_step prefix' step in
  match just with
  | Proof(step',stepl,step'') ->
      Proof(pp_step' step',map (pp_step'') stepl,pp_step' step'')
  | _ -> just;;

let outdent n step =
  let (_,src,_) = step in
  match flat src with
  | (x,_,_)::_ ->
      let x' = explode x in
      if length x' < n then step else
      let _,x'' = chop_list n x' in
      pp_step (implode x'') step
  | _ -> step;;

let replacement_steps (asl,w) f step =
  let n = String.length !proof_indent in
  let indent_of (_,src,substep) =
    let x,_,_ = hd (flat src) in
    match substep with
    | Qed _ -> x^ !proof_indent
    | _ -> x in
  let shift src2 src3 just =
    match just with
    | Proof _ ->
        if src3 <> [] then
          let (x,y,z) = last src3 in
          src2,((butlast src3)@[x,y,"\n"])
        else if src2 <> [] then
          let (x,y,z) = last src2 in
          ((butlast src2)@[x,y,"\n"]),src3
        else src2,src3
    | _ -> src2,src3 in
  let steps,labs,n = f (indent_of step) (!next_growth_label) in
  next_growth_label := n;
  if !grow_duplicates > 1 then
    steps@[rewrap_step (connect_step step labs)]
  else
  match steps,step with
  | [e,[src1'; src2'; src3'; src4'; src5'],Have(tm',_,just')],
    (_,[src1; src2; src3; src4; src5],Have(tm,labs,_)) when tm' = tm ->
      let src2'',src3'' = shift src2 src3 just' in
      [e,[src1; src2''; src3''; src4'; src5'],Have(tm,labs,just')]
  | [e,[src1'; src2'; src3'; src4'; src5'],Have(tm',_,just')],
    (_,[src1; src2; src3; src4; src5],Thus(tm,labs,_)) when tm' = tm ->
      let src2'',src3'' = shift src2 src3 just' in
      [e,[src1; src2''; src3''; src4'; src5'],Thus(tm,labs,just')]
  | [e,_,Have(tm',_,Proof(_,y,_))],
    (_,_,Qed(_)) when tm' = w ->
      map (outdent n) y
  | [e,[src1'; src2'; src3'; src4'; src5'],Have(tm',_,(By _ as just'))],
    (_,[src1; src2; src3; src4; src5],Qed(_)) when tm' = w ->
      [e,[src1; src2; src3; src4'; src5'],Qed(just')]
  | _ ->
  if !grow_duplicates > 0 then
    steps@[rewrap_step (connect_step step labs)]
  else
    let al = map (fun x,y -> concl y,x) asl in
    let rec filter_growth steps labs steps' labs' =
      match steps with
      | [] -> (rev steps'),(rev labs')
      | ((_,_,Have(tm,_,_)) as step')::rst ->
         (try let lab' = assoc tm al in
            if lab' <> "" then
              filter_growth rst (tl labs) steps' (lab'::labs')
            else
              filter_growth rst (tl labs) (step'::steps') ((hd labs)::labs')
          with _ ->
            filter_growth rst (tl labs) (step'::steps') ((hd labs)::labs'))
      | step'::rst ->
          filter_growth rst (tl labs) (step'::steps') ((hd labs)::labs') in
    let steps',labs' = filter_growth steps labs [] [] in
    steps'@[rewrap_step (connect_step step labs')];;

exception Grown of (string -> int -> step list * string list * int);;

let (FILTER_ASSUMS : (int * (string * thm) -> bool) -> tactic) =
  let rec filter' f n l =
    match l with
    | [] -> []
    | h::t ->
        let t' = filter' f (n + 1) t in
        if f (n,h) then h::t' else t' in
  fun f (asl,w) ->
    null_meta,[filter' f 0 asl,w],(fun i ths -> hd ths);;

let (MAP_ASSUMS : (string * thm -> string * thm) -> tactic) =
  let FIRST_ASSUM' ttac' (asl,w as g) =
    tryfind (fun lth -> ttac' lth g) asl in
  fun f ->
    let rec recurse g =
     (FIRST_ASSUM' (fun (l,th as lth) ->
       UNDISCH_THEN (concl th) (fun th ->
         recurse THEN uncurry LABEL_TAC (f lth))) ORELSE ALL_TAC) g in
    recurse ORELSE FAIL_TAC "MAP_ASSUMS";;

let (thenl':
    tactic -> (goal -> 'a * goalstate) list -> goal -> 'a list * goalstate) =
  let propagate_empty i _ = [] in
  let propagate_thm th i _ = INSTANTIATE_ALL i th in
  let compose_justs n just1 just2 i ths =
    let ths1,ths2 = chop_list n ths in
    (just1 i ths1)::(just2 i ths2) in
  let rec seqapply l1 l2 =
    match (l1,l2) with
    | ([],[]) -> [],(null_meta,[],propagate_empty)
    | (tac::tacs),(goal::goals) ->
            let a,((mvs1,insts1),gls1,just1) = tac goal in
            let goals' = map (inst_goal insts1) goals in
            let aa',((mvs2,insts2),gls2,just2) = seqapply tacs goals' in
            (a::aa'),((union mvs1 mvs2,compose_insts insts1 insts2),
              gls1@gls2,compose_justs (length gls1) just1 just2)
    | _,_ -> failwith "seqapply: Length mismatch" in
  let justsequence just1 just2 insts2 i ths =
    just1 (compose_insts insts2 i) (just2 i ths) in
  let tacsequence ((mvs1,insts1),gls1,just1) tacl =
    let aa,((mvs2,insts2),gls2,just2) = seqapply tacl gls1 in
    let jst = justsequence just1 just2 insts2 in
    let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
    aa,((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
  fun tac1 tac2l g ->
    let _,gls,_ as gstate = tac1 g in
    if gls = [] then tacsequence gstate [] else tacsequence gstate tac2l;;

let just_cache = ref undefined;;

let tactic_of_by fake l l' b =
 (fun (asl,_ as g) ->
  let hor = if b then 0 else !horizon in
  let rec find_tactic l =
    match l with
    | [] -> !default_prover,false
    | (Tactic (name, tac))::l' -> (name,tac),false
    | (Grow (name, tac))::l' -> (name,tac),true
    | _::l' -> find_tactic l' in
  let sets = BETA_THM::map snd (filter (fun x,_ -> x = "=") asl) in
  let asl' = filter (fun x,_ -> x <> "=") asl in
  let rec find_thms l b =
    match l with
    | [] ->
        if b then [] else
        map (PURE_REWRITE_RULE sets o snd)
          (try fst (chop_list hor asl') with _ -> asl')
    | (Thm (_, th))::l' -> th::(find_thms l' b)
    | (Label "*")::l' ->
        (map (PURE_REWRITE_RULE sets o snd) asl')@(find_thms l' b)
    | (Label s)::l' ->
        (PURE_REWRITE_RULE sets
          (if s = "-" then snd (hd asl') else assoc s asl'))::(find_thms l' b)
    | _::l' -> find_thms l' b in
  let rec find_labs l =
    match l with
    | [] -> []
    | (Label s)::l' -> s::(find_labs l')
    | _::l' -> find_labs l' in
  try
    let thms = find_thms l b in
    let thms' = find_thms l' true in
    let thms'' = thms@thms' in
    let (name,tac),grow = find_tactic (l@l') in
    if fake && (mem Hole l || mem Hole l') || not (!growth_mode) && grow then
      -2,FAKE_TAC fake thms'' g else
    let labs = find_labs l in
    let full_asl = hor < 0 || mem "*" labs in
   (try
      0,((FILTER_ASSUMS (fun _,(x,_) -> x <> "=") THEN
        FILTER_ASSUMS
         (fun n,(x,_) ->
            mem x labs || n < hor || (n = 0 && mem "-" labs) || full_asl) THEN
        MAP_ASSUMS (fun l,th -> l,PURE_REWRITE_RULE sets th) THEN
        MIZAR_NEXT' (PURE_REWRITE_TAC sets) THEN
       (fun (asl',w' as g') ->
          let key = name,(map concl thms,map concl thms'),w' in
          try
            if grow then failwith "apply";
            let e,th = apply (!just_cache) key in
            if e = 0 then (ACCEPT_TAC th THEN NO_TAC) g' else
            if e = 2 then raise Timeout else failwith "cached by"
          with
          | Failure "apply" ->
              try
                let (_,_,just as gs) =
                 ((fun g'' ->
                    let gs' = TIMED_TAC (!timeout) (tac thms) g'' in
                    if grow then raise (Grown (steps_of_goals g gs'))
                            else gs') THEN
                  REPEAT (fun (asl'',_ as g'') ->
                    if subset asl'' asl' then NO_TAC g''
                    else FIRST_ASSUM (UNDISCH_TAC o concl) g'') THEN
                  TRY (FIRST (map ACCEPT_TAC thms'')) THEN
                  REWRITE_TAC thms'' THEN NO_TAC) g' in
                let th = just null_inst [] in
                just_cache := (key |-> (0,th)) !just_cache;
                gs
              with
              | Grown _ as x -> raise x
              | x -> if name <> "GOAL_TAC" then just_cache :=
                    (key |-> ((if x = Timeout then 2 else 1),TRUTH))
                      !just_cache;
                  raise x
        )) g)
    with
    | Grown _ as x -> raise x
    | x -> (if x = Timeout then 2 else 1),(FAKE_TAC fake thms'' g))
  with Failure "find" | Failure "hd" -> 4,(FAKE_TAC fake [] g)
  : goal -> int * goalstate);;

let LABELS_TAC ls th =
  if ls = [] then ASSUME_TAC th else
  EVERY (map (fun l -> LABEL_TAC l th) ls);;

let PURE_EXACTLY_ONCE_REWRITE_TAC =
  let ONCE_COMB_QCONV conv tm =
    let l,r = dest_comb tm in
    try let th1 = conv l in AP_THM th1 r
    with Failure _ -> AP_TERM l (conv r) in
  let ONCE_SUB_QCONV conv tm =
    if is_abs tm then ABS_CONV conv tm
    else ONCE_COMB_QCONV conv tm in
  let rec EXACTLY_ONCE_DEPTH_QCONV conv tm =
      (conv ORELSEC (ONCE_SUB_QCONV (EXACTLY_ONCE_DEPTH_QCONV conv))) tm in
  let PURE_EXACTLY_ONCE_REWRITE_CONV thl =
    GENERAL_REWRITE_CONV false EXACTLY_ONCE_DEPTH_QCONV empty_net thl in
  fun thl ->
    CONV_TAC(PURE_EXACTLY_ONCE_REWRITE_CONV thl);;

let EQTF_INTRO =
  let lemma = TAUT `(~t <=> T) <=> (t <=> F)` in
  fun th ->
    PURE_ONCE_REWRITE_RULE[lemma] (EQT_INTRO th);;

let REWRITE_THESIS_TAC =
  let PROP_REWRITE_TAC =
    PURE_REWRITE_TAC[AND_CLAUSES; IMP_CLAUSES; NOT_CLAUSES; OR_CLAUSES;
      prop_2; TAUT `!t. (t <=> t) <=> T`] in
  fun th ->
    PURE_EXACTLY_ONCE_REWRITE_TAC[EQTF_INTRO th] THEN PROP_REWRITE_TAC;;

let thesis_var = `thesis:bool`;;

let rec tactic_of_step fake step (asl,w as g) =
  let justify tac just g =
    let (mvs,inst),gls,jst = tac g in
   (match gls with
    | [g1; g2] ->
        let (e,just'),((mvs',inst'),gls',jst') =
          tactic_of_just fake just g1 in
        let mvs'' = union mvs' mvs in
        let inst'' = compose_insts inst' inst in
        let gls'' = gls'@[g2] in
        let jst'' i ths =
          jst (compose_insts inst'' i) [jst' i (butlast ths); last ths] in
        (e,just'),((mvs'',inst''),gls'',jst'')
    | _ -> failwith "justify") in
  let SUBGOAL_THEN' tm tac =
    let th = fix_dots' asl tm in
    let lhs,_ = dest_eq (concl th) in
    SUBGOAL_THEN lhs tac THENL [MIZAR_NEXT' (CONV_TAC (K th)); ALL_TAC] in
  let fix_thesis tm = vsubst [w,thesis_var] tm in
  let e,src,substep = step in
    match substep with
    | Let tl ->
       (try (0,src,substep),(MAP_EVERY X_GEN_TAC tl g)
        with x -> if fake then (3,src,substep),(ALL_TAC g) else raise x)
    | Assume (tm, l) | Suppose (tm, l) ->
       (try (0,src,substep),(DISJ_CASES_THEN2
         (fun th -> MIZAR_NEXT' (REWRITE_THESIS_TAC th) THEN
            LABELS_TAC l th)
         (fun th ->
            let th' = PURE_REWRITE_RULE[NOT_CLAUSES; IMP_CLAUSES] th in
            REWRITE_TAC[th'] THEN CONTR_TAC th' THEN NO_TAC)
          (SPEC (fix_thesis tm) EXCLUDED_MIDDLE) g)
        with x -> if fake then (3,src,substep),(ALL_TAC g) else raise x)
    | Have (tm, l, just) ->
       (try let (e,just'),gs =
            justify (SUBGOAL_THEN' (fix_thesis tm) (LABELS_TAC l)) just g in
         (e,src,Have(tm, l, just')),gs
        with x -> raise x)
    | Now (l, just) ->
       (try let (e,just'),gs =
            justify (SUBGOAL_THEN (term_of_now just) (LABELS_TAC l)) just g in
         (e,src,Now(l, just')),gs
        with x -> raise x)
    | Thus (tm, l, just) ->
       (try let (e,just'),gs =
            justify (SUBGOAL_THEN' (fix_thesis tm) (LABELS_TAC l) THENL
              [ALL_TAC; MIZAR_NEXT'
                 (FIRST_ASSUM (fun th ->
                    EVERY (map (fun th' -> REWRITE_THESIS_TAC th')
                      (CONJUNCTS th))))])
              just g in
         (e,src,Thus(tm, l, just')),gs
        with x -> if fake then (3,src,substep),(ALL_TAC g) else raise x)
    | Qed just ->
       (try let (e,just'),gs = tactic_of_just fake just g in
         (e,src,substep),gs
        with x -> raise x)
    | Take tm ->
       (try (0,src,substep),(EXISTS_TAC tm g)
        with x -> if fake then (3,src,substep),(ALL_TAC g) else raise x)
    | Consider (tl, tm, l, just) ->
        let tm' = itlist (curry mk_exists) tl (fix_thesis tm) in
       (try let (e,just'),gs =
            justify (SUBGOAL_THEN tm'
            ((EVERY_TCL (map X_CHOOSE_THEN tl)) (LABELS_TAC l))) just g in
          (e,src,Consider(tl, tm, l, just')),gs
        with x -> if fake then (3,src,substep),(ALL_TAC g) else raise x)
    | Set (tm, l) ->
       (try
          let v,_ = dest_eq tm in
          let tm' = mk_exists(v,tm) in
          let l' = if l = [] then ["="] else l in
         (0,src,substep),
         ((SUBGOAL_THEN tm' (X_CHOOSE_THEN v (LABELS_TAC l')) THENL
           [REWRITE_TAC[EXISTS_REFL] ORELSE FAKE_TAC fake []; ALL_TAC]) g)
        with x -> raise x)
    | Cases (just, cases) ->
       (try
          let l,tm = terms_of_cases cases in
          let steps,gs =
           (thenl' (SUBGOAL_THEN tm
             (EVERY_TCL
               (map (K (DISJ_CASES_THEN2
                 (fun th -> ASSUME_TAC th THEN
                    FIRST_ASSUM (UNDISCH_TAC o concl)))) l) CONTR_TAC))
         ((tactic_of_just fake just)::
           (map (fun just -> tactic_of_just fake just) cases)) g) in
         (match steps with
          | (e,just')::ecases' -> (e,src,Cases(just',map snd ecases')),gs
          | _ -> failwith "tactic_of_step")
        with x -> raise x)
    | Bracket_proof | Bracket_end | Bracket_case ->
       (3,src,substep),(ALL_TAC g)
    | Exec(_,tac) ->
       (try (0,src,substep),(TIMED_TAC (!timeout) tac THENL [ALL_TAC]) g
        with
        | Timeout as x -> if fake then (2,src,substep),(ALL_TAC g) else raise x
        | x -> if fake then (3,src,substep),(ALL_TAC g) else raise x)
    | Error (_,_) | Error_point ->
        if fake then (e,src,substep),(ALL_TAC g) else failwith "tactic_of_step"
    | Empty_step ->
       (0,src,substep),(ALL_TAC g)

and tactic_of_just fake just g =
  let bracket_step step e =
    match step with
    | None -> if e = 0 then None else Some (e, [], Error_point)
    | Some (_, src, substep) -> Some (e, src, substep) in
  let rec tactic_of_just1 l (_,w as g) =
    match l with
    | [] ->
        if is_const w && fst (dest_const w) = "T"
          then [],0,ACCEPT_TAC TRUTH g
          else [],3,FAKE_TAC fake (map snd (fst g)) g
    | step::l' ->
       (try
          let step',((mvs,inst),gls,just) =
            MIZAR_NEXT (tactic_of_step fake step) g in
         (match gls with
          | [g'] ->
              let l'',e,((mvs',inst'),gls',just') = tactic_of_just1 l' g' in
              let mvs'' = union mvs' mvs in
              let inst'' = compose_insts inst' inst in
              let gls'' = gls' in
              let just'' i ths = just (compose_insts inst'' i) [just' i ths] in
              step'::l'',e,((mvs'',inst''),gls'',just'')
          | _ -> failwith "tactic_of_just")
        with Grown f ->
          tactic_of_just1 (replacement_steps g f step@l') g) in
  match just with
  | By(l,l',b) -> let e,gs = tactic_of_by fake l l' b g in (e,just),gs
  | Proof(step1, l, step2) ->
      let l',e,gs = tactic_of_just1 l g in
      (0,Proof(bracket_step step1 0, l', bracket_step step2 e)),gs
  | _ -> failwith "tactic_of_just";;

let parse_qproof s = steps_of_toks (fix_semi (tl (lex2 s)));;

let rec src_of_step (e,src,substep) =
  [e,strings_of_toks (flat src)]@
  match substep with
  | Have(_, _, just) -> src_of_just just
  | Now(_, just) -> src_of_just just
  | Thus(_, _, just) -> src_of_just just
  | Qed just -> src_of_just just
  | Consider(_, _, _, just) -> src_of_just just
  | Cases(just, cases) ->
      (src_of_just just)@(itlist (@) (map src_of_just cases) [])
  | Error(_, just) -> src_of_just just
  | _ -> []

and src_of_just just =
  let unpack step1 =
    match step1 with
    | Some step -> src_of_step step
    | _ -> [] in
  match just with
  | Proof(step1, steps, step2) ->
      (unpack step1)@(itlist (@) (map src_of_step steps) [])@(unpack step2)
  | _ -> [];;

let src_of_steps steps = itlist (@) (map src_of_step steps) [];;

let count_errors src =
  let rec count_errors1 src (n1,n2,n3) =
    match src with
    | [] -> n1,n2,n3
    | (e,_)::src' -> count_errors1 src'
       (if e > 2 then (n1 + 1,n2,n3) else
        if e > 0 then (n1,n2 + 1,n3) else
        if e = -2 then (n1,n2,n3 + 1) else
          (n1,n2,n3)) in
  count_errors1 src (0,0,0);;

let error_line l ee =
  let rec error_line1 s1 s2 n l ee =
    match l with
    | [] -> (s1^"\n"),s2,ee
    | (m,e)::l' ->
        let d = m - n - 1 in
        let d' = if d > 0 then d else 0 in
        let s' = "#"^string_of_int e in
        error_line1 (s1^(implode (replicate " " d'))^s')
         (if !explain_errors > 0 then
            if mem e ee then s2 else s2^":: "^(el (e - 1) ERRORS)^"\n"
          else s2)
         (add_width (n + d') s') l' (union ee [e]) in
  let s1,s2,ee' =
    error_line1 "::" "" 2 l (if !explain_errors > 1 then [] else ee) in
  (s1^s2),ee';;

let insert_errors n s l ee =
  let rec insert_errors1 n s l ee =
    match s with
    | [] -> [],n,l,ee
    | ("\n" as c)::s' ->
        let s1,ee' = if l = [] then "",ee else error_line l ee in
        let s2,n1,l1,ee' = insert_errors1 0 s' [] ee' in
        (c::s1::s2),n1,l1,ee'
    | c::s' ->
        let s1,n1,l1,ee' = insert_errors1 (add_width n c) s' l ee in
          (c::s1),n1,l1,ee' in
  let s1,n1,l1,ee' = insert_errors1 n (explode s) l ee in
  (implode s1),n1,l1,ee';;

let string_of_src m steps =
  let add_error l n e =
    if e > (if !sketch_mode then 2 else 0) then l@[n,e] else l in
  let rec string_of_src1 s n l s3' steps ee =
    match steps with
    | [] ->
        let s',n',l',ee' = insert_errors n s3' l ee in
        if l' = [] then s^s' else
          let s'',_,_,_ = insert_errors n' "\n" l' ee' in
          s^s'^s''
    | (e,(s1,"",s3))::steps' ->
        string_of_src1 s n (add_error l n e) (s3'^s1^s3) steps' ee
    | (e,(s1,s2,s3))::steps' ->
        let s',n',l',ee' = insert_errors n (s3'^s1) l ee in
        let n'' = add_width n' s2 in
        string_of_src1 (s^s'^s2) n'' (add_error l' n'' e) s3 steps' ee' in
  string_of_src1 "" m [] "" steps [];;

let print_boxed f s =
  let print_boxed_char c =
    if c = "\n"
      then Format.pp_print_cut f ()
      else Format.pp_print_string f c in
  Format.pp_open_vbox f 0;
  do_list print_boxed_char (explode s);
  Format.pp_close_box f ();;

let print_step f x =
  print_boxed f (string_of_src 0 (src_of_step x));;

let print_qsteps f x =
  print_boxed f ("`;\n"^(string_of_src 0 (src_of_steps x))^"`");;

#install_printer print_step;;
#install_printer print_qsteps;;

let GOAL_TAC g =
  current_goalstack := (mk_goalstate g)::!current_goalstack;
  ALL_TAC g;;

let GOAL_FROM x = fun y -> x y THEN GOAL_TAC;;

let ee s =
  let toks = lex2 s in
  let l,t = top_goal() in
  let env = itlist union (map frees l) (frees t) in
  let proof,step1,rst = steps_of_toks1 true false env toks in
  if rst <> [] || step1 <> None then failwith "ee" else
  (e o EVERY o map (fun step -> snd o tactic_of_step false step)) proof;;

let check_proof steps =
  let step =
    match steps with
    | [_,_,Have (_, _, _) as step] -> step
    | [_,_,Now (_, _) as step] -> step
    | _ ->
        -1,[],Now([], Proof(None,steps,
            Some(-1,[],Bracket_end))) in
  let step',gs = tactic_of_step true step ([],thesis_var) in
  let steps' =
    match step' with
    | _,[],Now(_, Proof(_,steps',_)) -> steps'
    | step' -> [step'] in
  let _,gl,j = gs in
  if length gl <> 1 then failwith "thm" else
  let (asl,w) = hd gl in
  if length asl <> 1 || w <> thesis_var then failwith "thm" else
  let a = (concl o snd o hd) asl in
  let src' = src_of_steps steps' in
  steps',count_errors src',j ([],[a,thesis_var],[]) [ASSUME a];;

exception Mizar_error of step list * (int * int * int);;

let thm steps =
  let steps',(n1,n2,n3 as n),th = check_proof steps in
  if n1 + n2 + n3 = 0 then th else raise (Mizar_error(steps',n));;

let thm_of_string = thm o parse_proof;;

let rec labels_of_steps labels context steps =
  match steps with
  | [] -> labels
  | (_,_,substep)::rst ->
     (match substep with
      | Assume(_,labs) | Suppose(_,labs) | Set(_,(_::_ as labs)) ->
          let label = (labs,ref 0) in
          labels_of_steps (label::labels) (label::context) rst
      | Have(_,labs,just) | Thus(_,labs,just) | Consider(_,_,labs,just)
      | Now(labs,just) ->
          let label = (labs,ref 0) in
          let labels1 = labels_of_just (label::labels) context just in
          labels_of_steps labels1 (label::context) rst
      | Qed(just) ->
          let labels1 = labels_of_just labels context just in
          labels_of_steps labels1 context rst
      | Cases(just,justl) ->
          itlist
            (fun just' labels' -> labels_of_just labels' context just')
            (rev justl) (labels_of_just labels context just)
      | Error(_,_) -> raise Noparse
      | _ -> labels_of_steps labels context rst)

and labels_of_just labels context just =
  let rec collect_strings l =
    match l with
    | [] -> []
    | Label(s)::l' -> s::collect_strings l'
    | _::l' -> collect_strings l' in
  match just with
  | Proof(_,steps,_) -> labels_of_steps labels context steps
  | By(x,y,_) ->
      do_list (fun s ->
          do_list (fun _,n -> n := !n + 1) (filter (mem s o fst) context))
        (subtract (collect_strings (x@y)) ["-"; "*"]);
      labels
  | _ -> labels;;

let isnumber = forall isnum o explode;;

let max_label labels = itlist max
  (map int_of_string (filter isnumber (flat (map fst labels)))) (-1);;

let rec number_labels n labels =
  match labels with
  | [] -> []
  | (oldlabs,count)::rst ->
      let newlabs,n' =
       (if !extra_labels > 1 || !count > 0 ||
          (!extra_labels > 0 && exists isnumber oldlabs)
        then [string_of_int n],(n + 1) else [],n) in
      (oldlabs,newlabs)::(number_labels n' rst);;

let rec renumber_steps labels context steps =
  let make_lab x1 y1 x2 y2 x3 y3 s =
    ([x1,Resword "[",y1; x2,Ident s,y2; x3,Resword "]",y3],[s]) in
  let rec renumber_labs b w src labs label =
    match labs with
    | [] ->
        if b then (make_lab "" "" "" "" "" w (hd (snd label)))," "
          else ([],[]),w
    | lab::rst when isnumber lab ->
       (match src with
        | (x1,Resword "[",y1)::(x2,Ident s',y2)::(x3,Resword "]",y3)::rstsrc ->
            let (src',labs'),w' = renumber_labs false y3 rstsrc rst label in
            let newsrc,newlabs =
              if b then make_lab x1 y1 x2 y2 x3 w' (hd (snd label))
              else [],[] in
            ((newsrc@src'),(newlabs@labs')),if b then w else y3
        | _ -> failwith "renumber_labs")
    | lab::rst ->
       (match src with
        | tok1::tok2::(x3,y3,z3)::rstsrc ->
            let (src',labs'),w' = renumber_labs b z3 rstsrc rst label in
            ((tok1::tok2::(x3,y3,w')::src'),(lab::labs')),w
        | _ -> failwith "renumber_labs") in
  let renumber_labs1 b src1 src labs label =
    let (x,y,w) = last src1 in
    let (src',labs'),w' = renumber_labs b w src labs label in
    let src1' = if w' <> w then (butlast src1)@[x,y,w'] else src1 in
    src1',src',labs' in
  match steps with
  | [] -> labels,[]
  | (e,src,substep)::rst ->
     (match src with
      | [src1; src2; src3; src4; src5] ->
         (match substep with
          | Assume(x,labs) ->
              let label = hd labels in
              let src2',src3',labs' =
                renumber_labs1 (snd label <> []) src2 src3 labs label in
              let labels',rst' =
                renumber_steps (tl labels) (label::context) rst in
              labels',
              (e,[src1; src2'; src3'; src4; src5],Assume(x,labs'))::rst'
          | Suppose(x,labs) ->
              let label = hd labels in
              let src2',src3',labs' =
                renumber_labs1 (snd label <> []) src2 src3 labs label in
              let labels',rst' =
                renumber_steps (tl labels) (label::context) rst in
              labels',
              (e,[src1; src2'; src3'; src4; src5],Suppose(x,labs'))::rst'
          | Set(x,(_::_ as labs)) ->
              let label = hd labels in
              let src2',src3',labs' =
                renumber_labs1 (snd label <> []) src2 src3 labs label in
              let labels',rst' =
                renumber_steps (tl labels) (label::context) rst in
              labels',
              (e,[src1; src2'; src3'; src4; src5],Set(x,labs'))::rst'
          | Have(x,labs,just) ->
              let label = hd labels in
              let src2',src3',labs' =
                renumber_labs1 (snd label <> []) src2 src3 labs label in
              let labels',src4',just' =
                renumber_just (tl labels) context src4 just in
              let labels'',rst' =
                renumber_steps labels' (label::context) rst in
              labels'',
                ((e,[src1; src2'; src3'; src4'; src5],Have(x,labs',just'))::
                 rst')
          | Thus(x,labs,just) ->
              let label = hd labels in
              let src2',src3',labs' =
                renumber_labs1 (snd label <> []) src2 src3 labs label in
              let labels',src4',just' =
                renumber_just (tl labels) context src4 just in
              let labels'',rst' =
                renumber_steps labels' (label::context) rst in
              labels'',
                ((e,[src1; src2'; src3'; src4'; src5],Thus(x,labs',just'))::
                 rst')
          | Qed(just) ->
              let labels',src4',just' =
                renumber_just labels context src4 just in
              let labels'',rst' =
                renumber_steps labels' context rst in
              labels'',
                ((e,[src1; src2; src3; src4'; src5],Qed(just'))::
                 rst')
          | Consider(x,y,labs,just) ->
              let label = hd labels in
              let src2',src3',labs' =
                renumber_labs1 (snd label <> []) src2 src3 labs label in
              let labels',src4',just' =
                renumber_just (tl labels) context src4 just in
              let labels'',rst' =
                renumber_steps labels' (label::context) rst in
              labels'',
                ((e,[src1; src2'; src3'; src4'; src5],
                  Consider(x,y,labs',just'))::
                 rst')
          | Now(labs,just) ->
              let label = hd labels in
              let src1',src3',labs' =
                renumber_labs1 (snd label <> []) src1 src3 labs label in
              let labels',src4',just' =
                renumber_just (tl labels) context src4 just in
              let labels'',rst' =
                renumber_steps labels' (label::context) rst in
              labels'',
                ((e,[src1'; src2; src3'; src4'; src5],Now(labs',just'))::
                 rst')
          | Cases(just,justl) ->
              let labels',src4',just' =
                renumber_just labels context src4 just in
              let labels'',justl'' =
                itlist
                  (fun just' (labels',justl') ->
                    let labels'',_,just'' =
                      renumber_just labels' context [] just' in
                    labels'',(just''::justl'))
                  (rev justl) (labels',[]) in
              let labels''',rst' =
                renumber_steps labels'' context rst in
              labels''',
                ((e,[src1; src2; src3; src4'; src5],Cases(just',rev justl''))::
                 rst')
          | Error(_,_) -> raise Noparse
          | _ ->
              let labels',rst' = renumber_steps labels context rst in
              labels',((e,src,substep)::rst'))
      | _ -> failwith "renumber_steps")

and renumber_just labels context src just =
  let rec renumber_by src l =
    match l with
    | [] -> [],src,[]
    | (Label s as x)::l' when isnumber s ->
       (match src with
        | tok::(x1,Ident _,x2 as tok')::src23 ->
            let labs = flat (map snd (filter (mem s o fst) context)) in
            let src2,src3,l'' = renumber_by src23 l' in
            if labs = [] then (tok::tok'::src2),src3,(x::l'') else
            let items = map (fun s -> Label s) labs in
            let labs' = tl labs in
            let src1 = flat (map
              (fun s -> ["",Ident ",",""; "",Ident s,x2]) labs') in
            (tok::(x1,Ident (hd labs),
                   if labs' = [] then x2 else "")::src1@src2),src3,(items@l'')
        | _ -> failwith "renumber_by")
    | x::l' ->
        let src1,src23 =
         (match src with
          | tok::(_,Ident "#",_ as tok1)::(_,Ident s,_ as tok2)::src23
              when s <> "," -> [tok;tok1;tok2],src23
          | tok::(_,Ident _,_ as tok')::src23 -> [tok;tok'],src23
          | _ -> failwith "renumber_by") in
        let src2,src3,l'' = renumber_by src23 l' in
        (src1@src2),src3,(x::l'') in
  match just with
  | Proof(x,steps,z) ->
      let labels',steps' = renumber_steps labels context steps in
      labels',src,Proof(x,steps',z)
  | By(x,y,z) ->
      let src1',src2,x' = renumber_by src x in
      let src2',_,y' = renumber_by src2 y in
      labels,(src1'@src2'),By(x',y',z)
  | _ -> labels,src,just;;

let renumber_steps1 steps =
  let labels = rev (labels_of_steps [] [] steps) in
  let labels' = number_labels (!start_label) labels in
  snd (renumber_steps labels' [] steps);;

let VERBOSE_TAC : bool -> tactic -> tactic =
  fun v tac g  ->
    let call f x =
      let v' = !verbose in verbose := v;
      let y = (try f x with e -> verbose := v'; raise e) in
      verbose := v'; y in
    let (mvs,insts),gls,just = call tac g in
    (mvs,insts),gls,(call just);;

let last_thm_internal = ref None;;
let last_thm_internal' = ref None;;

let last_thm () =
  match !last_thm_internal with
  | Some th -> last_thm_internal := None; th
  | None -> failwith "last_thm";;

let check_file_verbose name lemma =
  let l = String.length name in
  if l >= 3 && String.sub name (l - 3) 3 = ".ml" then
   (let _ = exec_phrase false ("loadt \""^name^"\";;") in
    (0,0,0),TRUTH)
  else
 (last_thm_internal := None;
  let file = Pervasives.open_in name in
  let n = in_channel_length file in
  let s = String.create n in
  really_input file s 0 n;
  close_in file;
  let t,x,y = try
    let steps = parse_proof s in
   (if !growth_mode then
      try next_growth_label := 1 + max_label (labels_of_steps [] [] steps)
      with _ -> ());
    let steps',((n1,n2,n3) as x),y = if !silent_server > 0 then
        let oldstdout = Unix.dup Unix.stdout in
        let cleanup () = Unix.dup2 oldstdout Unix.stdout in
        let newstdout = Unix.openfile "/dev/null" [wronly] 0 in
        Unix.dup2 newstdout Unix.stdout;
        try
          let x = check_proof steps in cleanup(); x
        with e -> cleanup(); raise e
      else check_proof steps in
    let steps'' = if !renumber_labels then
      try renumber_steps1 steps' with Noparse -> steps' else steps' in
    let y' = if n1 + n2 + n3 = 0 then y else ASSUME (concl y) in
    last_thm_internal := Some y;
    last_thm_internal' := Some y';
   (match lemma with
    | Some s ->
        let _ = exec_phrase (!silent_server < 2 && n1 + n2 + n3 = 0)
         ("let "^s^" = "^
          "match !last_thm_internal' with Some y -> y | None -> TRUTH;;") in
        by_item_cache := undefined;
    | None -> ());
    string_of_src 0 (src_of_steps steps''),x,y
  with _ -> ("::#"^"10\n:: 10: MIZ3 EXCEPTION\n"^s),(1,0,0),TRUTH in
  let file = open_out name in
  output_string file t;
  close_out file;
  x,y);;

let check_file name =
  let (n1,n2,n3),th = check_file_verbose name None in
  if n1 + n2 + n3 = 0 then th else
    failwith (string_of_int n1^"+"^string_of_int n2^"+"^string_of_int n3^
      " errors");;

usr2_handler :=
  fun () ->
    let cleanup () = let _ = Unix.system ("rm -f "^(!miz3_filename)) in () in
    try
      let namefile = Pervasives.open_in !miz3_filename in
      let name = input_line namefile in
      let lemma = try Some (input_line namefile) with End_of_file -> None in
      close_in namefile;
      let _ = check_file_verbose name lemma in cleanup()
    with _ -> cleanup();;

let exit_proc = ref (fun () -> ());;

let server_up () =
  if Unix.fork() = 0 then
   (exit_proc := (fun () -> ());
   (try
      let pidfile = open_out !miz3_pid in
      output_string pidfile ((string_of_int (Unix.getppid()))^"\n");
      close_out pidfile
    with _ -> print_string "server_up failed\n");
    exit 0)
  else let _ = Unix.wait() in ();;

let server_down () =
  if Unix.fork() = 0 then
   (exit_proc := (fun () -> ());
   (try
      let pidfile = Pervasives.open_in !miz3_pid in
      let pid_string = input_line pidfile in
      close_in pidfile;
      if pid_string <> string_of_int (Unix.getppid())
        then failwith "server_down" else
      let _ = Unix.system ("rm -f "^(!miz3_pid)) in ()
    with _ -> print_string "server_down failed\n");
    exit 0)
  else let _ = Unix.wait() in ();;

server_up();;
exit_proc := server_down;;
at_exit (fun _ -> !exit_proc ());;

let reset_miz3 h =
  horizon := h;
  timeout := 1;
  default_prover := ("HOL_BY", CONV_TAC o HOL_BY);
  sketch_mode := false;
  just_cache := undefined;
  by_item_cache := undefined;
  current_goalstack := [];
  server_up();;
