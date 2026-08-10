(* ========================================================================= *)
(* Untrusted Maxima certificate generation for the WZ method.                *)
(* ========================================================================= *)

needs "WZ/wz.ml";;

(* ------------------------------------------------------------------------- *)
(* Translate the supported fragment of HOL terms to Maxima syntax.           *)
(* ------------------------------------------------------------------------- *)

let wz_maxima_binops =
  [(`(+):num->num->num`,"+");
   (`(-):num->num->num`,"-");
   (`( * ):num->num->num`,"*");
   (`(+):real->real->real`,"+");
   (`(-):real->real->real`,"-");
   (`( * ):real->real->real`,"*");
   (`(/):real->real->real`,"/");
   (`(EXP):num->num->num`,"^");
   (`(pow):real->num->real`,"^");
   (`(spow):real->real->real`,"^")];;

let wz_maxima_real_of_num = `(&):num->real`
and wz_maxima_neg = `(--) :real->real`
and wz_maxima_binom = `binom:num#num->num`
and wz_maxima_rbinom = `rbinom:real#real->real`
and wz_maxima_fact = `FACT:num->num`;;

let wz_maxima_name s =
  if s <> "" &&
     forall (fun c -> isalnum c || c = "_") (explode s) &&
     not(isnum(hd(explode s)))
  then s
  else failwith("wz_maxima_name: unsupported variable name " ^ s);;

let rec wz_maxima_string_of_term tm =
  if is_ratconst tm then
    "(" ^ string_of_num(rat_of_term tm) ^ ")"
  else if is_numeral tm then
    string_of_num(dest_numeral tm)
  else if is_var tm then
    wz_maxima_name(fst(dest_var tm))
  else if is_comb tm && rator tm = wz_maxima_real_of_num then
    wz_maxima_string_of_term(rand tm)
  else if is_comb tm && rator tm = wz_maxima_neg then
    "-(" ^ wz_maxima_string_of_term(rand tm) ^ ")"
  else if is_comb tm && rator tm = wz_maxima_fact then
    "factorial(" ^ wz_maxima_string_of_term(rand tm) ^ ")"
  else if is_comb tm && rator tm = wz_maxima_binom then
    let l,r = dest_pair(rand tm) in
    "binomial(" ^ wz_maxima_string_of_term l ^ "," ^
    wz_maxima_string_of_term r ^ ")"
  else if is_comb tm && rator tm = wz_maxima_rbinom then
    let l,r = dest_pair(rand tm) in
    "binomial(" ^ wz_maxima_string_of_term l ^ "," ^
    wz_maxima_string_of_term r ^ ")"
  else
    tryfind
     (fun (op,s) ->
        let l,r = dest_binop op tm in
        "(" ^ wz_maxima_string_of_term l ^ s ^
        wz_maxima_string_of_term r ^ ")")
     wz_maxima_binops;;

(* ------------------------------------------------------------------------- *)
(* Parse Maxima rational expressions and lists into HOL terms.               *)
(* ------------------------------------------------------------------------- *)

type wz_maxima_object =
    Wzterm of term
  | Wzlist of wz_maxima_object list;;

let wz_maxima_tokens s =
  map (function Ident s -> s | Resword s -> s) (lex(explode s));;

let wz_maxima_mk_pow x y =
  try
    let op,n = dest_comb y in
    if op = wz_maxima_real_of_num && is_numeral n
    then mk_binop `(pow):real->num->real` x n
    else fail()
  with Failure _ ->
    failwith "wz_maxima_mk_pow: non-natural exponent";;

let wz_maxima_mk_neg x =
  try
    let l,r = dest_binop `(/):real->real->real` x in
    mk_binop `(/):real->real->real` (mk_comb(wz_maxima_neg,l)) r
  with Failure _ -> mk_comb(wz_maxima_neg,x);;

let rec wz_maxima_parse_expression inp =
  wz_maxima_parse_sum inp
and wz_maxima_parse_sum inp =
  let x,rst = wz_maxima_parse_difference inp in
  match rst with
    "+"::rst' ->
      let y,rst'' = wz_maxima_parse_sum rst' in
      mk_binop `(+):real->real->real` x y,rst''
  | _ -> x,rst
and wz_maxima_parse_difference inp =
  let x,rst = wz_maxima_parse_product inp in
  wz_maxima_parse_difference_tail x rst
and wz_maxima_parse_difference_tail x inp =
  match inp with
    "-"::rst ->
      let y,rst' = wz_maxima_parse_product rst in
      wz_maxima_parse_difference_tail
       (mk_binop `(-):real->real->real` x y) rst'
  | _ -> x,inp
and wz_maxima_parse_product inp =
  let x,rst = wz_maxima_parse_quotient inp in
  match rst with
    "*"::rst' ->
      let y,rst'' = wz_maxima_parse_product rst' in
      mk_binop `( * ):real->real->real` x y,rst''
  | _ -> x,rst
and wz_maxima_parse_quotient inp =
  let x,rst = wz_maxima_parse_unary inp in
  wz_maxima_parse_quotient_tail x rst
and wz_maxima_parse_quotient_tail x inp =
  match inp with
    "/"::rst ->
      let y,rst' = wz_maxima_parse_unary rst in
      wz_maxima_parse_quotient_tail
       (mk_binop `(/):real->real->real` x y) rst'
  | _ -> x,inp
and wz_maxima_parse_unary inp =
  match inp with
    "-"::rst ->
      let x,rst' = wz_maxima_parse_unary rst in
      wz_maxima_mk_neg x,rst'
  | _ -> wz_maxima_parse_power inp
and wz_maxima_parse_power inp =
  let x,rst = wz_maxima_parse_atom inp in
  match rst with
    "^"::rst' ->
      let y,rst'' = wz_maxima_parse_unary rst' in
      wz_maxima_mk_pow x y,rst''
  | _ -> x,rst
and wz_maxima_parse_atom inp =
  match inp with
    "("::rst ->
      let x,rst' = wz_maxima_parse_expression rst in
      (match rst' with
         ")"::rst'' -> x,rst''
       | _ -> failwith "wz_maxima_parse_atom: expected )")
  | s::rst when s <> "" && forall isnum (explode s) ->
      term_of_rat(num_of_string s),rst
  | s::rst when s <> "" &&
                forall (fun c -> isalnum c || c = "_") (explode s) ->
      mk_var(wz_maxima_name s,`:real`),rst
  | _ -> failwith "wz_maxima_parse_atom: expression expected";;

let rec wz_maxima_parse_object inp =
  match inp with
    "["::"]"::rst -> Wzlist [],rst
  | "["::rst ->
      let x,rst' = wz_maxima_parse_object rst in
      wz_maxima_parse_list [x] rst'
  | _ ->
      let x,rst = wz_maxima_parse_expression inp in
      Wzterm x,rst
and wz_maxima_parse_list acc inp =
  match inp with
    ","::rst ->
      let x,rst' = wz_maxima_parse_object rst in
      wz_maxima_parse_list (x::acc) rst'
  | "]"::rst -> Wzlist(rev acc),rst
  | _ -> failwith "wz_maxima_parse_list: expected , or ]";;

let wz_maxima_certificate_of_string s =
  let obj,rst = wz_maxima_parse_object(wz_maxima_tokens s) in
  if rst <> [] then failwith "wz_maxima_certificate_of_string: trailing input"
  else
    match obj with
      Wzlist
       (Wzlist
         [Wzterm r;
          Wzlist cs]::_) ->
        let dest = function
            Wzterm c -> c
          | _ -> failwith
                  "wz_maxima_certificate_of_string: bad coefficient" in
        r,map dest cs
    | _ -> failwith "wz_maxima_certificate_of_string: bad result";;

(* ------------------------------------------------------------------------- *)
(* Run Maxima and extract the marked certificate output.                     *)
(* ------------------------------------------------------------------------- *)

let wz_maxima_executable = ref "maxima";;

let wz_maxima_output input =
  let marker = "__HOL_LIGHT_WZ_RESULT__" in
  let infile = Filename.temp_file "hol_wz" ".mac"
  and outfile = Filename.temp_file "hol_wz" ".out" in
  let cleanup () =
    if Sys.file_exists infile then Sys.remove infile;
    if Sys.file_exists outfile then Sys.remove outfile in
  let marker_length = String.length marker in
  let rec extract = function
      [] -> failwith "wz_maxima_output: output marker not found"
    | h::t ->
        if String.length h >= marker_length &&
           String.sub h 0 marker_length = marker
        then String.sub h marker_length (String.length h - marker_length)
        else extract t in
  try
    file_of_string infile
     ("display2d:false$\n" ^
      "linel:100000$\n" ^
      "load(zeilberger)$\n" ^
      "printf(true,\"" ^ marker ^ "~a~%\"," ^ input ^ ")$\n" ^
      "quit()$\n");
    let command =
      Filename.quote !wz_maxima_executable ^
      " --very-quiet --batch=" ^ Filename.quote infile ^
      " >" ^ Filename.quote outfile ^ " 2>&1" in
    if Sys.command command <> 0 then
      let output = string_of_file outfile in
      failwith("wz_maxima_output: Maxima failed\n" ^ output)
    else
      let output = extract(strings_of_file outfile) in
      cleanup(); output
  with exn -> cleanup(); raise exn;;

(* ------------------------------------------------------------------------- *)
(* Generate a certificate, then prove the recurrence using the HOL checker.  *)
(* ------------------------------------------------------------------------- *)

let WZ_MAXIMA_CERTIFICATE ntm stm =
  let ktm,bod = dest_abs(rand stm) in
  let command =
    "Zeilberger(" ^ wz_maxima_string_of_term bod ^ "," ^
    wz_maxima_string_of_term ktm ^ "," ^
    wz_maxima_string_of_term ntm ^ ")" in
  let rtm,ctm =
    wz_maxima_certificate_of_string(wz_maxima_output command) in
  let variables = setify(ktm::frees stm) in
  let instantiations =
    map
     (fun v ->
        let name,ty = dest_var v in
        let replacement =
          if ty = `:num` then mk_comb(wz_maxima_real_of_num,v)
          else if ty = `:real` then v
          else failwith "WZ_MAXIMA_CERTIFICATE: unsupported variable type" in
        replacement,mk_var(name,`:real`))
     variables in
  subst instantiations rtm,map (subst instantiations) ctm;;

let WZ_MAXIMA_PROVE ntm stm atm =
  let rtm,ctm = WZ_MAXIMA_CERTIFICATE ntm stm in
  WZ_PROVE ntm stm rtm ctm atm;;
