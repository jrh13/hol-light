needs "Library/transc.ml";;

let maximas e =
  let filename = Filename.temp_file "maxima" ".out" in
  let s =
    "echo 'linel:10000; display2d:false;" ^ e ^
    ";' | maxima | grep '^(%o3)' | sed -e 's/^(%o3) //' >" ^
    filename in
  if Sys.command s <> 0 then failwith "maxima" else
  let fd = Pervasives.open_in filename in
  let data = input_line fd in
  close_in fd; Sys.remove filename; data;;

prioritize_real();;
let maxima_ops = ["+",`(+)`; "-",`(-)`; "*",`( * )`;  "/",`(/)`; "^",`(pow)`];;
let maxima_funs = ["sin",`sin`; "cos",`cos`];;

let mk_uneg = curry mk_comb `(--)`;;

let dest_uneg =
  let ntm = `(--)` in
  fun tm -> let op,t = dest_comb tm in
            if op = ntm then t else failwith "dest_uneg";;

let mk_pow = let f = mk_binop `(pow)` in fun x y -> f x (rand y);;
let mk_realvar = let real_ty = `:real` in fun x -> mk_var(x,real_ty);;

let rec string_of_hol tm =
  if is_ratconst tm then "("^string_of_num(rat_of_term tm)^")"
  else if is_numeral tm then string_of_num(dest_numeral tm)
  else if is_var tm then fst(dest_var tm)
  else if can dest_uneg tm then "-(" ^ string_of_hol(rand tm) ^ ")" else
  let lop,r = dest_comb tm in
  try let op,l = dest_comb lop in
      "("^string_of_hol l^" "^ rev_assoc op maxima_ops^" "^string_of_hol r^")"
  with Failure _ -> rev_assoc lop maxima_funs ^ "(" ^ string_of_hol r ^ ")";;

string_of_hol `(x + sin(-- &2 * x)) pow 2 - cos(x - &22 / &7)`;;

let lexe s = map (function Resword s -> s | Ident s -> s) (lex(explode s));;

let parse_bracketed prs inp =
  match prs inp with
    ast,")"::rst -> ast,rst
  | _ -> failwith "Closing bracket expected";;

let rec parse_ginfix op opup sof prs inp =
  match prs inp with
    e1,hop::rst when hop = op -> parse_ginfix op opup (opup sof e1) prs rst
  | e1,rest -> sof e1,rest;;

let parse_general_infix op =
  let opcon = if op = "^" then mk_pow else mk_binop (assoc op maxima_ops) in
  let constr = if op <> "^" & snd(get_infix_status op) = "right"
               then fun f e1 e2 -> f(opcon e1 e2)
               else fun f e1 e2 -> opcon(f e1) e2 in
  parse_ginfix op constr (fun x -> x);;

let rec parse_atomic_expression inp =
  match inp with
   [] -> failwith "expression expected"
  | "(" :: rest -> parse_bracketed parse_expression rest
  | s :: rest when forall isnum (explode s) ->
        term_of_rat(num_of_string s),rest
  | s :: "(" :: rest when forall isalnum (explode s) ->
        let e,rst = parse_bracketed parse_expression rest in
        mk_comb(assoc s maxima_funs,e),rst
  | s :: rest when forall isalnum (explode s) -> mk_realvar s,rest
and parse_exp inp = parse_general_infix "^" parse_atomic_expression inp
and parse_neg inp =
  match inp with
   | "-" :: rest -> let e,rst = parse_neg rest in mk_uneg e,rst
   | _ -> parse_exp inp
and parse_expression inp =
  itlist parse_general_infix (map fst maxima_ops) parse_neg inp;;

let hol_of_string = fst o parse_expression o lexe;;

hol_of_string "sin(x) - cos(-(- - 1 + x))";;

let FACTOR_CONV tm =
  let s = "factor("^string_of_hol tm^")" in
  let tm' = hol_of_string(maximas s) in
  REAL_RING(mk_eq(tm,tm'));;

FACTOR_CONV `&1234567890`;;

FACTOR_CONV `x pow 6 - &1`;;

FACTOR_CONV `r * (r * x * (&1 - x)) * (&1 - r * x * (&1 - x)) - x`;;

let ANTIDERIV_CONV tm =
  let x,bod = dest_abs tm in
  let s = "integrate("^string_of_hol bod^","^fst(dest_var x)^")" in
  let tm' = mk_abs(x,hol_of_string(maximas s)) in
  let th1 = CONV_RULE (NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV)
                      (SPEC x (DIFF_CONV tm')) in
  let th2 = REAL_RING(mk_eq(lhand(concl th1),bod)) in
  GEN x (GEN_REWRITE_RULE LAND_CONV [th2] th1);;

ANTIDERIV_CONV `\x. (x + &5) pow 2 + &77 * x`;;

ANTIDERIV_CONV `\x. sin(x) + x pow 11`;;

(**** This one fails as expected so we need more simplification later
ANTIDERIV_CONV `\x. sin(x) pow 3`;;
 ****)

let SIN_N_CLAUSES = prove
 (`(sin(&(NUMERAL(BIT0 n)) * x) =
    &2 * sin(&(NUMERAL n) * x) * cos(&(NUMERAL n) * x)) /\
   (sin(&(NUMERAL(BIT1 n)) * x) =
        sin(&(NUMERAL(BIT0 n)) * x) * cos(x) +
        sin(x) * cos(&(NUMERAL(BIT0 n)) * x)) /\
   (cos(&(NUMERAL(BIT0 n)) * x) =
        cos(&(NUMERAL n) * x) pow 2 - sin(&(NUMERAL n) * x) pow 2) /\
   (cos(&(NUMERAL(BIT1 n)) * x) =
        cos(&(NUMERAL(BIT0 n)) * x) * cos(x) -
        sin(x) * sin(&(NUMERAL(BIT0 n)) * x))`,
  REWRITE_TAC[REAL_MUL_2; REAL_POW_2] THEN
  REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SIN_ADD; COS_ADD; REAL_MUL_LID] THEN
  CONV_TAC REAL_RING);;

let TRIG_IDENT_TAC x =
  REWRITE_TAC[SIN_N_CLAUSES; SIN_ADD; COS_ADD] THEN
  REWRITE_TAC[REAL_MUL_LZERO; SIN_0; COS_0; REAL_MUL_RZERO] THEN
  MP_TAC(SPEC x SIN_CIRCLE) THEN CONV_TAC REAL_RING;;

let ANTIDERIV_CONV tm =
  let x,bod = dest_abs tm in
  let s = "expand(integrate("^string_of_hol bod^","^fst(dest_var x)^"))" in
  let tm' = mk_abs(x,hol_of_string(maximas s)) in
  let th1 = CONV_RULE (NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV)
                      (SPEC x (DIFF_CONV tm')) in
  let th2 = prove(mk_eq(lhand(concl th1),bod),TRIG_IDENT_TAC x) in
  GEN x (GEN_REWRITE_RULE LAND_CONV [th2] th1);;

time ANTIDERIV_CONV `\x. sin(x) pow 3`;;

time ANTIDERIV_CONV `\x. sin(x) * sin(x) pow 5 * cos(x) pow 4 + cos(x)`;;

let FCT1_WEAK = prove
 (`(!x. (f diffl f'(x)) x) ==> !x. &0 <= x ==> defint(&0,x) f' (f x - f(&0))`,
  MESON_TAC[FTC1]);;

let INTEGRAL_CONV tm =
  let th1 = MATCH_MP FCT1_WEAK (ANTIDERIV_CONV tm) in
  (CONV_RULE REAL_RAT_REDUCE_CONV o
   REWRITE_RULE[SIN_0; COS_0; REAL_MUL_LZERO; REAL_MUL_RZERO] o
   CONV_RULE REAL_RAT_REDUCE_CONV o BETA_RULE) th1;;

INTEGRAL_CONV `\x. sin(x) pow 13`;;
