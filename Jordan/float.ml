(* ------------------------------------------------------------------ *)
(* Author and Copyright: Thomas C. Hales                              *)
(* License: GPL http://www.gnu.org/copyleft/gpl.html                  *)
(* Project: FLYSPECK http://www.math.pitt.edu/~thales/flyspeck/       *)
(* ------------------------------------------------------------------ *)



prioritize_real();;

let add_test,test = new_test_suite();;

let twopow =
  new_definition(
        `twopow x = if (?n. (x = (int_of_num n)))
        then ((&2) pow (nabs x))
        else inv((&2) pow (nabs x))`);;

let float =
  new_definition(
                  `float x n = (real_of_int x)*(twopow n)`);;

let interval =
  new_definition(
                   `interval x f eps = ((abs (x-f)) <= eps)`);;

(*--------------------------------------------------------------------*)

let mk_interval a b ex =
   mk_comb(mk_comb (mk_comb (`interval`,a),b),ex);;

add_test("mk_interval",
   mk_interval `#3` `#4` `#1` = `interval #3 #4 #1`);;

let dest_interval intv =
   let (h1,ex) = dest_comb intv in
   let (h2,f) = dest_comb h1 in
   let (h3,a) = dest_comb h2 in
   let _ = assert(h3 = `interval`) in
   (a,f,ex);;

add_test("dest_interval",
   let a = `#3` and b = `#4` and c = `#1` in
   dest_interval (mk_interval a b c) = (a,b,c));;

(*--------------------------------------------------------------------*)

let (dest_int:term-> Num.num) =
  fun b ->
  let dest_pos_int a =
    let (op,nat) = dest_comb a in
    if (fst (dest_const op) = "int_of_num") then (dest_numeral nat)
      else fail() in
    let (op',u) = (dest_comb b) in
    try (if (fst (dest_const op') = "int_neg") then
           minus_num (dest_pos_int u) else
             dest_pos_int b) with
        Failure _ -> failwith "dest_int ";;


let (mk_int:Num.num -> term) =
  fun a ->
    let sgn = Num.sign_num a in
    let abv = Num.abs_num a in
    let r = mk_comb(` &: `,mk_numeral abv) in
    try (if (sgn<0) then mk_comb (` --: `,r) else r) with
        Failure _ -> failwith ("dest_int "^(string_of_num a));;

add_test("mk_int",
   (mk_int (Int (-1443)) = `--: (&:1443)`) &&
   (mk_int (Int 37) = `(&:37)`));;

(* ------------------------------------------------------------------ *)

let (split_ratio:Num.num -> Num.num*Num.num) =
  function
    (Ratio r) -> (Big_int (Ratio.numerator_ratio r)),
         (Big_int (Ratio.denominator_ratio r))|
    u -> (u,(Int 1));;

add_test("split_ratio",
   let (a,b) = split_ratio ((Int 4)//(Int 20)) in
   (a =/ (Int 1)) && (b =/ (Int 5)));;

(* ------------------------------------------------------------------ *)

(* break nonzero int r into a*(C**b) with a prime to C . *)
let (factor_C:int -> Num.num -> Num.num*Num.num) =
  function c ->
  let intC = (Int c) in
  let rec divC (a,b) =
    if ((Int 0) =/ mod_num a intC) then (divC (a//intC,b+/(Int 1)))
      else (a,b) in
  function r->
  if ((Num.is_integer_num r)&& not((Num.sign_num r) = 0)) then
    divC (r,(Int 0)) else failwith "factor_C";;

add_test("factor_C",
   (factor_C 2 (Int (4096+32)) = (Int 129,Int 5)) &&
   (factor_C 10 (Int (5000)) = (Int 5,Int 3)) &&
   (cannot (factor_C 2) ((Int 50)//(Int 3))));;

(*--------------------------------------------------------------------*)

let (dest_float:term -> Num.num) =
  fun f ->
    let (a,b) = dest_binop `float` f in
    (dest_int a)*/ ((Int 2) **/ (dest_int b));;

add_test("dest_float",
   dest_float `float (&:3) (&:17)` = (Int 393216));;

add_test("dest_float2", (* must express as numeral first *)
   cannot dest_float `float ((&:3)+:(&:1)) (&:17)`);;

(* ------------------------------------------------------------------ *)
(* creates float of the form `float a b` with a odd *)
let (mk_float:Num.num -> term) =
  function r ->
    let (a,b) = split_ratio r in
    let (a',exp_a) = if (a=/(Int 0)) then ((Int 0),(Int 0)) else factor_C 2 a in
    let (b',exp_b) = factor_C 2 b in
    let c = a'//b' in
    if (Num.is_integer_num c) then
          mk_binop `float` (mk_int c) (mk_int (exp_a -/ exp_b))
          else failwith "mk_float";;

add_test("mk_float",
   mk_float (Int (4096+32)) = `float (&:129) (&:5)` &&
   (mk_float (Int 0) = `float (&:0) (&:0)`));;

add_test("mk_float2",  (* throws exception exactly when denom != 2^k *)
   let rtest = fun t -> (t =/ dest_float (mk_float t)) in
   rtest ((Int 3)//(Int 1024)) &&
  (cannot rtest ((Int 1)//(Int 3))));;

add_test("mk_float dest_float",  (* constructs canonical form of float *)
  mk_float (dest_float `float (&:4) (&:3)`) = `float (&:1) (&:5)`);;

(* ------------------------------------------------------------------ *)
(* creates decimal of the form `DECIMAL a b` with a prime to 10 *)
let (mk_pos_decimal:Num.num -> term) =
  function r ->
    let _ = assert (r >=/ (Int 0)) in
    let (a,b) = split_ratio r in
    if (a=/(Int 0)) then `#0` else
    let (a1,exp_a5) = factor_C 5 a in
    let (a2,exp_a2) = factor_C 2 a1 in
    let (b1,exp_b5) = factor_C 5 b in
    let (b2,exp_b2) = factor_C 2 b1 in
    let _ = assert(b2 =/ (Int 1)) in
    let c = end_itlist Num.max_num [exp_b5-/exp_a5;exp_b2-/exp_a2;(Int 0)] in
    let a' = a2*/((Int 2)**/ (c +/ exp_a2 -/ exp_b2))*/
             ((Int 5)**/(c +/ exp_a5 -/ exp_b5)) in
    let b' = (Int 10) **/ c in
    mk_binop `DECIMAL` (mk_numeral a') (mk_numeral b');;

add_test("mk_pos_decimal",
   mk_pos_decimal (Int (5000)) = `#5000` &&
   (mk_pos_decimal ((Int 30)//(Int 40)) = `#0.75`) &&
   (mk_pos_decimal (Int 0) = `#0`) &&
   (mk_pos_decimal ((Int 15)//(Int 25)) = `#0.6`) &&
   (mk_pos_decimal ((Int 25)//(Int 4)) = `#6.25`) &&
   (mk_pos_decimal ((Int 2)//(Int 25)) = `#0.08`));;

let (mk_decimal:Num.num->term) =
  function r ->
  let a = Num.sign_num r in
  let b = mk_pos_decimal (Num.abs_num r) in
  if (a < 0) then (mk_comb (`--.`, b)) else b;;

add_test("mk_decimal",
  (mk_decimal (Int 3) = `#3`) &&
  (mk_decimal (Int (-3)) = `--. (#3)`));;



(*--------------------------------------------------------------------*)

let (dest_decimal:term -> Num.num) =
  fun f ->
    let (a,b) = dest_binop `DECIMAL` f in
    let a1 = dest_numeral a in
    let b1 = dest_numeral b in
        a1//b1;;

add_test("dest_decimal",
   dest_decimal `#3.4` =/ ((Int 34)//(Int 10)));;
add_test("dest_decimal2",
   cannot dest_decimal `--. (#3.4)`);;





(*--------------------------------------------------------------------*)
(*   Properties of integer powers of 2.                               *)
(* ------------------------------------------------------------------ *)


let TWOPOW_POS = prove(`!n. (twopow (int_of_num n) = (&2) pow n)`,
        (REWRITE_TAC[twopow])
        THEN GEN_TAC
        THEN COND_CASES_TAC
        THENL [AP_TERM_TAC;ALL_TAC]
        THEN (REWRITE_TAC[NABS_POS])
        THEN (UNDISCH_EL_TAC 0)
        THEN (TAUT_TAC (` ( A    ) ==> (~ A ==> B)`))
        THEN (MESON_TAC[]));;

let TWOPOW_NEG = prove(`!n. (twopow (--(int_of_num n)) = inv((&2) pow n))`,
        GEN_TAC
        THEN (REWRITE_TAC[twopow])
        THEN (COND_CASES_TAC THENL [ALL_TAC;REWRITE_TAC[NABS_NEG]])
        THEN (POP_ASSUM CHOOSE_TAC)
        THEN (REWRITE_TAC[NABS_NEG])
        THEN (UNDISCH_EL_TAC 0)
        THEN (REWRITE_TAC[int_eq;int_neg_th;INT_NUM_REAL])
        THEN (REWRITE_TAC[prove (`! u y.((--(real_of_num u) = (real_of_num y))=
                ((real_of_num u) +(real_of_num y) = (&0)))`,REAL_ARITH_TAC)])
        THEN (REWRITE_TAC[REAL_OF_NUM_ADD;REAL_OF_NUM_EQ;ADD_EQ_0])
        THEN (DISCH_TAC)
        THEN (ASM_REWRITE_TAC[real_pow;REAL_INV_1]));;


let TWOPOW_INV = prove(`!a. (twopow (--: a) = (inv (twopow a)))`,
  (GEN_TAC)
  THEN ((ASSUME_TAC (SPEC `a:int` INT_REP2)))
  THEN ((POP_ASSUM CHOOSE_TAC))
  THEN ((POP_ASSUM DISJ_CASES_TAC))
  THEN ((ASM_REWRITE_TAC[TWOPOW_POS;TWOPOW_NEG;REAL_INV_INV;INT_NEG_NEG])));;

let INT_REP3 = prove(`!a .(?n.( (a = &: n) \/ (a = --: (&: (n+1)))))`,
(GEN_TAC)
THEN ((ASSUME_TAC (SPEC `a:int` INT_REP2)))
THEN ((POP_ASSUM CHOOSE_TAC))
THEN ((DISJ_CASES_TAC (prove (`((a:int) = (&: 0)) \/ ~((a:int) =(&: 0))`, MESON_TAC[]))))
(* cases *)
THENL[ ((EXISTS_TAC `0`)) THEN ((ASM_REWRITE_TAC[]));ALL_TAC]
THEN ((UNDISCH_EL_TAC 0))
THEN ((POP_ASSUM DISJ_CASES_TAC))
THENL [DISCH_TAC THEN ((ASM MESON_TAC)[]);ALL_TAC]
THEN (DISCH_TAC)
THEN ((EXISTS_TAC `PRE n`))
THEN ((DISJ2_TAC))
THEN ((ASM_REWRITE_TAC[INT_EQ_NEG2]))
(*** Changed by JRH, 2006/03/28 to avoid PRE_ELIM_TAC ***)
THEN (FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)))
THEN (ASM_REWRITE_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ])
THEN (ARITH_TAC));;

let REAL_EQ_INV = prove(`!x y. ((x:real = y) <=> (inv(x) = inv (y)))`,
((REPEAT GEN_TAC))
THEN (EQ_TAC)
THENL [((DISCH_TAC THEN (ASM_REWRITE_TAC[])));
 (* branch 2*) ((DISCH_TAC))
THEN ((ONCE_REWRITE_TAC [(GSYM REAL_INV_INV)]))
THEN ((ASM_REWRITE_TAC[]))]);;

let TWOPOW_ADD_1 =
  prove(`!a. (twopow (a +: (&:1)) = twopow (a) *. (twopow (&:1)))`,
EVERY[
  GEN_TAC;
  CHOOSE_TAC (SPEC `a:int` INT_REP3);
  POP_ASSUM DISJ_CASES_TAC
  THENL[
    ASM_REWRITE_TAC[TWOPOW_POS;INT_OF_NUM_ADD;REAL_POW_ADD];
    EVERY[
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD;INT_NEG_ADD;GSYM INT_ADD_ASSOC;INT_ADD_LINV;INT_ADD_RID];
      REWRITE_TAC[GSYM INT_NEG_ADD;INT_OF_NUM_ADD;TWOPOW_NEG;TWOPOW_POS];
      ONCE_REWRITE_TAC[SPEC `(&. 2) pow 1` (GSYM REAL_INV_INV)];
      REWRITE_TAC[GSYM REAL_INV_MUL;GSYM REAL_EQ_INV;REAL_POW_ADD;GSYM REAL_MUL_ASSOC;REAL_POW_1];
      REWRITE_TAC[MATCH_MP REAL_MUL_RINV (REAL_ARITH `~((&. 2) = (&. 0))`); REAL_MUL_RID]
    ]
  ]
]);;

let REAL_INV2 = prove(
  `(inv(&. 2)*(&. 2) = (&.1)) /\ ((&. 2)*inv(&. 2) = (&.1))`,
  SUBGOAL_TAC `~((&.2) = (&.0))`
THENL[
  REAL_ARITH_TAC;
  SIMP_TAC[REAL_MUL_RINV;REAL_MUL_LINV]]);;

let TWOPOW_0 = prove(`twopow (&: 0) = (&. 1)`,
 (REWRITE_TAC[TWOPOW_POS;real_pow]));;

let TWOPOW_SUB_NUM = prove(`!m n.( twopow((&:m) - (&: n)) = twopow((&:m))*. twopow(--: (&:n)))`,
((INDUCT_TAC))
THENL [REWRITE_TAC[INT_SUB_LZERO;REAL_MUL_LID;TWOPOW_0];ALL_TAC]
THEN ((INDUCT_TAC THEN
   ( (ASM_REWRITE_TAC[INT_SUB_RZERO;TWOPOW_0;REAL_MUL_RID;INT_NEG_0;ADD1;GSYM INT_OF_NUM_ADD]))))
THEN ((ASM_REWRITE_TAC [TWOPOW_ADD_1;TWOPOW_INV;prove (`((&:m)+(&:1)) -: ((&:n) +: (&:1)) = ((&:m)-: (&:n))`,INT_ARITH_TAC)]))
THEN ((REWRITE_TAC[REAL_INV_MUL]))
THEN ((ABBREV_TAC `a:real = twopow (&: m)`))
THEN ((ABBREV_TAC `b:real = inv(twopow (&: n))`))
THEN ((REWRITE_TAC[TWOPOW_POS;REAL_POW_1;GSYM REAL_MUL_ASSOC;prove (`!(x:real). ((&.2)*x = x*(&.2))`,REAL_ARITH_TAC)]))
THEN ((REWRITE_TAC[REAL_INV2;REAL_MUL_RID])));;

let TWOPOW_ADD_NUM = prove(
  `!m n. (twopow ((&:m) + (&:n)) = twopow((&:m))*. twopow((&:n)))`,
(REWRITE_TAC[TWOPOW_POS;REAL_POW_ADD;INT_OF_NUM_ADD]));;

let TWOPOW_ADD_INT = prove(
  `!a b. (twopow (a +: b) = twopow(a) *. (twopow(b)))`,
 ((REPEAT GEN_TAC))
THEN ((ASSUME_TAC (SPEC `a:int` INT_REP)))
THEN ((POP_ASSUM CHOOSE_TAC))
THEN ((POP_ASSUM CHOOSE_TAC))
THEN ((ASSUME_TAC (SPEC `b:int` INT_REP)))
THEN ((REPEAT (POP_ASSUM CHOOSE_TAC)))
THEN ((ASM_REWRITE_TAC[]))
THEN ((SUBGOAL_TAC `&: n -: &: m +: &: n' -: &: m' = (&: (n+n')) -: (&: (m+m'))`))
(* branch *)
THENL[ ((REWRITE_TAC[GSYM INT_OF_NUM_ADD]))
THEN ((INT_ARITH_TAC));ALL_TAC]
(* 2nd *)
THEN ((DISCH_TAC))
THEN ((ASM_REWRITE_TAC[TWOPOW_SUB_NUM;TWOPOW_INV;TWOPOW_POS;REAL_POW_ADD;REAL_INV_MUL;GSYM REAL_MUL_ASSOC]))
THEN ((ABBREV_TAC `a':real = inv ((&. 2) pow m)`))
THEN ((ABBREV_TAC `c :real = (&. 2) pow n`))
THEN ((ABBREV_TAC `d :real = (&. 2) pow n'`))
THEN ((ABBREV_TAC `e :real = inv ((&. 2) pow m')`))
THEN (MESON_TAC[REAL_MUL_AC]));;

let TWOPOW_ABS = prove(`!a. ||. (twopow a) = (twopow a)`,
(GEN_TAC)
THEN ((CHOOSE_THEN DISJ_CASES_TAC (SPEC `a:int` INT_REP2)))
(* branch *)
THEN ((ASM_REWRITE_TAC[TWOPOW_POS;TWOPOW_NEG;REAL_ABS_POW;REAL_ABS_NUM;REAL_ABS_INV])));;

let REAL_POW_POW = prove(
  `!x m n . (x **. m) **. n = x **. (m *| n)`,
((GEN_TAC THEN GEN_TAC THEN INDUCT_TAC))
(* branch *)
THENL[ ((REWRITE_TAC[real_pow;MULT_0]));
(* second branch *)
((REWRITE_TAC[real_pow]))
THEN ((ASM_REWRITE_TAC[ADD1;LEFT_ADD_DISTRIB;REAL_POW_ADD;REAL_MUL_AC;MULT_CLAUSES]))]);;

let INT_POW_POW = INT_OF_REAL_THM REAL_POW_POW;;

let TWOPOW_POW = prove(
  `!a n. (twopow a) pow n = twopow (a *: (&: n))`,
((REPEAT GEN_TAC))
THEN ((CHOOSE_THEN DISJ_CASES_TAC (SPEC `a:int` INT_REP2)))
(* branch *)
THEN ((ASM_REWRITE_TAC[TWOPOW_POS;INT_OF_NUM_MUL;
   REAL_POW_POW;TWOPOW_NEG;REAL_POW_INV;INT_OF_NUM_MUL;GSYM INT_NEG_LMUL])));;

(* ------------------------------------------------------------------ *)
(*   Arithmetic operations on float                                   *)
(* ------------------------------------------------------------------ *)
let FLOAT_NEG = prove(`!a m. --. (float a m) = float (--: a) m`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[float;GSYM REAL_MUL_LNEG;int_neg_th]);;



let FLOAT_MUL = prove(`!a b m n. (float a m) *. (float b n) = (float (a *: b) (m +: n))`,
((REPEAT GEN_TAC))
THEN ((REWRITE_TAC[float;GSYM REAL_MUL_ASSOC;TWOPOW_ADD_INT;int_mul_th]))
THEN ((MESON_TAC[REAL_MUL_AC])));;

let FLOAT_ADD = prove(
  `!a b c m. (float a (m+: (&:c))) +. (float b m)
     = (float ( (&:(2 EXP c))*a +: b) m)`,
((REWRITE_TAC[float;int_add_th;REAL_ADD_RDISTRIB;int_mul_th;TWOPOW_ADD_INT]))
THEN ((REPEAT GEN_TAC))
THEN ((REWRITE_TAC[TWOPOW_POS;INT_NUM_REAL;GSYM REAL_OF_NUM_POW]))
THEN ((MESON_TAC[REAL_MUL_AC])));;

let FLOAT_ADD_EQ = prove(
  `!a b m. (float a  m) +. (float b m) =
  (float (a+:b) m)`,
 ((REPEAT GEN_TAC))
THEN ((REWRITE_TAC[REWRITE_RULE[INT_ADD_RID] (SPEC `m:int` (SPEC `0` (SPEC `b:int` (SPEC `a:int` FLOAT_ADD))))]))
THEN ((REWRITE_TAC[EXP;INT_MUL_LID])));;

let FLOAT_ADD_NP = prove(
  `!a b m n.  (float b (--:(&: n))) +. (float a (&: m)) = (float a (&: m)) +. (float b (--:(&: n)))`,
(REWRITE_TAC[REAL_ADD_AC]));;

let FLOAT_ADD_PN = prove(
  `!a b m n. (float a (&: m)) +. (float b (--(&: n))) = (float ( (&:(2 EXP (m+| n)))*a + b) (--:(&: n)))`,
((REPEAT GEN_TAC))
THEN ((SUBGOAL_TAC `&: m = (--:(&: n)) + (&:(m+n))`))
THENL[ ((REWRITE_TAC[GSYM INT_OF_NUM_ADD]))
THEN ((INT_ARITH_TAC));
(* branch *)
((DISCH_TAC))
THEN ((ASM_REWRITE_TAC[FLOAT_ADD]))]);;

let FLOAT_ADD_PP = prove(
  `!a b m n. ((n <=| m) ==>( (float a (&: m)) +. (float b (&: n)) = (float  ((&:(2 EXP (m -| n))) *a + b) (&: n))))`,
((REPEAT GEN_TAC))
THEN (DISCH_TAC)
THEN ((SUBGOAL_TAC `&: m = (&: n) + (&: (m-n))`))
THENL[ ((REWRITE_TAC[INT_OF_NUM_ADD]))
THEN (AP_TERM_TAC)
THEN ((REWRITE_TAC[prove (`!(m:num) n. (n+m-n) = (m-n)+n`,REWRITE_TAC[ADD_AC])]))
THEN ((UNDISCH_EL_TAC 0))
THEN ((MATCH_ACCEPT_TAC(GSYM SUB_ADD)));
(* branch *)
((DISCH_TAC))
THEN ((ASM_REWRITE_TAC[FLOAT_ADD]))]);;

let FLOAT_ADD_PPv2 = prove(
  `!a b m n. ((m <| n) ==>( (float a (&: m)) +. (float b (&: n)) = (float  ((&:(2 EXP (n -| m))) *b + a) (&: m))))`,
((REPEAT GEN_TAC))
THEN (DISCH_TAC)
THEN ((H_MATCH_MP (THM (prove(`!m n. m<|n ==> m <=|n`,MESON_TAC[LT_LE]))) (HYP_INT 0)))
THEN ((UNDISCH_EL_TAC 0))
THEN ((SIMP_TAC[GSYM FLOAT_ADD_PP]))
THEN (DISCH_TAC)
THEN ((REWRITE_TAC[REAL_ADD_AC])));;

let FLOAT_ADD_NN = prove(
`!a b m n. ((n <=| m) ==>( (float a (--:(&: m))) +. (float b (--:(&: n)))
     = (float  ((&:(2 EXP (m -| n))) *b + a) (--:(&: m)))))`,
((REPEAT GEN_TAC))
THEN (DISCH_TAC)
THEN ((SUBGOAL_TAC `--: (&: n) = --: (&: m) + (&: (m-n))`))
THENL [((UNDISCH_EL_TAC 0))
THEN ((SIMP_TAC [INT_OF_REAL_THM (GSYM REAL_OF_NUM_SUB)]))
THEN (DISCH_TAC)
THEN ((INT_ARITH_TAC));
(*branch*)
((DISCH_TAC))
THEN (ASM_REWRITE_TAC[GSYM FLOAT_ADD;REAL_ADD_AC])]);;

let FLOAT_ADD_NNv2 = prove(
`!a b m n. ((m <| n) ==>( (float a (--:(&: m))) +. (float b (--:(&: n)))
     = (float  ((&:(2 EXP (n -| m))) *a + b) (--:(&: n)))))`,
((REPEAT GEN_TAC))
THEN (DISCH_TAC)
THEN (((H_MATCH_MP (THM (prove(`!m n. m<|n ==> m <=|n`,MESON_TAC[LT_LE]))) (HYP_INT 0))))
THEN (((UNDISCH_EL_TAC 0)))
THEN (((SIMP_TAC[GSYM FLOAT_ADD_NN])))
THEN ((DISCH_TAC))
THEN (((REWRITE_TAC[REAL_ADD_AC]))));;

let FLOAT_SUB = prove(
  `!a b n m. (float a n) -. (float b m)
     = (float a n) +. (float (--: b) m)`,
REWRITE_TAC[float;int_neg_th;real_sub;REAL_NEG_LMUL]);;

let FLOAT_ABS = prove(
  `!a n. ||. (float a n) = (float (||: a) n)`,
(REWRITE_TAC[float;int_abs_th;REAL_ABS_MUL;TWOPOW_ABS]));;


let FLOAT_POW = prove(
  `!a n m. (float a n) **. m = (float (a **: m) (n *: (&:m)))`,
(REWRITE_TAC[float;REAL_POW_MUL;int_pow_th;TWOPOW_POW]));;

let INT_SUB = prove(
  `!a b. (a -: b) = (a +: (--: b))`,
 (REWRITE_TAC[GSYM INT_SUB_RNEG;INT_NEG_NEG]));;

let INT_ABS_NUM = prove(
  `!n. ||: (&: n) = (&: n)`,
 (REWRITE_TAC[int_eq;int_abs_th;INT_NUM_REAL;REAL_ABS_NUM]));;

let INT_ABS_NEG_NUM = prove(
  `!n. ||: (--: (&: n)) = (&: n)`,
 (REWRITE_TAC[int_eq;int_abs_th;int_neg_th;INT_NUM_REAL;REAL_ABS_NUM;REAL_ABS_NEG]));;

let INT_ADD_NEG_NUM = prove(`!x y. --: (&: x) +: (&: y) = (&: y) +: (--: (&: x))`,
 (REWRITE_TAC[INT_ADD_AC]));;

let INT_POW_MUL = INT_OF_REAL_THM REAL_POW_MUL;;

let INT_POW_NEG1 = prove (
  `!x n. (--: (&: x)) **: n = ((--: (&: 1)) **: n) *: ((&: x) **: n)`,
(REWRITE_TAC[GSYM INT_POW_MUL; GSYM INT_NEG_MINUS1]));;



let INT_POW_EVEN_NEG1 = prove(
  `!x n. (--: (&: x)) **: (NUMERAL (BIT0 n)) =  ((&: x) **: (NUMERAL (BIT0 n)))`,
((REPEAT GEN_TAC))
THEN ((ONCE_REWRITE_TAC[INT_POW_NEG1]))
THEN ((ABBREV_TAC `a = &: 1`))
THEN ((ABBREV_TAC `b = (&: x)**: (NUMERAL (BIT0 n))`))
THEN ((REWRITE_TAC[NUMERAL;BIT0]))
THEN ((REWRITE_TAC[GSYM MULT_2;GSYM INT_POW_POW;INT_OF_REAL_THM REAL_POW_2;INT_NEG_MUL2]))
THEN ((EXPAND_TAC "a"))
THEN ((REWRITE_TAC[INT_MUL_RID;INT_MUL_LID;INT_OF_REAL_THM REAL_POW_ONE])));;

let INT_POW_ODD_NEG1 = prove(
  `!x n. (--: (&: x)) **: (NUMERAL (BIT1 n)) = --: ((&: x) **: (NUMERAL (BIT1 n)))`,
((REPEAT GEN_TAC))
THEN ((ONCE_REWRITE_TAC[INT_POW_NEG1]))
THEN (((ABBREV_TAC `a = &: 1`)))
THEN (((ABBREV_TAC `b = (&: x)**: (NUMERAL (BIT1 n))`)))
THEN ((REWRITE_TAC[NUMERAL;BIT1]))
THEN ((ONCE_REWRITE_TAC[ADD1]))
THEN ((EXPAND_TAC "a"))
THEN ((REWRITE_TAC[GSYM MULT_2]))
THEN ((REWRITE_TAC[INT_OF_REAL_THM POW_MINUS1;INT_OF_REAL_THM REAL_POW_ADD]))
THEN ((REWRITE_TAC[INT_OF_REAL_THM POW_1;INT_MUL_LID;INT_MUL_LNEG])));;

(* subtraction of integers *)

let INT_ADD_NEG = prove(
 `!x y. (x < y ==> ((&: x) +: (--: (&: y)) = --: (&: (y - x))))`,
((REPEAT GEN_TAC))
THEN ((DISCH_TAC))
THEN ((SUBGOAL_TAC `&: (y-x ) = (&: y) - (&: x)`))
THENL [((SUBGOAL_TAC `x <=| y`))
         (* branch *)
         THENL [(((ASM MESON_TAC)[LE_LT]));((SIMP_TAC[GSYM (INT_OF_REAL_THM REAL_OF_NUM_SUB)]))]
(* branch *)
; ((DISCH_TAC))
THEN ((ASM_REWRITE_TAC[]))
THEN (ACCEPT_TAC(INT_ARITH `&: x +: --: (&: y) = --: (&: y -: &: x)`))]);;

let INT_ADD_NEGv2 = prove(
 `!x y. (y <= x ==> ((&: x) +: (--: (&: y)) = (&: (x - y))))`,
 ((REPEAT GEN_TAC))
 THEN ((DISCH_TAC))
 THEN ((SUBGOAL_TAC `&: (x - y) = (&: x) - (&: y)`))
 THENL[
  ((UNDISCH_EL_TAC 0)) THEN ((SIMP_TAC[GSYM (INT_OF_REAL_THM REAL_OF_NUM_SUB)]));
  ((DISCH_TAC)) THEN ((ASM_REWRITE_TAC[INT_SUB]))
     ]
);;

(* assumes a term of the form &:a +: (--: (&: b))  *)
let INT_SUB_CONV t =
    let a,b = dest_binop `(+:)` t in
  let (_,a) = dest_comb a in
  let (_,b) = dest_comb b in
  let (_,b) = dest_comb b in
  let a = dest_numeral a in
  let b = dest_numeral b in
  let thm = if  (b <=/ a) then
    INT_ADD_NEGv2
  else INT_ADD_NEG in
  (ARITH_SIMP_CONV[thm]) t;; (*   (SIMP_CONV[thm;ARITH]) t;; *)


(* ------------------------------------------------------------------ *)
(*   Simplifies an arithmetic expression in floats                    *)
(*   A workhorse                                                      *)
(* ------------------------------------------------------------------ *)

let FLOAT_CONV =
              (ARITH_SIMP_CONV[FLOAT_MUL;FLOAT_SUB;FLOAT_ABS;FLOAT_POW;
              FLOAT_ADD_NN;FLOAT_ADD_NNv2;FLOAT_ADD_PP;FLOAT_ADD_PPv2;
              FLOAT_ADD_NP;FLOAT_ADD_PN;FLOAT_NEG;
              INT_NEG_NEG;INT_SUB;
              INT_ABS_NUM;INT_ABS_NEG_NUM;
              INT_MUL_LNEG;INT_MUL_RNEG;INT_NEG_MUL2;INT_OF_NUM_MUL;
              INT_OF_NUM_ADD;GSYM INT_NEG_ADD;INT_ADD_NEG_NUM;
              INT_OF_NUM_POW;INT_POW_ODD_NEG1;INT_POW_EVEN_NEG1;
              INT_ADD_NEG;INT_ADD_NEGv2 (* ; ARITH *)
              ]) ;;

add_test("FLOAT_CONV1",
  let f z =
    let (x,y) =  dest_eq z in
    let (u,v) =  dest_thm (FLOAT_CONV x) in
    (u=[]) && (z = v) in
  f `float (&:3) (&:0) = float (&:3) (&:0)` &&
  f `float (&:3) (&:3) = float (&:3) (&:3)` &&
  f `float (&:3) (&:0) +. (float (&:4) (&:0)) = (float (&:7) (&:0))` &&
  f `float (&:1 + (&:3)) (&:4) = float (&:4) (&:4)` &&
  f `float (&:3 - (&:7)) (&:0) = float (--:(&:4)) (&:0)` &&
  f `float (&:3) (&:4) *. (float (--: (&:2)) (&:3)) = float (--: (&:6))
                                                        (&:7)` &&
  f `--. (float (--: (&:3)) (&:0)) = float (&:3) (&:0)`
        );;

(* ------------------------------------------------------------------ *)
(*   Operations on interval. Preliminary stuff to deal with           *)
(*   chains of inequalities.                                          *)
(* ------------------------------------------------------------------ *)


let REAL_ADD_LE_SUBST_RHS = prove(
  `!a b c P. ((a <=. ((P b)) /\ (!x. (P x) =  x + (P (&. 0))) /\ (b <=. c)) ==> (a <=. (P c)))`,
(((REPEAT GEN_TAC)))
THEN (((REPEAT (TAUT_TAC `(b ==> a==> c) ==> (a /\ b ==> c)`))))
THEN (((REPEAT DISCH_TAC)))
THEN ((((H_RULER(ONCE_REWRITE_RULE))[HYP_INT 1] (HYP_INT 0))))
THEN ((((ASM ONCE_REWRITE_TAC)[])))
THEN ((((ASM MESON_TAC)[REAL_LE_RADD;REAL_LE_TRANS]))));;

let REAL_ADD_LE_SUBST_LHS = prove(
  `!a b c P. (((P(a) <=. b /\ (!x. (P x) =  x + (P (&. 0))) /\ (c <=. a)))
     ==> ((P c) <=. b))`,
(REP_GEN_TAC)
THEN (DISCH_ALL_TAC)
THEN (((H_RULER(ONCE_REWRITE_RULE)) [HYP_INT 1] (HYP_INT 0)))
THEN (((ASM ONCE_REWRITE_TAC)[]))
THEN (((ASM MESON_TAC)[REAL_LE_RADD;REAL_LE_TRANS])));;
(*
let rec SPECL =
    function [] -> I |
    (a::b)  -> fun thm ->(SPECL b (SPEC a thm));;
*)
(*
  input:
    rel: b <=. c
    thm: a <=. P(b).

  output: a <=. P(c).

  condition: REAL_ARITH must be able to prove !x. P(x) = x+. P(&.0).
  condition: the term `a` must appear exactly once the lhs of the thm.
  *)

let IWRITE_REAL_LE_RHS rel thm =
  let bvar = genvar `:real` in
  let (bt,_) = dest_binop `(<=.)` (concl rel) in
  let sub = SUBS_CONV[ASSUME (mk_eq(bt,bvar))] in
  let rule = (fun th -> EQ_MP (sub (concl th)) th) in
  let (subrel,subthm) = (rule rel,rule thm) in
  let (a,p) = dest_binop `(<=.)` (concl subthm) in
  let (_,c) = dest_binop `(<=.)` (concl subrel) in
  let pfn = mk_abs (bvar,p) in
  let imp_th = BETA_RULE (SPECL [a;bvar;c;pfn] REAL_ADD_LE_SUBST_RHS) in
  let ppart =   REAL_ARITH
      (fst(dest_conj(snd(dest_conj(fst(dest_imp(concl imp_th))))))) in
  let prethm = MATCH_MP imp_th (CONJ subthm (CONJ ppart subrel)) in
  let prethm2 = SPEC bt (GEN bvar (DISCH
       (find (fun x -> try(bvar = rhs x) with failure -> false) (hyp prethm)) prethm)) in
  MATCH_MP prethm2 (REFL bt);;

(*
  input:
    rel: c <=. a
    thm: P a <=. b

  output: P c <=. b

  condition: REAL_ARITH must be able to prove !x. P(x) = x+. P(&.0).
  condition: the term `a` must appear exactly once the lhs of the thm.
  *)

let IWRITE_REAL_LE_LHS rel thm =
  let avar = genvar `:real` in
  let (_,at) = dest_binop `(<=.)` (concl rel) in
  let sub = SUBS_CONV[ASSUME (mk_eq(at,avar))] in
  let rule = (fun th -> EQ_MP (sub (concl th)) th) in
  let (subrel,subthm) = (rule rel,rule thm) in
  let (p,b) = dest_binop `(<=.)` (concl subthm) in
  let (c,_) = dest_binop `(<=.)` (concl subrel) in
  let pfn = mk_abs (avar,p) in
  let imp_th = BETA_RULE (SPECL [avar;b;c;pfn] REAL_ADD_LE_SUBST_LHS) in
  let ppart =   REAL_ARITH
      (fst(dest_conj(snd(dest_conj(fst(dest_imp(concl imp_th))))))) in
  let prethm = MATCH_MP imp_th (CONJ subthm (CONJ ppart subrel)) in
  let prethm2 = SPEC at (GEN avar (DISCH
       (find (fun x -> try(avar = rhs x) with failure -> false) (hyp prethm)) prethm)) in
  MATCH_MP prethm2 (REFL at);;

(* ------------------------------------------------------------------ *)
(*   INTERVAL ADD, NEG, SUBTRACT                                      *)
(* ------------------------------------------------------------------ *)


let INTERVAL_ADD = prove(
   `!x f ex y g ey. interval x f ex /\ interval y g ey ==>
                         interval (x +. y) (f +. g) (ex +. ey)`,
EVERY[
 REPEAT GEN_TAC;
 TAUT_TAC `(A==>B==>C)==>(A/\ B ==> C)`;
 REWRITE_TAC[interval];
 REWRITE_TAC[prove(`(x+.y) -. (f+.g) = (x-.f) +. (y-.g)`,REAL_ARITH_TAC)];
 ABBREV_TAC `a = x-.f`;
 ABBREV_TAC `b = y-.g`;
 ASSUME_TAC (SPEC `b:real` (SPEC `a:real` ABS_TRIANGLE));
 UNDISCH_EL_TAC 0;
 ABBREV_TAC `a':real = abs a`;
 ABBREV_TAC `b':real = abs b`;
 REPEAT DISCH_TAC;
 (H_VAL2(IWRITE_REAL_LE_RHS)) (HYP_INT 0) (HYP_INT 2);
 (H_VAL2(IWRITE_REAL_LE_RHS)) (HYP_INT 2) (HYP_INT 0);
 ASM_REWRITE_TAC[]]);;

let INTERVAL_NEG = prove(
  `!x f ex. interval x f ex = interval (--. x) (--. f) ex`,
(REWRITE_TAC[interval;REAL_ABS_NEG;REAL_ARITH `!x y. -- x -. (-- y) = --. (x -. y)`]));;

let INTERVAL_NEG2 = prove(
  `!x f ex. interval (--. x) f ex = interval x (--. f) ex`,
 (REWRITE_TAC[interval;REAL_ABS_NEG;REAL_ARITH `!x y. -- x -. y = --. (x -. (--. y))`]));;


let INTERVAL_SUB = prove(
   `!x f ex y g ey. interval x f ex /\ interval y g ey ==> interval (x -. y) (f -. g) (ex +. ey)`,
((REWRITE_TAC[real_sub]))
THEN (DISCH_ALL_TAC)
THEN (((H_RULER (ONCE_REWRITE_RULE))[THM(INTERVAL_NEG)] (HYP_INT 1)))
THEN (((ASM MESON_TAC)[INTERVAL_ADD])));;

(* ------------------------------------------------------------------ *)
(*   INTERVAL MULTIPLICATION                                          *)
(* ------------------------------------------------------------------ *)


let REAL_PROP_LE_LABS = prove(
  `!x y z. (y <=. z) ==> ((abs x)* y <=. (abs x) *z)`,(SIMP_TAC[REAL_LE_LMUL_IMP;ABS_POS]));;

(* renamed from REAL_LE_ABS_RMUL *)
let REAL_PROP_LE_RABS = prove(
  `!x y z. (y <=. z) ==> ( y * (abs x) <=. z *(abs x))`,(SIMP_TAC[REAL_LE_RMUL_IMP;ABS_POS]));;

let REAL_LE_ABS_MUL = prove(
  `!x y z w. (( x <=. y) /\ (abs z <=. w)) ==> (x*.w <=. y*.w) `,
(DISCH_ALL_TAC)
THEN ((ASSUME_TAC (REAL_ARITH `abs z <=. w ==> (&.0) <=. w`)))
THEN (((ASM MESON_TAC)[REAL_LE_RMUL_IMP])));;

let INTERVAL_MUL = prove(
  `!x f ex y g ey. (interval x f ex) /\ (interval y g ey) ==>
         (interval (x *. y) (f *. g) (abs(f)*.ey +. ex*. abs(g) +. ex*.ey))`,
(REP_GEN_TAC)
THEN ((REWRITE_TAC[interval]))
THEN ((REWRITE_TAC[REAL_ARITH `(x*. y -. f*. g) = (f *.(y -. g) +. (x -. f)*.g +. (x-.f)*.(y-. g))`]))
THEN (DISCH_ALL_TAC)
THEN ((ASSUME_TAC (SPECL [`f*.(y-g)`;`(x-f)*g +. (x-f)*.(y-g)`] ABS_TRIANGLE)))
THEN ((ASSUME_TAC (SPECL [`(x-f)*.g`;`(x-f)*.(y-g)`] ABS_TRIANGLE)))
THEN (((H_VAL2(IWRITE_REAL_LE_RHS)) (HYP_INT 0) (HYP_INT 1)))
THEN ((H_REWRITE_RULE [THM ABS_MUL] (HYP_INT 0)))
THEN ((H_MATCH_MP (THM (SPECL [`g:real`; `abs (x -. f)`; `ex:real`] REAL_PROP_LE_RABS)) (HYP_INT 4)))
THEN (((H_VAL2(IWRITE_REAL_LE_RHS)) (HYP_INT 0) (HYP_INT 1)))
THEN ((H_MATCH_MP (THM (SPECL [`f:real`; `abs (y -. g)`; `ey:real`] REAL_PROP_LE_LABS)) (HYP_INT 7)))
THEN (((H_VAL2 (IWRITE_REAL_LE_RHS)) (HYP_INT 0) (HYP_INT 1)))
THEN ((H_MATCH_MP (THM (SPECL [`x-.f`; `abs (y -. g)`; `ey:real`] REAL_PROP_LE_LABS)) (HYP_INT 9)))
THEN (((H_VAL2(IWRITE_REAL_LE_RHS)) (HYP_INT 0) (HYP_INT 1)))
THEN ((ASSUME_TAC (SPECL [`abs(x-.f)`;`ex:real`;`y-.g`;`ey:real`] REAL_LE_ABS_MUL)))
THEN ((H_CONJ (HYP_INT 11) (HYP_INT 12)))
THEN ((H_MATCH_MP (HYP_INT 1) (HYP_INT 0)))
THEN (((H_VAL2(IWRITE_REAL_LE_RHS)) (HYP_INT 0) (HYP_INT 3)))
THEN ((POP_ASSUM ACCEPT_TAC)));;

(* ------------------------------------------------------------------ *)
(*   INTERVAL BASIC OPERATIONS                                        *)
(* ------------------------------------------------------------------ *)


let INTERVAL_NUM = prove(
  `!n. (interval(&.n) (float(&:n) (&:0)) (float  (&: 0) (&:0)))`,
(REWRITE_TAC[interval;float;TWOPOW_POS;pow;REAL_MUL_RID;INT_NUM_REAL;REAL_SUB_REFL;REAL_ABS_0;REAL_LE_REFL]));;

let INTERVAL_CENTER = prove(
  `!x f ex g. (interval x f ex) ==> (interval x g (abs(f-g)+.ex))`,
((REWRITE_TAC[interval]))
THEN (DISCH_ALL_TAC)
THEN ((ASSUME_TAC (REAL_ARITH `abs(x -. g) <=. abs(f-.g) +. abs(x -. f)`)))
THEN ((H_VAL2 IWRITE_REAL_LE_RHS (HYP_INT 1) (HYP_INT 0)))
THEN ((ASM_REWRITE_TAC[])));;

let INTERVAL_WIDTH = prove(
  `!x f ex ex'. (ex <=. ex') ==> (interval x f ex) ==> (interval x f ex')`,
((REWRITE_TAC[interval]))
THEN (DISCH_ALL_TAC)
THEN ((H_VAL2 IWRITE_REAL_LE_RHS (HYP_INT 1) (HYP_INT 0)))
THEN ((ASM_REWRITE_TAC[])));;

let INTERVAL_MAX = prove(
  `!x f ex. interval x f ex ==> (x <=. f+.ex)`,
(REWRITE_TAC[interval]) THEN REAL_ARITH_TAC);;

let INTERVAL_MIN = prove(
  `!x f ex. interval x f ex ==> (f-. ex <=. x)`,
(REWRITE_TAC[interval]) THEN REAL_ARITH_TAC);;

let INTERVAL_ABS_MIN = prove(
  `!x f ex. interval x f ex ==> (abs(f)-. ex <=. abs(x))`,
  (REWRITE_TAC[interval] THEN REAL_ARITH_TAC)
);;

let INTERVAL_ABS_MAX = prove(
  `!x f ex. interval x f ex ==> (abs(x) <=. abs(f)+. ex)`,
  (REWRITE_TAC[interval] THEN REAL_ARITH_TAC)
);;

let REAL_RINV_2 = prove(
  `&.2 *. (inv (&.2 )) = &. 1`,
EVERY[
  MATCH_MP_TAC REAL_MUL_RINV;
  REAL_ARITH_TAC]);;

let INTERVAL_MK = prove(
   `let half = float(&:1)(--:(&:1)) in
    !x xmin xmax. ((xmin <=. x) /\ (x <=. xmax)) ==>
      interval x
         ((xmin+.xmax)*.half)
         ((xmax-.xmin)*.half)`,
EVERY[
  REWRITE_TAC[LET_DEF;LET_END_DEF];
  DISCH_ALL_TAC;
  REWRITE_TAC[interval;float;TWOPOW_NEG;INT_NUM_REAL;REAL_POW_1;REAL_MUL_LID];
  REWRITE_TAC[GSYM INTERVAL_ABS];
  CONJ_TAC
  ]
THENL[
  EVERY[
    REWRITE_TAC[GSYM REAL_SUB_RDISTRIB];
    REWRITE_TAC[REAL_ARITH `(b+.a)-.(a-.b)=b*.(&.2)`;GSYM REAL_MUL_ASSOC];
    ASM_REWRITE_TAC[REAL_RINV_2;REAL_MUL_RID]
  ];
  EVERY[
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB];
    REWRITE_TAC[REAL_ARITH `(b+.a)+. a -. b=a*.(&.2)`;GSYM REAL_MUL_ASSOC];
    ASM_REWRITE_TAC[REAL_RINV_2;REAL_MUL_RID]
  ]
]);;

let INTERVAL_EPS_POS = prove(`!x f ex.
  (interval x f ex) ==> (&.0 <=. ex)`,
EVERY[
  REWRITE_TAC[interval];
  REPEAT (GEN_TAC);
  DISCH_THEN(fun x -> (MP_TAC (CONJ (SPEC `x-.f` REAL_ABS_POS) x)));
  MATCH_ACCEPT_TAC REAL_LE_TRANS]);;

let INTERVAL_EPS_0 = prove(
  `!x f n. (interval x f (float (&:0) n)) ==> (x = f)`,
EVERY[
  REWRITE_TAC[interval;float;int_of_num_th;REAL_MUL_LZERO];
  REAL_ARITH_TAC]);;



let REAL_EQ_RCANCEL_IMP' = prove(`!x y z.(x * z = y * z) ==> (~(z = &0) ==> (x=y))`,
  MESON_TAC[REAL_EQ_RCANCEL_IMP]);;

(* renamed from REAL_ABS_POS *)
let REAL_MK_POS_ABS_' = prove (`!x. (~(x=(&.0))) ==> (&.0 < abs(x))`,
  MESON_TAC[REAL_PROP_NZ_ABS;ABS_POS;REAL_LT_LE]);;

(* ------------------------------------------------------------------ *)
(*   INTERVAL DIVIDE                                                  *)
(* ------------------------------------------------------------------ *)

let INTERVAL_DIV = prove(`!x f ex y g ey h ez.
  (((interval x f ex) /\ (interval y g ey) /\ (ey <. (abs g)) /\
  ((ex +. (abs (f -. (h*.g))) +. (abs h)*. ey) <=. (ez*.((abs g) -. ey))))
  ==> (interval (x / y) h ez))`,

let lemma1 = prove( `&.0 < u /\ ||. z <=. e*. u ==> (&.0) <=. e`,
  EVERY[
    DISCH_ALL_TAC;
    ASSUME_TAC (SPEC `z:real` REAL_MK_NN_ABS);
    H_MATCH_MP (THM REAL_LE_TRANS) (H_RULE2 CONJ (HYP_INT 0) (HYP_INT 2));
    H_MATCH_MP (THM REAL_PROP_NN_RCANCEL) (H_RULE2 CONJ (HYP_INT 2) (HYP_INT 0));
    ASM_REWRITE_TAC[]
  ]) in
EVERY[
  DISCH_ALL_TAC;
  SUBGOAL_TAC `~(y= (&.0))`
  THENL[
    EVERY[
      UNDISCH_LIST[1;2];
      REWRITE_TAC[interval];
      REAL_ARITH_TAC
    ];
    EVERY[
      REWRITE_TAC[interval];
      DISCH_TAC THEN (H I (HYP_INT 0)) THEN (UNDISCH_EL_TAC 0);
      DISCH_THEN (fun th -> (MP_TAC(MATCH_MP REAL_MK_POS_ABS_' th)));
      MATCH_MP_TAC REAL_MUL_RTIMES_LE;
      REWRITE_TAC[GSYM ABS_MUL;REAL_SUB_RDISTRIB;real_div;GSYM REAL_MUL_ASSOC];
      ASM_SIMP_TAC[REAL_MUL_LINV;REAL_MUL_RID];
      H (REWRITE_RULE[interval]) (HYP_INT 1);
      H (REWRITE_RULE[interval]) (HYP_INT 3);
      H (MATCH_MP INTERVAL_ABS_MIN) (HYP_INT 4);
      POPL_TAC[3;4;5];
      H_VAL2 (IWRITE_REAL_LE_LHS) (HYP_INT 2) (HYP_INT 4);
      H (REWRITE_RULE[ REAL_ADD_ASSOC]) (HYP_INT 0);
      H_VAL2 (IWRITE_REAL_LE_LHS) (THM (SPEC `f-. h*g` (SPEC `x-.f` ABS_TRIANGLE))) (HYP_INT 0);
      H (ONCE_REWRITE_RULE[REAL_ABS_SUB]) (HYP_INT 4);
      H (MATCH_MP (SPEC `h:real` REAL_PROP_LE_LABS)) (HYP_INT 0);
      H (REWRITE_RULE[GSYM ABS_MUL]) (HYP_INT 0);
      H_VAL2 (IWRITE_REAL_LE_LHS) (HYP_INT 0) (HYP_INT 3);
      H_VAL2 (IWRITE_REAL_LE_LHS) (THM (SPEC `h*.(g-.y)` (SPEC`(x-.f)+(f-. h*g)`  ABS_TRIANGLE))) (HYP_INT 0);
      POPL_TAC[1;2;3;4;5;6;7;9;10;12];
      H (ONCE_REWRITE_RULE[REAL_ARITH `((x-.f) +. (f -. h*. g)) +. h*.(g-. y) = x -. h*. y `]) (HYP_INT 0);
      ABBREV_TAC `z = x -. h*.y`;
      H (ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) (HYP_INT 4);
      ABBREV_TAC `u = abs(g) -. ey`;
      POPL_TAC[0;2;4;6];
      H (MATCH_MP lemma1 ) (H_RULE2 CONJ (HYP_INT 0) (HYP_INT 1));
      H (MATCH_MP REAL_PROP_LE_LMUL) (H_RULE2 CONJ (HYP_INT 0) (HYP_INT 3));
      H (MATCH_MP REAL_LE_TRANS) (H_RULE2 CONJ (HYP_INT 3) (HYP_INT 0));
      ASM_REWRITE_TAC[]
  ];
  ]]);;

(* ------------------------------------------------------------------ *)
(*   INTERVAL ABS VALUE                                               *)
(* ------------------------------------------------------------------ *)

let INTERVAL_ABSV = prove(`!x f ex. interval x f ex ==> (interval (abs x) (abs f) ex)`,
EVERY[
  REWRITE_TAC[interval];
  DISCH_ALL_TAC;
  ASSUME_TAC (SPECL [`x:real`;`f:real`] REAL_ABS_SUB_ABS);
  ASM_MESON_TAC[REAL_LE_TRANS]
]);;  (* 7 minutes *)

(* ------------------------------------------------------------------ *)
(*   INTERVAL SQRT                                                    *)
(*   This requires some preliminaries. Extend sqrt by 0 on negatives  *)
(* ------------------------------------------------------------------ *)

let ssqrt = new_definition `ssqrt x = if (x <. (&.0)) then (&.0) else sqrt x`;; (*2m*)

let LET_TAC = REWRITE_TAC[LET_DEF;LET_END_DEF];;


let REAL_SSQRT_NEG = prove(`!x. (x <. (&.0)) ==> (ssqrt x = (&.0))`,
  EVERY[
    DISCH_ALL_TAC;
    REWRITE_TAC[ssqrt];
    COND_CASES_TAC
    THENL[
      ACCEPT_TAC (REFL `&.0`);
      ASM_MESON_TAC[]
    ]
  ]);;
(* 5 min*)

let REAL_SSQRT_NN = prove(`!x. (&.0) <=. x ==> (ssqrt x = (sqrt x))`,
  EVERY[
  DISCH_ALL_TAC;
  REWRITE_TAC[ssqrt];
  COND_CASES_TAC
  THENL[
    ASM_MESON_TAC[real_lt];
    ACCEPT_TAC (REFL `sqrt x`)
  ]
  ]);;  (* 12 min, mostly spent loading *index-shell* *)


(*17 minutes*)
let REAL_MK_NN_SSQRT = prove(`!x. (&.0) <=. (ssqrt x)`,
  EVERY[
    GEN_TAC;
    DISJ_CASES_TAC (SPECL[`x:real`;`&.0`] REAL_LTE_TOTAL)
    THENL[
      POP_ASSUM (fun th -> MP_TAC(MATCH_MP (REAL_SSQRT_NEG) th)) THEN
      MESON_TAC[REAL_LE_REFL];
      POP_ASSUM (fun th -> ASSUME_TAC(CONJ th (MATCH_MP (REAL_SSQRT_NN) th)))  THEN
      ASM_MESON_TAC[REAL_PROP_NN_SQRT]
    ]
  ]);;

let REAL_SV_SSQRT_0  = prove(`!x. ssqrt (&.0) = (&.0)`,
  EVERY[
    GEN_TAC;
    MP_TAC (SPEC `&.0` REAL_LE_REFL);
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_SSQRT_NN th]);
    ACCEPT_TAC REAL_SV_SQRT_0
  ]);; (* 6 minutes *)


let REAL_SSQRT_EQ_0 = prove(`!(x:real). (ssqrt(x) = (&.0)) ==> (x <=. (&.0))`,
  EVERY[
    GEN_TAC;
    DISJ_CASES_TAC (SPECL[`x:real`;`&.0`] REAL_LTE_TOTAL)
    THENL[
      ASM_MESON_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_SSQRT_NN] THEN
      ASM_MESON_TAC[SQRT_EQ_0;REAL_EQ_IMP_LE]
    ]
  ]);;  (* 15 minutes *)


let REAL_SSQRT_MONO = prove(`!x. (x<=. y) ==> (ssqrt x <=. (ssqrt y))`,
  EVERY[
    GEN_TAC;
    DISJ_CASES_TAC (SPECL[`x:real`;`&.0`] REAL_LTE_TOTAL)
      THENL[
        ASM_MESON_TAC[REAL_SSQRT_NEG;REAL_MK_NN_SSQRT];
        ASM_MESON_TAC[REAL_LE_TRANS;REAL_SSQRT_NN;REAL_PROP_LE_SQRT];
      ]
  ]);;  (* 5 minutes *)

let REAL_SSQRT_CHAR = prove(`!x t. (&.0 <=. t /\ (t*t = x)) ==> (t = (ssqrt x))`,
  EVERY[
    DISCH_ALL_TAC;
    H_ASSUME_TAC (H_RULE_LIST REWRITE_RULE[HYP_INT 1] (THM (SPEC `t:real` REAL_MK_NN_SQUARE)));
    ASM_MESON_TAC[REAL_SSQRT_NN;SQRT_MUL;POW_2_SQRT_ABS;REAL_POW_2;REAL_ABS_REFL];
  ]);;  (* 13 minutes *)

let REAL_SSQRT_SQUARE = prove(`!x. (&.0 <=. x) ==> ((ssqrt x)*.(ssqrt x) = x)`,
  MESON_TAC[REAL_SSQRT_NN;POW_2;SQRT_POW_2]);;(* 7min *)

let REAL_SSQRT_SQUARE' = prove(`!x. (&.0<=. x) ==> (ssqrt (x*.x) = x)`,
  DISCH_ALL_TAC THEN
  REWRITE_TAC[(MATCH_MP REAL_SSQRT_NN (SPEC `x:real` REAL_MK_NN_SQUARE))] THEN
  ASM_SIMP_TAC[SQRT_MUL;GSYM POW_2;SQRT_POW_2]);; (*20min*)


(* an alternate proof appears in RCS *)
let INTERVAL_SSQRT = prove(`!x f ex u ey ez v. (interval x f ex) /\ (interval (u*.u) f ey) /\
  (ex +.ey <=. ez*.(v+.u)) /\ (v*.v <=. f-.ex) /\ (&.0 <. u) /\ (&.0 <=. v) ==>
  (interval (ssqrt x) u ez)`,
EVERY[
  DISCH_ALL_TAC;
  H (MATCH_MP REAL_LE_TRANS) (H_RULE2 CONJ (THM (SPEC `v:real` REAL_MK_NN_SQUARE)) (HYP_INT 3));
  H (MATCH_MP (INTERVAL_MIN)) (HYP_INT 1);
  H (MATCH_MP REAL_LE_TRANS)  (H_RULE2 CONJ (HYP_INT 1) (HYP_INT 0));
  H (MATCH_MP INTERVAL_EPS_POS) (HYP_INT 3);
  H (MATCH_MP INTERVAL_EPS_POS) (HYP_INT 5);
  H (MATCH_MP REAL_PROP_NN_ADD2) (H_RULE2 CONJ (HYP_INT 1) (HYP_INT 0));
  H (MATCH_MP REAL_PROP_POS_LADD) (H_RULE2 CONJ (HYP_INT 11) (HYP_INT 10));
  H (MATCH_MP REAL_PROP_POS_LADD) (H_RULE2 CONJ (THM (SPEC `x:real` REAL_MK_NN_SSQRT)) (HYP_INT 11));
  H (MATCH_MP REAL_PROP_POS_INV) (HYP_INT 0);
  ASSUME_TAC (REAL_ARITH  `(ssqrt x -. u) = (ssqrt x -. u)*.(&.1)`);
  H (MATCH_MP REAL_MK_NZ_POS) (HYP_INT 2);
  H (MATCH_MP REAL_MUL_RINV) (HYP_INT 0);
  H_REWRITE_RULE[(H_RULE GSYM) (HYP_INT 0)] (HYP_INT 2);
  POPL_TAC[1;2;3];
  H (REWRITE_RULE[REAL_MUL_ASSOC]) (HYP_INT 0);
  H (REWRITE_RULE[ONCE_REWRITE_RULE[REAL_MUL_SYM] REAL_DIFFSQ]) (HYP_INT 0);
  POPL_TAC[1;2];
  H_SIMP_RULE[HYP_INT 7;THM REAL_SSQRT_SQUARE] (HYP_INT 0);
  ASSUME_TAC (REAL_ARITH `abs(x -. u*.u) <=. abs(x -. f) + abs(f-. u*.u)`);
  H (REWRITE_RULE[interval]) (HYP_INT 12);
  H (ONCE_REWRITE_RULE[interval]) (HYP_INT 14);
  H (ONCE_REWRITE_RULE[REAL_ABS_SUB]) (HYP_INT 0);
  POPL_TAC[1;5;15;16];
  H (MATCH_MP REAL_LE_ADD2) (H_RULE2 CONJ (HYP_INT 1) (HYP_INT 0));
  H (MATCH_MP REAL_LE_TRANS) (H_RULE2 CONJ (HYP_INT 3) (HYP_INT 0));
  POPL_TAC[1;2;3;4];
  H (AP_TERM `||.`) (HYP_INT 1);
  H (REWRITE_RULE[ABS_MUL]) (HYP_INT 0);
  H (MATCH_MP REAL_LT_IMP_LE)  (HYP_INT 4);
  H (REWRITE_RULE[GSYM REAL_ABS_REFL]) (HYP_INT 0);
  H_REWRITE_RULE [HYP_INT 0] (HYP_INT 2);
  H (MATCH_MP REAL_LE_RMUL) (H_RULE2 CONJ (HYP_INT 5) (HYP_INT 2));
  H_REWRITE_RULE [H_RULE GSYM (HYP_INT 1)] (HYP_INT 0);
  POPL_TAC[1;2;3;5;6;7;8];
  H (MATCH_MP REAL_LE_TRANS) (H_RULE2 CONJ (HYP_INT 12) (HYP_INT 9));
  H (MATCH_MP REAL_SSQRT_MONO) (HYP_INT 0);
  H (MATCH_MP REAL_SSQRT_SQUARE') (HYP_INT 16);
  H_REWRITE_RULE [HYP_INT 0] (HYP_INT 1);
  H (ONCE_REWRITE_RULE[GSYM (SPECL[`v:real`;`ssqrt x`;`u:real`] REAL_LE_RADD)]) (HYP_INT 0);
  H (MATCH_MP REAL_LE_INV2) (H_RULE2 CONJ (HYP_INT 9) (HYP_INT 0));
  POPL_TAC[1;2;3;4;5;7;8;9;12;13];
  H (MATCH_MP REAL_LE_LMUL) (H_RULE2 CONJ (HYP_INT 3) (HYP_INT 0));
  H (MATCH_MP REAL_LE_TRANS) (H_RULE2 CONJ (HYP_INT 2) (HYP_INT 0));
  H (MATCH_MP REAL_PROP_POS_INV) (HYP_INT 4);
  H (MATCH_MP REAL_LT_IMP_LE) (HYP_INT 0);
  H (MATCH_MP REAL_LE_RMUL) (H_RULE2 CONJ (HYP_INT 11) (HYP_INT 0));
  H (REWRITE_RULE[GSYM REAL_MUL_ASSOC]) (HYP_INT 0);
  H (MATCH_MP REAL_MK_NZ_POS) (HYP_INT 8);
  H (MATCH_MP REAL_MUL_RINV) (HYP_INT 0);
  H_REWRITE_RULE[HYP_INT 0; THM REAL_MUL_RID] (HYP_INT 2);
  H (MATCH_MP REAL_LE_TRANS) (H_RULE2 CONJ (HYP_INT 7) (HYP_INT 0));
  ASM_REWRITE_TAC[interval]
  ]);;



test();;


(* conversion for interval *)

(* ------------------------------------------------------------------ *)
(*   Take a term x of type real.  Convert to a thm of the form        *)
(*   interval x f eps                                                 *)
(*                                                                    *)
(* ------------------------------------------------------------------ *)

let DOUBLE_CONV_FILE=true;;

let add_test,test = new_test_suite();;

(* Num package docs at http://caml.inria.fr/ocaml/htmlman/libref/Num.html *)

(* ------------------------------------------------------------------ *)
(* num_exponent
   Take the absolute value of input.
   Write it as a*2^k, where 1 <= a < 2, return k.

   Except:
   num_exponent (Int 0) is -1.
*)
let (num_exponent:Num.num -> Num.num) =
  fun a ->
    let afloat = float_of_num (abs_num a) in
    Int ((snd (frexp afloat)) - 1);;

(*test*)let f (u,v) = ((num_exponent u) =(Int v)) in
    add_test("num_exponenwt",
                forall f
    [Int 1,0; Int 65,6; Int (-65),6;
     Int 0,-1; (Int 3)//(Int 4),-1]);;
(* ------------------------------------------------------------------ *)

let dest_unary op tm =
  try let xop,r = dest_comb tm in
      if xop = op then r else fail()
  with Failure _ -> failwith "dest_unary";;


(* ------------------------------------------------------------------ *)


(* finds a nearby (outward-rounded) Int with only prec_b significant bits *)
let (round_outward: int -> Num.num -> Num.num) =
  fun prec_b a ->
    let b = abs_num a in
    let sign = if (a =/ b) then I else minus_num in
    let throw_bits = Num.max_num (Int 0) ((num_exponent b)-/ (Int prec_b)) in
    let twoexp = power_num (Int 2) throw_bits  in
    (sign (ceiling_num (b // twoexp)))*/twoexp;;

let (round_inward: int-> Num.num -> Num.num) =
  fun prec_b a ->
    let b = abs_num a in
    let sign = if (a=/b) then I else minus_num in
    let throw_bits = Num.max_num (Int 0) ((num_exponent b)-/ (Int prec_b)) in
    let twoexp = power_num (Int 2) throw_bits  in
    (sign (floor_num (b // twoexp)))*/twoexp;;

let round_rat bprec n =
  let b = abs_num n in
  let sign = if (b =/ n) then I else minus_num in
  let powt  = ((Int 2) **/ (Int bprec)) in
  sign ((round_outward bprec (Num.ceiling_num (b */ powt)))//powt);;

let round_inward_rat bprec n =
  let b = abs_num n in
  let sign = if (b =/ n) then I else minus_num in
  let powt  = ((Int 2) **/ (Int bprec)) in
  sign ((round_inward bprec (Num.floor_num (b */ powt)))//powt);;

let (round_outward_float: int -> float -> Num.num) =
 fun  bprec f ->
  if (f=0.0) then (Int 0) else
  begin
    let b = abs_float f in
    let sign = if (f >= 0.0) then I else minus_num in
    let (x,n) = frexp b in
    let u = int_of_float( ceil (ldexp x bprec)) in
    sign ((Int u)*/ ((Int 2) **/ (Int (n - bprec))))
  end;;

let (round_inward_float: int -> float -> Num.num) =
 fun  bprec f ->
  if (f=0.0) then (Int 0) else
  begin
    (* avoid overflow on 30 bit integers *)
    let bprec = if (bprec > 25) then 25 else bprec in
    let b = abs_float f in
    let sign = if (f >= 0.0) then I else minus_num in
    let (x,n) = frexp b in
    let u = int_of_float( floor (ldexp x bprec)) in
    sign ((Int u)*/ ((Int 2) **/ (Int (n - bprec))))
  end;;

(* ------------------------------------------------------------------ *)

(* This doesn't belong here.  A general term substitution function *)
let SUBST_TERM sublist tm =
  rhs (concl ((SPECL (map fst sublist)) (GENL (map snd sublist)
                                          (REFL tm))));;

add_test("SUBST_TERM",
 SUBST_TERM [(`#1`,`a:real`);(`#2`,`b:real`)] (`a +. b +. c`) =
 `#1 + #2 + c`);;

(* ------------------------------------------------------------------ *)

(* take a term of the form `interval x f ex` and clean up the f and ex *)

let INTERVAL_CLEAN_CONV:conv =
  fun interv ->
    let (ixf,ex) = dest_comb interv in
    let (ix,f) = dest_comb ixf in
    let fthm = FLOAT_CONV f in
    let exthm = FLOAT_CONV ex in
    let ixfthm = AP_TERM ix fthm in
    MK_COMB (ixfthm, exthm);;

(*test*) add_test("INTERVAL_CLEAN_CONV",
  let testval = INTERVAL_CLEAN_CONV `interval ((&.1) +. (&.1))
       (float (&:3) (&:4) +. (float (&:2) (--: (&:3))))
       (float (&:1) (&:2) *. (float (&:3) (--: (&:2))))` in
  let hypval = hyp testval in
  let concval = concl testval in
        (length hypval = 0) &&
        concval =
     `interval (&1 + &1) (float (&:3) (&:4) + float (&:2) (--: (&:3)))
     (float (&:1) (&:2) * float (&:3) (--: (&:2))) =
     interval (&1 + &1) (float (&:386) (--: (&:3))) (float (&:3) (&:0))`
                  );;

(* ------------------------------------------------------------------ *)
(*   GENERAL lemmas                                                   *)
(* ------------------------------------------------------------------ *)


(* verifies statement of the form `float a b = float a' b'` *)

let FLOAT_EQ = prove(
  `!a b a' b'.  (float a b = (float a'  b')) <=>
        ((float a b) -. (float a' b') = (&.0))`,MESON_TAC[REAL_SUB_0]);;

let FLOAT_LT = prove(
  `!a b a' b'. (float a b <. (float a' b')) <=>
        ((&.0) <. (float a' b') -. (float a b))`,MESON_TAC[REAL_SUB_LT]);;

let FLOAT_LE = prove(
  `!a b a' b'. (float a b <=. (float a' b')) <=>
        ((&.0) <=. (float a' b') -. (float a b))`,MESON_TAC[REAL_SUB_LE]);;

let TWOPOW_MK_POS = prove(
  `!a. (&.0 <. ( twopow a))`,
EVERY[
  GEN_TAC;
  CHOOSE_TAC (SPEC `a:int` INT_REP2);
  POP_ASSUM DISJ_CASES_TAC;
  ASM_REWRITE_TAC[TWOPOW_POS;TWOPOW_NEG];
  TRY (MATCH_MP_TAC REAL_INV_POS);
  MATCH_MP_TAC REAL_POW_LT ;
  REAL_ARITH_TAC;
]);;

let TWOPOW_NZ = prove(
  `!a. ~(twopow a = (&.0))`,
  GEN_TAC THEN
  ACCEPT_TAC (MATCH_MP REAL_MK_NZ_POS (SPEC `a:int` TWOPOW_MK_POS)));;

let FLOAT_ZERO = prove(
  `!a b. (float a b = (&.0)) <=> (a = (&:0))`,
EVERY[
  REWRITE_TAC[float;REAL_ENTIRE;INT_OF_NUM_DEST];
  MESON_TAC[TWOPOW_NZ];
]);;

let INT_ZERO = prove(
  `!n. ((&:n = (&:0)) = (n=0))`,REWRITE_TAC[INT_OF_NUM_EQ]);;

let INT_ZERO_NEG=prove(
  `!n. ((--: (&:n) = (&:0))) <=> (n=0)`,
    REWRITE_TAC[INT_NEG_EQ_0;INT_ZERO]);;

let FLOAT_NN = prove(
  `!a b. ((&.0) <=. (float a b)) <=> (&:0 <=: a)`,
EVERY[
  REWRITE_TAC[float;INT_OF_NUM_DEST];
  REP_GEN_TAC;
  EQ_TAC THENL[EVERY[
  DISCH_ALL_TAC;
  INPUT_COMBO[THM REAL_PROP_NN_RCANCEL;THM (SPEC `b:int` TWOPOW_MK_POS) &&& (HYP"0")];
  ASM_MESON_TAC[int_le;int_of_num_th]];
  EVERY[
  DISCH_ALL_TAC;
  INPUT_COMBO[THM REAL_PROP_NN_POS;THM(SPEC`b:int`TWOPOW_MK_POS)];
  INPUT_COMBO[THM int_of_num_th   ; THM int_le ;(HYP"0")];
  INPUT_COMBO[THM REAL_PROP_NN_MUL2; (HYP"2")&&&(HYP"1")];
  ASM_REWRITE_TAC[]]]
]);;

let INT_NN = INT_POS;;

let INT_NN_NEG = prove(`!n. ((&:0) <=: (--:(&:n))) <=> (n = 0)`,
  REWRITE_TAC[INT_NEG_GE0;INT_OF_NUM_LE] THEN ARITH_TAC
                      );;

let FLOAT_POS = prove(`!a b. ((&.0) <. (float a b)) <=> (&:0 <: a)`,
  MESON_TAC[FLOAT_NN;FLOAT_ZERO;INT_LT_LE;REAL_LT_LE]);;

let INT_POS' = prove(`!n. (&:0) <: (&:n) <=> (~(n=0) )`,
  REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC);;

let INT_POS_NEG =prove(`!n. ((&:0) <: (--:(&:n))) <=> F`,
  REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC);;

let RAT_LEMMA1_SUB = prove(`~(y1 = &0) /\ ~(y2 = &0) ==>
      ((x1 / y1) - (x2 / y2) = (x1 * y2 - x2 * y1) * inv(y1) * inv(y2))`,
  EVERY[REWRITE_TAC[real_div];
  REWRITE_TAC[real_sub;GSYM REAL_MUL_LNEG];
  REWRITE_TAC[GSYM real_div];
  SIMP_TAC[RAT_LEMMA1];
  DISCH_TAC;
  MESON_TAC[real_div]]);;

let INTERVAL_0 = prove(`! a f ex. (interval a f ex <=> (&.0 <= (ex - (abs (a -. f)))))`,
   MESON_TAC[interval;REAL_SUB_LE]);;



let ABS_NUM = prove (`!m n. abs (&. n -. (&. m)) = &.((m-|n) + (n-|m))`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPECL [`m:num`;`n:num`] LTE_CASES) THENL[
  (* first case *)
  EVERY[ LABEL_ALL_TAC;
  H_REWRITE_RULE [THM (GSYM REAL_OF_NUM_LT)] (HYP "0");
  LABEL_ALL_TAC;
  H_ONCE_REWRITE_RULE[THM (GSYM REAL_SUB_LT)] (HYP "1");
  LABEL_ALL_TAC;
  H_MATCH_MP (THM REAL_LT_IMP_LE) (HYP "2");
  LABEL_ALL_TAC;
  H_REWRITE_RULE [THM (GSYM ABS_REFL)] (HYP "3");
  ASM_REWRITE_TAC[];
  H_MATCH_MP (THM LT_IMP_LE) (HYP "0");
  ASM_SIMP_TAC[REAL_OF_NUM_SUB];
  REWRITE_TAC[REAL_OF_NUM_EQ];
  ONCE_REWRITE_TAC[ARITH_RULE `!x:num y:num. (x = y) = (y  = x)`];
  REWRITE_TAC[EQ_ADD_RCANCEL_0];
  ASM_REWRITE_TAC[SUB_EQ_0]];
  (* second case *)
  EVERY[LABEL_ALL_TAC;
  H_REWRITE_RULE [THM (GSYM REAL_OF_NUM_LE)] (HYP "0");
  LABEL_ALL_TAC;
  H_ONCE_REWRITE_RULE[THM (GSYM REAL_SUB_LE)] (HYP "1");
  LABEL_ALL_TAC;
  H_REWRITE_RULE [THM (GSYM ABS_REFL)] (HYP "2");
  ONCE_REWRITE_TAC[GSYM REAL_ABS_NEG];
  REWRITE_TAC[REAL_ARITH `!x y. --.(x -. y) = (y-x)`];
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[REAL_OF_NUM_SUB];
  REWRITE_TAC[REAL_OF_NUM_EQ];
  ONCE_REWRITE_TAC[ARITH_RULE `!x:num y:num. (x = y) <=> (y  = x)`];
  REWRITE_TAC[EQ_ADD_LCANCEL_0];
  ASM_REWRITE_TAC[SUB_EQ_0]]]);;

let INTERVAL_TO_LESS = prove(
  `!a f ex b g ey. ((interval a f ex) /\ (interval b g ey) /\
      (&.0 <. (g -. (ey +. ex +. f)))) ==> (a <. b)`,
   let lemma1 = REAL_ARITH `!ex ey f g. (&.0 <.
     (g -. (ey +. ex +. f))) ==> ((f +. ex)<. (g -. ey)) ` in
   EVERY[
   REPEAT GEN_TAC;
   DISCH_ALL_TAC;
   H_MATCH_MP (THM lemma1) (HYP "2");
   H_MATCH_MP (THM INTERVAL_MAX) (HYP "0");
   H_MATCH_MP (THM INTERVAL_MIN) (HYP "1");
   LABEL_ALL_TAC;
   H_MATCH_MP (THM REAL_LET_TRANS) (H_RULE2 CONJ (HYP "4") (HYP "5"));
   LABEL_ALL_TAC;
   H_MATCH_MP (THM REAL_LTE_TRANS) (H_RULE2 CONJ (HYP "6") (HYP "3"));
   ASM_REWRITE_TAC[]
   ]);;

let ABS_TO_INTERVAL = prove(
  `!c u k. (abs (c - u) <=. k) ==> (!f g ex ey.((interval u f ex) /\ (interval k g ey) ==> (interval c f (g+.ey+.ex))))`,
   EVERY[
   REWRITE_TAC[interval];
   DISCH_ALL_TAC;
   REPEAT GEN_TAC;
   DISCH_ALL_TAC;
   ONCE_REWRITE_TAC [REAL_ARITH `c -. f = (c-. u) + (u-. f)`];
   ONCE_REWRITE_TAC [REAL_ADD_ASSOC];
   ASSUME_TAC (SPECL [`c-.u`;`u-.f`] ABS_TRIANGLE);
   IMP_RES_THEN ASSUME_TAC (REAL_ARITH `||.(k-.g) <=. ey ==> (k <=. (g +. ey))`);
   MATCH_MP_TAC (REAL_ARITH `(?a b.((x <=. (a+.b)) /\ (a <=. u) /\ (b <=. v)))  ==> (x <=. (u +. v))`);
   EXISTS_TAC `abs (c-.u)`;
   EXISTS_TAC `abs(u-.f)`;
   ASM_REWRITE_TAC[];
   ASM_MESON_TAC[REAL_LE_TRANS];
   ]);;


(* end of general lemmas *)
(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(* Cache of computed constants (abs (c - u) <= k)  *)
(* ------------------------------------------------------------------ *)

let calculated_constants = ref ([]:(term*thm) list);;

let add_real_constant ineq =
  try(
  let (abst,k) = dest_binop `(<=.)` (concl ineq) in
  let (absh,cmu) = dest_comb abst in
  let (c,u) = dest_binop `(-.)` cmu in
  calculated_constants := (c,ineq)::(!calculated_constants))
  with _ ->
  (try(
  let (c,f,ex) = dest_interval (concl ineq) in
  calculated_constants :=  (c,ineq)::(!calculated_constants))
  with _ -> failwith "calculated_constants format : abs(c - u) <= k");;

let get_real_constant tm =
  assoc tm !calculated_constants;;

let remove_real_constant tm =
  calculated_constants :=
    filter (fun t -> not ((fst t) = tm)) !calculated_constants;;



(* ------------------------------------------------------------------ *)

(* term of the form '&.n'. Assume error checking done already. *)
let INTERVAL_OF_NUM:conv =
  fun tm ->
    let tm1 = snd (dest_comb tm) in
    let th1 = (ARITH_REWRITE_CONV[] tm1) in
    ONCE_REWRITE_RULE[AP_TERM `&.` (GSYM th1)]
      (SPEC (rhs (concl th1)) INTERVAL_NUM);;

add_test("INTERVAL_OF_NUM",
   dest_thm (INTERVAL_OF_NUM `&.3`) = ([],
   `interval (&3) (float (&:3) (&:0)) (float (&:0) (&:0))`));;

(* term of the form `--. (&.n)`.  Assume format checking already done. *)
let INTERVAL_OF_NEG:conv =
  fun tm ->
    let (sign,u) = dest_comb tm in
    let _ = assert(sign = `--.`) in
    let (amp,tm1) = (dest_comb u) in
    let _ = assert(amp = `&.`) in
    let th1 = (ARITH_REWRITE_CONV[] tm1) in
    ONCE_REWRITE_RULE[FLOAT_NEG] (
    ONCE_REWRITE_RULE[INTERVAL_NEG] (
    ONCE_REWRITE_RULE[AP_TERM `&.` (GSYM th1)] (
       (SPEC (rhs (concl th1)) INTERVAL_NUM))));;

add_test("INTERVAL_OF_NEG",
   dest_thm (INTERVAL_OF_NEG `--.(&. (3+4))`) =
   ([],`interval( --.(&.(3 + 4)) )
      (float (--: (&:7)) (&:0)) (float (&:0) (&:0))`));;

(* ------------------------------------------------------------------ *)

let INTERVAL_TO_LESS_CONV = fun thm1 thm2 ->
   let (a,f,ex) = dest_interval (concl thm1) in
   let (b,g,ey) = dest_interval (concl thm2) in
   let rthm = ASSUME `!f g ex ey. (&.0 <. (g -. (ey +. ex +. f)))` in
   let rspec = concl (SPECL [f;g;ex;ey] rthm) in
   let rspec_simp = FLOAT_CONV (snd (dest_binop `(<.)` rspec)) in
   let rthm2 = prove (rspec,REWRITE_TAC[rspec_simp;FLOAT_POS;INT_POS';
                                        INT_POS_NEG] THEN ARITH_TAC) in
   let fthm = CONJ thm1 (CONJ thm2 rthm2) in
   MATCH_MP INTERVAL_TO_LESS fthm;;

add_test("INTERVAL_TO_LESS_CONV",
  let thm1 = ASSUME
   `interval (#0.1) (float (&:1) (--: (&:1))) (float (&:1) (--: (&:2)))` in
  let thm2 = ASSUME `interval (#7) (float (&:4) (&:1)) (float (&:1) (&:0))` in
  let thm3 = INTERVAL_TO_LESS_CONV thm1 thm2 in
    concl thm3 = `#0.1 <. (#7)`);;

add_test("INTERVAL_TO_LESS_CONV2",
   let (h,c) = dest_thm (INTERVAL_TO_LESS_CONV
     (INTERVAL_OF_NUM `&.3`) (INTERVAL_OF_NUM `&.8`)) in
     (h=[]) && (c = `&.3 <. (&.8)`));;

(* ------------------------------------------------------------------ *)

(* conversion for DEC <= posfloat and posfloat <= DEC *)

let lemma1 = prove(
  `!n m p. ((&.p/(&.m)) <= (&.n)) <=> ((&.p/(&.m)) <= (&.n)/(&.1))`,
  MESON_TAC[REAL_DIV_1]);;

let lemma2 = prove(
  `!n m p. ((&.p) <= ((&.n)/(&.m))) <=> ((&.p/(&.1)) <= (&.n)/(&.m))`,
  MESON_TAC[REAL_DIV_1]);;

let lemma3 = prove(`!a b c d. (
   ((0<b) /\ (0<d) /\ (a*d <=| c*b))
    ==> (&.a/(&.b) <=. ((&.c)/(&.d))))`,
   EVERY[REPEAT GEN_TAC;
   DISCH_ALL_TAC;
   ASM_SIMP_TAC[RAT_LEMMA4;REAL_LT;REAL_OF_NUM_MUL;REAL_LE]]);;

let DEC_FLOAT = EQT_ELIM o
   ARITH_SIMP_CONV[DECIMAL;float;TWOPOW_POS;TWOPOW_NEG;GSYM real_div;
       REAL_OF_NUM_POW;INT_NUM_REAL;REAL_OF_NUM_MUL;
       lemma1;lemma2;lemma3];;

add_test("DEC_FLOAT",
   let f c x =
      dest_thm (c x) = ([],x) in
   ((f DEC_FLOAT `#10.0 <= (float (&:3) (&:2))`) &&
    (f DEC_FLOAT `#10 <= (float (&:3) (&:2))`) &&
    (f DEC_FLOAT `#0.1 <= (float (&:1) (--: (&:2)))`) &&
    (f DEC_FLOAT `float (&:3) (&:2) <= (#13.0)`) &&
    (f DEC_FLOAT `float (&:3) (&:2) <= (#13)`) &&
    (f DEC_FLOAT `float (&:1) (--: (&:2)) <= (#0.3)`)));;
(* ------------------------------------------------------------------ *)
(* conversion for float inequalities *)

let FLOAT_INEQ_CONV t =
  let thm1=  (ONCE_REWRITE_CONV[GSYM REAL_SUB_LT;GSYM REAL_SUB_LE] t) in
  let rhsx= rhs (concl thm1) in
  let thm2= prove(rhsx,REWRITE_TAC[FLOAT_CONV (snd (dest_comb rhsx))] THEN
                    REWRITE_TAC[FLOAT_NN;FLOAT_POS;INT_NN;INT_NN_NEG;
                       INT_POS';INT_POS_NEG] THEN ARITH_TAC) in
  REWRITE_RULE[GSYM thm1] thm2;;

let t1 = `(float (&:3) (&:0)) +. (float (&:4) (&:0)) <. (float (&:8) (&:1))`;;


add_test("FLOAT_INEQ_CONV",
  let f c x =
    dest_thm (c x) = ([],x) in
  let t1 =
   `(float (&:3) (&:0)) +. (float (&:4) (&:0)) <. (float (&:8) (&:1))` in
    ((f FLOAT_INEQ_CONV t1)));;




(* ------------------------------------------------------------------ *)

(* converts a DECIMAL TO A THEOREM *)

let INTERVAL_MINMAX = prove(`!x f ex.
   ((f -. ex) <= x) /\ (x <=. (f +. ex)) ==> (interval x f ex)`,
   EVERY[REPEAT GEN_TAC;
   REWRITE_TAC[interval;ABS_BOUNDS];
   REAL_ARITH_TAC]);;


let INTERVAL_OF_DECIMAL bprec dec =
  let a_num = dest_decimal dec in
  let f_num = round_rat bprec a_num in
  let ex_num = round_rat bprec (Num.abs_num (f_num -/ a_num)) in
  let _ = assert (ex_num <=/ f_num) in
  let f = mk_float f_num in
  let ex= mk_float ex_num in
  let fplus_ex = FLOAT_CONV (mk_binop `(+.)` f ex) in
  let fminus_ex= FLOAT_CONV (mk_binop `(-.)` f ex) in
  let fplus_term = rhs (concl fplus_ex) in
  let fminus_term = rhs (concl fminus_ex) in
  let th1 = DEC_FLOAT (mk_binop `(<=.)` fminus_term dec) in
  let th2 = DEC_FLOAT (mk_binop `(<=.)` dec fplus_term) in
  let intv = mk_interval dec f ex in
  EQT_ELIM (SIMP_CONV[INTERVAL_MINMAX;fplus_ex;fminus_ex;th1;th2] intv);;

add_test("INTERVAL_OF_DECIMAL",
  let (h,c) = dest_thm (INTERVAL_OF_DECIMAL 4 `#36.1`) in
  let (x,f,ex) = dest_interval c in
   (h=[]) && (x = `#36.1`));;

add_test("INTERVAL_OF_DECIMAL2",
 can (fun() -> INTERVAL_TO_LESS_CONV (INTERVAL_OF_DECIMAL 4 `#33.33`)
  (INTERVAL_OF_DECIMAL 4 `#36.1`)) ());;

(*--------------------------------------------------------------------*)
(*   functions to check format.                                       *)
(*   There are various implicit rules:                                *)
(*   NUMERAL is followed by bits and no other kind of num, etc.       *)
(*   FLOAT a b, both a and b are &:NUMERAL or --:&:NUMERAL, etc.      *)
(*--------------------------------------------------------------------*)


(* converts exceptions to false *)
let falsify_ex f x = try (f x) with _ -> false;;

let is_bits_format  =
    let rec format x =
    if (x = `_0`) then true
    else let (h,t) = dest_comb x  in
      (((h = `BIT1`) || (h = `BIT0`)) && (format t))
    in falsify_ex format;;

let is_numeral_format =
    let fn x =
    let (h,t) = dest_comb x in
      ((h = `NUMERAL`) && (is_bits_format t)) in
    falsify_ex fn;;

let is_decimal_format  =
    let fn x =
      let (t1,t2) = dest_binop `DECIMAL` x in
        ((is_numeral_format t1) && (is_numeral_format t2)) in
    falsify_ex fn;;

let is_pos_int_format =
    let fn x =
      let (h,t) = dest_comb x in
       (h = ` &: `) && (is_numeral_format t) in
    falsify_ex fn;;

let is_neg_int_format =
    let fn x =
      let (h,t) = dest_comb x in
        (h = ` --: `) && (is_pos_int_format t) in
      falsify_ex fn;;

let is_int_format x =
  (is_neg_int_format x) || (is_pos_int_format x);;

let is_float_format =
    let fn x =
      let (t1,t2) = dest_binop `float` x in
      (is_int_format t1) && (is_int_format t2) in
    falsify_ex fn;;

let is_interval_format =
  let fn x =
    let (a,b,c) = dest_interval x in
      (is_float_format b) && (is_float_format c) in
    falsify_ex fn;;

let is_neg_real =
  let fn x =
     let (h,t) = dest_comb x in
      (h= `--.`) in
    falsify_ex fn;;

let is_real_num_format =
  let fn x =
    let (h,t) = dest_comb x in
      (h=`&.`) && (is_numeral_format t) in
  falsify_ex fn;;

let is_comb_of t u =
  let fn t u =
    t = (fst (dest_comb u)) in
  try (fn t u) with failure -> false;;

(* ------------------------------------------------------------------ *)
(* Heron's formula for the square root of A
   Return a value x that is always at most the actual square root
   and such that abs (x  - A/x ) < epsilon *)

let rec heron_sqrt depth A x eps =
    let half = (Int 1)//(Int 2) in
    if (depth <= 0) then raise (Failure "sqrt recursion depth exceeded") else
    if (Num.abs_num (x -/ (A//x) ) </ eps) && (x*/ x >=/ A)  then (A//x) else
    let x' = half */ (x +/ (A//x)) in
    heron_sqrt (depth -1) A x' eps;;

let INTERVAL_OF_TWOPOW = prove(
   `!n. interval (twopow n) (float (&:1) n) (float (&:0) (&:0))`,
   REWRITE_TAC[interval;float;int_of_num_th] THEN
   REAL_ARITH_TAC
   );;

(* ------------------------------------------------------------------ *)

let rec INTERVAL_OF_TERM bprec tm =
  (* treat cached values first *)
  if (can get_real_constant tm) then
    begin
    try(
    let int_thm = get_real_constant tm in
    if (can dest_interval (concl int_thm)) then int_thm
    else (
    let absthm = get_real_constant tm in
    let (abst,k) = dest_binop `(<=.)` (concl absthm) in
    let (absh,cmu) = dest_comb abst in
    let (c,u) = dest_binop `(-.)` cmu in
    let intk = INTERVAL_OF_TERM bprec k in
    let intu = INTERVAL_OF_TERM bprec u in
    let thm1 = MATCH_MP ABS_TO_INTERVAL absthm in
    let thm2 = MATCH_MP thm1 (CONJ intu intk) in
    let (_,f,ex)= dest_interval (concl thm2) in
    let fthm = FLOAT_CONV f in
    let exthm = FLOAT_CONV ex in
    let thm3 = REWRITE_RULE[fthm;exthm] thm2 in
    (add_real_constant thm3; thm3)
    ))
    with _ -> failwith "INTERVAL_OF_TERM : CONSTANT"
    end
  else if (is_real_num_format tm) then (INTERVAL_OF_NUM tm)
  else if (is_decimal_format tm) then (INTERVAL_OF_DECIMAL bprec tm)
  (* treat negative terms *)
  else if (is_neg_real tm) then
    begin
    try(
    let (_,t) = dest_comb tm in
    let int1 = INTERVAL_OF_TERM bprec t in
    let (_,b,_) = dest_interval (concl int1) in
    let thm1  = FLOAT_CONV (mk_comb (`--.`, b)) in
    REWRITE_RULE[thm1] (ONCE_REWRITE_RULE[INTERVAL_NEG] int1))
    with _ -> failwith "INTERVAL_OF_TERM : NEG"
    end
  (* treat abs value *)
  else if (is_comb_of `||.` tm) then
    begin
      try(
      let (_,b) = dest_comb tm in
      let b_int = MATCH_MP INTERVAL_ABSV (INTERVAL_OF_TERM bprec b) in
      let (_,f,_) = dest_interval (concl b_int) in
      let thm1 = FLOAT_CONV f in
      REWRITE_RULE[thm1] b_int)
      with _ -> failwith "INTERVAL_OF_TERM : ABS"
    end
  (* treat twopow *)
  else if (is_comb_of `twopow` tm) then
    begin
      try(
      let (_,b) = dest_comb tm in
      SPEC b INTERVAL_OF_TWOPOW
      )
      with _ -> failwith "INTERVAL_OF_TERM : TWOPOW"
    end
  (* treat addition *)
  else if (can (dest_binop `(+.)`) tm) then
    begin
    try(
    let (a,b) = dest_binop `(+.)` tm in
    let a_int = INTERVAL_OF_TERM bprec a in
    let b_int = INTERVAL_OF_TERM bprec b in
    let c_int = MATCH_MP INTERVAL_ADD (CONJ a_int b_int) in
    let (_,f,ex) = dest_interval (concl c_int) in
    let thm1 = FLOAT_CONV f and thm2 = FLOAT_CONV ex in
    REWRITE_RULE[thm1;thm2] c_int)
    with _ -> failwith "INTERVAL_OF_TERM : ADD"
    end
  (* treat subtraction *)
  else if (can (dest_binop `(-.)`) tm) then
    begin
    try(
    let (a,b) = dest_binop `(-.)` tm in
    let a_int = INTERVAL_OF_TERM bprec a in
    let b_int = INTERVAL_OF_TERM bprec b in
    let c_int = MATCH_MP INTERVAL_SUB (CONJ a_int b_int) in
    let (_,f,ex) = dest_interval (concl c_int) in
    let thm1 = FLOAT_CONV f and thm2 = FLOAT_CONV ex in
    REWRITE_RULE[thm1;thm2] c_int)
    with _ -> failwith "INTERVAL_OF_TERM : SUB"
    end
  (* treat multiplication *)
  else if (can (dest_binop `( *. )`) tm) then
    begin
    try(
    let (a,b) = dest_binop `( *. )` tm in
    let a_int = INTERVAL_OF_TERM bprec a in
    let b_int = INTERVAL_OF_TERM bprec b in
    let c_int = MATCH_MP INTERVAL_MUL (CONJ a_int b_int) in
    let (_,f,ex) = dest_interval (concl c_int) in
    let thm1 = FLOAT_CONV f and thm2 = FLOAT_CONV ex in
    REWRITE_RULE[thm1;thm2] c_int)
    with _ -> failwith "INTERVAL_OF_TERM : MUL"
    end
  (* treat division : instantiate INTERVAL_DIV *)
  else if (can (dest_binop `( / )`) tm) then
    begin
    try(
    let (a,b) = dest_binop `( / )` tm in
    let a_int = INTERVAL_OF_TERM bprec a in
    let b_int = INTERVAL_OF_TERM bprec b in
    let (_,f,ex) = dest_interval (concl a_int) in
    let (_,g,ey) = dest_interval (concl b_int) in
    let f_num = dest_float f in
    let ex_num = dest_float ex in
    let g_num = dest_float g in
    let ey_num = dest_float ey in
    let h_num = round_rat bprec (f_num//g_num) in
    let h = mk_float h_num in
    let ez_rat = (ex_num +/ abs_num (f_num -/ (h_num*/ g_num))
        +/ (abs_num h_num */ ey_num))//((abs_num g_num) -/ (ey_num)) in
    let ez_num = round_rat bprec (ez_rat) in
    let _ = assert((ez_num >=/ (Int 0))) in
    let ez = mk_float ez_num in
    let hyp1 = a_int in
    let hyp2 = b_int in
    let hyp3 = FLOAT_INEQ_CONV (mk_binop `(<.)` ey (mk_comb (`||.`,g))) in
    let thm = SPECL [a;f;ex;b;g;ey;h;ez] INTERVAL_DIV in
    let conj2 x = snd (dest_conj x) in
    let hyp4t = (conj2 (conj2 (conj2 (fst(dest_imp (concl thm)))))) in
    let hyp4 = FLOAT_INEQ_CONV hyp4t in
    let hyp_all = end_itlist CONJ [hyp1;hyp2;hyp3;hyp4] in
    MATCH_MP thm hyp_all)
    with _ -> failwith "INTERVAL_OF_TERM :DIV"
    end
  (* treat sqrt : instantiate INTERVAL_SSQRT *)
  else if (can (dest_unary `ssqrt`) tm) then
    begin
    try(
    let x = dest_unary `ssqrt` tm in
    let x_int = INTERVAL_OF_TERM bprec x in
    let (_,f,ex)  = dest_interval (concl x_int) in
    let f_num = dest_float f in
    let ex_num = dest_float ex in
    let fd_num = f_num -/ ex_num in
    let fe_f = Num.float_of_num fd_num in
    let apprx_sqrt = Pervasives.sqrt fe_f in
    (* put in heron's formula *)
    let v_num1 = round_inward_float 25 (apprx_sqrt) in
    let v_num = round_inward_rat bprec
         (heron_sqrt 10 fd_num v_num1 ((Int 2) **/ (Int (-bprec-4)))) in
    let u_num1 = round_inward_float 25
        (Pervasives.sqrt (float_of_num f_num)) in
    let u_num = round_inward_rat bprec
        (heron_sqrt 10 f_num u_num1 ((Int 2) **/ (Int (-bprec-4)))) in
    let ey_num = round_rat bprec (abs_num (f_num -/ (u_num */ u_num))) in
    let ez_num = round_rat bprec ((ex_num +/ ey_num)//(u_num +/ v_num)) in
    let (v,u) = (mk_float v_num,mk_float u_num) in
    let (ey,ez) = (mk_float ey_num,mk_float ez_num) in
    let thm = SPECL [x;f;ex;u;ey;ez;v] INTERVAL_SSQRT in
    let conjhyp = fst (dest_imp (concl thm)) in
    let [hyp6;hyp5;hyp4;hyp3;hyp2;hyp1] =
      let rec break_conj c acc =
        if (not(is_conj c)) then (c::acc) else
        let (u,v) = dest_conj c in break_conj v (u::acc) in
       (break_conj conjhyp []) in
    let thm2 = prove(hyp2,REWRITE_TAC[interval] THEN
                       (CONV_TAC FLOAT_INEQ_CONV)) in
    let thm3 = FLOAT_INEQ_CONV hyp3 in
    let thm4 = FLOAT_INEQ_CONV hyp4 in
    let float_tac = REWRITE_TAC[FLOAT_NN;FLOAT_POS;INT_NN;INT_NN_NEG;
                       INT_POS';INT_POS_NEG] THEN ARITH_TAC in
    let thm5 = prove( hyp5,float_tac) in
    let thm6 = prove( hyp6,float_tac) in
    let ant  = end_itlist CONJ[x_int;thm2;thm3;thm4;thm5;thm6] in
    MATCH_MP thm ant
    )
    with _ -> failwith "INTERVAL_OF_TERM : SSQRT"
    end
  else failwith "INTERVAL_OF_TERM : case not installed";;


let real_ineq bprec tm =
  let (t1,t2) = dest_binop `(<.)` tm in
  let int1 = INTERVAL_OF_TERM bprec t1 in
  let int2 = INTERVAL_OF_TERM bprec t2 in
  INTERVAL_TO_LESS_CONV int1 int2;;

pop_priority();;


