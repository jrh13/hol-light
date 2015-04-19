(* ========================================================================= *)
(* Theory of integers.                                                       *)
(*                                                                           *)
(* The integers are carved out of the real numbers; hence all the            *)
(* universal theorems can be derived trivially from the real analog.         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "calc_rat.ml";;

(* ------------------------------------------------------------------------- *)
(* Representing predicate. The "is_int" variant is useful for backwards      *)
(* compatibility with former definition of "is_int" constant, now removed.   *)
(* ------------------------------------------------------------------------- *)

let integer = new_definition
  `integer(x) <=> ?n. abs(x) = &n`;;

let is_int = prove
 (`integer(x) <=> ?n. x = &n \/ x = -- &n`,
  REWRITE_TAC[integer] THEN AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Type of integers.                                                         *)
(* ------------------------------------------------------------------------- *)

let int_tybij = new_type_definition "int" ("int_of_real","real_of_int")
 (prove(`?x. integer x`,
       EXISTS_TAC `&0` THEN
       REWRITE_TAC[is_int; REAL_OF_NUM_EQ; EXISTS_OR_THM; GSYM EXISTS_REFL]));;

let int_abstr,int_rep =
  SPEC_ALL(CONJUNCT1 int_tybij),SPEC_ALL(CONJUNCT2 int_tybij);;

let dest_int_rep = prove
 (`!i. ?n. (real_of_int i = &n) \/ (real_of_int i = --(&n))`,
  REWRITE_TAC[GSYM is_int; int_rep; int_abstr]);;

(* ------------------------------------------------------------------------- *)
(* We want the following too.                                                *)
(* ------------------------------------------------------------------------- *)

let int_eq = prove
 (`!x y. (x = y) <=> (real_of_int x = real_of_int y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM `int_of_real`) THEN
  REWRITE_TAC[int_abstr]);;

(* ------------------------------------------------------------------------- *)
(* Set up interface map.                                                     *)
(* ------------------------------------------------------------------------- *)

do_list overload_interface
 ["+",`int_add:int->int->int`; "-",`int_sub:int->int->int`;
  "*",`int_mul:int->int->int`; "<",`int_lt:int->int->bool`;
  "<=",`int_le:int->int->bool`; ">",`int_gt:int->int->bool`;
  ">=",`int_ge:int->int->bool`; "--",`int_neg:int->int`;
  "pow",`int_pow:int->num->int`; "abs",`int_abs:int->int`;
  "max",`int_max:int->int->int`; "min",`int_min:int->int->int`;
  "&",`int_of_num:num->int`];;

let prioritize_int() = prioritize_overload(mk_type("int",[]));;

(* ------------------------------------------------------------------------- *)
(* Definitions and closure derivations of all operations but "inv" and "/".  *)
(* ------------------------------------------------------------------------- *)

let int_le = new_definition
  `x <= y <=> (real_of_int x) <= (real_of_int y)`;;

let int_lt = new_definition
  `x < y <=> (real_of_int x) < (real_of_int y)`;;

let int_ge = new_definition
  `x >= y <=> (real_of_int x) >= (real_of_int y)`;;

let int_gt = new_definition
  `x > y <=> (real_of_int x) > (real_of_int y)`;;

let int_of_num = new_definition
  `&n = int_of_real(real_of_num n)`;;

let int_of_num_th = prove
 (`!n. real_of_int(int_of_num n) = real_of_num n`,
  REWRITE_TAC[int_of_num; GSYM int_rep; is_int] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; EXISTS_OR_THM; GSYM EXISTS_REFL]);;

let int_neg = new_definition
 `--i = int_of_real(--(real_of_int i))`;;

let int_neg_th = prove
 (`!x. real_of_int(int_neg x) = --(real_of_int x)`,
  REWRITE_TAC[int_neg; GSYM int_rep; is_int] THEN
  GEN_TAC THEN STRIP_ASSUME_TAC(SPEC `x:int` dest_int_rep) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG; EXISTS_OR_THM; REAL_EQ_NEG2;
    REAL_OF_NUM_EQ; GSYM EXISTS_REFL]);;

let int_add = new_definition
 `x + y = int_of_real((real_of_int x) + (real_of_int y))`;;

let int_add_th = prove
 (`!x y. real_of_int(x + y) = (real_of_int x) + (real_of_int y)`,
  REWRITE_TAC[int_add; GSYM int_rep; is_int] THEN REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `m:num` DISJ_CASES_TAC (SPEC `x:int` dest_int_rep) THEN
  X_CHOOSE_THEN `n:num` DISJ_CASES_TAC (SPEC `y:int` dest_int_rep) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ; EXISTS_OR_THM] THEN
  REWRITE_TAC[GSYM EXISTS_REFL] THEN
  DISJ_CASES_THEN MP_TAC (SPECL [`m:num`; `n:num`] LE_CASES) THEN
  REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; OR_EXISTS_THM; REAL_NEG_ADD] THEN
  TRY(EXISTS_TAC `d:num` THEN REAL_ARITH_TAC) THEN
  REWRITE_TAC[EXISTS_OR_THM; GSYM REAL_NEG_ADD; REAL_EQ_NEG2;
    REAL_OF_NUM_ADD; REAL_OF_NUM_EQ; GSYM EXISTS_REFL]);;

let int_sub = new_definition
  `x - y = int_of_real(real_of_int x - real_of_int y)`;;

let int_sub_th = prove
 (`!x y. real_of_int(x - y) = (real_of_int x) - (real_of_int y)`,
  REWRITE_TAC[int_sub; real_sub; GSYM int_neg_th; GSYM int_add_th] THEN
  REWRITE_TAC[int_abstr]);;

let int_mul = new_definition
  `x * y = int_of_real ((real_of_int x) * (real_of_int y))`;;

let int_mul_th = prove
 (`!x y. real_of_int(x * y) = (real_of_int x) * (real_of_int y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_mul; GSYM int_rep; is_int] THEN
  X_CHOOSE_THEN `m:num` DISJ_CASES_TAC (SPEC `x:int` dest_int_rep) THEN
  X_CHOOSE_THEN `n:num` DISJ_CASES_TAC (SPEC `y:int` dest_int_rep) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ; EXISTS_OR_THM] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG; REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_EQ_NEG2; REAL_OF_NUM_EQ; GSYM EXISTS_REFL]);;

let int_abs = new_definition
  `abs x = int_of_real(abs(real_of_int x))`;;

let int_abs_th = prove
 (`!x. real_of_int(abs x) = abs(real_of_int x)`,
  GEN_TAC THEN REWRITE_TAC[int_abs; real_abs] THEN COND_CASES_TAC THEN
  REWRITE_TAC[GSYM int_neg; int_neg_th; int_abstr]);;

let int_sgn = new_definition
  `int_sgn x = int_of_real(real_sgn(real_of_int x))`;;

let int_sgn_th = prove
 (`!x. real_of_int(int_sgn x) = real_sgn(real_of_int x)`,
  GEN_TAC THEN REWRITE_TAC[int_sgn; real_sgn; GSYM int_rep] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  MESON_TAC[is_int]);;

let int_max = new_definition
  `int_max x y = int_of_real(max (real_of_int x) (real_of_int y))`;;

let int_max_th = prove
 (`!x y. real_of_int(max x y) = max (real_of_int x) (real_of_int y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_max; real_max] THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_abstr]);;

let int_min = new_definition
  `int_min x y = int_of_real(min (real_of_int x) (real_of_int y))`;;

let int_min_th = prove
 (`!x y. real_of_int(min x y) = min (real_of_int x) (real_of_int y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_min; real_min] THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_abstr]);;

let int_pow = new_definition
  `x pow n = int_of_real((real_of_int x) pow n)`;;

let int_pow_th = prove
 (`!x n. real_of_int(x pow n) = (real_of_int x) pow n`,
  GEN_TAC THEN REWRITE_TAC[int_pow] THEN INDUCT_TAC THEN
  REWRITE_TAC[real_pow] THENL
   [REWRITE_TAC[GSYM int_of_num; int_of_num_th];
    POP_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[GSYM int_mul; int_mul_th]]);;

(* ------------------------------------------------------------------------- *)
(* A couple of theorems peculiar to the integers.                            *)
(* ------------------------------------------------------------------------- *)

let INT_IMAGE = prove
 (`!x. (?n. x = &n) \/ (?n. x = --(&n))`,
  GEN_TAC THEN
  X_CHOOSE_THEN `n:num` DISJ_CASES_TAC (SPEC `x:int` dest_int_rep) THEN
  POP_ASSUM(MP_TAC o AP_TERM `int_of_real`) THEN REWRITE_TAC[int_abstr] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[int_of_num; int_neg] THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  EXISTS_TAC `n:num` THEN REWRITE_TAC[int_abstr] THEN
  REWRITE_TAC[GSYM int_of_num; int_of_num_th]);;

let INT_LT_DISCRETE = prove
 (`!x y. x < y <=> (x + &1) <= y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[int_le; int_lt; int_add_th] THEN
  DISJ_CASES_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC )
   (SPEC `x:int` INT_IMAGE) THEN
  DISJ_CASES_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC )
   (SPEC `y:int` INT_IMAGE) THEN
  REWRITE_TAC[int_neg_th; int_of_num_th] THEN
  REWRITE_TAC[REAL_LE_NEG2; REAL_LT_NEG2] THEN
  REWRITE_TAC[REAL_LE_LNEG; REAL_LT_LNEG; REAL_LE_RNEG; REAL_LT_RNEG] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM real_sub; REAL_LE_SUB_RADD] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM ADD1; ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1)] THEN
  REWRITE_TAC[SYM(REWRITE_CONV[ARITH_SUC] `SUC 0`)] THEN
  REWRITE_TAC[ADD_CLAUSES; LE_SUC_LT; LT_SUC_LE]);;

let INT_GT_DISCRETE = prove
 (`!x y. x > y <=> x >= (y + &1)`,
  REWRITE_TAC[int_gt; int_ge; real_ge; real_gt; GSYM int_le; GSYM int_lt] THEN
  MATCH_ACCEPT_TAC INT_LT_DISCRETE);;

(* ------------------------------------------------------------------------- *)
(* Conversions of integer constants to and from OCaml numbers.               *)
(* ------------------------------------------------------------------------- *)

let is_intconst tm =
  match tm with
    Comb(Const("int_of_num",_),n) -> is_numeral n
  | Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)) ->
      is_numeral n & not(dest_numeral n = num_0)
  | _ -> false;;

let dest_intconst tm =
  match tm with
    Comb(Const("int_of_num",_),n) -> dest_numeral n
  | Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)) ->
        let nn = dest_numeral n in
        if nn <>/ num_0 then minus_num(dest_numeral n)
        else failwith "dest_intconst"
  | _ -> failwith "dest_intconst";;

let mk_intconst =
  let cast_tm = `int_of_num` and neg_tm = `int_neg` in
  let mk_numconst n = mk_comb(cast_tm,mk_numeral n) in
  fun x -> if x </ num_0 then mk_comb(neg_tm,mk_numconst(minus_num x))
           else mk_numconst x;;

(* ------------------------------------------------------------------------- *)
(* A simple procedure to lift most universal real theorems to integers.      *)
(* For a more complete procedure, give required term to INT_ARITH (below).   *)
(* ------------------------------------------------------------------------- *)

let INT_OF_REAL_THM =
  let dest = `real_of_int`
  and real_ty = `:real`
  and int_ty = `:int`
  and cond_th = prove
   (`real_of_int(if b then x else y) =
       if b then real_of_int x else real_of_int y`,
    COND_CASES_TAC THEN REWRITE_TAC[]) in
  let thlist = map GSYM
   [int_eq; int_le; int_lt; int_ge; int_gt;
    int_of_num_th; int_neg_th; int_add_th; int_mul_th; int_sgn_th;
    int_sub_th; int_abs_th; int_max_th; int_min_th; int_pow_th; cond_th] in
  let REW_RULE = GEN_REWRITE_RULE DEPTH_CONV thlist in
  let int_tm_of_real_var v =
    let s,ty = dest_var v in
    if ty = real_ty then mk_comb(dest,mk_var(s,int_ty)) else v in
  let int_of_real_var v =
    let s,ty = dest_var v in
    if ty = real_ty then mk_var(s,int_ty) else v in
  let INT_OF_REAL_THM1 th =
    let newavs = subtract (frees (concl th)) (freesl (hyp th)) in
    let avs,bod = strip_forall(concl th) in
    let allavs = newavs@avs in
    let avs' = map int_tm_of_real_var allavs in
    let avs'' = map int_of_real_var avs in
    GENL avs'' (REW_RULE(SPECL avs' (GENL newavs th))) in
  let rec INT_OF_REAL_THM th =
    if is_conj(concl th) then CONJ (INT_OF_REAL_THM (CONJUNCT1 th))
                                   (INT_OF_REAL_THM (CONJUNCT2 th))
    else INT_OF_REAL_THM1 th in
  INT_OF_REAL_THM;;

(* ------------------------------------------------------------------------- *)
(* Collect together all the theorems derived automatically.                  *)
(* ------------------------------------------------------------------------- *)

let INT_ABS_0 = INT_OF_REAL_THM REAL_ABS_0;;
let INT_ABS_1 = INT_OF_REAL_THM REAL_ABS_1;;
let INT_ABS_ABS = INT_OF_REAL_THM REAL_ABS_ABS;;
let INT_ABS_BETWEEN = INT_OF_REAL_THM REAL_ABS_BETWEEN;;
let INT_ABS_BETWEEN1 = INT_OF_REAL_THM REAL_ABS_BETWEEN1;;
let INT_ABS_BETWEEN2 = INT_OF_REAL_THM REAL_ABS_BETWEEN2;;
let INT_ABS_BOUND = INT_OF_REAL_THM REAL_ABS_BOUND;;
let INT_ABS_CASES = INT_OF_REAL_THM REAL_ABS_CASES;;
let INT_ABS_CIRCLE = INT_OF_REAL_THM REAL_ABS_CIRCLE;;
let INT_ABS_LE = INT_OF_REAL_THM REAL_ABS_LE;;
let INT_ABS_MUL = INT_OF_REAL_THM REAL_ABS_MUL;;
let INT_ABS_NEG = INT_OF_REAL_THM REAL_ABS_NEG;;
let INT_ABS_NUM = INT_OF_REAL_THM REAL_ABS_NUM;;
let INT_ABS_NZ = INT_OF_REAL_THM REAL_ABS_NZ;;
let INT_ABS_POS = INT_OF_REAL_THM REAL_ABS_POS;;
let INT_ABS_POW = INT_OF_REAL_THM REAL_ABS_POW;;
let INT_ABS_REFL = INT_OF_REAL_THM REAL_ABS_REFL;;
let INT_ABS_SGN = INT_OF_REAL_THM REAL_ABS_SGN;;
let INT_ABS_SIGN = INT_OF_REAL_THM REAL_ABS_SIGN;;
let INT_ABS_SIGN2 = INT_OF_REAL_THM REAL_ABS_SIGN2;;
let INT_ABS_STILLNZ = INT_OF_REAL_THM REAL_ABS_STILLNZ;;
let INT_ABS_SUB = INT_OF_REAL_THM REAL_ABS_SUB;;
let INT_ABS_SUB_ABS = INT_OF_REAL_THM REAL_ABS_SUB_ABS;;
let INT_ABS_TRIANGLE = INT_OF_REAL_THM REAL_ABS_TRIANGLE;;
let INT_ABS_ZERO = INT_OF_REAL_THM REAL_ABS_ZERO;;
let INT_ADD2_SUB2 = INT_OF_REAL_THM REAL_ADD2_SUB2;;
let INT_ADD_AC = INT_OF_REAL_THM REAL_ADD_AC;;
let INT_ADD_ASSOC = INT_OF_REAL_THM REAL_ADD_ASSOC;;
let INT_ADD_LDISTRIB = INT_OF_REAL_THM REAL_ADD_LDISTRIB;;
let INT_ADD_LID = INT_OF_REAL_THM REAL_ADD_LID;;
let INT_ADD_LINV = INT_OF_REAL_THM REAL_ADD_LINV;;
let INT_ADD_RDISTRIB = INT_OF_REAL_THM REAL_ADD_RDISTRIB;;
let INT_ADD_RID = INT_OF_REAL_THM REAL_ADD_RID;;
let INT_ADD_RINV = INT_OF_REAL_THM REAL_ADD_RINV;;
let INT_ADD_SUB = INT_OF_REAL_THM REAL_ADD_SUB;;
let INT_ADD_SUB2 = INT_OF_REAL_THM REAL_ADD_SUB2;;
let INT_ADD_SYM = INT_OF_REAL_THM REAL_ADD_SYM;;
let INT_BOUNDS_LE = INT_OF_REAL_THM REAL_BOUNDS_LE;;
let INT_BOUNDS_LT = INT_OF_REAL_THM REAL_BOUNDS_LT;;
let INT_DIFFSQ = INT_OF_REAL_THM REAL_DIFFSQ;;
let INT_ENTIRE = INT_OF_REAL_THM REAL_ENTIRE;;
let INT_EQ_ADD_LCANCEL = INT_OF_REAL_THM REAL_EQ_ADD_LCANCEL;;
let INT_EQ_ADD_LCANCEL_0 = INT_OF_REAL_THM REAL_EQ_ADD_LCANCEL_0;;
let INT_EQ_ADD_RCANCEL = INT_OF_REAL_THM REAL_EQ_ADD_RCANCEL;;
let INT_EQ_ADD_RCANCEL_0 = INT_OF_REAL_THM REAL_EQ_ADD_RCANCEL_0;;
let INT_EQ_IMP_LE = INT_OF_REAL_THM REAL_EQ_IMP_LE;;
let INT_EQ_MUL_LCANCEL = INT_OF_REAL_THM REAL_EQ_MUL_LCANCEL;;
let INT_EQ_MUL_RCANCEL = INT_OF_REAL_THM REAL_EQ_MUL_RCANCEL;;
let INT_EQ_NEG2 = INT_OF_REAL_THM REAL_EQ_NEG2;;
let INT_EQ_SGN_ABS = INT_OF_REAL_THM REAL_EQ_SGN_ABS;;
let INT_EQ_SQUARE_ABS = INT_OF_REAL_THM REAL_EQ_SQUARE_ABS;;
let INT_EQ_SUB_LADD = INT_OF_REAL_THM REAL_EQ_SUB_LADD;;
let INT_EQ_SUB_RADD = INT_OF_REAL_THM REAL_EQ_SUB_RADD;;
let INT_LET_ADD = INT_OF_REAL_THM REAL_LET_ADD;;
let INT_LET_ADD2 = INT_OF_REAL_THM REAL_LET_ADD2;;
let INT_LET_ANTISYM = INT_OF_REAL_THM REAL_LET_ANTISYM;;
let INT_LET_TOTAL = INT_OF_REAL_THM REAL_LET_TOTAL;;
let INT_LET_TRANS = INT_OF_REAL_THM REAL_LET_TRANS;;
let INT_LE_01 = INT_OF_REAL_THM REAL_LE_01;;
let INT_LE_ADD = INT_OF_REAL_THM REAL_LE_ADD;;
let INT_LE_ADD2 = INT_OF_REAL_THM REAL_LE_ADD2;;
let INT_LE_ADDL = INT_OF_REAL_THM REAL_LE_ADDL;;
let INT_LE_ADDR = INT_OF_REAL_THM REAL_LE_ADDR;;
let INT_LE_ANTISYM = INT_OF_REAL_THM REAL_LE_ANTISYM;;
let INT_LE_DOUBLE = INT_OF_REAL_THM REAL_LE_DOUBLE;;
let INT_LE_LADD = INT_OF_REAL_THM REAL_LE_LADD;;
let INT_LE_LADD_IMP = INT_OF_REAL_THM REAL_LE_LADD_IMP;;
let INT_LE_LMUL = INT_OF_REAL_THM REAL_LE_LMUL;;
let INT_LE_LNEG = INT_OF_REAL_THM REAL_LE_LNEG;;
let INT_LE_LT = INT_OF_REAL_THM REAL_LE_LT;;
let INT_LE_MAX = INT_OF_REAL_THM REAL_LE_MAX;;
let INT_LE_MIN = INT_OF_REAL_THM REAL_LE_MIN;;
let INT_LE_MUL = INT_OF_REAL_THM REAL_LE_MUL;;
let INT_LE_MUL_EQ = INT_OF_REAL_THM REAL_LE_MUL_EQ;;
let INT_LE_NEG = INT_OF_REAL_THM REAL_LE_NEG;;
let INT_LE_NEG2 = INT_OF_REAL_THM REAL_LE_NEG2;;
let INT_LE_NEGL = INT_OF_REAL_THM REAL_LE_NEGL;;
let INT_LE_NEGR = INT_OF_REAL_THM REAL_LE_NEGR;;
let INT_LE_NEGTOTAL = INT_OF_REAL_THM REAL_LE_NEGTOTAL;;
let INT_LE_POW2 = INT_OF_REAL_THM REAL_LE_POW2;;
let INT_LE_RADD = INT_OF_REAL_THM REAL_LE_RADD;;
let INT_LE_REFL = INT_OF_REAL_THM REAL_LE_REFL;;
let INT_LE_RMUL = INT_OF_REAL_THM REAL_LE_RMUL;;
let INT_LE_RNEG = INT_OF_REAL_THM REAL_LE_RNEG;;
let INT_LE_SQUARE = INT_OF_REAL_THM REAL_LE_SQUARE;;
let INT_LE_SQUARE_ABS = INT_OF_REAL_THM REAL_LE_SQUARE_ABS;;
let INT_LE_SUB_LADD = INT_OF_REAL_THM REAL_LE_SUB_LADD;;
let INT_LE_SUB_RADD = INT_OF_REAL_THM REAL_LE_SUB_RADD;;
let INT_LE_TOTAL = INT_OF_REAL_THM REAL_LE_TOTAL;;
let INT_LE_TRANS = INT_OF_REAL_THM REAL_LE_TRANS;;
let INT_LNEG_UNIQ = INT_OF_REAL_THM REAL_LNEG_UNIQ;;
let INT_LTE_ADD = INT_OF_REAL_THM REAL_LTE_ADD;;
let INT_LTE_ADD2 = INT_OF_REAL_THM REAL_LTE_ADD2;;
let INT_LTE_ANTISYM = INT_OF_REAL_THM REAL_LTE_ANTISYM;;
let INT_LTE_TOTAL = INT_OF_REAL_THM REAL_LTE_TOTAL;;
let INT_LTE_TRANS = INT_OF_REAL_THM REAL_LTE_TRANS;;
let INT_LT_01 = INT_OF_REAL_THM REAL_LT_01;;
let INT_LT_ADD = INT_OF_REAL_THM REAL_LT_ADD;;
let INT_LT_ADD1 = INT_OF_REAL_THM REAL_LT_ADD1;;
let INT_LT_ADD2 = INT_OF_REAL_THM REAL_LT_ADD2;;
let INT_LT_ADDL = INT_OF_REAL_THM REAL_LT_ADDL;;
let INT_LT_ADDNEG = INT_OF_REAL_THM REAL_LT_ADDNEG;;
let INT_LT_ADDNEG2 = INT_OF_REAL_THM REAL_LT_ADDNEG2;;
let INT_LT_ADDR = INT_OF_REAL_THM REAL_LT_ADDR;;
let INT_LT_ADD_SUB = INT_OF_REAL_THM REAL_LT_ADD_SUB;;
let INT_LT_ANTISYM = INT_OF_REAL_THM REAL_LT_ANTISYM;;
let INT_LT_GT = INT_OF_REAL_THM REAL_LT_GT;;
let INT_LT_IMP_LE = INT_OF_REAL_THM REAL_LT_IMP_LE;;
let INT_LT_IMP_NE = INT_OF_REAL_THM REAL_LT_IMP_NE;;
let INT_LT_LADD = INT_OF_REAL_THM REAL_LT_LADD;;
let INT_LT_LE = INT_OF_REAL_THM REAL_LT_LE;;
let INT_LT_LMUL_EQ = INT_OF_REAL_THM REAL_LT_LMUL_EQ;;
let INT_LT_MAX = INT_OF_REAL_THM REAL_LT_MAX;;
let INT_LT_MIN = INT_OF_REAL_THM REAL_LT_MIN;;
let INT_LT_MUL = INT_OF_REAL_THM REAL_LT_MUL;;
let INT_LT_MUL_EQ = INT_OF_REAL_THM REAL_LT_MUL_EQ;;
let INT_LT_NEG = INT_OF_REAL_THM REAL_LT_NEG;;
let INT_LT_NEG2 = INT_OF_REAL_THM REAL_LT_NEG2;;
let INT_LT_NEGTOTAL = INT_OF_REAL_THM REAL_LT_NEGTOTAL;;
let INT_LT_POW2 = INT_OF_REAL_THM REAL_LT_POW2;;
let INT_LT_RADD = INT_OF_REAL_THM REAL_LT_RADD;;
let INT_LT_REFL = INT_OF_REAL_THM REAL_LT_REFL;;
let INT_LT_RMUL_EQ = INT_OF_REAL_THM REAL_LT_RMUL_EQ;;
let INT_LT_SQUARE_ABS = INT_OF_REAL_THM REAL_LT_SQUARE_ABS;;
let INT_LT_SUB_LADD = INT_OF_REAL_THM REAL_LT_SUB_LADD;;
let INT_LT_SUB_RADD = INT_OF_REAL_THM REAL_LT_SUB_RADD;;
let INT_LT_TOTAL = INT_OF_REAL_THM REAL_LT_TOTAL;;
let INT_LT_TRANS = INT_OF_REAL_THM REAL_LT_TRANS;;
let INT_MAX_ACI = INT_OF_REAL_THM REAL_MAX_ACI;;
let INT_MAX_ASSOC = INT_OF_REAL_THM REAL_MAX_ASSOC;;
let INT_MAX_LE = INT_OF_REAL_THM REAL_MAX_LE;;
let INT_MAX_LT = INT_OF_REAL_THM REAL_MAX_LT;;
let INT_MAX_MAX = INT_OF_REAL_THM REAL_MAX_MAX;;
let INT_MAX_MIN = INT_OF_REAL_THM REAL_MAX_MIN;;
let INT_MAX_SYM = INT_OF_REAL_THM REAL_MAX_SYM;;
let INT_MIN_ACI = INT_OF_REAL_THM REAL_MIN_ACI;;
let INT_MIN_ASSOC = INT_OF_REAL_THM REAL_MIN_ASSOC;;
let INT_MIN_LE = INT_OF_REAL_THM REAL_MIN_LE;;
let INT_MIN_LT = INT_OF_REAL_THM REAL_MIN_LT;;
let INT_MIN_MAX = INT_OF_REAL_THM REAL_MIN_MAX;;
let INT_MIN_MIN = INT_OF_REAL_THM REAL_MIN_MIN;;
let INT_MIN_SYM = INT_OF_REAL_THM REAL_MIN_SYM;;
let INT_MUL_AC = INT_OF_REAL_THM REAL_MUL_AC;;
let INT_MUL_ASSOC = INT_OF_REAL_THM REAL_MUL_ASSOC;;
let INT_MUL_LID = INT_OF_REAL_THM REAL_MUL_LID;;
let INT_MUL_LNEG = INT_OF_REAL_THM REAL_MUL_LNEG;;
let INT_MUL_LZERO = INT_OF_REAL_THM REAL_MUL_LZERO;;
let INT_MUL_POS_LE = INT_OF_REAL_THM REAL_MUL_POS_LE;;
let INT_MUL_POS_LT = INT_OF_REAL_THM REAL_MUL_POS_LT;;
let INT_MUL_RID = INT_OF_REAL_THM REAL_MUL_RID;;
let INT_MUL_RNEG = INT_OF_REAL_THM REAL_MUL_RNEG;;
let INT_MUL_RZERO = INT_OF_REAL_THM REAL_MUL_RZERO;;
let INT_MUL_SYM = INT_OF_REAL_THM REAL_MUL_SYM;;
let INT_NEGNEG = INT_OF_REAL_THM REAL_NEGNEG;;
let INT_NEG_0 = INT_OF_REAL_THM REAL_NEG_0;;
let INT_NEG_ADD = INT_OF_REAL_THM REAL_NEG_ADD;;
let INT_NEG_EQ = INT_OF_REAL_THM REAL_NEG_EQ;;
let INT_NEG_EQ_0 = INT_OF_REAL_THM REAL_NEG_EQ_0;;
let INT_NEG_GE0 = INT_OF_REAL_THM REAL_NEG_GE0;;
let INT_NEG_GT0 = INT_OF_REAL_THM REAL_NEG_GT0;;
let INT_NEG_LE0 = INT_OF_REAL_THM REAL_NEG_LE0;;
let INT_NEG_LMUL = INT_OF_REAL_THM REAL_NEG_LMUL;;
let INT_NEG_LT0 = INT_OF_REAL_THM REAL_NEG_LT0;;
let INT_NEG_MINUS1 = INT_OF_REAL_THM REAL_NEG_MINUS1;;
let INT_NEG_MUL2 = INT_OF_REAL_THM REAL_NEG_MUL2;;
let INT_NEG_NEG = INT_OF_REAL_THM REAL_NEG_NEG;;
let INT_NEG_RMUL = INT_OF_REAL_THM REAL_NEG_RMUL;;
let INT_NEG_SUB = INT_OF_REAL_THM REAL_NEG_SUB;;
let INT_NOT_EQ = INT_OF_REAL_THM REAL_NOT_EQ;;
let INT_NOT_LE = INT_OF_REAL_THM REAL_NOT_LE;;
let INT_NOT_LT = INT_OF_REAL_THM REAL_NOT_LT;;
let INT_OF_NUM_ADD = INT_OF_REAL_THM REAL_OF_NUM_ADD;;
let INT_OF_NUM_EQ = INT_OF_REAL_THM REAL_OF_NUM_EQ;;
let INT_OF_NUM_GE = INT_OF_REAL_THM REAL_OF_NUM_GE;;
let INT_OF_NUM_GT = INT_OF_REAL_THM REAL_OF_NUM_GT;;
let INT_OF_NUM_LE = INT_OF_REAL_THM REAL_OF_NUM_LE;;
let INT_OF_NUM_LT = INT_OF_REAL_THM REAL_OF_NUM_LT;;
let INT_OF_NUM_MAX = INT_OF_REAL_THM REAL_OF_NUM_MAX;;
let INT_OF_NUM_MIN = INT_OF_REAL_THM REAL_OF_NUM_MIN;;
let INT_OF_NUM_MUL = INT_OF_REAL_THM REAL_OF_NUM_MUL;;
let INT_OF_NUM_POW = INT_OF_REAL_THM REAL_OF_NUM_POW;;
let INT_OF_NUM_SUB = INT_OF_REAL_THM REAL_OF_NUM_SUB;;
let INT_OF_NUM_SUC = INT_OF_REAL_THM REAL_OF_NUM_SUC;;
let INT_POS = INT_OF_REAL_THM REAL_POS;;
let INT_POS_NZ = INT_OF_REAL_THM REAL_POS_NZ;;
let INT_POW2_ABS = INT_OF_REAL_THM REAL_POW2_ABS;;
let INT_POW_1 = INT_OF_REAL_THM REAL_POW_1;;
let INT_POW_1_LE = INT_OF_REAL_THM REAL_POW_1_LE;;
let INT_POW_1_LT = INT_OF_REAL_THM REAL_POW_1_LT;;
let INT_POW_2 = INT_OF_REAL_THM REAL_POW_2;;
let INT_POW_ADD = INT_OF_REAL_THM REAL_POW_ADD;;
let INT_POW_EQ = INT_OF_REAL_THM REAL_POW_EQ;;
let INT_POW_EQ_0 = INT_OF_REAL_THM REAL_POW_EQ_0;;
let INT_POW_EQ_ABS = INT_OF_REAL_THM REAL_POW_EQ_ABS;;
let INT_POW_LE = INT_OF_REAL_THM REAL_POW_LE;;
let INT_POW_LE2 = INT_OF_REAL_THM REAL_POW_LE2;;
let INT_POW_LE2_ODD = INT_OF_REAL_THM REAL_POW_LE2_ODD;;
let INT_POW_LE2_REV = INT_OF_REAL_THM REAL_POW_LE2_REV;;
let INT_POW_LE_1 = INT_OF_REAL_THM REAL_POW_LE_1;;
let INT_POW_LT = INT_OF_REAL_THM REAL_POW_LT;;
let INT_POW_LT2 = INT_OF_REAL_THM REAL_POW_LT2;;
let INT_POW_LT2_REV = INT_OF_REAL_THM REAL_POW_LT2_REV;;
let INT_POW_LT_1 = INT_OF_REAL_THM REAL_POW_LT_1;;
let INT_POW_MONO = INT_OF_REAL_THM REAL_POW_MONO;;
let INT_POW_MONO_LT = INT_OF_REAL_THM REAL_POW_MONO_LT;;
let INT_POW_MUL = INT_OF_REAL_THM REAL_POW_MUL;;
let INT_POW_NEG = INT_OF_REAL_THM REAL_POW_NEG;;
let INT_POW_NZ = INT_OF_REAL_THM REAL_POW_NZ;;
let INT_POW_ONE = INT_OF_REAL_THM REAL_POW_ONE;;
let INT_POW_POW = INT_OF_REAL_THM REAL_POW_POW;;
let INT_POW_ZERO = INT_OF_REAL_THM REAL_POW_ZERO;;
let INT_RNEG_UNIQ = INT_OF_REAL_THM REAL_RNEG_UNIQ;;
let INT_SGN = INT_OF_REAL_THM real_sgn;;
let INT_SGN_0 = INT_OF_REAL_THM REAL_SGN_0;;
let INT_SGN_ABS = INT_OF_REAL_THM REAL_SGN_ABS;;
let INT_SGN_CASES = INT_OF_REAL_THM REAL_SGN_CASES;;
let INT_SGN_EQ = INT_OF_REAL_THM REAL_SGN_EQ;;
let INT_SGN_INEQS = INT_OF_REAL_THM REAL_SGN_INEQS;;
let INT_SGN_MUL = INT_OF_REAL_THM REAL_SGN_MUL;;
let INT_SGN_NEG = INT_OF_REAL_THM REAL_SGN_NEG;;
let INT_SGN_POW = INT_OF_REAL_THM REAL_SGN_POW;;
let INT_SGN_POW_2 = INT_OF_REAL_THM REAL_SGN_POW_2;;
let INT_SGN_INT_SGN = INT_OF_REAL_THM REAL_SGN_REAL_SGN;;
let INT_SOS_EQ_0 = INT_OF_REAL_THM REAL_SOS_EQ_0;;
let INT_SUB_0 = INT_OF_REAL_THM REAL_SUB_0;;
let INT_SUB_ABS = INT_OF_REAL_THM REAL_SUB_ABS;;
let INT_SUB_ADD = INT_OF_REAL_THM REAL_SUB_ADD;;
let INT_SUB_ADD2 = INT_OF_REAL_THM REAL_SUB_ADD2;;
let INT_SUB_LDISTRIB = INT_OF_REAL_THM REAL_SUB_LDISTRIB;;
let INT_SUB_LE = INT_OF_REAL_THM REAL_SUB_LE;;
let INT_SUB_LNEG = INT_OF_REAL_THM REAL_SUB_LNEG;;
let INT_SUB_LT = INT_OF_REAL_THM REAL_SUB_LT;;
let INT_SUB_LZERO = INT_OF_REAL_THM REAL_SUB_LZERO;;
let INT_SUB_NEG2 = INT_OF_REAL_THM REAL_SUB_NEG2;;
let INT_SUB_RDISTRIB = INT_OF_REAL_THM REAL_SUB_RDISTRIB;;
let INT_SUB_REFL = INT_OF_REAL_THM REAL_SUB_REFL;;
let INT_SUB_RNEG = INT_OF_REAL_THM REAL_SUB_RNEG;;
let INT_SUB_RZERO = INT_OF_REAL_THM REAL_SUB_RZERO;;
let INT_SUB_SUB = INT_OF_REAL_THM REAL_SUB_SUB;;
let INT_SUB_SUB2 = INT_OF_REAL_THM REAL_SUB_SUB2;;
let INT_SUB_TRIANGLE = INT_OF_REAL_THM REAL_SUB_TRIANGLE;;

(* ------------------------------------------------------------------------- *)
(* More useful "image" theorems.                                             *)
(* ------------------------------------------------------------------------- *)

let INT_FORALL_POS = prove
 (`!P. (!n. P(&n)) <=> (!i:int. &0 <= i ==> P(i))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC THENL
   [DISJ_CASES_THEN (CHOOSE_THEN SUBST1_TAC) (SPEC `i:int` INT_IMAGE) THEN
    ASM_REWRITE_TAC[INT_LE_RNEG; INT_ADD_LID; INT_OF_NUM_LE; LE] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[INT_NEG_0];
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[INT_OF_NUM_LE; LE_0]]);;

let INT_EXISTS_POS = prove
 (`!P. (?n. P(&n)) <=> (?i:int. &0 <= i /\ P(i))`,
  GEN_TAC THEN GEN_REWRITE_TAC I [TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; INT_FORALL_POS] THEN MESON_TAC[]);;

let INT_FORALL_ABS = prove
 (`!P. (!n. P(&n)) <=> (!x:int. P(abs x))`,
  REWRITE_TAC[INT_FORALL_POS] THEN MESON_TAC[INT_ABS_POS; INT_ABS_REFL]);;

let INT_EXISTS_ABS = prove
 (`!P. (?n. P(&n)) <=> (?x:int. P(abs x))`,
  GEN_TAC THEN GEN_REWRITE_TAC I [TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; INT_FORALL_ABS] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sometimes handy in number-theoretic applications.                         *)
(* ------------------------------------------------------------------------- *)

let INT_ABS_MUL_1 = prove
 (`!x y. (abs(x * y) = &1) <=> (abs(x) = &1) /\ (abs(y) = &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_ABS_MUL] THEN
  MP_TAC(SPEC `y:int` INT_ABS_POS) THEN SPEC_TAC(`abs(y)`,`b:int`) THEN
  MP_TAC(SPEC `x:int` INT_ABS_POS) THEN SPEC_TAC(`abs(x)`,`a:int`) THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; INT_OF_NUM_MUL; INT_OF_NUM_EQ; MULT_EQ_1]);;

let INT_WOP = prove
 (`(?x. &0 <= x /\ P x) <=>
   (?x. &0 <= x /\ P x /\ !y. &0 <= y /\ P y ==> x <= y)`,
  ONCE_REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS; INT_OF_NUM_LE] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  REWRITE_TAC[GSYM NOT_LE; CONTRAPOS_THM]);;

(* ------------------------------------------------------------------------- *)
(* A few "pseudo definitions".                                               *)
(* ------------------------------------------------------------------------- *)

let INT_POW = prove
 (`(x pow 0 = &1) /\
   (!n. x pow (SUC n) = x * x pow n)`,
  REWRITE_TAC(map INT_OF_REAL_THM (CONJUNCTS real_pow)));;

let INT_ABS = prove
 (`!x. abs(x) = if &0 <= x then x else --x`,
  GEN_TAC THEN MP_TAC(INT_OF_REAL_THM(SPEC `x:real` real_abs)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_eq]);;

let INT_GE = prove
 (`!x y. x >= y <=> y <= x`,
  REWRITE_TAC[int_ge; int_le; real_ge]);;

let INT_GT = prove
 (`!x y. x > y <=> y < x`,
  REWRITE_TAC[int_gt; int_lt; real_gt]);;

let INT_LT = prove
 (`!x y. x < y <=> ~(y <= x)`,
  REWRITE_TAC[int_lt; int_le; real_lt]);;

(* ------------------------------------------------------------------------- *)
(* Now a decision procedure for the integers.                                *)
(* ------------------------------------------------------------------------- *)

let INT_ARITH =
  let atom_CONV =
    let pth = prove
      (`(~(x <= y) <=> y + &1 <= x) /\
        (~(x < y) <=> y <= x) /\
        (~(x = y) <=> x + &1 <= y \/ y + &1 <= x) /\
        (x < y <=> x + &1 <= y)`,
       REWRITE_TAC[INT_NOT_LE; INT_NOT_LT; INT_NOT_EQ; INT_LT_DISCRETE]) in
    GEN_REWRITE_CONV I [pth]
  and bub_CONV = GEN_REWRITE_CONV TOP_SWEEP_CONV
   [int_eq; int_le; int_lt; int_ge; int_gt;
    int_of_num_th; int_neg_th; int_add_th; int_mul_th;
    int_sub_th; int_pow_th; int_abs_th; int_max_th; int_min_th] in
  let base_CONV = TRY_CONV atom_CONV THENC bub_CONV in
  let NNF_NORM_CONV = GEN_NNF_CONV false
   (base_CONV,fun t -> base_CONV t,base_CONV(mk_neg t)) in
  let init_CONV =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    GEN_REWRITE_CONV DEPTH_CONV [INT_GT; INT_GE] THENC
    NNF_CONV THENC DEPTH_BINOP_CONV `(\/)` CONDS_ELIM_CONV THENC
    NNF_NORM_CONV in
  let p_tm = `p:bool`
  and not_tm = `(~)` in
  let pth = TAUT(mk_eq(mk_neg(mk_neg p_tm),p_tm)) in
  fun tm ->
    let th0 = INST [tm,p_tm] pth
    and th1 = init_CONV (mk_neg tm) in
    let th2 = REAL_ARITH(mk_neg(rand(concl th1))) in
    EQ_MP th0 (EQ_MP (AP_TERM not_tm (SYM th1)) th2);;

let INT_ARITH_TAC = CONV_TAC(EQT_INTRO o INT_ARITH);;

let ASM_INT_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  INT_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Some pseudo-definitions.                                                  *)
(* ------------------------------------------------------------------------- *)

let INT_SUB = INT_ARITH `!x y. x - y = x + --y`;;

let INT_MAX = INT_ARITH `!x y. max x y = if x <= y then y else x`;;

let INT_MIN = INT_ARITH `!x y. min x y = if x <= y then x else y`;;

(* ------------------------------------------------------------------------- *)
(* Additional useful lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let INT_OF_NUM_EXISTS = prove
 (`!x:int. (?n. x = &n) <=> &0 <= x`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[INT_POS] THEN
  MP_TAC(ISPEC `x:int` INT_IMAGE) THEN
  REWRITE_TAC[OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_INT_ARITH_TAC);;

let INT_LE_DISCRETE = INT_ARITH `!x y:int. x <= y <=> x < y + &1`;;

let INT_LE_TRANS_LE = prove
 (`!x y:int. x <= y <=> (!z. y <= z ==> x <= z)`,
  MESON_TAC[INT_LE_TRANS; INT_LE_REFL]);;

let INT_LE_TRANS_LT = prove
 (`!x y:int. x <= y <=> (!z. y < z ==> x < z)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y + &1:int`) THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Archimedian property for the integers.                                    *)
(* ------------------------------------------------------------------------- *)

let INT_ARCH = prove
 (`!x d. ~(d = &0) ==> ?c. x < c * d`,
  SUBGOAL_THEN `!x. &0 <= x ==> ?n. x <= &n` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_FORALL_POS; INT_OF_NUM_LE] THEN MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ?n. x <= &n` ASSUME_TAC THENL
   [ASM_MESON_TAC[INT_LE_TOTAL]; ALL_TAC] THEN
  SUBGOAL_THEN `!x d. &0 < d ==> ?c. x < c * d` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[INT_LT_DISCRETE; INT_ADD_LID] THEN
    ASM_MESON_TAC[INT_POS; INT_LE_LMUL; INT_ARITH
        `x + &1 <= &n /\ &n * &1 <= &n * d ==> x + &1 <= &n * d`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x d. ~(d = &0) ==> ?c. x < c * d` ASSUME_TAC THENL
   [ASM_MESON_TAC[INT_ARITH `--x * y = x * --y`;
                  INT_ARITH `~(d = &0) ==> &0 < d \/ &0 < --d`];
    ALL_TAC] THEN
  ASM_MESON_TAC[INT_ARITH `--x * y = x * --y`;
                INT_ARITH `~(d = &0) ==> &0 < d \/ &0 < --d`]);;

(* ------------------------------------------------------------------------- *)
(* Definitions of ("Euclidean") integer division and remainder.              *)
(* ------------------------------------------------------------------------- *)

let INT_DIVMOD_EXIST_0 = prove
 (`!m n:int. ?q r. if n = &0 then q = &0 /\ r = m
                   else &0 <= r /\ r < abs(n) /\ m = q * n + r`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = &0` THEN
  ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  SUBGOAL_THEN `?r. &0 <= r /\ ?q:int. m = n * q + r` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `--m:int` o MATCH_MP INT_ARCH) THEN
    DISCH_THEN(X_CHOOSE_TAC `s:int`) THEN
    EXISTS_TAC `m + s * n:int` THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; EXISTS_TAC `--s:int` THEN INT_ARITH_TAC];
    GEN_REWRITE_TAC LAND_CONV [INT_WOP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:int` THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:int` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `r - abs n`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `if &0 <= n then q + &1 else q - &1`) THEN
    ASM_INT_ARITH_TAC]);;

parse_as_infix("div",(22,"left"));;
parse_as_infix("rem",(22,"left"));;

let INT_DIVISION_0 =  new_specification ["div"; "rem"]
  (REWRITE_RULE[SKOLEM_THM] INT_DIVMOD_EXIST_0);;

let INT_DIVISION = prove
 (`!m n. ~(n = &0)
         ==> m = m div n * n + m rem n /\ &0 <= m rem n /\ m rem n < abs n`,
  MESON_TAC[INT_DIVISION_0]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on integers. Essentially a clone of stuff for reals *)
(* in the file "calc_int.ml", except for div and rem, which are more like N. *)
(* ------------------------------------------------------------------------- *)

let INT_LE_CONV,INT_LT_CONV,INT_GE_CONV,INT_GT_CONV,INT_EQ_CONV =
  let tth =
    TAUT `(F /\ F <=> F) /\ (F /\ T <=> F) /\
          (T /\ F <=> F) /\ (T /\ T <=> T)` in
  let nth = TAUT `(~T <=> F) /\ (~F <=> T)` in
  let NUM2_EQ_CONV = BINOP_CONV NUM_EQ_CONV THENC GEN_REWRITE_CONV I [tth] in
  let NUM2_NE_CONV =
    RAND_CONV NUM2_EQ_CONV THENC
    GEN_REWRITE_CONV I [nth] in
  let [pth_le1; pth_le2a; pth_le2b; pth_le3] = (CONJUNCTS o prove)
   (`(--(&m) <= &n <=> T) /\
     (&m <= &n <=> m <= n) /\
     (--(&m) <= --(&n) <=> n <= m) /\
     (&m <= --(&n) <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[INT_LE_NEG2] THEN
    REWRITE_TAC[INT_LE_LNEG; INT_LE_RNEG] THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE; LE_0] THEN
    REWRITE_TAC[LE; ADD_EQ_0]) in
  let INT_LE_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_le1];
    GEN_REWRITE_CONV I [pth_le2a; pth_le2b] THENC NUM_LE_CONV;
    GEN_REWRITE_CONV I [pth_le3] THENC NUM2_EQ_CONV] in
  let [pth_lt1; pth_lt2a; pth_lt2b; pth_lt3] = (CONJUNCTS o prove)
   (`(&m < --(&n) <=> F) /\
     (&m < &n <=> m < n) /\
     (--(&m) < --(&n) <=> n < m) /\
     (--(&m) < &n <=> ~((m = 0) /\ (n = 0)))`,
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3;
                GSYM NOT_LE; INT_LT] THEN
    CONV_TAC TAUT) in
  let INT_LT_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_lt1];
    GEN_REWRITE_CONV I [pth_lt2a; pth_lt2b] THENC NUM_LT_CONV;
    GEN_REWRITE_CONV I [pth_lt3] THENC NUM2_NE_CONV] in
  let [pth_ge1; pth_ge2a; pth_ge2b; pth_ge3] = (CONJUNCTS o prove)
   (`(&m >= --(&n) <=> T) /\
     (&m >= &n <=> n <= m) /\
     (--(&m) >= --(&n) <=> m <= n) /\
     (--(&m) >= &n <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; INT_GE] THEN
    CONV_TAC TAUT) in
  let INT_GE_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_ge1];
    GEN_REWRITE_CONV I [pth_ge2a; pth_ge2b] THENC NUM_LE_CONV;
    GEN_REWRITE_CONV I [pth_ge3] THENC NUM2_EQ_CONV] in
  let [pth_gt1; pth_gt2a; pth_gt2b; pth_gt3] = (CONJUNCTS o prove)
   (`(--(&m) > &n <=> F) /\
     (&m > &n <=> n < m) /\
     (--(&m) > --(&n) <=> m < n) /\
     (&m > --(&n) <=> ~((m = 0) /\ (n = 0)))`,
    REWRITE_TAC[pth_lt1; pth_lt2a; pth_lt2b; pth_lt3; INT_GT] THEN
    CONV_TAC TAUT) in
  let INT_GT_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_gt1];
    GEN_REWRITE_CONV I [pth_gt2a; pth_gt2b] THENC NUM_LT_CONV;
    GEN_REWRITE_CONV I [pth_gt3] THENC NUM2_NE_CONV] in
  let [pth_eq1a; pth_eq1b; pth_eq2a; pth_eq2b] = (CONJUNCTS o prove)
   (`((&m = &n) <=> (m = n)) /\
     ((--(&m) = --(&n)) <=> (m = n)) /\
     ((--(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
     ((&m = --(&n)) <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[GSYM INT_LE_ANTISYM; GSYM LE_ANTISYM] THEN
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; LE; LE_0] THEN
    CONV_TAC TAUT) in
  let INT_EQ_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_eq1a; pth_eq1b] THENC NUM_EQ_CONV;
    GEN_REWRITE_CONV I [pth_eq2a; pth_eq2b] THENC NUM2_EQ_CONV] in
  INT_LE_CONV,INT_LT_CONV,
  INT_GE_CONV,INT_GT_CONV,INT_EQ_CONV;;

let INT_NEG_CONV =
  let pth = prove
   (`(--(&0) = &0) /\
     (--(--(&x)) = &x)`,
    REWRITE_TAC[INT_NEG_NEG; INT_NEG_0]) in
  GEN_REWRITE_CONV I [pth];;

let INT_MUL_CONV =
  let pth0 = prove
   (`(&0 * &x = &0) /\
     (&0 * --(&x) = &0) /\
     (&x * &0 = &0) /\
     (--(&x) * &0 = &0)`,
    REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO])
  and pth1,pth2 = (CONJ_PAIR o prove)
   (`((&m * &n = &(m * n)) /\
      (--(&m) * --(&n) = &(m * n))) /\
     ((--(&m) * &n = --(&(m * n))) /\
      (&m * --(&n) = --(&(m * n))))`,
    REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG] THEN
    REWRITE_TAC[INT_OF_NUM_MUL]) in
  FIRST_CONV
   [GEN_REWRITE_CONV I [pth0];
    GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_MULT_CONV;
    GEN_REWRITE_CONV I [pth2] THENC RAND_CONV(RAND_CONV NUM_MULT_CONV)];;

let INT_ADD_CONV =
  let neg_tm = `(--)` in
  let amp_tm = `&` in
  let add_tm = `(+)` in
  let dest = dest_binop `(+)` in
  let m_tm = `m:num` and n_tm = `n:num` in
  let pth0 = prove
   (`(--(&m) + &m = &0) /\
     (&m + --(&m) = &0)`,
    REWRITE_TAC[INT_ADD_LINV; INT_ADD_RINV]) in
  let [pth1; pth2; pth3; pth4; pth5; pth6] = (CONJUNCTS o prove)
   (`(--(&m) + --(&n) = --(&(m + n))) /\
     (--(&m) + &(m + n) = &n) /\
     (--(&(m + n)) + &m = --(&n)) /\
     (&(m + n) + --(&m) = &n) /\
     (&m + --(&(m + n)) = --(&n)) /\
     (&m + &n = &(m + n))`,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_NEG_ADD] THEN
    REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID] THEN
    REWRITE_TAC[INT_ADD_RINV; INT_ADD_LID] THEN
    ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
    REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID] THEN
    REWRITE_TAC[INT_ADD_RINV; INT_ADD_LID]) in
  GEN_REWRITE_CONV I [pth0] ORELSEC
  (fun tm ->
    try let l,r = dest tm in
        if rator l = neg_tm then
          if rator r = neg_tm then
            let th1 = INST [rand(rand l),m_tm; rand(rand r),n_tm] pth1 in
            let tm1 = rand(rand(rand(concl th1))) in
            let th2 = AP_TERM neg_tm (AP_TERM amp_tm (NUM_ADD_CONV tm1)) in
            TRANS th1 th2
          else
            let m = rand(rand l) and n = rand r in
            let m' = dest_numeral m and n' = dest_numeral n in
            if m' <=/ n' then
              let p = mk_numeral (n' -/ m') in
              let th1 = INST [m,m_tm; p,n_tm] pth2 in
              let th2 = NUM_ADD_CONV (rand(rand(lhand(concl th1)))) in
              let th3 = AP_TERM (rator tm) (AP_TERM amp_tm (SYM th2)) in
              TRANS th3 th1
            else
              let p = mk_numeral (m' -/ n') in
              let th1 = INST [n,m_tm; p,n_tm] pth3 in
              let th2 = NUM_ADD_CONV (rand(rand(lhand(lhand(concl th1))))) in
              let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2)) in
              let th4 = AP_THM (AP_TERM add_tm th3) (rand tm) in
              TRANS th4 th1
        else
          if rator r = neg_tm then
            let m = rand l and n = rand(rand r) in
            let m' = dest_numeral m and n' = dest_numeral n in
            if n' <=/ m' then
              let p = mk_numeral (m' -/ n') in
              let th1 = INST [n,m_tm; p,n_tm] pth4 in
              let th2 = NUM_ADD_CONV (rand(lhand(lhand(concl th1)))) in
              let th3 = AP_TERM add_tm (AP_TERM amp_tm (SYM th2)) in
              let th4 = AP_THM th3 (rand tm) in
              TRANS th4 th1
            else
             let p = mk_numeral (n' -/ m') in
             let th1 = INST [m,m_tm; p,n_tm] pth5 in
             let th2 = NUM_ADD_CONV (rand(rand(rand(lhand(concl th1))))) in
             let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2)) in
             let th4 = AP_TERM (rator tm) th3 in
             TRANS th4 th1
          else
            let th1 = INST [rand l,m_tm; rand r,n_tm] pth6 in
            let tm1 = rand(rand(concl th1)) in
            let th2 = AP_TERM amp_tm (NUM_ADD_CONV tm1) in
            TRANS th1 th2
    with Failure _ -> failwith "INT_ADD_CONV");;

let INT_SUB_CONV =
  GEN_REWRITE_CONV I [INT_SUB] THENC
  TRY_CONV(RAND_CONV INT_NEG_CONV) THENC
  INT_ADD_CONV;;

let INT_POW_CONV =
  let pth1,pth2 = (CONJ_PAIR o prove)
   (`(&x pow n = &(x EXP n)) /\
     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))`,
    REWRITE_TAC[INT_OF_NUM_POW; INT_POW_NEG]) in
  let tth = prove
   (`((if T then x:int else y) = x) /\ ((if F then x:int else y) = y)`,
    REWRITE_TAC[]) in
  let neg_tm = `(--)` in
  (GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_EXP_CONV) ORELSEC
  (GEN_REWRITE_CONV I [pth2] THENC
   RATOR_CONV(RATOR_CONV(RAND_CONV NUM_EVEN_CONV)) THENC
   GEN_REWRITE_CONV I [tth] THENC
   (fun tm -> if rator tm = neg_tm then RAND_CONV(RAND_CONV NUM_EXP_CONV) tm
              else RAND_CONV NUM_EXP_CONV  tm));;

let INT_ABS_CONV =
  let pth = prove
   (`(abs(--(&x)) = &x) /\
     (abs(&x) = &x)`,
    REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM]) in
  GEN_REWRITE_CONV I [pth];;

let INT_MAX_CONV =
  REWR_CONV INT_MAX THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV INT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let INT_MIN_CONV =
  REWR_CONV INT_MIN THENC
  RATOR_CONV(RATOR_CONV(RAND_CONV INT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer.                                               *)
(* ------------------------------------------------------------------------- *)

let INT_POLY_CONV =
  let sth = prove
   (`(!x y z. x + (y + z) = (x + y) + z) /\
     (!x y. x + y = y + x) /\
     (!x. &0 + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z) /\
     (!x y. x * y = y * x) /\
     (!x. &1 * x = x) /\
     (!x. &0 * x = &0) /\
     (!x y z. x * (y + z) = x * y + x * z) /\
     (!x. x pow 0 = &1) /\
     (!x n. x pow (SUC n) = x * x pow n)`,
    REWRITE_TAC[INT_POW] THEN INT_ARITH_TAC)
  and rth = prove
   (`(!x. --x = --(&1) * x) /\
     (!x y. x - y = x + --(&1) * y)`,
    INT_ARITH_TAC)
  and is_semiring_constant = is_intconst
  and SEMIRING_ADD_CONV = INT_ADD_CONV
  and SEMIRING_MUL_CONV = INT_MUL_CONV
  and SEMIRING_POW_CONV = INT_POW_CONV in
  let _,_,_,_,_,INT_POLY_CONV =
    SEMIRING_NORMALIZERS_CONV sth rth
     (is_semiring_constant,
      SEMIRING_ADD_CONV,SEMIRING_MUL_CONV,SEMIRING_POW_CONV)
     (<) in
  INT_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Instantiate the ring and ideal procedures.                                *)
(* ------------------------------------------------------------------------- *)

let INT_RING,int_ideal_cofactors =
  let INT_INTEGRAL = prove
   (`(!x. &0 * x = &0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))`,
    REWRITE_TAC[MULT_CLAUSES; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ;
                GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN
    REWRITE_TAC[GSYM INT_ENTIRE] THEN INT_ARITH_TAC)
  and int_ty = `:int` in
  let pure,ideal =
  RING_AND_IDEAL_CONV
      (dest_intconst,mk_intconst,INT_EQ_CONV,
       `(--):int->int`,`(+):int->int->int`,`(-):int->int->int`,
       genvar bool_ty,`(*):int->int->int`,genvar bool_ty,
       `(pow):int->num->int`,
       INT_INTEGRAL,TRUTH,INT_POLY_CONV) in
  pure,
  (fun tms tm -> if forall (fun t -> type_of t = int_ty) (tm::tms)
                 then ideal tms tm
                 else failwith
                  "int_ideal_cofactors: not all terms have type :int");;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations also on div and rem, hence the whole lot.           *)
(* ------------------------------------------------------------------------- *)

let INT_DIVMOD_UNIQ = prove
 (`!m n q r:int. m = q * n + r /\ &0 <= r /\ r < abs n
                 ==> m div n = q /\ m rem n = r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n = &0)` MP_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o SPEC `m:int` o MATCH_MP INT_DIVISION) THEN
  ASM_CASES_TAC `m div n = q` THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING; ALL_TAC] THEN
  SUBGOAL_THEN `abs(m rem n - r) < abs n` MP_TAC THENL
   [ASM_INT_ARITH_TAC; MATCH_MP_TAC(TAUT `~p ==> p ==> q`)] THEN
  MATCH_MP_TAC(INT_ARITH
   `&1 * abs n <= abs(q - m div n) * abs n /\
    abs(m rem n - r) = abs((q - m div n) * n)
    ==> ~(abs(m rem n - r) < abs n)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_RMUL THEN ASM_INT_ARITH_TAC;
    AP_TERM_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING]);;

let INT_DIV_CONV,INT_REM_CONV =
  let pth = prove
   (`q * n + r = m ==> &0 <= r ==> r < abs n ==> m div n = q /\ m rem n = r`,
    MESON_TAC[INT_DIVMOD_UNIQ])
  and m = `m:int` and n = `n:int` and q = `q:int` and r = `r:int`
  and dtm = `(div)` and mtm = `(rem)` in
  let emod_num x y =
    let r = mod_num x y in
    if r </ Int 0 then r +/ abs_num y else r in
  let equo_num x y = quo_num (x -/ emod_num x y) y in
  let INT_DIVMOD_CONV x y =
    let k = equo_num x y
    and l = emod_num x y in
    let th0 = INST [mk_intconst x,m; mk_intconst y,n;
                    mk_intconst k,q; mk_intconst l,r] pth in
    let tm0 = lhand(lhand(concl th0)) in
    let th1 = (LAND_CONV INT_MUL_CONV THENC INT_ADD_CONV) tm0 in
    let th2 = MP th0 th1 in
    let tm2 = lhand(concl th2) in
    let th3 = MP th2 (EQT_ELIM(INT_LE_CONV tm2)) in
    let tm3 = lhand(concl th3) in
    MP th3 (EQT_ELIM((RAND_CONV INT_ABS_CONV THENC INT_LT_CONV) tm3)) in
  (fun tm -> try let l,r = dest_binop dtm tm in
                 CONJUNCT1(INT_DIVMOD_CONV (dest_intconst l) (dest_intconst r))
             with Failure _ -> failwith "INT_DIV_CONV"),
  (fun tm -> try let l,r = dest_binop mtm tm in
                 CONJUNCT2(INT_DIVMOD_CONV (dest_intconst l) (dest_intconst r))
             with Failure _ -> failwith "INT_MOD_CONV");;

let INT_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv)
    [`x <= y`,INT_LE_CONV;
     `x < y`,INT_LT_CONV;
     `x >= y`,INT_GE_CONV;
     `x > y`,INT_GT_CONV;
     `x:int = y`,INT_EQ_CONV;
     `--x`,CHANGED_CONV INT_NEG_CONV;
     `abs(x)`,INT_ABS_CONV;
     `x + y`,INT_ADD_CONV;
     `x - y`,INT_SUB_CONV;
     `x * y`,INT_MUL_CONV;
     `x div y`,INT_DIV_CONV;
     `x rem y`,INT_REM_CONV;
     `x pow n`,INT_POW_CONV;
     `max x y`,INT_MAX_CONV;
     `min x y`,INT_MIN_CONV]
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let INT_REDUCE_CONV = DEPTH_CONV INT_RED_CONV;;

(* ------------------------------------------------------------------------- *)
(* Set up overloading so we can use same symbols for N, Z and even R.        *)
(* ------------------------------------------------------------------------- *)

make_overloadable "divides" `:A->A->bool`;;
make_overloadable "mod" `:A->A->A->bool`;;
make_overloadable "coprime" `:A#A->bool`;;
make_overloadable "gcd" `:A#A->A`;;

(* ------------------------------------------------------------------------- *)
(* The general notion of congruence: just syntax for equivalence relation.   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("==",(10,"right"));;

let cong = new_definition
  `(x == y) (rel:A->A->bool) <=> rel x y`;;

(* ------------------------------------------------------------------------- *)
(* Get real moduli defined and out of the way first.                         *)
(* ------------------------------------------------------------------------- *)

let real_mod = new_definition
  `real_mod n (x:real) y = ?q. integer q /\ x - y = q * n`;;

overload_interface ("mod",`real_mod`);;

(* ------------------------------------------------------------------------- *)
(* Integer divisibility.                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("divides",(12,"right"));;
overload_interface("divides",`int_divides:int->int->bool`);;

let int_divides = new_definition
  `a divides b <=> ?x. b = a * x`;;

(* ------------------------------------------------------------------------- *)
(* Integer congruences.                                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "mod";;
overload_interface ("mod",`int_mod:int->int->int->bool`);;

let int_mod = new_definition
  `(mod n) x y = n divides (x - y)`;;

let int_congruent = prove
 (`!x y n. (x == y) (mod n) <=> ?d. x - y = n * d`,
  REWRITE_TAC[int_mod; cong; int_divides]);;

(* ------------------------------------------------------------------------- *)
(* Integer coprimality.                                                      *)
(* ------------------------------------------------------------------------- *)

overload_interface("coprime",`int_coprime:int#int->bool`);;

let int_coprime = new_definition
 `!a b. coprime(a,b) <=> ?x y. a * x + b * y = &1`;;

(* ------------------------------------------------------------------------- *)
(* A tactic for simple divisibility/congruence/coprimality goals.            *)
(* ------------------------------------------------------------------------- *)

let INTEGER_TAC =
  let int_ty = `:int` in
  let INT_POLYEQ_CONV =
    GEN_REWRITE_CONV I [GSYM INT_SUB_0] THENC LAND_CONV INT_POLY_CONV in
  let ISOLATE_VARIABLE =
    let pth = INT_ARITH `!a x. a = &0 <=> x = x + a` in
    let is_defined v t =
      let mons = striplist(dest_binary "int_add") t in
      mem v mons & forall (fun m -> v = m or not(free_in v m)) mons in
    fun vars tm ->
      let th = INT_POLYEQ_CONV tm
      and th' = (SYM_CONV THENC INT_POLYEQ_CONV) tm in
      let v,th1 =
          try find (fun v -> is_defined v (lhand(rand(concl th)))) vars,th'
          with Failure _ ->
              find (fun v -> is_defined v (lhand(rand(concl th')))) vars,th in
      let th2 = TRANS th1 (SPECL [lhs(rand(concl th1)); v] pth) in
      CONV_RULE(RAND_CONV(RAND_CONV INT_POLY_CONV)) th2 in
  let UNWIND_POLYS_CONV tm =
    let vars,bod = strip_exists tm in
    let cjs = conjuncts bod in
    let th1 = tryfind (ISOLATE_VARIABLE vars) cjs in
    let eq = lhand(concl th1) in
    let bod' = list_mk_conj(eq::(subtract cjs [eq])) in
    let th2 = CONJ_ACI_RULE(mk_eq(bod,bod')) in
    let th3 = TRANS th2 (MK_CONJ th1 (REFL(rand(rand(concl th2))))) in
    let v = lhs(lhand(rand(concl th3))) in
    let vars' = (subtract vars [v]) @ [v] in
    let th4 = CONV_RULE(RAND_CONV(REWR_CONV UNWIND_THM2)) (MK_EXISTS v th3) in
    let IMP_RULE v v' =
     DISCH_ALL(itlist SIMPLE_CHOOSE v (itlist SIMPLE_EXISTS v' (ASSUME bod))) in
    let th5 = IMP_ANTISYM_RULE (IMP_RULE vars vars') (IMP_RULE vars' vars) in
    TRANS th5 (itlist MK_EXISTS (subtract vars [v]) th4) in
  let zero_tm = `&0` and one_tm = `&1` in
  let isolate_monomials =
    let mul_tm = `(int_mul)` and add_tm = `(int_add)`
    and neg_tm = `(int_neg)` in
    let dest_mul = dest_binop mul_tm
    and dest_add = dest_binop add_tm
    and mk_mul = mk_binop mul_tm
    and mk_add = mk_binop add_tm in
    let scrub_var v m =
      let ps = striplist dest_mul m in
      let ps' = subtract ps [v] in
      if ps' = [] then one_tm else end_itlist mk_mul ps' in
    let find_multipliers v mons =
      let mons1 = filter (fun m -> free_in v m) mons in
      let mons2 = map (scrub_var v) mons1 in
      if mons2 = [] then zero_tm else end_itlist mk_add mons2 in
    fun vars tm ->
      let cmons,vmons =
         partition (fun m -> intersect (frees m) vars = [])
                   (striplist dest_add tm) in
      let cofactors = map (fun v -> find_multipliers v vmons) vars
      and cnc = if cmons = [] then zero_tm
                else mk_comb(neg_tm,end_itlist mk_add cmons) in
      cofactors,cnc in
  let isolate_variables evs ps eq =
    let vars = filter (fun v -> vfree_in v eq) evs in
    let qs,p = isolate_monomials vars eq in
    let rs = filter (fun t -> type_of t = int_ty) (qs @ ps) in
    let rs = int_ideal_cofactors rs p in
    eq,zip (fst(chop_list(length qs) rs)) vars in
  let subst_in_poly i p = rhs(concl(INT_POLY_CONV (vsubst i p))) in
  let rec solve_idealism evs ps eqs =
    if evs = [] then [] else
    let eq,cfs = tryfind (isolate_variables evs ps) eqs in
    let evs' = subtract evs (map snd cfs)
    and eqs' = map (subst_in_poly cfs) (subtract eqs [eq]) in
    cfs @ solve_idealism evs' ps eqs' in
  let rec GENVAR_EXISTS_CONV tm =
    if not(is_exists tm) then REFL tm else
    let ev,bod = dest_exists tm in
    let gv = genvar(type_of ev) in
    (GEN_ALPHA_CONV gv THENC BINDER_CONV GENVAR_EXISTS_CONV) tm in
  let EXISTS_POLY_TAC (asl,w as gl) =
    let evs,bod = strip_exists w
    and ps = mapfilter (check (fun t -> type_of t = int_ty) o
                        lhs o concl o snd) asl in
    let cfs = solve_idealism evs ps (map lhs (conjuncts bod)) in
    (MAP_EVERY EXISTS_TAC(map (fun v -> rev_assocd v cfs zero_tm) evs) THEN
     REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING) gl in
  let SCRUB_NEQ_TAC = MATCH_MP_TAC o MATCH_MP (MESON[]
    `~(x = y) ==> x = y \/ p ==> p`) in
  REWRITE_TAC[int_coprime; int_congruent; int_divides] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
              LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM] THEN
  CONV_TAC(REPEATC UNWIND_POLYS_CONV) THEN
  REPEAT(FIRST_X_ASSUM SCRUB_NEQ_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
              LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN
  REWRITE_TAC[GSYM INT_ENTIRE;
              TAUT `a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN CONV_TAC GENVAR_EXISTS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN EXISTS_POLY_TAC;;

let INTEGER_RULE tm = prove(tm,INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existence of integer gcd, and the Bezout identity.                        *)
(* ------------------------------------------------------------------------- *)

let WF_INT_MEASURE = prove
 (`!P m. (!x. &0 <= m(x)) /\ (!x. (!y. m(y) < m(x) ==> P(y)) ==> P(x))
         ==> !x:A. P(x)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `!n x:A. m(x) = &n ==> P(x)` MP_TAC THENL
   [MATCH_MP_TAC num_WF; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; INT_FORALL_POS] THEN ASM_MESON_TAC[]);;

let WF_INT_MEASURE_2 = prove
 (`!P m. (!x y. &0 <= m x y) /\
         (!x y. (!x' y'. m x' y' < m x y ==> P x' y') ==> P x y)
         ==> !x:A y:B. P x y`,
  REWRITE_TAC[FORALL_UNCURRY; GSYM FORALL_PAIR_THM; WF_INT_MEASURE]);;

let INT_GCD_EXISTS = prove
 (`!a b. ?d. d divides a /\ d divides b /\ ?x y. d = a * x + b * y`,
  let INT_GCD_EXISTS_CASES = INT_ARITH
   `(a = &0 \/ b = &0) \/
    abs(a - b) + abs b < abs a + abs b \/ abs(a + b) + abs b < abs a + abs b \/
    abs a + abs(b - a) < abs a + abs b \/ abs a + abs(b + a) < abs a + abs b` in
  MATCH_MP_TAC WF_INT_MEASURE_2 THEN EXISTS_TAC `\x y. abs(x) + abs(y)` THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_THEN MP_TAC INT_GCD_EXISTS_CASES THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[INTEGER_RULE `d divides &0`] THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID; INT_ADD_RID] THEN
    MESON_TAC[INTEGER_RULE `d divides d`; INT_MUL_RID];
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (ANTE_RES_THEN MP_TAC)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN INTEGER_TAC]);;

let INT_GCD_EXISTS_POS = prove
 (`!a b. ?d. &0 <= d /\ d divides a /\ d divides b /\ ?x y. d = a * x + b * y`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_TAC `d:int` (SPECL [`a:int`; `b:int`] INT_GCD_EXISTS) THEN
  DISJ_CASES_TAC(SPEC `d:int` INT_LE_NEGTOTAL) THEN
  ASM_MESON_TAC[INTEGER_RULE `(--d) divides x <=> d divides x`;
                INT_ARITH `a * --x + b * --y = --(a * x + b * y)`]);;

(* ------------------------------------------------------------------------- *)
(* Hence define (positive) gcd function; add elimination to INTEGER_TAC.      *)
(* ------------------------------------------------------------------------- *)

overload_interface("gcd",`int_gcd:int#int->int`);;

let int_gcd = new_specification ["int_gcd"]
 (REWRITE_RULE[EXISTS_UNCURRY; SKOLEM_THM] INT_GCD_EXISTS_POS);;

let INTEGER_TAC =
  let GCD_ELIM_TAC =
    let gcd_tm = `gcd` in
    let dest_gcd tm =
      let l,r = dest_comb tm in
      if l = gcd_tm then dest_pair r else failwith "dest_gcd" in
    REPEAT GEN_TAC THEN
    W(fun (asl,w) ->
          let gts = find_terms (can dest_gcd) w in
          let ths = map
           (fun tm -> let a,b = dest_gcd tm in SPECL [a;b] int_gcd) gts in
          MAP_EVERY MP_TAC ths THEN
          MAP_EVERY SPEC_TAC (zip gts (map (genvar o type_of) gts))) in
  REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN GCD_ELIM_TAC THEN INTEGER_TAC;;

let INTEGER_RULE tm = prove(tm,INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Mapping from nonnegative integers back to natural numbers.                *)
(* ------------------------------------------------------------------------- *)

let num_of_int = new_definition
  `num_of_int x = @n. &n = x`;;

let NUM_OF_INT_OF_NUM = prove
 (`!n. num_of_int(&n) = n`,
  REWRITE_TAC[num_of_int; INT_OF_NUM_EQ; SELECT_UNIQUE]);;

let INT_OF_NUM_OF_INT = prove
 (`!x. &0 <= x ==> &(num_of_int x) = x`,
  REWRITE_TAC[GSYM INT_FORALL_POS; num_of_int] THEN
  GEN_TAC THEN CONV_TAC SELECT_CONV THEN MESON_TAC[]);;

let NUM_OF_INT = prove
 (`!x. &0 <= x <=> (&(num_of_int x) = x)`,
  MESON_TAC[INT_OF_NUM_OF_INT; INT_POS]);;

(* ------------------------------------------------------------------------- *)
(* Now define similar notions over the natural numbers.                      *)
(* ------------------------------------------------------------------------- *)

overload_interface("divides",`num_divides:num->num->bool`);;
overload_interface ("mod",`num_mod:num->num->num->bool`);;
overload_interface("coprime",`num_coprime:num#num->bool`);;
overload_interface("gcd",`num_gcd:num#num->num`);;

let num_divides = new_definition
 `a divides b <=> &a divides &b`;;

let num_mod = new_definition
  `(mod n) x y <=> (mod &n) (&x) (&y)`;;

let num_congruent = prove
 (`!x y n. (x == y) (mod n) <=> (&x == &y) (mod &n)`,
  REWRITE_TAC[cong; num_mod]);;

let num_coprime = new_definition
 `coprime(a,b) <=> coprime(&a,&b)`;;

let num_gcd = new_definition
 `gcd(a,b) = num_of_int(gcd(&a,&b))`;;

(* ------------------------------------------------------------------------- *)
(* Map an assertion over N to an integer equivalent.                         *)
(* To make this work nicely, all variables of type num should be quantified. *)
(* ------------------------------------------------------------------------- *)

let NUM_TO_INT_CONV =
  let pth_relativize = prove
   (`((!n. P(&n)) <=> (!i. ~(&0 <= i) \/ P i)) /\
     ((?n. P(&n)) <=> (?i. &0 <= i /\ P i))`,
    REWRITE_TAC[INT_EXISTS_POS; INT_FORALL_POS] THEN MESON_TAC[]) in
  let relation_conv = (GEN_REWRITE_CONV TOP_SWEEP_CONV o map GSYM)
   [INT_OF_NUM_EQ; INT_OF_NUM_LE; INT_OF_NUM_LT; INT_OF_NUM_GE; INT_OF_NUM_GT;
    INT_OF_NUM_SUC; INT_OF_NUM_ADD; INT_OF_NUM_MUL; INT_OF_NUM_POW]
  and quantifier_conv = GEN_REWRITE_CONV DEPTH_CONV [pth_relativize] in
  NUM_SIMPLIFY_CONV THENC relation_conv THENC quantifier_conv;;

(* ------------------------------------------------------------------------- *)
(* Linear decision procedure for the naturals at last!                       *)
(* ------------------------------------------------------------------------- *)

let ARITH_RULE =
  let init_conv =
    NUM_SIMPLIFY_CONV THENC
    GEN_REWRITE_CONV DEPTH_CONV [ADD1] THENC
    PROP_ATOM_CONV (BINOP_CONV NUM_NORMALIZE_CONV) THENC
    PRENEX_CONV THENC
    (GEN_REWRITE_CONV TOP_SWEEP_CONV o map GSYM)
      [INT_OF_NUM_EQ; INT_OF_NUM_LE; INT_OF_NUM_LT; INT_OF_NUM_GE;
       INT_OF_NUM_GT; INT_OF_NUM_ADD; SPEC `NUMERAL k` INT_OF_NUM_MUL;
       INT_OF_NUM_MAX; INT_OF_NUM_MIN]
  and is_numimage t =
    match t with
      Comb(Const("int_of_num",_),n) when not(is_numeral n) -> true
    | _ -> false in
  fun tm ->
    let th1 = init_conv tm in
    let tm1 = rand(concl th1) in
    let avs,bod = strip_forall tm1 in
    let nim = setify(find_terms is_numimage bod) in
    let gvs = map (genvar o type_of) nim in
    let pths = map (fun v -> SPEC (rand v) INT_POS) nim in
    let ibod = itlist (curry mk_imp o concl) pths bod in
    let gbod = subst (zip gvs nim) ibod in
    let th2 = INST (zip nim gvs) (INT_ARITH gbod) in
    let th3 = GENL avs (rev_itlist (C MP) pths th2) in
    EQ_MP (SYM th1) th3;;

let ARITH_TAC = CONV_TAC(EQT_INTRO o ARITH_RULE);;

let ASM_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Also a similar divisibility procedure for natural numbers.                *)
(* ------------------------------------------------------------------------- *)

let NUM_GCD = prove
 (`!a b. &(gcd(a,b)) = gcd(&a,&b)`,
  REWRITE_TAC[num_gcd; GSYM NUM_OF_INT; int_gcd]);;

let NUMBER_TAC =
  let pth_relativize = prove
   (`((!n. P(&n)) <=> (!i. &0 <= i ==> P i)) /\
     ((?n. P(&n)) <=> (?i. &0 <= i /\ P i))`,
    GEN_REWRITE_TAC RAND_CONV [TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
    REWRITE_TAC[NOT_EXISTS_THM; INT_FORALL_POS] THEN MESON_TAC[]) in
  let relation_conv =
   GEN_REWRITE_CONV TOP_SWEEP_CONV
    (num_divides::num_congruent::num_coprime::NUM_GCD::(map GSYM
    [INT_OF_NUM_EQ; INT_OF_NUM_LE; INT_OF_NUM_LT; INT_OF_NUM_GE; INT_OF_NUM_GT;
     INT_OF_NUM_SUC; INT_OF_NUM_ADD; INT_OF_NUM_MUL; INT_OF_NUM_POW]))
  and quantifier_conv = GEN_REWRITE_CONV DEPTH_CONV [pth_relativize] in
  W(fun (_,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
  CONV_TAC(relation_conv THENC quantifier_conv) THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN
  INTEGER_TAC;;

let NUMBER_RULE tm = prove(tm,NUMBER_TAC);;

let divides = prove
 (`a divides b <=> ?x. b = a * x`,
  EQ_TAC THENL [REWRITE_TAC[num_divides; int_divides]; NUMBER_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:int`) THEN EXISTS_TAC `num_of_int(abs x)` THEN
  SIMP_TAC[GSYM INT_OF_NUM_EQ;
           INT_ARITH `&m:int = &n <=> abs(&m :int) = abs(&n)`] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_MUL; INT_ABS_MUL] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_ABS_ABS]);;

let DIVIDES_LE = prove
 (`!m n. m divides n ==> m <= n \/ n = 0`,
  SUBGOAL_THEN `!m n. m <= m * n \/ m * n = 0`
    (fun th -> MESON_TAC[divides; th]) THEN
  REWRITE_TAC[LE_MULT_LCANCEL; MULT_EQ_0; ARITH_RULE
   `m <= m * n <=> m * 1 <= m * n`] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Make sure we give priority to N.                                          *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;
