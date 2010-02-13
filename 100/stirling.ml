(* ========================================================================= *)
(* Stirling's approximation.                                                 *)
(* ========================================================================= *)

needs "Library/analysis.ml";;
needs "Library/transc.ml";;

override_interface("-->",`(tends_num_real)`);;

(* ------------------------------------------------------------------------- *)
(* This is a handy induction for Wallis's product below.                     *)
(* ------------------------------------------------------------------------- *)

let ODDEVEN_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* A particular limit we need below.                                         *)
(* ------------------------------------------------------------------------- *)

let LN_LIM_BOUND = prove
 (`!n. ~(n = 0) ==> abs(&n * ln(&1 + &1 / &n) - &1) <= &1 / (&2 * &n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&1 / &n`; `2`] MCLAURIN_LN_POS) THEN
  ASM_SIMP_TAC[SUM_2; REAL_LT_DIV; REAL_OF_NUM_LT; LT_NZ; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_POW_1; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
              REAL_NEG_NEG; REAL_MUL_LID; REAL_INV_1; REAL_POW_NEG;
              REAL_POW_ONE; ARITH; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
   `~(x = &0) ==> x * (inv(x) + a) - &1 = x * a`] THEN
  REWRITE_TAC[REAL_ARITH `n * --((i * i) * a) = --((n * i) * a * i)`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL] THEN
  ONCE_REWRITE_TAC[REAL_INV_MUL] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_POS] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
  UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC);;

let LN_LIM_LEMMA = prove
 (`(\n. &n * ln(&1 + &1 / &n)) --> &1`,
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
   [REAL_ARITH `a = (a - &1) + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_LE_0 THEN EXISTS_TAC `\n. &1 / &n` THEN
  REWRITE_TAC[SEQ_HARMONIC] THEN
  EXISTS_TAC `1` THEN REWRITE_TAC[ARITH_RULE `n >= 1 <=> ~(n = 0)`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 / (&2 * &n)` THEN ASM_SIMP_TAC[LN_LIM_BOUND] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `~(n = 0)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemma for proving inequality via derivative and limit at infinity.        *)
(* ------------------------------------------------------------------------- *)

let POSITIVE_DIFF_LEMMA = prove
 (`!f f'. (!x. &0 < x ==> (f diffl f'(x)) x /\ f'(x) < &0) /\
          (\n. f(&n)) --> &0
          ==> !n. ~(n = 0) ==> &0 < f(&n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m p. n <= m /\ m < p ==> (f:real->real)(&p) < f(&m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `&m`; `&p`] MVT_ALT) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[LT_NZ; LTE_TRANS; REAL_OF_NUM_LT; REAL_LTE_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < z * --y ==> z * y + a < a`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_ARITH `&0 < --x <=> x < &0`] THEN
    ASM_MESON_TAC[LT_NZ; LTE_TRANS; REAL_OF_NUM_LT; REAL_LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `f(&(n + 1)) < &0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `n + 1`]) THEN ANTS_TAC THENL
     [ARITH_TAC; UNDISCH_TAC `f(&n) <= &0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SEQ]) THEN
  DISCH_THEN(MP_TAC o SPEC `--f(&(n + 1))`) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ARITH `&0 < --x <=> x < &0`] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (MP_TAC o SPEC `n + p + 2`)) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y < &0 /\ z < y ==> abs(z) < --y ==> F`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary definition.                                                     *)
(* ------------------------------------------------------------------------- *)

let stirling = new_definition
 `stirling n = ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n)`;;

(* ------------------------------------------------------------------------- *)
(* This difference is a decreasing sequence.                                 *)
(* ------------------------------------------------------------------------- *)

let STIRLING_DIFF = prove
 (`!n. ~(n = 0)
       ==> stirling(n) - stirling(n + 1) =
           (&n + &1 / &2) * ln((&n + &1) / &n) - &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stirling] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(f' - f) + x = (nl' - nl) /\ n' = n + &1
    ==> (f - (nl - n)) - (f' - (nl' - n')) = x - &1`) THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REWRITE_RULE[ADD1] FACT; GSYM REAL_OF_NUM_MUL] THEN
  SIMP_TAC[LN_MUL; FACT_LT; ADD_EQ_0; ARITH; LT_NZ; REAL_OF_NUM_LT] THEN
  ASM_SIMP_TAC[LN_DIV; REAL_OF_NUM_LT; ADD_EQ_0; ARITH; LT_NZ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let STIRLING_DELTA_DERIV = prove
 (`!x. &0 < x
       ==> ((\x. ln ((x + &1) / x) - &1 / (x + &1 / &2)) diffl
            (-- &1 / (x * (x + &1) * (&2 * x + &1) pow 2))) x`,
  GEN_TAC THEN DISCH_TAC THEN
  W(fun (asl,w) -> MP_TAC(SPEC(rand w) (DIFF_CONV(lhand(rator w))))) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_DIV) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let STIRLING_DELTA_LIMIT = prove
 (`(\n. ln ((&n + &1) / &n) - &1 / (&n + &1 / &2)) --> &0`,
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
  MATCH_MP_TAC SEQ_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SEQ_LE_0 THEN
  EXISTS_TAC `\n. &1 / &n` THEN REWRITE_TAC[SEQ_HARMONIC] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GE; GSYM REAL_OF_NUM_LE] THEN
  DISCH_TAC THEN MATCH_MP_TAC
   (REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`)
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC LN_POS THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_FIELD `&1 <= x ==> (x + &1) / x = &1 + &1 / x`] THEN
    MATCH_MP_TAC LN_LE THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS];
    MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;

let STIRLING_DECREASES = prove
 (`!n. ~(n = 0) ==> stirling(n + 1) < stirling(n)`,
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN SIMP_TAC[STIRLING_DIFF] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1 / &2`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  MATCH_MP_TAC POSITIVE_DIFF_LEMMA THEN
  EXISTS_TAC `\x. -- &1 / (x * (x + &1) * (&2 * x + &1) pow 2)` THEN
  SIMP_TAC[STIRLING_DELTA_DERIV; STIRLING_DELTA_LIMIT] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `--x < &0 <=> &0 < x`; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* However a slight tweak gives an *increasing* sequence.                    *)
(* ------------------------------------------------------------------------- *)

let OTHER_DERIV_LEMMA = prove
 (`!x. &0 < x
       ==> ((\x. &1 / (&12 * x * (x + &1) * (x + &1 / &2))) diffl
            --(&3 * x pow 2 + &3 * x + &1 / &2) /
              (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)) x`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC(SPEC(rand w) (DIFF_CONV(lhand(rator w))))) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_ENTIRE] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let STIRLING_INCREASES = prove
 (`!n. ~(n = 0)
       ==> stirling(n + 1) - &1 / (&12 * (&(n + 1)))
           > stirling(n) - &1 / (&12 * &n)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `a - b > c - d <=> c - a < d - b`] THEN
  SIMP_TAC[REAL_FIELD
    `~(&n = &0) ==> &1 / (&12 * &n) - &1 / (&12 * (&n + &1)) =
                    &1 / (&12 * &n * (&n + &1))`] THEN
  SIMP_TAC[REAL_OF_NUM_EQ; STIRLING_DIFF] THEN
  REWRITE_TAC[REAL_ARITH `a * b - &1 < c <=> b * a < c + &1`] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &n + &1 / &2`] THEN
  REWRITE_TAC[REAL_ARITH `(&1 / x + &1) / y = &1 / x / y + &1 / y`] THEN
  REWRITE_TAC[REAL_ARITH `a < b + c <=> &0 < b - (a - c)`] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC POSITIVE_DIFF_LEMMA THEN
  EXISTS_TAC `\x. &1 / (x * (x + &1) * (&2 * x + &1) pow 2) -
                  (&3 * x pow 2 + &3 * x + &1 / &2) /
                  (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
    MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC[STIRLING_DELTA_LIMIT] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_FIELD
     `inv(&12) * x * y * inv(&n + inv(&2)) = x * y * inv(&12 * &n + &6)`] THEN
    GEN_REWRITE_TAC RAND_CONV [SYM(REAL_RAT_REDUCE_CONV `&0 * &0 * &0`)] THEN
    REPEAT(MATCH_MP_TAC SEQ_MUL THEN CONJ_TAC) THEN
    MP_TAC(SPEC `&1` SEQ_HARMONIC) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUBSEQ) THENL
     [DISCH_THEN(MP_TAC o SPECL [`1`; `1`]);
      DISCH_THEN(MP_TAC o SPECL [`12`; `6`])] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; ARITH; MULT_CLAUSES]] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV
     [REAL_ARITH `&1 / x - y / z = --y / z - -- &1 / x`] THEN
    MATCH_MP_TAC DIFF_SUB THEN
    ASM_SIMP_TAC[STIRLING_DELTA_DERIV; OTHER_DERIV_LEMMA];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a - b < &0 <=> a < b`] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; REAL_FIELD
   `&0 < x
    ==> &1 / (x * (x + &1) * (&2 * x + &1) pow 2) =
        (&3 * x * (x + &1)) /
        (&12 * (x * (x + &1) * (x + &1 / &2)) *
               (x * (x + &1) * (x + &1 / &2)))`] THEN
  ONCE_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence it converges to *something*.                                        *)
(* ------------------------------------------------------------------------- *)

let STIRLING_UPPERBOUND = prove
 (`!n. stirling(SUC n) <= &1`,
  INDUCT_TAC THENL
   [REWRITE_TAC[stirling] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = SUC n + 1`] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC STIRLING_DECREASES THEN
  ARITH_TAC);;

let STIRLING_LOWERBOUND = prove
 (`!n. -- &1 <= stirling(SUC n)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n) - &1 / (&12 * &(SUC n))` THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_POS]] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[stirling] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n) - &1 / (&12 * &(SUC n))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = SUC n + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `b > a ==> a <= b`) THEN
  MATCH_MP_TAC STIRLING_INCREASES THEN ARITH_TAC);;

let STIRLING_MONO = prove
 (`!m n. ~(m = 0) /\ m <= n ==> stirling n <= stirling m`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `stirling(m + d)` THEN
  ASM_SIMP_TAC[ADD1; REAL_LT_IMP_LE; STIRLING_DECREASES; ADD_EQ_0]);;

let STIRLING_CONVERGES = prove
 (`?c. stirling --> c`,
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  REWRITE_TAC[GSYM convergent] THEN MATCH_MP_TAC SEQ_BCONV THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[mono; real_ge] THEN DISJ2_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN MATCH_MP_TAC STIRLING_MONO THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC] THEN
  REWRITE_TAC[MR1_BOUNDED; GE; LE_REFL] THEN
  MAP_EVERY EXISTS_TAC [`&2`; `0`] THEN REWRITE_TAC[LE_0] THEN
  SIMP_TAC[REAL_ARITH `-- &1 <= x /\ x <= &1 ==> abs(x) < &2`;
           STIRLING_UPPERBOUND; STIRLING_LOWERBOUND]);;

(* ------------------------------------------------------------------------- *)
(* Now derive Wallis's infinite product.                                     *)
(* ------------------------------------------------------------------------- *)

let [PI2_LT; PI2_LE; PI2_NZ] = (CONJUNCTS o prove)
 (`&0 < pi / &2 /\ &0 <= pi / &2 /\ ~(pi / &2 = &0)`,
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let WALLIS_PARTS = prove
 (`!n. (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow n)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`\x. sin(x) pow (n + 1)`; `\x. --cos(x)`;
                `\x. (&n + &1) * sin(x) pow n * cos(x)`;
                `\x. sin(x)`; `&0`; `pi / &2`] INTEGRAL_BY_PARTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[REAL_LT_IMP_LE; PI_POS; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN REWRITE_TAC[] THEN
    CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN DIFF_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; ADD_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SIN_PI2; COS_PI2; SIN_0; COS_0] THEN
  REWRITE_TAC[REAL_ARITH `s pow k * s = s * s pow k`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow); ARITH_RULE `SUC(n + 1) = n + 2`] THEN
  REWRITE_TAC[GSYM ADD1; real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_NEG_0; REAL_SUB_LZERO] THEN
  REWRITE_TAC[C MATCH_MP (SPEC_ALL SIN_CIRCLE) (REAL_RING
    `sin(x) pow 2 + cos(x) pow 2 = &1
     ==> (n * sn * cos(x)) * --cos(x) = (n * sn) * (sin(x) pow 2 - &1)`)] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN
   `integral(&0,pi / &2)
        (\x. (&n + &1) * sin x pow (n + 2) - (&n + &1) * sin x pow n) =
    (&n + &1) * (integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) -
                 integral(&0,pi / &2) (\x. sin(x) pow n))`
   (fun th -> SUBST1_TAC th THEN REAL_ARITH_TAC) THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `(&n + &1) *
    integral(&0,pi / &2) (\x. sin x pow (n + 2) - sin x pow n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_CMUL;
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SUB] THEN
  CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN SIMP_TAC[PI2_LE]);;

let WALLIS_PARTS' = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) / (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow n)`,
  MP_TAC WALLIS_PARTS THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC REAL_FIELD);;

let WALLIS_0 = prove
 (`integral(&0,pi / &2) (\x. sin(x) pow 0) = pi / &2`,
  REWRITE_TAC[real_pow; REAL_DIV_1; REAL_MUL_LID] THEN
  SIMP_TAC[INTEGRAL_CONST; REAL_LT_IMP_LE; PI_POS; REAL_LT_DIV;
           REAL_OF_NUM_LT; ARITH; REAL_MUL_LID; REAL_SUB_RZERO]);;

let WALLIS_1 = prove
 (`integral(&0,pi / &2) (\x. sin(x) pow 1) = &1`,
  MATCH_MP_TAC DEFINT_INTEGRAL THEN REWRITE_TAC[PI2_LE; REAL_POW_1] THEN
  MP_TAC(SPECL [`\x. --cos(x)`; `\x. sin x`; `&0`; `pi / &2`] FTC1) THEN
  REWRITE_TAC[COS_0; COS_PI2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[PI2_LE] THEN
  REPEAT STRIP_TAC THEN DIFF_TAC THEN REAL_ARITH_TAC);;

let WALLIS_EVEN = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) =
         (&(FACT(2 * n)) / (&2 pow n * &(FACT n)) pow 2) * pi / &2`,
  INDUCT_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[WALLIS_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; WALLIS_PARTS'] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y * z = (&2 * y) * (x * z)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_MUL] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 2 = SUC(SUC(2 * n))`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_2; FACT;
              GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;

let WALLIS_ODD = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
         (&2 pow n * &(FACT n)) pow 2 / &(FACT(2 * n + 1))`,
  INDUCT_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[WALLIS_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * SUC n + 1 = (2 * n + 1) + 2`;
                  WALLIS_PARTS'] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y * z = (x * z) * (&2 * y)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_MUL] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(SUC n)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_2; FACT;
              GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `2 * n + 1` FACT_LT) THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  CONV_TAC REAL_FIELD);;

let WALLIS_QUOTIENT = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
        (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4 *
        pi / &2`,
  GEN_TAC THEN REWRITE_TAC[WALLIS_EVEN; WALLIS_ODD] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_POW_INV; REAL_INV_INV] THEN
  REAL_ARITH_TAC);;

let WALLIS_QUOTIENT' = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) * &2 / pi =
         (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4`,
  GEN_TAC THEN REWRITE_TAC[WALLIS_QUOTIENT] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM REAL_INV_DIV] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
  MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD);;

let WALLIS_MONO = prove
 (`!m n. m <= n
         ==> integral(&0,pi / &2) (\x. sin(x) pow n)
                <= integral(&0,pi / &2) (\x. sin(x) pow m)`,
  REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_LE THEN
  CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN REWRITE_TAC[PI2_LE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE; MATCH_MP_TAC REAL_POW_1_LE] THEN
  REWRITE_TAC[SIN_BOUNDS] THEN
  (MP_TAC(SPEC `x:real` SIN_POS_PI_LE) THEN
   ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
   REPEAT(POP_ASSUM MP_TAC) THEN MP_TAC PI2_LT THEN REAL_ARITH_TAC));;

let WALLIS_LT = prove
 (`!n. &0 < integral(&0,pi / &2) (\x. sin(x) pow n)`,
  MATCH_MP_TAC ODDEVEN_INDUCT THEN
  REWRITE_TAC[WALLIS_0; WALLIS_1; PI2_LT; REAL_OF_NUM_LT; ARITH] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WALLIS_PARTS'] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REAL_ARITH_TAC);;

let WALLIS_NZ = prove
 (`!n. ~(integral(&0,pi / &2) (\x. sin(x) pow n) = &0)`,
  MP_TAC WALLIS_LT THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let WALLIS_BOUNDS = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 1))
        <= integral(&0,pi / &2) (\x. sin(x) pow n) /\
       integral(&0,pi / &2) (\x. sin(x) pow n) <=
        (&n + &2) / (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow (n + 1))`,
  GEN_TAC THEN SIMP_TAC[WALLIS_MONO; LE_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&n + &2) / (&n + &1) *
              integral (&0,pi / &2) (\x. sin x pow (n + 2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WALLIS_PARTS'] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[WALLIS_MONO; ARITH_RULE `n + 1 <= n + 2`] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC);;

let WALLIS_RATIO_BOUNDS = prove
 (`!n. &1 <= integral(&0,pi / &2) (\x. sin(x) pow n) /
            integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) /\
      integral(&0,pi / &2) (\x. sin(x) pow n) /
      integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) <= (&n + &2) / (&n + &1)`,
  GEN_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LE_RDIV_EQ; WALLIS_LT; REAL_MUL_LID; WALLIS_BOUNDS];
    SIMP_TAC[REAL_LE_LDIV_EQ; WALLIS_LT; WALLIS_BOUNDS]]);;

let WALLIS = prove
 (`(\n. (&2 pow n * &(FACT n)) pow 4 / (&(FACT(2 * n)) * &(FACT(2 * n + 1))))
   --> pi / &2`,
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC SEQ_INV THEN
  CONJ_TAC THENL [ALL_TAC; MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD] THEN
  REWRITE_TAC[GSYM WALLIS_QUOTIENT'] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
  GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [REAL_ARITH `x = (x - &1) + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_LE_0 THEN EXISTS_TAC `\n. &1 / &n` THEN
  REWRITE_TAC[SEQ_HARMONIC] THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!d. &1 <= x /\ x <= d /\ d - &1 <= e ==> abs(x - &1) <= e`) THEN
  EXISTS_TAC `(&(2 * n) + &2) / (&(2 * n) + &1)` THEN
  REWRITE_TAC[WALLIS_RATIO_BOUNDS] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_FIELD
   `(&2 * &n + &2) / (&2 * &n + &1) - &1 = &1 / (&2 * &n + &1)`] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence determine the actual value of the limit.                            *)
(* ------------------------------------------------------------------------- *)

let LN_WALLIS = prove
 (`(\n. &4 * &n * ln(&2) + &4 * ln(&(FACT n)) -
        (ln(&(FACT(2 * n))) + ln(&(FACT(2 * n + 1))))) --> ln(pi / &2)`,
  REWRITE_TAC[REAL_ARITH `&4 * x + &4 * y - z = &4 * (x + y) - z`] THEN
  SUBGOAL_THEN `!n. &0 < &2 pow n`
   (fun th -> SIMP_TAC[th; GSYM LN_POW; REAL_OF_NUM_LT; ARITH; GSYM LN_MUL;
                       FACT_LT; REAL_POW_LT; REAL_LT_MUL; GSYM LN_DIV]) THEN
  SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC CONTL_SEQ THEN REWRITE_TAC[WALLIS] THEN
  MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `inv(pi / &2)` THEN
  MP_TAC(SPEC `pi / &2` (DIFF_CONV `\x. ln(x)`)) THEN
  SIMP_TAC[ETA_AX; PI2_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RID]);;

let STIRLING = prove
 (`(\n. ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n + ln(&2 * pi) / &2))
   --> &0`,
  REWRITE_TAC[REAL_ARITH `a - (b - c + d) = (a - (b - c)) - d`] THEN
  SUBST1_TAC(SYM(SPEC `ln(&2 * pi) / &2` REAL_SUB_REFL)) THEN
  MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC[SEQ_CONST] THEN
  X_CHOOSE_THEN `C:real` MP_TAC STIRLING_CONVERGES THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[stirling] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`2`; `1`] o MATCH_MP SEQ_SUBSEQ) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`2`; `0`] o MATCH_MP SEQ_SUBSEQ) THEN
  REWRITE_TAC[ARITH; ADD_CLAUSES; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_ADD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SEQ_MUL o CONJ (SPEC `&4` SEQ_CONST)) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUB) THEN
  MP_TAC LN_WALLIS THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUB) THEN
  REWRITE_TAC[ARITH_RULE
   `(a + &4 * x - (y + z)) - (&4 * (x - b) - ((y - c) + (z - d))) =
    (a + &4 * b) - (c + d)`] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `C = ln(&2 * pi) / &2` (fun th -> REWRITE_TAC[th]) THEN
  POP_ASSUM(MP_TAC o CONJ (SPEC `&2 * ln(&2)` SEQ_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_ADD) THEN
  SIMP_TAC[LN_DIV; PI_POS; REAL_OF_NUM_LT; ARITH; LN_MUL] THEN
  REWRITE_TAC[REAL_ARITH `&2 * l + p - l - (&4 * C - (C + C)) =
                          (l + p) - &2 * C`] THEN
  SIMP_TAC[REAL_ARITH `C = (l + p) / &2 <=> (l + p) - &2 * C = &0`] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
    SEQ_UNIQ) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_ARITH
   `a + (b + &4 * (c - x)) - ((d - &2 * x) + (e - (&2 * x + &1))) =
    (a + b + &4 * c + &1) - (d + e)`] THEN
  REWRITE_TAC[REAL_ARITH `&2 * l + &4 * n * l + &4 * (n + &1 / &2) * x + &1 =
                          (&4 * n + &2) * (l + x) + &1`] THEN
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[GSYM LN_MUL; REAL_OF_NUM_LT; ARITH; LT_0] THEN
  REWRITE_TAC[GSYM SEQ_SUC] THEN
  CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  REWRITE_TAC[REAL_ARITH
   `((&4 * n + &2) * l + &1) - ((&2 * n + &1 / &2) * l + z) =
    (&2 * n + &3 / &2) * l + &1 - z`] THEN
  REWRITE_TAC[REAL_ARITH
   `(&2 * n + &3 / &2) * l + &1 - ((&2 * n + &1) + &1 / &2) * l' =
    (&2 * n + &3 / &2) * (l - l') + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&0 = -- &1 + &1`] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * (b - c) = --(a * (c - b))`] THEN
  REWRITE_TAC[GSYM SEQ_NEG] THEN
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[GSYM LN_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; LT_0; ARITH;
           REAL_ARITH `&0 < &2 * &n + &1`] THEN
  SIMP_TAC[REAL_OF_NUM_LT; LT_0; REAL_FIELD
   `&0 < x ==> (&2 * x + &1) / (&2 * x) = &1 + &1 / (&2 * x)`] THEN
  REWRITE_TAC[GSYM SEQ_SUC] THEN
  CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  MP_TAC SEQ_SUBSEQ THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o GENL [`f:num->real`; `l:real`] o
   SPECL [`f:num->real`; `l:real`; `2`; `0`]) THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH; REAL_OF_NUM_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&1 = &1 + &3 / &2 * &0`] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[LN_LIM_LEMMA] THEN
  MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
  MP_TAC LN_LIM_LEMMA THEN MP_TAC(SPEC `&1` SEQ_HARMONIC) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_MUL) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[real_div; REAL_MUL_LID; REAL_MUL_ASSOC; REAL_MUL_LINV;
           REAL_MUL_RID; REAL_OF_NUM_EQ; NOT_SUC]);;
