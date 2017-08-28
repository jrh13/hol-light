(* ========================================================================= *)
(* "Second proof" of Prime Number Theorem from Newman's book.                *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;
needs "Library/pocklington.ml";;
needs "Examples/mangoldt.ml";;

prioritize_real();;
prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* A few miscelleneous lemmas.                                               *)
(* ------------------------------------------------------------------------- *)

let LT_NORM_CPOW_NUM = prove
 (`!n s. &0 < Re s /\ 2 <= n ==> &1 < norm(Cx(&n) cpow s)`,
  SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
           ARITH_RULE `2 <= n ==> 0 < n`] THEN
  REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
  SIMP_TAC[REAL_LT_MUL; LOG_POS_LT; REAL_OF_NUM_LT;
           ARITH_RULE `2 <= n ==> 1 < n`]);;

let CPOW_NUM_NE_1 = prove
 (`!n s. &0 < Re s /\ 2 <= n ==> ~(Cx(&n) cpow s = Cx(&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SYM o AP_TERM `norm:complex->real`) THEN
  ASM_SIMP_TAC[LT_NORM_CPOW_NUM; COMPLEX_NORM_CX; REAL_ABS_NUM;
               REAL_LT_IMP_NE]);;

let FINITE_ATMOST = prove
 (`!P n. FINITE {m:num | P m /\ m <= n}`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  SIMP_TAC[LE_0; FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG]);;

let PRIME_ATMOST_ALT = prove
 (`{p | prime p /\ p <= n} = {p | p IN 1..n /\ prime p}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An auxiliary zeta function that's analytic in the right halfplane.        *)
(* ------------------------------------------------------------------------- *)

let nearzeta = new_definition
 `nearzeta n s = infsum (from n)
                        (\m. (s - Cx(&1)) / Cx(&m) cpow s -
                              (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                               Cx(&1) / Cx(&(m+1)) cpow (s - Cx(&1))))`;;

(* ------------------------------------------------------------------------- *)
(* The actual zeta function, with analyticity of z_n(s) - 1/(s - 1)^{n-1}    *)
(* ------------------------------------------------------------------------- *)

let genzeta = new_definition
 `genzeta n s = if s = Cx(&1) then complex_derivative (nearzeta n) (Cx(&1))
                else (nearzeta n s + Cx(&1) / Cx(&n) cpow (s - Cx(&1))) /
                     (s - Cx(&1))`;;

let zeta = new_definition
 `zeta s = genzeta 1 s`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about convergence and analyticity of the series.                   *)
(* ------------------------------------------------------------------------- *)

let NEARZETA_BOUND_LEMMA = prove
 (`!s n. ~(n = 0) /\ &0 <= Re s + &1
         ==> norm((s - Cx(&1)) / Cx(&n) cpow s -
                  (Cx(&1) / Cx(&n) cpow (s - Cx(&1)) -
                   Cx(&1) / Cx(&(n + 1)) cpow (s - Cx(&1)))) <=
             norm(s * (s - Cx(&1)) / Cx(&n) cpow (s + Cx(&1)))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\n z. if n = 0 then Cx(&1) / z cpow (s - Cx(&1))
           else if n = 1 then (Cx(&1) - s) / z cpow s
           else s * (s - Cx(&1)) / z cpow (s + Cx(&1))`;
    `1`; `segment[Cx(&n),Cx(&n) + Cx(&1)]`;
    `norm(s * (s - Cx (&1)) / Cx(&n) cpow (s + Cx(&1)))`] COMPLEX_TAYLOR) THEN
  REWRITE_TAC[ARITH] THEN ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_SEGMENT] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `z:complex`] THEN STRIP_TAC;
      X_GEN_TAC `z:complex` THEN DISCH_TAC] THEN
    (SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
      [MATCH_MP_TAC RE_POS_SEGMENT THEN
       MAP_EVERY EXISTS_TAC [`Cx(&n)`; `Cx(&n) + Cx(&1)`] THEN
       ASM_REWRITE_TAC[RE_ADD; RE_CX; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
       ASM_ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
      [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[RE_CX; REAL_LT_REFL];
       ALL_TAC])
    THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
        (ARITH_RULE `i <= 1 ==> i = 0 \/ i = 1`)) THEN
      ASM_REWRITE_TAC[ARITH] THEN COMPLEX_DIFF_TAC THEN
      ASM_REWRITE_TAC[CPOW_EQ_0] THEN
      SIMP_TAC[COMPLEX_POW_2; CPOW_ADD; CPOW_SUB; CPOW_N; COMPLEX_POW_1] THEN
      (SUBGOAL_THEN `~(z cpow s = Cx(&0))` MP_TAC THENL
       [ASM_REWRITE_TAC[CPOW_EQ_0]; UNDISCH_TAC `~(z = Cx(&0))`]) THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_POW] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ; CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN `real z` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`Cx(&n)`; `Cx(&n) + Cx(&1)`] THEN
      ASM_SIMP_TAC[REAL_CX; REAL_ADD];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[RE_ADD; RE_CX] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
    UNDISCH_TAC `z IN segment[Cx (&n),Cx (&n) + Cx (&1)]` THEN
    REWRITE_TAC[segment; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[RE_CMUL; RE_ADD; RE_CX] THEN
    UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUMSEG_CONV `0..1`] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_DIV_1; COMPLEX_MUL_RID] THEN
  DISCH_THEN(MP_TAC o SPECL [`Cx(&n)`; `Cx(&n) + Cx(&1)`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT; COMPLEX_NORM_CX; COMPLEX_ADD_SUB] THEN
  REWRITE_TAC[VECTOR_ADD_RID; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_DIV_1; REAL_MUL_RID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD; complex_div] THEN
  CONV_TAC COMPLEX_RING);;

let NORM_CPOW_LOWERBOUND = prove
 (`!m s n. &m <= Re s /\ ~(n = 0) ==> &n pow m <= norm(Cx(&n) cpow s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&m * log(&n))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG; REAL_OF_NUM_LT; LT_NZ; REAL_LE_REFL];
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[REAL_EXP_0; EXP_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
    SIMP_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

let ZETATERM_BOUND = prove
 (`!s n m. &m <= Re s /\ ~(n = 0)
           ==> norm(Cx(&1) / Cx(&n) cpow s) <= inv(&n pow m)`,
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_POW_LT; NORM_CPOW_LOWERBOUND; REAL_OF_NUM_LT; LT_NZ]);;

let ZETA_CONVERGES_LEMMA = prove
 (`!n s. &2 <= Re s ==> summable (from n) (\m. Cx(&1) / Cx(&m) cpow s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[summable] THEN
  MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `\n. inv(&n - &1) - inv(&(n + 1) - &1)` THEN CONJ_TAC THENL
   [EXISTS_TAC `lift(inv(&n - &1))` THEN
    MP_TAC(ISPECL [`\n. lift(inv(&n - &1))`; `n:num`] SERIES_DIFFS) THEN
    REWRITE_TAC[o_DEF; LIFT_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC `1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
    REWRITE_TAC[SEQ_HARMONIC];
    ALL_TAC] THEN
  EXISTS_TAC `2` THEN REWRITE_TAC[GE; IN_FROM] THEN X_GEN_TAC `m:num` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_FIELD
   `&2 <= x ==> inv(x - &1) - inv((x + &1) - &1) = inv(x * (x - &1))`] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&n pow 2 <= x ==> &n * (&n - &1) <= x`) THEN
  MATCH_MP_TAC NORM_CPOW_LOWERBOUND THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let ZETADIFF_CONVERGES = prove
 (`!n s. &0 < Re(s)
         ==> ((\m. Cx(&1) / Cx(&m) cpow s - Cx(&1) / Cx(&(m + 1)) cpow s)
              sums Cx(&1) / Cx(&n) cpow s) (from n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. Cx(&1) / Cx(&m) cpow s`; `n:num`] SERIES_DIFFS) THEN
  REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\n. lift(&1 / exp (Re s * log (&n)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 VECTOR_SUB_REFL; LE_1];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &1 / (Re s * log(&n))` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_EXP; real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < x /\ (&0 <= x ==> &1 + u <= v) ==> &0 < x /\ u <= v`) THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_LT_MUL; REAL_OF_NUM_LT;
                 ARITH_RULE `2 <= n ==> 1 < n`];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `exp(inv(Re s * e))` (MATCH_MP REAL_ARCH REAL_LT_01)) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 2` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; NORM_LIFT] THEN
  SUBGOAL_THEN `&0 < log(&n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `N + 2 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_MUL;
               REAL_ARITH `&0 < x ==> abs x = x`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN
  ASM_REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n` THEN ASM_SIMP_TAC[REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[ARITH_RULE `N + 2 <= n ==> N <= n`] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EXP_LOG THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

let NEARZETA_CONVERGES_LEMMA = prove
 (`!n s. &1 <= Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
  REWRITE_TAC[summable] THEN MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `\m. norm(s * (s - Cx(&1)) / Cx(&m) cpow (s + Cx(&1)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[IN_FROM; GE; LE_1; NEARZETA_BOUND_LEMMA;
                 REAL_ARITH `&1 <= s ==> &0 <= s + &1`]] THEN
  SUBGOAL_THEN
   `summable (from n)
     (\m. lift(((Cx (norm s) * Cx (norm (s - Cx (&1)))) *
                Cx (&1) / Cx (&m) cpow Cx (Re s + &1))$1))`
  MP_TAC THENL
   [MATCH_MP_TAC SUMMABLE_COMPONENT THEN REWRITE_TAC[DIMINDEX_2; ARITH] THEN
    MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC ZETA_CONVERGES_LEMMA THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM summable] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC SUMMABLE_IFF_EVENTUALLY THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_FROM; o_THM] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM RE_DEF] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; complex_div] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID; COMPLEX_NORM_INV] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               LE_1] THEN
  REWRITE_TAC[GSYM CX_INV; RE_CX; RE_ADD]);;

let GENZETA_CONVERGES = prove
 (`!n s. &1 < Re s
         ==> ((\m. Cx(&1) / Cx(&m) cpow s) sums genzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP NEARZETA_CONVERGES_LEMMA o
        MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPECL [`n:num`; `s - Cx(&1)`] ZETADIFF_CONVERGES) THEN ANTS_TAC THENL
   [REWRITE_TAC[RE_SUB; RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SERIES_ADD) THEN
  REWRITE_TAC[COMPLEX_RING `a + (b - a) = b:complex`; genzeta] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `&1 < Re s` THEN ASM_REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(s - Cx(&1))` o
     MATCH_MP SERIES_COMPLEX_LMUL) THEN
  SUBGOAL_THEN `~(s - Cx(&1) = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[complex_div; COMPLEX_MUL_ASSOC; COMPLEX_MUL_LINV] THEN
  REWRITE_TAC[COMPLEX_MUL_AC; COMPLEX_ADD_AC]);;

let ZETA_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. Cx(&1) / Cx(&n) cpow s) sums zeta(s)) (from 1)`,
  REWRITE_TAC[zeta; GENZETA_CONVERGES]);;

(* ------------------------------------------------------------------------- *)
(* We need the series for the derivative at one stage, so do this now.       *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DERIVATIVE_ZETA_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. --clog(Cx(&n)) / Cx(&n) cpow s) sums
            complex_derivative zeta s) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n z. Cx(&1) / Cx(&n) cpow z`;
    `\n z. --clog(Cx(&n)) / Cx(&n) cpow z`;
    `{s | Re s > &1}`;
    `from 1`]
   SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX) THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
      CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; LE_1];
      ALL_TAC] THEN
    POP_ASSUM(K ALL_TAC) THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_gt] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(Re z - &1) / &2`;
      `\n. Cx(&1) / Cx(&n) cpow (Cx(&1 + (Re z - &1) / &2))`;
      `42`] THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_SUB_LT] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `Cx(&1 + (Re z - &1) / &2)` ZETA_CONVERGES) THEN
      ANTS_TAC THENL [REWRITE_TAC[RE_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MESON_TAC[summable];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_FROM; CPOW_REAL_REAL; REAL_OF_NUM_LT; RE_CX; REAL_CX;
                 LE_1; COMPLEX_NORM_DIV; NORM_CPOW_REAL] THEN
    REWRITE_TAC[GSYM CX_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_CX; RE_CX;
                real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_EXP_POS_LE] THEN
    REWRITE_TAC[REAL_ABS_EXP; GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `--(a * x) <= --(b * x) <=> b * x <= a * x`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
    MP_TAC(SPEC `z - y:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; real_gt] THEN
  MAP_EVERY X_GEN_TAC [`f:complex->complex`; `g:complex->complex`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:complex`) THEN SIMP_TAC[ASSUME `&1 < Re s`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:complex`) THEN SIMP_TAC[ASSUME `&1 < Re s`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `b /\ c /\ d ==> e <=> b /\ c ==> d ==> e`]
                HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT) THEN
  EXISTS_TAC `Re s - &1` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\n. Cx(&1) / Cx(&n) cpow z`; `from 1`] THEN
  SUBGOAL_THEN `&1 < Re z` (fun th -> ASM_SIMP_TAC[th; ZETA_CONVERGES]) THEN
  MP_TAC(SPEC `z - s:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The zeta function is actually analytic on a larger set.                   *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_NEARZETA_LEMMA = prove
 (`!n. 1 <= n
       ==> ?g g'. !s. s IN {s | Re(s) > &0}
                      ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                           (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                            Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
                           sums g s) (from n) /\
                           ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) /
                                 Cx(&m) cpow s -
                                 (clog(Cx(&(m + 1))) /
                                  Cx(&(m + 1)) cpow (s - Cx(&1)) -
                                  clog(Cx(&m)) /
                                  Cx(&m) cpow (s - Cx(&1))))
                            sums g' s) (from n) /\
                       (g has_complex_derivative g' s) (at s)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `s:complex`] THEN
    REWRITE_TAC[IN_ELIM_THM; real_gt; from] THEN STRIP_TAC THEN
    COMPLEX_DIFF_TAC THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
    ASM_REWRITE_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:complex` THEN REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
  DISCH_TAC THEN EXISTS_TAC `min (Re s / &2) (&1)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; REAL_HALF] THEN
  EXISTS_TAC `\n. Cx(norm(s) + &2) pow 2 /
                  Cx(&n) cpow Cx((Re s / &2 + &1))` THEN
  EXISTS_TAC `1` THEN CONJ_TAC THENL
   [REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MP_TAC(SPECL [`n:num`; `Cx(Re s / &2 + &1)`] GENZETA_CONVERGES) THEN
    REWRITE_TAC[RE_CX] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN MESON_TAC[summable];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN REWRITE_TAC[from; IN_ELIM_THM] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1;
                 GSYM CX_DIV; GSYM CX_POW] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_BALL; dist] THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NEARZETA_BOUND_LEMMA o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(w) = &1 /\ norm(z) <= x + &1
      ==> norm z <= abs(x + &2) /\ norm(z - w) <=  abs(x + &2)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN ASM_NORM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX; RE_CX;
               REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; RE_ADD; RE_CX] THEN
  MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC);;

let HOLOMORPHIC_NEARZETA_STRONG = prove
 (`!n s. 1 <= n /\ &0 < Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
              (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
               Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums (nearzeta n s)) (from n) /\
              ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) /
                    Cx(&m) cpow s -
                    (clog(Cx(&(m + 1))) /
                     Cx(&(m + 1)) cpow (s - Cx(&1)) -
                     clog(Cx(&m)) /
                     Cx(&m) cpow (s - Cx(&1))))
               sums (complex_derivative(nearzeta n) s)) (from n) /\
          ((nearzeta n) has_complex_derivative
           complex_derivative(nearzeta n) s) (at s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOLOMORPHIC_NEARZETA_LEMMA) THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:complex->complex`; `g':complex->complex`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [FORALL_AND_THM; TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. &0 < Re s
        ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
    ASM_MESON_TAC[summable];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. &0 < Re z ==> nearzeta n z = g z` ASSUME_TAC THENL
   [ASM_MESON_TAC[SERIES_UNIQUE]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!z. &0 < Re z ==> ((nearzeta n) has_complex_derivative g' z) (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`g:complex->complex`; `Re z`] THEN
    ASM_SIMP_TAC[dist] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `w - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_DERIVATIVE]);;

let NEARZETA_CONVERGES = prove
 (`!n s. &0 < Re s
         ==> ((\m. (s - Cx(&1)) / Cx(&m) cpow s -
                   (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1))))
              sums nearzeta n s) (from n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; SUMS_INFSUM] THEN
  MATCH_MP_TAC SUMMABLE_EQ_COFINITE THEN EXISTS_TAC `from(n + 1)` THEN
  SUBGOAL_THEN
   `from(n + 1) DIFF from n UNION from n DIFF from(n + 1) = {n}`
   (fun th -> REWRITE_TAC[th; FINITE_INSERT; FINITE_RULES])
  THENL
   [SIMP_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_FROM; IN_SING] THEN ARITH_TAC;
    MP_TAC(SPECL [`n + 1`; `s:complex`] HOLOMORPHIC_NEARZETA_STRONG) THEN
    ASM_REWRITE_TAC[summable] THEN ANTS_TAC THENL [ARITH_TAC; MESON_TAC[]]]);;

let SUMS_COMPLEX_DERIVATIVE_NEARZETA = prove
 (`!n s. 1 <= n /\ &0 < Re s
         ==> ((\m. (Cx(&1) - (s - Cx(&1)) * clog(Cx(&m))) / Cx(&m) cpow s -
                    (clog(Cx(&(m + 1))) / Cx(&(m + 1)) cpow (s - Cx(&1)) -
                     clog(Cx(&m)) / Cx(&m) cpow (s - Cx(&1)))) sums
            (complex_derivative (nearzeta n) s)) (from n)`,
  SIMP_TAC[HOLOMORPHIC_NEARZETA_STRONG]);;

let HOLOMORPHIC_NEARZETA = prove
 (`!n. 1 <= n ==> (nearzeta n) holomorphic_on {s | Re(s) > &0}`,
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN
  REWRITE_TAC[real_gt] THEN MESON_TAC[HOLOMORPHIC_NEARZETA_STRONG]);;

let COMPLEX_DIFFERENTIABLE_NEARZETA = prove
 (`!n s. 1 <= n /\ &0 < Re s ==> (nearzeta n) complex_differentiable (at s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOLOMORPHIC_NEARZETA_STRONG) THEN
  MESON_TAC[complex_differentiable]);;

let NEARZETA_1 = prove
 (`!n. 1 <= n ==> nearzeta n (Cx(&1)) = Cx(&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nearzeta; COMPLEX_SUB_REFL] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  MATCH_MP_TAC SUMS_EQ THEN EXISTS_TAC `\n:num. (vec 0:complex)` THEN
  REWRITE_TAC[SERIES_0; GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; IN_FROM; complex_div] THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[complex_pow] THEN
  CONV_TAC COMPLEX_RING);;

let HOLOMORPHIC_ZETA = prove
 (`zeta holomorphic_on {s | Re(s) > &0 /\ ~(s = Cx(&1))}`,
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[zeta; genzeta] THEN
  MATCH_MP_TAC HOLOMORPHIC_TRANSFORM THEN
  EXISTS_TAC `\z. (nearzeta 1 z + Cx(&1) / Cx(&1) cpow (z - Cx(&1))) /
                  (z - Cx(&1))` THEN
  SIMP_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  SIMP_TAC[IN_ELIM_THM; COMPLEX_SUB_0; HOLOMORPHIC_ON_SUB;
           HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `{s | Re s > &0}` THEN
    SIMP_TAC[HOLOMORPHIC_NEARZETA; LE_REFL; ETA_AX] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
    REPEAT STRIP_TAC THEN COMPLEX_DIFFERENTIABLE_TAC THEN
    REWRITE_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ]]);;

let COMPLEX_DIFFERENTIABLE_AT_ZETA = prove
 (`!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> zeta complex_differentiable at s`,
  MP_TAC HOLOMORPHIC_ZETA THEN
  REWRITE_TAC[SET_RULE `{s | P s /\ ~(s = a)} = {s | P s} DELETE a`] THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DELETE; OPEN_HALFSPACE_RE_GT] THEN
  REWRITE_TAC[complex_differentiable; IN_ELIM_THM; IN_DELETE; real_gt]);;

(* ------------------------------------------------------------------------- *)
(* Euler product formula. Nice proof from Ahlfors' book avoiding any         *)
(* messing round with the geometric series.                                  *)
(* ------------------------------------------------------------------------- *)

let SERIES_DIVISORS_LEMMA = prove
 (`!x p l k.
      ((\n. x(p * n)) sums l) k
      ==> ~(p = 0) /\
          (!n. (p * n) IN k <=> n IN k)
          ==> (x sums l) {n | n IN k /\ p divides n}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `p * N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n DIV p`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (rand o rand) VSUM_IMAGE (lhand w))) THEN
  ASM_SIMP_TAC[FINITE_INTER_NUMSEG; EQ_MULT_LCANCEL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER; IN_NUMSEG] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; divides; LE_0] THEN ASM_MESON_TAC[]);;

let EULER_PRODUCT_LEMMA = prove
 (`!s ps. &1 < Re s /\ FINITE ps /\ (!p. p IN ps ==> prime p)
          ==> ((\n. Cx(&1) / Cx(&n) cpow s) sums
               (cproduct ps (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s))
       {n | 1 <= n /\ !p. prime p /\ p divides n ==> ~(p IN ps)}`,
  let lemma = prove
   (`(x sums (k + l)) (s UNION t) /\ s INTER t = {}
     ==> (x sums k) s ==> (x sums l) t`,
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[sums] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN REWRITE_TAC[VECTOR_ADD_SUB] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ABS_TAC THEN ASM_SIMP_TAC[SET_RULE
     `s INTER t = {}
      ==> t INTER u = (((s UNION t) INTER u) DIFF (s INTER u))`] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_DIFF THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG] THEN SET_TAC[]) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[ZETA_CONVERGES; COMPLEX_MUL_LID; NOT_IN_EMPTY; GSYM from] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `ps:num->bool`] THEN
  REWRITE_TAC[IN_INSERT; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `inv(Cx(&p) cpow s)` o MATCH_MP
    SERIES_COMPLEX_LMUL) THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `x * Cx(&1) * y = Cx(&1) * x * y`] THEN
  REWRITE_TAC[GSYM COMPLEX_INV_MUL] THEN REWRITE_TAC[GSYM complex_div] THEN
  ASM_SIMP_TAC[GSYM CPOW_MUL_REAL; REAL_CX; RE_CX; REAL_POS] THEN
  REWRITE_TAC[GSYM CX_MUL; REAL_OF_NUM_MUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[]
   (ISPEC `\n. Cx(&1) / Cx(&n) cpow s` SERIES_DIVISORS_LEMMA))) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    ASM_REWRITE_TAC[MULT_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIME_PRIME_FACTOR; PRIME_1];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_RING `a * x + (Cx(&1) - a) * x = x`] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN FIRST_X_ASSUM(fun th ->
    MP_TAC th THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC) THEN
  SET_TAC[]);;

let SUMMABLE_SUBZETA = prove
 (`!s t. &1 < Re s /\ ~(0 IN t)
         ==> summable t (\n. Cx (&1) / Cx (&n) cpow s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_SUBSET THEN
  EXISTS_TAC `from 1` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_FROM] THEN ASM_MESON_TAC[LE_1]; ALL_TAC] THEN
  MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\n. Cx(&1) / Cx(&n) cpow (Cx(Re s))` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[summable] THEN EXISTS_TAC `zeta (Cx(Re s))` THEN
    MATCH_MP_TAC ZETA_CONVERGES THEN ASM_REWRITE_TAC[RE_CX];
    SIMP_TAC[IN_FROM; LE_1; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
             GSYM CX_DIV; REAL_LE_DIV; REAL_POS; REAL_EXP_POS_LE];
    EXISTS_TAC `0` THEN REWRITE_TAC[GE; LE_0; IN_FROM] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NORM_0; NORM_POS_LE] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX; RE_CX;
                 REAL_LE_REFL; REAL_OF_NUM_LT; LE_1]]);;

let EULER_PRODUCT_MULTIPLY = prove
 (`!s. &1 < Re s
       ==> ((\n. cproduct {p | prime p /\ p <= n}
                          (\p. Cx(&1) - inv(Cx(&p) cpow s)) * zeta s)
            --> Cx(&1)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
    `\n. infsum {m | 1 <= m /\ !p. prime p /\ p divides m
                                   ==> ~(p IN {p | prime p /\ p <= n})}
                (\n. Cx (&1) / Cx (&n) cpow s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
    MATCH_MP_TAC EULER_PRODUCT_LEMMA THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..n` THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; LE_0; IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?l. ((\n. Cx (&1) / Cx (&n) cpow Cx(Re s)) sums l) (from 1)`
  MP_TAC THENL
   [MP_TAC(SPEC `Cx(Re s)` ZETA_CONVERGES) THEN
    ASM_SIMP_TAC[RE_CX] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SERIES_CAUCHY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF; GE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`s:complex`;
                 `{m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)}`]
                SUMMABLE_SUBZETA) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; ARITH] THEN
  REWRITE_TAC[GSYM SUMS_INFSUM] THEN REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (MP_TAC o SPEC `N1 + N2 + 1`)) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN SIMP_TAC[NOT_LE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `dist(x,z) < e / &2 /\ dist(y,z) <= dist(x,y) + dist(x,z)
    ==> dist(x,y) < e / &2 ==> dist(y,z) < e`) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[DIST_TRIANGLE; DIST_SYM]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2 + 1`) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  REWRITE_TAC[dist] THEN SUBGOAL_THEN
   `vsum
     ({m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)} INTER
      (0..N1 + N2 + 1))
     (\n. Cx (&1) / Cx (&n) cpow s) - Cx(&1) =
    vsum
     (({m | 1 <= m /\ (!p. prime p /\ p divides m ==> n < p)} INTER
       (0..N1 + N2 + 1)) DELETE 1)
     (\n. Cx (&1) / Cx (&n) cpow s)`
  SUBST1_TAC THENL
   [SIMP_TAC[VSUM_DELETE_CASES; FINITE_INTER_NUMSEG] THEN
    REWRITE_TAC[IN_ELIM_THM; DIVIDES_ONE; IN_INTER] THEN
    REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN
    REWRITE_TAC[MESON[] `(!x. P x /\ x = 1 ==> Q x) <=> P 1 ==> Q 1`] THEN
    REWRITE_TAC[PRIME_1; IN_NUMSEG; ARITH; ARITH_RULE `1 <= a + b + 1`];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_NORM_VSUM_BOUND_SUBSET THEN
  REWRITE_TAC[FINITE_INTER_NUMSEG] THEN CONJ_TAC THENL
   [SIMP_TAC[SUBSET; IN_DELETE; IN_INTER; IN_ELIM_THM; IN_NUMSEG; IN_FROM] THEN
    ASM_MESON_TAC[PRIME_FACTOR; DIVIDES_LE; NUM_REDUCE_CONV `1 <= 0`;
                  LT_IMP_LE; LE_TRANS];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_INTER; IN_FROM] THEN STRIP_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LID; COMPLEX_NORM_INV] THEN
  ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1;
               NORM_CPOW_REAL] THEN
  SIMP_TAC[REAL_INV; REAL_CX; GSYM CX_INV; RE_CX; REAL_LE_REFL]);;

let ZETA_NONZERO_LEMMA = prove
 (`!s. &1 < Re s ==> ~(zeta s = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EULER_PRODUCT_MULTIPLY) THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; LE_REFL] THEN
  REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; COMPLEX_NORM_CX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let EULER_PRODUCT = prove
 (`!s. &1 < Re s
       ==> ((\n. cproduct {p | prime p /\ p <= n}
                          (\p. inv(Cx(&1) - inv(Cx(&p) cpow s))))
            --> zeta(s)) sequentially`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (PAT_CONV `\x. ((\n. x) --> x) sq`)
   [GSYM COMPLEX_INV_INV] THEN
  MATCH_MP_TAC LIM_COMPLEX_INV THEN
  ASM_SIMP_TAC[COMPLEX_INV_EQ_0; ZETA_NONZERO_LEMMA] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EULER_PRODUCT_MULTIPLY) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(zeta(s))` o MATCH_MP LIM_COMPLEX_RMUL) THEN
  REWRITE_TAC[COMPLEX_MUL_LID; GSYM COMPLEX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[ZETA_NONZERO_LEMMA; COMPLEX_MUL_RINV; COMPLEX_MUL_RID] THEN
  ASM_SIMP_TAC[GSYM CPRODUCT_INV; FINITE_ATMOST; COMPLEX_INV_INV]);;

(* ------------------------------------------------------------------------- *)
(* Show that s = 1 is not a zero, just for tidiness.                         *)
(* ------------------------------------------------------------------------- *)

let SUMS_GAMMA = prove
 (`((\n. Cx(sum(1..n) (\i. &1 / &i - (log(&(i + 1)) - log(&i))))) -->
    complex_derivative (nearzeta 1) (Cx(&1))) sequentially`,
  MP_TAC(SPECL [`1`; `Cx(&1)`] SUMS_COMPLEX_DERIVATIVE_NEARZETA) THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG; RE_CX; REAL_LT_01; LE_REFL] THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; CPOW_N; sums] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ THEN
  SIMP_TAC[IN_NUMSEG; CX_INJ; REAL_OF_NUM_EQ; ADD_EQ_0; ARITH; REAL_OF_NUM_LT;
           ARITH_RULE `1 <= i ==> 0 < i /\ ~(i = 0)`; GSYM CX_LOG;
           ARITH_RULE `0 < i + 1`] THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_SUB_RZERO] THEN
  REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; REAL_DIV_1]);;

let ZETA_1_NZ = prove
 (`~(zeta(Cx(&1)) = Cx(&0))`,
  REWRITE_TAC[zeta; genzeta] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 - log(&2) <= Re(complex_derivative (nearzeta 1) (Cx(&1)))`
  MP_TAC THENL
   [REWRITE_TAC[RE_DEF] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_COMPONENT_LBOUND) THEN
    EXISTS_TAC `\n. Cx(sum(1..n) (\i. &1 / &i - (log(&(i + 1)) - log(&i))))` THEN
    REWRITE_TAC[SUMS_GAMMA; TRIVIAL_LIMIT_SEQUENTIALLY; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM RE_DEF; RE_CX] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH; REAL_DIV_1; LOG_1] THEN
    REWRITE_TAC[REAL_ARITH `a - b <= a - (b - &0) + c <=> &0 <= c`] THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    SIMP_TAC[REAL_SUB_LE; GSYM LOG_DIV; REAL_OF_NUM_LT;
             ARITH_RULE `2 <= x ==> 0 < x /\ 0 < x + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SIMP_TAC[REAL_FIELD `&0 < x ==> (x + &1) / x = &1 + &1 / x`;
             REAL_OF_NUM_LT; ARITH_RULE `2 <= x ==> 0 < x`] THEN
    SIMP_TAC[LOG_LE; REAL_LE_DIV; REAL_POS];
    ASM_REWRITE_TAC[RE_CX; REAL_NOT_LE; REAL_SUB_LT] THEN
    GEN_REWRITE_TAC I [GSYM REAL_EXP_MONO_LT] THEN
    SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; ARITH] THEN
    SUBGOAL_THEN `(&1 + &1 / &2) pow 2 <= exp(&1 / &2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_LE_X];
      ALL_TAC] THEN
    SIMP_TAC[GSYM REAL_EXP_N; REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Lack of zeros on Re(s) >= 1. Nice proof from Bak & Newman.                *)
(* ------------------------------------------------------------------------- *)

let ZETA_MULTIPLE_BOUND = prove
 (`!x y. real x /\ real y /\ &1 < Re x
       ==> &1 <= norm(zeta(x) pow 3 *
                      zeta(x + ii * y) pow 4 *
                      zeta(x + Cx(&2) * ii * y) pow 2)`,
  let lemma1 = prove
   (`&0 <= a /\ &0 <= b /\ &0 <= c /\
     c * (&2 * a + b) pow 3 / &27 <= x
     ==> c * a pow 2 * b <= x`,
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= x ==> a <= x`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH
     `a pow 2 * b <= (&2 * a + b) pow 3 / &27 <=>
      &0 <= (&8 / &27 * a + &1 / &27 * b) * (a - b) pow 2`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    ASM_REAL_ARITH_TAC)
  and lemma2 = prove
   (`-- &1 <= t /\ t <= &1
     ==> &0 <= &1 + r pow 2 - &2 * r * t`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `&0 <= (&1 - t) * (&1 + t) /\ &0 <= (r - t) pow 2
      ==> &0 <= &1 + r pow 2 - &2 * r * t`) THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_LBOUND) THEN
  EXISTS_TAC
   `\n. cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) - inv(Cx(&p) cpow x))) pow 3 *
        cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) - inv(Cx(&p) cpow (x + ii * y)))) pow 4 *
        cproduct {p | prime p /\ p <= n}
                 (\p. inv(Cx(&1) -
                      inv(Cx(&p) cpow (x + Cx(&2) * ii * y)))) pow 2` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC) THEN
    MATCH_MP_TAC LIM_COMPLEX_POW THEN
    MATCH_MP_TAC EULER_PRODUCT THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real]) THEN
    ASM_REWRITE_TAC[RE_ADD; RE_MUL_CX; RE_MUL_II;
                    REAL_NEG_0; REAL_ADD_RID; REAL_MUL_RZERO];
    ALL_TAC] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[LE_0] THEN X_GEN_TAC `n:num` THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_INV; COMPLEX_NORM_NZ; COMPLEX_INV_EQ_0] THEN
  ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; ARITH; COMPLEX_INV_EQ_0;
               CPRODUCT_EQ_0; IN_ELIM_THM; FINITE_ATMOST] THEN
  REWRITE_TAC[COMPLEX_RING `Cx(&1) - x = Cx(&0) <=> x = Cx(&1)`] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[TAUT `(~p \/ ~q) \/ ~r <=> p /\ q ==> ~r`] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `(norm:complex->real) o inv`) THEN
    REWRITE_TAC[COMPLEX_NORM_INV; o_THM; COMPLEX_NORM_CX; REAL_ABS_NUM;
                REAL_INV_INV; REAL_INV_1] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ;
                 REAL_EXP_EQ_1; REAL_CX; RE_CX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real]) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; RE_ADD; RE_MUL_CX; RE_MUL_II;
                    REAL_NEG_0; REAL_ADD_RID; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 < x /\ &0 < y ==> ~(x = &0 \/ y = &0)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS_LT THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CPRODUCT_POW; FINITE_ATMOST; GSYM CPRODUCT_MUL] THEN
  SIMP_TAC[GSYM CPRODUCT_INV; COMPLEX_INV_INV; FINITE_ATMOST] THEN
  REWRITE_TAC[COMPLEX_INV_MUL; GSYM COMPLEX_POW_INV; COMPLEX_INV_INV] THEN
  SIMP_TAC[NORM_CPRODUCT; FINITE_ATMOST; REAL_INV_1] THEN
  MATCH_MP_TAC PRODUCT_LE_1 THEN SIMP_TAC[NORM_POS_LE; FINITE_ATMOST] THEN
  X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[CPOW_ADD; COMPLEX_MUL_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_INV_MUL] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ASM_REWRITE_TAC[cpow; CX_INJ; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
  REWRITE_TAC[GSYM CEXP_NEG; GSYM CEXP_N] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o CONV_RULE(REWR_CONV REAL))) THEN
  SIMP_TAC[GSYM CX_MUL; GSYM CX_NEG; GSYM CX_EXP; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_RING `--(ii * x) = ii * --x`] THEN
  REWRITE_TAC[COMPLEX_RING `--(Cx(&2) * ii * x) = ii * Cx(&2) * --x`] THEN
  REWRITE_TAC[CEXP_EULER] THEN
  REWRITE_TAC[CCOS_NEG; CSIN_NEG; GSYM CX_SIN; GSYM CX_COS; GSYM CX_NEG;
              GSYM CX_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  SIMP_TAC[REAL_RING `(z:real) pow 4 = (z pow 2) pow 2`; COMPLEX_SQNORM] THEN
  REWRITE_TAC[COMPLEX_SQNORM] THEN
  REWRITE_TAC[RE_SUB; RE_CX; RE_MUL_CX; RE_ADD; RE_MUL_II;
              IM_SUB; IM_CX; IM_MUL_CX; IM_ADD; IM_MUL_II] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_ADD_RID; REAL_SUB_LZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_RING
   `(&1 - r * c) pow 2 + --(r * s) pow 2 =
    &1 + r pow 2 * (s pow 2 + c pow 2) - &2 * r * c`] THEN
  REWRITE_TAC[SIN_CIRCLE; REAL_POW_NEG; ARITH] THEN
  ABBREV_TAC `r = exp(--(Re x * log(&p)))` THEN
  REWRITE_TAC[COS_DOUBLE_COS; COS_NEG; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  ABBREV_TAC `t = cos(Re y * log(&p))` THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ARITH
   `x - &2 * r * (&2 * y - &1) = x + &2 * r - &4 * r * y`] THEN
  MP_TAC(SPEC `Re y * log(&p)` COS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < r /\ r < &1` MP_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    SUBST1_TAC(GSYM REAL_EXP_0) THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_LT_LNEG; REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; ARITH_RULE `1 < t <=> 2 <= t`;
                 PRIME_GE_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_ARITH `r < &1 ==> abs(&1 - r) = (&1 - r)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
  MATCH_MP_TAC lemma1 THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_SUB_LE; lemma2] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `&1 + s + &2 * r - &4 * r * t = &1 + s - &2 * r * (&2 * t - &1)`] THEN
    MATCH_MP_TAC lemma2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `-- &1 <= &2 * x pow 2 - &1 <=> &0 <= x * x`;
                REAL_ARITH `&2 * t pow 2 - &1 <= &1 <=> t pow 2 <= &1 pow 2`;
                REAL_LE_SQUARE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `x pow 3 * y pow 3 / &27 <= &1 <=> (x * y) pow 3 <= &3 pow 3`] THEN
  MATCH_MP_TAC REAL_POW_LE2_ODD THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[REAL_ARITH
   `&2 * (&1 + r pow 2 - &2 * r * t) + &1 + r pow 2 +
    &2 * r - &4 * r * t pow 2 =
    (&3 + &3 * r pow 2) - &2 * r * (&2 * t pow 2 + &2 * t - &1)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - r) * ((&3 + &3 * r pow 2) + &3 * r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_ARITH
     `c - &2 * r * y <= c + &3 * r <=> &0 <= r * (&2 * y + &3)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &2 * (&2 * t pow 2 + &2 * t - &1) + &3 <=>
                            &0 <= (t + &1 / &2) pow 2`] THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r pow 3` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE]; REAL_ARITH_TAC]);;

let ZETA_NONZERO = prove
 (`!s. &1 <= Re s ==> ~(zeta s = Cx(&0))`,
  REWRITE_TAC[REAL_ARITH `&1 <= x <=> &1 < x \/ x = &1`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[ZETA_NONZERO_LEMMA] THEN
  SUBST1_TAC(SPEC `s:complex` COMPLEX_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `y = Im s` THEN ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; ZETA_1_NZ] THEN
  DISCH_TAC THEN SUBGOAL_THEN
  `~(&1 <= norm((Cx(&0) *
                complex_derivative (\x. zeta(x + ii * Cx y)) (Cx(&1)) pow 4) *
                zeta (Cx(&1) + Cx (&2) * ii * Cx(y)) pow 2))`
  MP_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_MUL_LZERO] THEN REAL_ARITH_TAC;
    SIMP_TAC[]] THEN
  MATCH_MP_TAC(ISPEC `at (Cx(&1)) within {s | real s /\ &1 < Re s}`
   LIM_NORM_LBOUND) THEN
  EXISTS_TAC
   `\x. zeta (x) pow 3 * zeta (x + ii * Cx(y)) pow 4 *
        zeta (x + Cx (&2) * ii * Cx(y)) pow 2` THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; TRIVIAL_LIMIT_WITHIN] THEN
  SUBGOAL_THEN `Cx(&1) limit_point_of {s | real s /\ &1 < Re s}`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIMPT_APPROACHABLE_LE] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN EXISTS_TAC `Cx(&1 + e)` THEN
    REWRITE_TAC[dist; CX_INJ; IN_ELIM_THM; REAL_CX; RE_CX] THEN
    REWRITE_TAC[GSYM CX_SUB; REAL_ADD_SUB; COMPLEX_NORM_CX] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IN_ELIM_THM] THEN
    SIMP_TAC[ZETA_MULTIPLE_BOUND; REAL_CX]] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN MATCH_MP_TAC LIM_COMPLEX_MUL THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONTINUOUS_WITHIN] THEN
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_POW THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_ZETA THEN
    REWRITE_TAC[RE_ADD; RE_MUL_CX; RE_MUL_II; RE_II; RE_CX] THEN
    REWRITE_TAC[COMPLEX_RING `x + y = x <=> y = Cx(&0)`] THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ; REAL_OF_NUM_EQ; ARITH] THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\x. (zeta x pow 3 * (x - Cx(&1)) pow 4) *
                  (zeta(x + ii * Cx y) / (x - Cx(&1))) pow 4` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SIMP_TAC[LIM_WITHIN; GSYM DIST_NZ; COMPLEX_SUB_0; COMPLEX_FIELD
     `~(x = Cx(&0))
      ==> (y * x pow 4) * (z / x) pow 4 - y * z pow 4 = Cx(&0)`] THEN
    SIMP_TAC[dist; COMPLEX_VEC_0; COMPLEX_SUB_REFL; COMPLEX_NORM_0] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LIM_COMPLEX_POW THEN
    SUBGOAL_THEN `((\x. zeta (x + ii * Cx y)) has_complex_derivative
                   complex_derivative (\x. zeta (x + ii * Cx y)) (Cx (&1)))
                  (at (Cx (&1)) within {s | real s /\ &1 < Re s})`
    MP_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN; COMPLEX_SUB_RZERO]] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN
    SIMP_TAC[COMPLEX_DIFFERENTIABLE_ADD; COMPLEX_DIFFERENTIABLE_CONST;
             COMPLEX_DIFFERENTIABLE_ID] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_ZETA THEN
    ASM_REWRITE_TAC[RE_ADD; RE_MUL_II; COMPLEX_RING `x + y = x <=> y = Cx(&0)`;
                    IM_CX; COMPLEX_ENTIRE; II_NZ; RE_CX; CX_INJ] THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\x. (nearzeta 1 (x) + Cx(&1)) pow 3 * (x - Cx(&1))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[LIM_WITHIN; CPOW_1; GSYM DIST_NZ; zeta; genzeta; COMPLEX_DIV_1;
    COMPLEX_FIELD
    `~(x:complex = a)
     ==> b * (x - a) - (c / (x - a)) pow 3 * (x - a) pow 4 =
         (b - c pow 3) * (x - a)`] THEN
    REWRITE_TAC[dist; VECTOR_SUB_RZERO; VECTOR_SUB_REFL] THEN
    SIMP_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_NORM_0] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_AT_WITHIN THEN SUBST1_TAC(COMPLEX_RING
   `Cx(&0) = (nearzeta 1 (Cx(&1)) + Cx(&1)) pow 3 * (Cx(&1) - Cx(&1))`) THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN
  SIMP_TAC[LIM_SUB; LIM_CONST; LIM_AT_ID] THEN
  MATCH_MP_TAC LIM_COMPLEX_POW THEN MATCH_MP_TAC LIM_ADD THEN
  REWRITE_TAC[LIM_CONST] THEN REWRITE_TAC[GSYM CONTINUOUS_AT] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  ASM_SIMP_TAC[ETA_AX; COMPLEX_DIFFERENTIABLE_NEARZETA;
               RE_CX; REAL_OF_NUM_LT; ARITH]);;

let NEARZETA_NONZERO = prove
 (`!s. &1 <= Re s ==> ~(nearzeta 1 s + Cx (&1) = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZETA_NONZERO) THEN
  REWRITE_TAC[zeta; genzeta] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[NEARZETA_1; ARITH; CPOW_1] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The logarithmic derivative of the zeta function.                          *)
(* ------------------------------------------------------------------------- *)

let NORM_CLOG_BOUND = prove
 (`norm(z) <= &1 / &2 ==> norm(clog(Cx(&1) - z)) <= &2 * norm(z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. clog(Cx(&1) - z)`; `\z. inv(z - Cx(&1))`;
   `cball(Cx(&0),&1 / &2)`; `&2`] COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL [`z:complex`; `Cx(&0)`]) THEN
    REWRITE_TAC[COMPLEX_SUB_RZERO; CLOG_1] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN REWRITE_TAC[IN_CBALL] THEN
    ASM_REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  REWRITE_TAC[CONVEX_CBALL; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
   [COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_RING `(Cx(&0) - Cx(&1)) * x = --x`] THEN
    REWRITE_TAC[COMPLEX_NEG_INV; COMPLEX_NEG_SUB] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RE_SUB; REAL_SUB_LT] THEN
    MP_TAC(SPEC `w:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; RE_CX] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&1 / &2)`)) THEN
  REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  MP_TAC(SPEC `1` COMPLEX_NORM_NUM) THEN ASM_NORM_ARITH_TAC);;

let LOGZETA_EXISTS = prove
 (`?logzeta logzeta'.
        !s. s IN {s | Re s > &1}
            ==> ((\p. clog(Cx(&1) - inv(Cx(&p) cpow s)))
                 sums logzeta(s))
                {p | prime p} /\
                ((\p. clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1)))
                 sums logzeta'(s))
                {p | prime p} /\
                (logzeta has_complex_derivative logzeta'(s)) (at s)`,
  MATCH_MP_TAC SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
    REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ;
      COMPLEX_SUB_LZERO; COMPLEX_MUL_LID; COMPLEX_FIELD
       `~(x = Cx(&0)) ==> --(a * x) / x pow 2 = --(a / x)`] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LNEG; COMPLEX_NEG_NEG] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_INV_MUL] THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ; COMPLEX_FIELD
     `~(y = Cx(&0)) ==> y * (Cx(&1) - inv(y)) = y - Cx(&1)`] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RE_SUB; REAL_SUB_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `!y. abs x <= y /\ y < w ==> x < w`) THEN
    EXISTS_TAC `norm(inv (Cx (&p) cpow s))` THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN REWRITE_TAC[RE_CX] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX; RE_CX;
                 REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_LT_LNEG; REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; ARITH_RULE `1 < p <=> 2 <= p`;
                 PRIME_GE_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt] THEN X_GEN_TAC `s:complex` THEN
  DISCH_TAC THEN EXISTS_TAC `(Re(s) - &1) / &2` THEN
  EXISTS_TAC `\p. Cx(&2) / Cx(&p) cpow (Cx(&1 + (Re(s) - &1) / &2))` THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT; RIGHT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC SUMMABLE_SUBSET_COMPLEX THEN EXISTS_TAC `from 1` THEN
    SIMP_TAC[CPOW_REAL_REAL; IN_FROM; REAL_CX; RE_CX; REAL_OF_NUM_LT;
             ARITH_RULE `0 < n <=> 1 <= n`; GSYM CX_INV; REAL_LE_INV_EQ;
             REAL_EXP_POS_LE] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_FROM; PRIME_GE_2;
             ARITH_RULE `2 <= p ==> 1 <= p`] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC `zeta(Cx(&1 + (Re s - &1) / &2))` THEN
    ONCE_REWRITE_TAC[COMPLEX_RING `inv(x) = Cx(&1) * inv x`] THEN
    REWRITE_TAC[GSYM complex_div] THEN MATCH_MP_TAC ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SIMP_TAC[CPOW_REAL_REAL; IN_FROM; REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ;
             PRIME_IMP_NZ; GSYM CX_DIV; REAL_CX; REAL_LE_DIV; REAL_POS;
             REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `summable (from 1) (\n. Cx (&1) / Cx (&n) cpow (Cx(&1 + (Re s - &1) / &2)))`
  MP_TAC THENL
   [REWRITE_TAC[summable] THEN
    EXISTS_TAC `zeta(Cx(&1 + (Re s - &1) / &2))` THEN
    MATCH_MP_TAC ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2` o MATCH_MP SERIES_GOESTOZERO) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(fun th ->
    X_GEN_TAC `y:complex` THEN STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[IN_FROM; PRIME_IMP_NZ; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * norm(inv(Cx(&p) cpow y))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NORM_CLOG_BOUND THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < a ==> y <= x ==> y <= a`)) THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID];
    SIMP_TAC[complex_div; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]] THEN
  REWRITE_TAC[GSYM CPOW_NEG] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL_MONO; REAL_CX; RE_CX; REAL_OF_NUM_LT; PRIME_GE_2;
               ARITH_RULE `2 <= p ==> 1 < p`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_BALL_RE) THEN
  REWRITE_TAC[RE_NEG; RE_CX] THEN REAL_ARITH_TAC);;

let LOGZETA_PROPERTIES =
  new_specification ["logzeta"; "logzeta'"] LOGZETA_EXISTS;;

let [LOGZETA_CONVERGES; LOGZETA'_CONVERGES; HAS_COMPLEX_DERIVATIVE_LOGZETA] =
    CONJUNCTS(REWRITE_RULE[IN_ELIM_THM; FORALL_AND_THM; real_gt; TAUT
                             `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                          LOGZETA_PROPERTIES);;

let CEXP_LOGZETA = prove
 (`!s. &1 < Re s ==> cexp(--(logzeta s)) = zeta s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. cexp(vsum({p | prime p} INTER (0..n))
                 (\p. --clog(Cx(&1) - inv(Cx(&p) cpow s))))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`cexp`; `--logzeta s`] CONTINUOUS_AT_SEQUENTIALLY) THEN
    REWRITE_TAC[CONTINUOUS_AT_CEXP; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM sums] THEN
    MATCH_MP_TAC SERIES_NEG THEN ASM_SIMP_TAC[LOGZETA_CONVERGES];
    SIMP_TAC[CEXP_VSUM; FINITE_INTER_NUMSEG] THEN
    MATCH_MP_TAC LIM_TRANSFORM THEN
    EXISTS_TAC `\n. cproduct {p | prime p /\ p <= n}
                             (\p. inv(Cx(&1) - inv(Cx(&p) cpow s)))` THEN
    ASM_SIMP_TAC[EULER_PRODUCT] THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[VECTOR_SUB_EQ; numseg; LE_0] THEN
    REWRITE_TAC[SET_RULE `{x | P x} INTER {x | Q x} = {x | P x /\ Q x}`] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
    REWRITE_TAC[IN_ELIM_THM; CEXP_NEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CEXP_CLOG THEN
    REWRITE_TAC[COMPLEX_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; REAL_OF_NUM_LT; RE_CX; REAL_ABS_NUM;
     COMPLEX_NORM_INV; PRIME_IMP_NZ; LT_NZ; COMPLEX_NORM_CX; REAL_EXP_EQ_1] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM REAL_EXP_0; GSYM REAL_EXP_NEG; REAL_EXP_INJ] THEN
    REWRITE_TAC[REAL_NEG_EQ_0; REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 < s ==> ~(s = &0)`] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC]);;

let HAS_COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &1 < Re s ==> (zeta has_complex_derivative
                      (--(logzeta'(s)) * zeta(s))) (at s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. cexp(--(logzeta s))` THEN EXISTS_TAC `Re s - &1` THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM IN_BALL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CEXP_LOGZETA THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_BALL_RE) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN
  ASM_SIMP_TAC[GSYM CEXP_LOGZETA; HAS_COMPLEX_DERIVATIVE_CEXP] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_NEG THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_LOGZETA]);;

let COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &1 < Re s
       ==> complex_derivative zeta s = --(logzeta'(s)) * zeta(s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_ZETA]);;

let CONVERGES_LOGZETA'' = prove
 (`!s. &1 < Re s
       ==> ((\p. Cx(log(&p)) / (Cx(&p) cpow s - Cx(&1))) sums
            (--(complex_derivative zeta s / zeta s))) {p | prime p}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--(complex_derivative zeta s / zeta s) = logzeta'(s)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[ZETA_NONZERO_LEMMA; COMPLEX_DERIVATIVE_ZETA; COMPLEX_FIELD
     `~(b = Cx(&0)) ==> (--(a / b) = c <=> a = --c * b)`];
    MATCH_MP_TAC SUMS_EQ THEN
    EXISTS_TAC `\p. clog(Cx(&p)) / (Cx(&p) cpow s - Cx(&1))` THEN
    ASM_SIMP_TAC[LOGZETA'_CONVERGES; IN_ELIM_THM] THEN
    SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ]]);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas about negating a path.                                        *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_NEGATEPATH = prove
 (`!g. valid_path g ==> valid_path ((--) o g)`,
  REWRITE_TAC[valid_path; o_DEF] THEN
  ASM_SIMP_TAC[PIECEWISE_DIFFERENTIABLE_NEG]);;

let PATHSTART_NEGATEPATH = prove
 (`!g. pathstart((--) o g) = --(pathstart g)`,
  REWRITE_TAC[pathstart; o_THM]);;

let PATHFINISH_NEGATEPATH = prove
 (`!g. pathfinish((--) o g) = --(pathfinish g)`,
  REWRITE_TAC[pathfinish; o_THM]);;

let PATH_IMAGE_NEGATEPATH = prove
 (`!g. path_image((--) o g) = IMAGE (--) (path_image g)`,
  REWRITE_TAC[path_image; IMAGE_o]);;

let HAS_PATH_INTEGRAL_NEGATEPATH = prove
 (`!g z. valid_path g /\ ((\z. f(--z)) has_path_integral (--i)) g
         ==> (f has_path_integral i) ((--) o g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[has_path_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[valid_path; piecewise_differentiable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[NEGLIGIBLE_FINITE] THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
  REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[o_DEF; GSYM COMPLEX_MUL_RNEG] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_LT_01] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_NEG THEN
  ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS; DIFFERENTIABLE_AT_WITHIN]);;

let WINDING_NUMBER_NEGATEPATH = prove
 (`!g z. valid_path g /\ ~(Cx(&0) IN path_image g)
         ==> winding_number((--) o g,Cx(&0)) = winding_number(g,Cx(&0))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WINDING_NUMBER_VALID_PATH; VALID_PATH_NEGATEPATH;
               PATH_IMAGE_NEGATEPATH; IN_IMAGE; UNWIND_THM2;
               COMPLEX_RING `Cx(&0) = --x <=> x = Cx(&0)`] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_NEGATEPATH THEN
  ASM_REWRITE_TAC[COMPLEX_RING `--z - Cx(&0) = --(z - Cx(&0))`] THEN
  REWRITE_TAC[complex_div; COMPLEX_INV_NEG; COMPLEX_MUL_RNEG] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_NEG THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  ASM_SIMP_TAC[GSYM complex_div; PATH_INTEGRABLE_INVERSEDIFF]);;

let PATH_INTEGRABLE_NEGATEPATH = prove
 (`!g z. valid_path g /\ (\z. f(--z)) path_integrable_on g
         ==> f path_integrable_on ((--) o g)`,
  REWRITE_TAC[path_integrable_on] THEN
  MESON_TAC[HAS_PATH_INTEGRAL_NEGATEPATH; COMPLEX_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Some bounding lemmas given by Newman. BOUND_LEMMA_2 is my variant since I *)
(* use a slightly different contour.                                         *)
(* ------------------------------------------------------------------------- *)

let BOUND_LEMMA_0 = prove
 (`!z R. norm(z) = R
         ==> Cx(&1) / z + z / Cx(R) pow 2 = Cx(&2 * Re z / R pow 2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[complex_div; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[GSYM complex_div] THEN ASM_REWRITE_TAC[COMPLEX_INV_CNJ] THEN
  ASM_REWRITE_TAC[complex_div; GSYM COMPLEX_ADD_RDISTRIB] THEN
  REWRITE_TAC[COMPLEX_ADD_CNJ; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_INV; COMPLEX_NORM_POW] THEN
  REWRITE_TAC[CX_MUL; CX_DIV; CX_POW; complex_div; GSYM COMPLEX_MUL_ASSOC]);;

let BOUND_LEMMA_1 = prove
 (`!z R. norm(z) = R
         ==> norm(Cx(&1) / z + z / Cx(R) pow 2) = &2 * abs(Re z) / R pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BOUND_LEMMA_0; COMPLEX_NORM_CX] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
  ASM_MESON_TAC[NORM_ARITH `norm z = R ==> abs R = R`]);;

let BOUND_LEMMA_2 = prove
 (`!R x z. Re(z) = --x /\ abs(Im(z)) = R /\ &0 <= x /\ &0 < R
           ==> norm (Cx (&1) / z + z / Cx R pow 2) <= &2 * x / R pow 2`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_LE_SQUARE; COMPLEX_SQNORM; DOT_SQUARE_NORM] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= &2 * x <=> &0 <= x`] THEN
  ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POW_LT] THEN
  REWRITE_TAC[complex_div] THEN
  SUBST1_TAC(SPEC `z:complex` COMPLEX_INV_CNJ) THEN
  ASM_SIMP_TAC[cnj; RE; IM; COMPLEX_MUL_LID; REAL_LE_MUL; REAL_POS] THEN
  REWRITE_TAC[GSYM CX_POW; COMPLEX_SQNORM; RE; IM] THEN
  ASM_REWRITE_TAC[REAL_RING `(--x:real) pow 2 = x pow 2`] THEN
  REWRITE_TAC[GSYM CX_INV; complex_div] THEN
  REWRITE_TAC[complex_mul; complex_add; RE; IM; RE_CX; IM_CX;
              REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_LID] THEN
  ASM_REWRITE_TAC[REAL_RING `(--x:real) pow 2 = x pow 2`;
   REAL_RING `(--x * a + --x * b:real) pow 2 = x pow 2 * (a + b) pow 2`;
   REAL_RING `(--R * a + R * b:real) pow 2 = R pow 2 * (b - a) pow 2`] THEN
  SUBGOAL_THEN `&0 < x pow 2 + R pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 < y ==> &0 < x + y`) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN `Im z pow 2 = R pow 2` SUBST1_TAC THENL
   [ASM_MESON_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_FIELD
   `&0 < R pow 2 /\ &0 < x pow 2 + R pow 2
    ==> x pow 2 * (inv (x pow 2 + R pow 2) + inv (R pow 2)) pow 2 +
        R pow 2 * (inv (R pow 2) - inv (x pow 2 + R pow 2)) pow 2 =
        (x pow 4 + &5 * R pow 2 * x pow 2 + &4 * R pow 4) /
        (x pow 2 + R pow 2) pow 2 *
        (x pow 2 / R pow 4)`] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_FIELD
  `&0 < R pow 2 ==> (&2 * x / R pow 2) pow 2 = &4 * x pow 2 / R pow 4`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LT_IMP_LE]);;

let BOUND_LEMMA_3 = prove
 (`!a n. (!m. 1 <= m ==> norm(a(m)) <= &1) /\
         1 <= n /\ &1 <= Re w /\ &0 < Re z
         ==> norm(vsum(1..n) (\n. a(n) / Cx(&n) cpow (w - z)))
                  <= exp(Re(z) * log(&n)) * (&1 / &n + &1 / Re(z))`,
  let lemma1 = prove
   (`!n x.
          &1 <= x
          ==> sum(1..n) (\n. exp((x - &1) * log(&n))) <=
                  exp(x * log(&n + &1)) / x`,
    REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
     [ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUM_CLAUSES] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n. n cpow (Cx(x) - Cx(&1))`;
      `\n. n cpow (Cx(x)) / (Cx(x))`;
      `1`; `n:num`]
    SUM_INTEGRAL_UBOUND_INCREASING) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
           [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
          REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
         [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC;
          CONV_TAC COMPLEX_FIELD];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&1 <= b` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y /\ u <= v ==> x <= u ==> y <= v`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[GSYM CX_SUB];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < n <=> 1 <= n`;
                 REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[CPOW_1] THEN
    REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
    UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC)
  and lemma1' = prove
   (`!n x.
          &0 < x /\ x <= &1
          ==> sum(1..n) (\n. exp((x - &1) * log(&n))) <=
                  exp(x * log(&n)) / x`,
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
     [ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUM_CLAUSES] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_EXP_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT] THEN
    REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_EXP_0; ARITH] THEN
    ASM_CASES_TAC `2 <= n` THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
      SIMP_TAC[GSYM NUMSEG_EMPTY; SUM_CLAUSES] THEN DISCH_THEN(K ALL_TAC) THEN
      SUBGOAL_THEN `n = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_1; REAL_MUL_RZERO; REAL_EXP_0; real_div; REAL_MUL_LID;
                   REAL_ADD_RID; REAL_INV_1_LE]] THEN
    MP_TAC(ISPECL
     [`\n. n cpow (Cx(x) - Cx(&1))`;
      `\n. n cpow (Cx(x)) / (Cx(x))`;
      `2`; `n:num`]
    SUM_INTEGRAL_UBOUND_DECREASING) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
       [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
           [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
          REWRITE_TAC[RE_CX] THEN
          REPEAT(FIRST_X_ASSUM(MP_TAC o
            GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
         [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
          CONV_TAC COMPLEX_FIELD];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&1 <= b` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&1 - x) * a <= (&1 - x) * b ==> (x - &1) * b <= (x - &1) * a`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x = y /\ &1 + u <= v ==> x <= u ==> &1 + y <= v`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[CPOW_1] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[GSYM CX_SUB];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `2 <= i ==> 0 < i`] THEN
    REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 + a - x <= a`) THEN
    ASM_SIMP_TAC[REAL_INV_1_LE; real_div; REAL_MUL_LID]) in
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\n. exp((Re(z) - &1) * log(&n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT; ARITH_RULE `0 < k <=> 1 <= k`] THEN
    REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; GSYM RE_NEG; COMPLEX_NEG_SUB] THEN
    REWRITE_TAC[RE_SUB] THEN UNDISCH_TAC `&1 <= Re w` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = Re z` THEN
  DISJ_CASES_TAC(ARITH_RULE `x <= &1 \/ &1 <= x`) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(x * log(&n)) / x` THEN
    ASM_SIMP_TAC[lemma1'] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_ARITH `x <= a + x <=> &0 <= a`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_EXP_POS_LE; REAL_LE_INV_EQ; REAL_POS];
    ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH
     `b <= x * a /\ c <= x * d ==> c + b <= x * (a + d)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_EXP_SUB; REAL_MUL_LID] THEN
      ASM_SIMP_TAC[real_div; REAL_MUL_LID; EXP_LOG; REAL_OF_NUM_LT;
                   ARITH_RULE `0 < n <=> 1 <= n`; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(x * log(&(n - 1) + &1)) / x` THEN CONJ_TAC THEN
    ASM_SIMP_TAC[lemma1] THEN REWRITE_TAC[REAL_OF_NUM_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> n - 1 + 1 = n`] THEN
    REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LID]]);;

let BOUND_LEMMA_4 = prove
 (`!a n m. (!m. 1 <= m ==> norm(a(m)) <= &1) /\
           1 <= n /\ &1 <= Re w /\ &0 < Re z
           ==> norm(vsum(n+1..m) (\n. a(n) / Cx(&n) cpow (w + z)))
                    <= &1 / (Re z * exp(Re z * log(&n)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(n+1..m) (\n. &1 / exp((Re(z) + &1) * log(&n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0 < r /\ 1 <= r` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; RE_NEG; COMPLEX_NEG_SUB] THEN
    REWRITE_TAC[RE_ADD; REAL_LE_NEG2] THEN
    UNDISCH_TAC `&1 <= Re w` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = Re z` THEN
  ASM_CASES_TAC `n + 1 <= m` THENL
   [ALL_TAC;
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
    SIMP_TAC[GSYM NUMSEG_EMPTY; SUM_CLAUSES] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_LE_MUL;
                 REAL_EXP_POS_LE; REAL_LT_IMP_LE]] THEN
  MP_TAC(ISPECL
   [`\n. n cpow (--(Cx(x) + Cx(&1)))`;
    `\n. --(n cpow (--(Cx(x)))) / Cx(x)`;
    `n + 1`; `m:num`]
   SUM_INTEGRAL_UBOUND_DECREASING) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
         [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
        REWRITE_TAC[RE_CX] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o
          GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_RING `--x - Cx(&1) = --(x + Cx(&1))`] THEN
      SUBGOAL_THEN `~(Cx x = Cx(&0))` MP_TAC THENL
       [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC;
        CONV_TAC COMPLEX_FIELD];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < a /\ &0 < b` STRIP_ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o
          GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x * a <= x * b ==> --x * b <= --x * a`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = y /\ u <= v ==> x <= u ==> y <= v`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG] THEN
    SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[CPOW_NEG] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `n + 1 <= m ==> 0 < m`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 <= n ==> 0 < n`)) THEN
  ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[GSYM CX_INV; GSYM CX_SUB; RE_CX; GSYM CX_DIV; GSYM CX_NEG] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_SUB_NEG2; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x = z /\ &0 <= y ==> x - y <= z`) THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_EXP_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Our overall bound does go to zero as N increases.                         *)
(* ------------------------------------------------------------------------- *)

let OVERALL_BOUND_LEMMA = prove
 (`!d M R. &0 < d
           ==> !e. &0 < e
                   ==> ?N. !n. N <= n
                               ==> abs(&2 * pi / &n +
                                       &6 * M * R / (d * exp (d * log (&n))) +
                                       &4 * M / (R * log (&n)) pow 2) < e`,
  ONCE_REWRITE_TAC[REAL_ARITH `abs x = abs(x - &0)`] THEN
  REWRITE_TAC[GSYM REALLIM_SEQUENTIALLY] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  REPEAT(MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N] THENL
   [MP_TAC(SPEC `Cx d` LIM_1_OVER_POWER) THEN ASM_REWRITE_TAC[RE_CX] THEN
    REWRITE_TAC[REALLIM_COMPLEX; o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; REAL_OF_NUM_LT; CX_INV; LE_1;
             complex_div; COMPLEX_MUL_LID];
    MATCH_MP_TAC REALLIM_NULL_POW THEN REWRITE_TAC[REAL_INV_MUL; ARITH] THEN
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_LOG]]);;

(* ------------------------------------------------------------------------- *)
(* Newman/Ingham analytic lemma (as in Newman's book).                       *)
(* ------------------------------------------------------------------------- *)

let NEWMAN_INGHAM_THEOREM = prove
 (`!f a. (!n. 1 <= n ==> norm(a(n)) <= &1) /\
         f analytic_on {z | Re(z) >= &1} /\
         (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
         ==> !z. Re(z) >= &1
                 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REWRITE_TAC[real_ge; analytic_on; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `&1 <= w ==> w > &1 \/ w = &1`)) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ABBREV_TAC `R = max (&3 / e) (&1)` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ d <= R /\
        (\z. f(w + z)) holomorphic_on {z | Re(z) >= --d /\ abs(Im z) <= R}`
  (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))))
  THENL
   [SUBGOAL_THEN
     `?d. &0 < d /\
          (\z. f(w + z)) holomorphic_on {z | Re(z) >= --d /\ abs(Im z) <= R}`
     (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)
    THENL
     [ALL_TAC;
      EXISTS_TAC `min d R` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{z | Re(z) >= --d /\ abs(Im z) <= R}` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC] THEN
    ABBREV_TAC `g = \z. (f:complex->complex) (w + z)` THEN
    SUBGOAL_THEN
     `!z. &0 <= Re z ==> ?e. &0 < e /\ g holomorphic_on ball (z,e)`
    MP_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `!z. &1 <= Re z ==> (?e. &0 < e /\ f holomorphic_on ball (z,e))` THEN
      DISCH_THEN(MP_TAC o SPEC `w + z:complex`) THEN
      ASM_SIMP_TAC[RE_ADD;REAL_ARITH `&0 <= z ==> &1 <= &1 + z`] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
      SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
      UNDISCH_TAC `f holomorphic_on ball(w + z,d)` THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_BALL; IN_IMAGE] THEN
      REWRITE_TAC[COMPLEX_RING `x:complex = w + y <=> x - w = y`] THEN
      REWRITE_TAC[UNWIND_THM1] THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `bs:complex->real`) THEN
    MP_TAC(ISPECL [`complex(&0,--R)`; `complex(&0,R)`] COMPACT_INTERVAL) THEN
    REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
    DISCH_THEN(MP_TAC o SPEC
     `IMAGE (\z. {w | abs(Re(z - w)) < bs z / &2 /\ abs(Im(z - w)) < bs z / &2})
            (interval[complex(&0,--R),complex(&0,R)])`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[RE_SUB; IM_SUB; REAL_ARITH
         `abs(x - a) < e /\ abs(y - b) < e <=>
          a < x + e /\ a > x - e /\ b < y + e /\ b > y - e`] THEN
        SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
        REPEAT(MATCH_MP_TAC OPEN_INTER THEN STRIP_TAC) THEN
        REWRITE_TAC[OPEN_HALFSPACE_IM_GT; OPEN_HALFSPACE_IM_LT;
                    OPEN_HALFSPACE_RE_GT; OPEN_HALFSPACE_RE_LT];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> x IN g x) ==> s SUBSET (UNIONS (IMAGE g s))`) THEN
      REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_ABS_NUM] THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      ASM_MESON_TAC[REAL_HALF];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> c /\ b /\ a`] THEN
    REWRITE_TAC[FINITE_SUBSET_IMAGE; RIGHT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> d /\ a /\ b /\ c`] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:complex->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inf (IMAGE (bs:complex->real) t) / &2` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET UNIONS (IMAGE g t) ==> ~(s = {}) ==> ~(t = {})`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `complex(&0,&0)` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    REWRITE_TAC[REAL_HALF] THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `t SUBSET s ==> (!x. x IN s ==> P x) ==> (!x. x IN t ==> P x)`)) THEN
      REWRITE_TAC[IN_INTERVAL; FORALL_2; GSYM RE_DEF; DIMINDEX_2] THEN
      REWRITE_TAC[RE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE] THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_WITHIN THEN
    ASM_CASES_TAC `&0 <= Re z` THENL
     [ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; complex_differentiable; OPEN_BALL;
                    CENTRE_IN_BALL];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `complex(&0,Im z)` o MATCH_MP (SET_RULE
     `i SUBSET UNIONS s ==> !x. x IN i ==> x IN UNIONS s`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
      REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
      UNDISCH_TAC `abs(Im z) <= R` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:complex` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN `Re v = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `(v:complex) IN t` THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `t SUBSET s ==> (x IN s ==> P x) ==> (x IN t ==> P x)`)) THEN
      REWRITE_TAC[IN_INTERVAL; FORALL_2; GSYM RE_DEF; DIMINDEX_2] THEN
      REWRITE_TAC[RE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; RE_SUB; IM_SUB; RE; IM] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    UNDISCH_TAC
     `!z. &0 <= Re z ==> &0 < bs z /\ g holomorphic_on ball (z,bs z)` THEN
    DISCH_THEN(MP_TAC o SPEC `v:complex`) THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL; GSYM complex_differentiable] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL] THEN
    REWRITE_TAC[dist; complex_norm] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x < abs e ==> x < e`) THEN
    ASM_REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < b * b /\ x <= (b / &2) pow 2 /\ y <= (b / &2) pow 2
      ==> x + y < b pow 2`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[IM_SUB; REAL_ARITH `&0 < b ==> abs(b / &2) = b / &2`] THEN
    ASM_SIMP_TAC[RE_SUB; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `--(x / &2) <= z ==> &2 * --z <= x`)) THEN
    ASM_SIMP_TAC[REAL_LE_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `v:complex`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&0 <= Re z)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?M. &0 < M /\
        !z. Re z >= --d /\ abs (Im z) <= R /\ Re(z) <= R
            ==> norm(f(w + z):complex) <= M`
  (X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2a"))) THENL
   [MP_TAC(ISPEC `IMAGE (\z. f (w + z):complex)
                        {z | Re z >= --d /\ abs (Im z) <= R /\ Re(z) <= R}`
                 COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP HOLOMORPHIC_ON_IMP_CONTINUOUS_ON) THEN
      MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
                        CONTINUOUS_ON_SUBSET) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `cball(Cx(&0),&2 * R + d)` THEN
      REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL; dist] THEN
      REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG; IN_ELIM_THM] THEN
      MP_TAC COMPLEX_NORM_LE_RE_IM THEN MATCH_MP_TAC MONO_FORALL THEN
      UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_ARITH `x <= Im z <=> Im z >= x`] THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_RE_LE; CLOSED_HALFSPACE_IM_LE;
                CLOSED_HALFSPACE_RE_GE; CLOSED_HALFSPACE_IM_GE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `M:real`; `R:real`] OVERALL_BOUND_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 / &3 * e * pi`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; PI_POS; REAL_ARITH `&0 < &2 / &3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "X")) THEN
  EXISTS_TAC `N0 + 2` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  REMOVE_THEN "X" (MP_TAC o SPEC `N:num`) THEN
  ASM_SIMP_TAC[ARITH_RULE `N0 + 2 <= N ==> N0 <= N`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(N = 0) /\ 1 < N` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN
  ABBREV_TAC `S_N(w) = vsum(1..N) (\n. a(n) / Cx(&n) cpow w)` THEN
  REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  ABBREV_TAC `r_N(w) = (f:complex->complex)(w) - S_N(w)` THEN
  ABBREV_TAC `A = partcirclepath(Cx(&0),R,--(pi / &2),pi / &2)` THEN
  SUBGOAL_THEN
   `valid_path A /\
    pathstart A = complex(&0,--R) /\
    pathfinish A = complex(&0,R) /\
    &0 < Re(winding_number(A,Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[VALID_PATH_PARTCIRCLEPATH] THEN
    REWRITE_TAC[PATHSTART_PARTCIRCLEPATH; PATHFINISH_PARTCIRCLEPATH] THEN
    REWRITE_TAC[CEXP_EULER; SIN_NEG; COS_NEG; SIN_PI2; COS_PI2;
                GSYM CX_SIN; GSYM CX_COS] THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; RE_II; IM_II; IM_MUL_CX; RE; IM] THEN
    REPEAT(CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC WINDING_NUMBER_PARTCIRCLEPATH_POS_LT THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0; COMPLEX_SUB_REFL] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image A SUBSET {z | Re(z) >= &0 /\ norm(z) = R}`
  ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    ASM_SIMP_TAC[PATH_IMAGE_PARTCIRCLEPATH; REAL_LT_IMP_LE; PI_POS;
                 REAL_ARITH `--p < p <=> &0 < p`; REAL_HALF] THEN
    REWRITE_TAC[SUBSET; COMPLEX_ADD_LID; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RE_MUL_CX; RE_CEXP] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; COMPLEX_NORM_CX; RE_MUL_II] THEN
    REWRITE_TAC[IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; real_ge] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REWRITE_TAC[IM_MUL_II; RE_CX] THEN ASM_SIMP_TAC[COS_POS_PI_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&0) IN path_image A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[IN_ELIM_THM; COMPLEX_NORM_0] THEN
    UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = linepath(complex(&0,R),complex(--d,R)) ++
                  linepath(complex(--d,R),complex(--d,--R)) ++
                  linepath(complex(--d,--R),complex(&0,--R))` THEN
  SUBGOAL_THEN
   `valid_path B /\
    ~(Cx(&0) IN path_image B) /\
    &0 < Re(winding_number(B,Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC WINDING_NUMBER_JOIN_POS_COMBINED THEN
           REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
                       PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
           CONJ_TAC) THEN
    (REWRITE_TAC[VALID_PATH_LINEPATH] THEN CONJ_TAC THENL
      [ALL_TAC;
       MATCH_MP_TAC WINDING_NUMBER_LINEPATH_POS_LT THEN
       REWRITE_TAC[complex_mul; RE; IM; RE_SUB; RE_CNJ; IM_SUB; IM_CNJ;
                   RE_CX; IM_CX] THEN
       CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
       ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH]]) THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH; segment; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_CMUL; RE_ADD; RE_CX; RE;
                            IM_CMUL; IM_ADD; IM_CX; IM] THEN
    REWRITE_TAC[REAL_ARITH `&0 = (&1 - u) * x + u * x <=> x = &0`] THEN
    ASM_SIMP_TAC[REAL_NEG_EQ_0; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart B = complex(&0,R) /\
    pathfinish B = complex(&0,--R)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image B SUBSET {z | --d <= Re z /\ Re(z) <= &0 /\ abs(Im z) <= R}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `convex {z | --d <= Re z /\ Re z <= &0 /\ abs (Im z) <= R}`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_BOUNDS_LE;
        SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[REWRITE_RULE[real_ge] CONVEX_HALFSPACE_RE_GE;
                  REWRITE_RULE[real_ge] CONVEX_HALFSPACE_IM_GE;
                  CONVEX_HALFSPACE_RE_LE; CONVEX_HALFSPACE_IM_LE];
      ALL_TAC] THEN
    EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC(SET_RULE
            `path_image(p1 ++ p2) SUBSET path_image p1 UNION path_image p2 /\
             path_image p1 SUBSET s /\ path_image p2 SUBSET s
             ==> path_image(p1 ++ p2) SUBSET s`) THEN
           REWRITE_TAC[PATH_IMAGE_JOIN_SUBSET] THEN CONJ_TAC) THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RE; IM] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < d`; `&0 < R`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `valid_path(A ++ B) /\
    pathstart(A ++ B) = complex(&0,--R) /\
    pathfinish(A ++ B) = complex(&0,--R) /\
    ~(Cx(&0) IN path_image(A ++ B))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATH_IMAGE_JOIN; IN_UNION; VALID_PATH_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `winding_number(A++B,Cx(&0)) = Cx(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_EQ_1 THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH; PATH_IMAGE_JOIN; IN_UNION;
                 WINDING_NUMBER_JOIN; REAL_LT_ADD; RE_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 /\ y < &1 ==> x + y < &2`) THEN
    CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LT_1 THENL
     [EXISTS_TAC `--Cx(&1)`; EXISTS_TAC `Cx(&1)`] THEN
    ASM_SIMP_TAC[] THEN (CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC]) THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_SUB_RZERO; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_MUL_RNEG; GSYM CX_MUL; RE_CX; IM_CX; RE_NEG] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    has_path_integral (Cx(&2) * Cx pi * ii * f(w))) (A ++ B)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) + z pow 2 / Cx(R) pow 2)`;
      `{z | Re(z) >= --d /\ abs(Im z) <= R}`;
      `A ++ B:real^1->complex`;
      `Cx(&0)`]
        CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_LID; CPOW_N] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; complex_div] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; complex_pow] THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&1) + Cx(&0) pow 2 * z = Cx(&1)`] THEN
    REWRITE_TAC[COMPLEX_MUL_RID] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      ASM_CASES_TAC `z = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(z = Cx(&0))` THEN REWRITE_TAC[] THEN
      ABBREV_TAC `wever = inv(Cx R pow 2)` THEN CONV_TAC COMPLEX_FIELD] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `abs(x) <= a <=> x >= --a /\ x <= a`] THEN
      REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_HALFSPACE_RE_GE] THEN
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_HALFSPACE_IM_GE; CONVEX_HALFSPACE_IM_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
      SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_ID;
               HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ADD] THEN
      REWRITE_TAC[holomorphic_on] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      EXISTS_TAC `clog(Cx(&N)) * Cx(&N) cpow z` THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT THEN
      ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `min d R:real` THEN
      ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN
      REWRITE_TAC[SUBSET; IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(n1) <= n /\ abs(n2) <= n
        ==>  n < min d R ==> n1 >= --d /\ abs n2 <= R`) THEN
      REWRITE_TAC[COMPLEX_NORM_GE_RE_IM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; VALID_PATH_IMP_PATH; UNION_SUBSET] THEN
    CONJ_TAC THEN  MATCH_MP_TAC(SET_RULE
     `~(x IN s) /\ s SUBSET t ==> s SUBSET (t DELETE x)`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MP_TAC COMPLEX_NORM_GE_RE_IM THEN MATCH_MP_TAC MONO_FORALL THEN
    UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_JOIN; IMP_CONJ] THEN
  REWRITE_TAC[path_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_fA:complex` (LABEL_TAC "fA")) THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_fB:complex` (LABEL_TAC "fB")) THEN
  SUBGOAL_THEN `integral_fA + integral_fB = Cx(&2) * Cx pi * ii * f(w:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A ++ B:real^1->complex`] THEN
    ASM_SIMP_TAC[HAS_PATH_INTEGRAL_JOIN];
    ALL_TAC] THEN
  ABBREV_TAC `A' = (--) o (A:real^1->complex)` THEN
  SUBGOAL_THEN
   `valid_path A' /\
    pathstart A' = complex(&0,R) /\
    pathfinish A' = complex(&0,--R) /\
    ~(Cx(&0) IN path_image A') /\
    &0 < Re(winding_number(A',Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN
    ASM_SIMP_TAC[VALID_PATH_NEGATEPATH; PATHSTART_NEGATEPATH;
                 PATHFINISH_NEGATEPATH; WINDING_NUMBER_NEGATEPATH;
                 PATH_IMAGE_NEGATEPATH] THEN
    REWRITE_TAC[IN_IMAGE; COMPLEX_RING `Cx(&0) = --x <=> x = Cx(&0)`] THEN
    ASM_REWRITE_TAC[UNWIND_THM2] THEN
    SIMP_TAC[COMPLEX_EQ; RE_NEG; IM_NEG; RE; IM; REAL_NEG_0; REAL_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `valid_path(A ++ A') /\
    pathstart(A ++ A') = complex(&0,--R) /\
    pathfinish(A ++ A') = complex(&0,--R) /\
    ~(Cx(&0) IN path_image(A ++ A')) /\
    path_image(A ++ A') = path_image A UNION path_image A'`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; IN_UNION;
                 PATH_IMAGE_JOIN; VALID_PATH_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image A' SUBSET {z | Re z <= &0 /\ norm z = R}`
  ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN REWRITE_TAC[path_image; IMAGE_o; SUBSET] THEN
    ONCE_REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[GSYM path_image] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> (!x. x IN t ==> P x) ==> (!x. x IN s ==> P x)`)) THEN
    REWRITE_TAC[IN_ELIM_THM; RE_NEG; NORM_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `winding_number(A++A',Cx(&0)) = Cx(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_EQ_1 THEN
    ASM_SIMP_TAC[VALID_PATH_IMP_PATH; IN_UNION;
                 VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 WINDING_NUMBER_JOIN; REAL_LT_ADD; RE_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 /\ y < &1 ==> x + y < &2`) THEN
    CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LT_1 THENL
     [EXISTS_TAC `--Cx(&1)`; EXISTS_TAC `Cx(&1)`] THEN
    ASM_SIMP_TAC[] THEN (CONJ_TAC THENL [CONV_TAC COMPLEX_FIELD; ALL_TAC]) THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_SUB_RZERO; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_MUL_RNEG; GSYM CX_MUL; RE_CX; IM_CX; RE_NEG] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. S_N (w + z) * Cx (&N) cpow z * (Cx (&1) + z pow 2 * inv (Cx R pow 2)))
    holomorphic_on (:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
      REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV;
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_CPOW_RIGHT; HOLOMORPHIC_ON_ID; CPOW_EQ_0;
          HOLOMORPHIC_ON_CONST; REAL_OF_NUM_EQ; HOLOMORPHIC_ON_MUL;
          ARITH_RULE `~(n = 0) <=> 1 <= n`;
          HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_POW; CX_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    has_path_integral (Cx(&2) * Cx pi * ii * S_N(w))) (A ++ A')`
  MP_TAC THENL
   [MP_TAC(ISPECL
     [`\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) + z pow 2 / Cx(R) pow 2)`;
      `cball(Cx(&0),R)`;
      `A ++ A':real^1->complex`;
      `Cx(&0)`]
      CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; INTERIOR_CBALL; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_LID; CPOW_N] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; complex_div] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; complex_pow] THEN
    REWRITE_TAC[COMPLEX_RING `Cx(&1) + Cx(&0) pow 2 * z = Cx(&1)`] THEN
    REWRITE_TAC[COMPLEX_MUL_RID] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      ASM_CASES_TAC `z = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(z = Cx(&0))` THEN REWRITE_TAC[] THEN
      ABBREV_TAC `wever = inv(Cx R pow 2)` THEN CONV_TAC COMPLEX_FIELD] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN  MATCH_MP_TAC(SET_RULE
     `~(x IN s) /\ s SUBSET t ==> s SUBSET (t DELETE x)`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_CBALL; dist; COMPLEX_SUB_LZERO;
             NORM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
  ASM_SIMP_TAC[PATH_INTEGRABLE_JOIN; IMP_CONJ] THEN
  REWRITE_TAC[path_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_sA:complex` (LABEL_TAC "sA")) THEN
  DISCH_THEN(X_CHOOSE_THEN `integral_sA':complex` (LABEL_TAC "sA'")) THEN
  SUBGOAL_THEN
   `integral_sA + integral_sA' = Cx(&2) * Cx pi * ii * S_N(w:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. S_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A ++ A':real^1->complex`] THEN
    ASM_SIMP_TAC[HAS_PATH_INTEGRAL_JOIN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. S_N(w - z) * Cx (&N) cpow (--z) * (Cx (&1) / z + z / Cx R pow 2))
     has_path_integral integral_sA') A`
  (LABEL_TAC "s'A") THENL
   [SUBGOAL_THEN `(A:real^1->complex) = (--) o (--) o A` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; COMPLEX_NEG_NEG]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_NEGATEPATH THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
     [GSYM COMPLEX_NEG_NEG] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_NEG THEN
    REMOVE_THEN "sA'" MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; COMPLEX_SUB_RNEG; COMPLEX_NEG_NEG] THEN
    REWRITE_TAC[complex_div; COMPLEX_INV_NEG; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[GSYM COMPLEX_NEG_ADD; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC[COMPLEX_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx(R) pow 2))
    path_integrable_on A`
  MP_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_SUB THEN
    REWRITE_TAC[path_integrable_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[path_integrable_on; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `integral_rA:complex` THEN DISCH_THEN(LABEL_TAC "rA") THEN
  SUBGOAL_THEN `integral_fA - integral_sA:complex = integral_rA`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN MAP_EVERY EXISTS_TAC
     [`\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `A:real^1->complex`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `r_N(w:complex) = ((integral_rA - integral_sA') + integral_fB) /
                      (Cx(&2) * Cx(pi) * ii)`
  SUBST1_TAC THENL
   [SIMP_TAC[COMPLEX_FIELD `~(z = Cx(&0)) ==> (x = y / z <=> z * x = y)`;
             CX_2PII_NZ] THEN
    REWRITE_TAC[GSYM(ASSUME `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; GSYM COMPLEX_MUL_ASSOC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
              COMPLEX_NORM_II; REAL_MUL_RID; REAL_ABS_PI; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; PI_POS; REAL_ARITH `&0 < &2 * p <=> &0 < p`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&4 * pi / R + &2 * pi / &N +
              &6 * M * R / (d * exp(d * log(&N))) +
              &4 * M / (R * log(&N)) pow 2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `&4 * pi / R <= &4 * pi * (e / &3) /\
      y < &2 / &3 * e * pi
      ==> &4 * pi / R + y < e * &2 * pi`) THEN
    ASM_SIMP_TAC[REAL_ARITH `abs x < e ==> x < e`] THEN
    SIMP_TAC[real_div; REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    EXPAND_TAC "R" THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x) <= &2 * a /\ norm(y) <= &2 * a + b /\ norm(z) <= c
    ==> norm(x - y + z) <= &4 * a + b + c`) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\z. r_N(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_rA:complex`; `Cx(&0)`; `R:real`; `--(pi / &2)`; `pi / &2`;
      `&2 / R pow 2`;
      `{complex(&0,R),complex(&0,--R)}`]
     HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_ARITH `p / &2 - --(p / &2) = p`; PI_POS_LE;
                REAL_ARITH `--(p / &2) <= (p / &2) <=> &0 <= p`] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(r = &0) ==> &2 / r pow 2 * r * x = &2 * x / r`;
                 REAL_LT_IMP_NZ] THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `norm(z) = R /\ &0 < Re z` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `path_image A SUBSET {z | Re z >= &0 /\ norm z = R}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
      ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[REAL_RING
       `&0 pow 2 + x pow 2 = y pow 2 <=> x = y \/ x = --y`] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(z = complex(&0,--R))` THEN
      UNDISCH_TAC `~(z = complex(&0,R))` THEN
      ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 / (Re z * exp(Re z * log(&N))) *
                exp(Re z * log(&N)) * (&2 * abs(Re z) / R pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&0 < z ==> abs z = z`] THEN
      ASM_SIMP_TAC[REAL_EXP_NZ; REAL_LE_REFL; REAL_FIELD
       `&0 < z /\ ~(e = &0)
        ==> &1 / (z * e) * e * &2 * z / R pow 2 = &2 / R pow 2`]] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL; NORM_CPOW_REAL; BOUND_LEMMA_1;
                   REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ]] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC
     `\n. vsum(1..n) (\n. a n / Cx (&n) cpow (w + z)) - S_N(w + z)` THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. (f:complex->complex) w - S_N w = r_N w`)] THEN
      MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
      MP_TAC(SPEC `w + z:complex` (ASSUME
      `!z. Re z > &1 ==> ((\n. a n / Cx(&n) cpow z) sums f z) (from 1)`)) THEN
      SIMP_TAC[RE_ADD; REAL_ARITH `&0 < z ==> &1 + z > &1`;
               ASSUME `Re w = &1`; ASSUME `&0 < Re z`] THEN
      REWRITE_TAC[sums; FROM_INTER_NUMSEG];
      ALL_TAC] THEN
    EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM(ASSUME
     `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vsum(N+1..n) (\n. a n / Cx(&n) cpow (w + z)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC BOUND_LEMMA_4 THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= N <=> ~(N = 0)`]] THEN
    MATCH_MP_TAC(NORM_ARITH `y + z = x ==> norm(x - y) <= norm(z)`) THEN
    MP_TAC(SPECL [`1`; `N:num`; `n:num`] NUMSEG_COMBINE_R) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(N = 0)`; `N + 1 <= n`] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VSUM_UNION THEN
    REWRITE_TAC[FINITE_NUMSEG; DISJOINT_NUMSEG] THEN ARITH_TAC;

    MP_TAC(ISPECL
     [`\z. S_N(w - z) * Cx(&N) cpow (--z) * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_sA':complex`; `Cx(&0)`; `R:real`; `--(pi / &2)`; `pi / &2`;
      `&2 / R pow 2 + &2 / (&N * R)`;
      `{complex(&0,R),complex(&0,--R)}`]
     HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `&0 < R /\ ~(N = &0)
      ==> (&2 / R pow 2 + &2 / (N * R)) * R * (p / &2 - --(p / &2)) =
          &2 * p / R + &2 * p / N`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL; REAL_POS;
                   REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PI_POS; REAL_ARITH `&0 < x ==> --(x / &2) <= x / &2`] THEN
    X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `norm(z) = R /\ &0 < Re z` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `path_image A SUBSET {z | Re z >= &0 /\ norm z = R}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
      ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[REAL_RING
       `&0 pow 2 + x pow 2 = y pow 2 <=> x = y \/ x = --y`] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(z = complex(&0,--R))` THEN
      UNDISCH_TAC `~(z = complex(&0,R))` THEN
      ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(exp (Re z * log (&N)) * (&1 / &N + &1 / Re z)) *
                inv(exp(Re z * log(&N))) * (&2 * abs(Re z) / R pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&0 < z ==> abs z = z`] THEN
      ASM_SIMP_TAC[REAL_EXP_NZ; REAL_FIELD
       `~(e = &0) ==> (e * x) * inv(e) * y = x * y`] THEN
      ASM_SIMP_TAC[REAL_FIELD
       `&0 < x ==> (n + &1 / x) * &2 * x / y = &2 / y + &2 * x * n / y`] THEN
      REWRITE_TAC[REAL_LE_LADD] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; LT_NZ;
       REAL_FIELD `&0 < n /\ &0 < r
                   ==> (&2 * z * &1 / n / r pow 2) * n * r = &2 * z / r`] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &2 * x <= &2`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
       `!w. vsum (1..N) (\n. a n / Cx (&n) cpow w) = S_N w`)] THEN
      MATCH_MP_TAC BOUND_LEMMA_3 THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; ARITH_RULE `1 <= N <=> ~(N = 0)`];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL; NORM_CPOW_REAL; BOUND_LEMMA_1;
                 REAL_CX; RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[RE_NEG; REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL];

    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
    path_integrable_on B`
  MP_TAC THENL
   [ASM_MESON_TAC[path_integrable_on]; ALL_TAC] THEN
  EXPAND_TAC "B" THEN
  SIMP_TAC[PATH_INTEGRABLE_JOIN; VALID_PATH_JOIN; PATHSTART_JOIN;
           PATHFINISH_JOIN; VALID_PATH_LINEPATH; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[path_integrable_on; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `integral_fC:complex` THEN DISCH_TAC THEN
  X_GEN_TAC `integral_fD:complex` THEN DISCH_TAC THEN
  X_GEN_TAC `integral_fC':complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `integral_fB:complex = integral_fC + integral_fD + integral_fC'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HAS_PATH_INTEGRAL_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `B:real^1->complex`] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
           ASM_SIMP_TAC[VALID_PATH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH;
             PATHFINISH_JOIN; VALID_PATH_LINEPATH; PATHSTART_LINEPATH]);
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y) <= a /\ norm(x) <= &2 * b /\ norm(z) <= &2 * b
    ==> norm(x + y + z) <= a + &4 * b`) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL
     [`\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2)`;
      `integral_fD:complex`;
      `complex (--d,R)`; `complex (--d,--R)`;
      `M * inv(exp(d * log(&N))) * &3 / d`]
     HAS_PATH_INTEGRAL_BOUND_LINEPATH) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC;
      SUBGOAL_THEN `complex (--d,--R) - complex (--d,R) =
                    Cx(&2) * ii * Cx(--R)`
      SUBST1_TAC THENL
       [REWRITE_TAC[COMPLEX_EQ; RE_SUB; IM_SUB; RE_MUL_CX; IM_MUL_CX;
                    RE_CX; IM_CX; RE_MUL_II; IM_MUL_II; RE; IM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs(--R) = R`; REAL_ABS_NUM] THEN
      CONV_TAC REAL_FIELD] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_EXP_POS_LE;
                   REAL_LE_DIV; REAL_POS];
      ALL_TAC] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Re z = --d` ASSUME_TAC THENL
     [UNDISCH_TAC `z IN segment[complex(--d,R),complex(--d,--R)]` THEN
      REWRITE_TAC[segment; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[RE_CMUL; RE_ADD; RE] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[complex(--d,R),complex(--d,--R)] SUBSET
                       {z | abs(Im z) <= R}`
    MP_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[REAL_ARITH `abs(x) <= r <=> x >= --r /\ x <= r`] THEN
      SIMP_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`;
          CONVEX_INTER; CONVEX_HALFSPACE_IM_LE; CONVEX_HALFSPACE_IM_GE] THEN
      REWRITE_TAC[SET_RULE `{a,b} SUBSET s <=> a IN s /\ b IN s`] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER; IM] THEN
      UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < R`; `&0 < d`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CPOW_REAL_REAL; NORM_CPOW_REAL; REAL_CX; RE_CX;
                   REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `Re z = --d` THEN
      ASM_REWRITE_TAC[RE_CX] THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; COMPLEX_FIELD
     `~(z = Cx(&0)) /\ ~(R = Cx(&0))
      ==> Cx(&1) / z + z / R pow 2 =
          (Cx(&1) + (z / R) pow 2) * inv(z)`] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(i) = &1 /\ norm(z) <= &2 ==> norm(i + z) <= &3`) THEN
      REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_POW; REAL_ABS_NUM] THEN
      REWRITE_TAC[COMPLEX_NORM_DIV; REAL_POW_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; COMPLEX_NORM_NZ; REAL_POW_LT;
                   CX_INJ; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
      ASM_REWRITE_TAC[COMPLEX_SQNORM] THEN
      MATCH_MP_TAC(REAL_ARITH
       `d pow 2 <= R pow 2 /\ i pow 2 <= R pow 2
        ==> --d pow 2 + i pow 2 <= &2 * R pow 2`) THEN
      ONCE_REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
      MAP_EVERY UNDISCH_TAC
       [`&0 < d`; `&0 < R`; `d <= R`; `abs(Im z) <= R`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(Re z)` THEN REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. --(inv(clog(Cx(&N)) pow 2)) * (Cx(&1) + z * clog(Cx(&N))) *
         Cx(&N) cpow (--z)`;
    `\z. z * Cx(&N) cpow (--z)`;
    `linepath(Cx(&0),Cx(d))`;
    `(:complex)`] PATH_INTEGRAL_PRIMITIVE) THEN
  REWRITE_TAC[VALID_PATH_LINEPATH; SUBSET_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_ADD_LID; COMPLEX_MUL_LNEG] THEN
    ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN `~(clog(Cx(&N)) = Cx(&0))` MP_TAC THENL
     [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ; CX_INJ] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[COMPLEX_NEG_0; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO;
              COMPLEX_ADD_RID] THEN
  REWRITE_TAC[COMPLEX_RING
   `--x * y - --x * z:complex = x * (z - y)`] THEN
  ASM_REWRITE_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ; complex_pow] THEN
  ASM_SIMP_TAC[CPOW_NEG; CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               LT_NZ; GSYM CX_LOG; GSYM CX_MUL; GSYM CX_INV;
               GSYM CX_ADD; GSYM CX_SUB; GSYM CX_POW] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 + d) = --d`] THEN
  ABBREV_TAC
   `integral_bound =
    inv(log(&N) pow 2) *
    (&1 - (&1 + d * log(&N)) * inv(exp(d * log (&N))))` THEN
  SUBGOAL_THEN
   `&0 <= integral_bound /\ integral_bound <= inv(log(&N) pow 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "integral_bound" THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_DIV2_EQ; REAL_LE_RDIV_EQ;
                 REAL_POW_LT; LOG_POS_LT; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_ARITH `&0 * x <= &1 - y /\ &1 - y <= &1 <=>
                            &0 <= y /\ y <= &1`] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_EXP_POS_LT] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_EXP_LE_X]] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; LOG_POS_LT; REAL_OF_NUM_LT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_PATH_INTEGRAL_COMPLEX_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&2) * Cx(M) / Cx(R) pow 2`) THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
   [UNDISCH_TAC
     `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
       has_path_integral integral_fC)
       (linepath (complex (&0,R),complex (--d,R)))`;
    UNDISCH_TAC
     `((\z. f(w + z) * Cx(&N) cpow z * (Cx(&1) / z + z / Cx R pow 2))
       has_path_integral integral_fC')
      (linepath (complex(--d,--R),complex(&0,--R)))`] THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL; VECTOR_DERIVATIVE_LINEPATH_AT] THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o C CONJ (ARITH_RULE `~(-- &1 = &0)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `vec 1:real^1` o
      MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
    REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG; VECTOR_NEG_0;
                VECTOR_ADD_LID; VECTOR_NEG_NEG; REAL_POW_ONE; REAL_INV_1] THEN
    REWRITE_TAC[VECTOR_ARITH `--x + y:real^1 = y - x`; VECTOR_SUB_REFL]] THEN
  (SUBGOAL_THEN
    `(!x. linepath(complex (&0,R),complex (--d,R)) x =
          ii * Cx(R) - Cx(d * drop x)) /\
     (!x. linepath(Cx (&0),Cx d) x = Cx(d * drop x)) /\
     (complex(--d,R) - complex(&0,R) = --Cx(d)) /\
     (!x. linepath(complex (--d,--R),complex(&0,--R)) (vec 1 - x) =
          --ii * Cx(R) - Cx(d * drop x)) /\
     (complex(&0,--R) - complex(--d,--R) = Cx(d))`
    (fun th -> REWRITE_TAC[th])
   THENL
    [REWRITE_TAC[linepath; COMPLEX_EQ; IM_CMUL; RE_CMUL; IM; RE; RE_SUB;
                 IM_SUB; IM_ADD; RE_ADD; RE_MUL_II; IM_MUL_II; RE_MUL_CX;
                 RE_II; IM_II; IM_MUL_CX; IM_CX; RE_CX; RE_NEG; IM_NEG;
                 DROP_SUB; DROP_VEC] THEN
     REAL_ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP
    (ONCE_REWRITE_RULE[TAUT `a /\ b /\ c /\ d /\ e ==> f <=>
                             c /\ d ==> a /\ b /\ e ==> f`]
       HAS_INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT)) THEN
   DISCH_THEN(MP_TAC o SPEC `1`) THEN REWRITE_TAC[GSYM RE_DEF] THEN
   ANTS_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
     REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV; RE_CX] THEN
     REWRITE_TAC[real_div; GSYM REAL_POW_INV; REAL_POW_MUL; REAL_INV_MUL] THEN
     MATCH_MP_TAC(REAL_ARITH
      `&0 <= (M * R) * (b - i) ==> (&2 * M * R) * i <= &2 * M * R * b`) THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
     ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_MUL; REAL_POW_LE; REAL_LE_INV_EQ;
                  REAL_LT_IMP_LE] THEN
     ASM_REWRITE_TAC[REAL_POW_INV]] THEN
   REWRITE_TAC[DIMINDEX_2; ARITH] THEN
   REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
   X_GEN_TAC `x:real` THEN STRIP_TAC THEN
   REWRITE_TAC[COMPLEX_NORM_MUL] THEN
   ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                CPOW_REAL_REAL; LT_NZ] THEN
   REWRITE_TAC[RE_MUL_II; RE_NEG; RE_II; RE_MUL_CX; RE_SUB; RE_CX; IM_CX] THEN
   REWRITE_TAC[REAL_MUL_LZERO; REAL_NEG_0; COMPLEX_SUB_RZERO;
               REAL_ARITH `&0 - d * x = --(d * x)`] THEN
   GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
    [GSYM CX_MUL; GSYM CX_INV; GSYM CX_POW; GSYM CX_DIV; RE_CX] THEN
   REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LE_RMUL_EQ;
                REAL_MUL_ASSOC] THEN
   GEN_REWRITE_TAC LAND_CONV
    [REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
   REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_MUL_LNEG] THEN
   ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_EXP_POS_LT] THEN
   REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
   ONCE_REWRITE_TAC[REAL_ARITH
    `&2 * M * r * d * x = M * (&2 * (d * x) * r)`] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE; GSYM real_div] THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[RE_MUL_II; IM_MUL_II; RE_SUB; IM_SUB; RE_CX; IM_CX;
                 COMPLEX_MUL_LNEG; RE_NEG; IM_NEG] THEN
     SUBGOAL_THEN `&0 <= d * x /\ d * x <= d * &1` MP_TAC THENL
      [ALL_TAC;
       MAP_EVERY UNDISCH_TAC [`&0 < d`; `d <= R`] THEN REAL_ARITH_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_LMUL_EQ];
     ALL_TAC] THEN
   MATCH_MP_TAC BOUND_LEMMA_2 THEN
   ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_MUL] THEN
   REWRITE_TAC[RE_MUL_II; IM_MUL_II; RE_SUB; IM_SUB; RE_CX; IM_CX;
               COMPLEX_MUL_LNEG; RE_NEG; IM_NEG] THEN
   UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(* The application is to any bounded a_n, not |a_n| <= 1, so...              *)
(* ------------------------------------------------------------------------- *)

let NEWMAN_INGHAM_THEOREM_BOUND = prove
 (`!f a b. &0 < b /\
           (!n. 1 <= n ==> norm(a(n)) <= b) /\
           f analytic_on {z | Re(z) >= &1} /\
           (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
           ==> !z. Re(z) >= &1
                   ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:complex. inv(Cx(b)) * f z`;
                 `\n:num. inv(Cx(b)) * a n`]
                NEWMAN_INGHAM_THEOREM) THEN
  ASM_SIMP_TAC[ANALYTIC_ON_MUL; ANALYTIC_ON_CONST] THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM complex_div] THEN ASM_SIMP_TAC[SERIES_COMPLEX_LMUL] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_INV] THEN
  REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div)] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ARITH `&0 < b ==> abs b = b`;
               REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `z:complex` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx b` o MATCH_MP SERIES_COMPLEX_LMUL) THEN
  ASM_SIMP_TAC[complex_div; COMPLEX_MUL_ASSOC; COMPLEX_MUL_RINV;
               CX_INJ; REAL_LT_IMP_NZ; COMPLEX_MUL_LID]);;

let NEWMAN_INGHAM_THEOREM_STRONG = prove
 (`!f a b. (!n. 1 <= n ==> norm(a(n)) <= b) /\
           f analytic_on {z | Re(z) >= &1} /\
           (!z. Re(z) > &1 ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1))
           ==> !z. Re(z) >= &1
                   ==> ((\n. a(n) / Cx(&n) cpow z) sums (f z)) (from 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC NEWMAN_INGHAM_THEOREM_BOUND THEN
  EXISTS_TAC `abs b + &1` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b + &1`]);;

(* ------------------------------------------------------------------------- *)
(* Newman's analytic function "f", re-using our "nearzeta" stuff.            *)
(* ------------------------------------------------------------------------- *)

let GENZETA_BOUND_LEMMA = prove
 (`!n s m. ~(n = 0) /\ &1 < Re s /\ n + 1 <= m
           ==> sum(n..m) (\x. norm(Cx(&1) / Cx(&x) cpow s))
                <= (&1 / &n + &1 / (Re s - &1)) * exp((&1 - Re s) * log(&n))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; MATCH_MP (ARITH_RULE `n + 1 <= m ==> n <= m`)
              (ASSUME `n + 1 <= m`)] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= a - x ==> x + y <= a`) THEN
  MP_TAC(SPECL
   [`\z. Cx(&1) / z cpow (Cx(Re s))`;
    `\z. Cx(&1) / ((Cx(&1) - (Cx(Re s))) * z cpow (Cx(Re s) - Cx(&1)))`;
    `n + 1`; `m:num`] SUM_INTEGRAL_UBOUND_DECREASING) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(n + &1) - &1 = n`] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN COMPLEX_DIFF_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
      STRIP_TAC THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM LT_NZ]) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
       [ASM_MESON_TAC[RE_CX; REAL_LT_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[CPOW_N; CPOW_SUB; COMPLEX_POW_1] THEN
      REWRITE_TAC[COMPLEX_ENTIRE; complex_div] THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
        ASM_REWRITE_TAC[COMPLEX_INV_EQ_0; CPOW_EQ_0; COMPLEX_SUB_0] THEN
        REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < x /\ &0 < y` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT; GSYM LT_NZ]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; RE_CX; REAL_CX; GSYM CX_DIV] THEN
    SIMP_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= s * (y - x) ==> --(s * y) <= --(s * x)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ a <= b ==> x <= a ==> y <= b`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0 < r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 COMPLEX_NORM_DIV; NORM_CPOW_REAL] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_DIV; RE_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[RE_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= --x /\ --y <= e ==> x - y <= e`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `n + 1 <= m ==> 0 < m`)) THEN
  ASM_SIMP_TAC[GSYM CX_SUB; CPOW_REAL_REAL; REAL_CX; RE_CX; COMPLEX_NORM_DIV;
               REAL_OF_NUM_LT; NORM_CPOW_REAL; LT_NZ] THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_DIV; RE_CX] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_INV_NEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_EXP_POS_LE; REAL_SUB_LE;
               REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_INV_MUL; GSYM REAL_EXP_NEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= n * e ==> i * e <= (n + i) * e - x`) THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_EXP_SUB; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LT_NZ; REAL_EXP_POS_LT;
   REAL_FIELD `&0 < x /\ &0 < z ==> inv(x) * x / z = inv(z)`] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG; REAL_LE_REFL]);;

let GENZETA_BOUND = prove
 (`!n s. ~(n = 0) /\ &1 < Re s
         ==> norm(genzeta n s) <=
                (&1 / &n + &1 / (Re s - &1)) * exp((&1 - Re s) * log(&n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\m. vsum(n..m) (\r. Cx(&1) / Cx(&r) cpow s)` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP GENZETA_CONVERGES) THEN
  SIMP_TAC[sums; FROM_INTER_NUMSEG; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  ASM_SIMP_TAC[GENZETA_BOUND_LEMMA]);;

let NEARZETA_BOUND_SHARP = prove
 (`!n s. ~(n = 0) /\ &0 < Re s
         ==> norm(nearzeta n s) <=
                  norm(s * (s - Cx(&1))) *
                  (&1 / &n + &1 / Re s) / exp(Re s * log(&n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
    `\m. vsum(n..m)
              (\r. (s - Cx(&1)) / Cx(&r) cpow s -
                   (Cx(&1) / Cx(&r) cpow (s - Cx(&1)) -
                    Cx(&1) / Cx(&(r + 1)) cpow (s - Cx(&1))))` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP NEARZETA_CONVERGES) THEN
  SIMP_TAC[sums; FROM_INTER_NUMSEG; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (n..m)
                (\r. norm(s * (s - Cx (&1)) / Cx(&r) cpow (s + Cx(&1))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC NEARZETA_BOUND_LEMMA THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `a / b = a * Cx(&1) / b`] THEN
  REWRITE_TAC[SUM_LMUL; COMPLEX_NORM_MUL; GSYM REAL_MUL_ASSOC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GENZETA_BOUND_LEMMA o lhand o snd) THEN
  ASM_REWRITE_TAC[RE_ADD; REAL_LT_ADDL; RE_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[REAL_ARITH `(x + &1) - &1 = x`;
              REAL_ARITH `(&1 - (s + &1)) * x = --(s * x)`] THEN
  REWRITE_TAC[real_div; REAL_EXP_NEG; REAL_LE_REFL]);;

let NEARZETA_BOUND = prove
 (`!n s. ~(n = 0) /\ &0 < Re s
         ==> norm(nearzeta n s)
                  <= ((norm(s) + &1) pow 3 / Re s) / exp (Re s * log (&n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NEARZETA_BOUND_SHARP) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_EXP_POS_LE; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_RING `(x pow 3):real = x * x * x`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LE_ADD; REAL_LE_INV_EQ;
               REAL_POS; REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LE_ADD; REAL_LE_INV_EQ;
               REAL_POS; REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(y) = b ==> norm(x - y) <= norm(x) + b`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a + y <= (x + &1) * y <=> a <= x * y`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1)` THEN
  ASM_SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[REAL_INV_1; GSYM real_div; REAL_LE_RDIV_EQ] THEN
  MP_TAC(SPEC `s:complex` COMPLEX_NORM_GE_RE_IM) THEN REAL_ARITH_TAC);;

let NEARNEWMAN_EXISTS = prove
 (`?f. !s. s IN {s | Re(s) > &1 / &2}
           ==> ((\p. clog(Cx(&p)) / Cx(&p) * nearzeta p s -
                     clog(Cx(&p)) / (Cx(&p) cpow s * (Cx(&p) cpow s - Cx(&1))))
                sums (f s)) {p | prime p} /\
               f complex_differentiable (at s)`,
  MATCH_MP_TAC SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_NEARZETA THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ARITH_TAC];
      ALL_TAC] THEN
    COMPLEX_DIFFERENTIABLE_TAC THEN
    ASM_SIMP_TAC[COMPLEX_ENTIRE; CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ;
                 COMPLEX_SUB_0; PRIME_IMP_NZ; PRIME_GE_2; CPOW_NUM_NE_1;
                 REAL_ARITH `&1 / &2 < x ==> &0 < x`];
    ALL_TAC] THEN
  X_GEN_TAC `s:complex` THEN STRIP_TAC THEN
  EXISTS_TAC `min (&1 / &2) ((Re s - &1 / &2) / &2)` THEN
  EXISTS_TAC `\p. Cx(&2 * (norm(s:complex) + &2) pow 3 + &2) *
                  clog(Cx(&p)) /
                  Cx(&p) cpow (Cx(&1 + (Re s - &1 / &2) / &4))` THEN
  EXISTS_TAC `5` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC SUMMABLE_SUBSET_COMPLEX THEN EXISTS_TAC `from 1` THEN
    SIMP_TAC[IN_FROM; SUBSET; IN_ELIM_THM; GSYM CX_LOG; CPOW_REAL_REAL;
             RE_CX; REAL_CX; REAL_OF_NUM_LT; LE_1; PRIME_IMP_NZ] THEN
    SIMP_TAC[GSYM CX_DIV; REAL_CX; RE_CX; LOG_POS; REAL_OF_NUM_LE;
             REAL_LE_DIV; REAL_EXP_POS_LE] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC
     `--(complex_derivative zeta (Cx(&1 + (Re s - &1 / &2) / &4)))` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
     [GSYM COMPLEX_NEG_NEG] THEN
    MATCH_MP_TAC SERIES_NEG THEN
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_ZETA_CONVERGES THEN
    REWRITE_TAC[RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `p:num` THENL
   [SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX; GSYM CX_LOG; REAL_OF_NUM_LT;
             LT_NZ; PRIME_IMP_NZ; GSYM CX_DIV; GSYM CX_MUL] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x + &2`) THEN
      MATCH_MP_TAC REAL_POW_LE THEN NORM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
                   PRIME_GE_2]];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  REWRITE_TAC[IN_BALL; REAL_LT_MIN; dist] THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= a * b /\ a * b <= abs a * b ==> x <= abs a * b`) THEN
  SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE; REAL_ABS_LE] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x) <= a /\ norm(y) <= b ==> norm(x - y) <= a + b`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CPOW_ADD; CX_ADD; CPOW_N; CX_INJ; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ; GSYM complex_div] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV] THEN
    REWRITE_TAC[COMPLEX_POW_1; real_div] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `x * a * b:real = a * x * b`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NEARZETA_BOUND o lhand o snd) THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b ==> c) ==> (a ==> b) ==> c`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
      MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y = x * &2 * y`] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE; REAL_LE_INV_EQ; REAL_LE_MUL;
                 REAL_LT_IMP_LE; REAL_POS; REAL_LE_ADD; GSYM REAL_INV_MUL;
                 REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_NORM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT; PRIME_IMP_NZ;
                 LT_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_ARITH `--(a * p) <= --(b * p) <=> b * p <= a * p`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
                 PRIME_GE_2] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!y:complex. norm(x) <= &2 * norm(y) /\ norm(y) <= a
                ==> norm(x) <= &2 * a`) THEN
  EXISTS_TAC `clog(Cx(&p)) / Cx(&p) cpow (z + z)` THEN CONJ_TAC THENL
   [REWRITE_TAC[CPOW_ADD; complex_div; COMPLEX_MUL_ASSOC; COMPLEX_INV_MUL] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    ONCE_REWRITE_TAC[COMPLEX_NORM_DIV] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_ARITH `&0 < x * inv(&2) <=> &0 < x`; COMPLEX_NORM_NZ] THEN
    ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ;
                 COMPLEX_VEC_0] THEN
    MATCH_MP_TAC(NORM_ARITH
     `&2 <= norm(a) /\ norm(b) = &1 ==> norm(a) * inv(&2) <= norm(a - b)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `5 <= p ==> 0 < p`] THEN
    SUBST1_TAC(SYM(MATCH_MP EXP_LOG (REAL_ARITH `&0 < &2`))) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 / &2 * log(&4)` THEN
    SIMP_TAC[REAL_ARITH `l <= &1 / &2 * x <=> &2 * l <= x`;
             GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; LOG_POS; REAL_OF_NUM_LE; ARITH;
                 LOG_MONO_LE_IMP; REAL_OF_NUM_LT;
                 ARITH_RULE `5 <= p ==> 4 <= p`] THEN
    MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; REAL_OF_NUM_LT;
               ARITH_RULE `5 <= p ==> 0 < p`] THEN
  REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_ARITH `--(a * p) <= --(b * p) <=> b * p <= a * p`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; ARITH_RULE `2 <= p ==> 1 <= p`;
               PRIME_GE_2] THEN
  MP_TAC(SPEC `s - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; RE_ADD] THEN ASM_REAL_ARITH_TAC);;

let nearnewman = new_specification ["nearnewman"] NEARNEWMAN_EXISTS;;

let [CONVERGES_NEARNEWMAN; COMPLEX_DIFFERENTIABLE_NEARNEWMAN] =
  CONJUNCTS(REWRITE_RULE[FORALL_AND_THM; IN_ELIM_THM; real_gt;
                         TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                nearnewman);;

let newman = new_definition
 `newman(s) = (nearnewman(s) - (complex_derivative zeta s / zeta s)) /
              (s - Cx(&1))`;;

(* ------------------------------------------------------------------------- *)
(* Careful correlation of singularities of the various functions.            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DERIVATIVE_ZETA = prove
 (`!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> complex_derivative zeta s =
                complex_derivative (nearzeta 1) s / (s - Cx(&1)) -
                (nearzeta 1 s + Cx(&1)) / (s - Cx(&1)) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] (GEN_ALL zeta);
              REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] (GEN_ALL genzeta)] THEN
  REWRITE_TAC[CPOW_1; complex_div; COMPLEX_MUL_LID; COMPLEX_INV_1] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. (nearzeta 1 s + Cx(&1)) * inv(s - Cx(&1))` THEN
  EXISTS_TAC `dist(Cx(&1),s)` THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`\z. nearzeta 1 z + Cx(&1)`; `complex_derivative(nearzeta 1) s`;
    `\z. inv(z - Cx(&1))`;
    `--Cx(&1) / (s - Cx(&1)) pow 2`;
    `s:complex`]
   HAS_COMPLEX_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMPLE_COMPLEX_ARITH_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    COMPLEX_DIFF_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
    CONV_TAC COMPLEX_FIELD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_ADD_RID] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE; ETA_AX] THEN
  MP_TAC(SPEC `1` HOLOMORPHIC_NEARZETA) THEN
  SIMP_TAC[ARITH; HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GSYM complex_differentiable; real_gt]);;

let ANALYTIC_ZETA_DERIVDIFF = prove
 (`?a. (\z. if z = Cx(&1) then a
            else (z - Cx(&1)) * complex_derivative zeta z -
                 complex_derivative zeta z / zeta z)
       analytic_on {s | Re(s) >= &1}`,
  EXISTS_TAC
   `complex_derivative
     (\z. (Cx(&1) - inv(nearzeta 1 z + Cx(&1))) *
          ((z - Cx(&1)) * complex_derivative (nearzeta 1) z -
           (nearzeta 1 z + Cx(&1)))) (Cx(&1))` THEN
  MATCH_MP_TAC POLE_THEOREM_ANALYTIC_0 THEN
  MAP_EVERY EXISTS_TAC
   [`\z. (Cx(&1) - inv(nearzeta 1 z + Cx(&1))) *
         ((z - Cx(&1)) * complex_derivative (nearzeta 1) z -
          (nearzeta 1 z + Cx(&1)))`;
    `Cx(&1)`] THEN
  SIMP_TAC[NEARZETA_1; ARITH] THEN
  REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_INV_1; COMPLEX_SUB_REFL;
              COMPLEX_MUL_LZERO] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ANALYTIC_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC ANALYTIC_ON_SUB THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_INV THEN
      ASM_SIMP_TAC[IN_ELIM_THM; real_ge; NEARZETA_NONZERO] THEN
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN REWRITE_TAC[ANALYTIC_ON_CONST; ETA_AX];
      MATCH_MP_TAC ANALYTIC_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC ANALYTIC_ON_MUL THEN
        SIMP_TAC[ETA_AX; ANALYTIC_ON_SUB; ANALYTIC_ON_CONST;
                 ANALYTIC_ON_ID] THEN MATCH_MP_TAC ANALYTIC_COMPLEX_DERIVATIVE;
        MATCH_MP_TAC ANALYTIC_ON_ADD THEN
        REWRITE_TAC[ANALYTIC_ON_CONST; ETA_AX]]] THEN
    MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN EXISTS_TAC `{s | Re(s) > &0}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[ETA_AX; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
             HOLOMORPHIC_NEARZETA; LE_REFL] THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_ELIM_THM; real_ge] THEN
    DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NEARZETA_NONZERO) THEN
    MP_TAC(ISPECL [`\z. nearzeta 1 z + Cx(&1)`; `z:complex`; `Cx(&0)`]
                CONTINUOUS_AT_AVOID) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_ADD THEN
      REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST; ETA_AX] THEN
      MP_TAC(SPEC `1` HOLOMORPHIC_NEARZETA) THEN
      SIMP_TAC[ARITH; HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT] THEN
      REWRITE_TAC[complex_differentiable; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
    REWRITE_TAC[BALL_MIN_INTER; IN_INTER; IN_BALL; REAL_LT_MIN] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < Re w` ASSUME_TAC THENL
     [MP_TAC(SPEC `z - w:complex` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB] THEN ASM_NORM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_DERIVATIVE_ZETA] THEN
    ASM_REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM] zeta; genzeta] THEN
    REWRITE_TAC[CPOW_1; COMPLEX_DIV_1] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(w = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD]);;

let ANALYTIC_NEWMAN_VARIANT = prove
 (`?c a. (\z. if z = Cx(&1) then a
              else newman z + complex_derivative zeta z + c * zeta z)
         analytic_on {s | Re(s) >= &1}`,
  X_CHOOSE_TAC `c:complex` ANALYTIC_ZETA_DERIVDIFF THEN
  EXISTS_TAC `--(c + nearnewman(Cx(&1)))` THEN
  EXISTS_TAC
   `complex_derivative
     (\z. nearnewman z +
          (if z = Cx(&1)
           then c
           else (z - Cx(&1)) * complex_derivative zeta z -
                complex_derivative zeta z / zeta z) +
           --(c + nearnewman (Cx(&1))) * (nearzeta 1 z + Cx(&1)))
     (Cx(&1))` THEN
  MATCH_MP_TAC POLE_THEOREM_ANALYTIC_0 THEN
  MAP_EVERY EXISTS_TAC
   [`\z. nearnewman z +
         (if z = Cx(&1) then c
          else (z - Cx(&1)) * complex_derivative zeta z -
               complex_derivative zeta z / zeta z) +
          --(c + nearnewman(Cx(&1))) * (nearzeta 1 z + Cx(&1))`;
    `Cx(&1)`] THEN
  SIMP_TAC[NEARZETA_1; LE_REFL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ANALYTIC_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN
      EXISTS_TAC `{s | Re(s) > &1 / &2}` THEN
      SIMP_TAC[SUBSET; IN_ELIM_THM; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
               HOLOMORPHIC_ON_OPEN; real_gt; GSYM complex_differentiable;
               COMPLEX_DIFFERENTIABLE_NEARNEWMAN] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ANALYTIC_ON_MUL THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_ADD THEN REWRITE_TAC[ANALYTIC_ON_CONST] THEN
      MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN EXISTS_TAC `{s | Re(s) > &0}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      SIMP_TAC[ETA_AX; ANALYTIC_ON_OPEN; OPEN_HALFSPACE_RE_GT;
               HOLOMORPHIC_NEARZETA; LE_REFL] THEN REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN REWRITE_TAC[newman] THEN
    GEN_REWRITE_TAC (funpow 4 RAND_CONV o ONCE_DEPTH_CONV) [zeta] THEN
    ASM_REWRITE_TAC[genzeta; CPOW_1; COMPLEX_DIV_1] THEN
    UNDISCH_TAC `~(w = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD;
    SIMPLE_COMPLEX_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Hence apply the analytic lemma.                                           *)
(* ------------------------------------------------------------------------- *)

let CONVERGES_NEWMAN_PRIME = prove
 (`!s. &1 < Re s
       ==> ((\p. clog(Cx(&p)) / Cx(&p) * genzeta p s) sums newman(s))
           {p | prime p}`,
  X_GEN_TAC `s:complex` THEN ASM_CASES_TAC `s = Cx(&1)` THEN
  ASM_REWRITE_TAC[RE_CX; REAL_LT_REFL; genzeta; newman] THEN
  DISCH_TAC THEN REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC SERIES_COMPLEX_RMUL THEN REWRITE_TAC[GSYM complex_div] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_LOGZETA'') THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_NEARNEWMAN o MATCH_MP
   (REAL_ARITH `&1 < x ==> &1 / &2 < x`)) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SERIES_ADD) THEN
  REWRITE_TAC[GSYM complex_sub] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC SUMS_IFF THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING
   `c - b = a * m ==> (a:complex) * n - b + c = a * (n + m)`) THEN
  ASM_SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ; complex_div] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_SUB_LDISTRIB] THEN
  AP_TERM_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID; GSYM COMPLEX_INV_MUL] THEN
  ASM_SIMP_TAC[CPOW_SUB; CPOW_N; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ] THEN
  REWRITE_TAC[COMPLEX_POW_1] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `~(ps = Cx(&1)) /\ ~(ps = Cx(&0)) /\ ~(p = Cx(&0))
    ==> inv(ps - Cx(&1)) - inv(ps * (ps - Cx(&1))) =
        inv(p * ps / p)`) THEN
  ASM_SIMP_TAC[CPOW_NUM_NE_1; PRIME_GE_2; REAL_ARITH `&1 < x ==> &0 < x`] THEN
  ASM_SIMP_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ; PRIME_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* Now swap the order of summation in the series.                            *)
(* ------------------------------------------------------------------------- *)

let GENZETA_OFFSET = prove
 (`!m n s. &1 < Re s /\ m <= n
           ==> genzeta m s - vsum(m..n) (\k. Cx(&1) / Cx(&k) cpow s) =
               genzeta (n + 1) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\k. Cx(&1) / Cx(&k) cpow s`; `from(n + 1)`] THEN
  ASM_SIMP_TAC[GENZETA_CONVERGES] THEN
  GEN_REWRITE_TAC (PAT_CONV `\n. (f sums (a - vsum(m..n) s)) k`)
   [ARITH_RULE `n = (n + 1) - 1`] THEN
  MATCH_MP_TAC SUMS_OFFSET THEN ASM_SIMP_TAC[GENZETA_CONVERGES] THEN
  ASM_ARITH_TAC);;

let NEWMAN_CONVERGES = prove
 (`!s. &1 < Re s
       ==> ((\n. vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) /
                 Cx(&n) cpow s)
            sums (newman s)) (from 1)`,
  let lemma = prove
   (`vsum (1..n) (\m. vsum {p | prime p /\ p <= m} (\p. f p m)) =
     vsum {p | prime p /\ p <= n} (\p. vsum (p..n) (\m. f p m))`,
    SIMP_TAC[VSUM_VSUM_PRODUCT; FINITE_NUMSEG; FINITE_ATMOST] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
    REPEAT(EXISTS_TAC `\(x:num,y:num). (y,x)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG; LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGES_NEWMAN_PRIME) THEN
  GEN_REWRITE_TAC LAND_CONV [sums] THEN
  SUBGOAL_THEN `!n. {p | prime p} INTER (0..n) = {p | prime p /\ p <= n}`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_NUMSEG; LE_0];
         ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  REWRITE_TAC[dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "0")) THEN
  SUBGOAL_THEN
   `((\n. Cx(&1 + &1 / (Re s - &1)) *
          (clog(Cx(&n)) + Cx(&24)) / Cx(&n) cpow (s - Cx(&1)))
     --> Cx(&0)) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM complex_div] THEN MATCH_MP_TAC LIM_LOG_OVER_POWER_N;
      MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN
      ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `inv x = Cx(&1) / x`] THEN
      MATCH_MP_TAC LIM_1_OVER_POWER] THEN
    REWRITE_TAC[RE_SUB; RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist; COMPLEX_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "1")) THEN
  EXISTS_TAC `N0 + N1 + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REMOVE_THEN "0" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x - y) <= e / &2 ==> norm(x - a) < e / &2 ==> norm(y - a) < e`) THEN
  SIMP_TAC[complex_div; GSYM VSUM_COMPLEX_RMUL; FINITE_ATMOST] THEN
  REWRITE_TAC[GSYM complex_div] THEN REWRITE_TAC[lemma] THEN
  SIMP_TAC[FINITE_ATMOST; GSYM VSUM_SUB] THEN SIMP_TAC[complex_div] THEN
  SIMP_TAC[COMPLEX_MUL_ASSOC; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN SIMP_TAC[GSYM complex_div] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `inv x = Cx(&1) / x`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(vsum {p | prime p /\ p <= n}
              (\p. clog(Cx(&p)) / Cx(&p) * genzeta (n + 1) s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; GENZETA_OFFSET];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_ATMOST] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= x ==> x < e ==> y <= e`) THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `a * b * c:complex = b * a * c`] THEN
  REWRITE_TAC[GSYM complex_div] THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `~(n = 0) /\ 1 <= n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MERTENS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `abs(x - y) <= e ==> &0 <= y ==> abs(x) <= y + e`)) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(REAL_ARITH
      `x' <= x /\ y' = y ==> abs x <= y ==> x' <= y'`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[GSYM CX_DIV; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x <= x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; LOG_POS; REAL_OF_NUM_LE; LE_1];
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LT_NZ] THEN
      REWRITE_TAC[GSYM CX_ADD; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS; LOG_POS; REAL_OF_NUM_LE; LE_1]];
    MP_TAC(SPECL [`n + 1`; `s:complex`] GENZETA_BOUND) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[complex_div; COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_DIV; REAL_POS; REAL_SUB_LE;
                 REAL_LT_IMP_LE; REAL_EXP_POS_LE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= &1 ==> a + b <= abs(&1 + b)`) THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_REAL; REAL_CX;
                 RE_CX; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE; RE_SUB; RE_CX] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - s) * l <= --((s - &1) * m) <=>
                            (s - &1) * m <= (s - &1) * l`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_SUB_LT] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LT; LT_NZ] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Hence the main result of the analytic part.                               *)
(* ------------------------------------------------------------------------- *)

let MAIN_RESULT = prove
 (`?c. summable (from 1)
        (\n. (vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) -
              clog(Cx(&n)) + c) / Cx(&n))`,
  MP_TAC ANALYTIC_NEWMAN_VARIANT THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:complex`; `singval:complex`] THEN DISCH_TAC THEN
  EXISTS_TAC `c:complex` THEN MP_TAC(SPECL
   [`\z. if z = Cx(&1) then singval
         else newman z + complex_derivative zeta z + c * zeta z`;
    `\n. vsum {p | prime p /\ p <= n} (\p. clog(Cx(&p)) / Cx(&p)) -
         clog(Cx(&n)) + c`;
    `&24 + norm(c:complex)`]
  NEWMAN_INGHAM_THEOREM_STRONG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN
    REWRITE_TAC[RE_CX; real_ge; REAL_LE_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUMS_SUMMABLE) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMMABLE_EQ) THEN
    SIMP_TAC[IN_FROM; CPOW_N; CX_INJ; REAL_OF_NUM_EQ] THEN
    SIMP_TAC[LE_1; COMPLEX_POW_1]] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x - y) <= &24 ==> norm(x - y + c) <= &24 + norm c`) THEN
    MP_TAC(SPEC `n:num` MERTENS) THEN ASM_SIMP_TAC[LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= a ==> y <= a`) THEN
    REWRITE_TAC[GSYM COMPLEX_NORM_CX] THEN AP_TERM_TAC THEN
    SIMP_TAC[GSYM VSUM_CX; CX_SUB; FINITE_ATMOST] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LE_1] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM CX_LOG; CX_DIV; REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_gt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[RE_CX; REAL_LT_REFL] THEN
  DISCH_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; COMPLEX_SUB_RDISTRIB] THEN
  REWRITE_TAC[COMPLEX_ADD_ASSOC] THEN MATCH_MP_TAC SERIES_ADD THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ZETA_CONVERGES) THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LID]] THEN
  REWRITE_TAC[complex_sub] THEN MATCH_MP_TAC SERIES_ADD THEN
  REWRITE_TAC[GSYM complex_div] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[COMPLEX_DERIVATIVE_ZETA_CONVERGES]] THEN
  ASM_SIMP_TAC[NEWMAN_CONVERGES]);;

(* ------------------------------------------------------------------------- *)
(* The theorem relating summability and convergence.                         *)
(* ------------------------------------------------------------------------- *)

let SUM_GOESTOZERO_LEMMA = prove
 (`!a M N.
        abs(sum(M..N) (\i. a(i) / &i)) <= d
        ==> 0 < M /\ M < N /\ (!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1))
            ==> a(M) <= d * &N / (&N - &M) + (&N - &M) / &M /\
                --a(N) <= d * &N / (&N - &M) + (&N - &M) / &M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT]) THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a. a <= b /\ x <= a /\ y <= a ==> x <= b /\ y <= b`) THEN
  EXISTS_TAC `d * &N / (&N - &M) + log(&N / &M)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < m /\ &0 < n
                             ==> n / m = &1 + (n - m) / m`] THEN
    MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_SUB_RADD] THEN
  SUBGOAL_THEN `!m n. &m <= &n ==> a m + log(&m) <= a n + log(&n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
    ASM_REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  CONJ_TAC THEN
  (MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(d * &N) / (&N - &M + &1)` THEN CONJ_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
     ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
     ASM_REAL_ARITH_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= y /\ (&0 <= x ==> x <= y) ==> x <= y`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `m < n ==> &0 < n - m + &1`;
               REAL_LE_DIV; REAL_LE_MUL; REAL_MUL_LZERO; REAL_POS] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x * y) * z:real = y * (x * z)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(sum(M..N) (\i. a(i) / &i))` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`);
    MATCH_MP_TAC(REAL_ARITH `a <= --x ==> x <= abs a`)] THEN
  (SUBGOAL_THEN `&N - &M + &1 = &((N + 1) - M)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM
                 REAL_OF_NUM_LE; REAL_ARITH `m < n ==> m <= n + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC]) THEN
  REWRITE_TAC[GSYM SUM_CONST_NUMSEG; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
  (SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG; REAL_NEG_SUB; REAL_SUB_RNEG] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `(a M - log(&N * inv(&M))) * inv(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; LOG_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x'. x' <= x /\ a - (x' - m) <= b ==> a - (x - m) <= b`) THEN
    EXISTS_TAC `log(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `a - (x - y) <= b <=> a + y <= b + x`];
    EXISTS_TAC `(log(&N * inv(&M)) + a N) * inv(&n)` THEN CONJ_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH `a * x <= a * y <=> --a * y <= --a * x`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_ARITH `--(x + y:real) = --y - x`] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; LOG_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x'. x <= x' /\ a <= y - x' + b ==> a <= y - x + b`) THEN
    EXISTS_TAC `log(&n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `a <= x - y + b <=> a + y <= b + x`]]);;

let SUM_GOESTOZERO_THEOREM = prove
 (`!a c. ((\i. a(i) / &i) real_sums c) (from 1) /\
         (!n. a(n) + log(&n) <= a(n + 1) + log(&n + &1))
         ==> (a ---> &0) sequentially`,
  let lemma = prove
   (`(!e. &0 < e /\ e < &1 / &4 ==> ?N:num. !n. N <= n ==> f(n) < e)
     ==> (!e. &0 < e ==> ?N. !n. N <= n ==> f(n) < e)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min e (&1 / &5)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[REAL_LT_MIN]) in
  REWRITE_TAC[LEFT_FORALL_IMP_THM; LEFT_EXISTS_AND_THM] THEN
  REWRITE_TAC[REAL_SERIES_CAUCHY] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC lemma THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(e / &8) pow 2`) THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `e / &4` REAL_ARCH_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * N0 + N1 + 7` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `&n * e / &4` FLOOR) THEN
  MP_TAC(SPEC `&n * e / &4` FLOOR_POS) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < k /\ 4 * k <= n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LT_NZ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&n * e / &4 < &0 + &1` THEN
      REWRITE_TAC[REAL_NOT_LT; REAL_ADD_LID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N1 * e / &4` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_NZ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_ARITH `&4 * x <= y <=> x <= y * inv(&4)`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n * e / &4` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_BOUNDS_LT] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n - k:num`; `n:num`]);
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `n + k:num`])] THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[FROM_INTER_NUMSEG_GEN] THEN
   COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
   DISCH_THEN(MP_TAC o MATCH_MP SUM_GOESTOZERO_LEMMA) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC])
  THENL
   [DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> --x <= a ==> --b < x`);
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> x <= a ==> x < b`)] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `4 * k <= n ==> k <= n`;
               GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `n - (n - k):real = k`;
              REAL_ARITH `(n + k) - n:real = k`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x < e / &2 /\ y < e / &2 ==> x + y < e`) THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH
   `(e / &8) pow 2 * x < e / &2 <=> e * e / &16 * x < e * &2`] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_SUB_LT; REAL_OF_NUM_LT;
               ARITH_RULE `0 < k /\ 4 * k <= n ==> k < n`;
               ARITH_RULE `~(n < 1) ==> 0 < n`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `n * e / &4 < k + &1 /\ &1 <= k ==> e / &16 * n < &2 * k`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&n * e / &4` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH
     `n * e / &4 < e / &2 * m <=> e * n < e * &2 * m`] THEN
    REWRITE_TAC[REAL_ARITH `n < &2 * (n - k) <=> &2 * k < n`] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `n * e / &4 < k + &1 /\ &1 <= k /\ (&1 / &4 + e / &16) * k < &1 * k
      ==> e / &16 * (n + k) < &2 * k`) THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_OF_NUM_LE; REAL_OF_NUM_LT;
                 ARITH_RULE `1 <= n <=> 0 < n`] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `k <= n * e / &4 /\ &0 < n * e ==> k < e / &2 * n`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT;
                 ARITH_RULE `~(n < 1) ==> 0 < n`]]);;

(* ------------------------------------------------------------------------- *)
(* Hence transform into the desired limit.                                   *)
(* ------------------------------------------------------------------------- *)

let MERTENS_LIMIT = prove
 (`?c. ((\n. sum {p | prime p /\ p <= n} (\p. log(&p) / &p) - log(&n))
        ---> c) sequentially`,
  X_CHOOSE_THEN `c:complex` MP_TAC MAIN_RESULT THEN
  REWRITE_TAC[summable] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `--Re(c)` THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MATCH_MP_TAC SUM_GOESTOZERO_THEOREM THEN EXISTS_TAC `Re l` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP REAL_SUMS_RE) THEN
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_SUMS_EQ) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RE_ADD; RE_DIV_CX; RE_SUB; REAL_SUB_RNEG] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; LE_1; RE_CX] THEN
    SIMP_TAC[RE_VSUM; FINITE_ATMOST] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; GSYM CX_LOG; REAL_OF_NUM_LT; PRIME_IMP_NZ; LT_NZ;
             GSYM CX_DIV; RE_CX];
    GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_ADD] THEN MATCH_MP_TAC(REAL_ARITH
     `s <= s' ==> (s - l - c) + l <= (s' - l' - c) + l'`) THEN
    MATCH_MP_TAC SUM_SUBSET THEN REWRITE_TAC[FINITE_ATMOST] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THENL
     [ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LOG_POS THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Reformulate the PNT using partial summation.                              *)
(* ------------------------------------------------------------------------- *)

let PNT_PARTIAL_SUMMATION = prove
 (`&(CARD {p | prime p /\ p <= n}) =
        sum(1..n)
         (\k. &k / log (&k) *
              (sum {p | prime p /\ p <= k} (\p. log (&p) / &p) -
               sum {p | prime p /\ p <= k - 1} (\p. log (&p) / &p)))`,
  REWRITE_TAC[PRIME_ATMOST_ALT] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  SIMP_TAC[GSYM SUM_CONST; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  SIMP_TAC[FINITE_NUMSEG; SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC (PAT_CONV `\x. l = a * (sum(1..x) f - s)`)
        [MATCH_MP (ARITH_RULE `1 <= p ==> p = SUC(p - 1)`) th]) THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= p ==> SUC(p - 1) = p`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  MATCH_MP_TAC(REAL_FIELD `&0 < x /\ &0 < y ==> &1 = x / y * y / x`) THEN
  ASM_SIMP_TAC[LOG_POS_LT; REAL_OF_NUM_LT; LE_1; PRIME_GE_2;
               ARITH_RULE `2 <= p ==> 1 < p`]);;

let SUM_PARTIAL_LIMIT = prove
 (`!f e c M.
        (!k. M <= k ==> &0 < f k) /\
        (!k. M <= k ==> f(k) <= f(k + 1)) /\
        ((\k. inv(f k)) ---> &0) sequentially /\
        (e ---> c) sequentially
        ==> ((\n. (sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
                  f(n + 1)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g") (LABEL_TAC "e")) THEN
  SUBGOAL_THEN `!k:num. M <= k ==> &0 <= f k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SIMP_TAC[tendsto_real] THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?N. (!k. N <= k ==> &0 < f k) /\
                    (!k. N <= k ==> f(k) <= f(k + 1)) /\
                    (!k. N <= k ==> abs(e k - c) < d / &4)`
   (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)
  THENL
   [USE_THEN "e" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `d / &4`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    ASM_MESON_TAC[ARITH_RULE `M + N <= (n:num) ==> M <= n /\ N <= n`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N + 1 <= n
        ==> abs((sum((N+1)..n) (\k. e k * (f (k + 1) - f k)) -
                 e(n) * f(n + 1)) +
                c * f(N + 1))
            <= d / &2 * f(n + 1)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\k. (e k - c:real) * (f (k + 1) - f k)`;
                   `\k. d / &4 * (f (k + 1) - f k)`;
                   `(N+1)..n`] SUM_ABS_LE) THEN
    REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ABS_MUL; ARITH_RULE `N + 1 <= n ==> N <= n`;
                   REAL_ARITH `a <= b ==> abs(b - a) = b - a`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_RULE `N + 1 <= n ==> N <= n`];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[SUM_SUB_NUMSEG] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUM_PARTIAL_SUC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
     [SUM_PARTIAL_SUC] THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= d * f1 /\ &0 <= dd /\ abs(en - cn) <= d / &4 * f1
      ==> abs(s - (cn - cN)) <= d / &4 * f1 - dd
          ==> abs(s - en + cN) <= d / &2 * f1`) THEN
    REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_SUB_RDISTRIB] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_DIV; REAL_LT_IMP_LE; REAL_OF_NUM_LT;
                 ARITH; LE_ADD; ARITH_RULE `N + 1 <= n ==> N <= n + 1`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_RULE `N + 1 <= n ==> N <= n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  USE_THEN "g" (MP_TAC o MATCH_MP REALLIM_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC
   `sum(1..N) (\k. e k * (f (k + 1) - f k)) - c * f(N + 1)`) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP REAL_SEQ_OFFSET) THEN
  REWRITE_TAC[REAL_MUL_RZERO; tendsto_real; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `d / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N + 1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `N + 1 <= n`)) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_ARITH `&0 < x ==> abs x = x`;
               ARITH_RULE `N + 1 <= n ==> N <= n + 1`; REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `1 <= N + 1 /\ N <= n` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
  REAL_ARITH_TAC);;

let SUM_PARTIAL_LIMIT_ALT = prove
 (`!f e b c M.
        (!k. M <= k ==> &0 < f k) /\
        (!k. M <= k ==> f(k) <= f(k + 1)) /\
        ((\k. inv(f k)) ---> &0) sequentially /\
        ((\n. f(n + 1) / f n) ---> b) sequentially /\
        (e ---> c) sequentially
        ==> ((\n. (sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
                  f(n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((sum(1..n) (\k. e(k) * (f(k + 1) - f(k))) - e(n) * f(n + 1)) /
         f(n + 1)) * (f(n + 1) / f(n))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `M:num` THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < a /\ &0 < b ==> x / b * b / a = x / a`;
                 ARITH_RULE `M <= n ==> M <= n + 1`];
    ALL_TAC] THEN
  SUBST1_TAC(REAL_ARITH `&0 = &0 * b`) THEN
  MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_PARTIAL_LIMIT THEN ASM_MESON_TAC[]);;

let REALLIM_NA_OVER_N = prove
 (`!a. ((\n. (&n + a) / &n) ---> &1) sequentially`,
  GEN_TAC THEN REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n:num. &1` THEN REWRITE_TAC[REALLIM_CONST] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N]]);;

let REALLIM_N_OVER_NA = prove
 (`!a. ((\n. &n / (&n + &1)) ---> &1) sequentially`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REALLIM_INV THEN
  REWRITE_TAC[REALLIM_NA_OVER_N] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let REALLIM_LOG1_OVER_LOG = prove
 (`((\n. log(&n + &1) / log(&n)) ---> &1) sequentially`,
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. &1 + log(&1 + &1 / &n) / log(&n)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LOG_POS_LT; REAL_ARITH `&2 <= x ==> &1 < x`;
       REAL_FIELD `&0 < x ==> (&1 + a / x = b / x <=> x + a = b)`] THEN
    ASM_SIMP_TAC[GSYM LOG_MUL; REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
                 REAL_LE_DIV; REAL_POS; REAL_ARITH `&2 <= x ==> &0 < x`] THEN
    AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. inv(&n)` THEN REWRITE_TAC[REALLIM_1_OVER_N] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_LE_INV_EQ; REAL_POS;
                 REAL_ARITH `&0 <= x ==> &1 <= &1 + x`] THEN
    MATCH_MP_TAC LOG_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * log(&2)` THEN
  CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC);;

let REALLIM_LOG_OVER_LOG1 = prove
 (`((\n. log(&n) / log(&n + &1)) ---> &1) sequentially`,
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REALLIM_INV THEN
  REWRITE_TAC[REALLIM_LOG1_OVER_LOG] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let ADHOC_BOUND_LEMMA = prove
 (`!k. 1 <= k ==> abs((&k + &1) * (log(&k + &1) - log(&k)) - &1)
                  <= &2 / &k`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`\n z. if n = 0 then clog z
           else if n = 1 then inv z
           else --inv(z pow 2)`;
    `Cx(&k + &1)`; `Cx(&k)`; `1`]
        COMPLEX_TAYLOR_MVT) THEN
  REWRITE_TAC[ARITH; ADD_EQ_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_DIV_1; complex_pow; COMPLEX_POW_1; COMPLEX_VEC_0] THEN
  REWRITE_TAC[GSYM CX_SUB; COMPLEX_ADD_RID;
              REAL_ARITH `k - (k + &1) = -- &1`] THEN
  REWRITE_TAC[CX_SUB; CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG;
              COMPLEX_NEG_NEG; COMPLEX_MUL_RID] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:complex`] THEN
    REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ARITH] THEN
    COMPLEX_DIFF_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; complex_div; COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX_GEN]) THEN
  STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &k /\ &0 < &k + &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[RE_ADD] THEN
  ONCE_REWRITE_TAC[REAL_RING `w:real = z + u <=> w - z = u`] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_INV; GSYM CX_ADD; GSYM CX_SUB;
               GSYM CX_NEG; RE_CX] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) (&k + &1)`) THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&0 < x ==> x * (y - (z + --inv x)) = &1 - x * (z - y)`] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
  REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_MUL; GSYM CX_POW; GSYM CX_INV; RE_CX] THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_POW_INV; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c * d = (a * b:real) * (c * d)`] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_LE_LDIV_EQ;
                 REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_REAL_ARITH_TAC);;

let REALLIM_MUL_SERIES = prove
 (`!x y z B.
        eventually (\n. &0 < x n) sequentially /\
        eventually (\n. &0 < y n) sequentially /\
        eventually (\n. &0 < z n) sequentially /\
        ((\n. inv(z n)) ---> &0) sequentially /\
        eventually (\n. abs(sum (1..n) x / z(n)) <= B) sequentially /\
        ((\n. y(n) / x(n)) ---> &0) sequentially
        ==> ((\n. sum (1..n) y / z(n)) ---> &0) sequentially`,
  REWRITE_TAC[CONJ_ASSOC; GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[tendsto_real] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ASSUME
   `eventually (\n. &0 < x n /\ &0 < y n /\ &0 < z n) sequentially`) THEN
  MP_TAC(ASSUME `((\n. y n / x n) ---> &0) sequentially`) THEN
  REWRITE_TAC[tendsto_real] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&2 * (&1 + abs B))`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_HALF; IMP_IMP; GSYM EVENTUALLY_AND] THEN
  GEN_REWRITE_TAC LAND_CONV [EVENTUALLY_SEQUENTIALLY] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `((\n. inv (z n)) ---> &0) sequentially`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_LMUL) THEN
  DISCH_THEN(MP_TAC o SPEC
   `e / (&2 * (&1 + abs B)) * abs(sum(1..N) x) + abs(sum(1..N) y)`) THEN
  REWRITE_TAC[REAL_MUL_RZERO; tendsto_real; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MP_TAC(ASSUME
   `eventually (\n. abs (sum (1..n) x / z n) <= B) sequentially`) THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `N + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= N + 1 /\ N <= n` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `!x. abs(x) / z(n:num) = abs(x / z n)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < n ==> abs n = n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n`];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM real_div] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!y'. abs(y) <= y' /\ abs(x) + y' < e ==> abs(x + y) < e`) THEN
  EXISTS_TAC `e / (&2 * (&1 + abs B)) * sum(N+1..n) x / z n` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ABS_MUL; REAL_ABS_INV;
                 REAL_ARITH `&0 < n ==> abs n = n`;
                 ARITH_RULE `N + 1 <= n ==> N <= n`;
                 REAL_LE_RMUL_EQ; REAL_LT_INV_EQ; REAL_MUL_ASSOC;
                 GSYM REAL_LE_LDIV_EQ] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x /\ abs x < y ==> x <= y`) THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV;
                 ARITH_RULE `N + 1 <= n ==> N <= n`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(d * abs xN + abs yN) < e / &2
    ==> d * abs xN = abs(d * xN) /\ abs(d * xN + xn) <= e / &2
        ==> abs(yN) + xn < e`)) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM;
              GSYM REAL_ADD_LDISTRIB; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < n ==> abs n = n`;
               REAL_ARITH `abs(&1 + abs B) = &1 + abs B`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(e * inv(&2) * i) * x = (e * inv(&2)) * x * i`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 + abs B`] THEN
  ASM_REAL_ARITH_TAC);;

let REALLIM_MUL_SERIES_LIM = prove
 (`!x y z l.
        eventually (\n. &0 < x n) sequentially /\
        eventually (\n. &0 < y n) sequentially /\
        eventually (\n. &0 < z n) sequentially /\
        ((\n. inv(z n)) ---> &0) sequentially /\
        ((\n. sum (1..n) x / z(n)) ---> l) sequentially /\
        ((\n. y(n) / x(n)) ---> &0) sequentially
        ==> ((\n. sum (1..n) y / z(n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_MUL_SERIES THEN
  EXISTS_TAC `x:num->real` THEN
  MP_TAC(MATCH_MP REAL_CONVERGENT_IMP_BOUNDED
   (ASSUME `((\n. sum (1..n) x / z n) ---> l) sequentially`)) THEN
  REWRITE_TAC[real_bounded] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[ALWAYS_EVENTUALLY; FORALL_IN_IMAGE; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Finally, the Prime Number Theorem!                                        *)
(* ------------------------------------------------------------------------- *)

let PNT = prove
 (`((\n. &(CARD {p | prime p /\ p <= n}) / (&n / log(&n)))
    ---> &1) sequentially`,
  REWRITE_TAC[PNT_PARTIAL_SUMMATION] THEN
  REWRITE_TAC[SUM_PARTIAL_PRE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; SUB_REFL; CONJUNCT1 LE] THEN
  SUBGOAL_THEN `{p | prime p /\ p = 0} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) *
         sum {p | prime p /\ p <= n} (\p. log(&p) / &p) -
         sum (1..n)
         (\k. sum {p | prime p /\ p <= k} (\p. log(&p) / &p) *
              ((&k + &1) / log(&k + &1) - &k / log(&k)))) / (&n / log(&n))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) * log(&n) -
         sum (1..n)
         (\k. log(&k) * ((&k + &1) / log(&k + &1) - &k / log(&k)))) /
        (&n / log(&n))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `(a * x - s) / b - (a * x' - s') / b:real =
      ((s' - s) - (x' - x) * a) / b`] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC SUM_PARTIAL_LIMIT_ALT THEN
    EXISTS_TAC `&1` THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    EXISTS_TAC `16` THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[MERTENS_LIMIT] THEN REWRITE_TAC[REAL_INV_DIV] THEN
    SIMP_TAC[REAL_LT_DIV; LOG_POS_LT; REAL_OF_NUM_LT;
             ARITH_RULE `16 <= n ==> 0 < n /\ 1 < n`] THEN
    REWRITE_TAC[REALLIM_LOG_OVER_N] THEN CONJ_TAC THENL
     [ALL_TAC;
      MP_TAC(CONJ REALLIM_LOG_OVER_LOG1 (SPEC `&1` REALLIM_NA_OVER_N)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP REALLIM_MUL) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_ADD_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
      REWRITE_TAC[REAL_MUL_AC]] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`\z. z / clog z`; `\z. inv(clog z) - inv(clog z) pow 2`;
                  `Cx(&n)`; `Cx(&n + &1)`]
                COMPLEX_MVT_LINE) THEN
    REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
    REWRITE_TAC[REAL_ARITH `~(n + &1 <= x /\ x <= n)`] THEN ANTS_TAC THENL
     [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
       [SUBGOAL_THEN `~(z = Cx(&0))` MP_TAC THENL
         [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
        REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
      REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_ARITH `&16 <= x ==> &0 < x`] THEN
      REWRITE_TAC[CX_INJ] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:complex`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
    REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&0 < Re z /\ &0 < &n /\ &0 < &n + &1` STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_POW; GSYM CX_INV; GSYM CX_SUB;
                 GSYM CX_DIV; RE_CX; GSYM CX_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_SUB; REAL_MUL_RID] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_ARITH `x pow 2 <= x <=> x * x <= x * &1`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC LOG_POS THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN ONCE_REWRITE_TAC[SUM_PARTIAL_SUC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. ((&n + &1) / log(&n + &1) * (log(&n) - log(&n + &1)) +
         sum(1..n) (\k. (&k + &1) / log(&k + &1) *
                        (log(&k + &1) - log(&k)))) / (&n / log(&n))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_OF_NUM_ADD; LOG_1; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_SEQ_OFFSET_REV THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC i`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `a * (x - y) + s + a * (y - x):real = s`] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC
   `\n. sum(1..n) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) /
        ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_STRADDLE THEN
    EXISTS_TAC `\n. ((&n + &2) / log (&n + &2) +
                   (sum(1..15) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) -
                      &17 / log (&17))) / ((&n + &1) / log (&n + &1))` THEN
    EXISTS_TAC `\n.  ((&n + &1) / log(&n + &1) +
                (sum(1..15) (\k. &1 / log(&k + &1) - &1 / log(&k + &1) pow 2) -
                      &16 / log (&16))) / ((&n + &1) / log (&n + &1))` THEN
    MP_TAC(GEN `n:num` (ISPECL
     [`\z. Cx(&1) / clog(z + Cx(&1)) - Cx(&1) / (clog(z + Cx(&1))) pow 2`;
      `\z. (z + Cx(&1)) / clog(z + Cx(&1))`;
      `16`; `n:num`]
     SUM_INTEGRAL_BOUNDS_DECREASING)) THEN
    MATCH_MP_TAC(MESON[]
     `(!n. P n ==> Q n) /\ ((!n. P n ==> R n) ==> s)
      ==> (!n. P n /\ Q n ==> R n) ==> s`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
        STRIP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        COMPLEX_DIFF_TAC THEN
        REWRITE_TAC[RE_ADD; RE_CX; GSYM CONJ_ASSOC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
         [SUBGOAL_THEN `~(z + Cx(&1) = Cx(&0))` MP_TAC THENL
           [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
          DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN SIMP_TAC[RE_ADD; RE_CX] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM real]) THEN
        REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[GSYM CX_ADD; GSYM CX_LOG; RE_CX; REAL_CX;
                     REAL_ARITH `&15 <= z ==> &0 < z + &1`; CX_INJ] THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&15 <= y` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM CX_ADD; GSYM CX_LOG; RE_CX;
                   REAL_ARITH `&15 <= x ==> &0 < x + &1`] THEN
      REWRITE_TAC[GSYM CX_DIV; GSYM CX_SUB; RE_CX; GSYM CX_POW] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_POW_INV] THEN
      REWRITE_TAC[REAL_ARITH
       `x - x pow 2 <= y - y pow 2 <=>
          (x + y) * (y - x) <= &1 * (y - x)`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= inv(&2) /\ y <= x
        ==> y + x <= &1 /\ &0 <= x - y`) THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
        CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_div];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `1 <= 15 + 1 /\ 15 <= n` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `16 <= n`)) THEN
      REWRITE_TAC[GSYM CX_ADD; REAL_ARITH `(n + &1) + &1 = n + &2`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; ARITH;
                   REAL_ARITH `&0 < &n + &1 /\ &0 < &n + &2`] THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MP_TAC(CONJ REALLIM_LOG_OVER_LOG1 (SPEC `&1` REALLIM_NA_OVER_N)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP REALLIM_MUL) THEN
        REWRITE_TAC[REAL_MUL_LID] THEN
        DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP REAL_SEQ_OFFSET) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_ADD_ASSOC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
        REWRITE_TAC[REAL_MUL_AC];
        ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[GSYM real_div; REAL_INV_DIV] THEN
      MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD];
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_div];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `1 <= 15 + 1 /\ 15 <= n` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[GSYM(MATCH_MP SUM_COMBINE_R th)]) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `16 <= n`)) THEN
      REWRITE_TAC[GSYM CX_ADD; REAL_ARITH `(n + &1) + &1 = n + &2`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[GSYM CX_LOG; REAL_OF_NUM_LT; ARITH;
                   REAL_ARITH `&0 < &n + &1 /\ &0 < &n + &2`] THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; GSYM CX_SUB; RE_CX] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
        EXISTS_TAC `\n:num. &1` THEN REWRITE_TAC[REALLIM_CONST] THEN
        REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN X_GEN_TAC `n:num` THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `&0 < log(&n + &1)` ASSUME_TAC THENL
         [ALL_TAC; POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD] THEN
        MATCH_MP_TAC LOG_POS_LT THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[GSYM real_div; REAL_INV_DIV] THEN
      MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. sum(1..n) (\k. &1 / log(&k + &1) pow 2 +
                                 &2 / (&k * log(&k + &1))) /
                  ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_INV_DIV; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ abs(a - b) <= y ==> abs(a - x - b) <= x + y`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `&1 / l - m1 / l * x:real = --((m1 * x - &1) / l)`] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; ADHOC_BOUND_LEMMA] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`; REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. sum(1..n) (\k. &3 / log(&k + &1) pow 2) /
                  ((&n + &1) / log(&n + &1))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_INV_DIV; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= y /\ y <= x
      ==> abs(&1 * x + &2 * y) <= &3 * x`) THEN
    SUBGOAL_THEN `&0 < log(&m + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_POW_2; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN MATCH_MP_TAC LOG_LE THEN
    REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC REALLIM_MUL_SERIES_LIM THEN
  MAP_EVERY EXISTS_TAC
   [`\n. &1 / log(&n + &1) - &1 / log(&n + &1) pow 2`; `&1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `16` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LID; REAL_SUB_LT] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN
    SUBGOAL_THEN `&1 < log(&n + &1)`
     (fun th -> SIMP_TAC[th; REAL_ARITH `&1 < x ==> &0 < x`; REAL_SUB_LT;
             REAL_LT_MUL; REAL_ARITH `x < x pow 2 <=> &0 < x * (x - &1)`]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_LT_INV_EQ; LOG_POS_LT; REAL_POW_LT;
             REAL_ARITH `&1 <= x ==> &1 < x + &1`; REAL_OF_NUM_LE];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    SIMP_TAC[REAL_LT_INV_EQ; LOG_POS_LT; REAL_POW_LT;
             REAL_ARITH `&1 <= x ==> &1 < x + &1`; REAL_OF_NUM_LE;
             REAL_LT_DIV; REAL_ARITH `&0 < &n + &1`];
    MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_LOG_OVER_N)) THEN
    REWRITE_TAC[REAL_INV_DIV; GSYM REAL_OF_NUM_ADD];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &2 / log(&n + &1)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    MP_TAC(SPEC `1` (MATCH_MP REAL_SEQ_OFFSET REALLIM_1_OVER_LOG)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD]] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `42` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 < log(&n + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&4 * log(&2)` THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_INV; REAL_ABS_POW;
               REAL_ARITH `&2 < x ==> abs x = x`] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_POW_LT;
               REAL_ARITH `&2 < x ==> &0 < x`] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&2 < l ==> (inv(l) * &2) * l pow 2 = inv(inv(&2 * l))`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_MUL; real_div; GSYM REAL_POW_INV; REAL_MUL_LID] THEN
  MATCH_MP_TAC(REAL_ARITH
   `l pow 2 <= l / &2
    ==> inv(&2) * l <= abs(l - l pow 2)`) THEN
  REWRITE_TAC[REAL_ARITH `l pow 2 <= l / &2 <=> &0 <= (&1 / &2 - l) * l`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_SUB_LE;
               ARITH_RULE `&2 < x ==> &0 <= x`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;
