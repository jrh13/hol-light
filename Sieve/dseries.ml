(* ========================================================================= *)
(* Dirichlet series dseries a s = sum_{n >= 1} a(n) n^-s.                    *)
(*                                                                           *)
(* dseries a s is infsum (from 1) (\n. a n / Cx(&n) cpow s), s complex.      *)
(* Two kinds of coefficients are treated.                                    *)
(*  * Bounded partial sums, |sum_{n<=K} a(n)| <= Q for all K: the series     *)
(*    converges for Re s > 0 (DSERIES_SUMS), with the tail bound             *)
(*      DSERIES_TAIL  |dseries a s - sum_{n<=M} a(n) n^-s|                   *)
(*                      <= Q (2 + |s| / Re s) M^-Re s                        *)
(*    (Abel summation VSUM_ABEL_COMPLEX and CPOW_DIFF_BOUND), so dseries a   *)
(*    is holomorphic on Re s > 0 (HOLOMORPHIC_DSERIES, a locally uniform     *)
(*    limit of partial sums: HOLOMORPHIC_UNIFORM_SEQUENCE).                  *)
(*  * Coefficients |a(n)| <= B (1 + log n)^k: absolute convergence on        *)
(*    Re s > 1 (DSERIES_SUMS_ABS), termwise derivatives                      *)
(*    (HAS_COMPLEX_DERIVATIVE_DSERIES, HIGHER_DSERIES), linearity            *)
(*    (DSERIES_ADD, DSERIES_LMUL, DSERIES_NEG), real nonnegative values      *)
(*    (DSERIES_REAL_NONNEG), |dseries a s| <= sum_n |a(n)| n^-Re s           *)
(*    (DSERIES_NORM_BOUND) and Dirichlet convolution (DSERIES_MUL).          *)
(* Completely multiplicative f with f(1) = 1 and |f| <= 1, on Re s > 1,      *)
(* D = dseries f:                                                            *)
(*   DSERIES_EXP            D(s) = cexp(dseries_log f s),                    *)
(*                          dseries_log f s = sum_n (Lambda(n) / log n) f(n) *)
(*                          n^-s,                                            *)
(*   DSERIES_NEG_LOG_DERIV  -D'(s) / D(s) = sum_n Lambda(n) f(n) n^-s,       *)
(* so D(s) <> 0 (DSERIES_NZ); LAMBDA_SERIES_BOUND bounds the partial sums    *)
(* of sum_n Lambda(n) |f(n)| n^-s for real s > 1.                            *)
(*                                                                           *)
(* Method for DSERIES_EXP: f * (Lambda f) = f log (DSERIES_LOG_DERIV_CONV,   *)
(* by complete multiplicativity and sum_{d | n} Lambda(d) = log n) and       *)
(* DSERIES_MUL give D' = D (dseries_log f)', so D cexp(-dseries_log f) has   *)
(* derivative 0 on the convex set Re s > 1; along s = m + 2 it tends to f(1) *)
(* = 1 (DSERIES_LIM_INFINITY).                                               *)
(* ========================================================================= *)

needs "Sieve/nt.ml";;
needs "100/pnt.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Complex powers of positive integers.                                      *)
(* ------------------------------------------------------------------------- *)

let NORM_CPOW_NUM = prove
 (`!n s. 1 <= n ==> norm(Cx(&n) cpow s) = &n rpow Re s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; rpow]);;

let CPOW_NUM_NZ = prove
 (`!n s. 1 <= n ==> ~(Cx(&n) cpow s = Cx(&0))`,
  REWRITE_TAC[CPOW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN ARITH_TAC);;

let CPOW_NUM_MUL = prove
 (`!m n s. Cx(&(m * n)) cpow s = Cx(&m) cpow s * Cx(&n) cpow s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  MATCH_MP_TAC CPOW_MUL_REAL THEN REWRITE_TAC[REAL_CX; RE_CX; REAL_POS]);;

let NORM_DIV_CPOW_NUM = prove
 (`!a n s. 1 <= n ==> norm(a / Cx(&n) cpow s) = norm a * &n rpow (--Re s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_NUM; RPOW_NEG; real_div]);;

let RPOW_NUM_POS = prove
 (`!n x. 1 <= n ==> &0 < &n rpow x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RPOW_POS_LT THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC);;

let RPOW_NUM_MONO = prove
 (`!m n x. 1 <= m /\ m <= n /\ &0 <= x ==> &n rpow (--x) <= &m rpow (--x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RPOW_NEG] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC RPOW_LE2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_POS]]);;

let RPOW_TELESCOPE_STEP = prove
 (`!n x. 2 <= n /\ &0 < x
         ==> x * &n rpow (--(x + &1)) <= &(n - 1) rpow (--x) - &n rpow (--x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < &n - &1 /\ &(n - 1) = &n - &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `2 <= n ==> 1 <= n`] THEN
    SUBGOAL_THEN `&2 <= &n` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[rpow] THEN
  ABBREV_TAC `ln = log(&n)` THEN ABBREV_TAC `lm = log(&n - &1)` THEN
  SUBGOAL_THEN `&1 / &n <= ln - lm:real` ASSUME_TAC THENL
   [MP_TAC(SPEC `--(&1 / &n):real` LOG_LE_STRONG) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 < &1 + --x <=> x < &1`] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 + --(&1 / &n) = (&n - &1) / &n:real` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_DIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--x * lm) = exp(--x * ln) * exp(x * (ln - lm)) /\
                exp(--(x + &1) * ln) = exp(--x * ln) * inv(&n:real)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "ln" THEN
    REWRITE_TAC[REAL_ARITH `--(x + &1) * l = --x * l + --l`] THEN
    REWRITE_TAC[REAL_EXP_ADD; REAL_EXP_NEG] THEN
    ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `x * (ln - lm):real` REAL_EXP_LE_X) THEN
  SUBGOAL_THEN `x * inv(&n) <= x * (ln - lm):real` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `--x * ln:real` REAL_EXP_POS_LT) THEN
  ABBREV_TAC `E = exp(--x * ln)` THEN
  ABBREV_TAC `F1 = exp(x * (ln - lm))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= E * (F1 - &1 - x * inv(&n:real))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let SUM_RPOW_TELESCOPE = prove
 (`!M N x. 1 <= M /\ M <= N /\ &0 < x
           ==> sum(M+1..N) (\n. &n rpow (--(x + &1))) <=
               (&M rpow (--x) - &N rpow (--x)) / x`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_ARITH_TAC; REPEAT STRIP_TAC] THEN
  ASM_CASES_TAC `M = SUC N` THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `n < n + 1`] THEN
    REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `M <= N:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `M <= N ==> M + 1 <= SUC N`] THEN
  MP_TAC(SPECL [`SUC N`; `x:real`] RPOW_TELESCOPE_STEP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC N - 1 = N`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
  UNDISCH_TAC `sum (M + 1..N) (\n. &n rpow --(x + &1)) <=
               (&M rpow --x - &N rpow --x) / x` THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

let SUM_RPOW_TAIL = prove
 (`!M N x. 1 <= M /\ &0 < x
           ==> sum(M+1..N) (\n. &n rpow (--(x + &1))) <= &M rpow (--x) / x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `M <= N:num` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&M rpow (--x) - &N rpow (--x)) / x` THEN
    ASM_SIMP_TAC[SUM_RPOW_TELESCOPE] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `a - b <= a <=> &0 <= b`] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC RPOW_NUM_POS THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `~(M <= N) ==> N < M + 1`] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC RPOW_NUM_POS THEN
    ASM_ARITH_TAC]);;

let CPOW_DIFF_BOUND = prove
 (`!n s. 1 <= n /\ &0 <= Re s
         ==> norm(Cx(&1) / Cx(&n) cpow s - Cx(&1) / Cx(&(n + 1)) cpow s)
             <= norm s * &n rpow (--(Re s + &1))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LID; GSYM CPOW_NEG] THEN
  MP_TAC(ISPECL [`\z. z cpow --s`; `\z. --s * z cpow (--s - Cx(&1))`;
                 `segment[Cx(&n),Cx(&(n + 1))]`;
                 `norm(s:complex) * &n rpow (--(Re s + &1))`]
         COMPLEX_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD] THEN STRIP_TAC THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_ADD]) THEN
      ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&1 <= Re z` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CPOW THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `z = Cx(Re z)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_NEG] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN `&0 < Re z` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX] THEN
    REWRITE_TAC[RE_SUB; RE_NEG; RE_CX] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[rpow] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_ARITH `(--s - &1) * l = --(s + &1) * l:real`] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_NEG2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`Cx(&n)`; `Cx(&(n + 1))`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `abs(n - (n + &1)) = &1`; REAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Bounded partial sums: convergence and holomorphy on Re s > 0.             *)
(* ------------------------------------------------------------------------- *)

let VSUM_ABEL_COMPLEX = prove
 (`!a b M N.
     M <= N
     ==> vsum(M+1..N) (\n. a n * b n) =
         vsum(1..N) a * b(N + 1) - vsum(1..M) a * b(M + 1) -
         vsum(M+1..N) (\n. vsum(1..n) a * (b(n + 1) - b n))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[VSUM_TRIV_NUMSEG; ARITH; COMPLEX_VEC_0] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `M = SUC N` THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VSUM_TRIV_NUMSEG; ARITH_RULE `n < n + 1`; COMPLEX_VEC_0] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `M + 1 <= SUC N` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC N`] THEN
  REWRITE_TAC[ADD1] THEN CONV_TAC COMPLEX_RING);;

let DSERIES_TAIL_FINITE = prove
 (`!a s Q M N.
     (!n. norm(vsum(1..n) a) <= Q) /\ &0 < Re s /\ 1 <= M
     ==> norm(vsum(M+1..N) (\n. a n / Cx(&n) cpow s))
         <= Q * (&2 + norm s / Re s) * &M rpow (--Re s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &M rpow (--Re s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_NUM_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `M <= N:num` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; ARITH_RULE `~(M <= N) ==> N < M + 1`;
                 NORM_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 + x`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE]] THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_MUL_LID] THEN
  REWRITE_TAC[GSYM complex_div; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC; COMPLEX_MUL_LID] THEN
  MP_TAC(ISPECL [`a:num->complex`; `\n. inv(Cx(&n) cpow s)`;
                 `M:num`; `N:num`] VSUM_ABEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!n. 1 <= n ==> norm(inv(Cx(&n) cpow s)) = &n rpow (--Re s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_NORM_INV; NORM_CPOW_NUM] THEN
    REWRITE_TAC[RPOW_NEG];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!x y z p1 p2 p3 e.
      norm(x:complex) <= p1 /\ norm(y:complex) <= p2 /\
      norm(z:complex) <= p3 /\ p1 + p2 + p3 <= e
      ==> norm(x - y - z) <= e`) THEN
  EXISTS_TAC `Q * &M rpow (--Re s)` THEN
  EXISTS_TAC `Q * &M rpow (--Re s)` THEN
  EXISTS_TAC `Q * (norm(s:complex) * &M rpow (--Re s) / Re s)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= N + 1`] THEN
    MATCH_MP_TAC RPOW_NUM_MONO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= M + 1`] THEN
    MATCH_MP_TAC RPOW_NUM_MONO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(M+1..N) (\n. Q * (norm(s:complex) *
                                       &n rpow (--(Re s + &1))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[NORM_POS_LE] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN
      MP_TAC(SPECL [`n:num`; `s:complex`] CPOW_DIFF_BOUND) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_ARITH_TAC;
                      ALL_TAC] THEN
      REWRITE_TAC[complex_div; COMPLEX_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC SUM_RPOW_TAIL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < Re s` THEN
    CONV_TAC REAL_FIELD]);;

let dseries = new_definition
 `dseries (a:num->complex) s = infsum (from 1) (\n. a n / Cx(&n) cpow s)`;;

let RPOW_NEG_EVENTUALLY_LT = prove
 (`!x e. &0 < x /\ &0 < e ==> ?N. 1 <= N /\ !n. N <= n ==> &n rpow (--x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `exp(--(log e) / x)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0 + 1` THEN
  REWRITE_TAC[ARITH_RULE `1 <= N0 + 1`] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(--(log e) / x) < &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N0` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `exp(--(log e) / x)` THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[rpow] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < e`))] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT] THEN
  SUBGOAL_THEN `--(log e) / x < log(&n)` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC);;

let DSERIES_SUMS = prove
 (`!a s Q. (!n. norm(vsum(1..n) a) <= Q) /\ &0 < Re s
           ==> ((\n. a n / Cx(&n) cpow s) sums dseries a s) (from 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dseries; SUMS_INFSUM] THEN
  REWRITE_TAC[summable; SERIES_CAUCHY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `Kc = Q * (&2 + norm(s:complex) / Re s) + &1` THEN
  SUBGOAL_THEN `&0 < Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 + x`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`Re s`; `e / Kc:real`] RPOW_NEG_EVENTUALLY_LT) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N + 1` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  REWRITE_TAC[GE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `from 1 INTER (m..n) = (m - 1) + 1..n` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_FROM; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num->complex`; `s:complex`; `Q:real`; `m - 1`;
                 `n:num`] DSERIES_TAIL_FINITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y < e ==> x <= y ==> x < e`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `Kc * &(m - 1) rpow (--Re s)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Kc" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC RPOW_NUM_POS THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

let DSERIES_TAIL = prove
 (`!a s Q M. (!n. norm(vsum(1..n) a) <= Q) /\ &0 < Re s /\ 1 <= M
             ==> norm(dseries a s - vsum(1..M) (\n. a n / Cx(&n) cpow s))
                 <= Q * (&2 + norm s / Re s) * &M rpow (--Re s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num->complex`; `s:complex`; `Q:real`] DSERIES_SUMS) THEN
  ASM_REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\N. vsum(1..N) (\n. a n / Cx(&n) cpow s) -
                  vsum(1..M) (\n. a n / Cx(&n) cpow s)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `M:num` THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= M + 1`] THEN
  REWRITE_TAC[VECTOR_ARITH `(x + y) - x:real^N = y`] THEN
  MATCH_MP_TAC DSERIES_TAIL_FINITE THEN ASM_REWRITE_TAC[]);;

let HOLOMORPHIC_DSERIES_TERM = prove
 (`!a n. 1 <= n ==> (\s. a / Cx(&n) cpow s) holomorphic_on (:complex)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_CONST; CPOW_NUM_NZ] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_CPOW_RIGHT THEN
  REWRITE_TAC[HOLOMORPHIC_ON_ID]);;

let HOLOMORPHIC_DSERIES_PARTIAL = prove
 (`!a N s. (\s. vsum(1..N) (\n. a n / Cx(&n) cpow s)) holomorphic_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
  ASM_SIMP_TAC[HOLOMORPHIC_DSERIES_TERM; SUBSET_UNIV]);;

let HOLOMORPHIC_DSERIES = prove
 (`!a Q. (!n. norm(vsum(1..n) a) <= Q)
         ==> (dseries a) holomorphic_on {s | Re s > &0}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_UNIFORM_SEQUENCE THEN
  EXISTS_TAC `\N s. vsum(1..N) (\n. a n / Cx(&n) cpow s)` THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT; HOLOMORPHIC_DSERIES_PARTIAL] THEN
  X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
  DISCH_TAC THEN EXISTS_TAC `Re x / &2` THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  SUBGOAL_THEN `!y. y IN cball(x,Re x / &2)
                    ==> Re x / &2 <= Re y /\ norm y <= norm x + Re x / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_CBALL; dist] THEN
    MP_TAC(SPEC `x - y:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:complex`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  ABBREV_TAC `Kc = Q * (&2 + (norm(x:complex) + Re x / &2) / (Re x / &2)) +
                   &1` THEN
  SUBGOAL_THEN `&0 < Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1:real`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 + x:real`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    MP_TAC(ISPEC `x:complex` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`Re x / &2`; `e / Kc:real`] RPOW_NEG_EVENTUALLY_LT) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N0:num` THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `y:complex` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:complex`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN
  MP_TAC(SPECL [`a:num->complex`; `y:complex`; `Q:real`; `N:num`]
    DSERIES_TAIL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y < e ==> x <= y ==> x < e:real`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `Kc * &N rpow (--(Re x / &2))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 + x:real`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "Kc" THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1:real`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_LADD] THEN
      MATCH_MP_TAC REAL_LE_DIV_BOTH THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC RPOW_NUM_POS THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[RPOW_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_NUM_POS THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Polylogarithmic coefficients: the half-plane Re s > 1.                    *)
(* ------------------------------------------------------------------------- *)

let LOG_POW_RPOW_BOUND = prove
 (`!n k d. 1 <= n /\ &0 < d
           ==> (&1 + log(&n)) pow k <= (&k / d) pow k * exp d * &n rpow d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n /\ &0 <= log(&n)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
                    MATCH_MP_TAC LOG_POS THEN
                    ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp d * &n rpow d = exp(d * (&1 + log(&n)))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[rpow; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    MP_TAC(SPEC `d * (&1 + log(&n)):real` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `&0 <= d * (&1 + log(&n))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `d * (&1 + log(&n))`] EXP_GE_POW) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + log(&n)) pow k =
                (&k / d) pow k * ((d * (&1 + log(&n))) / &k) pow k`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC]);;

let DSERIES_DOMINATION = prove
 (`!a B k s t n. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
                 &1 < t /\ t <= Re s /\ 1 <= n
                 ==> norm(a n / Cx(&n) cpow s) <=
                     B * (&k / ((t - &1) / &2)) pow k *
                     exp((t - &1) / &2) *
                     inv(&n rpow ((t + &1) / &2))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NORM_DIV_CPOW_NUM] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[LOG_1; REAL_ADD_RID; REAL_POW_ONE; REAL_MUL_RID] THEN
    MP_TAC(ISPEC `(a:num->complex) 1` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(B * (&1 + log(&n)) pow k) * &n rpow --t` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; RPOW_NUM_POS; NORM_POS_LE] THEN
    MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `k:num`; `(t - &1) / &2`] LOG_POW_RPOW_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&k / ((t - &1) / &2)) pow k * exp((t - &1) / &2) *
               &n rpow ((t - &1) / &2)) * &n rpow --t` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; RPOW_NUM_POS];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RPOW_ADD; GSYM RPOW_NEG] THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

let DSERIES_ABS_SUMMABLE = prove
 (`!a B k s. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
             &1 < Re s
             ==> summable (from 1) (\n. a n / Cx(&n) cpow s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n. B * (&k / ((Re s - &1) / &2)) pow k *
                  exp((Re s - &1) / &2) *
                  inv(&n rpow ((Re s + &1) / &2))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_SUMMABLE] THEN
    REPEAT(MATCH_MP_TAC REAL_SUMMABLE_LMUL) THEN
    MATCH_MP_TAC REAL_SUMMABLE_ZETA THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `1` THEN REWRITE_TAC[IN_FROM; GE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DSERIES_DOMINATION THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let DSERIES_SUMS_ABS = prove
 (`!a B k s. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
             &1 < Re s
             ==> ((\n. a n / Cx(&n) cpow s) sums dseries a s) (from 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dseries; SUMS_INFSUM] THEN
  MATCH_MP_TAC DSERIES_ABS_SUMMABLE THEN ASM_MESON_TAC[]);;

let HAS_COMPLEX_DERIVATIVE_DSERIES_TERM = prove
 (`!a n s. 1 <= n
           ==> ((\s. a / Cx(&n) cpow s) has_complex_derivative
                --(Cx(log(&n)) * a) / Cx(&n) cpow s) (at s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `clog(Cx(&n)) = Cx(log(&n))` ASSUME_TAC THENL
   [MATCH_MP_TAC(GSYM CX_LOG) THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  COMPLEX_DIFF_TAC THEN
  ASM_SIMP_TAC[CPOW_NUM_NZ; CX_INJ; REAL_OF_NUM_EQ;
               ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
  MP_TAC(SPECL [`n:num`; `s:complex`] CPOW_NUM_NZ) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC COMPLEX_FIELD);;

let DSERIES_DERIV_COEFF_BOUND = prove
 (`!a B k. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k)
           ==> !n. 1 <= n ==> norm(--(Cx(log(&n)) * a n))
                              <= B * (&1 + log(&n)) pow (k + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log(&n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[LOG_1; REAL_ADD_RID; REAL_POW_ONE; REAL_MUL_RID] THEN
    MP_TAC(ISPEC `(a:num->complex) 1` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_POW_ADD;
              REAL_POW_1] THEN
  ASM_SIMP_TAC[REAL_ABS_REFL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `B * x * y = y * B * x:real`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_COMPLEX_DERIVATIVE_DSERIES = prove
 (`!a B k s. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
             &1 < Re s
             ==> (dseries a has_complex_derivative
                  dseries (\n. --(Cx(log(&n)) * a n)) s) (at s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n s. (a:num->complex) n / Cx(&n) cpow s`;
                 `\n s. --(Cx(log(&n)) * (a:num->complex) n) / Cx(&n) cpow s`;
                 `{s | Re s > &1}`; `from 1`]
         SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX) THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM; IN_FROM; real_gt] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DSERIES_TERM THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    ABBREV_TAC `t = (Re x + &1) / &2` THEN
    EXISTS_TAC `(Re x - &1) / &2` THEN
    EXISTS_TAC `\n. Cx(B * (&k / ((t - &1) / &2)) pow k *
                       exp((t - &1) / &2) *
                       inv(&n rpow ((t + &1) / &2)))` THEN
    EXISTS_TAC `1` THEN REWRITE_TAC[REAL_CX; RE_CX] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM(REWRITE_RULE[o_DEF] REAL_SUMMABLE_COMPLEX)] THEN
      REPEAT(MATCH_MP_TAC REAL_SUMMABLE_LMUL) THEN
      MATCH_MP_TAC REAL_SUMMABLE_ZETA THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[LE_REFL] THEN
        REWRITE_TAC[LOG_1; REAL_ADD_RID; REAL_POW_ONE; REAL_MUL_RID] THEN
        MP_TAC(ISPEC `(a:num->complex) 1` NORM_POS_LE) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`n:num`; `y:complex`] THEN
      REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y:real`) THEN
      MATCH_MP_TAC DSERIES_DOMINATION THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `x - y:complex` COMPLEX_NORM_GE_RE_IM) THEN
      UNDISCH_TAC `dist(x:complex,y) < (Re x - &1) / &2` THEN
      REWRITE_TAC[dist; RE_SUB] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->complex`
    (X_CHOOSE_TAC `g':complex->complex`)) THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`g:complex->complex`; `Re s - &1`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  SUBGOAL_THEN `!y. &1 < Re y ==> g y = dseries a y` ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC SERIES_UNIQUE THEN
    EXISTS_TAC `\n. (a:num->complex) n / Cx(&n) cpow y` THEN
    EXISTS_TAC `from 1` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:complex`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC DSERIES_SUMS_ABS THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `y - s:complex` COMPLEX_NORM_GE_RE_IM) THEN
    UNDISCH_TAC `dist(y:complex,s) < Re s - &1` THEN
    REWRITE_TAC[dist; RE_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `g' (s:complex) = dseries (\n. --(Cx(log(&n)) * a n)) s`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC SERIES_UNIQUE THEN
    EXISTS_TAC `\n. --(Cx(log(&n)) * (a:num->complex) n) / Cx(&n) cpow s` THEN
    EXISTS_TAC `from 1` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:complex`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC DSERIES_SUMS_ABS THEN
      MAP_EVERY EXISTS_TAC [`B:real`; `k + 1`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DSERIES_DERIV_COEFF_BOUND THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `s:complex`) THEN ASM_SIMP_TAC[]]);;

let HOLOMORPHIC_DSERIES_ABS = prove
 (`!a B k. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k)
           ==> (dseries a) holomorphic_on {s | Re s > &1}`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_HALFSPACE_RE_GT; IN_ELIM_THM;
   real_gt] THEN
  X_GEN_TAC `s:complex` THEN DISCH_TAC THEN
  EXISTS_TAC `dseries (\n. --(Cx(log(&n)) * a n)) s` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DSERIES THEN ASM_MESON_TAC[]);;

let HIGHER_DSERIES_COEFF_BOUND = prove
 (`!a B k m. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k)
             ==> !n. 1 <= n ==> norm((--Cx(log(&n))) pow m * a n)
                                <= B * (&1 + log(&n)) pow (k + m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log(&n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[LOG_1; REAL_ADD_RID; REAL_POW_ONE; REAL_MUL_RID] THEN
    MP_TAC(ISPEC `(a:num->complex) 1` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; NORM_NEG; COMPLEX_NORM_CX;
              REAL_POW_ADD] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `B * x * y = y * B * x:real`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

let HIGHER_DSERIES = prove
 (`!a B k m s. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
               &1 < Re s
               ==> higher_complex_derivative m (dseries a) s =
                   dseries (\n. (--Cx(log(&n))) pow m * a n) s`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[higher_complex_derivative] THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_LID; ETA_AX];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[higher_complex_derivative] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `complex_derivative
                (dseries (\n. (--Cx(log(&n))) pow m * a n)) s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `{s | Re s > &1}` THEN
    REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE THEN
      REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN
      MATCH_MP_TAC HOLOMORPHIC_DSERIES_ABS THEN ASM_MESON_TAC[];
      MATCH_MP_TAC HOLOMORPHIC_DSERIES_ABS THEN
      MAP_EVERY EXISTS_TAC [`B:real`; `k + m:num`] THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HIGHER_DSERIES_COEFF_BOUND THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM; real_gt];
      REWRITE_TAC[IN_ELIM_THM; real_gt] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. (--Cx(log(&n))) pow m * (a:num->complex) n`;
                 `B:real`; `k + m:num`; `s:complex`]
    HAS_COMPLEX_DERIVATIVE_DSERIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HIGHER_DSERIES_COEFF_BOUND THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[complex_pow] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC COMPLEX_RING);;

let DSERIES_ADD = prove
 (`!a b B k s. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
               (!n. 1 <= n ==> norm(b n) <= B * (&1 + log(&n)) pow k) /\
               &1 < Re s
               ==> dseries (\n. a n + b n) s = dseries a s + dseries b s`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [dseries] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  REWRITE_TAC[COMPLEX_FIELD `(a + b) / c = a / c + b / c:complex`] THEN
  MATCH_MP_TAC SERIES_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC DSERIES_SUMS_ABS THEN ASM_MESON_TAC[]);;

let DSERIES_LMUL = prove
 (`!a c B k s. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
               &1 < Re s
               ==> dseries (\n. c * a n) s = c * dseries a s`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [dseries] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  REWRITE_TAC[COMPLEX_FIELD `(c * a) / d = c * a / d:complex`] THEN
  MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN
  MATCH_MP_TAC DSERIES_SUMS_ABS THEN ASM_MESON_TAC[]);;

let DSERIES_REAL_NONNEG = prove
 (`!a B k x. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
             (!n. 1 <= n ==> real(a n) /\ &0 <= Re(a n)) /\ &1 < x
             ==> real(dseries a (Cx x)) /\ &0 <= Re(dseries a (Cx x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num->complex`; `B:real`; `k:num`; `Cx x`]
    DSERIES_SUMS_ABS) THEN
  ASM_REWRITE_TAC[RE_CX] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. n IN from 1
        ==> Im((a:num->complex) n / Cx(&n) cpow Cx x) = &0 /\
            &0 <= Re(a n / Cx(&n) cpow Cx x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CPOW_REAL_REAL; REAL_CX; RE_CX] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
      check (fun th -> can (find_term ((=) `real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_EXISTS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real` ASSUME_TAC)
      MP_TAC) THEN
    ASM_REWRITE_TAC[RE_CX] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM CX_DIV; RE_CX; IM_CX] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= --x ==> x = &0`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_SERIES_POS THENL
     [EXISTS_TAC `Im o (\n. (a:num->complex) n / Cx(&n) cpow Cx x)` THEN
      EXISTS_TAC `from 1` THEN
      ASM_SIMP_TAC[REAL_SUMS_IM; o_THM; REAL_LE_REFL];
      EXISTS_TAC `\n. --(Im((a:num->complex) n / Cx(&n) cpow Cx x))` THEN
      EXISTS_TAC `from 1` THEN ASM_SIMP_TAC[REAL_NEG_0; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_SERIES_NEG THEN
      REWRITE_TAC[GSYM o_DEF] THEN ASM_SIMP_TAC[REAL_SUMS_IM]];
    MATCH_MP_TAC REAL_SERIES_POS THEN
    EXISTS_TAC `Re o (\n. (a:num->complex) n / Cx(&n) cpow Cx x)` THEN
    EXISTS_TAC `from 1` THEN ASM_SIMP_TAC[REAL_SUMS_RE; o_THM]]);;

let DSERIES_NORM_BOUND = prove
 (`!a B k s S. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
               &1 < Re s /\
               (!N. sum(1..N) (\n. norm(a n) * &n rpow (--Re s)) <= S)
               ==> norm(dseries a s) <= S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num->complex`; `B:real`; `k:num`; `s:complex`]
    DSERIES_SUMS_ABS) THEN
  ASM_REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
  DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\N. vsum(1..N) (\n. (a:num->complex) n / Cx(&n) cpow s)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\n. norm((a:num->complex) n) * &n rpow (--Re s))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  SIMP_TAC[NORM_DIV_CPOW_NUM; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Dirichlet convolution.                                                    *)
(* ------------------------------------------------------------------------- *)

let DSERIES_PARTIAL_CONV = prove
 (`!a b s N.
     vsum(1..N) (\n. vsum {d | d divides n} (\d. a d * b(n DIV d)) /
                     Cx(&n) cpow s) =
     vsum(1..N) (\d. a d / Cx(&d) cpow s *
                     vsum(1..N DIV d) (\k. b k / Cx(&k) cpow s))`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(1..N) (\n. vsum {d | d divides n}
                   (\d. (a:num->complex) d * b(n DIV d) / Cx(&n) cpow s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SIMP_TAC[complex_div; COMPLEX_MUL_ASSOC] THEN
    MATCH_MP_TAC(GSYM VSUM_COMPLEX_RMUL) THEN
    MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(k * d) DIV d = k` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC DIV_MULT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CPOW_NUM_MUL] THEN
  MP_TAC(SPECL [`k:num`; `s:complex`] CPOW_NUM_NZ) THEN
  MP_TAC(SPECL [`d:num`; `s:complex`] CPOW_NUM_NZ) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_FIELD);;

let DSERIES_PRODUCT_DIFF = prove
 (`!a b s N.
     vsum(1..N) (\n. a n / Cx(&n) cpow s) *
     vsum(1..N) (\n. b n / Cx(&n) cpow s) -
     vsum(1..N) (\d. a d / Cx(&d) cpow s *
                     vsum(1..N DIV d) (\k. b k / Cx(&k) cpow s)) =
     vsum(1..N) (\d. a d / Cx(&d) cpow s *
                     vsum(N DIV d + 1..N) (\k. b k / Cx(&k) cpow s))`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG; GSYM VSUM_SUB] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `N DIV d <= N` MP_TAC THENL [REWRITE_TAC[DIV_LE]; ALL_TAC] THEN
  SPEC_TAC(`N DIV d`,`M:num`) THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
  REWRITE_TAC[VECTOR_ARITH `(x + y) - z:real^N = y <=> x = z`]);;

let DIV_LOWER_HALF = prove
 (`!N d. 1 <= d /\ d <= N ==> &N <= &2 * &d * &(N DIV d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`N:num`; `d:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `1 <= N DIV d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  ABBREV_TAC `q = N DIV d` THEN ABBREV_TAC `r = N MOD d` THEN
  SUBGOAL_THEN `d * 1 <= d * q` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MULT_CLAUSES]] THEN
  UNDISCH_TAC `r < d:num` THEN ARITH_TAC);;

let RPOW_DIV_LOWER = prove
 (`!N d e. 1 <= d /\ d <= N /\ &0 < e
           ==> &(N DIV d) rpow (--e) <=
               &2 rpow e * &d rpow e * &N rpow (--e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &d /\ &0 < &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 rpow e * &d rpow e * &N rpow (--e) =
                (&N / (&2 * &d)) rpow (--e)` SUBST1_TAC THENL
   [REWRITE_TAC[RPOW_DIV; RPOW_MUL; RPOW_NEG] THEN
    SUBGOAL_THEN `&0 < &2 rpow e /\ &0 < &d rpow e /\ &0 < &N rpow e`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[RPOW_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &2 * d`] THEN
  MP_TAC(SPECL [`N:num`; `d:num`] DIV_LOWER_HALF) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let DSERIES_PRODUCT_DIFF_BOUND = prove
 (`!a b s Ca Cb e N.
     &0 < e /\ 1 <= N /\
     (!n. 1 <= n ==> norm(a n / Cx(&n) cpow s) <= Ca * inv(&n rpow (&1 + e)))
       /\
     (!n. 1 <= n ==> norm(b n / Cx(&n) cpow s) <= Cb * inv(&n rpow (&1 + e)))
     ==> norm(vsum(1..N) (\d. a d / Cx(&d) cpow s *
                              vsum(N DIV d + 1..N) (\k. b k / Cx(&k) cpow s)))
         <= Ca * Cb * &2 rpow e / e * &N rpow (--e) * (&1 + log(&N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Ca /\ &0 <= Cb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `1` (ASSUME `!n. 1 <= n ==> norm(a n / Cx(&n) cpow s) <=
                                     Ca * inv(&n rpow (&1 + e))`)) THEN
      MP_TAC(ISPEC `(a:num->complex) 1 / Cx(&1) cpow s` NORM_POS_LE);
      MP_TAC(SPEC `1` (ASSUME `!n. 1 <= n ==> norm(b n / Cx(&n) cpow s) <=
                                     Cb * inv(&n rpow (&1 + e))`)) THEN
      MP_TAC(ISPEC `(b:num->complex) 1 / Cx(&1) cpow s` NORM_POS_LE)] THEN
    REWRITE_TAC[LE_REFL; RPOW_ONE; REAL_INV_1; REAL_MUL_RID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\d. Ca * Cb * &2 rpow e / e * &N rpow (--e) *
                              inv(&d))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_LMUL] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[HARMONIC_LE_LOG; RPOW_POS_LE; REAL_POS; REAL_LE_DIV;
                 REAL_LT_IMP_LE]] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `1 <= N DIV d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Ca * inv(&d rpow (&1 + e))) *
              (Cb * &(N DIV d) rpow (--e) / e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(N DIV d + 1..N) (\k. Cb * &k rpow (--(e + &1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[RPOW_NEG; REAL_ARITH `e + &1 = &1 + e`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUM_LMUL; real_div; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC SUM_RPOW_TAIL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `d:num`; `e:real`] RPOW_DIV_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < &d` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Ca * inv(&d rpow (&1 + e))) *
              (Cb * (&2 rpow e * &d rpow e * &N rpow (--e)) / e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1] THEN
  SUBGOAL_THEN `&0 < &d rpow e` MP_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < &d` THEN
  CONV_TAC REAL_FIELD);;

let RPOW_LOG_DECAY = prove
 (`!e N. &0 < e /\ 1 <= N
         ==> &N rpow (--e) * (&1 + log(&N)) <=
             &2 / e * exp(e / &2) * &N rpow (--(e / &2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `1`; `e / &2`] LOG_POW_RPOW_BOUND) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_POW_1] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&N rpow (--e) * (&1 / (e / &2) * exp(e / &2) *
                               &N rpow (e / &2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `&N rpow (--e) * &N rpow (e / &2) = &N rpow (--(e / &2))`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD);;

let DSERIES_MUL_SUMS = prove
 (`!a b A B k s.
     (!n. 1 <= n ==> norm(a n) <= A * (&1 + log(&n)) pow k) /\
     (!n. 1 <= n ==> norm(b n) <= B * (&1 + log(&n)) pow k) /\ &1 < Re s
     ==> ((\n. vsum {d | d divides n} (\d. a d * b(n DIV d)) / Cx(&n) cpow s)
          sums (dseries a s * dseries b s)) (from 1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e = (Re s - &1) / &2` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Ca = A * (&k / e) pow k * exp e` THEN
  ABBREV_TAC `Cb = B * (&k / e) pow k * exp e` THEN
  SUBGOAL_THEN
   `(!n. 1 <= n ==> norm(a n / Cx(&n) cpow s) <= Ca * inv(&n rpow (&1 + e))) /\
    (!n. 1 <= n ==> norm(b n / Cx(&n) cpow s) <= Cb * inv(&n rpow (&1 + e)))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 + e = (Re s + &1) / &2` SUBST1_TAC THENL
     [EXPAND_TAC "e" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Ca"; "Cb"; "e"] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DSERIES_DOMINATION THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG; DSERIES_PARTIAL_CONV] THEN
  MP_TAC(SPECL [`a:num->complex`; `b:num->complex`; `s:complex`]
    DSERIES_PRODUCT_DIFF) THEN
  REWRITE_TAC[COMPLEX_RING `x - y = z <=> y = x - z`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM COMPLEX_SUB_RZERO] THEN
  MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:num->complex`; `A:real`; `k:num`; `s:complex`]
        DSERIES_SUMS_ABS);
      MP_TAC(ISPECL [`b:num->complex`; `B:real`; `k:num`; `s:complex`]
        DSERIES_SUMS_ABS)] THEN
    ASM_REWRITE_TAC[sums; FROM_INTER_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist; COMPLEX_SUB_RZERO] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  ABBREV_TAC `K2 = Ca * Cb * &2 rpow e / e * &2 / e * exp(e / &2) + &1` THEN
  SUBGOAL_THEN `&0 <= Ca /\ &0 <= Cb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `1` (ASSUME `!n. 1 <= n ==> norm(a n / Cx(&n) cpow s) <=
                                     Ca * inv(&n rpow (&1 + e))`)) THEN
      MP_TAC(ISPEC `(a:num->complex) 1 / Cx(&1) cpow s` NORM_POS_LE);
      MP_TAC(SPEC `1` (ASSUME `!n. 1 <= n ==> norm(b n / Cx(&n) cpow s) <=
                                     Cb * inv(&n rpow (&1 + e))`)) THEN
      MP_TAC(ISPEC `(b:num->complex) 1 / Cx(&1) cpow s` NORM_POS_LE)] THEN
    REWRITE_TAC[LE_REFL; RPOW_ONE; REAL_INV_1; REAL_MUL_RID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K2` ASSUME_TAC THENL
   [EXPAND_TAC "K2" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1:real`) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS; REAL_LE_DIV; REAL_LT_IMP_LE;
                 REAL_EXP_POS_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`e / &2`; `r / K2:real`] RPOW_NEG_EVENTUALLY_LT) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N0:num` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `Ca * Cb * &2 rpow e / e * &N rpow (--e) * (&1 + log(&N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DSERIES_PRODUCT_DIFF_BOUND THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(Ca * Cb * &2 rpow e / e) *
              (&2 / e * exp(e / &2) * &N rpow (--(e / &2)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS; REAL_LE_DIV; REAL_LT_IMP_LE];
      ALL_TAC]) THEN
    MATCH_MP_TAC RPOW_LOG_DECAY THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `K2 * &N rpow (--(e / &2))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [EXPAND_TAC "K2" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let DSERIES_MUL = prove
 (`!a b A B k s.
     (!n. 1 <= n ==> norm(a n) <= A * (&1 + log(&n)) pow k) /\
     (!n. 1 <= n ==> norm(b n) <= B * (&1 + log(&n)) pow k) /\ &1 < Re s
     ==> dseries (\n. vsum {d | d divides n} (\d. a d * b(n DIV d))) s =
         dseries a s * dseries b s`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [dseries] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  MATCH_MP_TAC DSERIES_MUL_SUMS THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Completely multiplicative coefficients: exponential form.                 *)
(* ------------------------------------------------------------------------- *)

let DSERIES_EQ = prove
 (`!a b s. (!n. 1 <= n ==> a n = b n) ==> dseries a s = dseries b s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dseries; infsum] THEN AP_TERM_TAC THEN
  ABS_TAC THEN EQ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMS_EQ) THEN
  ASM_SIMP_TAC[IN_FROM]);;

let DSERIES_NEAR_ONE = prove
 (`!a s. (!n. 1 <= n ==> norm(a n) <= &1) /\ &2 <= Re s
         ==> norm(dseries a s - a 1) <= &2 rpow (&2 - Re s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num->complex`; `&1`; `0`;
   `s:complex`] DSERIES_SUMS_ABS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[real_pow; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\N. vsum(1..N) (\n. a n / Cx(&n) cpow s) - a 1` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[VSUM_CLAUSES_LEFT] THEN
  REWRITE_TAC[CPOW_1; COMPLEX_DIV_1; ARITH] THEN
  REWRITE_TAC[VECTOR_ARITH `(x + y) - x:real^N = y`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2..N) (\n. &2 rpow (&2 - Re s) * inv(&n pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_DIV_CPOW_NUM; ARITH_RULE `2 <= n ==> 1 <= n`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &n rpow --Re s` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS; ARITH_RULE `2 <= n ==> 1 <= n`];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&n rpow --Re s = &n rpow (&2 - Re s) * inv(&n pow 2)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM RPOW_POW; GSYM RPOW_NEG; GSYM RPOW_ADD] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    REWRITE_TAC[rpow; REAL_ARITH `&0 < &2`] THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_ARITH `(&2 - s) * x <= (&2 - s) * y <=>
                            &0 <= (s - &2) * (x - y)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[RPOW_POS_LE; REAL_POS] THEN
  MP_TAC(SPEC `N:num` SUM_INV_SQUARE_LE_2) THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_INV_1] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP
    (REAL_ARITH `&1 + x <= &2 ==> x <= &1:real`)));;

let dseries_log = new_definition
 `dseries_log (f:num->complex) s =
  dseries (\n. Cx(mangoldt n / log(&n)) * f n) s`;;

let MANGOLDT_DIV_LOG_BOUNDS = prove
 (`!n. 1 <= n ==> &0 <= mangoldt n / log(&n) /\ mangoldt n / log(&n) <= &1`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[MANGOLDT_1; real_div; REAL_MUL_LZERO; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; MANGOLDT_POS_LE; REAL_LT_IMP_LE;
               REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
  MATCH_MP_TAC MANGOLDT_LE_LOG THEN ASM_ARITH_TAC);;

let DSERIES_LIM_INFINITY = prove
 (`!a. (!n. 1 <= n ==> norm(a n) <= &1)
       ==> ((\m. dseries a (Cx(&m + &2))) --> a 1) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `e:real`] REAL_ARCH_POW_INV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[dist] THEN
  MP_TAC(SPECL [`a:num->complex`; `Cx(&m + &2)`] DSERIES_NEAR_ONE) THEN
  ASM_REWRITE_TAC[RE_CX] THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POS; REAL_LE_ADDL]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y < e ==> x <= y ==> x < e:real`) THEN
  REWRITE_TAC[REAL_ARITH `&2 - (&m + &2) = --(&m)`; RPOW_NEG; RPOW_POW] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 / &2) pow M` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let DSERIES_LOG_DERIV_CONV = prove
 (`!f n. (!m n. f(m * n) = f m * f n) /\ 1 <= n
         ==> vsum {d | d divides n}
               (\d. f d * --(Cx(mangoldt(n DIV d)) * f(n DIV d))) =
             --(Cx(log(&n)) * f n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {d | d divides n} (\d. --(f n) * Cx(mangoldt(n DIV d)))`
    THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:num->complex) n = f d * f(n DIV d)` SUBST1_TAC THENL
     [MP_TAC(SPECL [`d:num`; `n DIV d`]
        (ASSUME `!m n. (f:num->complex)(m * n) = f m * f n`)) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
      ASM_MESON_TAC[DIVIDES_DIV_MULT; MULT_SYM];
      CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_DIVISORS] THEN
  REWRITE_TAC[VSUM_CX] THEN
  ASM_SIMP_TAC[SUM_DIVISORS_REFLECT; LOG_MANGOLDT_SUM] THEN
  REWRITE_TAC[ETA_AX] THEN
  ABBREV_TAC `ls = sum {d | d divides n} mangoldt` THEN
  CONV_TAC COMPLEX_RING);;

let DSERIES_LOG_ALT = prove
 (`!f. dseries_log f = dseries (\n. Cx(mangoldt n / log(&n)) * f n)`,
  REWRITE_TAC[FUN_EQ_THM; dseries_log]);;

let DSERIES_EXP = prove
 (`!f s. (!m n. f(m * n) = f m * f n) /\ f 1 = Cx(&1) /\
         (!n. norm(f n) <= &1) /\ &1 < Re s
         ==> dseries f s = cexp(dseries_log f s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!n. 1 <= n ==> norm((f:num->complex) n) <= &1 * (&1 + log(&n)) pow 0) /\
    (!n. 1 <= n ==> norm(Cx(mangoldt n / log(&n)) * f n)
                    <= &1 * (&1 + log(&n)) pow 0) /\
    (!n. 1 <= n ==> norm(--(Cx(mangoldt n) * f n))
                    <= &1 * (&1 + log(&n)) pow 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_POW_1] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      MP_TAC(SPEC `n:num` MANGOLDT_DIV_LOG_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
      MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. Re z > &1
        ==> ((\z. dseries f z * cexp(--(dseries_log f z)))
               has_complex_derivative
             Cx(&0)) (at z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_gt] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:num->complex`; `&1`; `0`; `z:complex`]
      HAS_COMPLEX_DERIVATIVE_DSERIES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\n. Cx(mangoldt n / log(&n)) * (f:num->complex) n`;
                   `&1`; `0`; `z:complex`]
      HAS_COMPLEX_DERIVATIVE_DSERIES) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM DSERIES_LOG_ALT] THEN
    SUBGOAL_THEN
     `dseries (\n. --(Cx(log(&n)) * Cx(mangoldt n / log(&n)) * f n)) z =
      dseries (\n. --(Cx(mangoldt n) * f n)) z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC DSERIES_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_CASES_TAC `n = 1` THENL
       [ASM_REWRITE_TAC[MANGOLDT_1; LOG_1] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < log(&n)` MP_TAC THENL
       [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC;
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `dseries f z * dseries (\n. --(Cx(mangoldt n) * f n)) z =
      dseries (\n. --(Cx(log(&n)) * f n)) z`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`f:num->complex`; `\n. --(Cx(mangoldt n) *
                                               (f:num->complex) n)`;
                     `&1`; `&1`; `1`; `z:complex`] DSERIES_MUL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1 * (&1 + log(&n)) pow 0` THEN ASM_SIMP_TAC[] THEN
        REWRITE_TAC[real_pow; REAL_POW_1; REAL_MUL_LID] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
        MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DSERIES_EQ THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC DSERIES_LOG_DERIV_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `D1 = dseries (\n. --(Cx(log(&n)) * (f:num->complex) n)) z` THEN
    ABBREV_TAC `G1 = dseries (\n. --(Cx(mangoldt n) * (f:num->complex) n)) z`
      THEN
    SUBGOAL_THEN
     `((\z. cexp(--(dseries_log f z))) has_complex_derivative
       cexp(--(dseries_log f z)) * --G1) (at z)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\z. --(dseries_log f z)`; `cexp`; `--G1:complex`;
                     `cexp(--(dseries_log f z))`; `z:complex`]
        COMPLEX_DIFF_CHAIN_AT) THEN
      REWRITE_TAC[o_DEF; HAS_COMPLEX_DERIVATIVE_CEXP] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_NEG THEN
      FIRST_X_ASSUM(MP_TAC o check
                      (fun th -> can (find_term ((=) `dseries_log`))
        (concl th))) THEN
      REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `Cx(&0) = dseries f z * (cexp(--(dseries_log f z)) * --G1) +
               D1 * cexp(--(dseries_log f z))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `dseries f z * G1 = D1` THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_AT THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL
           [`\z. dseries f z * cexp(--(dseries_log f z))`; `{z | Re z > &1}`]
    HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[CONVEX_HALFSPACE_RE_GT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:complex`) THEN
  SUBGOAL_THEN `c = Cx(&1)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\m. dseries f (Cx(&m + &2)) *
                    cexp(--(dseries_log f (Cx(&m + &2))))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\m. dseries f (Cx(&m + &2)) *
                         cexp(--(dseries_log f (Cx(&m + &2))))) = (\m. c)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&m + &2)`) THEN
        REWRITE_TAC[RE_CX; real_gt] THEN DISCH_THEN MATCH_MP_TAC THEN
        MP_TAC(SPEC `m:num` REAL_POS) THEN REAL_ARITH_TAC;
        REWRITE_TAC[LIM_CONST]];
      ALL_TAC] THEN
    SUBGOAL_THEN `Cx(&1) = f 1 * cexp(--(Cx(mangoldt 1 / log(&1)) * f 1))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[MANGOLDT_1; real_div; REAL_MUL_LZERO;
                      COMPLEX_MUL_LZERO; COMPLEX_NEG_0; CEXP_0;
                      COMPLEX_MUL_LID];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC DSERIES_LIM_INFINITY THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN
    REWRITE_TAC[CONTINUOUS_AT_CEXP] THEN MATCH_MP_TAC LIM_NEG THEN
    REWRITE_TAC[dseries_log] THEN MATCH_MP_TAC DSERIES_LIM_INFINITY THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
      check (fun th -> can (find_term ((=) `mangoldt`)) (concl th) &&
                       can (find_term ((=) `( / ):real->real->real`))
                           (concl th))) THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:complex`) THEN
  ASM_REWRITE_TAC[real_gt] THEN
  REWRITE_TAC[CEXP_NEG] THEN
  MP_TAC(SPEC `dseries_log f s` CEXP_NZ) THEN CONV_TAC COMPLEX_FIELD);;

let DSERIES_NZ = prove
 (`!f s. (!m n. f(m * n) = f m * f n) /\ f 1 = Cx(&1) /\
         (!n. norm(f n) <= &1) /\ &1 < Re s
         ==> ~(dseries f s = Cx(&0))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`f:num->complex`; `s:complex`]
    DSERIES_EXP) THEN ASM_REWRITE_TAC[CEXP_NZ]);;

let NORM_DSERIES_EXP = prove
 (`!f s. (!m n. f(m * n) = f m * f n) /\ f 1 = Cx(&1) /\
         (!n. norm(f n) <= &1) /\ &1 < Re s
         ==> norm(dseries f s) = exp(Re(dseries_log f s))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`f:num->complex`; `s:complex`]
    DSERIES_EXP) THEN ASM_SIMP_TAC[NORM_CEXP]);;

let DSERIES_LOG_DERIV = prove
 (`!f s. (!m n. f(m * n) = f m * f n) /\ (!n. norm(f n) <= &1) /\ &1 < Re s
         ==> dseries f s * dseries (\n. Cx(mangoldt n) * f n) s =
             dseries (\n. Cx(log(&n)) * f n) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->complex`; `\n. Cx(mangoldt n) * (f:num->complex) n`;
                 `&1`; `&1`; `1`; `s:complex`] DSERIES_MUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID] THEN CONJ_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC LOG_POS THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
      MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DSERIES_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`f:num->complex`; `n:num`] DSERIES_LOG_DERIV_CONV) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RNEG; VSUM_NEG] THEN
  REWRITE_TAC[VECTOR_ARITH `--x = --y <=> x = y:real^N`]);;

let DSERIES_NEG = prove
 (`!a B k s. (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
             &1 < Re s
             ==> dseries (\n. --(a n)) s = --(dseries a s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dseries; complex_div;
   COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC INFSUM_NEG THEN REWRITE_TAC[GSYM complex_div] THEN
  MATCH_MP_TAC DSERIES_ABS_SUMMABLE THEN ASM_MESON_TAC[]);;

let DSERIES_NEG_LOG_DERIV = prove
 (`!f s. (!m n. f(m * n) = f m * f n) /\ f 1 = Cx(&1) /\
         (!n. norm(f n) <= &1) /\ &1 < Re s
         ==> --(complex_derivative (dseries f) s) / dseries f s =
             dseries (\n. Cx(mangoldt n) * f n) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->complex`; `&1`; `0`; `s:complex`]
    HAS_COMPLEX_DERIVATIVE_DSERIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[real_pow; REAL_MUL_LID]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_DERIVATIVE) THEN
  MP_TAC(SPECL [`f:num->complex`; `s:complex`] DSERIES_NZ) THEN
  MP_TAC(SPECL [`f:num->complex`; `s:complex`] DSERIES_LOG_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\n. Cx(log(&n)) * (f:num->complex) n`; `&1`; `1`;
                 `s:complex`] DSERIES_NEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE;
     REAL_ABS_POS] THEN
    MP_TAC(SPEC `&n` LOG_POS) THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC COMPLEX_FIELD);;

let LAMBDA_SERIES_BOUND = prove
 (`!f s N. (!n. norm(f n) <= &1) /\ &1 < s
           ==> sum(1..N) (\n. norm(Cx(mangoldt n) * f n) * &n rpow (--s))
               <= &2 / (s - &1) * exp((s - &1) / &2) * (&1 + &2 / (s - &1))`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `e = (s - &1) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ &1 + &2 * e = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 / (s - &1) = &1 / e` SUBST1_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `&1 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\n. (&1 / e * exp e) * &n rpow (--(e + &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`n:num`; `1`; `e:real`] LOG_POW_RPOW_BOUND) THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + log(&n)) * &n rpow (--s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE;
       REAL_ABS_POS] THEN
      MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
      MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((&1 / e) * exp e * &n rpow e) * &n rpow (--s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS] THEN
      UNDISCH_TAC `(&1 + log (&n)) <= (&1 / e) * exp e * &n rpow e` THEN
      REWRITE_TAC[real_div; REAL_MUL_LID];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&n rpow e * &n rpow (--s) = &n rpow (--(e + &1))`
    MP_TAC THENL
     [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  SUBGOAL_THEN `&2 / (s - &1) = &1 / e` SUBST1_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `&1 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x:real`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `~(N = 0) ==> 1 <= N`] THEN
  REWRITE_TAC[RPOW_ONE; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> &1 + y <= &1 + z:real`) THEN
  MP_TAC(SPECL [`1`; `N:num`; `e:real`] SUM_RPOW_TAIL) THEN
  ASM_REWRITE_TAC[LE_REFL; RPOW_ONE; ARITH]);;
