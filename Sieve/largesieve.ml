(* ========================================================================= *)
(* The large sieve inequality (additive and multiplicative forms).           *)
(*                                                                           *)
(* LARGE_SIEVE_POINTS: if the points x_r (r in J) are d-spaced modulo 1,     *)
(* i.e. |x_r - x_s - m| >= d for r <> s and all integers m (d > 0),          *)
(*   sum_r |sum_{n<=N} a_n e(n x_r)|^2 <= (4 N + 36 / d) sum_{n<=N} |a_n|^2. *)
(* LARGE_SIEVE_FAREY: the fractions a/q, q <= Q, (a,q) = 1, are Q^-2 spaced, *)
(*   sum_{q<=Q} sum_{(a,q)=1} |S(a/q)|^2 <= (4 N + 36 Q^2) sum |a_n|^2.      *)
(* LARGE_SIEVE_MULTIPLICATIVE:                                               *)
(*   sum_{q<=Q} q/phi(q) sum_{chi primitive mod q} |sum_{n<=N} a_n chi(n)|^2 *)
(*     <= (4 N + 36 Q^2) sum_{n<=N} |a_n|^2.                                 *)
(*                                                                           *)
(* Method (no integrals).  By duality (LARGE_SIEVE_DUALITY, an AM-GM         *)
(* argument without square roots) it suffices to bound the dual sums         *)
(* sum_{n<=N} |sum_r b_r e(n x_r)|^2.  After the shift n -> n + N, they are  *)
(* at most N^-1 sum_{i,j<=2N} |T(i + j)|^2 (SUM_DOUBLE_LOWER), a Fejer-type  *)
(* sum which expands into the squared kernel K(t)^2, K(t) = sum_{n<=2N}      *)
(* e(n t).  From |1 - e(u)| = 2 |sin pi u| >= u (1 - u),                     *)
(*   |K(t)|^2 <= min(4 N^2, 8 / u^2 + 8 / (1 - u)^2),  u = frac(t),          *)
(* and the spacing sum is bounded by the injection s -> floor(u_s / d)       *)
(* (SUM_DECREASING_SEPARATED) and sum_k min(K^2, 8 / (d k)^2) <= 9 K / d.    *)
(* The multiplicative form uses tau(conj chi) sum a_n chi(n) =               *)
(* sum_b conj chi(b) S(b/q), |tau|^2 = q for primitive chi, and              *)
(* DIRICHLET_CHARACTER_PARSEVAL.                                             *)
(* ========================================================================= *)

needs "Sieve/gauss.ml";;
needs "Sieve/nt.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Elementary bounds: sin, |1 - e(u)|, the kernel, sums of 1/k^2.            *)
(* ------------------------------------------------------------------------- *)

let PI_BOUNDS_CRUDE = prove
 (`&3 <= pi /\ pi <= &4`,
  MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

let SIN_PI_LOWER_HALF = prove
 (`!u. &0 <= u /\ u <= &1 / &2 ==> u <= &2 * sin(pi * u)`,
  REPEAT STRIP_TAC THEN MP_TAC PI_BOUNDS_CRUDE THEN STRIP_TAC THEN
  ASM_CASES_TAC `&1 / &6 <= u` THENL
   [MP_TAC(SPECL [`pi / &6`; `pi * u`] SIN_MONO_LE) THEN
    REWRITE_TAC[SIN_PI6] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC PI_POS THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `pi * &1 / &6 <= pi * u ==> pi / &6 <= pi * u`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `pi * u <= pi * &1 / &2 ==> pi * u <= pi / &2`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`0`; `Cx(pi * u)`] TAYLOR_CSIN) THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; IM_CX; REAL_ABS_NUM; REAL_EXP_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_MUL_LID; COMPLEX_DIV_1;
              GSYM CX_SIN; GSYM CX_SUB; COMPLEX_NORM_CX; REAL_MUL_LID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `&0 <= pi * u /\ pi * u <= &2 / &3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * &1 / &6` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2; REAL_ARITH_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_POW; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  SUBGOAL_THEN `(pi * u) pow 3 <= (&4 / &9) * (pi * u)` MP_TAC THENL
   [SUBGOAL_THEN `(pi * u) pow 3 = (pi * u) pow 2 * (pi * u)` SUBST1_TAC
    THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x * x <= (&2 / &3) * (&2 / &3) ==> x * x <= &4 / &9`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * u <= pi * u` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let NORM_ONE_SUB_EXPI = prove
 (`!u. norm(Cx(&1) - expi u) = &2 * abs(sin(pi * u))`,
  GEN_TAC THEN
  REWRITE_TAC[expi; ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] CEXP_EULER] THEN
  REWRITE_TAC[GSYM CX_COS; GSYM CX_SIN; complex_norm] THEN
  REWRITE_TAC[RE_SUB; IM_SUB; RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II;
              IM_MUL_II] THEN
  SUBGOAL_THEN `&2 * u * pi = &2 * (pi * u)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COS_DOUBLE_SIN; SIN_DOUBLE] THEN
  SUBGOAL_THEN `&2 * abs(sin(pi * u)) = sqrt((&2 * sin(pi * u)) pow 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[POW_2_SQRT_ABS; REAL_ABS_MUL; REAL_ABS_NUM]; ALL_TAC] THEN
  AP_TERM_TAC THEN MP_TAC(SPEC `pi * u` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

let NORM_ONE_SUB_EXPI_LOWER = prove
 (`!u. &0 <= u /\ u <= &1 ==> u * (&1 - u) <= norm(Cx(&1) - expi u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_ONE_SUB_EXPI] THEN
  ASM_CASES_TAC `u <= &1 / &2` THENL
   [MP_TAC(SPEC `u:real` SIN_PI_LOWER_HALF) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= u * u` MP_TAC THENL
     [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPEC `&1 - u` SIN_PI_LOWER_HALF) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sin(pi * (&1 - u)) = sin(pi * u)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID; SIN_SUB; SIN_PI;
                  COS_PI] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - u) * (&1 - u)` MP_TAC THENL
     [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let NORM_VSUM_GP_UNIT = prove
 (`!z N. norm z = &1 /\ ~(z = Cx(&1))
         ==> norm(vsum(1..N) (\n. z pow n)) <= &2 / norm(Cx(&1) - z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(Cx(&1) - z)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_GP] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_0] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x:complex) = &1 /\ norm(y:complex) = &1 ==> norm(x - y) <= &2`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_POW; REAL_POW_ONE]);;

let EXPI_FRAC = prove
 (`!x. expi(frac x) = expi x`,
  GEN_TAC THEN MATCH_MP_TAC EXPI_INTEGER_DIFF THEN
  REWRITE_TAC[FRAC_FLOOR; REAL_ARITH `(x - f) - x:real = --f`; INTEGER_NEG;
              FLOOR]);;

let LARGE_SIEVE_KERNEL = prove
 (`!N t. ~integer t
         ==> norm(vsum(1..N) (\n. expi(&n * t)))
             <= &2 * (inv(frac t) + inv(&1 - frac t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXPI_NUM_MUL] THEN
  SUBGOAL_THEN `expi t = expi(frac t)` SUBST1_TAC THENL
   [REWRITE_TAC[EXPI_FRAC]; ALL_TAC] THEN
  ABBREV_TAC `u = frac t` THEN
  SUBGOAL_THEN `&0 < u /\ u < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[REAL_FRAC_POS_LT; FLOOR_FRAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(expi u = Cx(&1))` ASSUME_TAC THENL
   [REWRITE_TAC[EXPI_EQ_1] THEN DISCH_TAC THEN
    MP_TAC(SPEC `u:real` REAL_ABS_INTEGER_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / norm(Cx(&1) - expi u)` THEN
  ASM_SIMP_TAC[NORM_VSUM_GP_UNIT; NORM_EXPI] THEN
  MP_TAC(SPEC `u:real` NORM_ONE_SUB_EXPI_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < u * (&1 - u)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv u + inv(&1 - u) = inv(u * (&1 - u))` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < u`; `u < &1`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2] THEN
  ASM_REWRITE_TAC[]);;

let LARGE_SIEVE_KERNEL_SQUARE = prove
 (`!K t. ~integer t
         ==> norm(vsum(1..K) (\n. expi(&n * t))) pow 2
             <= min (&K pow 2)
                    (&8 / frac t pow 2 + &8 / (&1 - frac t) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..K) (\n. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN
      REWRITE_TAC[FINITE_NUMSEG; NORM_EXPI; REAL_LE_REFL];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K:num`; `t:real`] LARGE_SIEVE_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < frac t /\ frac t < &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_FRAC_POS_LT; FLOOR_FRAC]; ALL_TAC] THEN
  ABBREV_TAC `u = frac t` THEN
  ABBREV_TAC `y = norm(vsum(1..K) (\n. expi(&n * t)))` THEN
  SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 / u pow 2 + &8 / (&1 - u) pow 2 =
                &8 * (inv u pow 2 + inv(&1 - u) pow 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_POW_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * (inv u + inv(&1 - u))) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    MP_TAC(SPEC `inv u - inv(&1 - u)` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC]);;

let SUM_MIN_INV_SQUARE = prove
 (`!K d M. &0 < d /\ 1 <= K
           ==> sum(1..M) (\k. min (&K pow 2) (&8 / (d * &k) pow 2))
               <= &9 * &K / d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &K` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k ==> &8 / (d * &k) pow 2 = &8 / d pow 2 * inv(&k pow 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `&3 <= &K * d` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..M) (\k. &8 / d pow 2 * inv(&k pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&8 / d pow 2 * &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[SUM_INV_SQUARE_LE_2] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&8 / d pow 2 * &2 = (&16 / d) * inv d /\
                  &9 * &K / d = (&9 / d) * &K`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `inv d <= &K / &3` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &3`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&16 / d) * (&K / &3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN
      SUBGOAL_THEN `&0 <= inv d * &K` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPEC `&3 / (&K * d)` FLOOR_POS) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `j:num`)] THEN
  MP_TAC(SPEC `&3 / (&K * d)` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `k0 = j + 1` THEN
  SUBGOAL_THEN `&0 < &K * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < &3 / (&K * d)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 / (&K * d) <= &k0 /\ &k0 <= &6 / (&K * d) /\ 1 <= k0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&6 / (&K * d) = &2 * &3 / (&K * d)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..M) (\k. if k <= k0 then &K pow 2
                   else &8 / d pow 2 * inv(&k pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CASES; FINITE_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= &K / d /\ a <= &6 * (&K / d) /\ b <= &8 / &3 * (&K / d)
    ==> a + b <= &9 * &K / d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..k0) (\k. &K pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG;
                  REAL_LE_POW_2] THEN
      ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&6 / (&K * d) * &K pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        MAP_EVERY UNDISCH_TAC [`&0 < d`; `&1 <= &K`] THEN
        CONV_TAC REAL_FIELD]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(k0+1..M) (\k. &8 / d pow 2 * inv(&k pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&8 / d pow 2 * inv(&k0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SUM_INV_SQUARE_TAIL] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&8 / d pow 2 * (&K * d / &3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &k0` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&3 / (&K * d))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_INV_DIV; real_div] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < d` THEN
      CONV_TAC REAL_FIELD]]);;

(* ------------------------------------------------------------------------- *)
(* Sums over well-spaced points.                                             *)
(* ------------------------------------------------------------------------- *)

let SUM_DECREASING_SEPARATED = prove
 (`!J (f:A->real) g d K.
     FINITE J /\ &0 < d /\ inv d <= &K /\
     (!s. s IN J ==> d <= f s /\ f s <= &1) /\
     (!s s'. s IN J /\ s' IN J /\ ~(s = s') ==> d <= abs(f s - f s')) /\
     (!x y. &0 < x /\ x <= y ==> g y <= g x) /\
     (!x. &0 < x ==> &0 <= g x)
     ==> sum J (\s. g(f s)) <= sum(1..K) (\k. g(d * &k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s:A. s IN J ==> ?k. floor(f s / d) = &k` MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FLOOR_POS THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A->num` (LABEL_TAC "hfl")) THEN
  SUBGOAL_THEN
   `!s:A. s IN J ==> 1 <= h s /\ h s <= K /\ d * &(h s) <= f s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:A` THEN DISCH_TAC THEN
    MP_TAC(SPEC `(f:A->real) s / d` FLOOR) THEN
    USE_THEN "hfl" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(s:A) IN J`)]) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:A` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= (f:A->real) s / d /\ f s / d <= inv d`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ;
        REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN `&0 < &((h:A->num) s) + &1 - &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `x + &1 - &1 = x`; REAL_OF_NUM_LT;
                  REAL_OF_NUM_LE] THEN ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s s':A. s IN J /\ s' IN J /\ (h:A->num) s = h s' ==> s = s'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:A = s'` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:A`; `s':A`] o
      check (fun th -> length(fst(strip_forall(concl th))) = 2 &&
                       is_imp(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[REAL_NOT_LE] THEN
    MP_TAC(SPEC `(f:A->real) s / d` FLOOR) THEN
    MP_TAC(SPEC `(f:A->real) s' / d` FLOOR) THEN
    USE_THEN "hfl" (fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `(s:A) IN J`)]) THEN
    USE_THEN "hfl" (fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `(s':A) IN J`)]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `abs((f:A->real) s / d - f s' / d) < &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(f:A->real) s / d - f s' / d = (f s - f s') / d`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LT_LDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum J (\s:A. (g:real->real) (d * &(h s)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:A` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= n ==> 0 < n`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->num`; `\k. (g:real->real) (d * &k)`; `J:A->bool`]
    SUM_IMAGE) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

let FRAC_DIFF_SEPARATED = prove
 (`!J (x:A->real) d r.
     r IN J /\
     (!r s m. r IN J /\ s IN J /\ ~(r = s) /\ integer m
              ==> d <= abs(x r - x s - m))
     ==> (!s. s IN J DELETE r
              ==> d <= frac(x r - x s) /\ frac(x r - x s) <= &1 /\
                  d <= &1 - frac(x r - x s) /\
                  &1 - frac(x r - x s) <= &1) /\
         (!s s'. s IN J DELETE r /\ s' IN J DELETE r /\ ~(s = s')
                 ==> d <= abs(frac(x r - x s) - frac(x r - x s')) /\
                     d <= abs((&1 - frac(x r - x s)) -
                              (&1 - frac(x r - x s'))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `s:A` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    MP_TAC(SPEC `(x:A->real) r - x s` FLOOR_FRAC) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`r:A`; `s:A`; `floor((x:A->real) r - x s)`] th) THEN
      MP_TAC(SPECL [`r:A`; `s:A`; `floor((x:A->real) r - x s) + &1`] th)) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:A`; `s':A`] THEN REWRITE_TAC[IN_DELETE] THEN
    STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `(&1 - a) - (&1 - b) = --(a - b)`;
                REAL_ABS_NEG] THEN
    REWRITE_TAC[FRAC_FLOOR] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`s':A`; `s:A`;
      `floor((x:A->real) r - x s) - floor(x r - x s')`]) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; FLOOR] THEN REAL_ARITH_TAC]);;

let LARGE_SIEVE_SPACING_SQUARE = prove
 (`!J (x:A->real) d r K.
     FINITE J /\ &0 < d /\ 1 <= K /\ r IN J /\
     (!r s m. r IN J /\ s IN J /\ ~(r = s) /\ integer m
              ==> d <= abs(x r - x s - m))
     ==> sum (J DELETE r)
           (\s. norm(vsum(1..K) (\n. expi(&n * (x r - x s)))) pow 2)
         <= &18 * &K / d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`J:A->bool`; `x:A->real`; `d:real`; `r:A`]
    FRAC_DIFF_SEPARATED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `inv(d:real)` FLOOR_POS) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
  MP_TAC(SPEC `inv(d:real)` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `g = \y. min (&K pow 2) (&8 / y pow 2)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (J DELETE r) (\s:A. (g:real->real) (frac((x:A->real) r - x s))) +
    sum (J DELETE r) (\s:A. g(&1 - frac(x r - x s)))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD; FINITE_DELETE] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_DELETE] THEN
    X_GEN_TAC `s:A` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `min (&K pow 2)
          (&8 / frac((x:A->real) r - x s) pow 2 +
           &8 / (&1 - frac(x r - x s)) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LARGE_SIEVE_KERNEL_SQUARE THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`r:A`; `s:A`; `(x:A->real) r - x s`] o
        check (fun th -> length(fst(strip_forall(concl th))) = 3)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c
      ==> min a (b + c) <= min a b + min a c`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= &9 * &K / d /\ b <= &9 * &K / d ==> a + b <= &18 * &K / d`) THEN
  SUBGOAL_THEN
   `(!y z. &0 < y /\ y <= z ==> (g:real->real) z <= g y) /\
    (!y. &0 < y ==> &0 <= g y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> min a b <= min a c`) THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_MIN; REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..j+1) (\k. (g:real->real) (d * &k))` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC SUM_DECREASING_SEPARATED THEN
     ASM_SIMP_TAC[FINITE_DELETE] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
     EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
     MATCH_MP_TAC SUM_MIN_INV_SQUARE THEN ASM_REWRITE_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* The dual inequality and duality.                                          *)
(* ------------------------------------------------------------------------- *)

let SUM_SYMMETRIC_KERNEL = prove
 (`!J (u:A->real) k M.
     FINITE J /\
     (!r s. r IN J /\ s IN J ==> &0 <= k r s /\ k r s = k s r) /\
     (!r. r IN J ==> sum J (\s. k r s) <= M)
     ==> sum J (\r. sum J (\s. u r * u s * k r s))
         <= M * sum J (\r. u r pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(sum J (\r:A. sum J (\s. (u:A->real) r pow 2 * (k:A->A->real) r s)) +
     sum J (\r:A. sum J (\s. u s pow 2 * k s r))) / &2` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD; real_div; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:A`; `s:A`] o
      check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&0 <= ((u:A->real) r - u s) pow 2 * k (r:A) (s:A)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r s:A. (u:A->real) s pow 2 * (k:A->A->real) s r`;
                 `J:A->bool`; `J:A->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ARITH `(a + a) / &2 = a:real`] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:A` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_POW_2]);;

let LARGE_SIEVE_DUAL_EXPAND = prove
 (`!J (x:A->real) N (b:A->complex).
     FINITE J
     ==> vsum(1..N) (\n. vsum J (\r. b r * expi(&n * x r)) *
                         cnj(vsum J (\r. b r * expi(&n * x r)))) =
         vsum J (\r. vsum J (\s. (b r * cnj(b s)) *
                                 vsum(1..N) (\n. expi(&n * (x r - x s)))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CNJ_VSUM; CNJ_MUL; CNJ_EXPI] THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL] THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MP_TAC(ISPECL
   [`\n r. vsum J (\s. ((b:A->complex) r * expi(&n * (x:A->real) r)) *
                       cnj(b s) * expi(--(&n * x s)))`;
    `1..N`; `J:A->bool`] VSUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:A` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL
   [`\n s. ((b:A->complex) r * expi(&n * (x:A->real) r)) *
           cnj(b s) * expi(--(&n * x s))`;
    `1..N`; `J:A->bool`] VSUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `s:A` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; real_sub; EXPI_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let LARGE_SIEVE_DOUBLE_EXPAND = prove
 (`!J (x:A->real) K (b:A->complex).
     FINITE J
     ==> vsum(1..K) (\i. vsum(1..K) (\j.
            vsum J (\r. b r * expi(&(i + j) * x r)) *
            cnj(vsum J (\r. b r * expi(&(i + j) * x r))))) =
         vsum J (\r. vsum J (\s. (b r * cnj(b s)) *
                     vsum(1..K) (\n. expi(&n * (x r - x s))) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j r. (b:A->complex) r * expi(&(i + j) * (x:A->real) r) =
            (b r * expi(&i * x r)) * expi(&j * x r)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; EXPI_ADD] THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:A->bool`; `x:A->real`; `K:num`]
    LARGE_SIEVE_DUAL_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GEN `i:num` (BETA_RULE(ISPEC
    `\r:A. (b:A->complex) r * expi(&i * (x:A->real) r)` th))]) THEN
  MP_TAC(ISPECL
   [`\i r. vsum J (\s. (((b:A->complex) r * expi(&i * (x:A->real) r)) *
                       cnj(b s * expi(&i * x s))) *
                      vsum (1..K) (\j. expi(&j * (x r - x s))))`;
    `1..K`; `J:A->bool`] VSUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:A` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL
   [`\i s. (((b:A->complex) r * expi(&i * (x:A->real) r)) *
            cnj(b s * expi(&i * x s))) *
           vsum (1..K) (\j. expi(&j * (x r - x s)))`;
    `1..K`; `J:A->bool`] VSUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `s:A` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[COMPLEX_POW_2] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[CNJ_MUL; CNJ_EXPI] THEN
  SUBGOAL_THEN
   `expi(&i * ((x:A->real) r - x s)) = expi(&i * x r) * expi(--(&i * x s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXPI_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    CONV_TAC COMPLEX_RING]);;

let LARGE_SIEVE_DOUBLE_BOUND = prove
 (`!J (x:A->real) K (b:A->complex).
     FINITE J
     ==> sum(1..K) (\i. sum(1..K) (\j.
            norm(vsum J (\r. b r * expi(&(i + j) * x r))) pow 2))
         <= sum J (\r. sum J (\s. norm(b r) * norm(b s) *
                  norm(vsum(1..K) (\n. expi(&n * (x r - x s)))) pow 2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(vsum(1..K) (\i. vsum(1..K) (\j.
       vsum J (\r. (b:A->complex) r * expi(&(i + j) * (x:A->real) r)) *
       cnj(vsum J (\r. b r * expi(&(i + j) * x r))))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; VSUM_CX; COMPLEX_NORM_CX] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[LARGE_SIEVE_DOUBLE_EXPAND] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:A` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_POW;
                REAL_MUL_ASSOC; REAL_LE_REFL]]);;

let SUM_DOUBLE_LOWER = prove
 (`!c N. (!m. &0 <= c m)
         ==> &N * sum(N+1..2*N) c
             <= sum(1..2*N) (\i. sum(1..2*N) (\j. c(i + j)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\i. sum(1..2*N) (\j. (c:num->real)(i + j)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
    CONJ_TAC THENL
     [ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN
   `&N * sum(N+1..2*N) c = sum(1..N) (\i. sum(N+1..2*N) (c:num->real))`
  SUBST1_TAC THENL [REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum((N+1)-i..2*N-i) (\j. (c:num->real)(i + j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(ISPECL [`i:num`; `c:num->real`; `(N+1)-i`; `2*N-i`] SUM_OFFSET) THEN
    SUBGOAL_THEN `((N + 1) - i:num) + i = N + 1 /\ (2 * N - i) + i = 2 * N`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_SYM];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let LARGE_SIEVE_DUAL = prove
 (`!J (x:A->real) d N (b:A->complex).
     FINITE J /\ &0 < d /\
     (!r s m. r IN J /\ s IN J /\ ~(r = s) /\ integer m
              ==> d <= abs(x r - x s - m))
     ==> sum(1..N) (\n. norm(vsum J (\r. b r * expi(&n * x r))) pow 2)
         <= (&4 * &N + &36 / d) * sum J (\r. norm(b r) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sum J (\r. norm((b:A->complex) r) pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `b' = \r:A. (b:A->complex) r * expi(--(&N * (x:A->real) r))` THEN
  SUBGOAL_THEN
   `sum(1..N) (\n. norm(vsum J (\r. (b:A->complex) r *
                                     expi(&n * (x:A->real) r))) pow 2) =
    sum(N+1..2*N) (\m. norm(vsum J (\r. (b':A->complex) r *
                                         expi(&m * x r))) pow 2)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`N:num`;
      `\m. norm(vsum J (\r. (b':A->complex) r *
                            expi(&m * (x:A->real) r))) pow 2`;
      `1`; `N:num`] SUM_OFFSET) THEN
    REWRITE_TAC[ARITH_RULE `1 + N = N + 1 /\ N + N = 2 * N`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXPAND_TAC "b'" THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM EXPI_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ABS_TAC THEN
    REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum J (\r. norm((b:A->complex) r) pow 2) =
    sum J (\r. norm((b':A->complex) r) pow 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:A` THEN DISCH_TAC THEN
    EXPAND_TAC "b'" THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\m. norm(vsum J (\r. (b':A->complex) r *
                          expi(&m * (x:A->real) r))) pow 2`;
    `N:num`] SUM_DOUBLE_LOWER) THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  MP_TAC(ISPECL [`J:A->bool`; `x:A->real`; `2 * N`; `b':A->complex`]
    LARGE_SIEVE_DOUBLE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`J:A->bool`; `\r:A. norm((b':A->complex) r)`;
    `\r s:A. norm(vsum(1..2 * N) (\n. expi(&n * ((x:A->real) r - x s))))
             pow 2`;
    `&(2 * N) pow 2 + &18 * &(2 * N) / d`] SUM_SYMMETRIC_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r:A`; `s:A`] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_NORM_CNJ] THEN
      SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG; CNJ_EXPI] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `r:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\s:A. norm(vsum(1..2 * N)
                   (\n. expi(&n * ((x:A->real) r - x s)))) pow 2`;
      `J:A->bool`; `r:A`] SUM_DELETE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a = k /\ b <= m ==> b = s - a ==> s <= k + m`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; EXPI_0;
                  VSUM_CONST_NUMSEG] THEN
      REWRITE_TAC[ADD_SUB; NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM;
                  REAL_MUL_RID];
      MATCH_MP_TAC LARGE_SIEVE_SPACING_SQUARE THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(2 * N) pow 2 + &18 * &(2 * N) / d = &N * (&4 * &N + &36 / d)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN UNDISCH_TAC `&0 < d` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `&N:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let LARGE_SIEVE_DUALITY = prove
 (`!(c:B->A->complex) s t D a.
     FINITE s /\ FINITE t /\ &0 <= D /\
     (!b. sum s (\n. norm(vsum t (\r. b r * c r n)) pow 2)
          <= D * sum t (\r. norm(b r) pow 2))
     ==> sum t (\r. norm(vsum s (\n. a n * c r n)) pow 2)
         <= D * sum s (\n. norm(a n) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = \r:B. vsum s (\n:A. a n * (c:B->A->complex) r n)` THEN
  SUBGOAL_THEN `!r:B. vsum s (\n:A. a n * (c:B->A->complex) r n) = S r`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Ts = sum t (\r:B. norm((S:B->complex) r) pow 2)` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\r:B. cnj((S:B->complex) r)`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CNJ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Ts <= sum s (\n:A. norm(a n:complex) *
                      norm(vsum t (\r:B. cnj((S:B->complex) r) * c r n)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `Cx Ts = vsum s (\n:A. a n * vsum t (\r:B. cnj((S:B->complex) r) *
                                                c r n))`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
      MP_TAC(ISPECL
       [`\n:A r:B. (a:A->complex) n * cnj((S:B->complex) r) * c r n`;
        `s:A->bool`; `t:B->bool`] VSUM_SWAP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      EXPAND_TAC "Ts" THEN REWRITE_TAC[GSYM VSUM_CX; CX_POW] THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:B` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM COMPLEX_MUL_CNJ] THEN EXPAND_TAC "S" THEN
      ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL] THEN
      MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(Cx Ts)` THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC
   `W = \n:A. norm(vsum t (\r:B. cnj((S:B->complex) r) *
                                 (c:B->A->complex) r n))` THEN
  SUBGOAL_THEN
   `!n:A. norm(vsum t (\r:B. cnj((S:B->complex) r) *
                             (c:B->A->complex) r n)) = W n`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `D = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`\n:A. (W:A->real) n pow 2`; `s:A->bool`]
      SUM_POS_EQ_0) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [UNDISCH_TAC `sum s (\n:A. (W:A->real) n pow 2) <= &0 * Ts` THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum s (\n:A. norm((a:A->complex) n) * W n)` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_MUL_RZERO; SUM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `Ts <= D / &2 * sum s (\n:A. norm((a:A->complex) n) pow 2) +
         inv(&2 * D) * sum s (\n. (W:A->real) n pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum s (\n:A. norm((a:A->complex) n) * W n)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `norm((a:A->complex) n) * (W:A->real) n =
      inv(&2 * D) * (&2 * D * norm(a n) * W n) /\
      D / &2 * norm(a n) pow 2 + inv(&2 * D) * W n pow 2 =
      inv(&2 * D) * ((D * norm(a n)) pow 2 + W n pow 2)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [UNDISCH_TAC `&0 < D` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `D * norm((a:A->complex) n) - (W:A->real) n`
      REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(&2 * D) * sum s (\n:A. (W:A->real) n pow 2) <= Ts / &2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * D) * (D * Ts)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < D` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let LARGE_SIEVE_POINTS = prove
 (`!J (x:A->real) d N (a:num->complex).
     FINITE J /\ &0 < d /\
     (!r s m. r IN J /\ s IN J /\ ~(r = s) /\ integer m
              ==> d <= abs(x r - x s - m))
     ==> sum J (\r. norm(vsum(1..N) (\n. a n * expi(&n * x r))) pow 2)
         <= (&4 * &N + &36 / d) * sum(1..N) (\n. norm(a n) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r:A n:num. expi(&n * (x:A->real) r)`; `1..N`;
                 `J:A->bool`; `&4 * &N + &36 / d`;
                 `a:num->complex`] LARGE_SIEVE_DUALITY) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    GEN_TAC THEN MATCH_MP_TAC LARGE_SIEVE_DUAL THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Farey fractions.                                                          *)
(* ------------------------------------------------------------------------- *)

let FAREY_SEPARATED = prove
 (`!Q q a q' a' m.
     q IN 1..Q /\ a < q /\ coprime(a,q) /\
     q' IN 1..Q /\ a' < q' /\ coprime(a',q') /\
     ~((q,a) = (q',a')) /\ integer m
     ==> inv(&Q pow 2) <= abs(&a / &q - &a' / &q' - m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG; PAIR_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&q = &0) /\ ~(&q' = &0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &a / &q /\ &a / &q < &1 /\ &0 <= &a' / &q' /\ &a' / &q' < &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &q /\ &0 < &q'` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_LDIV_EQ; REAL_MUL_LID;
                 REAL_OF_NUM_LT];
    ALL_TAC] THEN
  ABBREV_TAC `z = &a * &q' - &a' * &q - m * &q * &q'` THEN
  SUBGOAL_THEN `integer z` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `&a / &q - &a' / &q' - m = z / (&q * &q')` SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN
    MAP_EVERY UNDISCH_TAC [`~(&q = &0)`; `~(&q' = &0)`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `&a / &q - &a' / &q' = m` ASSUME_TAC THENL
     [UNDISCH_TAC `&a * &q' - &a' * &q - m * &q * &q' = z` THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(&q = &0)`; `~(&q' = &0)`] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `m = &0` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(SPEC `m:real` REAL_ABS_INTEGER_LEMMA) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:num) * q' = a' * q` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
      UNDISCH_TAC `&a * &q' - &a' * &q - &0 * &q * &q' = z` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `q:num = q'` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
      MAP_EVERY UNDISCH_TAC
       [`coprime(a:num,q)`; `coprime(a':num,q')`; `(a:num) * q' = a' * q`] THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    UNDISCH_TAC `(a:num) * q' = a' * q'` THEN
    ASM_REWRITE_TAC[EQ_MULT_RCANCEL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `z:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `&0 < &q * &q' /\ &q * &q' <= &Q pow 2` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SUBGOAL_THEN `&0 < &Q pow 2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID]);;

let LARGE_SIEVE_FAREY = prove
 (`!Q N (c:num->complex).
     1 <= Q
     ==> sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                          (\a. norm(vsum(1..N)
                                     (\n. c n * expi(&n * &a / &q))) pow 2))
         <= (&4 * &N + &36 * &Q pow 2) *
            sum(1..N) (\n. norm(c n) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!q. FINITE {a:num | a < q /\ coprime(a,q)}` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{a:num | a < q}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_PRODUCT o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `J = {q,j | q IN 1..Q /\ j IN {a | a < q /\ coprime(a,q)}}` THEN
  SUBGOAL_THEN `FINITE(J:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:num#num->bool`; `\p:num#num. &(SND p) / &(FST p)`;
                 `inv(&Q pow 2)`; `N:num`; `c:num->complex`]
    LARGE_SIEVE_POINTS) THEN
  SUBGOAL_THEN `&0 < &Q pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    EXPAND_TAC "J" THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `a:num`; `q':num`; `a':num`; `m:real`] THEN
    STRIP_TAC THEN MATCH_MP_TAC FAREY_SEPARATED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_INV_INV] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The multiplicative large sieve.                                           *)
(* ------------------------------------------------------------------------- *)

let LARGE_SIEVE_MODULUS = prove
 (`!q N (a:num->complex).
     1 <= q
     ==> &q * sum {c | primitive_character q c}
                  (\c. norm(vsum(1..N) (\n. a n * c n)) pow 2)
         <= &(phi q) *
            sum {b | b < q /\ coprime(b,q)}
                (\b. norm(vsum(1..N) (\n. a n * expi(&n * &b / &q))) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM DIRICHLET_CHARACTER_PARSEVAL] THEN
  SUBGOAL_THEN
   `{c | primitive_character q c} SUBSET {c | dirichlet_character q c}`
  ASSUME_TAC THENL
   [SIMP_TAC[SUBSET; IN_ELIM_THM; primitive_character]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {c | primitive_character q c}
      (\c. norm(vsum {b | b < q}
              (\b. cnj(c b) *
                   vsum(1..N) (\n. (a:num->complex) n *
                                   expi(&n * &b / &q)))) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `c:num->complex` THEN
    DISCH_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[GSYM GAUSS_SUM_CHARACTER_SUM] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL] THEN
    MP_TAC(ISPECL [`q:num`; `\n. cnj((c:num->complex) n)`]
      GAUSS_SUM_NORM) THEN
    ASM_SIMP_TAC[PRIMITIVE_CHARACTER_CNJ];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS] THEN
    REWRITE_TAC[REAL_LE_POW_2]]);;

let LARGE_SIEVE_MULTIPLICATIVE = prove
 (`!Q N (a:num->complex).
     1 <= Q
     ==> sum(1..Q) (\q. &q / &(phi q) *
                        sum {c | primitive_character q c}
                            (\c. norm(vsum(1..N) (\n. a n * c n)) pow 2))
         <= (&4 * &N + &36 * &Q pow 2) *
            sum(1..N) (\n. norm(a n) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`Q:num`; `N:num`; `a:num->complex`] LARGE_SIEVE_FAREY) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(phi q)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `N:num`; `a:num->complex`] LARGE_SIEVE_MODULUS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `S1 = sum {c | primitive_character q c}
             (\c. norm(vsum(1..N) (\n. (a:num->complex) n * c n)) pow 2)` THEN
  ABBREV_TAC
   `S2 = sum {b | b < q /\ coprime(b,q)}
             (\b. norm(vsum(1..N) (\n. (a:num->complex) n *
                                       expi(&n * &b / &q))) pow 2)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&q / &(phi q) * S1 = (&q * S1) / &(phi q)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;
