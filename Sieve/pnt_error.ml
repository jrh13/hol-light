(* ========================================================================= *)
(* The prime number theorem with an error term (de la Vallee Poussin):       *)
(*   PNT_THETA_ERROR:                                                        *)
(*     !A. ?Cb. !x. &2 <= x                                                  *)
(*                  ==> abs(sum {p | prime p /\ &p <= x} (\p. log(&p)) - x)  *)
(*                      <= Cb * x / log x pow A                              *)
(* (the Vinogradov major arcs need it for the modulus q = 1, which sw.ml,    *)
(* whose characters are nonprincipal, does not cover).                       *)
(*                                                                           *)
(* Method: the generic Perron machinery of perron.ml for the coefficients    *)
(* a(n) = Lambda(n) - [n >= 2], whose Dirichlet series                       *)
(*   -zeta'/zeta(s) - zeta(s) + 1 = -Z'(s)/Z(s) - nearzeta 1 s/(s - 1) + 1,  *)
(*   Z(s) = (s - 1) zeta(s) = nearzeta 1 s + 1,                              *)
(* has no pole at s = 1 (pnt_zetaf, PNT_ZETAF_HOLOMORPHIC,                   *)
(* PNT_ZETAF_DSERIES).                                                       *)
(* * ZETA_OFFSET_GEN, GENZETA_TAIL_BOUND: zeta(s) as a partial sum plus a    *)
(*   tail for Re s > 0; ZETA_STRIP_BOUND, ZETA_DERIV_BOUND: |zeta| and       *)
(*   |zeta'| are O(log N) and O(log^2 N) for |s| <= N in a strip left of     *)
(*   Re s = 1.                                                               *)
(* * ZETA_LOWER_ABSTRACT, ZF_ZETA_RIGHT, ZF_ZETA_DISC, ZF_ZETA_LINE,         *)
(*   PNT_ZETAF_RECT: with Lg = 1 + log N, zeta has no zeros and |zeta'/zeta| *)
(*   <= 10^11 Lg^9 for 1 - 1/(10^11 Lg^9) <= Re s <= 2 away from s = 1       *)
(*   (3-4-1 and the mean value theorem, as in zerofree.ml), and |pnt_zetaf|  *)
(*   <= 2 10^11 Lg^9 on the whole rectangle.                                 *)
(* * PSI1_GEN, PSI1_ZETA, PSI1_ZETA_MONO: sum_{n <= x} a(n) (1 - n/x) is     *)
(*   O(x/log^A x); PNT_THETA_FROM_PSI1 (differencing, prime powers) and      *)
(*   PNT_MZ_DZ_BOUNDS, THETA_TRIVIAL give PNT_THETA_ERROR.                   *)
(* ========================================================================= *)

needs "Sieve/primes.ml";;
needs "Sieve/sw.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Zeta as a partial sum plus a tail; bounds in a strip.                     *)
(* ------------------------------------------------------------------------- *)

let NEARZETA_OFFSET = prove
 (`!N s. &0 < Re s
         ==> nearzeta 1 s =
             vsum(1..N) (\m. (s - Cx(&1)) / Cx(&m) cpow s -
                             (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                              Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1)))) +
             nearzeta (N + 1) s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING `b = a - v ==> a = v + b:complex`) THEN
  MATCH_MP_TAC SERIES_UNIQUE THEN
  EXISTS_TAC `\m. (s - Cx(&1)) / Cx(&m) cpow s -
                  (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                   Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1)))` THEN
  EXISTS_TAC `from(N + 1)` THEN
  ASM_SIMP_TAC[NEARZETA_CONVERGES] THEN
  MP_TAC(ISPECL
   [`\m. (s - Cx(&1)) / Cx(&m) cpow s -
         (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
          Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1)))`;
    `nearzeta 1 s`; `1`; `N + 1`] SUMS_OFFSET) THEN
  ASM_SIMP_TAC[NEARZETA_CONVERGES; ADD_SUB] THEN
  DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC);;

let NEARZETA_TERMS_SUM = prove
 (`!N s. vsum(1..N) (\m. (s - Cx(&1)) / Cx(&m) cpow s -
                         (Cx(&1) / Cx(&m) cpow (s - Cx(&1)) -
                          Cx(&1) / Cx(&(m + 1)) cpow (s - Cx(&1)))) =
         (s - Cx(&1)) * vsum(1..N) (\k. Cx(&1) / Cx(&k) cpow s) -
         (Cx(&1) - Cx(&1) / Cx(&(N + 1)) cpow (s - Cx(&1)))`,
  INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THENL
   [REWRITE_TAC[ARITH; CPOW_1; COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[ADD1; complex_div] THEN CONV_TAC COMPLEX_RING]);;

let ZETA_OFFSET_GEN = prove
 (`!N s. &0 < Re s /\ ~(s = Cx(&1))
         ==> zeta s = vsum(1..N) (\k. Cx(&1) / Cx(&k) cpow s) +
                      genzeta (N + 1) s`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[zeta; genzeta; CPOW_1] THEN
  MP_TAC(SPECL [`N:num`; `s:complex`] NEARZETA_OFFSET) THEN
  ASM_REWRITE_TAC[NEARZETA_TERMS_SUM] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `~(s = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD);;

let GENZETA_TAIL_BOUND = prove
 (`!n s. 1 <= n /\ &0 < Re s /\ ~(s = Cx(&1))
         ==> norm(genzeta n s) <=
             norm s * (&1 / &n + &1 / Re s) / exp(Re s * log(&n)) +
             exp((&1 - Re s) * log(&n)) / norm(s - Cx(&1))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[genzeta] THEN
  SUBGOAL_THEN `&0 < norm(s - Cx(&1))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ASM_SIMP_TAC[REAL_ADD_RDISTRIB; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:complex) <= x /\ norm(b:complex) <= y ==> norm(a + b) <= x + y`)
  THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`n:num`; `s:complex`] NEARZETA_BOUND_SHARP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    SUBGOAL_THEN `&0 < exp(Re s * log(&n))` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < norm(s - Cx(&1))` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NORM_CPOW_REAL; REAL_CX; RE_CX; RE_SUB] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `--((Re s - &1) * log(&n)) = (&1 - Re s) * log(&n)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < norm(s - Cx(&1))` THEN CONV_TAC REAL_FIELD);;

let ZETA_PARTIAL_TERM_BOUND = prove
 (`!s N k. 4 <= N /\ &1 - inv(log(&N)) <= Re s /\ 1 <= k /\ k <= N
           ==> norm(Cx(&1) / Cx(&k) cpow s) <= &3 * inv(&k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &k /\ &0 <= log(&k) /\ log(&k) <= log(&N) /\
                &1 <= log(&N)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_GE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - Re s) * log(&k) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(log(&N)) * log(&k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV; NORM_CPOW_REAL; REAL_CX; RE_CX;
               COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `inv(&k) = exp(--log(&k))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_NEG; EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG] THEN
  SUBGOAL_THEN `--(Re s * log(&k)) = (&1 - Re s) * log(&k) + --log(&k)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_EXP_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&1)` THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE; EXP_1_LE_3]);;

let ZETA_STRIP_EXP_BOUND = prove
 (`!s N. 4 <= N /\ &1 - inv(log(&N)) <= Re s
         ==> exp((&1 - Re s) * log(&(N + 1))) <= &9`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log(&N) /\ &0 <= log(&(N + 1)) /\
                log(&(N + 1)) <= &2 * log(&N)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_GE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM LOG_POW] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_POW_2; REAL_OF_NUM_MUL; REAL_OF_NUM_LE;
                  REAL_OF_NUM_LT] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE `4 <= N /\ 4 * N <= N * N ==> N + 1 <= N * N`)
      THEN ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1) * exp(&1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(log(&N)) * log(&(N + 1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * &3` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE; EXP_1_LE_3]]);;

let ZETA_STRIP_BOUND = prove
 (`!s N. 4 <= N /\ norm s <= &N /\ &1 - inv(log(&N)) <= Re s /\
         &1 / &2 <= Re s /\ ~(Im s = &0)
         ==> norm(zeta s) <= &3 * (&1 + log(&N)) + &20 + &9 / abs(Im s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s = Cx(&1)) /\ &0 < Re s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(Im s = &0)` THEN
      ASM_REWRITE_TAC[IM_CX];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `s:complex`] ZETA_OFFSET_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:complex) <= x /\ norm(b:complex) <= y ==> norm(a + b) <= x + y`)
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..N) (\k. &3 * inv(&k))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC ZETA_PARTIAL_TERM_BOUND THEN
      EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HARMONIC_LE_LOG THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N + 1`; `s:complex`] GENZETA_TAIL_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`s:complex`; `N:num`] ZETA_STRIP_EXP_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `X = exp((&1 - Re s) * log(&(N + 1)))` THEN
  SUBGOAL_THEN `&0 < &(N + 1) /\ &0 < X /\
                inv(exp(Re s * log(&(N + 1)))) = X / &(N + 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < N + 1`] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG; real_div] THEN
    SUBGOAL_THEN `inv(&(N + 1)) = exp(--log(&(N + 1)))` SUBST1_TAC THENL
     [SIMP_TAC[REAL_EXP_NEG; EXP_LOG; REAL_OF_NUM_LT; ARITH_RULE `0 < N + 1`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= x /\ b <= y ==> g <= a + b ==> g <= x + y`)
  THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[real_div] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `norm s * (&1 / &(N + 1) + &1 / Re s) * X / &(N + 1) =
      (norm s / &(N + 1)) * (&1 / &(N + 1) + &1 / Re s) * X`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &(N + 1)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * (&11 / &5 * &9)` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `a <= &1 / &5 /\ b <= &2 ==> a + b <= &11 / &5`) THEN
        CONJ_TAC THENL
         [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_INV2 THEN
          REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(Im s) <= norm(s - Cx(&1)) /\ &0 < abs(Im s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `s - Cx(&1)` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[IM_SUB; IM_CX; REAL_SUB_RZERO] THEN SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(s - Cx(&1))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&9 / norm(s - Cx(&1))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lower bounds and the zero-free rectangle for zeta.                        *)
(* ------------------------------------------------------------------------- *)

let CHI_0_1 = prove
 (`chi_0 1 = \n. Cx(&1)`,
  REWRITE_TAC[FUN_EQ_THM; chi_0; COPRIME_1]);;

let ZETA_LOWER_RIGHT = prove
 (`!t M2 y.
     &1 < y /\ y <= &2 /\ norm(zeta(Cx y + Cx(&2) * ii * Cx t)) <= M2
     ==> (y - &1) pow 3 <= &8 * M2 * norm(zeta(Cx y + ii * Cx t)) pow 4`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `chi_0 1`; `t:real`; `M2:real`; `y:real`]
    LFUN_LOWER_RIGHT) THEN
  REWRITE_TAC[DIRICHLET_CHARACTER_CHI_0; CHI_0_1] THEN
  REWRITE_TAC[COMPLEX_POW_ONE; ETA_AX] THEN
  SUBGOAL_THEN `&1 < Re(Cx y + Cx(&2) * ii * Cx t) /\
                &1 < Re(Cx y + ii * Cx t)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RE_ADD; RE_CX; RE_MUL_CX; RE_MUL_II; IM_CX] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[DSERIES_ZETA]);;

let ZETA_LOWER_ABSTRACT = prove
 (`!t M1 M2 x.
     ~(t = &0) /\ &1 <= M1 /\ &1 <= M2 /\
     (!y. &1 < y /\ y <= &2
          ==> norm(zeta(Cx y + Cx(&2) * ii * Cx t)) <= M2) /\
     (!z. Im z = t /\ &1 - inv(&2048 * M1 pow 4 * M2) <= Re z /\ Re z <= &2
          ==> norm(complex_derivative zeta z) <= M1) /\
     &1 - inv(&2048 * M1 pow 4 * M2) <= x /\ x <= &2
     ==> &2 * inv(&2048 * M1 pow 4 * M2) * M1
         <= norm(zeta(Cx x + ii * Cx t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e = inv(&2048 * M1 pow 4 * M2)` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 / &2048 /\ &2048 * e * M1 pow 4 * M2 = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    SUBGOAL_THEN `&1 <= M1 pow 4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &2048 * M1 pow 4 * M2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2048 * &1 * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2048 * &1 * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `a * i * b * c = i * (a * b * c):real`] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. &1 + e <= y /\ y <= &2
        ==> &4 * e * M1 <= norm(zeta(Cx y + ii * Cx t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `4` THEN
    REWRITE_TAC[NORM_POS_LE; ARITH] THEN
    MP_TAC(SPECL [`t:real`; `M2:real`; `y:real`] ZETA_LOWER_RIGHT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `e pow 3 <= (y - &1) pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `B = norm(zeta(Cx y + ii * Cx t))` THEN
    SUBGOAL_THEN `(&4 * e * M1) pow 4 * (&8 * M2) = e pow 3` ASSUME_TAC THENL
     [UNDISCH_TAC `&2048 * e * M1 pow 4 * M2 = &1` THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &8 * M2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&4 * e * M1) pow 4 * (&8 * M2) <= B pow 4 * (&8 * M2)`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 + e <= x` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * e * M1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 + e`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`zeta`; `complex_derivative zeta`;
                 `segment[Cx x + ii * Cx t,Cx(&1 + e) + ii * Cx t]`; `M1:real`]
    COMPLEX_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Im z = t /\ x <= Re z /\ Re z <= &1 + e` STRIP_ASSUME_TAC
    THENL
     [UNDISCH_TAC `z IN segment[Cx x + ii * Cx t,Cx(&1 + e) + ii * Cx t]` THEN
      REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[RE_ADD; IM_ADD; RE_CMUL; IM_CMUL; RE_CX; IM_CX;
                  RE_MUL_II; IM_MUL_II] THEN
      MP_TAC(SPECL [`u:real`; `(&1 + e) - x`] REAL_LE_MUL) THEN
      MP_TAC(SPECL [`&1 - u`; `(&1 + e) - x`] REAL_LE_MUL) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_ZETA THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN ASM_REWRITE_TAC[IM_CX]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`Cx x + ii * Cx t`;
   `Cx(&1 + e) + ii * Cx t`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[COMPLEX_RING `(a + b) - (c + b):complex = a - c`] THEN
  REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `abs(x - (&1 + e)) <= &2 * e` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L0 = norm(zeta(Cx(&1 + e) + ii * Cx t))` THEN
  SUBGOAL_THEN `&0 <= M1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `M1 * abs(x - (&1 + e)) <= M1 * (&2 * e)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b:complex p q. norm(a - b) <= p /\ &4 * q <= norm b /\ p <= &2 * q
                      ==> &2 * q <= norm a`) THEN
  MAP_EVERY EXISTS_TAC [`zeta(Cx(&1 + e) + ii * Cx t)`;
                        `M1 * abs(x - (&1 + e))`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `M1 * abs(x - (&1 + e)) <= M1 * (&2 * e)` THEN
  REAL_ARITH_TAC);;

let ZETA_DERIV_BOUND = prove
 (`!s N. 16 <= N /\ norm s + &1 <= &N /\ &1 - inv(&2 * log(&N)) <= Re s /\
         inv(log(&N)) <= abs(Im s)
         ==> norm(complex_derivative zeta s) <= &46 * (&1 + log(&N)) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&16)` THEN
    REWRITE_TAC[LOG_16_GE_2] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = inv(&2 * log(&N))` THEN
  SUBGOAL_THEN `&0 < r /\ r <= &1 / &4 /\ inv(log(&N)) = &2 * r`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. norm(s - w) <= r
        ==> &1 - inv(log(&N)) <= Re w /\ &1 / &2 <= Re w /\
            norm w <= &N /\ r <= abs(Im w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MP_TAC(SPEC `s - w:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; IM_SUB] THEN
    MP_TAC(NORM_ARITH `norm(w:complex) <= norm(s) + norm(s - w)`) THEN
    SUBGOAL_THEN `inv(log(&N)) <= &1 / &2` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(s,r) SUBSET {z | Re z > &0 /\ ~(z = Cx(&1))}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM; real_gt; dist] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `r <= abs(Im w)` THEN
      ASM_REWRITE_TAC[IM_CX] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`zeta`; `s:complex`; `r:real`;
                 `&3 * (&1 + log(&N)) + &20 + &18 * log(&N)`; `1`]
    CAUCHY_INEQUALITY) THEN
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_1; NUM_FACT_CONV `FACT 1`;
              REAL_MUL_LID; REAL_POW_1] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{z | Re z > &0 /\ ~(z = Cx(&1))}` THEN
      ASM_REWRITE_TAC[HOLOMORPHIC_ZETA];
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `{z | Re z > &0 /\ ~(z = Cx(&1))}` THEN
      ASM_MESON_TAC[HOLOMORPHIC_ZETA; BALL_SUBSET_CBALL; SUBSET_TRANS];
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&3 * (&1 + log(&N)) + &20 + &9 / abs(Im w)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ZETA_STRIP_BOUND THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> x + y + a <= x + y + b`) THEN
        SUBGOAL_THEN `&0 < abs(Im w)` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&18 * log(&N)) * r` THEN CONJ_TAC THENL
         [SUBST1_TAC(SYM(ASSUME `inv(&2 * log(&N)) = r`)) THEN
          REWRITE_TAC[REAL_INV_MUL] THEN
          SUBGOAL_THEN `~(log(&N) = &0)` MP_TAC THENL
           [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
  EXPAND_TAC "r" THEN REWRITE_TAC[real_div; REAL_INV_INV] THEN
  SUBGOAL_THEN `&0 <= log(&N) * log(&N)` MP_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

let ZETA_RIGHT_NORM = prove
 (`!s. &1 < Re s ==> norm(zeta s) <= Re s / (Re s - &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zeta] THEN
  MP_TAC(SPECL [`1`; `s:complex`] GENZETA_BOUND) THEN
  ASM_REWRITE_TAC[ARITH; LOG_1; REAL_MUL_RZERO; REAL_EXP_0] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b:real`) THEN
  UNDISCH_TAC `&1 < Re s` THEN CONV_TAC REAL_FIELD);;

let ZETA_DERIV_DSERIES = prove
 (`!s. &1 < Re s
       ==> complex_derivative (dseries (\n. Cx(&1))) s =
           complex_derivative zeta s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `{z | Re z > &1}` THEN
  REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_DSERIES_ABS THEN
    MAP_EVERY EXISTS_TAC [`&1`; `0`] THEN
    REWRITE_TAC[real_pow; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_LE_REFL;
                REAL_MUL_LID];
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `{s | Re s > &0 /\ ~(s = Cx(&1))}` THEN
    REWRITE_TAC[HOLOMORPHIC_ZETA; SUBSET; IN_ELIM_THM; real_gt] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 < Re(Cx(&1))` THEN
      REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC];
    ASM_REWRITE_TAC[real_gt];
    SIMP_TAC[DSERIES_ZETA; real_gt]]);;

let ZF_ZETA_RIGHT = prove
 (`!s ta. &0 < ta /\ ta <= &1 /\ &1 + ta <= Re s /\ Re s <= &2
          ==> ~(zeta s = Cx(&0)) /\
              norm(complex_derivative zeta s / zeta s) <= &12 / ta pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `chi_0 1`; `s:complex`; `ta:real`] ZF_RIGHT) THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_CHI_0; CHI_0_1] THEN
  SUBGOAL_THEN `&1 < Re s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DSERIES_ZETA; ZETA_DERIV_DSERIES]);;

let NEARZETA_1_DISC = prove
 (`!s. norm(s - Cx(&1)) <= &1 / &6
       ==> norm(nearzeta 1 s) <= &3 * norm(s - Cx(&1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&5 / &6 <= Re s /\ norm s <= &7 / &6` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `s - Cx(&1)` COMPLEX_NORM_GE_RE_IM) THEN
    MP_TAC(NORM_ARITH `norm(s:complex) <= norm(Cx(&1)) + norm(s - Cx(&1))`)
    THEN REWRITE_TAC[COMPLEX_NORM_CX; RE_SUB; RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`1`; `s:complex`] NEARZETA_BOUND_SHARP) THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_EXP_0; REAL_DIV_1] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; REAL_ARITH `(a * b) * c = b * (a * c):real`]
  THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&7 / &6 * (&1 + &6 / &5)` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&5 / &6 <= x ==> &0 < x`] THEN
    ASM_REAL_ARITH_TAC]);;

let ZF_ZETA_DISC = prove
 (`!s. norm(s - Cx(&1)) <= &1 / &12
       ==> norm(nearzeta 1 s) <= &1 / &4 /\
           norm(complex_derivative (nearzeta 1) s) <= &6`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 * norm(s - Cx(&1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NEARZETA_1_DISC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(s,&1 / &12) SUBSET {z | Re z > &0}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM; real_gt; dist] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MP_TAC(SPEC `w - Cx(&1)` COMPLEX_NORM_GE_RE_IM) THEN
    MP_TAC(NORM_ARITH `norm(w - Cx(&1)) <= norm(s - w) + norm(s - Cx(&1))`)
    THEN REWRITE_TAC[RE_SUB; RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nearzeta 1`; `s:complex`; `&1 / &12`; `&1 / &2`; `1`]
    CAUCHY_INEQUALITY) THEN
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_1; NUM_FACT_CONV `FACT 1`;
              REAL_MUL_LID; REAL_POW_1] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `{z | Re z > &0}` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_NEARZETA; LE_REFL];
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `{z | Re z > &0}` THEN
      ASM_MESON_TAC[HOLOMORPHIC_NEARZETA; LE_REFL; BALL_SUBSET_CBALL;
                    SUBSET_TRANS];
      REAL_ARITH_TAC;
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&3 * norm(w - Cx(&1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC NEARZETA_1_DISC;
        ALL_TAC] THEN
      MP_TAC(NORM_ARITH `norm(w - Cx(&1)) <= norm(s - w) + norm(s - Cx(&1))`)
      THEN ASM_REAL_ARITH_TAC];
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let ZF_ZETA_LINE = prove
 (`!N s. 16 <= N /\ inv(log(&N)) <= abs(Im s) /\
         &2 * abs(Im s) + &3 <= &N /\
         &1 - inv(&10 pow 11 * (&1 + log(&N)) pow 9) <= Re s /\ Re s <= &2
         ==> ~(zeta s = Cx(&0)) /\
             norm(complex_derivative zeta s / zeta s) <=
             &10 pow 11 * (&1 + log(&N)) pow 9`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&16)` THEN
    REWRITE_TAC[LOG_16_GE_2] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * log(&N)) <= &1 / &4` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = &1 + log(&N)` THEN
  SUBGOAL_THEN `&3 <= L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(Im s = &0) /\ &0 < abs(Im s)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(log(&N))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &46 * L pow 2 /\ &1 <= &3 * L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&46 * &1` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC
      THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2048 * (&46 * L pow 2) pow 4 * (&3 * L) = &27509489664 * L pow 9`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; GSYM REAL_POW_POW] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L pow 9 /\ L <= L pow 9` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(&10 pow 11 * L pow 9) <= inv(&2048 * (&46 * L pow 2) pow 4 * (&3 * L))
     /\
    inv(&2048 * (&46 * L pow 2) pow 4 * (&3 * L)) <= inv(&2 * log(&N))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. Im z = Im s /\ &1 - inv(&2 * log(&N)) <= Re z /\ Re z <= &2
        ==> norm(complex_derivative zeta z) <= &46 * L pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "L" THEN
    MATCH_MP_TAC ZETA_DERIV_BOUND THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `z:complex` COMPLEX_NORM_LE_RE_IM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`Im s`; `&46 * L pow 2`; `&3 * L`; `Re s`]
    ZETA_LOWER_ABSTRACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&3 + log(&N) + inv(abs(Im(Cx y + Cx(&2) * ii * Cx(Im s))))`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC ZETA_LINE_BOUND THEN
        REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX;
                    RE_II; IM_II; RE_MUL_II; IM_MUL_II] THEN
        REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          ASM_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `norm(Cx y) + norm(Cx(&2) * ii * Cx(Im s))` THEN
          REWRITE_TAC[NORM_TRIANGLE; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
                      COMPLEX_NORM_II] THEN
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_CX; IM_MUL_II; RE_CX] THEN
        REWRITE_TAC[REAL_ADD_LID; REAL_ABS_MUL; REAL_ABS_NUM] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= l /\ i <= l /\ &1 + l = L ==> &3 + l + i <= &3 * L`) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC
          THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_INV_MUL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2) * log(&N)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_EXPAND] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `e = inv(&27509489664 * L pow 9)` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * e * &46 * L pow 2` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&2 * e * &46 * L pow 2 <= norm(zeta s)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV] THEN
  SUBGOAL_THEN `&0 < norm(zeta s)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&46 * L pow 2` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&10 pow 11 * L pow 9) * (&2 * e * &46 * L pow 2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `(&10 pow 11 * L pow 9) * (&2 * e * &46 * L pow 2) =
                (&92 * &10 pow 11 / &27509489664) * L pow 2`
  SUBST1_TAC THENL
   [EXPAND_TAC "e" THEN
    SUBGOAL_THEN `~(L pow 9 = &0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The function pnt_zetaf without the pole at s = 1.                         *)
(* ------------------------------------------------------------------------- *)

let pnt_zetaf = new_definition
 `pnt_zetaf s =
  --(complex_derivative (nearzeta 1) s / (nearzeta 1 s + Cx(&1))) -
            (if s = Cx(&1) then complex_derivative (nearzeta 1) (Cx(&1))
             else nearzeta 1 s / (s - Cx(&1)))`;;

let PNT_ZETAF_HOLOMORPHIC = prove
 (`!U. U SUBSET {s | Re s > &0} /\
       (!s. s IN U ==> ~(nearzeta 1 s + Cx(&1) = Cx(&0)))
       ==> pnt_zetaf holomorphic_on U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `pnt_zetaf = \s. --(complex_derivative (nearzeta 1) s /
                   (nearzeta 1 s + Cx(&1))) -
                (\z. if z = Cx(&1) then complex_derivative (nearzeta 1)
                  (Cx(&1))
                     else (nearzeta 1 z - nearzeta 1 (Cx(&1))) /
                          (z - Cx(&1))) s`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pnt_zetaf] THEN
    SIMP_TAC[NEARZETA_1; LE_REFL; COMPLEX_SUB_RZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_NEG THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `{s | Re s > &0}` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE THEN
      SIMP_TAC[OPEN_HALFSPACE_RE_GT; HOLOMORPHIC_NEARZETA; LE_REFL];
      MATCH_MP_TAC HOLOMORPHIC_ON_ADD
        THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `{s | Re s > &0}` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_NEARZETA; LE_REFL]];
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `{s | Re s > &0}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POLE_LEMMA_OPEN THEN
    SIMP_TAC[OPEN_HALFSPACE_RE_GT; HOLOMORPHIC_NEARZETA; LE_REFL]]);;

let ZETA_DERIV_NEARZETA = prove
 (`!s. &0 < Re s /\ ~(s = Cx(&1))
       ==> complex_derivative zeta s =
           (complex_derivative (nearzeta 1) s * (s - Cx(&1)) -
            (nearzeta 1 s + Cx(&1)) * Cx(&1)) / (s - Cx(&1)) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`\w. (nearzeta 1 w + Cx(&1)) / (w - Cx(&1))`;
                        `{w | Re w > &0} DELETE Cx(&1)`] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_HALFSPACE_RE_GT; IN_DELETE; IN_ELIM_THM;
           real_gt] THEN
  ASM_SIMP_TAC[ZETA_NEARZETA] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DIV_AT THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM COMPLEX_ADD_RID] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST; ETA_AX] THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `{w | Re w > &0}` THEN
    ASM_SIMP_TAC[OPEN_HALFSPACE_RE_GT; HOLOMORPHIC_NEARZETA; LE_REFL;
                 IN_ELIM_THM; real_gt];
    SUBGOAL_THEN
     `((\w. w - Cx(&1)) has_complex_derivative (Cx(&1) - Cx(&0))) (at s)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_ID; HAS_COMPLEX_DERIVATIVE_CONST];
      REWRITE_TAC[COMPLEX_SUB_RZERO]]]);;

let PNT_ZETAF_EQ = prove
 (`!s. &0 < Re s /\ ~(s = Cx(&1)) /\ ~(zeta s = Cx(&0))
       ==> pnt_zetaf s = --(complex_derivative zeta s / zeta s) - zeta s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[pnt_zetaf; ZETA_DERIV_NEARZETA; ZETA_NEARZETA] THEN
  UNDISCH_TAC `~(zeta s = Cx(&0))` THEN ASM_SIMP_TAC[ZETA_NEARZETA] THEN
  UNDISCH_TAC `~(s = Cx(&1))` THEN CONV_TAC COMPLEX_FIELD);;

let PNT_ZETAF_DSERIES = prove
 (`!s. &1 < Re s ==> pnt_zetaf s = dseries (\n. Cx(mangoldt n - &1)) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s = Cx(&1)) /\ ~(zeta s = Cx(&0)) /\ &0 < Re s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 < Re(Cx(&1))` THEN
      REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[ZETA_NONZERO_LEMMA];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PNT_ZETAF_EQ] THEN
  MP_TAC(ISPECL [`\n:num. Cx(&1)`; `s:complex`] DSERIES_NEG_LOG_DERIV) THEN
  ASM_SIMP_TAC[COMPLEX_MUL_LID; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_LE_REFL;
               COMPLEX_MUL_RID; DSERIES_ZETA; ZETA_DERIV_DSERIES] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(\n. Cx(mangoldt n - &1)) =
                (\n. Cx(mangoldt n) + --(Cx(&1)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; CX_SUB] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. Cx(mangoldt n)`; `\n:num. --(Cx(&1))`; `&1`; `1`;
                 `s:complex`] DSERIES_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID; NORM_NEG; COMPLEX_NORM_CX;
                    REAL_ABS_NUM] THEN
    CONJ_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THENL
     [MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
      MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= log(&n)` MP_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 <= log(&n)` MP_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        REAL_ARITH_TAC]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\n:num. Cx(&1)`; `&1`; `1`; `s:complex`] DSERIES_NEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID; COMPLEX_NORM_CX;
                    REAL_ABS_NUM] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= log(&n)` MP_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      REAL_ARITH_TAC];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[DSERIES_ZETA] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[complex_div] THEN
  CONV_TAC COMPLEX_RING);;

let PNT_ZETAF_RECT = prove
 (`!N Th s. 16 <= N /\ &48 <= log(&N) /\ &2 * Th + &3 <= &N /\
           &1 - inv(&10 pow 11 * (&1 + log(&N)) pow 9) <= Re s /\
           Re s <= &2 /\ abs(Im s) <= Th
           ==> ~(nearzeta 1 s + Cx(&1) = Cx(&0)) /\
               norm(pnt_zetaf s) <= &2 * &10 pow 11 * (&1 + log(&N)) pow 9`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = &1 + log(&N)` THEN
  SUBGOAL_THEN `&49 <= L /\ &1 <= L pow 9 /\ L <= L pow 9`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&10 pow 11 * L pow 9) <= &1 / &48 /\
                inv(&10 pow 11 * L pow 9) <= inv(log(&N)) /\
                inv(log(&N)) <= &1 / &48`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ~(z = Cx(&1)) /\ ~(zeta z = Cx(&0))
        ==> ~(nearzeta 1 z + Cx(&1) = Cx(&0))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(zeta z = Cx(&0))` THEN ASM_SIMP_TAC[ZETA_NEARZETA] THEN
    REWRITE_TAC[complex_div; COMPLEX_MUL_LZERO];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 / &24 <= abs(Im s)` THENL
   [SUBGOAL_THEN `~(s = Cx(&1)) /\ &0 < Re s` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &24 <= abs(Im(Cx(&1)))`
        THEN REWRITE_TAC[IM_CX] THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`N:num`; `s:complex`] ZF_ZETA_LINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PNT_ZETAF_EQ] THEN
    MP_TAC(SPECL [`s:complex`; `N:num`] ZETA_STRIP_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        MP_TAC(SPEC `s:complex` COMPLEX_NORM_LE_RE_IM) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&9 / abs(Im s) <= &216` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < abs(Im s)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a b:complex x y z. norm a <= x /\ norm b <= y /\ x + y <= z
                         ==> norm(--a - b) <= z`) THEN
    EXISTS_TAC `&10 pow 11 * L pow 9` THEN
    EXISTS_TAC `&3 * L + &236` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 + &1 / &24 <= Re s` THENL
   [SUBGOAL_THEN `~(s = Cx(&1)) /\ &0 < Re s` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 + &1 / &24 <= Re(Cx(&1))`
        THEN REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`s:complex`; `&1 / &24`] ZF_ZETA_RIGHT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PNT_ZETAF_EQ] THEN
    MP_TAC(SPEC `s:complex` ZETA_RIGHT_NORM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `Re s / (Re s - &1) <= &48` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < Re s - &1` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a b:complex x y z. norm a <= x /\ norm b <= y /\ x + y <= z
                         ==> norm(--a - b) <= z`) THEN
    EXISTS_TAC `&12 / (&1 / &24) pow 2` THEN EXISTS_TAC `&48` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(s - Cx(&1)) <= &1 / &12` ASSUME_TAC THENL
   [MP_TAC(SPEC `s - Cx(&1)` COMPLEX_NORM_LE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; REAL_SUB_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `s:complex` ZF_ZETA_DISC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&3 / &4 <= norm(nearzeta 1 s + Cx(&1))` ASSUME_TAC THENL
   [MP_TAC(NORM_ARITH `norm(Cx(&1)) <= norm(nearzeta 1 s + Cx(&1)) +
                       norm(nearzeta 1 s)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&3 / &4 <= norm(nearzeta 1 s + Cx(&1))` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[pnt_zetaf] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b:complex x y z. norm a <= x /\ norm b <= y /\ x + y <= z
                       ==> norm(--a - b) <= z`) THEN
  EXISTS_TAC `&8` THEN EXISTS_TAC `&6` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_DIV] THEN
    SUBGOAL_THEN `&0 < norm(nearzeta 1 s + Cx(&1))` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_DIV] THEN
    SUBGOAL_THEN `&0 < norm(s - Cx(&1))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MP_TAC(SPEC `s:complex` NEARZETA_1_DISC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &10 pow 11 * &1` THEN
    CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC]) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Perron for a(n) = Lambda(n) - [n >= 2].                                   *)
(* ------------------------------------------------------------------------- *)

let PSI1_GEN = prove
 (`!a f x s1 Th M.
     (!n. 1 <= n ==> norm(a n) <= &1 + log(&n)) /\
     (!N. sum(1..N) (\n. norm(a n) * &n rpow (--(&1 + inv(log x))))
          <= &24 * log x pow 2) /\
     f holomorphic_on {s | s1 <= Re s /\ Re s <= &2 /\ abs(Im s) <= Th} /\
     (!s. &1 < Re s ==> f s = dseries a s) /\
     exp(&1) <= x /\ &1 / &2 <= s1 /\ s1 < &1 /\ &6 <= Th /\ &0 <= M /\
     (!s. s1 <= Re s /\ Re s <= &2 /\ abs(Im s) <= Th ==> norm(f s) <= M)
     ==> norm(vsum {n | 1 <= n /\ &n <= x} (\n. a n * Cx(&1 - &n / x)))
         <= &600 * x * log x pow 2 / Th + M * x / Th +
            Th * M * exp(s1 * log x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x /\ &1 <= log x` STRIP_ASSUME_TAC THENL
   [MP_TAC REAL_EXP_POS_LT THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cc = &1 + inv(log x)` THEN
  SUBGOAL_THEN `&1 < cc /\ cc <= &2 /\ s1 < cc /\
                exp(cc * log x) = exp(&1) * x`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    SUBGOAL_THEN `&0 < inv(log x) /\ inv(log x) <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID; REAL_EXP_ADD] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_MUL_LINV; REAL_ARITH `&1 <= l ==> ~(l = &0)`]
    THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num->complex`; `&1`; `1`; `x:real`; `cc:real`;
                 `Th:real`; `&24 * log x pow 2`] PERRON_SERIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `S0 = &24 * log x pow 2` THEN
  ABBREV_TAC `R0 = {s | s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th}` THEN
  ABBREV_TAC `G = \s. (f:complex->complex) s *
                      cexp(s * Cx(log x)) / (s * (s + Cx(&1)))` THEN
  SUBGOAL_THEN
   `R0 SUBSET {s | s1 <= Re s /\ Re s <= &2 /\ abs(Im s) <= Th} /\
    (!s. s IN R0 ==> &1 / &2 <= Re s)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `s:complex` THEN STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `G holomorphic_on R0` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET];
      MATCH_MP_TAC KERNEL_HOLOMORPHIC THEN X_GEN_TAC `s:complex` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:complex`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
      REWRITE_TAC[RE_NEG; RE_CX] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_integral (linepath(Cx cc - ii * Cx Th,Cx cc + ii * Cx Th))
      (\s. dseries a s * cexp(s * Cx(log x)) / (s * (s + Cx(&1)))) =
    path_integral (linepath(Cx cc - ii * Cx Th,Cx cc + ii * Cx Th)) G`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PATH_INTEGRAL_EQ THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    X_GEN_TAC `s:complex` THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP SEGMENT_VERTICAL_LINE) THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:complex` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `dseries`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. (!u. u IN segment[p,q] ==> s1 <= Re u /\ Re u <= cc /\
                                     abs(Im u) <= Th)
          ==> segment[p,q] SUBSET R0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "R0" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `R0:complex->bool`; `cc:real`;
                 `s1:real`; `Th:real`] RECTANGLE_SHIFT) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "R0" THEN REWRITE_TAC[RECT_CONVEX] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `u:complex` THEN
    DISCH_THEN(MP_TAC o MATCH_MP SEGMENT_COMPONENTS) THEN
    REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_CX; IM_CX; RE_MUL_II;
                IM_MUL_II; REAL_NEG_0; REAL_SUB_RZERO; REAL_ADD_RID;
                REAL_SUB_LZERO; REAL_ADD_LID] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `(G:complex->complex) continuous_on R0 /\
    (!s. s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th
         ==> norm(G s) <= M * exp(Re s * log x) / norm(s * (s + Cx(&1))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
    X_GEN_TAC `s:complex` THEN STRIP_TAC THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; NORM_NEG; NORM_CEXP;
                RE_MUL_CX] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `M:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN
      SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_MUL; NORM_POS_LE]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`G:complex->complex`; `s1:real`; `cc:real`; `Th:real`;
                `M:real`; `x:real`; `--Th:real`] RECT_HORIZ_BOUND) THEN
  MP_TAC(SPECL [`G:complex->complex`; `s1:real`; `cc:real`; `Th:real`;
                `M:real`; `x:real`; `Th:real`] RECT_HORIZ_BOUND) THEN
  MP_TAC(SPECL [`G:complex->complex`; `s1:real`; `cc:real`; `Th:real`;
                `M:real`; `x:real`] RECT_VERT_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
  SUBGOAL_THEN `&1 <= Th /\ abs Th = Th /\ &1 <= x` STRIP_ASSUME_TAC THENL
   [MP_TAC REAL_EXP_POS_LT THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_RNEG; GSYM complex_sub] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `I1 = path_integral
                    (linepath (Cx cc - ii * Cx Th,Cx s1 - ii * Cx Th)) G` THEN
  ABBREV_TAC `I2 = path_integral
                    (linepath (Cx s1 - ii * Cx Th,Cx s1 + ii * Cx Th)) G` THEN
  ABBREV_TAC `I3 = path_integral
                    (linepath (Cx s1 + ii * Cx Th,Cx cc + ii * Cx Th)) G` THEN
  ABBREV_TAC `Ps = vsum {n | 1 <= n /\ &n <= x}
                     (\n. a n * Cx(&1 - &n / x))` THEN
  SUBGOAL_THEN `&6 <= &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(Cx(&2) * Cx pi * ii * Ps) = &2 * pi * norm(Ps:complex)`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X1 = exp(s1 * log x)` THEN
  SUBGOAL_THEN `&0 <= X1 /\ exp(&1) <= &4 /\ &0 <= log x pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X1" THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_1_LE_4;
                                     REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * pi * norm(Ps:complex) <=
                &32 * (exp(&1) * x) / Th * S0 +
                &2 * (&2 * M * (exp(&1) * x) / Th pow 2) + &4 * Th * M * X1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> can (find_term ((=) `pi`)) (concl th) &&
                       is_eq(concl th))) THEN
    MATCH_MP_TAC(NORM_ARITH
     `!p i1 i2 i3:complex a b c.
        norm((i1 + i2 + i3) - p) <= a /\ norm i1 <= b /\ norm i2 <= c /\
        norm i3 <= b
        ==> norm p <= a + &2 * b + c`) THEN
    MAP_EVERY EXISTS_TAC [`I1:complex`; `I2:complex`; `I3:complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Th /\ &0 <= x / Th /\ &0 <= S0` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "S0" THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&32 * (exp(&1) * x) / Th * S0 <=
                &3072 * log x pow 2 * (x / Th)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&32 * (exp(&1) * x) / Th * S0 =
                  (&32 * exp(&1) * S0) * (x / Th)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Th` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_ARITH `&3072 * l = &32 * (&4 * (&24 * l)):real`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
    EXPAND_TAC "S0" THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &2 * M * (exp(&1) * x) / Th pow 2 <= &6 * (M * x / Th)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * &2 * M * (exp(&1) * x) / Th pow 2 =
                  ((&4 * exp(&1)) / Th) * (M * x / Th)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Th` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[GSYM real_div]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Th * M * X1 /\ &0 <= M * x / Th /\
                &0 <= log x pow 2 * (x / Th)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN TRY(ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[GSYM real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 * norm(Ps:complex) <= &2 * pi * norm Ps` MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&600 * x * log x pow 2 / Th = &600 * (log x pow 2 * (x / Th))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < Th` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let LAMBDA_LOG_SERIES_BOUND = prove
 (`!f x N. (!n. norm(f n) <= &1) /\ exp(&1) <= x
           ==> sum(1..N) (\n. norm(Cx(mangoldt n) * f n) *
                              &n rpow (--(&1 + inv(log x))))
               <= &12 * log x pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x /\ &1 <= log x` STRIP_ASSUME_TAC THENL
   [MP_TAC REAL_EXP_POS_LT THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cc = &1 + inv(log x)` THEN
  SUBGOAL_THEN `&1 < cc` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN MATCH_MP_TAC(REAL_ARITH `&0 < y ==> &1 < &1 + y`)
    THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / (cc - &1) * exp((cc - &1) / &2) * (&1 + &2 / (cc - &1))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC LAMBDA_SERIES_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `S0 = &2 / (cc - &1) * exp((cc - &1) / &2) *
                   (&1 + &2 / (cc - &1))` THEN
  EXPAND_TAC "S0" THEN EXPAND_TAC "cc" THEN
    REWRITE_TAC[REAL_ADD_SUB] THEN
    ASM_SIMP_TAC[REAL_INV_DIV; REAL_ARITH `&1 <= l ==> ~(l = &0)`;
                 real_div; REAL_INV_INV] THEN
    SUBGOAL_THEN `exp(inv(log x) * inv(&2)) <= &2` ASSUME_TAC THENL
     [MP_TAC(SPEC `inv(log x) * inv(&2)` REAL_EXP_BOUND_LEMMA) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(log x) <= &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * log x) * &2 * (&3 * log x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]);;

let ONE_LOG_SERIES_BOUND = prove
 (`!x N. exp(&1) <= x
         ==> sum(1..N) (\n. &n rpow (--(&1 + inv(log x)))) <= &1 + log x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log x` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1..N = 1 INSERT (1 + 1..N)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG; ARITH_RULE `~(1 + 1 <= 1)`]
  THEN REWRITE_TAC[RPOW_ONE] THEN
  MATCH_MP_TAC(REAL_ARITH `s <= l ==> &1 + s <= &1 + l`) THEN
  MP_TAC(SPECL [`1`; `N:num`; `inv(log x)`] SUM_RPOW_TAIL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RPOW_ONE; REAL_ARITH `inv l + &1 = &1 + inv l`] THEN
  ASM_SIMP_TAC[real_div; REAL_INV_INV; REAL_MUL_LID]);;

let MANGOLDT_ONE_SERIES_BOUND = prove
 (`!x N. exp(&1) <= x
         ==> sum(1..N) (\n. norm(Cx(mangoldt n - &1)) *
                            &n rpow (--(&1 + inv(log x))))
             <= &24 * log x pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log x` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\n. norm(Cx(mangoldt n) * Cx(&1)) *
                             &n rpow (--(&1 + inv(log x)))) +
              sum(1..N) (\n. &n rpow (--(&1 + inv(log x))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM;
                REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `b * r + r = (b + &1) * r`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num. Cx(&1)`; `x:real`; `N:num`]
    LAMBDA_LOG_SERIES_BOUND) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_LE_REFL] THEN
  MP_TAC(SPECL [`x:real`; `N:num`] ONE_LOG_SERIES_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `log x <= log x pow 2` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID]
    THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let PSI1_ZETA = prove
 (`!x N Th.
     exp(&1) <= x /\ &6 <= Th /\ 16 <= N /\ &48 <= log(&N) /\
     &2 * Th + &3 <= &N
     ==> norm(vsum {n | 1 <= n /\ &n <= x}
                   (\n. Cx(mangoldt n - &1) * Cx(&1 - &n / x)))
         <= &600 * x * log x pow 2 / Th +
            (&2 * &10 pow 11 * (&1 + log(&N)) pow 9) * x / Th +
            Th * (&2 * &10 pow 11 * (&1 + log(&N)) pow 9) *
            exp((&1 - inv(&10 pow 11 * (&1 + log(&N)) pow 9)) * log x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = &1 + log(&N)` THEN
  SUBGOAL_THEN `&49 <= L /\ &1 <= L pow 9` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&10 pow 11 * L pow 9) /\
                inv(&10 pow 11 * L pow 9) <= &1 / &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC PSI1_GEN THEN EXISTS_TAC `pnt_zetaf` THEN
  ASM_SIMP_TAC[MANGOLDT_ONE_SERIES_BOUND; PNT_ZETAF_DSERIES] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN
    MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
    MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= log(&n)` MP_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      REAL_ARITH_TAC];
    MATCH_MP_TAC PNT_ZETAF_HOLOMORPHIC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:complex` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:complex` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`N:num`; `Th:real`; `s:complex`] PNT_ZETAF_RECT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:complex` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `Th:real`; `s:complex`] PNT_ZETAF_RECT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MANGOLDT_ONE_COEFF_BOUND = prove
 (`!n. 1 <= n
       ==> norm(Cx(if n = 1 then &0 else mangoldt n - &1)) <= log(&n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ABS_NUM; LOG_1; REAL_LE_REFL] THEN
  MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
  MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`2`; `1`] MANGOLDT_PRIMEPOW) THEN
    REWRITE_TAC[PRIME_2; EXP_1; LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&n)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
    CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3` THEN
    REWRITE_TAC[EXP_1_LE_3; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    REAL_ARITH_TAC]);;

let PNT_PSI1_ADJUST = prove
 (`!X E. &1 <= X /\
         norm(vsum {n | 1 <= n /\ &n <= X}
                   (\n. Cx(mangoldt n - &1) * Cx(&1 - &n / X))) <= E
         ==> norm(vsum {n | 1 <= n /\ &n <= X}
                       (\n. Cx(if n = 1 then &0 else mangoldt n - &1) *
                            Cx(&1 - &n / X))) <= E + &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b:complex. norm(a - b) <= &1 /\ norm b <= E ==> norm a <= E + &1`) THEN
  EXISTS_TAC `vsum {n | 1 <= n /\ &n <= X}
                   (\n. Cx(mangoldt n - &1) * Cx(&1 - &n / X))` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUM_RANGE_LE] THEN
  SUBGOAL_THEN
   `!n. Cx(if n = 1 then &0 else mangoldt n - &1) * Cx(&1 - &n / X) -
        Cx(mangoldt n - &1) * Cx(&1 - &n / X) =
        if n = 1 then Cx(&1 - &1 / X) else vec 0`
  (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[MANGOLDT_1; COMPLEX_VEC_0] THEN
    REWRITE_TAC[CX_SUB; CX_DIV] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_DELTA; IN_ELIM_THM; LE_REFL] THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `&0 < X /\ &1 / X <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= X ==> &0 < X`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 / X` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let PNT_THETA_FROM_PSI1 = prove
 (`!x h E.
     &4 <= x /\ &0 < h /\ h <= x /\
     (!X. exp(&1) <= X /\ X <= &2 * x
          ==> norm(vsum {n | 1 <= n /\ &n <= X}
                        (\n. Cx(mangoldt n - &1) * Cx(&1 - &n / X))) <= E)
     ==> abs(sum {p | prime p /\ &p <= x} (\p. log(&p)) - x) <=
         &3 * x * (E + &1) / h + (h + &1) * log(&2 * x) + &2 +
         sqrt x * log x pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&4`) THEN ANTS_TAC THENL
     [MP_TAC REAL_EXP_1_LE_4 THEN ASM_REAL_ARITH_TAC;
      MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `4 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&3 < &N` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {p | prime p /\ &p <= x} (\p. log(&p)) =
    sum(1..N) (\m. if prime m then log(&m) else &0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN EQ_TAC THEN STRIP_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `2 <= p` THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
        SUBGOAL_THEN `&p < &N + &1` MP_TAC THENL
         [ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
          ARITH_TAC]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `psi = sum(1..N) (\m. mangoldt m)` THEN
  ABBREV_TAC `th = sum(1..N) (\m. if prime m then log(&m) else &0)` THEN
  SUBGOAL_THEN `&0 <= psi - th /\ psi - th <= sqrt(&N) * log(&N) pow 2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["psi"; "th"] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN
      STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
       [MP_TAC(SPECL [`m:num`; `1`] MANGOLDT_PRIMEPOW) THEN
        ASM_REWRITE_TAC[EXP_1; LE_REFL] THEN REAL_ARITH_TAC;
        MP_TAC(SPEC `m:num` MANGOLDT_POS_LE) THEN REAL_ARITH_TAC];
      MATCH_MP_TAC PRIME_POWER_SUM_BOUND THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. Cx(if n = 1 then &0 else mangoldt n - &1)`; `&N`;
                 `h:real`] PSI_FROM_PSI1) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_ACCEPT_TAC MANGOLDT_ONE_COEFF_BOUND;
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum {n | 1 <= n /\ &n <= &N}
         (\n. Cx(if n = 1 then &0 else mangoldt n - &1)) =
    Cx(psi - (&N - &1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[NUMSEG_AS_UPTO; VSUM_CX] THEN AP_TERM_TAC THEN
    EXPAND_TAC "psi" THEN
    SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; ASSUME `1 <= N`] THEN
    REWRITE_TAC[MANGOLDT_1; ARITH] THEN
    SUBGOAL_THEN `sum(2..N) (\n. if n = 1 then &0 else mangoldt n - &1) =
                  sum(2..N) (\n. mangoldt n - &1)` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(i = 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; ETA_AX; REAL_MUL_RID] THEN
    SUBGOAL_THEN `&((N + 1) - 2) = &N - &1` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `1 <= N ==> 2 <= N + 1`]
      THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&N + h`; `E:real`] PNT_PSI1_ADJUST) THEN
  MP_TAC(SPECL [`&N`; `E:real`] PNT_PSI1_ADJUST) THEN
  SUBGOAL_THEN `exp(&1) <= &N` ASSUME_TAC THENL
   [MP_TAC REAL_EXP_1_LE_4 THEN UNDISCH_TAC `4 <= N` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ABBREV_TAC `S1 = norm(vsum {n | 1 <= n /\ &n <= &N + h}
     (\n. Cx(if n = 1 then &0 else mangoldt n - &1) *
          Cx(&1 - &n / (&N + h))))` THEN
  ABBREV_TAC `S2 = norm(vsum {n | 1 <= n /\ &n <= &N}
     (\n. Cx(if n = 1 then &0 else mangoldt n - &1) * Cx(&1 - &n / &N)))` THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((&N + h) * S1 + &N * S2) / h <= ((&3 * x) * (E + &1)) / h`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&N + h) * (E + &1) + &N * (E + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL
      THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&N + h) <= log(&2 * x) /\ &0 <= h + &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h + &1) * log(&N + h) <= (h + &1) * log(&2 * x)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&N) * log(&N) pow 2 <= sqrt x * log x pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let PSI1_ZETA_MONO = prove
 (`!Tn x X Lg.
     6 <= Tn /\ &1 + log(&(16 * 1 * (Tn + 4))) = Lg /\ &49 <= Lg /\
     exp(&1) <= X /\ X <= &2 * x
     ==> norm(vsum {n | 1 <= n /\ &n <= X}
                   (\n. Cx(mangoldt n - &1) * Cx(&1 - &n / X))) <=
         &600 * (&2 * x) * log(&2 * x) pow 2 / &Tn +
         (&2 * &10 pow 11 * Lg pow 9) * (&2 * x) / &Tn +
         &Tn * (&2 * &10 pow 11 * Lg pow 9) *
         exp((&1 - inv(&10 pow 11 * Lg pow 9)) * log(&2 * x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`X:real`; `16 * 1 * (Tn + 4)`; `&Tn`] PSI1_ZETA) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' /\ c <= c'
                           ==> x <= a + b + c ==> x <= a' + b' + c'`) THEN
  SUBGOAL_THEN `&1 <= X /\ &0 < X /\ &0 <= log X /\ log X <= log(&2 * x) /\
                &0 < &Tn`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= X` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_POS; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= Lg pow 9` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * &10 pow 11 * Lg pow 9 /\
                &0 <= &1 - inv(&10 pow 11 * Lg pow 9)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
    ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The prime number theorem with error term.                                 *)
(* ------------------------------------------------------------------------- *)

let PNT_MZ_DZ_BOUNDS = prove
 (`!w A Tn Lg.
     &2 <= w /\ &Tn <= w pow (16 * A + 24) + &1 /\
     &1 + log(&(16 * 1 * (Tn + 4))) = Lg
     ==> &2 * &10 pow 11 * Lg pow 9 <=
         (&2 * &10 pow 11 *
          (&2 * &24 pow 12 * (&8 + &(16 * A + 24)) pow 12)) * w pow 5 /\
         inv(&10 pow 11 *
             (&2 * &24 pow 12 * (&8 + &(16 * A + 24)) pow 12)) * w pow 5
         <= inv(&10 pow 11 * Lg pow 9) * w pow 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K3 = &2 * &24 pow 12 * (&8 + &(16 * A + 24)) pow 12` THEN
  MP_TAC(SPECL [`1`; `Tn:num`; `w:real`; `0`; `16 * A + 24`] LG_W_BOUND) THEN
  ASM_REWRITE_TAC[real_pow; LE_REFL; REAL_LE_REFL; REAL_MUL_RZERO;
                  REAL_ADD_RID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= Lg` ASSUME_TAC THENL
   [EXPAND_TAC "Lg" THEN
    REWRITE_TAC[REAL_ARITH `&1 <= &1 + x <=> &0 <= x`] THEN
    MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Lg:real) pow 9 <= K3 * w` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Lg:real) pow 12` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((&8 + &(16 * A + 24)) * (&1 + log w)) pow 12` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "K3" THEN REWRITE_TAC[REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * b * c * w = c * (a * b * w):real`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC ONE_PLUS_LOG_POW THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K3 /\ &1 <= (Lg:real) pow 9 /\ w <= (w:real) pow 5 /\
                (w:real) pow 5 <= w pow 7`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "K3" THEN MATCH_MP_TAC REAL_LT_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ARITH_TAC];
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K3 * w:real` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&10 pow 11 * K3) * (w:real) pow 7` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&10 pow 11 * (K3 * w)) * (w:real) pow 8` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `&0 < w` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < K3` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;

let THETA_TRIVIAL = prove
 (`!x. &1 <= x
       ==> &0 <= sum {p | prime p /\ &p <= x} (\p. log(&p)) /\
           sum {p | prime p /\ &p <= x} (\p. log(&p)) <= x * log x`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_PRIMES_LE_REAL; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{p | prime p /\ &p <= x} SUBSET 1..N` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN X_GEN_TAC `p:num` THEN
    STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    SUBGOAL_THEN `(&p:real) < &N + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ &p <= x} (\p. log x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_PRIMES_LE_REAL; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_PRIMES_LE_REAL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[LOG_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N:real` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_NUMSEG]);;

let PNT_THETA_ERROR = prove
 (`!A. ?Cb. !x. &2 <= x
               ==> abs(sum {p | prime p /\ &p <= x} (\p. log(&p)) - x) <=
                   Cb * x / log x pow A`,
  GEN_TAC THEN
  ABBREV_TAC `K3 = &2 * &24 pow 12 * (&8 + &(16 * A + 24)) pow 12` THEN
  ABBREV_TAC `KM = &2 * &10 pow 11 * K3` THEN
  ABBREV_TAC `cd = inv(&10 pow 11 * K3)` THEN
  ABBREV_TAC `m = 7 * A + 8` THEN
  ABBREV_TAC `CE = &12000 + &6 * KM + &12 * KM * (&m / cd) pow m` THEN
  ABBREV_TAC `CS = &2 + &2 * (&2 * &(A + 1)) pow (A + 1) +
                   &6 * (&2 * &A) pow A + (&2 * &(A + 2)) pow (A + 2)` THEN
  ABBREV_TAC `CL = &3 * (&2 * &(2 * A + 1)) pow (2 * A + 1)` THEN
  ABBREV_TAC `C0 = &2 * exp(&16) pow (A + 1)` THEN
  SUBGOAL_THEN `&0 < K3 /\ &0 < cd /\ &0 <= KM /\ &0 <= CE /\ &0 <= CS /\
                &0 <= CL /\ &0 <= C0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < K3` ASSUME_TAC THENL
     [EXPAND_TAC "K3" THEN MATCH_MP_TAC REAL_LT_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= KM /\ &0 < cd` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["KM"; "cd"] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
        ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["CE"; "CS"; "CL"; "C0"] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ &0 <= a * b ==> &0 <= &12000 + &6 * a + &12 * a * b`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS];
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= &2 + &2 * a + &6 * b + c`) THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
      ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
      ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_EXP_POS_LE]];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * CE + CS + CL + C0` THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  ABBREV_TAC `th = sum {p | prime p /\ &p <= x} (\p. log(&p))` THEN
  ABBREV_TAC `u = log x` THEN
  SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u pow A /\ &0 <= x / u pow A` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= CE * x / u pow A /\ &0 <= CS * x / u pow A /\
                &0 <= CL * x / u pow A /\ &0 <= C0 * x / u pow A`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `u < exp(&16)` THENL
   [MP_TAC(SPEC `x:real` THETA_TRIVIAL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `x * (u + &1) <= C0 * x / u pow A` ASSUME_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(x * a) * b = x * a * b:real`] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * exp(&16)) * exp(&16) pow A` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MP_TAC(SPEC `&16` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
        EXPAND_TAC "C0" THEN REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= x * u` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&256 <= u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&16)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `exp(&16) = exp(&4) pow 4` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&5:real) pow 4` THEN
    CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    MP_TAC(SPEC `&4` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `u:real` W_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `w = exp(log u / &8)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `exp(&2) <= w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `&16 <= l ==> &2 <= l / &8`) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= x` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp u = x` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `log x = u`)) THEN MATCH_MP_TAC EXP_LOG THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `u:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&48) <= (w:real) pow (16 * A + 24)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(w:real) pow 24` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&2) pow 24` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]];
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPEC `(w:real) pow (16 * A + 24)` FLOOR_POS) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  MP_TAC(SPEC `(w:real) pow (16 * A + 24)` FLOOR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Tn = N0 + 1` THEN
  SUBGOAL_THEN `(w:real) pow (16 * A + 24) <= &Tn /\
                &Tn <= w pow (16 * A + 24) + &1 /\
                &Tn <= &2 * w pow (16 * A + 24) /\ 6 <= Tn /\
                exp(&48) <= &Tn`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&48` REAL_EXP_LE_X) THEN DISCH_TAC THEN
    EXPAND_TAC "Tn" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Lg = &1 + log(&(16 * 1 * (Tn + 4)))` THEN
  SUBGOAL_THEN `&49 <= Lg` ASSUME_TAC THENL
   [EXPAND_TAC "Lg" THEN
    MATCH_MP_TAC(REAL_ARITH `&48 <= l ==> &49 <= &1 + l`) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Tn:real` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * &10 pow 11 * Lg pow 9` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h = (x:real) / u pow (A + 1)` THEN
  SUBGOAL_THEN `&0 < h /\ h <= x /\ (x:real) / h = u pow (A + 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SUBGOAL_THEN `&1 <= u pow (A + 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * y ==> x <= x * y`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(x = &0) /\ ~(u pow (A + 1) = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  ABBREV_TAC
   `E6 = &600 * (&2 * x) * log(&2 * x) pow 2 / &Tn +
         (&2 * &10 pow 11 * Lg pow 9) * (&2 * x) / &Tn +
         &Tn * (&2 * &10 pow 11 * Lg pow 9) *
         exp((&1 - inv(&10 pow 11 * Lg pow 9)) * log(&2 * x))` THEN
  ABBREV_TAC
   `E5 = &500 * (&2 * x) * log(&2 * x) pow 2 / &Tn +
         (&2 * &10 pow 11 * Lg pow 9) * (&2 * x) / &Tn +
         &Tn * (&2 * &10 pow 11 * Lg pow 9) *
         exp((&1 - inv(&10 pow 11 * Lg pow 9)) * log(&2 * x))` THEN
  SUBGOAL_THEN `E6 <= &6 / &5 * E5` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E6"; "E5"] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c
      ==> &600 * a + b + c <= &6 / &5 * (&500 * a + b + c)`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real) / h * E6 <= x / h * (&6 / &5 * E5)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * u pow (A + 1) <= CL * x / u pow A` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2 * A + 1`; `x:real`] LOG_POW_LE_SQRT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sqrt x <= x` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * x ==> x <= x * x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&3 * u pow (A + 1) = (&3 * u pow (2 * A + 1)) / u pow A`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "CL" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * &(2 * A + 1)) pow (2 * A + 1) * sqrt x` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`w:real`; `A:num`; `Tn:num`; `Lg:real`] PNT_MZ_DZ_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `u:real`; `w:real`; `A:num`; `Tn:num`;
                `&2 * &10 pow 11 * Lg pow 9`; `inv(&10 pow 11 * Lg pow 9)`;
                `KM:real`; `cd:real`; `m:num`; `E5:real`] SW_E_TERM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `A:num`] SW_SMALL_TERMS) THEN
  MP_TAC(SPECL [`x:real`; `h:real`; `E6:real`] PNT_THETA_FROM_PSI1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `X:real` THEN STRIP_TAC THEN
    EXPAND_TAC "E6" THEN MATCH_MP_TAC PSI1_ZETA_MONO THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`(x:real) / h * E6 <= x / h * (&6 / &5 * E5)`;
    `(x:real) / h = u pow (A + 1)`;
    `&3 * u pow (A + 1) <= CL * x / u pow A`;
    `&0 <= CE * x / u pow A`; `&0 <= C0 * x / u pow A`] THEN
  REAL_ARITH_TAC);;
