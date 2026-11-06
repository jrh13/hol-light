(* ========================================================================= *)
(* Hua's theorem I: the minor arcs.  For the prime square sum                *)
(*   T(x) = sum_{n <= P} Lambda(n) e(x n^2)                                  *)
(* and j/M off the major arcs circ_major M Kw Q (vinogradov.ml),             *)
(*   HUA_MINOR_LAMBDA: |T(j/M)| <= 18 U + (type I terms) + (type II term),   *)
(* an explicit bound which is at most P / log^7 P times any given e > 0 for  *)
(* U = V = log^191 P, Q of order log^784 P and Kw = N / Q (hua.ml).          *)
(* Method.  Vaughan's identity (VAUGHAN_VSUM_GEN) with parameters U, V.      *)
(* * Quadratic Weyl differencing on an interval (QWEYL_INTERVAL):            *)
(*   |sum_{A < n <= A + L} e(y n^2)|^2 <= L + 4 sum_{e <= L} emin(L, 2 e y). *)
(* * Type I (TYPEI_S1, TYPEI_S2): for y = x d^2 a fresh Dirichlet            *)
(*   approximation of 2 y; a small denominator would put j on a major arc    *)
(*   (MINOR_FAR_FRACTION), so EMIN_SUM_CONST applies; hua_e1 collects the    *)
(*   saving, the log weights by Abel summation (LOG_WEIGHT_BOUND).           *)
(* * Type II (HUA_S3_BOUND): dyadic blocks in m, Cauchy-Schwarz over m and   *)
(*   over (k1, k2), Weyl in m, then two fibre Cauchy-Schwarz steps with      *)
(*   sum_{n <= X} tau(n)^2 <= X (1 + log X)^3 (FIBRE_TAU, TAU_SQUARE_SUM,    *)
(*   TAU_CS) reduce everything to sum_{n <= X} emin(M0, n x), bounded with   *)
(*   the Dirichlet approximation of x (MINOR_DIRICHLET).  No divisor bound   *)
(*   tau(n) <= C n^e is needed.                                              *)
(* ========================================================================= *)

needs "Sieve/vinogradov.ml";;
needs "Sieve/waring_weyl.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Quadratic Weyl differencing on an interval.                               *)
(* ------------------------------------------------------------------------- *)

let SUM_LT_SPLIT0 = prove
 (`!L a (h:num->real).
     &0 <= a /\ (!e. &0 <= h e)
     ==> sum {e | e < L} (\e. if e = 0 then a else h e) <= a + sum(1..L) h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NUMSEG_LT] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!b c. b <= c ==> a + b <= a + c`) THEN
  TRANS_TAC REAL_LE_TRANS `sum(0 + 1..L - 1) h` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG] THEN ARITH_TAC]);;

let QWEYL_INTERVAL = prove
 (`!y A L. norm(vsum(A+1..A+L) (\n. expi(&(n EXP 2) * y))) pow 2
           <= &L + &4 * sum(1..L) (\e. emin (&L) (&e * (&2 * y)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `vsum(A+1..A+L) (\n. expi(&(n EXP 2) * y)) =
    vsum(1..L) (\n. expi((\n. &((n + A) EXP 2) * y) n))`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[VSUM_OFFSET] THEN
    REWRITE_TAC[ADD_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. &((n + A) EXP 2) * y`; `L:num`; `L:num`] WEYL_STEP) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {e | e < L}
      (\e. if e = 0 then &L else &4 * emin (&L) (&e * &2 * y))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LT_SPLIT0 THEN REWRITE_TAC[REAL_POS] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. &(((n + e) + A) EXP 2) * y - &((n + A) EXP 2) * y =
        &n * (&e * &2 * y) + (&e * &e + &2 * &e * &A) * y`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXPI_ADD] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  ABBREV_TAC `z = vsum(1..L - e) (\n. expi(&n * &e * &2 * y))` THEN
  ABBREV_TAC `c = expi((&e * &e + &2 * &e * &A) * y)` THEN
  SUBGOAL_THEN `norm(c:complex) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[NORM_EXPI]; ALL_TAC] THEN
  SUBGOAL_THEN `Re(z * c) <= norm(z:complex)` ASSUME_TAC THENL
   [MP_TAC(SPEC `z * c:complex` COMPLEX_NORM_GE_RE_IM) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:complex) <= &L /\
                norm(z:complex) <= &2 * emin (&L) (&e * &2 * y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `sum(1..L - e) (\n. &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_NORM_LE THEN
        REWRITE_TAC[FINITE_NUMSEG; NORM_EXPI; REAL_LE_REFL];
        REWRITE_TAC[SUM_CONST_NUMSEG; REAL_MUL_RID; REAL_OF_NUM_LE] THEN
        ARITH_TAC];
      MP_TAC(SPECL [`&e * &2 * y:real`; `0`;
       `L - e:num`] VSUM_EXPI_INTERVAL) THEN
      REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= &2 * b ==> a <= &2 * c`) THEN
      MATCH_MP_TAC EMIN_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Type I sums.                                                              *)
(* ------------------------------------------------------------------------- *)

let MINOR_FAR_FRACTION = prove
 (`!M Kw Q j b q.
     j < M /\ ~(j IN circ_major M Kw Q) /\ 1 <= q /\ q <= Q
     ==> inv(&Kw) < ndist(&j / &M - &b / &q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b:num`; `q:num`] GCD_COPRIME_EXISTS) THEN
  ABBREV_TAC `g = gcd(b,q)` THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:num` (X_CHOOSE_THEN `q1:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(q1 = 0) /\ ~(g = 0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `q = q1 * g:num` THEN UNDISCH_TAC `1 <= q` THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `q1 = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_CASES_TAC `g = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~(j IN circ_major M Kw Q)` THEN
  REWRITE_TAC[circ_major; UNIONS_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
  EXISTS_TAC `q1:num` THEN
  SUBGOAL_THEN `1 <= q1 /\ q1 <= Q` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC LE_TRANS `q:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `q1 = q1 * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `b1 MOD q1` THEN
  ASM_REWRITE_TAC[MOD_LT_EQ; COPRIME_LMOD; circ_arc; IN_ELIM_THM] THEN
  SUBGOAL_THEN `&j / &M - &(b1 MOD q1) / &q1 =
                (&j / &M - &b / &q) + &(b1 DIV q1)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`b1:num`; `q1:num`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `real_of_num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&0 < &q1 /\ &0 < &g` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[NDIST_INTEGER_ADD; INTEGER_CLOSED] THEN FIRST_ASSUM ACCEPT_TAC);;

let TYPEI_SINGLE = prove
 (`!M Kw Q j d R.
     j < M /\ ~(j IN circ_major M Kw Q) /\ 1 <= d /\ 1 <= R /\ 1 <= Q /\
     1 <= Kw /\ &Kw <= &2 * &d pow 2 * &R
     ==> !H H'. H' <= H
                ==> norm(vsum(1..H')
                       (\h. expi(&(h EXP 2) * (&d pow 2 * &j / &M)))) pow 2
                    <= &H + &4 * (&14 * &d pow 2 * &H pow 2 / &Q +
                                  &4 * &H * (&1 + log(&R)) + &7 * &H +
                                  &4 * &R * (&1 + log(&R)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `y = &d pow 2 * &j / &M` THEN
  SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_DIV];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&2 * y`; `R:num`] DIRICHLET_APPROX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `r:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < &r /\ &0 < &d /\ &0 < &R /\ &0 < &Kw`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Q < 2 * d EXP 2 * r` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `ndist(&j / &M - &b / &(2 * d EXP 2 * r)) <= inv(&Kw)`
    MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN
      MATCH_MP_TAC MINOR_FAR_FRACTION THEN EXISTS_TAC `Q:num` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
      ASM_ARITH_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `abs(&j / &M - &b / &(2 * d EXP 2 * r))` THEN
    REWRITE_TAC[NDIST_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    SUBGOAL_THEN
     `&j / &M - &b / (&2 * &d pow 2 * &r) =
      (&r * &2 * y - &b) / (&2 * &d pow 2 * &r)`
    SUBST1_TAC THENL
     [EXPAND_TAC "y" THEN
      SUBGOAL_THEN `~(&r = &0) /\ ~(&d = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * &d pow 2 * &r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
      ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    TRANS_TAC REAL_LE_TRANS `inv(&R)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `inv(&Kw) * &2 * &d pow 2 * &r = (&2 * &d pow 2 * &r) / &Kw`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    TRANS_TAC REAL_LE_TRANS `&2 * &d pow 2 * &R` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (&2 * &d pow 2 * &R) * (&r - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE;
         REAL_LT_IMP_LE];
        UNDISCH_TAC `1 <= r` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
        REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`y:real`; `0`; `H':num`] QWEYL_INTERVAL) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  MATCH_MP_TAC(REAL_ARITH `!b c. b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `abs(&2 * y - &b / &r) <= inv(&r pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * y - &b / &r = (&r * &2 * y - &b) / &r` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_POW_2; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&R)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&2 * y`; `b:num`; `r:num`; `&H`; `H':num`; `&0`]
    EMIN_SUM_CONST) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_ADD_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(1..H') (\e. emin (&H') (&e * &2 * y)) <=
    sum(1..H') (\k. emin (&H) (&k * &2 * y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC EMIN_MONO THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&H' / &r <= &2 * &d pow 2 * &H / &Q` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    TRANS_TAC REAL_LE_TRANS `&H` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * &d pow 2 * &H / &Q) * &r =
                  &H * ((&2 * &d pow 2 * &r) / &Q)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    UNDISCH_TAC `Q < 2 * d EXP 2 * r` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_MUL;
                GSYM REAL_OF_NUM_POW] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&r) /\ log(&r) <= log(&R)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&H' / &r + &1) * (&7 * &H + &4 * &r * (&1 + log(&r))) <=
    &14 * &d pow 2 * &H pow 2 / &Q + &4 * &H * (&1 + log(&R)) + &7 * &H +
    &4 * &R * (&1 + log(&R))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(&H' / &r + &1) * (&7 * &H + &4 * &r * (&1 + log(&r))) =
      &7 * &H * (&H' / &r) + &4 * &H' * (&1 + log(&r)) + &7 * &H +
      &4 * &r * (&1 + log(&r))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&7 * &H * (&H' / &r) <= &14 * &d pow 2 * &H pow 2 / &Q`
    MP_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&7 * &H * (&2 * &d pow 2 * &H / &Q)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
        REWRITE_TAC[real_div; REAL_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * &H' * (&1 + log(&r)) <= &4 * &H * (&1 + log(&R)) /\
                  &4 * &r * (&1 + log(&r)) <= &4 * &R * (&1 + log(&R))`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&H' <= &H` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ABBREV_TAC `s1 = sum(1..H') (\e. emin (&H') (&e * &2 * y))` THEN
  ABBREV_TAC `s2 = sum(1..H') (\k. emin (&H) (&k * &2 * y))` THEN
  ASM_REAL_ARITH_TAC);;

let TYPEI_INNER = prove
 (`!M Kw Q j P D d H'.
     j < M /\ ~(j IN circ_major M Kw Q) /\ 1 <= Q /\ 1 <= Kw /\
     1 <= d /\ d <= D /\ 1 <= P /\ H' <= P DIV d
     ==> norm(vsum(1..H')
                (\h. expi(&(h EXP 2) * (&d pow 2 * &j / &M)))) pow 2
         <= (&P / &d) pow 2 *
            (&48 * (&1 + log(&Kw)) * &D / &P + &56 * &D pow 2 / &Q +
             &16 * (&1 + log(&Kw)) * &Kw * &D pow 2 / &P pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`; `j:num`; `d:num`; `Kw:num`]
    TYPEI_SINGLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&2 * &1 pow 2 * &Kw` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`P DIV d`; `H':num`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!b c. b <= c ==> a <= b ==> a <= c`) THEN
  ABBREV_TAC `l = &1 + log(&Kw)` THEN
  ABBREV_TAC `H = &(P DIV d)` THEN ABBREV_TAC `X = &P / &d` THEN
  SUBGOAL_THEN `&1 <= l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`)
     THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &d /\ &0 < &P /\ &d <= &D /\ &0 < &Q`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= H /\ H <= X` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN EXPAND_TAC "X" THEN
    ASM_SIMP_TAC[REAL_POS; NUM_DIV_LE_REAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &D / &d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `&45 * l * H <= &48 * l * (X pow 2 * &D / &P)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `X pow 2 * &D / &P = X * (&D / &d)` SUBST1_TAC THENL
     [EXPAND_TAC "X" THEN
      SUBGOAL_THEN `~(&P = &0) /\ ~(&d = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `H <= X * (&D / &d)` MP_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `X:real` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ
      (ASSUME `&0 <= l`)) THEN
    SUBGOAL_THEN `&0 <= l * H` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&56 * &d pow 2 * H pow 2 / &Q <= &56 * X pow 2 * &D pow 2 / &Q`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&d * H <= X * &D` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `2` o MATCH_MP REAL_POW_LE2 o CONJ
      (MATCH_MP REAL_LE_MUL (CONJ (MATCH_MP REAL_LT_IMP_LE
        (ASSUME `&0 < &d`)) (ASSUME `&0 <= H`)))) THEN
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 * &Kw * l <= &16 * l * &Kw * X pow 2 * &D pow 2 / &P pow 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `X pow 2 * &D pow 2 / &P pow 2 = (&D / &d) pow 2`
    SUBST1_TAC THENL
     [EXPAND_TAC "X" THEN
      SUBGOAL_THEN `~(&P = &0) /\ ~(&d = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= (&D / &d) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &16 * l * &Kw` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `t = (&D / &d) pow 2` THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&16 * &Kw * l = (&16 * l * &Kw) * &1 /\
                  &16 * l * &Kw * t = (&16 * l * &Kw) * t`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= H * l` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `H <= H * (l:real)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `&45 * l * H <= &48 * l * X pow 2 * &D / &P` THEN
  UNDISCH_TAC `&56 * &d pow 2 * H pow 2 / &Q <= &56 * X pow 2 * &D pow 2 / &Q`
    THEN
  UNDISCH_TAC `&16 * &Kw * l <= &16 * l * &Kw * X pow 2 * &D pow 2 / &P pow 2`
    THEN
  UNDISCH_TAC `H <= H * (l:real)` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let LOG_WEIGHT_BOUND = prove
 (`!(x:num->complex) H B.
     1 <= H /\ &0 <= B /\
     (!h. 1 <= h /\ h <= H ==> norm(vsum(1..h) x) <= B)
     ==> norm(vsum(1..H) (\h. Cx(log(&h)) * x h)) <= &2 * B * log(&H)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(H = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MP_TAC(ISPECL [`x:num->complex`; `\h. Cx(log(&h))`; `H:num`; `B:real`]
    ABEL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&0 <= log(&H)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..H-1) (\h. norm(Cx(log(&(h + 1))) - Cx(log(&h)))) =
                log(&H)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..H-1) (\h. log(&(h + 1)) - log(&h))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> abs(b - a) = b - a`) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUM_DIFFS_ALT] THEN COND_CASES_TAC THENL
       [SUBGOAL_THEN `H - 1 + 1 = H` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REWRITE_TAC[LOG_1; REAL_SUB_RZERO]];
        SUBGOAL_THEN `H = 1` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REWRITE_TAC[LOG_1]]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

let TYPEI_GEN = prove
 (`!P D W (w:num->real) (z:num->complex) e.
     1 <= D /\ &0 <= W /\ &0 <= e /\
     (!d. 1 <= d /\ d <= P ==> abs(w d) <= W) /\
     (!d. 1 <= d /\ d <= P /\ D < d ==> w d = &0) /\
     (!d. 1 <= d /\ d <= P /\ d <= D ==> norm(z d) <= &P / &d * e)
     ==> norm(vsum(1..P) (\d. Cx(w d) * z d))
         <= W * &P * (&1 + log(&D)) * e`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..P) (\d. if d <= D then W * (&P / &d * e) else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    COND_CASES_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE];
      SUBGOAL_THEN `(w:num->real) d = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[REAL_ABS_0; REAL_MUL_LZERO; REAL_LE_REFL]]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `sum(1..D) (\d. W * (&P / &d * e))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; IN_DIFF] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_ARITH `w * (p * i) * e = (w * p * e) * i:real`]
    THEN
  REWRITE_TAC[SUM_LMUL] THEN
  REWRITE_TAC[REAL_ARITH `(w * p * e) * x = w * p * x * e:real`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[HARMONIC_LE_LOG]);;

let hua_e1 = new_definition
 `hua_e1 P D Q Kw =
    &48 * (&1 + log(&Kw)) * &D / &P + &56 * &D pow 2 / &Q +
    &16 * (&1 + log(&Kw)) * &Kw * &D pow 2 / &P pow 2`;;

let HUA_E1_POS = prove
 (`!P D Q Kw. 1 <= Kw ==> &0 <= hua_e1 P D Q Kw`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hua_e1] THEN
  SUBGOAL_THEN `&0 <= &1 + log(&Kw)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POS; REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_POW_LE]);;

let TYPEI_INNER_SQRT = prove
 (`!M Kw Q j P D d H'.
     j < M /\ ~(j IN circ_major M Kw Q) /\ 1 <= Q /\ 1 <= Kw /\
     1 <= d /\ d <= D /\ 1 <= P /\ H' <= P DIV d
     ==> norm(vsum(1..H')
                (\h. expi(&(h EXP 2) * (&d pow 2 * &j / &M))))
         <= &P / &d * sqrt(hua_e1 P D Q Kw)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`; `j:num`; `P:num`; `D:num`;
                `d:num`; `H':num`] TYPEI_INNER) THEN
  ASM_REWRITE_TAC[GSYM hua_e1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_RSQRT) THEN
  REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `sqrt((&P / &d) pow 2) = &P / &d` SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS];
    REWRITE_TAC[]]);;

let QPHASE_MUL = prove
 (`!d h x. expi(&((d * h) EXP 2) * x) = expi(&(h EXP 2) * (&d pow 2 * x))`,
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MULT_EXP; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  REAL_ARITH_TAC);;

let TYPEI_S1 = prove
 (`!M Kw Q j P V D.
     j < M /\ ~(j IN circ_major M Kw Q) /\ 1 <= Q /\ 1 <= Kw /\ 1 <= P /\
     1 <= D /\ V <= &D
     ==> norm(vsum(1..P) (\d. Cx(vaughan_G V d) *
                vsum(1..P DIV d) (\h. Cx(log(&h)) *
                                      expi(&((d * h) EXP 2) * (&j / &M)))))
         <= &1 * &P * (&1 + log(&D)) * (&2 * sqrt(hua_e1 P D Q Kw) * log(&P))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TYPEI_GEN THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  SUBGOAL_THEN `&0 <= sqrt(hua_e1 P D Q Kw) /\ &0 <= log(&P)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; HUA_E1_POS] THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[vaughan_G] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_MOBIUS; REAL_ABS_0; REAL_POS];
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[vaughan_G] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `D < d:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[QPHASE_MUL] THEN
    SUBGOAL_THEN `1 <= P DIV d` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\h. expi(&(h EXP 2) * (&d pow 2 * &j / &M))`;
                   `P DIV d`; `&P / &d * sqrt(hua_e1 P D Q Kw)`]
      LOG_WEIGHT_BOUND) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; SQRT_POS_LE; HUA_E1_POS];
        X_GEN_TAC `h:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC TYPEI_INNER_SQRT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!b c. b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[REAL_ARITH `&2 * (x * y) * l = x * (&2 * y * l):real`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; DIV_LE] THEN
    ASM_ARITH_TAC]);;

let TYPEI_S2 = prove
 (`!M Kw Q j P U V D.
     j < M /\ ~(j IN circ_major M Kw Q) /\ 1 <= Q /\ 1 <= Kw /\ 1 <= P /\
     1 <= D /\ U * V <= &D
     ==> norm(vsum(1..P)
                (\s. Cx(dirichlet_conv (vaughan_G V) (vaughan_F U) s) *
                vsum(1..P DIV s) (\t. expi(&((s * t) EXP 2) * (&j / &M)))))
         <= log(&P) * &P * (&1 + log(&D)) * sqrt(hua_e1 P D Q Kw)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TYPEI_GEN THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sqrt(hua_e1 P D Q Kw) /\ &0 <= log(&P)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; HUA_E1_POS] THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN STRIP_TAC THEN
    TRANS_TAC REAL_LE_TRANS `log(&s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VAUGHAN_C_BOUND THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN MATCH_MP_TAC VAUGHAN_C_ZERO THEN
    UNDISCH_TAC `D < s:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN REWRITE_TAC[QPHASE_MUL] THEN
    MATCH_MP_TAC TYPEI_INNER_SQRT THEN ASM_REWRITE_TAC[LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Divisor fibres.                                                           *)
(* ------------------------------------------------------------------------- *)

let FIBRE_TAU = prove
 (`!c A B (f:num->real).
     1 <= c /\ (!n. &0 <= f n)
     ==> sum(1..A) (\a. sum(1..B) (\b. f(c * a * b))) <=
         sum(1..c * A * B) (\n. &(CARD {d | d divides n}) * f n)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  ABBREV_TAC `s = {a,b | a IN 1..A /\ b IN 1..B}` THEN
  SUBGOAL_THEN `FINITE(s:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(a:num,b:num). c * a * b`;
   `\(a:num,b:num). f(c * a * b):real`;
                 `s:num#num->bool`; `1..c * A * B`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
      ASM_ARITH_TAC;
      REPEAT(MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL])];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `t = {x | x IN s /\ (\(a,b). c * a * b:num) x = n}` THEN
  SUBGOAL_THEN `FINITE(t:num#num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:num#num->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum t (\(a,b). f(c * a * b)) = sum t (\x:num#num. f(n:num))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `CARD(t:num#num->bool) = CARD(IMAGE FST t)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a1:num`; `b1:num`; `a2:num`; `b2:num`] THEN
    EXPAND_TAC "t" THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_ELIM_PAIR_THM; PAIR_EQ; IN_NUMSEG] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c * a2 * b2 = n:num` THEN
    UNDISCH_TAC `c * a1 * b1 = n:num` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM;
      IN_ELIM_THM] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[] THEN NUMBER_TAC;
    MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC]);;

let TAU_SQUARE_SUM = prove
 (`!X. 1 <= X
       ==> sum(1..X) (\n. &(CARD {d | d divides n}) pow 2)
           <= &X * (&1 + log(&X)) pow 3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&X`; `X:num`] SUM_TAU_LE_SQUARE_NUMSEG) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[tau_le] THEN
  SUBGOAL_THEN `{d | d divides n /\ &d <= &X} = {d | d divides n}`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; REAL_OF_NUM_LE] THEN
  X_GEN_TAC `d:num` THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let TAU_CS = prove
 (`!X V (G:num->real).
     1 <= X /\ (!n. &0 <= G n /\ G n <= V)
     ==> sum(1..X) (\n. &(CARD {d | d divides n}) * G n) pow 2
         <= V * &X * (&1 + log(&X)) pow 3 * sum(1..X) G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum(1..X) (\n. &(CARD {d | d divides n}) * G n) =
                sum(1..X) (\n. G n * &(CARD {d | d divides n}))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC[REAL_MUL_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:num->real`; `\n. &(CARD {d | d divides n})`; `1..X`]
    SUM_WEIGHTED_CS) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c:real`) THEN
  SUBGOAL_THEN `&0 <= sum(1..X) G` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..X) (\x. G x * &(CARD {d | d divides x}) pow 2) <=
    V * &X * (&1 + log(&X)) pow 3`
  MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sum(1..X) (\n. V * &(CARD {d | d divides n}) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[TAU_SQUARE_SUM]];
    ALL_TAC] THEN
  ABBREV_TAC `t = sum(1..X) (\x. G x * &(CARD {d | d divides x}) pow 2)` THEN
  ABBREV_TAC `g = sum(1..X) G` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `g * t <= g * (V * &X * (&1 + log(&X)) pow 3)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Type II sums.                                                             *)
(* ------------------------------------------------------------------------- *)

let TYPE2_STEP_B = prove
 (`!x a q M0 A B X.
     1 <= q /\ coprime(a,q) /\ abs(x - &a / &q) <= inv(&q pow 2) /\
     1 <= A /\ 1 <= B /\ X = 2 * A * B
     ==> sum(1..A) (\w. sum(1..B)
           (\v. emin (&M0) (&(2 * w * v) * x))) pow 2
         <= &M0 * &X * (&1 + log(&X)) pow 3 *
            ((&X / &q + &1) * (&7 * &M0 + &4 * &q * (&1 + log(&q))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= X` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `X = 2 * A * B` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`2`; `A:num`; `B:num`; `\n. emin (&M0) (&n * x)`]
    FIBRE_TAU) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 2`] THEN
  ANTS_TAC THENL [GEN_TAC THEN MATCH_MP_TAC EMIN_POS THEN
                  REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Ts = sum(1..A) (\w. sum(1..B)
                    (\v. emin (&M0) (&(2 * w * v) * x)))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`X:num`; `&M0:real`; `\n. emin (&M0) (&n * x)`] TAU_CS) THEN
  ASM_REWRITE_TAC[EMIN_LE] THEN
  ANTS_TAC THENL [GEN_TAC THEN MATCH_MP_TAC EMIN_POS THEN
                  REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `a:num`; `q:num`; `&M0:real`; `X:num`; `&0:real`]
    EMIN_SUM_CONST) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_ADD_LID] THEN
  ABBREV_TAC `S = sum(1..X) (\n. &(CARD {d | d divides n}) *
                                 emin (&M0) (&n * x))` THEN
  ABBREV_TAC `E = sum(1..X) (\k. emin (&M0) (&k * x))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(S:real) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&M0 * &X * (&1 + log(&X)) pow 3 * E` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
  MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let SQ_DIFF_FACTOR = prove
 (`!i j. j <= i ==> i EXP 2 - j EXP 2 = (i - j) * (i + j)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2; EXP_2] THEN ARITH_TAC);;

let SQDIFF_FIBRE = prove
 (`!Kq (f:num->real).
     (!n. &0 <= f n)
     ==> sum(1..Kq) (\i. sum(1..Kq) (\j. if j < i then f(i EXP 2 - j EXP 2)
                                       else &0)) <=
         sum(1..Kq EXP 2) (\r. &(CARD {d | d divides r}) * f r)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  ABBREV_TAC `s = {i,j | i IN 1..Kq /\ j IN 1..Kq}` THEN
  SUBGOAL_THEN `FINITE(s:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum s (\(i,j). if j < i then f(i EXP 2 - j EXP 2) else &0) =
    sum {p | p IN s /\ SND p < FST p} (\(i,j). f(i EXP 2 - j EXP 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s' = {p | p IN s /\ SND p < FST (p:num#num)}` THEN
  SUBGOAL_THEN `FINITE(s':num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(i:num,j:num). i EXP 2 - j EXP 2`;
                 `\(i:num,j:num). f(i EXP 2 - j EXP 2):real`;
                 `s':num#num->bool`; `1..Kq EXP 2`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "s'" THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `b < a ==> 1 <= a - b`) THEN
      REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ARITH_RULE `a <= c:num ==> a - b <= c`) THEN
      REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `t = {x | x IN s' /\ (\(i,j). i EXP 2 - j EXP 2:num) x = n}` THEN
  SUBGOAL_THEN `FINITE(t:num#num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s':num#num->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum t (\(i,j). f(i EXP 2 - j EXP 2)) =
                sum t (\x:num#num. f(n:num))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `CARD(t:num#num->bool) =
                CARD(IMAGE (\(i:num,j:num). i - j) t)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`i1:num`; `j1:num`; `i2:num`; `j2:num`] THEN
    EXPAND_TAC "t" THEN EXPAND_TAC "s'" THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(i1 - j1) * (i1 + j1) = (i2 - j2) * (i2 + j2):num` MP_TAC
      THENL
     [ASM_SIMP_TAC[GSYM SQ_DIFF_FACTOR; LT_IMP_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[EQ_MULT_LCANCEL] THEN
    SUBGOAL_THEN `~(i2 - j2 = 0:num)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `i1 - j1 = i2 - j2:num` THEN
    UNDISCH_TAC `j1 < i1:num` THEN UNDISCH_TAC `j2 < i2:num` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [EXPAND_TAC "t" THEN EXPAND_TAC "s'" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_THM] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SQ_DIFF_FACTOR; LT_IMP_LE] THEN NUMBER_TAC;
    MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC]);;

let TYPE2_TQ = prove
 (`!x a q M0 K0 X.
     1 <= q /\ coprime(a,q) /\ abs(x - &a / &q) <= inv(&q pow 2) /\
     1 <= M0 /\ 1 <= K0 /\ X = 2 * M0 * K0 EXP 2
     ==> sum(1..M0) (\e. sum(1..K0) (\i. sum(1..K0) (\j.
           if j < i then emin (&M0) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
           else &0))) pow 4
         <= &M0 pow 4 * &K0 pow 4 * (&1 + log(&X)) pow 6 *
            (&M0 * &X * (&1 + log(&X)) pow 3 *
             ((&X / &q + &1) * (&7 * &M0 + &4 * &q * (&1 + log(&q)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `a:num`; `q:num`; `M0:num`; `M0:num`;
                `K0 EXP 2`; `X:num`] TYPE2_STEP_B) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `F0 = \r. sum(1..M0) (\e. emin (&M0) (&(2 * e * r) * x))` THEN
  SUBGOAL_THEN `!r. &0 <= (F0:num->real) r /\ F0 r <= &M0 * &M0`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "F0" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS];
      TRANS_TAC REAL_LE_TRANS `sum(1..M0) (\v. &M0)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN REWRITE_TAC[EMIN_LE];
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..M0) (\e. sum(1..K0) (\i. sum(1..K0) (\j.
      if j < i then emin (&M0) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
      else &0))) <=
    sum(1..K0 EXP 2) (\r. &(CARD {d | d divides r}) * F0 r)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sum(1..M0) (\e. sum(1..K0 EXP 2) (\r. &(CARD {d | d divides r}) *
                        emin (&M0) (&(2 * e * r) * x)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`K0:num`; `\r. emin (&M0) (&(2 * e * r) * x)`]
        SQDIFF_FIBRE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
      MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS];
      EXPAND_TAC "F0" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
      GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..M0) (\w. sum(1..K0 EXP 2) (\v. emin (&M0) (&(2 * w * v) * x))) =
    sum(1..K0 EXP 2) F0`
  SUBST1_TAC THENL
   [EXPAND_TAC "F0" THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0 EXP 2`; `&M0 * &M0:real`; `F0:num->real`] TAU_CS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `TQ = sum(1..M0) (\e. sum(1..K0) (\i. sum(1..K0) (\j.
           if j < i then emin (&M0) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
           else &0)))` THEN
  ABBREV_TAC `S1 = sum(1..K0 EXP 2) (\r. &(CARD {d | d divides r}) *
                                         (F0:num->real) r)` THEN
  ABBREV_TAC `G1 = sum(1..K0 EXP 2) (F0:num->real)` THEN
  ABBREV_TAC `Bb = &M0 * &(2 * M0 * K0 EXP 2) *
                   (&1 + log (&(2 * M0 * K0 EXP 2))) pow 3 *
                   (&(2 * M0 * K0 EXP 2) / &q + &1) *
                   (&7 * &M0 + &4 * &q * (&1 + log (&q)))` THEN
  ABBREV_TAC `lx = &1 + log (&(2 * M0 * K0 EXP 2))` THEN
  ABBREV_TAC `l1 = &1 + log(&(K0 EXP 2))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= TQ` ASSUME_TAC THENL
   [EXPAND_TAC "TQ" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC EMIN_POS THEN
    REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= l1 /\ l1 <= lx` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l1" THEN EXPAND_TAC "lx" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; EXP_EQ_0] THEN
        ASM_ARITH_TAC;
        TRANS_TAC LE_TRANS `1 * 1 * K0 EXP 2` THEN CONJ_TAC THENL
         [ARITH_TAC;
          MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `TQ pow 2 <= ((&M0 * &M0) * &(K0 EXP 2) * l1 pow 3) * G1`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(S1:real) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `S1 pow 2 <= (&M0 * &M0) * &(K0 EXP 2) * l1 pow 3 * G1` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `c = (&M0 * &M0) * &(K0 EXP 2) * l1 pow 3` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(TQ:real) pow 4 <= c pow 2 * Bb` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(c * G1:real) pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Bb` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(G1:real) pow 2` THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(c:real) pow 2 * Bb` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
  SUBGOAL_THEN `(l1:real) pow 6 <= lx pow 6` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &M0 pow 4 * &K0 pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&M0 pow 4 * &K0 pow 4) * l1 pow 6 <=
                (&M0 pow 4 * &K0 pow 4) * lx pow 6` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let TYPE2Q_PAIR = prove
 (`!(b:num->real) P M0 i j x.
     1 <= i /\ 1 <= j
     ==> abs(sum(M0+1..2*M0)
               (\m. (if i <= P DIV m then b i else &0) *
                    (if j <= P DIV m then b j else &0) *
                    Re(expi(&((m * i) EXP 2) * x - &((m * j) EXP 2) * x))))
         <= abs(b i) * abs(b j) *
            sqrt(&M0 + &4 * sum(1..M0)
                   (\e. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP
                     2))))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y = x * (&(i EXP 2) - &(j EXP 2))` THEN
  ABBREV_TAC `L = MIN (2 * M0) (MIN (P DIV i) (P DIV j)) - M0` THEN
  SUBGOAL_THEN
   `sum(M0+1..2*M0)
      (\m. (if i <= P DIV m then b i else &0) *
           (if j <= P DIV m then b j else &0) *
           Re(expi(&((m * i) EXP 2) * x - &((m * j) EXP 2) * x))) =
    b i * b j * Re(vsum(M0+1..M0+L) (\m. expi(&(m EXP 2) * y)))`
  SUBST1_TAC THENL
   [SIMP_TAC[RE_VSUM; FINITE_NUMSEG; GSYM SUM_LMUL] THEN
    SUBGOAL_THEN `M0+1..M0+L = {m | m IN M0+1..2*M0 /\
                                    i <= P DIV m /\ j <= P DIV m}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN
       X_GEN_TAC `m:num` THEN
      ASM_CASES_TAC `m = 0` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
      EXPAND_TAC "L" THEN
      REWRITE_TAC[GSYM LE_RDIV_EQ] THEN
      ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
      SUBGOAL_THEN `(m * i <= P <=> m <= P DIV i) /\ (m * j <= P <=> m <= P
          DIV j)`
        (fun th -> REWRITE_TAC[th]) THENL
         [ONCE_REWRITE_TAC[MULT_SYM] THEN CONJ_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC LE_RDIV_EQ THEN ASM_ARITH_TAC;
          ALL_TAC] THEN
        EXPAND_TAC "L" THEN REWRITE_TAC[MIN] THEN ARITH_TAC;
      REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `&((m * i) EXP 2) * x - &((m * j) EXP 2) * x = &(m EXP 2)
            * y`
        SUBST1_TAC THENL
         [EXPAND_TAC "y" THEN
          REWRITE_TAC[MULT_EXP; GSYM REAL_OF_NUM_MUL;
           GSYM REAL_OF_NUM_POW] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_CASES_TAC `i <= P DIV m` THEN ASM_CASES_TAC `j <= P DIV m` THEN
        ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ABBREV_TAC `W = vsum(M0 + 1..M0 + L) (\m. expi(&(m EXP 2) * y))` THEN
  TRANS_TAC REAL_LE_TRANS `norm(W:complex)` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  MP_TAC(SPECL [`y:real`; `M0:num`; `L:num`] QWEYL_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!b c:real. b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `L <= M0:num` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[MIN] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c d:real. a <= b /\ c <= d ==>
                             a + &4 * c <= b + &4 * d`) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `sum(1..L) (\e. emin (&M0) (&e * &2 * y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EMIN_MONO THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS]]);;

let DOUBLE_SUM_CS = prove
 (`!(f:num->real) (g:num->num->real) Kq.
     (!i j. &0 <= g i j)
     ==> sum(1..Kq) (\i. sum(1..Kq) (\j. abs(f i) * abs(f j) * sqrt(g i j)))
         <= sum(1..Kq) (\k. f k pow 2) *
            sqrt(sum(1..Kq) (\i. sum(1..Kq) (\j. g i j)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {i,j | i IN 1..Kq /\ j IN 1..Kq}` THEN
  SUBGOAL_THEN `FINITE(s:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:num->num->real. sum(1..Kq) (\i. sum(1..Kq) (\j. h i j)) =
                       sum s (\p. h (FST p) (SND p))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "s" THEN
    SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\p:num#num. abs(f(FST p)) * abs(f(SND p))`;
                 `\p:num#num. sqrt(g (FST p) (SND p))`; `s:num#num->bool`]
    SIEVE_SUM_CAUCHY_SCHWARZ) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!p:num#num. sqrt(g (FST p) (SND p)) pow 2 = g (FST p) (SND p)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum s (\x:num#num. (abs(f(FST x)) * abs(f(SND x))) pow 2) =
    sum(1..Kq) (\k. f k pow 2) pow 2`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `\i j. (abs((f:num->real) i) * abs(f j)) pow 2`)
     THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS; SUM_LMUL] THEN
    REWRITE_TAC[SUM_RMUL; REAL_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_RSQRT) THEN
  REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `sqrt(sum(1..Kq) (\k. f k pow 2) pow 2) =
                sum(1..Kq) (\k. f k pow 2)` SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[REAL_LE_POW_2];
    REWRITE_TAC[]]);;

let TYPE2Q_SQUARE = prove
 (`!(b:num->real) P M0 K0 x.
     1 <= M0 /\ P DIV (M0 + 1) <= K0
     ==> sum(M0+1..2*M0)
           (\m. norm(vsum(1..P DIV m)
                       (\k. Cx(b k) * expi(&((m * k) EXP 2) * x))) pow 2)
         <= sum(1..K0) (\i. sum(1..K0) (\j. abs(b i) * abs(b j) *
              sqrt(&M0 + &4 * sum(1..M0)
                (\e. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP
                  2))))))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(M0+1..2*M0) (\m. sum(1..K0) (\i. sum(1..K0) (\j.
                 (if i <= P DIV m then b i else &0) *
                 (if j <= P DIV m then b j else &0) *
                 Re(expi(&((m * i) EXP 2) * x - &((m * j) EXP 2) * x)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `P DIV m <= K0` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `P DIV (M0 + 1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIV_MONO2 THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`b:num->real`; `\k. expi(&((m * k) EXP 2) * x)`;
                   `P DIV m`; `K0:num`] VSUM_NUMSEG_INDICATOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_VSUM_EXPI_POW2];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y:real`) THEN
  MATCH_MP_TAC TYPE2Q_PAIR THEN ASM_REWRITE_TAC[]);;

let TYPE2Q_BLOCK = prove
 (`!(a:num->real) (b:num->real) P M0 K0 x.
     1 <= M0 /\ P DIV (M0 + 1) <= K0
     ==> norm(vsum(M0+1..2*M0) (\m. Cx(a m) *
                vsum(1..P DIV m) (\k. Cx(b k) * expi(&((m * k) EXP 2) * x))))
         pow 2
         <= sum(M0+1..2*M0) (\m. a m pow 2) *
            sum(1..K0) (\k. b k pow 2) *
            sqrt(sum(1..K0) (\i. sum(1..K0) (\j. &M0 + &4 * sum(1..M0)
              (\e. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP 2))))))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(M0+1..2*M0) (\m. (a:num->real) m pow 2) *
    sum(M0+1..2*M0) (\m. norm(vsum(1..P DIV m)
                     (\k. Cx(b k) * expi(&((m * k) EXP 2) * x))) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NORM_VSUM_CAUCHY_SCHWARZ THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..K0) (\i. sum(1..K0) (\j. abs(b i) * abs(b j) *
              sqrt(&M0 + &4 * sum(1..M0)
                (\e. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP
                  2))))))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TYPE2Q_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`b:num->real`;
    `\i j. &M0 + &4 * sum(1..M0)
       (\e. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP 2)))))`;
    `K0:num`] DOUBLE_SUM_CS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN
     REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN
    MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS];
    REWRITE_TAC[]]);;

let QSUM_SPLIT = prove
 (`!x M0 K0 e.
     sum(1..K0) (\i. sum(1..K0) (\j.
       emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP 2))))))
     = &K0 * &M0 +
       &2 * sum(1..K0) (\i. sum(1..K0) (\j.
              if j < i then emin (&M0) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
              else &0))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!i j. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP 2)))) =
            (if i = j then &M0 else &0) +
            (if j < i then emin (&M0) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
             else &0) +
            (if i < j then emin (&M0) (&(2 * e * (j EXP 2 - i EXP 2)) * x)
             else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    ASM_CASES_TAC `i:num = j` THENL
     [ASM_REWRITE_TAC[LT_REFL; REAL_SUB_REFL; REAL_MUL_RZERO] THEN
      REWRITE_TAC[emin; INTEGER_CLOSED] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `j < i \/ i < j:num` DISJ_CASES_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THENL
     [ASM_SIMP_TAC[ARITH_RULE `j < i ==> ~(i < j:num)`] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `j EXP 2 <= i EXP 2` ASSUME_TAC THENL
       [REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_MUL] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `i < j ==> ~(j < i:num)`] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM EMIN_NEG] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `i EXP 2 <= j EXP 2` ASSUME_TAC THENL
       [REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_MUL] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN `sum(1..K0) (\i. sum(1..K0) (\j. if i = j then &M0 else &0)) =
                &K0 * &M0` SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `sum(1..K0) (\i. &M0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      TRANS_TAC EQ_TRANS `sum(1..K0) (\j. if j = i then &M0 else &0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ_NUMSEG THEN MESON_TAC[];
        REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. b = c ==> a + c + b = a + &2 * c`) THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let TYPE2Q_GSUM = prove
 (`!x M0 K0.
     sum(1..K0) (\i. sum(1..K0) (\j. &M0 + &4 * sum(1..M0)
       (\e. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP 2)))))))
     = &K0 pow 2 * &M0 + &4 * &M0 pow 2 * &K0 +
       &8 * sum(1..M0) (\e. sum(1..K0) (\i. sum(1..K0) (\j.
              if j < i then emin (&M0) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
              else &0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
  SUBGOAL_THEN
   `sum(1..K0) (\i. sum(1..K0) (\j. sum(1..M0)
      (\e. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP 2))))))) =
    sum(1..M0) (\e. sum(1..K0) (\i. sum(1..K0)
      (\j. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP 2)))))))`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `sum(1..K0) (\i. sum(1..M0) (\e. sum(1..K0)
        (\j. emin (&M0) (&e * &2 * (x * (&(i EXP 2) - &(j EXP 2)))))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[QSUM_SPLIT; SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG;
              ADD_SUB] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let TYPE2Q_BLOCK4 = prove
 (`!U V P M0 K0 x.
     &1 <= V /\ 1 <= M0 /\ P DIV (M0 + 1) = K0
     ==> norm(vsum(M0+1..2*M0) (\m. Cx(mangoldt m - vaughan_F U m) *
                vsum(1..P DIV m)
                  (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x))))
         pow 4
         <= (&36 * &M0 * log(&2 * &M0)) pow 2 *
            (&K0 * (&1 + log V) pow 3) pow 2 *
            (&K0 pow 2 * &M0 + &4 * &M0 pow 2 * &K0 +
             &8 * sum(1..M0) (\e. sum(1..K0) (\i. sum(1..K0) (\j.
              if j < i then emin (&M0) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
              else &0))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. mangoldt m - vaughan_F U m`; `vaughan_e V`;
                 `P:num`; `M0:num`; `K0:num`; `x:real`] TYPE2Q_BLOCK) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN REWRITE_TAC[TYPE2Q_GSUM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `Gs = &K0 pow 2 * &M0 + &4 * &M0 pow 2 * &K0 +
             &8 * sum(1..M0) (\e. sum(1..K0) (\i. sum(1..K0) (\j.
              if j < i then emin (&M0) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
              else &0)))` THEN
  ABBREV_TAC `Ss = norm(vsum(M0+1..2*M0) (\m. Cx(mangoldt m - vaughan_F U m) *
                vsum(1..P DIV m)
                  (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x))))` THEN
  MP_TAC(SPECL [`U:real`; `M0:num`] SUM_A_SQUARE) THEN
  MP_TAC(SPECL [`V:real`; `K0:num`] SUM_B_SQUARE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = sum(M0+1..2*M0) (\m. (mangoldt m - vaughan_F U m) pow 2)`
    THEN
  ABBREV_TAC `Bk = sum(1..K0) (\k. vaughan_e V k pow 2)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= A /\ &0 <= Bk /\ &0 <= Gs /\ &0 <= Ss`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN EXPAND_TAC "Bk" THEN EXPAND_TAC "Ss" THEN
    REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
      EXPAND_TAC "Gs" THEN
      REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      REPEAT(MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
             REWRITE_TAC[]) THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ss:real) pow 4 <= (A * Bk) pow 2 * Gs` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
    TRANS_TAC REAL_LE_TRANS `(A * Bk * sqrt Gs) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
      REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `A pow 2 * Bk pow 2 <=
    (&36 * &M0 * log(&2 * &M0)) pow 2 * (&K0 * (&1 + log V) pow 3) pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(A pow 2 * Bk pow 2) * Gs:real` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `Ss pow 4 <= (A * Bk) pow 2 * Gs:real` THEN
    REWRITE_TAC[REAL_POW_MUL];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]]);;

let TYPE2Q_BLOCK_NORM = prove
 (`!U V P M1 K1 x a q s.
     1 <= q /\ coprime(a,q) /\ abs(x - &a / &q) <= inv(&q pow 2) /\
     &1 <= V /\ 1 <= M1 /\ 1 <= K1 /\ P DIV (M1 + 1) = K1 /\ 3 <= P /\
     inv(&M1) <= s /\ inv(&K1) <= s /\ inv(&q) <= s /\
     (&1 + log(&q)) / &M1 <= s /\ inv(&P) <= s /\
     &q * (&1 + log(&q)) / &P pow 2 <= s /\ s <= &1
     ==> norm(vsum(M1+1..2*M1) (\m. Cx(mangoldt m - vaughan_F U m) *
                vsum(1..P DIV m)
                  (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x))))
         pow 4
         <= &10642752 * log(&P) pow 5 * (&1 + log V) pow 6 * &P pow 4 *
            sqrt(sqrt s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `M1 * K1 <= P /\ P < 4 * M1 * K1 /\ M1 <= P` STRIP_ASSUME_TAC
    THENL
   [MP_TAC(SPECL [`P:num`; `M1 + 1`] DIVISION) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `K1 <= K1 * M1 /\ M1 <= K1 * M1 /\ 1 <= K1 * M1`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k = k * 1`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k = 1 * k`] THEN
        REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
        ASM_ARITH_TAC];
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&P)` ASSUME_TAC THENL
   [MP_TAC LOG_3_LOWER THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> &5493 / &5000 <= b ==> &1 <= c`) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = log(&P)` THEN
  SUBGOAL_THEN `log(&2 * &M1) <= &2 * L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    SUBGOAL_THEN `&2 * log(&P) = log(&P pow 2)` SUBST1_TAC THENL
     [MATCH_MP_TAC(GSYM LOG_POW) THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_LT;
                REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_2] THEN TRANS_TAC LE_TRANS `2 * P` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`U:real`; `V:real`; `P:num`; `M1:num`; `K1:num`; `x:real`]
    TYPE2Q_BLOCK4) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`x:real`; `a:num`; `q:num`; `M1:num`; `K1:num`;
                `2 * M1 * K1 EXP 2`] TYPE2_TQ) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `TQ = sum(1..M1) (\e. sum(1..K1) (\i. sum(1..K1) (\j.
              if j < i then emin (&M1) (&(2 * e * (i EXP 2 - j EXP 2)) * x)
              else &0)))` THEN
  ABBREV_TAC `Ss = norm(vsum(M1+1..2*M1) (\m. Cx(mangoldt m - vaughan_F U m) *
                vsum(1..P DIV m)
                  (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x))))` THEN
  ABBREV_TAC `X1 = 2 * M1 * K1 EXP 2` THEN
  ABBREV_TAC `lx = &1 + log(&X1)` THEN
  ABBREV_TAC `lq = &1 + log(&q)` THEN
  ABBREV_TAC `lV = &1 + log V` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= lx /\ lx <= &4 * L` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lx" THEN EXPAND_TAC "L" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN EXPAND_TAC "X1" THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                  MULT_EQ_0; EXP_EQ_0] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= l /\ x <= &3 * l ==> &1 + x <= &4 * l`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
    SUBGOAL_THEN `&3 * log(&P) = log(&P pow 3)` SUBST1_TAC THENL
     [MATCH_MP_TAC(GSYM LOG_POW) THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN EXPAND_TAC "X1" THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `K1 <= P:num` ASSUME_TAC THENL
     [TRANS_TAC LE_TRANS `M1 * K1:num` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k = 1 * k`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `2 * M1 * K1 EXP 2 = (M1 * K1) * (2 * K1) /\
                  P EXP 3 = P * (P * P)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXP_2; ARITH_RULE `P EXP 3 = P * P * P`] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&M1 * &X1 * (&X1 / &q + &1) * (&7 * &M1 + &4 * &q * lq) <=
    &228 * (&M1 * &K1) pow 4 * s`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &M1 /\ &0 < &K1 /\ &0 < &q /\ &0 < &P /\ &0 < &X1`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "X1" THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&X1 = &2 * &M1 * &K1 pow 2` ASSUME_TAC THENL
     [EXPAND_TAC "X1" THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `inv(&P)` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &P * s` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&P * inv(&P)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `lq <= &M1 * s` ASSUME_TAC THENL
     [UNDISCH_TAC `lq / &M1 <= s` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&q * lq <= &P pow 2 * s` ASSUME_TAC THENL
     [UNDISCH_TAC `&q * lq / &P pow 2 <= s` THEN
      SUBGOAL_THEN `&q * lq / &P pow 2 = (&q * lq) / &P pow 2` SUBST1_TAC
      THENL [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&P < &4 * &M1 * &K1` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= &K1` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      SUBGOAL_THEN
       `&M1 * &X1 * (&X1 / &q + &1) * (&7 * &M1 + &4 * &q * lq) =
        &7 * (&M1 pow 2 * &X1 pow 2) * inv(&q) + &4 * (&M1 * &X1 pow 2) * lq +
        &7 * (&M1 pow 2 * &X1) + &4 * (&M1 * &X1) * (&q * lq)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &M1 pow 2 * &X1 pow 2 /\ &0 <= &M1 * &X1 pow 2 /\
                    &0 <= &M1 pow 2 * &X1 /\ &0 <= &M1 * &X1`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&M1 pow 2 * &X1 pow 2) * inv(&q) <=
                    (&M1 pow 2 * &X1 pow 2) * s` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(&M1 * &X1 pow 2) * lq <= (&M1 * &X1 pow 2) * (&M1 * s)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= &2 * &X1 * s` ASSUME_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `&P * s` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_ARITH `&2 * x * s = (&2 * x) * s:real`] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `&4 * &M1 * &K1` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `&4 * &M1 * &K1 * &1 <= &4 * &M1 * &K1 * &K1` MP_TAC THENL
         [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
          ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&M1 pow 2 * &X1) * &1 <= (&M1 pow 2 * &X1) * (&2 * &X1 *
          s)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&P pow 2 <= &8 * &M1 * &X1` ASSUME_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `(&4 * &M1 * &K1) pow 2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE;
          REAL_POS];
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&M1 * &X1) * (&q * lq) <= (&M1 * &X1) * (&8 * &M1 * &X1 *
          s)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        TRANS_TAC REAL_LE_TRANS `&P pow 2 * s` THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH `&8 * m * x * s = (&8 * m * x) * s:real`] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(&M1 pow 2 * &X1 pow 2) * inv(&q) <=
                   (&M1 pow 2 * &X1 pow 2) * s:real` THEN
      UNDISCH_TAC `(&M1 * &X1 pow 2) * lq <= (&M1 * &X1 pow 2) * (&M1 *
          s:real)`
      THEN
      UNDISCH_TAC
       `(&M1 pow 2 * &X1) * &1 <= (&M1 pow 2 * &X1) * (&2 * &X1 * s:real)` THEN
      UNDISCH_TAC
       `(&M1 * &X1) * (&q * lq) <= (&M1 * &X1) * (&8 * &M1 * &X1 * s:real)`
         THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A1 = &X1 / &q + &1` THEN
  ABBREV_TAC `A2 = &7 * &M1 + &4 * &q * lq` THEN
  ABBREV_TAC `ss = sqrt(sqrt s)` THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `inv(&P)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ss /\ ss <= &1 /\ ss pow 4 = s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE];
      MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POS; REAL_POW_ONE] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_POW_ONE];
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
      ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s <= ss:real` ASSUME_TAC THENL
   [UNDISCH_TAC `(ss:real) pow 4 = s` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= TQ` ASSUME_TAC THENL
   [EXPAND_TAC "TQ" THEN
    REPEAT(MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
           REWRITE_TAC[]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &M1 * &X1 * A1 * A2` ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN EXPAND_TAC "A2" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_MUL; REAL_POS] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN EXPAND_TAC "lq" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `TQ pow 4 <= (&M1 * &K1) pow 8 * (&4 * L) pow 9 * (&228 * s)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `(&M1 pow 4 * &K1 pow 4 * lx pow 9) * (&M1 * &X1 * A1 * A2)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `TQ pow 4 <=
       &M1 pow 4 * &K1 pow 4 * lx pow 6 * &M1 * &X1 * lx pow 3 * A1 * A2` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `(&M1 pow 4 * &K1 pow 4 * (&4 * L) pow 9) * (&228 * (&M1 * &K1) pow 4 *
         s)`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POW_LE; REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN
        SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `TQ <= (&M1 * &K1) pow 2 * (&4 * (&4 * L) pow 3 * ss)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `4` THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_MUL] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(&M1 * &K1) pow 8 * (&4 * L) pow 9 * &228 * s`
      THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_POW_POW] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `(&4 * L) pow 9 <= (&4 * L) pow 12` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&M1 * &K1) pow 8 * s` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL;
                                                  REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `((&M1 * &K1) pow 8 * s) * (&4 * L) pow 9 * &228 <=
                  ((&M1 * &K1) pow 8 * s) * (&4 * L) pow 12 * &256`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &M1 /\ &0 < &K1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&K1 pow 2 * &M1 + &4 * &M1 pow 2 * &K1 + &8 * TQ <=
    &2053 * L pow 3 * (&M1 * &K1) pow 2 * ss`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&K1 pow 2 * &M1 = (&M1 * &K1) pow 2 * inv(&M1) /\
                  &M1 pow 2 * &K1 = (&M1 * &K1) pow 2 * inv(&K1)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN UNDISCH_TAC `&0 < &M1` THEN UNDISCH_TAC `&0 < &K1` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&M1 * &K1) pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `(&M1 * &K1) pow 2 * inv(&M1) <= (&M1 * &K1) pow 2 * ss /\
                  (&M1 * &K1) pow 2 * inv(&K1) <= (&M1 * &K1) pow 2 * ss`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= L pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((&M1 * &K1) pow 2 * ss) * &1 <=
                  ((&M1 * &K1) pow 2 * ss) * L pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
    UNDISCH_TAC `TQ <= (&M1 * &K1) pow 2 * &4 * (&4 * L) pow 3 * ss` THEN
    UNDISCH_TAC `(&M1 * &K1) pow 2 * inv(&M1) <= (&M1 * &K1) pow 2 * ss` THEN
    UNDISCH_TAC `(&M1 * &K1) pow 2 * inv(&K1) <= (&M1 * &K1) pow 2 * ss` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&36 * &M1 * log(&2 * &M1)) pow 2 <= (&72 * &M1 * L) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_MUL;
       REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&72 * m * l = &36 * m * &2 * l:real`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&M1 * &K1) pow 4 <= &P pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_POS; REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&72 * &M1 * L) pow 2 * (&K1 * lV pow 3) pow 2 *
    (&2053 * L pow 3 * (&M1 * &K1) pow 2 * ss)` THEN
  CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `(&36 * &M1 * log(&2 * &M1)) pow 2 * (&K1 * lV pow 3) pow 2 *
      (&K1 pow 2 * &M1 + &4 * &M1 pow 2 * &K1 + &8 * TQ)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &10642752 * L pow 5 * lV pow 6 * ss` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE] THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN TRY ASM_REAL_ARITH_TAC THEN
    EXPAND_TAC "lV" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`)
      THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&10642752 * L pow 5 * lV pow 6 * ss) * (&M1 * &K1) pow 4 <=
                (&10642752 * L pow 5 * lV pow 6 * ss) * &P pow 4` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

let TYPE2Q_BLOCK_ROOT = prove
 (`!U V P M1 x a q s.
     1 <= q /\ coprime(a,q) /\ abs(x - &a / &q) <= inv(&q pow 2) /\
     &2 <= V /\ 1 <= M1 /\ 3 <= P /\
     inv(&M1) <= s /\ inv V <= s /\ inv(&q) <= s /\
     (&1 + log(&q)) / &M1 <= s /\ inv(&P) <= s /\
     &q * (&1 + log(&q)) / &P pow 2 <= s /\ s <= &1
     ==> norm(vsum(M1+1..2*M1) (\m. Cx(mangoldt m - vaughan_F U m) *
                vsum(1..P DIV m)
                  (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x))))
         <= &P * sqrt(sqrt(&10642752 * log(&P) pow 5 * (&1 + log V) pow 6 *
                           sqrt(sqrt s)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K1 = P DIV (M1 + 1)` THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `inv(&P)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `Y = &10642752 * log(&P) pow 5 * (&1 + log V) pow 6 *
                  sqrt(sqrt s)` THEN
  SUBGOAL_THEN `&0 <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE] THEN MATCH_MP_TAC REAL_POW_LE THEN
    TRY(MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Ss = norm(vsum(M1+1..2*M1) (\m. Cx(mangoldt m - vaughan_F U m) *
                vsum(1..P DIV m)
                  (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x))))` THEN
  ASM_CASES_TAC `(V:real) < &K1` THENL
   [ALL_TAC;
    SUBGOAL_THEN `Ss = &0` SUBST1_TAC THENL
     [EXPAND_TAC "Ss" THEN REWRITE_TAC[NORM_EQ_0] THEN
      MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `vsum(1..P DIV m)
                     (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x)) =
                    vec 0` (fun th -> REWRITE_TAC[th; COMPLEX_MUL_RZERO;
                        COMPLEX_VEC_0]) THEN
      MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `vaughan_e V k = &0`
        (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
      MATCH_MP_TAC VAUGHAN_E_SMALL THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC REAL_LE_TRANS `&K1` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN TRANS_TAC LE_TRANS `P DIV m` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "K1" THEN MATCH_MP_TAC DIV_MONO2 THEN
        ASM_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE]]] THEN
  SUBGOAL_THEN `1 <= K1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`U:real`; `V:real`; `P:num`; `M1:num`; `K1:num`; `x:real`;
                `a:num`; `q:num`; `s:real`] TYPE2Q_BLOCK_NORM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `inv(V:real)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `4` THEN
  REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `sqrt(sqrt Y) pow 4 = Y` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
    ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `Ss pow 4 <= &10642752 * log(&P) pow 5 * (&1 + log V) pow 6 *
                            &P pow 4 * sqrt(sqrt s)` THEN
  EXPAND_TAC "Y" THEN REAL_ARITH_TAC);;

let INV_LE_TWO_DIV = prove
 (`!U M0. &2 <= U /\ U / &2 <= &M0 ==> inv(&M0) <= &2 / U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < U /\ &0 < &M0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  TRANS_TAC REAL_LE_TRANS `inv(&M0) * (&2 * &M0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &M0` THEN
    CONV_TAC REAL_FIELD]);;

let HUA_S3_BOUND = prove
 (`!U V P x a q s.
     1 <= q /\ coprime(a,q) /\ abs(x - &a / &q) <= inv(&q pow 2) /\
     &2 <= U /\ &2 <= V /\ 3 <= P /\
     &2 / U <= s /\ inv V <= s /\ inv(&q) <= s /\
     &2 * (&1 + log(&q)) / U <= s /\ inv(&P) <= s /\
     &q * (&1 + log(&q)) / &P pow 2 <= s /\ s <= &1
     ==> norm(vsum(1..P) (\m. Cx(mangoldt m - vaughan_F U m) *
                vsum(1..P DIV m)
                  (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x))))
         <= (&2 * log(&P) + &1) *
            (&P * sqrt(sqrt(&10642752 * log(&P) pow 5 * (&1 + log V) pow 6 *
                            sqrt(sqrt s))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `R = &P * sqrt(sqrt(&10642752 * log(&P) pow 5 *
                  (&1 + log V) pow 6 * sqrt(sqrt s)))` THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `inv(&P)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_LE_MUL THEN
     REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE] THEN MATCH_MP_TAC REAL_POW_LE THEN
    TRY(MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `U:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `M0:num`)] THEN
  MP_TAC(SPEC `U:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= M0 /\ U / &2 <= &M0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `P:num` EXISTS_LOG2) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \m. Cx(mangoldt m - vaughan_F U m) *
                      vsum(1..P DIV m)
                       (\k. Cx(vaughan_e V k) * expi(&((m * k) EXP 2) * x))`
                           THEN
  SUBGOAL_THEN `vsum(1..P) g = vsum(M0+1..M0 * 2 EXP (J + 1)) (g:num->complex)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `vsum(M0+1..P) (g:num->complex)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_SUPERSET THEN
      REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[vaughan_F] THEN
      SUBGOAL_THEN `&m <= U` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M0:real` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        REWRITE_TAC[REAL_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
      REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `P <= M0 * 2 EXP (J + 1)` MP_TAC THENL
         [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP (J + 1)` THEN
          CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
          REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
          ARITH_TAC];
        ALL_TAC] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN EXPAND_TAC "g" THEN
      SUBGOAL_THEN `P DIV m = 0` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC;
        REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH; COMPLEX_VEC_0;
                    COMPLEX_MUL_RZERO]]];
    ALL_TAC] THEN
  REWRITE_TAC[DYADIC_VSUM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..J) (\j. R)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    EXPAND_TAC "g" THEN EXPAND_TAC "R" THEN
    MATCH_MP_TAC TYPE2Q_BLOCK_ROOT THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `q:num`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&M0 <= &(M0 * 2 EXP j)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE; LE_MULT_EXP2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &M0` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&(M0 * 2 EXP j)) <= inv(&M0) /\ inv(&M0) <= &2 / U`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC INV_LE_TWO_DIV THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `M0:num` THEN
      ASM_REWRITE_TAC[LE_MULT_EXP2];
      ASM_MESON_TAC[REAL_LE_TRANS];
      TRANS_TAC REAL_LE_TRANS `&2 * (&1 + log(&q)) / U` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= &1 + log(&q)` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_ARITH `&2 * l * i = l * (&2 * i):real`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
      ASM_MESON_TAC[REAL_LE_TRANS]];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_LE_RADD] THEN
    MATCH_MP_TAC LOG2_BOUND THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The minor arc bound.                                                      *)
(* ------------------------------------------------------------------------- *)

let HUA_MINOR_LAMBDA = prove
 (`!M Kw Q j P U V D1 D2.
     j < M /\ ~(j IN circ_major M Kw Q) /\ 1 <= Q /\ 1 <= Kw /\ 3 <= P /\
     &2 <= U /\ &2 <= V /\ 1 <= D1 /\ V <= &D1 /\ 1 <= D2 /\ U * V <= &D2 /\
     &2 * (&1 + log(&Kw)) / U + inv V + inv(&Q) + inv(&P) +
     &Kw * (&1 + log(&Kw)) / &P pow 2 <= &1
     ==> norm(vsum(1..P) (\n. Cx(mangoldt n) * expi(&(n EXP 2) * (&j / &M))))
         <= &18 * U +
            &1 * &P * (&1 + log(&D1)) *
            (&2 * sqrt(hua_e1 P D1 Q Kw) * log(&P)) +
            log(&P) * &P * (&1 + log(&D2)) * sqrt(hua_e1 P D2 Q Kw) +
            (&2 * log(&P) + &1) *
            (&P * sqrt(sqrt(&10642752 * log(&P) pow 5 * (&1 + log V) pow 6 *
              sqrt(sqrt(&2 * (&1 + log(&Kw)) / U + inv V + inv(&Q) +
                        inv(&P) + &Kw * (&1 + log(&Kw)) / &P pow 2)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real`; `V:real`; `\n. expi(&(n EXP 2) * (&j / &M))`;
                 `P:num`] VAUGHAN_VSUM_GEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:complex) <= a' /\ norm b <= b' /\ norm c <= c' /\ norm d <= d'
    ==> norm(a + b - c + d) <= a' + b' + c' + d'`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC VAUGHAN_S0_BOUND THEN REWRITE_TAC[NORM_EXPI;
    REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC TYPEI_S1 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC TYPEI_S2 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`; `j:num`] MINOR_DIRICHLET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `q:num`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC HUA_S3_BOUND THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `q:num`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= q /\ &0 < U /\ &0 < V /\ &0 < &P /\ &0 < &Q /\ &0 < &q`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&q) /\ log(&q) <= log(&Kw) /\ &0 <= log(&Kw)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * (&1 + log(&Kw)) / U /\ &0 <= inv V /\
                &0 <= inv(&Q) /\ &0 <= inv(&P) /\
                &0 <= &Kw * (&1 + log(&Kw)) / &P pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[real_div] THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_POW_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t1 = &2 * (&1 + log(&Kw)) / U` THEN
  ABBREV_TAC `t5 = &Kw * (&1 + log(&Kw)) / &P pow 2` THEN
  SUBGOAL_THEN `&2 / U <= t1 /\ inv(&q) <= inv(&Q) /\
                &2 * (&1 + log(&q)) / U <= t1 /\
                &q * (&1 + log(&q)) / &P pow 2 <= t5`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN EXPAND_TAC "t5" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_POS];
        ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]);;
