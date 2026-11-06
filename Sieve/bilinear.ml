(* ========================================================================= *)
(* The bilinear form inequality ([N] Theorem 10.7) from Siegel-Walfisz.      *)
(*                                                                           *)
(* BILINEAR_BV: from SIEGEL_WALFISZ (sw.ml; for every A, B,                  *)
(* |sum_{p<=x} chi(p)| <= C x / log^A x for nonprincipal chi mod q with      *)
(* q <= log^B x), for every A there is C with                                *)
(*   sum_{d <= sqrt(XY) / log^A Y} |sum_{m <= X, Z < p <= Y, mp == a_d (d)}  *)
(*      alpha(m) - phi(d)^-1 sum_{(mp,d) = 1} alpha(m)|                      *)
(*   <= C X Y log^2(XY) / log^A Y     for |alpha| <= 1, X >= log^(2A) Y.     *)
(*                                                                           *)
(* Method ([N] 10.7).  Characters (CHARACTER_DISCREPANCY_BOUND), the box is  *)
(* a product so chi(mp) = chi(m) chi(p); each nonprincipal chi mod d = rs is *)
(* induced by a primitive chi* mod r > 1 (PRIMITIVE_REDUCTION_SUM), the      *)
(* twisted sums then depend only on s (BILINEAR_H_INDUCED), and              *)
(* phi(r) phi(s) <= phi(rs) (PHI_MUL_GE) gives the sum over s of 1/phi(s)    *)
(* (<= 4 (1 + log D), SUM_INV_PHI_LE) times inner sums over r.  For          *)
(* r <= log^A Y the prime sums are small by Siegel-Walfisz (SW_UNIFORM); for *)
(* larger r Cauchy-Schwarz and the large sieve bound the cumulative sums     *)
(* (BILINEAR_LARGE_SIEVE) and summation by parts (ABEL_RECIPROCAL_BOUND)     *)
(* gives XY/R0 + log D (X sqrt Y + Y sqrt X) + D sqrt(XY).                   *)
(* ========================================================================= *)

needs "Sieve/sw.ml";;
needs "Sieve/largesieve.ml";;
needs "Sieve/nt.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Arithmetic lemmas: phi, divisor sums, AM-GM, summation by parts.          *)
(* ------------------------------------------------------------------------- *)

let PHI_MUL_PRIME = prove
 (`!p k. prime p
         ==> phi(p * k) = (if p divides k then p else p - 1) * phi k`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; PHI_0]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `coprime(p:num,k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_COPRIME_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[PHI_MULTIPLICATIVE; PHI_PRIME]] THEN
  MP_TAC(SPECL [`k:num`; `p:num`] INDEX_DECOMPOSITION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `a = index p k` THEN
  SUBGOAL_THEN `~(a = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN ASM_REWRITE_TAC[INDEX_EQ_0] THEN
    ASM_MESON_TAC[PRIME_1];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rhs(concl th) = `k:num`)) THEN
  REWRITE_TAC[MULT_ASSOC; GSYM(CONJUNCT2 EXP)] THEN
  SUBGOAL_THEN `coprime(p EXP SUC a,m) /\ coprime(p EXP a,m)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COPRIME_LEXP]; ALL_TAC] THEN
  ASM_SIMP_TAC[PHI_MULTIPLICATIVE; PHI_PRIMEPOW; NOT_SUC] THEN
  REWRITE_TAC[MULT_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[SUC_SUB1; LEFT_SUB_DISTRIB] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(a = 0) ==> SUC(a - 1) = a`]);;

let PHI_MUL_GE = prove
 (`!m n. phi m * phi n <= phi(m * n)`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[PHI_0; MULT_CLAUSES; LE_0]; ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[PHI_1; MULT_CLAUSES; LE_REFL]; ALL_TAC] THEN
  MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [divides]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * k < p * k ==> k < p * k`) THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `2 <= p ==> 1 < p`) THEN
      ASM_MESON_TAC[PRIME_GE_2];
      DISCH_TAC THEN UNDISCH_TAC `~(p * k = 0)` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `m * p * k = p * m * k:num`] THEN
  ASM_SIMP_TAC[PHI_MUL_PRIME] THEN DISCH_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(if p divides k then p else p - 1) * phi m * phi k` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[DIVIDES_LMUL; LE_REFL] THEN
  COND_CASES_TAC THEN ARITH_TAC);;

let PHI_RATIO_LE = prove
 (`!n. ~(n = 0)
       ==> &n / &(phi n) <= sum {d | d divides n} (\d. inv(&(phi d)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(phi n)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&n = sum {d | d divides n} (\d. &(phi(n DIV d)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUM_DIVISORS_REFLECT; GSYM REAL_OF_NUM_SUM;
                 FINITE_DIVISORS; REWRITE_RULE[ETA_AX] PHI_DIVISORSUM];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_DIVISORS; IN_ELIM_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(phi d)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`n DIV d`; `d:num`] PHI_MUL_GE) THEN
  SUBGOAL_THEN `n DIV d * d = n` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[DIVIDES_DIV_MULT]);;

let SUM_INV_MUL_PHI_LE = prove
 (`!N. sum(1..N) (\e. inv(&e * &(phi e))) <= &4`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..N) (\e. sum {f | f divides e}
                       (\f. inv(&e pow 2) * inv(&(phi f))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    REWRITE_TAC[SUM_LMUL] THEN
    MP_TAC(SPEC `e:num` PHI_RATIO_LE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &e` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&e pow 2) * &e / &(phi e)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &e` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SUM_DIVISORS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\n. &2 * inv(&n pow 2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_MUL; REAL_INV_MUL] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_RMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * inv(&n pow 2) * inv(&(phi n))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[SUM_INV_SQUARE_LE_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2; REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
     ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> &2 * x <= &4`) THEN
    REWRITE_TAC[SUM_INV_SQUARE_LE_2]]);;

let SUM_INV_PHI_LE = prove
 (`!N. 1 <= N ==> sum(1..N) (\n. inv(&(phi n))) <= &4 * (&1 + log(&N))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..N) (\n. sum {d | d divides n} (\d. inv(&n) * inv(&(phi d))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[SUM_LMUL] THEN
    MP_TAC(SPEC `n:num` PHI_RATIO_LE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&n) * &n / &(phi n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &n` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SUM_DIVISORS] THEN
  SUBGOAL_THEN `&0 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\d. inv(&d * &(phi d)) * (&1 + log(&N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!k. inv(&(k * d)) * inv(&(phi d)) = inv(&k) * inv(&d * &(phi d))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_INV_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_RMUL] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    ASM_CASES_TAC `N DIV d = 0` THENL
     [ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + log(&(N DIV d))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HARMONIC_LE_LOG THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[DIV_LE]];
    REWRITE_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[SUM_INV_MUL_PHI_LE] THEN ASM_REAL_ARITH_TAC]);;

let REAL_SQRT_AMGM = prove
 (`!S U V. &0 <= U /\ &0 <= V /\
           (!l. &0 < l ==> S <= (l * U + V / l) / &2)
           ==> S <= sqrt U * sqrt V`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `U = &0` THENL
   [ASM_REWRITE_TAC[SQRT_0; REAL_MUL_LZERO] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `V / S + &1`) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE;
                 REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    SUBGOAL_THEN `(V:real) / (V / S + &1) = V * S / (V + S)` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD
       `&0 < S /\ &0 < V + S ==> V / (V / S + &1) = V * S / (V + S)`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `V * S / (V + S) <= S:real` MP_TAC THENL
     [SUBGOAL_THEN `(V:real) * S / (V + S) = S - S * S / (V + S)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD
         `&0 < V + S ==> V * S / (V + S) = S - S * S / (V + S)`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x:real`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `V = &0` THENL
   [ASM_REWRITE_TAC[SQRT_0; REAL_MUL_RZERO] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `S / (U + &1)`) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ;
                 REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `(S:real) / (U + &1) * U < S` MP_TAC THENL
     [SUBGOAL_THEN `(S:real) / (U + &1) * U = S - S / (U + &1)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD
         `&0 < U + &1 ==> S / (U + &1) * U = S - S / (U + &1)`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < y ==> x - y < x:real`) THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt U /\ &0 < sqrt V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `U = sqrt U pow 2 /\ V = sqrt V pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `a = sqrt U` THEN ABBREV_TAC `b = sqrt V` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(b:real) / a` o check (is_forall o concl)) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `V:real`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `U:real`)) THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> s <= x ==> s <= y:real`) THEN
  MAP_EVERY UNDISCH_TAC [`&0 < a`; `&0 < b`] THEN CONV_TAC REAL_FIELD);;

let SUM_AMGM = prove
 (`!s (x:A->real) y l.
     FINITE s /\ &0 < l
     ==> sum s (\i. x i * y i)
         <= (l * sum s (\i. x i pow 2) + inv l * sum s (\i. y i pow 2)) / &2`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[real_div; GSYM SUM_LMUL; GSYM SUM_ADD; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `(l * (x:A->real) i pow 2 + inv l * y i pow 2) * inv(&2) - x i * y i =
    (l * x i - y i) pow 2 * inv(&2 * l)`
  MP_TAC THENL
   [UNDISCH_TAC `&0 < l` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= z ==> a - b = z ==> b <= a`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC);;

let ABEL_RECIPROCAL_BOUND = prove
 (`!t a M c0 c1 c2.
     1 <= a /\ a <= M /\ (!r. &0 <= t r) /\
     &0 <= c0 /\ &0 <= c1 /\ &0 <= c2 /\
     (!k. a <= k /\ k <= M
          ==> sum(a..k) t <= c0 + c1 * &k + c2 * &k pow 2)
     ==> sum(a..M) (\r. t r / &r)
         <= c0 / &a + c1 * (&2 + log(&M)) + &2 * c2 * &M`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = \k. sum(a..k) (t:num->real)` THEN
  SUBGOAL_THEN
   `sum(a..M) (\r. (t:num->real) r / &r) =
    sum(a..M) (\r. inv(&r) * ((g:num->real) r - g(r - 1)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `0 < r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_RIGHT] THEN
    REWRITE_TAC[real_div; REAL_ADD_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_PARTIAL_PRE] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:num->real)(a - 1) = &0` SUBST1_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `!k. a <= k /\ k <= M ==> &0 <= (g:num->real) k /\
                    g k <= c0 + c1 * &k + c2 * &k pow 2`
  (LABEL_TAC "gb") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &a /\ &a <= &M` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; real_div] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= c0 * inv(&M + &1) + c1 + c2 * &M /\
    --y <= c0 * (inv(&a) - inv(&M + &1)) + c1 * (&1 + log(&M)) + c2 * &M
    ==> x - y <= c0 * inv(&a) + c1 * (&2 + log(&M)) + &2 * c2 * &M`) THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN CONJ_TAC THENL
   [USE_THEN "gb" (MP_TAC o SPEC `M:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 < &M + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&M + &1) * (c0 + c1 * &M + c2 * &M pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&M + &1) * &M <= &1 /\ inv(&M + &1) * &M pow 2 <= &M`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REWRITE_TAC[REAL_POW_2] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c1 * (inv(&M + &1) * &M) <= c1 * &1 /\
                  c2 * (inv(&M + &1) * &M pow 2) <= c2 * &M`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(a..M) (\x. c0 * (inv(&x) - inv(&x + &1)) + c1 * inv(&x) + c2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    BETA_TAC THEN USE_THEN "gb" (MP_TAC o SPEC `x:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `&1 <= &x` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&x) - inv(&x + &1) = inv(&x * (&x + &1))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `&1 <= &x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `--(g * (a - b)) = g * (b - a:real)`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(c0 + c1 * &x + c2 * &x pow 2) * inv(&x * (&x + &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(c0 + c1 * &x + c2 * &x pow 2) * inv(&x * (&x + &1)) =
      c0 * inv(&x * (&x + &1)) + c1 * inv(&x + &1) + c2 * (&x / (&x + &1))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&1 <= &x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `b <= c1 * inv(&x) /\ c <= c2
      ==> a + b + c <= a + c1 * inv(&x) + c2`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &x + &1` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG] THEN
  SUBGOAL_THEN
   `sum(a..M) (\x. inv(&x) - inv(&x + &1)) = inv(&a) - inv(&M + &1)`
  SUBST1_TAC THENL
   [MP_TAC(INST [`\k. --inv(&k)`,`f:num->real`]
      (SPECL [`a:num`; `M:num`] SUM_DIFFS_ALT)) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum (a..M) (\k. --inv (&k + &1) - --inv (&k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(a..M) (\x. inv(&x)) <= &1 + log(&M) /\ &((M + 1) - a) <= &M`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..M) (\x. inv(&x))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
        CONJ_TAC THENL
         [ASM_ARITH_TAC;
          REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]];
        MATCH_MP_TAC HARMONIC_LE_LOG THEN ASM_ARITH_TAC];
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c1 * sum(a..M) (\x. inv(&x)) <= c1 * (&1 + log(&M)) /\
    c2 * &((M + 1) - a) <= c2 * &M`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let LOG_POW_RATIO_MONO = prove
 (`!x y A. &0 < x /\ x <= y /\ &0 < log x /\ &0 < log y /\
           log y <= &2 * log x
           ==> x / log x pow A <= &2 pow A * (y / log y pow A)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log x pow A /\ &0 < log y pow A` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `y / log y pow A * log y pow A` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `y / log y pow A * (&2 * log x) pow A` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]);;

let SQRT_DIV_POW_LE = prove
 (`!X Y A l. &1 <= X /\ &1 <= Y /\ &1 / &2 <= l
             ==> sqrt(X * Y) / l pow A <= (X * Y) * &2 pow A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= X * Y` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1`; `X:real`; `&1`; `Y:real`] REAL_LE_MUL2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&2 = inv(&1 / &2)` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]]);;

let NUMSEG_REAL_FLOOR = prove
 (`!X. &0 <= X
       ==> ?N. &N <= X /\ X < &N + &1 /\ {m | 1 <= m /\ &m <= X} = 1..N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `X:real` FLOOR_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  MP_TAC(SPEC `X:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `&m < &N + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Characters: discrepancies and the reduction to primitive characters.      *)
(* ------------------------------------------------------------------------- *)

let CHARACTER_SUM_INDICATOR = prove
 (`!q a (n:A->num) (w:A->real) t.
     1 <= q /\ coprime(a,q) /\ FINITE t
     ==> vsum {c | dirichlet_character q c}
              (\c. cnj(c a) * vsum t (\x. Cx(w x) * c(n x))) =
         Cx(&(phi q)) * Cx(sum {x | x IN t /\ (n x == a) (mod q)} w)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; ASSUME `FINITE(t:A->bool)`] THEN
  MP_TAC(ISPECL
   [`\c x. cnj((c:num->complex) a) * Cx((w:A->real) x) * c((n:A->num) x)`;
    `{c | dirichlet_character q c}`; `t:A->bool`] VSUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum t (\x:A. if ((n:A->num) x == a) (mod q)
                  then Cx(&(phi q)) * Cx((w:A->real) x) else Cx(&0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    ONCE_REWRITE_TAC[COMPLEX_RING
     `cnj((c:num->complex) a) * (w:complex) * c(m:num) = w * cnj(c a) * c m`]
    THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_DIRICHLET_CHARACTERS] THEN
    ASM_SIMP_TAC[DIRICHLET_CHARACTER_SUM_CNJ_MUL] THEN
    REWRITE_TAC[CONG_SYM] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  ASM_SIMP_TAC[GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_RESTRICT; VSUM_CX]);;

let CHARACTER_DISCREPANCY_BOUND = prove
 (`!q a (n:A->num) (w:A->real) t.
     1 <= q /\ coprime(a,q) /\ FINITE t
     ==> abs(sum {x | x IN t /\ (n x == a) (mod q)} w -
             inv(&(phi q)) * sum {x | x IN t /\ coprime(n x,q)} w)
         <= inv(&(phi q)) *
            sum ({c | dirichlet_character q c} DELETE chi_0 q)
                (\c. norm(vsum t (\x. Cx(w x) * c(n x))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(phi q)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum ({c | dirichlet_character q c} DELETE chi_0 q)
         (\c. cnj((c:num->complex) a) *
              vsum t (\x:A. Cx((w:A->real) x) * c((n:A->num) x))) =
    Cx(&(phi q) * sum {x | x IN t /\ (n x == a) (mod q)} w -
       sum {x | x IN t /\ coprime(n x,q)} w)`
  ASSUME_TAC THENL
   [SIMP_TAC[VSUM_DELETE; FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM;
             DIRICHLET_CHARACTER_CHI_0] THEN
    ASM_SIMP_TAC[CHARACTER_SUM_INDICATOR] THEN
    REWRITE_TAC[CX_SUB; CX_MUL] THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[chi_0; CNJ_CX; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[COND_RAND; COMPLEX_MUL_RZERO; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    ASM_SIMP_TAC[GSYM VSUM_RESTRICT_SET; VSUM_CX; FINITE_RESTRICT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `inv(&(phi q)) *
    norm(vsum ({c | dirichlet_character q c} DELETE chi_0 q)
               (\c. cnj((c:num->complex) a) *
                    vsum t (\x:A. Cx((w:A->real) x) * c((n:A->num) x))))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ASM_SIMP_TAC[REAL_FIELD
     `!f x y. &0 < f ==> x - inv f * y = inv f * (f * x - y)`] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < f ==> abs f = f`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; ASSUME `&0 < &(phi q)`] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_DELETE; FINITE_DIRICHLET_CHARACTERS] THEN
  REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

let DIRICHLET_CHARACTER_MOD_1 = prove
 (`!c n. dirichlet_character 1 c ==> c n = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP
    DIRICHLET_CHARACTER_EQ_1 th)]) THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC[NUMBER_RULE `(a == b) (mod 1)`]);;

let FINITE_PRIMITIVE_CHARACTERS = prove
 (`!r. FINITE {c | primitive_character r c}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c | dirichlet_character r c}` THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; SUBSET; IN_ELIM_THM] THEN
  SIMP_TAC[primitive_character]);;

let PRIMITIVE_REDUCTION_SUM = prove
 (`!q (g:(num->complex)->real).
     1 <= q /\ (!c. &0 <= g c)
     ==> sum ({c | dirichlet_character q c} DELETE chi_0 q) g
         <= sum {r | r divides q /\ ~(r = 1)}
                (\r. sum {c | primitive_character r c}
                         (\c. g(\n. if coprime(n,q) then c n else Cx(&0))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {r | r divides q /\ ~(r = 1)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r | r divides q}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC; SET_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_PRODUCT o rand o snd) THEN
  ASM_REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC
   `P = {r,c | r IN {r | r divides q /\ ~(r = 1)} /\
               c IN {c | primitive_character r c}}` THEN
  SUBGOAL_THEN `FINITE(P:num#(num->complex)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS];
    ALL_TAC] THEN
  ABBREV_TAC
   `h = \x:num#(num->complex).
          (\n. if coprime(n,q) then SND x n else Cx(&0))` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE h (P:num#(num->complex)->bool))
                  (g:(num->complex)->real)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `c:num->complex` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`q:num`; `c:num->complex`] PRIMITIVE_CHARACTER_EXISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `c':num->complex`] THEN STRIP_TAC THEN
    EXISTS_TAC `(r:num,c':num->complex)` THEN
    SUBGOAL_THEN
     `c = (\n. if coprime(n,q) then (c':num->complex) n else Cx(&0))`
    ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0];
      ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "h" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(c = chi_0 q)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[chi_0; FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIRICHLET_CHARACTER_MOD_1 THEN
    ASM_MESON_TAC[primitive_character];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (P:num#(num->complex)->bool) ((g:(num->complex)->real) o h)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_IMAGE_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM]]);;

let CARD_DIRICHLET_CHARACTERS = prove
 (`!d. 1 <= d ==> CARD {c | dirichlet_character d c} = phi d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `1`] DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS) THEN
  ASM_REWRITE_TAC[CONG_REFL] THEN
  SUBGOAL_THEN
   `vsum {c | dirichlet_character d c} (\c. c 1) =
    vsum {c | dirichlet_character d c} (\c. Cx(&1))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[DIRICHLET_CHARACTER_EQ_1];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_CONST; FINITE_DIRICHLET_CHARACTERS] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID; CX_INJ; REAL_OF_NUM_EQ]);;

let CARD_PRIMITIVE_CHARACTERS_LE = prove
 (`!r. 1 <= r ==> &(CARD {c | primitive_character r c}) <= &(phi r)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM CARD_DIRICHLET_CHARACTERS] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; SUBSET; IN_ELIM_THM] THEN
  SIMP_TAC[primitive_character]);;

let INDUCED_COPRIME_EQ = prove
 (`!r s c n. dirichlet_character r c
             ==> (if coprime(n,r * s) then c n else Cx(&0)) =
                 (if coprime(n,s) then c n else Cx(&0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COPRIME_RMUL] THEN
  ASM_CASES_TAC `coprime(n:num,s)` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0]);;

let VSUM_BOX_FACTOR = prove
 (`!M P (c:num->complex) (alpha:num->real).
     FINITE M /\ FINITE P /\ (!m n. c(m * n) = c m * c n)
     ==> vsum {x | FST x IN M /\ SND x IN P}
              (\x. Cx(alpha(FST x)) * c(FST x * SND x)) =
         vsum M (\m. Cx(alpha m) * c m) * vsum P c`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; ASSUME `FINITE(M:num->bool)`] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; ASSUME `FINITE(P:num->bool)`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_VSUM_PRODUCT o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `{x:num#num | FST x IN M /\ SND x IN P} = {i,j | i IN M /\ j IN P}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_ASSOC]);;

let SUM_HYPERBOLA_SWAP = prove
 (`!(f:num->num->real) N.
     sum(1..N) (\r. sum(1..N DIV r) (\k. f r k)) =
     sum(1..N) (\k. sum(1..N DIV k) (\r. f r k))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!r. 1 <= r ==> 1..N DIV r = {k | k IN 1..N /\ r * k <= N}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= r:num ==> ~(r = 0)`] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC LE_TRANS `r * k:num` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k:num = 1 * k`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..N) (\r. sum(1..N) (\k. if r * k <= N then f r k else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN SIMP_TAC[SUM_RESTRICT_SET; FINITE_NUMSEG];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN SIMP_TAC[SUM_RESTRICT_SET; FINITE_NUMSEG] THEN
  REWRITE_TAC[MULT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Siegel-Walfisz, uniformly in x <= y.                                      *)
(* ------------------------------------------------------------------------- *)

let PRIME_VSUM_TRIVIAL = prove
 (`!x (c:num->complex).
     &0 <= x /\ (!n. norm(c n) <= &1)
     ==> norm(vsum {p | prime p /\ &p <= x} c) <= x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` NUMSEG_REAL_FLOOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{p | prime p /\ &p <= x} SUBSET 1..N` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ &p <= x} (\p. &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..N) (\p. &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID]]);;

let SW_UNIFORM = prove
 (`!A B. ?C. &0 <= C /\
             !y x q c. &2 <= y /\ x <= y /\ 1 <= q /\ &q <= log y pow B /\
                       dirichlet_character q c /\ ~(c = chi_0 q)
                       ==> norm(vsum {p | prime p /\ &p <= x} c)
                           <= C * y / log y pow A`,
  ASSUME_TAC SIEGEL_WALFISZ THEN
  MAP_EVERY X_GEN_TAC [`A:num`; `B:num`] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `C:real` o SPECL [`A:num`; `B + 1`]) THEN
  ABBREV_TAC `K1 = (&2 * &A) pow A` THEN
  ABBREV_TAC `E = exp(&2 pow B)` THEN
  EXISTS_TAC `K1 + abs C * &2 pow A + E * K1` THEN
  SUBGOAL_THEN `&0 <= K1 /\ &1 <= E` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K1"; "E"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `&2 pow B` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&0 <= &2 pow B` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real`; `x:real`; `q:num`; `c:num->complex`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!n. norm((c:num->complex) n) <= &1` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log y` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log y pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sqrt y /\ sqrt y * sqrt y = y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt y <= K1 * y / log y pow A` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
    MP_TAC(SPECL [`A:num`; `y:real`] LOG_POW_LE_SQRT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt y * K1 * sqrt y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH `s * k * s = k * (s * s:real)`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `Qy = y / log y pow A` THEN
  SUBGOAL_THEN `&0 < Qy` ASSUME_TAC THENL
   [EXPAND_TAC "Qy" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ALL_TAC THEN
  SUBGOAL_THEN
   `&0 <= abs C * &2 pow A * Qy /\ &0 <= E * K1 * Qy /\ &0 <= K1 * Qy`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_POW_LE; REAL_POS; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
  ASM_CASES_TAC `x <= sqrt y` THENL
   [MATCH_MP_TAC(REAL_ARITH
      `n <= a /\ &0 <= b /\ &0 <= c ==> n <= a + b + c`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt y` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&0 <= x` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real` THEN
      ASM_SIMP_TAC[PRIME_VSUM_TRIVIAL];
      SUBGOAL_THEN `{p | prime p /\ &p <= x} = {}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        GEN_TAC THEN MP_TAC(SPEC `x':num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[VSUM_CLAUSES; NORM_0] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < x /\ &0 < log x /\ log y <= &2 * log x`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_POS_LT] THEN
    MP_TAC(SPEC `y:real` LOG_SQRT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `log(sqrt y) <= log x` MP_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&2 pow B <= log x` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH
      `n <= c /\ &0 <= a /\ &0 <= b ==> n <= a + b + c`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `x:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRIME_VSUM_TRIVIAL THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `x < E` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN
      SUBGOAL_THEN `x = exp(log x)` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E * sqrt y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x < e /\ e * &1 <= e * s ==> x <= e * s`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]] THEN
  MATCH_MP_TAC(REAL_ARITH
    `n <= b /\ &0 <= a /\ &0 <= c ==> n <= a + b + c`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 <= x` ASSUME_TAC THENL
   [SUBGOAL_THEN `x = exp(log x)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `log x` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `&1 <= &2 pow B` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&q <= log x pow (B + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log y pow B` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * log x) pow B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL; REAL_POW_ADD; REAL_POW_1] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `q:num`; `c:num->complex`] o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> n <= a ==> n <= b:real`) THEN
  EXPAND_TAC "Qy" THEN
  SUBGOAL_THEN `&0 < log x pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs C * x / log x pow A` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC LOG_POW_RATIO_MONO THEN ASM_REAL_ARITH_TAC);;

let PRIME_INTERVAL_TWIST = prove
 (`!Y Z s (c:num->complex).
     1 <= s /\ (!n. norm(c n) <= &1)
     ==> norm(vsum {p | prime p /\ Z < &p /\ &p <= Y}
                   (\p. if coprime(p,s) then c p else Cx(&0)))
         <= norm(vsum {p | prime p /\ &p <= Y} c) +
            norm(vsum {p | prime p /\ &p <= Z} c) + log(&s) / log(&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. FINITE {p | prime p /\ &p <= x}` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ABBREV_TAC `Ps = {p | prime p /\ Z < &p /\ &p <= Y}` THEN
  SUBGOAL_THEN `FINITE(Ps:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ps" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\ &p <= Y}` THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o SPEC `Y:real`);
      SIMP_TAC[SUBSET; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum Ps (\p. if coprime(p,s) then (c:num->complex) p else Cx(&0)) =
    vsum Ps c - vsum {p | p IN Ps /\ p divides s} c`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM VSUM_DIFF; SUBSET_RESTRICT] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    ASM_SIMP_TAC[GSYM VSUM_RESTRICT_SET] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `(p:num) IN Ps` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `prime p` (fun th -> SIMP_TAC[th; PRIME_COPRIME_EQ]) THEN
    UNDISCH_TAC `(p:num) IN Ps` THEN EXPAND_TAC "Ps" THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_ASSOC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:complex) <= x /\ norm(b:complex) <= y ==> norm(a - b) <= x + y`)
  THEN CONJ_TAC THENL
   [ASM_CASES_TAC `Z <= Y` THENL
     [SUBGOAL_THEN
       `Ps = {p | prime p /\ &p <= Y} DIFF {p | prime p /\ &p <= Z}`
      SUBST1_TAC THENL
       [EXPAND_TAC "Ps" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
        X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `{p | prime p /\ &p <= Z} SUBSET {p | prime p /\ &p <= Y}`
      ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LE_TRANS];
        ALL_TAC] THEN
      ASM_SIMP_TAC[VSUM_DIFF] THEN
      MATCH_ACCEPT_TAC(NORM_ARITH
       `!x y:complex. norm(x - y) <= norm x + norm y`);
      SUBGOAL_THEN `Ps:num->bool = {}` SUBST1_TAC THENL
       [EXPAND_TAC "Ps" THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[VSUM_CLAUSES; NORM_0] THEN
        MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[NORM_POS_LE]]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {p | prime p /\ p divides s})` THEN
  ASM_SIMP_TAC[OMEGA_LE_LOG] THEN
  SUBGOAL_THEN
   `{p | p IN Ps /\ p divides s} SUBSET {p | prime p /\ p divides s}`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ps" THEN SIMP_TAC[SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p divides s}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {p | p IN Ps /\ p divides s})` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {p | p IN Ps /\ p divides s} (\p. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_SIMP_TAC[FINITE_RESTRICT];
      ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT; REAL_MUL_RID; REAL_LE_REFL]];
    REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The large sieve for bilinear sums.                                        *)
(* ------------------------------------------------------------------------- *)

let SQRT_LS_BOUND = prove
 (`!N k. sqrt((&4 * &N + &36 * &k pow 2) * &N)
         <= &2 * &N + &6 * &k * sqrt(&N)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(&N) /\ sqrt(&N) pow 2 = &N` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
  ABBREV_TAC `s = sqrt(&N)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rhs(concl th) = `&N:real`)) THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN
  SUBGOAL_THEN `&0 <= &k * s pow 3 /\ &0 <= &k * s /\ &0 <= s pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let SUM_NORM_POW2_LE_CARD = prove
 (`!N (a:num->complex). (!n. norm(a n) <= &1)
                        ==> sum(1..N) (\n. norm(a n) pow 2) <= &N`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\n. &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_LE_REFL]]);;

let BILINEAR_LARGE_SIEVE = prove
 (`!N1 N2 (a:num->complex) (b:num->complex) k.
     1 <= k /\ (!n. norm(a n) <= &1) /\ (!n. norm(b n) <= &1)
     ==> sum(1..k) (\r. &r / &(phi r) *
                       sum {c | primitive_character r c}
                           (\c. norm(vsum(1..N1) (\n. a n * c n)) *
                                norm(vsum(1..N2) (\n. b n * c n))))
         <= (&2 * &N1 + &6 * &k * sqrt(&N1)) *
            (&2 * &N2 + &6 * &k * sqrt(&N2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!N. &0 <= (&4 * &N + &36 * &k pow 2) * &N` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt((&4 * &N1 + &36 * &k pow 2) * &N1) *
              sqrt((&4 * &N2 + &36 * &k pow 2) * &N2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_LS_BOUND;
     SQRT_POS_LE]] THEN
  MATCH_MP_TAC REAL_SQRT_AMGM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `l:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `N1:num`; `a:num->complex`]
    LARGE_SIEVE_MULTIPLICATIVE) THEN
  MP_TAC(SPECL [`k:num`; `N2:num`; `b:num->complex`]
    LARGE_SIEVE_MULTIPLICATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N1:num`; `a:num->complex`] SUM_NORM_POW2_LE_CARD) THEN
  MP_TAC(SPECL [`N2:num`; `b:num->complex`] SUM_NORM_POW2_LE_CARD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..k) (\r. &r / &(phi r) *
       ((l * sum {c | primitive_character r c}
                (\c. norm(vsum(1..N1) (\n. (a:num->complex) n * c n)) pow 2) +
         inv l * sum {c | primitive_character r c}
                (\c. norm(vsum(1..N2) (\n. (b:num->complex) n * c n)) pow 2)) /
        &2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC SUM_AMGM THEN ASM_REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(l * sum(1..k) (\r. &r / &(phi r) *
           sum {c | primitive_character r c}
               (\c. norm(vsum(1..N1) (\n. (a:num->complex) n * c n)) pow 2)) +
     inv l * sum(1..k) (\r. &r / &(phi r) *
           sum {c | primitive_character r c}
               (\c. norm(vsum(1..N2) (\n. (b:num->complex) n * c n)) pow 2)))
    / &2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..k) (\r. (l * (&r / &(phi r) *
           sum {c | primitive_character r c}
               (\c. norm(vsum(1..N1) (\n. (a:num->complex) n * c n)) pow 2)) +
       inv l * (&r / &(phi r) *
           sum {c | primitive_character r c}
               (\c. norm(vsum(1..N2) (\n. (b:num->complex) n * c n)) pow 2)))
       / &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[real_div] THEN
      REWRITE_TAC[REAL_ARITH `!w l m s t h:real.
        w * ((l * s + m * t) * h) = (l * (w * s) + m * (w * t)) * h`];
      REWRITE_TAC[real_div; SUM_RMUL; SUM_ADD_NUMSEG; SUM_LMUL]];
    ALL_TAC] THEN
  ABBREV_TAC
   `SA = sum(1..k) (\r. &r / &(phi r) *
          sum {c | primitive_character r c}
              (\c. norm(vsum(1..N1) (\n. (a:num->complex) n * c n)) pow 2))`
  THEN
  ABBREV_TAC
   `SB = sum(1..k) (\r. &r / &(phi r) *
          sum {c | primitive_character r c}
              (\c. norm(vsum(1..N2) (\n. (b:num->complex) n * c n)) pow 2))`
  THEN
  ABBREV_TAC `TA = sum(1..N1) (\n. norm((a:num->complex) n) pow 2)` THEN
  ABBREV_TAC `TB = sum(1..N2) (\n. norm((b:num->complex) n) pow 2)` THEN
  ABBREV_TAC `c1 = &4 * &N1 + &36 * &k pow 2` THEN
  ABBREV_TAC `c2 = &4 * &N2 + &36 * &k pow 2` THEN
  SUBGOAL_THEN `&0 <= c1 /\ &0 <= c2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c1"; "c2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `SA <= c1 * &N1 /\ SB <= c2 * &N2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `(c1:real) * TA`; EXISTS_TAC `(c2:real) * TB`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `l * SA <= l * c1 * &N1 /\ inv l * SB <= inv l * c2 * &N2`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bilinear form inequality.                                             *)
(* ------------------------------------------------------------------------- *)

let TWISTED_ALPHA_SUM_BOUND = prove
 (`!X s (alpha:num->real) (c:num->complex).
     &0 <= X /\ (!n. abs(alpha n) <= &1) /\ (!n. norm(c n) <= &1)
     ==> norm(vsum {m | 1 <= m /\ &m <= X}
                   (\m. Cx(alpha m) * (if coprime(m,s) then c m else Cx(&0))))
         <= X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `X:real` NUMSEG_REAL_FLOOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\m. &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS;
     NORM_POS_LE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID]]);;

let BILINEAR_DISCREPANCY_CHARS = prove
 (`!M P (alpha:num->real) a d.
     FINITE M /\ FINITE P /\ 1 <= d /\ coprime(a,d)
     ==> abs(sum {x | FST x IN M /\ SND x IN P /\
                      (FST x * SND x == a) (mod d)} (\x. alpha(FST x)) -
             inv(&(phi d)) *
             sum {x | FST x IN M /\ SND x IN P /\
                      coprime(FST x * SND x,d)} (\x. alpha(FST x)))
         <= inv(&(phi d)) *
            sum {r | r divides d /\ ~(r = 1)}
             (\r. sum {c | primitive_character r c}
               (\c. norm(vsum M (\m. Cx(alpha m) *
                          (if coprime(m,d) then c m else Cx(&0)))) *
                    norm(vsum P (\p. if coprime(p,d) then c p
                                     else Cx(&0)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {x:num#num | FST x IN M /\ SND x IN P}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i,j | (i:num) IN M /\ (j:num) IN P}` THEN
    ASM_SIMP_TAC[FINITE_PRODUCT] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:num`; `a:num`; `\x:num#num. FST x * SND x`;
                 `\x:num#num. (alpha:num->real)(FST x)`;
                 `{x:num#num | FST x IN M /\ SND x IN P}`]
    CHARACTER_DISCREPANCY_BOUND) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum ({c | dirichlet_character d c} DELETE chi_0 d)
        (\c. norm(vsum M (\m. Cx((alpha:num->real) m) * c m)) *
             norm(vsum P c))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN X_GEN_TAC `c:num->complex` THEN
    STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC VSUM_BOX_FACTOR THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`d:num`;
    `\c. norm(vsum M (\m. Cx((alpha:num->real) m) * c m)) *
         norm(vsum P (c:num->complex))`] PRIMITIVE_REDUCTION_SUM) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
  REWRITE_TAC[ETA_AX]);;

let BILINEAR_REINDEX = prove
 (`!(Fn:num->num->real) N.
     (!r d. &0 <= Fn r d)
     ==> sum(1..N) (\d. inv(&(phi d)) *
                        sum {r | r divides d /\ ~(r = 1)} (\r. Fn r d))
         <= sum(1..N) (\k. inv(&(phi k)) *
                 sum(1..N DIV k) (\r. if r = 1 then &0
                                      else inv(&(phi r)) * Fn r (k * r)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..N) (\d. sum {r | r divides d}
       (\r. if r = 1 then &0
             else inv(&(phi d)) * (Fn:num->num->real) r d))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    SUBGOAL_THEN
     `{r | r divides d /\ ~(r = 1)} =
      {r | r IN {r | r divides d} /\ ~(r = 1)}`
    SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SUM_DIVISORS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..N) (\r. sum(1..N DIV r) (\k. inv(&(phi k)) *
       (if r = 1 then &0
        else inv(&(phi r)) * (Fn:num->num->real) r (k * r))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
     BETA_TAC THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      BETA_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_LE;
     PHI_MUL_GE] THEN
    REWRITE_TAC[LT_MULT] THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_HYPERBOLA_SWAP] THEN REWRITE_TAC[SUM_LMUL; REAL_LE_REFL]);;

let bilinear_A = new_definition
 `bilinear_A X (alpha:num->real) s (c:num->complex) =
    vsum {m | 1 <= m /\ &m <= X}
         (\m. Cx(alpha m) * (if coprime(m,s) then c m else Cx(&0)))`;;

let bilinear_P = new_definition
 `bilinear_P Y Z s (c:num->complex) =
    vsum {p | prime p /\ Z < &p /\ &p <= Y}
         (\p. if coprime(p,s) then c p else Cx(&0))`;;

let bilinear_H = new_definition
 `bilinear_H X Y Z (alpha:num->real) r s =
    sum {c | primitive_character r c}
        (\c. norm(bilinear_A X alpha s c) * norm(bilinear_P Y Z s c))`;;

let BILINEAR_H_POS = prove
 (`!X Y Z alpha r s. &0 <= bilinear_H X Y Z alpha r s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bilinear_H] THEN MATCH_MP_TAC SUM_POS_LE THEN
  SIMP_TAC[FINITE_PRIMITIVE_CHARACTERS; REAL_LE_MUL; NORM_POS_LE]);;

let BILINEAR_A_NUMSEG = prove
 (`!X (alpha:num->real) s c N.
     {m | 1 <= m /\ &m <= X} = 1..N
     ==> bilinear_A X alpha s c =
         vsum(1..N) (\n. (Cx(alpha n) *
                          (if coprime(n,s) then Cx(&1) else Cx(&0))) * c n)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bilinear_A] THEN
  MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_MUL_RID; COMPLEX_MUL_RZERO;
                                  COMPLEX_MUL_LZERO]);;

let BILINEAR_P_NUMSEG = prove
 (`!Y Z s c N.
     &N <= Y /\ Y < &N + &1
     ==> bilinear_P Y Z s c =
         vsum(1..N) (\n. (if prime n /\ Z < &n /\ coprime(n,s)
                          then Cx(&1) else Cx(&0)) * c n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bilinear_P] THEN
  SUBGOAL_THEN
   `{p | prime p /\ Z < &p /\ &p <= Y} =
    {n | n IN 1..N /\ prime n /\ Z < &n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `prime n` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= n` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(SPEC `n:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `&n < &N + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `prime n /\ Z < &n` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    ASM_MESON_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]);;

let BILINEAR_LARGE_PART = prove
 (`!X Y Z (alpha:num->real) s a M.
     &0 <= X /\ &0 <= Y /\ (!n. abs(alpha n) <= &1) /\ 1 <= a /\ a <= M
     ==> sum(a..M) (\r. inv(&(phi r)) * bilinear_H X Y Z alpha r s)
         <= &4 * X * Y / &a +
            &12 * (X * sqrt Y + Y * sqrt X) * (&2 + log(&M)) +
            &72 * sqrt X * sqrt Y * &M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `X:real` NUMSEG_REAL_FLOOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `Y:real` NUMSEG_REAL_FLOOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `t = \r. &r / &(phi r) * bilinear_H X Y Z (alpha:num->real) r s` THEN
  SUBGOAL_THEN `!r. &0 <= (t:num->real) r` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[BILINEAR_H_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(a..M) (\r. (t:num->real) r / &r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(&r = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt X /\ &0 <= sqrt Y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:num->real`; `a:num`; `M:num`; `&4 * X * Y`;
                 `&12 * (X * sqrt Y + Y * sqrt X)`; `&36 * sqrt X * sqrt Y`]
    ABEL_RECIPROCAL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
       ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC];
    MATCH_MP_TAC(REAL_ARITH `x = y ==> s <= x ==> s <= y`) THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..k) (t:num->real)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bilinear_H] THEN
  REWRITE_TAC[MATCH_MP BILINEAR_A_NUMSEG
    (ASSUME `{m | 1 <= m /\ &m <= X} = 1..N1`)] THEN
  REWRITE_TAC[MATCH_MP BILINEAR_P_NUMSEG
    (CONJ (ASSUME `&N2 <= Y`) (ASSUME `Y < &N2 + &1`))] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * &N1 + &6 * &k * sqrt(&N1)) *
              (&2 * &N2 + &6 * &k * sqrt(&N2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BILINEAR_LARGE_SIEVE THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THEN GEN_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&N1) <= sqrt X /\ sqrt(&N2) <= sqrt Y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * X + &6 * &k * sqrt X) * (&2 * Y + &6 * &k * sqrt Y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        SIMP_TAC[REAL_POS; SQRT_POS_LE] THEN NO_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= b /\ c <= d ==> &2 * a + c <= &2 * b + d`) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
            [REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]);;

let BILINEAR_P_SW_BOUND = prove
 (`!C1 A Y Z s r c.
     (!y x q c. &2 <= y /\ x <= y /\ 1 <= q /\ &q <= log y pow A /\
                dirichlet_character q c /\ ~(c = chi_0 q)
                ==> norm(vsum {p | prime p /\ &p <= x} c)
                    <= C1 * y / log y pow (2 * A)) /\
     &0 <= C1 /\ &2 <= Y /\ 1 <= s /\ 2 <= r /\ &r <= log Y pow A /\
     primitive_character r c
     ==> norm(bilinear_P Y Z s c)
         <= &2 * C1 * Y / log Y pow (2 * A) + log(&s) / log(&2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
    [primitive_character]) THEN
  SUBGOAL_THEN `~(c = chi_0 r)` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIMITIVE_CHARACTER_NONPRINCIPAL THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. norm((c:num->complex) n) <= &1` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&s) / log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C1 * Y / log Y pow (2 * A)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `Z <= Y:real` THENL
   [REWRITE_TAC[bilinear_P] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vsum {p | prime p /\ &p <= Y} (c:num->complex)) +
                norm(vsum {p | prime p /\ &p <= Z} c) + log(&s) / log(&2)` THEN
    ASM_SIMP_TAC[PRIME_INTERVAL_TWIST] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= b /\ c <= b ==> a + c + l <= &2 * b + l`) THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`Y:real`; `Y:real`; `r:num`;
                                  `c:num->complex`]);
      FIRST_ASSUM(MP_TAC o SPECL [`Y:real`; `Z:real`; `r:num`;
                                  `c:num->complex`])] THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_ARITH_TAC; REWRITE_TAC[]]);
    REWRITE_TAC[bilinear_P] THEN
    SUBGOAL_THEN `{p | prime p /\ Z < &p /\ &p <= Y} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VSUM_CLAUSES; NORM_0] THEN ASM_REAL_ARITH_TAC]]);;

let BILINEAR_SMALL_PART = prove
 (`!C1 A X Y Z (alpha:num->real) s R.
     (!y x q c. &2 <= y /\ x <= y /\ 1 <= q /\ &q <= log y pow A /\
                dirichlet_character q c /\ ~(c = chi_0 q)
                ==> norm(vsum {p | prime p /\ &p <= x} c)
                    <= C1 * y / log y pow (2 * A)) /\
     &0 <= C1 /\ &0 <= X /\ &2 <= Y /\ (!n. abs(alpha n) <= &1) /\
     1 <= s /\ &R <= log Y pow A
     ==> sum(2..R) (\r. inv(&(phi r)) * bilinear_H X Y Z alpha r s)
         <= &R * X * (&2 * C1 * Y / log Y pow (2 * A) + log(&s) / log(&2))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = &2 * C1 * Y / log Y pow (2 * A) + log(&s) / log(&2)` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(2..R) (\r. X * B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `&0 < &(phi r)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
      MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(X * B) * &(CARD {c | primitive_character r c})` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bilinear_H] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum {c | primitive_character r c} (\c. X * B)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS] THEN
        X_GEN_TAC `c:num->complex` THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
         [REWRITE_TAC[bilinear_A] THEN
           MATCH_MP_TAC TWISTED_ALPHA_SUM_BOUND THEN
          ASM_REWRITE_TAC[] THEN GEN_TAC THEN
          FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM
            (CONJUNCT1(GEN_REWRITE_RULE I [primitive_character] th))]) THEN
          COND_CASES_TAC THEN REAL_ARITH_TAC;
          EXPAND_TAC "B" THEN MATCH_MP_TAC BILINEAR_P_SW_BOUND THEN
          ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:num` THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&R` THEN
          ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
        SIMP_TAC[SUM_CONST; FINITE_PRIMITIVE_CHARACTERS] THEN
        REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CARD_PRIMITIVE_CHARACTERS_LE THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC);;

let BILINEAR_INNER_BOUND = prove
 (`!C1 A X Y Z (alpha:num->real) k M.
     (!y x q c. &2 <= y /\ x <= y /\ 1 <= q /\ &q <= log y pow A /\
                dirichlet_character q c /\ ~(c = chi_0 q)
                ==> norm(vsum {p | prime p /\ &p <= x} c)
                    <= C1 * y / log y pow (2 * A)) /\
     &0 <= C1 /\ &0 <= X /\ &2 <= Y /\ (!n. abs(alpha n) <= &1) /\
     1 <= k /\ 1 <= M
     ==> sum(1..M) (\r. if r = 1 then &0
                        else inv(&(phi r)) * bilinear_H X Y Z alpha r k)
         <= log Y pow A * X *
            (&2 * C1 * Y / log Y pow (2 * A) + log(&k) / log(&2)) +
            &4 * X * Y / log Y pow A +
            &12 * (X * sqrt Y + Y * sqrt X) * (&2 + log(&M)) +
            &72 * sqrt X * sqrt Y * &M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log Y pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC LOG_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `log Y pow A` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `R:num`) THEN
  MP_TAC(SPEC `log Y pow A` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `f = \r. inv(&(phi r)) * bilinear_H X Y Z (alpha:num->real) r k` THEN
  SUBGOAL_THEN `!r. &0 <= (f:num->real) r` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[BILINEAR_H_POS; REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..M) (\r. if r = 1 then &0
                   else inv(&(phi r)) * bilinear_H X Y Z alpha r k) =
    sum(2..M) (f:num->real)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_LEFT] THEN REWRITE_TAC[ARITH; REAL_ADD_LID] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C1:real`; `A:num`; `X:real`; `Y:real`; `Z:real`;
                 `alpha:num->real`; `k:num`; `R:num`] BILINEAR_SMALL_PART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= X * (&2 * C1 * Y / log Y pow (2 * A) +
                           log(&k) / log(&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(2..R) (\r. inv(&(phi r)) * bilinear_H X Y Z alpha r k) <=
    log Y pow A * X * (&2 * C1 * Y / log Y pow (2 * A) + log(&k) / log(&2))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&R * X * (&2 * C1 * Y / log Y pow (2 * A) +
                          log(&k) / log(&2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt X /\ &0 <= sqrt Y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * X * Y / log Y pow A /\
                &0 <= &12 * (X * sqrt Y + Y * sqrt X) * (&2 + log(&M)) /\
                &0 <= &72 * sqrt X * sqrt Y * &M`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= log(&M)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `M:num <= R` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(2..R) (f:num->real)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(2..M) (f:num->real) <= sum(2..R) f + sum(R+1..M) f`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum((2..R) UNION (R+1..M)) (f:num->real)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_REWRITE_TAC[FINITE_UNION; FINITE_NUMSEG; SUBSET; IN_UNION;
                      IN_NUMSEG] THEN
      ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_UNION THEN
      REWRITE_TAC[FINITE_NUMSEG; DISJOINT; EXTENSION; IN_INTER; IN_NUMSEG;
                  NOT_IN_EMPTY] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real`; `Y:real`; `Z:real`; `alpha:num->real`; `k:num`;
                 `R + 1:num`; `M:num`] BILINEAR_LARGE_PART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (ASM_REAL_ARITH_TAC ORELSE ASM_ARITH_TAC);
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `&4 * X * Y / &(R + 1) <= &4 * X * Y / log Y pow A`
  MP_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BILINEAR_H_INDUCED = prove
 (`!X Y Z (alpha:num->real) r k.
     bilinear_H X Y Z alpha r (k * r) = bilinear_H X Y Z alpha r k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bilinear_H] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
    [primitive_character]) THEN
  BINOP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[bilinear_A; bilinear_P] THEN MATCH_MP_TAC VSUM_EQ THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[INDUCED_COPRIME_EQ]);;

let BILINEAR_TOTAL_BOUND = prove
 (`!C1 A X Y Z (alpha:num->real) a Dn.
     (!y x q c. &2 <= y /\ x <= y /\ 1 <= q /\ &q <= log y pow A /\
                dirichlet_character q c /\ ~(c = chi_0 q)
                ==> norm(vsum {p | prime p /\ &p <= x} c)
                    <= C1 * y / log y pow (2 * A)) /\
     &0 <= C1 /\ &0 <= X /\ &2 <= Y /\ (!n. abs(alpha n) <= &1) /\
     (!d. coprime(a d,d)) /\ 1 <= Dn
     ==> sum(1..Dn)
          (\d. abs(sum {x | FST x IN {m | 1 <= m /\ &m <= X} /\
                            SND x IN {p | prime p /\ Z < &p /\ &p <= Y} /\
                            (FST x * SND x == a d) (mod d)}
                       (\x. alpha(FST x)) -
                   inv(&(phi d)) *
                   sum {x | FST x IN {m | 1 <= m /\ &m <= X} /\
                            SND x IN {p | prime p /\ Z < &p /\ &p <= Y} /\
                            coprime(FST x * SND x,d)}
                       (\x. alpha(FST x))))
         <= &4 * (&1 + log(&Dn)) *
            (log Y pow A * X *
             (&2 * C1 * Y / log Y pow (2 * A) + log(&Dn) / log(&2)) +
             &4 * X * Y / log Y pow A +
             &12 * (X * sqrt Y + Y * sqrt X) * (&2 + log(&Dn)) +
             &72 * sqrt X * sqrt Y * &Dn)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE {m | 1 <= m /\ &m <= X} /\
    FINITE {p | prime p /\ Z < &p /\ &p <= Y}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `X:real` NUMSEG_REAL_FLOOR) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
      MP_TAC(SPEC `Y:real` NUMSEG_REAL_FLOOR) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..N` THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `1..N`)) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..Dn) (\d. inv(&(phi d)) *
       sum {r | r divides d /\ ~(r = 1)}
           (\r. bilinear_H X Y Z (alpha:num->real) r d))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[bilinear_H; bilinear_A; bilinear_P] THEN
    MATCH_MP_TAC BILINEAR_DISCREPANCY_CHARS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r d. bilinear_H X Y Z (alpha:num->real) r d`; `Dn:num`]
    BILINEAR_REINDEX) THEN
  REWRITE_TAC[BILINEAR_H_POS; BILINEAR_H_INDUCED] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN
   `&0 < log Y /\ &0 < log Y pow A /\ &0 <= log(&Dn) /\ &0 < log(&2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC LOG_POS_LT THEN
        ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt X /\ &0 <= sqrt Y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C1 * Y / log Y pow (2 * A)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Bd = log Y pow A * X *
     (&2 * C1 * Y / log Y pow (2 * A) + log (&Dn) / log (&2)) +
     &4 * X * Y / log Y pow A +
     &12 * (X * sqrt Y + Y * sqrt X) * (&2 + log (&Dn)) +
     &72 * sqrt X * sqrt Y * &Dn` THEN
  SUBGOAL_THEN `&0 <= Bd` ASSUME_TAC THENL
   [EXPAND_TAC "Bd" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Dn) (\k. inv(&(phi k)) * Bd)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_RMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SUM_INV_PHI_LE]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  SUBGOAL_THEN `1 <= Dn DIV k /\ Dn DIV k <= Dn` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= k ==> ~(k = 0)`; MULT_CLAUSES;
    DIV_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C1:real`; `A:num`; `X:real`; `Y:real`; `Z:real`;
                 `alpha:num->real`; `k:num`;
                  `Dn DIV k`] BILINEAR_INNER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  EXPAND_TAC "Bd" THEN
  SUBGOAL_THEN
   `log(&k) <= log(&Dn) /\ log(&(Dn DIV k)) <= log(&Dn) /\
    &(Dn DIV k) <= &Dn`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LOG_MONO_LE_IMP) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= a' /\ c <= c' /\ d <= d'
    ==> a + b + c + d <= a' + b + c' + d':real`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> a + x <= a + y:real`) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[]]);;

let BILINEAR_FINAL_ARITH = prove
 (`!A C1 X Y Dn.
     &0 <= C1 /\ &1 <= X /\ &2 <= Y /\ log Y pow (2 * A) <= X /\ 1 <= Dn /\
     &Dn <= sqrt(X * Y) / log Y pow A
     ==> &4 * (&1 + log(&Dn)) *
         (log Y pow A * X *
          (&2 * C1 * Y / log Y pow (2 * A) + log(&Dn) / log(&2)) +
          &4 * X * Y / log Y pow A +
          &12 * (X * sqrt Y + Y * sqrt X) * (&2 + log(&Dn)) +
          &72 * sqrt X * sqrt Y * &Dn)
         <= (&4 * (&3 + &2 * &A) *
             (&4 * C1 + &152 + &2 * (&4 * &A) pow (2 * A) * (&1 + &2 * &A) +
              &12 * ((&2 * &A) pow A + &1) * (&5 + &2 * &A))) *
            X * Y * log(X * Y) pow 2 / log Y pow A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= log Y /\ &1 / &2 <= log(X * Y)` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&2)` THEN
    REWRITE_TAC[LOG_2_BOUNDS] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
    MP_TAC(SPECL [`&1`; `X:real`; `&2`; `Y:real`] REAL_LE_MUL2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`X:real`; `Y:real`; `A:num`; `log Y`] SQRT_DIV_POW_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`A:num`; `Y:real`] LOG_POW_LE_SQRT) THEN
  MP_TAC(SPECL [`2 * A`; `Y:real`] LOG_POW_LE_SQRT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `L = log(X * Y)` THEN
  ABBREV_TAC `a = log Y pow A` THEN
  SUBGOAL_THEN `log Y pow (2 * A) = (a:real) pow 2`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[REAL_POW_POW] THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &(2 * A) = &4 * &A`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `P1 = (&2 * &A) pow A` THEN
  ABBREV_TAC `P2 = (&4 * &A) pow (2 * A)` THEN
  SUBGOAL_THEN `&0 <= P1 /\ &0 <= P2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P1"; "P2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a:real)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(X * Y) = sqrt X * sqrt Y` SUBST_ALL_TAC THENL
   [REWRITE_TAC[SQRT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= sqrt X /\ &1 <= sqrt Y /\ sqrt X pow 2 = X /\ sqrt Y pow 2 = Y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `sx = sqrt X` THEN ABBREV_TAC `sy = sqrt Y` THEN
  ABBREV_TAC `G = log(&Dn)` THEN ABBREV_TAC `D0 = &Dn` THEN
  SUBGOAL_THEN `&0 <= G /\ G <= L + &A` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "D0"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `log(((X:real) * Y) * &2 pow A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((sx:real) * sy) / a` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (X:real) * Y /\ &0 < &2 pow A` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
                      MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_ARITH `&0 < &2`] THEN
    MP_TAC LOG_2_BOUNDS THEN
    SUBGOAL_THEN `&A * log(&2) <= &A * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; LOG_2_BOUNDS];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `W = ((X:real) * Y) / a` THEN
  SUBGOAL_THEN `&0 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC REAL_LE_DIV THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a * X * (&2 * C1 * Y / a pow 2 + G / log(&2)) =
                &2 * C1 * W + (a * X) * (G / log(&2))` SUBST1_TAC THENL
   [EXPAND_TAC "W" THEN UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * X * Y / a = &4 * W` SUBST1_TAC THENL
   [EXPAND_TAC "W" THEN UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sy:real) <= Y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sy:real) pow 2` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real) * W = X * Y` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t c. (a:real) * t <= c * (X * Y) ==> t <= c * W`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(a:real) * t <= a * (c * W)` MP_TAC THENL
     [SUBGOAL_THEN `(a:real) * (c * W) = c * (a * W)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real) <= sx` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real) * X <= P2 * W` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `W:real`)) (concl th))) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(P2 * Y) * X:real` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `P2 * sy:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `X * sy <= P1 * W:real` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `W:real`)) (concl th))) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(P1 * sy) * X * sy:real` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(P1 * sy) * X * sy = P1 * X * (sy:real) pow 2`
      SUBST1_TAC THENL
       [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y * sx <= &1 * W:real` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `W:real`)) (concl th))) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sx * Y * sx:real` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `sx * Y * sx = Y * (sx:real) pow 2` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sx * sy * D0 <= &1 * W:real` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `W:real`)) (concl th))) THEN
    SUBGOAL_THEN `a * D0 <= sx * sy:real` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        concl th = `D0 <= ((sx:real) * sy) / a`)) THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(sx * sy) * (sx * sy):real` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `a * sx * sy * D0 = (sx * sy) * (a * D0):real`
      SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(sx * sy) * (sx * sy) = (sx:real) pow 2 * sy pow 2`
      SUBST1_TAC THENL
       [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `K' = &4 * C1 + &152 + &2 * P2 * (&1 + &2 * &A) +
                   &12 * (P1 + &1) * (&5 + &2 * &A)` THEN
  ABBREV_TAC `Bd = (&2 * C1 * W + (a * X) * (G / log(&2))) + &4 * W +
                   &12 * (X * sy + Y * sx) * (&2 + G) +
                   &72 * sx * sy * D0` THEN
  SUBGOAL_THEN `&0 <= Bd` ASSUME_TAC THENL
   [EXPAND_TAC "Bd" THEN
    SUBGOAL_THEN `&0 <= a * X /\ &0 <= G / log(&2) /\ &0 <= X * sy + Y * sx /\
                  &0 <= sx * sy * D0` MP_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LE_DIV) THEN TRY(MATCH_MP_TAC REAL_LE_ADD) THEN
      REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      MP_TAC LOG_2_BOUNDS THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= C1 * W /\ &0 <= (a * X) * (G / log(&2)) /\
                  &0 <= (X * sy + Y * sx) * (&2 + G)` MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &2 * L /\ &A <= &2 * &A * L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&A`; `&1`; `&2 * L`] REAL_LE_LMUL) THEN
    REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `G <= (&1 + &2 * &A) * L` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Bd <= K' * W * L` ASSUME_TAC THENL
   [EXPAND_TAC "Bd" THEN EXPAND_TAC "K'" THEN
    SUBGOAL_THEN `(a * X) * (G / log(&2)) <= (P2 * W) * (&2 * G)` ASSUME_TAC
    THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= G * (&2 * log(&2) - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC LOG_2_BOUNDS THEN
       ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(X * sy + Y * sx) * (&2 + G) <= ((P1 + &1) * W) * (&2 + G)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(P2 * W) * G <= (P2 * W) * ((&1 + &2 * &A) * L)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((P1 + &1) * W) * (&2 + G) <=
      ((P1 + &1) * W) * ((&5 + &2 * &A) * L)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `W * &1 <= W * (&2 * L) /\ (C1 * W) * &1 <= (C1 * W) * (&2 * L)`
  STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + G <= (&3 + &2 * &A) * L` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * (&3 + &2 * &A) * K') * X * Y * L pow 2 / a =
                &4 * ((&3 + &2 * &A) * L) * (K' * W * L)` SUBST1_TAC THENL
   [EXPAND_TAC "W" THEN UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let BILINEAR_BV = prove
 (`!A. ?C. !X Y Z (alpha:num->real) a.
        &2 <= Y /\ (!n. abs(alpha n) <= &1) /\
        log Y pow (2 * A) <= X /\ (!d. coprime(a d,d))
        ==> sum {d | 1 <= d /\ &d <= sqrt(X * Y) / log Y pow A}
              (\d. abs(sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                       prime(SND x) /\ Z < &(SND x) /\
                                       &(SND x) <= Y /\
                                       (FST x * SND x == a d) (mod d)}
                           (\x. alpha(FST x)) -
                       inv(&(phi d)) *
                       sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                       prime(SND x) /\ Z < &(SND x) /\
                                       &(SND x) <= Y /\
                                       coprime(FST x * SND x,d)}
                           (\x. alpha(FST x))))
            <= C * X * Y * log(X * Y) pow 2 / log Y pow A`,
  X_GEN_TAC `A:num` THEN
  MP_TAC(SPECL [`2 * A`; `A:num`] SW_UNIFORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `&4 * (&3 + &2 * &A) *
    (&4 * C1 + &152 + &2 * (&4 * &A) pow (2 * A) * (&1 + &2 * &A) +
     &12 * ((&2 * &A) pow A + &1) * (&5 + &2 * &A))` THEN
  MAP_EVERY X_GEN_TAC [`X:real`; `Y:real`; `Z:real`; `alpha:num->real`;
                       `a:num->num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log Y pow A /\ &0 <= X` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC LOG_POS_LT THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log Y pow (2 * A)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&4 * (&3 + &2 * &A) *
           (&4 * C1 + &152 + &2 * (&4 * &A) pow (2 * A) * (&1 + &2 * &A) +
            &12 * ((&2 * &A) pow A + &1) * (&5 + &2 * &A))) *
          X * Y * log(X * Y) pow 2 / log Y pow A`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
      ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
       ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
            [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= X` THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_0 THEN
    X_GEN_TAC `d:num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `!P. {x:num#num | 1 <= FST x /\ &(FST x) <= X /\ prime(SND x) /\
                       Z < &(SND x) /\ &(SND x) <= Y /\ P x} = {}`
    (fun th -> REWRITE_TAC[th; SUM_CLAUSES; REAL_MUL_RZERO; REAL_SUB_REFL;
                           REAL_ABS_NUM]) THEN
    GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:num#num` THEN
    ASM_CASES_TAC `1 <= FST(x:num#num)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= &(FST(x:num#num))` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ASM_REAL_ARITH_TAC]] THEN
  ABBREV_TAC `D = sqrt(X * Y) / log Y pow A` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `D:real` NUMSEG_REAL_FLOOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Dn:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `Dn = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. {x:num#num | 1 <= FST x /\ &(FST x) <= X /\ prime(SND x) /\
                     Z < &(SND x) /\ &(SND x) <= Y /\ P x} =
        {x | FST x IN {m | 1 <= m /\ &m <= X} /\
             SND x IN {p | prime p /\ Z < &p /\ &p <= Y} /\ P x}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`C1:real`; `A:num`; `X:real`; `Y:real`; `Z:real`;
                 `alpha:num->real`; `a:num->num`; `Dn:num`]
    BILINEAR_TOTAL_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (ASM_REAL_ARITH_TAC ORELSE ASM_ARITH_TAC);
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC BILINEAR_FINAL_ARITH THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;
