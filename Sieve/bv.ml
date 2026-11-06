(* ========================================================================= *)
(* The Bombieri-Vinogradov theorem from Siegel-Walfisz.                      *)
(*                                                                           *)
(* BOMBIERI_VINOGRADOV (from SIEGEL_WALFISZ, sw.ml): for every A there are   *)
(* B, C such that for x >= 2 and residues a(d) coprime to d                  *)
(*   sum_{d <= sqrt x / log^B x} |pi(x;d,a(d)) - pi(x)/phi(d)|               *)
(*     <= C x / log^A x,                                                     *)
(* pi(x) = pi_upto x and pi(x;d,a) = pi_ap x d a the prime counts.           *)
(*                                                                           *)
(* Method: no integrals, no Polya-Vinogradov inequality                      *)
(* and no maximal large sieve; all parameters are powers of L = log x.       *)
(* (1) Residue classes -> characters -> primitive characters (BV_AP_TOTAL):  *)
(*     the sum is <= 4 (1 + log D) Ss |pi(x,chi)| + 2 D^2 log D / log 2,     *)
(*     Ss f = sum_{2 <= r <= D} phi(r)^-1 sum_{chi primitive mod r} f(chi)   *)
(*     (bv_sum).                                                             *)
(* (2) Moduli r <= R0: Siegel-Walfisz (BV_SMALL_PART).                       *)
(* (3) pi -> theta by summation by parts; the weights telescope, so the      *)
(*     sum over characters is taken before the max over n <= x               *)
(*     (PI_THETA_WEIGHTED); theta -> psi via prime powers (THETA_PSI_BV).    *)
(* (4) Vaughan's identity (vaughan.ml).  Type I: |sum_{k<=K} chi(k)| <= r    *)
(*     (VAUGHAN_S1_BOUND, _S2_, _S3_).  Type II: the sum over U < m <= N is  *)
(*     cut along the grid U (1 + delta)^j (bv_grid) into boxes plus a term   *)
(*     supported on (N/(1 + delta), N] (TYPE2_SPLIT); the large sieve with   *)
(*     general l2 norms (LARGE_SIEVE_BILINEAR_L2, LARGE_SIEVE_LINEAR_L2) and *)
(*     the l2 bounds for tau_le give cumulative bounds c0 + c1 k + c2 k^2,   *)
(*     summed by parts over R0 < r <= D (TYPE2_TOTAL, BV_PSI_BOUND).         *)
(* (5) Parameters M = L^(A+1), delta = M^-10, U = V = M^22, R0 = [M^10],     *)
(*     D = [sqrt x / M^23] (BV_PSI_ARITH, BV_LARGE_PART, BV_FINAL_ARITH);    *)
(*     x < 8 is trivial (BV_SMALL_X).                                        *)
(* ========================================================================= *)

needs "Sieve/bilinear.ml";;
needs "Sieve/vaughan.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Weighted sums over primitive characters.                                  *)
(* ------------------------------------------------------------------------- *)

let bv_sum = new_definition
 `bv_sum a b (f:(num->complex)->real) =
    sum(a..b) (\r. inv(&(phi r)) * sum {c | primitive_character r c} f)`;;

let BV_SUM_LE = prove
 (`!a b f g. (!r c. a <= r /\ r <= b /\ primitive_character r c
                    ==> f c <= g c)
             ==> bv_sum a b f <= bv_sum a b g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_sum] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let BV_SUM_ADD = prove
 (`!a b f g. bv_sum a b (\c. f c + g c) = bv_sum a b f + bv_sum a b g`,
  REWRITE_TAC[bv_sum; GSYM SUM_ADD_NUMSEG; GSYM REAL_ADD_LDISTRIB] THEN
  SIMP_TAC[SUM_ADD; FINITE_PRIMITIVE_CHARACTERS]);;

let BV_SUM_LMUL = prove
 (`!a b k f. bv_sum a b (\c. k * f c) = k * bv_sum a b f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bv_sum; SUM_LMUL] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(a..b) (\r. k * inv(&(phi r)) *
                sum {c | primitive_character r c} f)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_MUL_AC];
    REWRITE_TAC[SUM_LMUL]]);;

let BV_SUM_SUM = prove
 (`!a b s (f:A->(num->complex)->real).
     FINITE s
     ==> bv_sum a b (\c. sum s (\i. f i c)) = sum s (\i. bv_sum a b (f i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_sum] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(a..b) (\r. sum s (\i. inv(&(phi r)) *
     sum {c | primitive_character r c} ((f:A->(num->complex)->real) i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\c:num->complex i:A. (f:A->(num->complex)->real) i c`;
                   `{c | primitive_character r c}`; `s:A->bool`] SUM_SWAP) THEN
    ASM_REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; ETA_AX];
    MP_TAC(ISPECL [`\r:num i:A. inv(&(phi r)) *
                     sum {c | primitive_character r c}
                         ((f:A->(num->complex)->real) i)`;
                   `a..b`; `s:A->bool`] SUM_SWAP) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG]]);;

let BV_SUM_CONST_LE = prove
 (`!a b z. 1 <= a /\ &0 <= z ==> bv_sum a b (\c. z) <= &b * z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_sum] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..b) (\r. z)` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(a..b) (\r. z)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SIMP_TAC[SUM_CONST; FINITE_PRIMITIVE_CHARACTERS] THEN
    ASM_CASES_TAC `r = 0` THENL
     [ASM_REWRITE_TAC[PHI_0; REAL_INV_0; REAL_MUL_LZERO] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &(phi r)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
      MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    MATCH_MP_TAC CARD_PRIMITIVE_CHARACTERS_LE THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC]);;

let BV_SUM_SPLIT_LE = prove
 (`!a m b (f:(num->complex)->real).
     a <= m + 1 /\ (!c. &0 <= f c)
     ==> bv_sum a b f <= bv_sum a m f + bv_sum (m + 1) b f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_sum] THEN
  SUBGOAL_THEN `!r. &0 <= inv(&(phi r)) * sum {c | primitive_character r c} f`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS];
    ALL_TAC] THEN
  ASM_CASES_TAC `m <= b:num` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` SUBST1_TAC o
      GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    ASM_SIMP_TAC[SUM_ADD_SPLIT; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(m + 1..b) (\r. inv(&(phi r)) *
                  sum {c | primitive_character r c} f) = &0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Partial sums of primitive characters.                                     *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_PARTIAL_SUM_BOUND = prove
 (`!r c K. 2 <= r /\ primitive_character r c ==> norm(vsum(1..K) c) <= &r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dirichlet_character r c /\ ~(c = chi_0 r)` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[primitive_character];
      MATCH_MP_TAC PRIMITIVE_CHARACTER_NONPRINCIPAL THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC
   [MATCH_MP DIRICHLET_CHARACTER_SUM_MOD (CONJ th (ASSUME `~(c = chi_0 r)`))])
  THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..K MOD r) (\n. &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC]);;

let PRIMITIVE_LOG_SUM_BOUND = prove
 (`!r c H. 2 <= r /\ primitive_character r c
           ==> norm(vsum(1..H) (\h. Cx(log(&h)) * c h))
               <= &2 * &r * log(&H + &1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `H = 0` THENL
   [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `~(1 = 0)`; NORM_0] THEN
    REWRITE_TAC[REAL_ADD_LID; LOG_1; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. log(&k)`; `\k. vsum(1..k-1) (c:num->complex)`;
                 `1`; `H:num`] VSUM_PARTIAL_SUC) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= H <=> ~(H = 0)`; ADD_SUB] THEN
  REWRITE_TAC[SUB_REFL; LOG_1; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN
   `vsum(1..H) (\k. log(&k) % (vsum(1..k) c - vsum(1..k - 1) c)) =
    vsum(1..H) (\h. Cx(log(&h)) * (c:num->complex) h)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_CMUL] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[VSUM_CLAUSES_RIGHT; ARITH_RULE `1 <= k ==> 0 < k`] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `log(&(H + 1)) * &r +
              sum(1..H) (\k. (log(&(k + 1)) - log(&k)) * &r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(x:complex) <= a /\ norm(y:complex) <= b
      ==> norm(x - y) <= a + b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; PRIMITIVE_PARTIAL_SUM_BOUND] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x <= x`) THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; PRIMITIVE_PARTIAL_SUM_BOUND] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> abs(y - x) <= y - x`) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    REWRITE_TAC[SUM_RMUL; SUM_DIFFS_ALT] THEN
    REWRITE_TAC[ARITH_RULE `1 <= H <=> ~(H = 0)`] THEN
    ASM_REWRITE_TAC[LOG_1; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Type I sums.                                                              *)
(* ------------------------------------------------------------------------- *)

let VAUGHAN_S1_BOUND = prove
 (`!U N (c:num->complex).
     &1 <= U /\ (!n. norm(c n) <= &1)
     ==> norm(vsum(1..N) (\n. Cx(vaughan_F U n) * c n)) <= &18 * U`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\n. vaughan_F U n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS;
     NORM_POS_LE] THEN
    REWRITE_TAC[vaughan_F] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_LE_REFL] THEN
    REWRITE_TAC[real_abs; MANGOLDT_POS_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(SPEC `U:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MP_TAC(SPEC `U:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..M) (\d. mangoldt d)` THEN CONJ_TAC THENL
   [REWRITE_TAC[vaughan_F] THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET; ETA_AX] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; MANGOLDT_POS_LE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&n < &M + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&18 * &M` THEN
    REWRITE_TAC[PSI_BOUND] THEN ASM_REAL_ARITH_TAC]);;

let VAUGHAN_S2_BOUND = prove
 (`!U V N r (c:num->complex).
     &1 <= U /\ &1 <= V /\ 2 <= r /\ primitive_character r c
     ==> norm(vsum(1..N)
                (\s. Cx(dirichlet_conv (vaughan_G V) (vaughan_F U) s) * c s *
                              vsum(1..N DIV s) c))
         <= &2 * &r * U * V * log(U * V)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= U * V` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(U * V)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\s. if &s <= U * V then log(U * V) * &r else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN COND_CASES_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[VAUGHAN_C_ZERO; GSYM REAL_NOT_LE; COMPLEX_MUL_LZERO;
                   COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_LE_REFL]] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&s)` THEN
      ASM_SIMP_TAC[VAUGHAN_C_BOUND; ARITH_RULE `1 <= s ==> ~(s = 0)`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_SIMP_TAC[PRIMITIVE_PARTIAL_SUM_BOUND] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE; primitive_character];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(U * V + &1) * log(U * V) * &r` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {t | &0 < (&t:real) /\ &t <= U * V})` THEN
      CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[FINITE_NUM_INTERVAL] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG; REAL_OF_NUM_LT] THEN
      ARITH_TAC;
      MP_TAC(SPECL [`&0:real`; `U * V:real`] CARD_REAL_INTERVAL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y - &0 + &1 ==> x <= y + &1:real`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    SUBGOAL_THEN `&2 * &r * U * V * log(U * V) =
                  (&2 * (U * V)) * (log(U * V) * &r)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]]]);;

let VAUGHAN_S3_BOUND = prove
 (`!V N r (c:num->complex).
     &1 <= V /\ 2 <= r /\ primitive_character r c
     ==> norm(vsum(1..N) (\d. Cx(vaughan_G V d) * c d *
                              vsum(1..N DIV d) (\h. Cx(log(&h)) * c h)))
         <= &4 * &r * V * log(&N + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log(&N + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_LE_ADDL; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\d. if &d <= V then &2 * &r * log(&N + &1)
                             else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[vaughan_G] THEN
    COND_CASES_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_NORM_CX; REAL_ABS_NUM;
                  REAL_LE_REFL]] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MOBIUS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE; primitive_character];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * &r * log(&(N DIV d) + &1)` THEN
    ASM_SIMP_TAC[PRIMITIVE_LOG_SUM_BOUND] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE; DIV_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(V + &1) * &2 * &r * log(&N + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {t | &0 < (&t:real) /\ &t <= V})` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[FINITE_NUM_INTERVAL] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG; REAL_OF_NUM_LT] THEN
      ARITH_TAC;
      MP_TAC(SPECL [`&0:real`; `V:real`] CARD_REAL_INTERVAL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y - &0 + &1 ==> x <= y + &1:real`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    SUBGOAL_THEN `&4 * &r * V * log(&N + &1) =
                  (&2 * V) * (&2 * &r * log(&N + &1))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS]]]);;

(* ------------------------------------------------------------------------- *)
(* The large sieve with general l2 norms.                                    *)
(* ------------------------------------------------------------------------- *)

let LARGE_SIEVE_BILINEAR_L2 = prove
 (`!N1 N2 (a:num->complex) (b:num->complex) k.
     1 <= k
     ==> sum(1..k) (\r. &r / &(phi r) *
                       sum {c | primitive_character r c}
                           (\c. norm(vsum(1..N1) (\n. a n * c n)) *
                                norm(vsum(1..N2) (\n. b n * c n))))
         <= sqrt((&4 * &N1 + &36 * &k pow 2) *
                 sum(1..N1) (\n. norm(a n) pow 2)) *
            sqrt((&4 * &N2 + &36 * &k pow 2) *
                 sum(1..N2) (\n. norm(b n) pow 2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SQRT_AMGM THEN
  SUBGOAL_THEN
   `!N (a:num->complex).
      &0 <= (&4 * &N + &36 * &k pow 2) * sum(1..N) (\n. norm(a n) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  X_GEN_TAC `l:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `N1:num`; `a:num->complex`]
    LARGE_SIEVE_MULTIPLICATIVE) THEN
  MP_TAC(SPECL [`k:num`; `N2:num`; `b:num->complex`]
    LARGE_SIEVE_MULTIPLICATIVE) THEN
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
  SUBGOAL_THEN `l * SA <= l * c1 * TA /\ inv l * SB <= inv l * c2 * TB`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let LARGE_SIEVE_LINEAR_L2 = prove
 (`!N (a:num->complex) k.
     1 <= k
     ==> sum(1..k) (\r. &r / &(phi r) *
                       sum {c | primitive_character r c}
                           (\c. norm(vsum(1..N) (\n. a n * c n))))
         <= &8 * &k * sqrt((&4 * &N + &36 * &k pow 2) *
                           sum(1..N) (\n. norm(a n) pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `1`; `a:num->complex`; `\n:num. Cx(&1)`; `k:num`]
    LARGE_SIEVE_BILINEAR_L2) THEN
  ASM_REWRITE_TAC[NUMSEG_SING; VSUM_SING; SUM_SING; COMPLEX_MUL_LID;
                  COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = y /\ s * t <= &8 * &k * s ==> y <= s * t ==> x <= &8 * &k * s`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `c:num->complex` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:num->complex) 1 = Cx(&1)` SUBST1_TAC THENL
     [MATCH_MP_TAC DIRICHLET_CHARACTER_EQ_1 THEN EXISTS_TAC `r:num` THEN
      ASM_MESON_TAC[primitive_character];
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_MUL_RID]];
    ONCE_REWRITE_TAC[REAL_ARITH `&8 * &k * s = s * &8 * &k:real`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
        MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2]];
      MATCH_MP_TAC REAL_LE_LSQRT THEN
      CONJ_TAC THENL [SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= &k` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      SPEC_TAC(`&k:real`,`x:real`) THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `&1 <= x pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* The geometric grid U (1 + d)^j.                                           *)
(* ------------------------------------------------------------------------- *)

let bv_grid = new_definition
 `bv_grid U d j = U * (&1 + d) pow j`;;

let bv_grid_j = new_definition
 `bv_grid_j U d m = @j. bv_grid U d j < &m /\ &m <= bv_grid U d (j + 1)`;;

let bv_grid_K = new_definition
 `bv_grid_K N U d j =
    @K. &K <= &N / bv_grid U d (j + 1) /\ &N / bv_grid U d (j + 1) < &K + &1`;;

let BV_GRID_POS = prove
 (`!U d j. &0 < U /\ &0 < d ==> &0 < bv_grid U d j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_grid] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC);;

let BV_GRID_SUC = prove
 (`!U d j. bv_grid U d (j + 1) = (&1 + d) * bv_grid U d j`,
  REWRITE_TAC[bv_grid; GSYM ADD1; real_pow] THEN REAL_ARITH_TAC);;

let BV_GRID_MONO_LE = prove
 (`!U d i j. &0 < U /\ &0 < d /\ i <= j ==> bv_grid U d i <= bv_grid U d j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_grid] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]);;

let BV_GRID_UNBOUNDED = prove
 (`!U d y. &0 < U /\ &0 < d ==> ?j. y <= bv_grid U d j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(y:real) / (U * d)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN EXISTS_TAC `j:num` THEN
  REWRITE_TAC[bv_grid] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `U * (&1 + &j * d)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < U * d` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    UNDISCH_TAC `y / (U * d) <= &j` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= U` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LBOUND THEN ASM_REAL_ARITH_TAC]]);;

let BV_GRID_J = prove
 (`!U d m. &0 < U /\ &0 < d /\ U < &m
           ==> bv_grid U d (bv_grid_j U d m) < &m /\
               &m <= bv_grid U d (bv_grid_j U d m + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bv_grid_j] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(SPECL [`U:real`; `d:real`; `&m:real`] BV_GRID_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `i = 0` THENL
   [UNDISCH_TAC `&m <= bv_grid U d i` THEN ASM_REWRITE_TAC[bv_grid] THEN
    REWRITE_TAC[real_pow; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `i - 1` THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> i - 1 + 1 = i`] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

let BV_GRID_J_UNIQUE = prove
 (`!U d m j. &0 < U /\ &0 < d /\ U < &m
             ==> (bv_grid U d j < &m /\ &m <= bv_grid U d (j + 1) <=>
                  j = bv_grid_j U d m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`U:real`; `d:real`; `m:num`] BV_GRID_J) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `i = bv_grid_j U d m` THEN STRIP_TAC THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `j = i <=> ~(j + 1 <= i) /\ ~(i + 1 <= j)`] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`U:real`; `d:real`; `j + 1`; `i:num`] BV_GRID_MONO_LE);
    MP_TAC(SPECL [`U:real`; `d:real`; `i + 1`; `j:num`] BV_GRID_MONO_LE)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let BV_GRID_K = prove
 (`!N U d j. &0 < U /\ &0 < d
             ==> &(bv_grid_K N U d j) <= &N / bv_grid U d (j + 1) /\
                 &N / bv_grid U d (j + 1) < &(bv_grid_K N U d j) + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bv_grid_K] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(SPEC `&N / bv_grid U d (j + 1)` FLOOR_POS) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[BV_GRID_POS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN EXISTS_TAC `K0:num` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FLOOR]);;

let BV_GRID_K_DIV = prove
 (`!N U d j m. &0 < U /\ &0 < d /\ 1 <= m /\ &m <= bv_grid U d (j + 1)
               ==> bv_grid_K N U d j <= N DIV m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `U:real`; `d:real`; `j:num`] BV_GRID_K) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= m ==> ~(m = 0)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&0 < bv_grid U d (j + 1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BV_GRID_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `bv_grid U d (j + 1) * &(bv_grid_K N U d j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]]);;

let BV_GRID_COVER = prove
 (`!U d x J. &1 <= U /\ &0 < d /\ d <= &1 /\ &0 < x /\ &2 * log x <= &J * d
             ==> x <= bv_grid U d J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_grid] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + d) pow J` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(d / &2) pow J` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < x`))] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MP_TAC(SPEC `d / &2` REAL_EXP_BOUND_LEMMA) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Type II: dissection into boxes and a boundary term.                       *)
(* ------------------------------------------------------------------------- *)

let bv_A = new_definition
 `bv_A N U d j (c:num->complex) =
    vsum(1..N) (\m. Cx(if bv_grid U d j < &m /\ &m <= bv_grid U d (j + 1)
                       then mangoldt m else &0) * c m)`;;

let bv_B = new_definition
 `bv_B V (c:num->complex) K = vsum(1..K) (\k. Cx(vaughan_e V k) * c k)`;;

let bv_g = new_definition
 `bv_g N U V d n =
    sum {e | e divides n}
        (\e. (mangoldt e - vaughan_F U e) * vaughan_e V (n DIV e) *
             (if bv_grid_K N U d (bv_grid_j U d e) <
              n DIV e then &1 else &0))`;;

let VAUGHAN_F_LARGE = prove
 (`!U m. U < &m ==> mangoldt m - vaughan_F U m = mangoldt m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vaughan_F] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let VAUGHAN_F_SMALL = prove
 (`!U m. &m <= U ==> mangoldt m - vaughan_F U m = &0`,
  SIMP_TAC[vaughan_F; REAL_SUB_REFL]);;

let TYPE2_BOX = prove
 (`!N U V d J (c:num->complex).
     &0 < U /\ &0 < d /\ &N <= bv_grid U d J
     ==> vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) * c m *
                         bv_B V c (bv_grid_K N U d (bv_grid_j U d m))) =
         vsum(0..J) (\j. bv_A N U d j c * bv_B V c (bv_grid_K N U d j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_A] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o rand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN ASM_CASES_TAC `&m <= U` THENL
   [ASM_SIMP_TAC[VAUGHAN_F_SMALL; COMPLEX_MUL_LZERO] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(bv_grid U d j < &m)` (fun th ->
      REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `U:real` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[bv_grid] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  ASM_SIMP_TAC[VAUGHAN_F_LARGE] THEN
  MP_TAC(SPECL [`U:real`; `d:real`; `m:num`] BV_GRID_J_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(0..J) (\j'. if j' = bv_grid_j U d m
                               then (Cx(mangoldt m) * c m) *
                                    bv_B V c
                                      (bv_grid_K N U d (bv_grid_j U d m))
                               else vec 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_VEC_0];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_DELTA; IN_NUMSEG; LE_0; COMPLEX_MUL_ASSOC] THEN
  SUBGOAL_THEN `bv_grid_j U d m <= J` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`U:real`; `d:real`; `m:num`] BV_GRID_J) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`U:real`; `d:real`; `J:num`; `bv_grid_j U d m`]
    BV_GRID_MONO_LE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&m <= &N` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let VSUM_TAIL_INDICATOR = prove
 (`!(f:num->complex) a b.
     a <= b
     ==> vsum(1..b) f - vsum(1..a) f =
         vsum(1..b) (\k. if a < k then f k else Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= a + 1`] THEN
  MATCH_MP_TAC(VECTOR_ARITH `x = vec 0 /\ y:complex = z
                             ==> (w + y) - w = x + z`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let TYPE2_DELTA = prove
 (`!N U V d (c:num->complex).
     &0 < U /\ &0 < d /\ (!m n. c(m * n) = c m * c n)
     ==> vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) * c m *
                         (bv_B V c (N DIV m) -
                          bv_B V c (bv_grid_K N U d (bv_grid_j U d m)))) =
         vsum(1..N) (\n. Cx(bv_g N U V d n) * c n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum(1..N) (\m. vsum(1..N DIV m) (\k.
      Cx((mangoldt m - vaughan_F U m) * vaughan_e V k *
         (if bv_grid_K N U d (bv_grid_j U d m) < k then &1 else &0)) *
      ((c:num->complex) m * c k)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `&m <= U` THENL
     [ASM_SIMP_TAC[VAUGHAN_F_SMALL; REAL_MUL_LZERO; COMPLEX_MUL_LZERO] THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(SPECL [`U:real`; `d:real`; `m:num`] BV_GRID_J) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `bv_grid_K N U d (bv_grid_j U d m) <= N DIV m`
    ASSUME_TAC THENL
     [MATCH_MP_TAC BV_GRID_K_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[bv_B; VSUM_TAIL_INDICATOR] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; COMPLEX_MUL_RZERO;
                COMPLEX_MUL_LZERO; CX_MUL] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum(1..N) (\n. vsum {e | e divides n} (\e.
      Cx((mangoldt e - vaughan_F U e) * vaughan_e V (n DIV e) *
         (if bv_grid_K N U d (bv_grid_j U d e) < n DIV e then &1 else &0)) *
      ((c:num->complex) e * c (n DIV e))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT; LE_1;
                 ARITH_RULE `1 <= m ==> ~(m = 0)`];
    ALL_TAC] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[bv_g] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VSUM_CX] THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_DIVISORS] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  UNDISCH_TAC `e divides n` THEN REWRITE_TAC[DIVIDES_DIV_MULT] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM th]) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_SYM]);;

let TYPE2_SPLIT = prove
 (`!N U V d J (c:num->complex).
     &0 < U /\ &0 < d /\ &N <= bv_grid U d J /\ (!m n. c(m * n) = c m * c n)
     ==> vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) * c m *
                         vsum(1..N DIV m) (\k. Cx(vaughan_e V k) * c k)) =
         vsum(0..J) (\j. bv_A N U d j c * bv_B V c (bv_grid_K N U d j)) +
         vsum(1..N) (\n. Cx(bv_g N U V d n) * c n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `U:real`; `V:real`; `d:real`; `J:num`;
                `c:num->complex`] TYPE2_BOX) THEN
  MP_TAC(SPECL [`N:num`; `U:real`; `V:real`; `d:real`; `c:num->complex`]
    TYPE2_DELTA) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[bv_B] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Type II: coefficient bounds.                                              *)
(* ------------------------------------------------------------------------- *)

let BV_G_BOUND = prove
 (`!N U V d n. &1 <= V /\ ~(n = 0)
               ==> abs(bv_g N U V d n) <= &(tau_le V n) * log(&n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_g] THEN
  ASM_SIMP_TAC[LOG_MANGOLDT_SUM; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
  X_GEN_TAC `e:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mangoldt e * (&(tau_le V n) * &1)` THEN CONJ_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS];
    REWRITE_TAC[vaughan_F] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO; REAL_ABS_NUM;
                MANGOLDT_POS_LE] THEN
    REWRITE_TAC[real_abs; MANGOLDT_POS_LE; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(tau_le V (n DIV e))` THEN
    ASM_SIMP_TAC[VAUGHAN_E_BOUND; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC TAU_LE_DIVIDES_MONO THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`e:num`; `n:num`] DIVISOR_NONZERO) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `e divides n` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN EXISTS_TAC `e:num` THEN
    REWRITE_TAC[MULT_SYM];
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NUM] THEN REAL_ARITH_TAC]);;

let BV_G_SUPPORT = prove
 (`!N U V d n. &0 < U /\ &0 < d /\ &n <= &N / (&1 + d)
               ==> bv_g N U V d n = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_g] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `&e <= U` THENL
   [ASM_SIMP_TAC[VAUGHAN_F_SMALL; REAL_MUL_LZERO]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  MP_TAC(SPECL [`U:real`; `d:real`; `e:num`] BV_GRID_J) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `j = bv_grid_j U d e` THEN
  MP_TAC(SPECL [`N:num`; `U:real`; `d:real`; `j:num`] BV_GRID_K) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < bv_grid U d j` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BV_GRID_POS]; ALL_TAC] THEN
  MP_TAC(ASSUME `&n <= &N / (&1 + d)`) THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
  SUBGOAL_THEN `&n = &e * &(n DIV e)` SUBST1_TAC THENL
   [UNDISCH_TAC `e divides n` THEN REWRITE_TAC[DIVIDES_DIV_MULT] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N / bv_grid U d (j + 1) < &(n DIV e)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&(bv_grid_K N U d j) + &1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&N / (&1 + d) = bv_grid U d j * (&N / bv_grid U d (j + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[BV_GRID_SUC] THEN
    SUBGOAL_THEN `~(bv_grid U d j = &0) /\ ~(&1 + d = &0)` MP_TAC THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `bv_grid U d j * &(n DIV e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N / bv_grid U d (j + 1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_SIMP_TAC[BV_GRID_POS]]);;

let BV_G_L2 = prove
 (`!N U V d. &0 < U /\ &0 < d /\ &1 <= V
             ==> sum(1..N) (\n. norm(Cx(bv_g N U V d n)) pow 2)
                 <= log(&N) pow 2 *
                    ((&N - &N / (&1 + d)) * (&1 + log V) pow 3 + V pow 2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
  SUBGOAL_THEN `&0 <= &N / (&1 + d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&N / (&1 + d) <= &N` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &1 + d`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= n * d ==> n <= n * (&1 + d)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..N) (\n. bv_g N U V d n pow 2) =
    sum {n | &N / (&1 + d) < &n /\ n <= N} (\n. bv_g N U V d n pow 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &n` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
      X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `bv_g N U V d n = &0` (fun th ->
        REWRITE_TAC[th; REAL_POW_ZERO; ARITH_RULE `~(2 = 0)`]) THEN
      MATCH_MP_TAC BV_G_SUPPORT THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[REAL_NOT_LT]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {n | &N / (&1 + d) < &n /\ n <= N}
                (\n. log(&N) pow 2 * &(tau_le V n) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&N / (&1 + d) < &n` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(tau_le V n) * log(&n)` THEN
    ASM_SIMP_TAC[BV_G_BOUND] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC SUM_TAU_LE_SQUARE_INTERVAL THEN ASM_REWRITE_TAC[]);;

let BV_A_SHORT = prove
 (`!N U d j M1 (c:num->complex).
     bv_grid U d (j + 1) < &M1 + &1
     ==> bv_A N U d j c =
         vsum(1..MIN N M1)
           (\m. Cx(if bv_grid U d j < &m /\ &m <= bv_grid U d (j + 1)
                   then mangoldt m else &0) * c m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_A] THEN
  ASM_CASES_TAC `N <= M1:num` THENL
   [ASM_SIMP_TAC[ARITH_RULE `N <= M1 ==> MIN N M1 = N`]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  ASM_SIMP_TAC[ARITH_RULE `M1 < N ==> MIN N M1 = M1`] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` SUBST1_TAC o
    REWRITE_RULE[LT_EXISTS]) THEN
  REWRITE_TAC[ARITH_RULE `M1 + SUC p = M1 + p + 1`] THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= M1 + 1`] THEN
  REWRITE_TAC[VECTOR_ARITH `x + y:complex = x <=> y = vec 0`] THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&m <= bv_grid U d (j + 1))`
    (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&M1 + &1` THEN ASM_REWRITE_TAC[REAL_OF_NUM_ADD;
   REAL_OF_NUM_LE] THEN
  ASM_ARITH_TAC);;

let VB_A_L2 = prove
 (`!N U d j M1. &0 < U /\ &0 < d /\ 1 <= N
                ==> sum(1..MIN N M1)
                      (\m. norm(Cx(if bv_grid U d j < &m /\
                                      &m <= bv_grid U d (j + 1)
                                   then mangoldt m else &0)) pow 2)
                    <= log(&N) pow 2 *
                       (bv_grid U d (j + 1) - bv_grid U d j + &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_POW_ZERO; ARITH_RULE `~(2 = 0)`] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {m | m IN 1..MIN N M1 /\ bv_grid U d j < &m /\
                       &m <= bv_grid U d (j + 1)} (\m. log(&N) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[MANGOLDT_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&m)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MANGOLDT_LE_LOG THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `&(CARD {t | bv_grid U d j < &t /\ &t <= bv_grid U d (j + 1)})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_NUM_INTERVAL] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`bv_grid U d j`; `bv_grid U d (j + 1)`]
           CARD_REAL_INTERVAL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC BV_GRID_MONO_LE THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y - a + &1 ==> x <= y - a + &1:real`) THEN
  FIRST_ASSUM ACCEPT_TAC);;

let BV_B_ZERO = prove
 (`!V (c:num->complex) K. &K <= V ==> bv_B V c K = Cx(&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_B; GSYM COMPLEX_VEC_0] THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `vaughan_e V k = &0`
    (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
  MATCH_MP_TAC VAUGHAN_E_SMALL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&K:real` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let VB_B_L2 = prove
 (`!V K. &1 <= V
         ==> sum(1..K) (\k. norm(Cx(vaughan_e V k)) pow 2)
             <= &K * (&1 + log V) pow 3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..K) (\k. &(tau_le V k) pow 2)` THEN
  ASM_SIMP_TAC[SUM_TAU_LE_SQUARE_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS; VAUGHAN_E_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Type II: large sieve estimates and summation over the moduli.             *)
(* ------------------------------------------------------------------------- *)

let BOX_ALG_F1 = prove
 (`!M N1 X1 k d L.
     &0 < M /\ &0 <= d /\ &0 <= L /\ &N1 <= &2 * M /\ &0 <= X1 /\
     X1 <= &2 * d * L pow 2 * M
     ==> sqrt((&4 * &N1 + &36 * &k pow 2) * X1)
         <= L * sqrt d * (&4 * M + &12 * &k * sqrt M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt M /\ sqrt M pow 2 = M /\
                &0 <= sqrt d /\ sqrt d pow 2 = d`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4 * (&2 * M) + &36 * &k pow 2) * (&2 * d * L pow 2 * M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `s = sqrt M` THEN ABBREV_TAC `t = sqrt d` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rhs(concl th) = `d:real`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rhs(concl th) = `M:real`)) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
  SUBGOAL_THEN
   `(L * t * (&4 * s pow 2 + &12 * &k * s)) pow 2 -
    (&4 * (&2 * s pow 2) + &36 * &k pow 2) *
    (&2 * t pow 2 * L pow 2 * s pow 2) =
    (L * t * s) pow 2 * (&96 * &k * s + &72 * &k pow 2)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2]);;

let BOX_ALG_F2 = prove
 (`!q kj X2 k b.
     &0 <= q /\ &0 <= b /\ &kj <= q /\ &0 <= X2 /\ X2 <= &kj * b pow 2
     ==> sqrt((&4 * &kj + &36 * &k pow 2) * X2)
         <= b * (&2 * q + &6 * &k * sqrt q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt q /\ sqrt q pow 2 = q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4 * q + &36 * &k pow 2) * (q * b pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&kj * b pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  ABBREV_TAC `s = sqrt q` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rhs(concl th) = `q:real`)) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
  SUBGOAL_THEN
   `(b * (&2 * s pow 2 + &6 * &k * s)) pow 2 -
    (&4 * s pow 2 + &36 * &k pow 2) * (s pow 2 * b pow 2) =
    b pow 2 * (&24 * &k * s pow 3)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POS; REAL_POW_LE]);;

let BOX_ALG_F3 = prove
 (`!M N U V k L d b.
     &0 < M /\ &0 < U /\ &0 < V /\ U <= M /\ M * V <= &N /\
     &0 <= L /\ &0 <= d /\ &0 <= b
     ==> (L * sqrt d * (&4 * M + &12 * &k * sqrt M)) *
         (b * (&2 * (&N / M) + &6 * &k * sqrt(&N / M)))
         <= L * sqrt d * b *
            (&8 * &N + &24 * &k * &N / sqrt V + &24 * &k * &N / sqrt U +
             &72 * &k pow 2 * sqrt(&N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt M /\ sqrt M pow 2 = M /\ &0 <= sqrt(&N) /\
                sqrt(&N) pow 2 = &N /\ &0 < sqrt U /\ &0 < sqrt V /\
                &0 <= sqrt d`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POS_LE; SQRT_POW_2; REAL_POS;
                 REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_DIV] THEN
  SUBGOAL_THEN
   `(L * sqrt d * (&4 * M + &12 * &k * sqrt M)) *
    (b * (&2 * (&N / M) + &6 * &k * (sqrt(&N) / sqrt M))) =
    (L * sqrt d * b) *
    (&8 * &N + &24 * &k * (sqrt(&N) * sqrt M) + &24 * &k * &N / sqrt M +
     &72 * &k pow 2 * sqrt(&N))`
  SUBST1_TAC THENL
   [ABBREV_TAC `s = sqrt M` THEN ABBREV_TAC `w = sqrt(&N)` THEN
    MAP_EVERY (fun t -> FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = t))) [`M:real`; `&N:real`] THEN
    UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
          [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= a' /\ b <= b' ==> &8 * n + a + b + c <= &8 * n + a' + b' + c`) THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&N pow 2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      SIMP_TAC[POW_2_SQRT; REAL_POS; REAL_LE_REFL]];
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REAL_ARITH_TAC]);;

let TYPE2_BOX_BOUND = prove
 (`!N U V d j k L b.
     1 <= N /\ &1 <= V /\ &0 < U /\ &0 < d /\ d <= &1 /\ &1 <= d * U /\
     1 <= k /\ log(&N) <= L /\ &0 <= b /\ (&1 + log V) pow 3 <= b pow 2
     ==> sum(1..k) (\r. &r / &(phi r) *
           sum {c | primitive_character r c}
             (\c. norm(bv_A N U d j c) * norm(bv_B V c (bv_grid_K N U d j))))
         <= L * sqrt d * b *
            (&8 * &N + &24 * &k * &N / sqrt V + &24 * &k * &N / sqrt U +
             &72 * &k pow 2 * sqrt(&N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt U /\ &0 < sqrt V /\ &0 <= sqrt d /\ &0 <= sqrt(&N)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `kj = bv_grid_K N U d j` THEN
  ASM_CASES_TAC `&kj <= V` THENL
   [ASM_SIMP_TAC[BV_B_ZERO; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_MUL_RZERO;
                 SUM_0] THEN
    REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_DIV;
                  MATCH_MP_TAC REAL_LE_ADD; CONJ_TAC]) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  ABBREV_TAC `M = bv_grid U d j` THEN
  SUBGOAL_THEN `&0 < M /\ U <= M /\ bv_grid U d (j + 1) = (&1 + d) * M`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[BV_GRID_SUC] THEN
    ASM_SIMP_TAC[BV_GRID_POS] THEN
    MP_TAC(SPECL [`U:real`; `d:real`; `0`; `j:num`] BV_GRID_MONO_LE) THEN
    ASM_REWRITE_TAC[LE_0] THEN REWRITE_TAC[bv_grid; real_pow; REAL_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `U:real`; `d:real`; `j:num`] BV_GRID_K) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `bv_grid U d (j + 1)` FLOOR_POS) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
  MP_TAC(SPEC `bv_grid U d (j + 1)` FLOOR) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `U:real`; `d:real`; `j:num`; `M1:num`] VB_A_L2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`V:real`; `kj:num`] VB_B_L2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `bv_grid U d (j + 1) < &M1 + &1` (fun th ->
    REWRITE_TAC[MATCH_MP BV_A_SHORT th]) THENL [ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  REWRITE_TAC[bv_B] THEN
  MP_TAC(ISPECL [`MIN N M1`; `kj:num`;
    `\m. Cx(if bv_grid U d j < &m /\ &m <= bv_grid U d (j + 1)
            then mangoldt m else &0)`;
    `\k. Cx(vaughan_e V k)`; `k:num`] LARGE_SIEVE_BILINEAR_L2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP (REAL_ARITH
    `!x y z. x <= y ==> y <= z ==> x <= z:real`) th)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(L * sqrt d * (&4 * M + &12 * &k * sqrt M)) *
              (b * (&2 * (&N / M) + &6 * &k * sqrt(&N / M)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC BOX_ALG_F3 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * &kj:real` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(M:real) * &N / ((&1 + d) * M)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `M * &N / ((&1 + d) * M) = &N / (&1 + d)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < M` THEN UNDISCH_TAC `&0 < d` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &1 + d`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= n * d ==> n <= n * (&1 + d)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC] THEN
  ABBREV_TAC `X1 = sum(1..MIN N M1) (\m. norm (Cx (if M < &m /\
                     &m <= (&1 + d) * M then mangoldt m else &0)) pow 2)` THEN
  ABBREV_TAC `X2 = sum (1..kj) (\m. norm (Cx (vaughan_e V m)) pow 2)` THEN
  SUBGOAL_THEN `&0 <= X1 /\ &0 <= X2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X1"; "X2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `d * M <= M /\ &1 <= d * M` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d * U:real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(MIN N M1) <= &2 * M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M1:real` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `X1 <= &2 * d * L pow 2 * M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(L:real) pow 2 * (d * M + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `log(&N) pow 2 * ((&1 + d) * M - M + &1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&2 * d * L pow 2 * M = L pow 2 * (&2 * (d * M))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N / M /\ &kj <= &N / M` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&N / ((&1 + d) * M):real` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `X2 <= &kj * b pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&kj * (&1 + log V) pow 3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    MATCH_MP_TAC BOX_ALG_F1 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    MATCH_MP_TAC BOX_ALG_F2 THEN ASM_REWRITE_TAC[]]);;

let TYPE2_DELTA_BOUND = prove
 (`!N U V d k L b.
     1 <= N /\ &0 < U /\ &0 < d /\ &1 <= V /\ 1 <= k /\
     log(&N) <= L /\ &0 <= b /\ (&1 + log V) pow 3 <= b pow 2
     ==> sum(1..k) (\r. &r / &(phi r) *
           sum {c | primitive_character r c}
             (\c. norm(vsum(1..N) (\n. Cx(bv_g N U V d n) * c n))))
         <= &k * &16 * L * (sqrt d * b * &N + V * sqrt(&N)) +
            &k pow 2 * &48 * L * (sqrt d * b * sqrt(&N) + V)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:num`; `\n. Cx(bv_g N U V d n)`; `k:num`]
    LARGE_SIEVE_LINEAR_L2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP (REAL_ARITH
    `!x y z. x <= y ==> y <= z ==> x <= z:real`) th)) THEN
  MP_TAC(SPECL [`N:num`; `U:real`; `V:real`; `d:real`] BV_G_L2) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Y = sum(1..N) (\n. norm(Cx(bv_g N U V d n)) pow 2)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt d /\ sqrt d pow 2 = d /\ &0 <= sqrt(&N) /\
                sqrt(&N) pow 2 = &N`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y <= (L:real) pow 2 * ((d * &N) * b pow 2 + V pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&N) pow 2 *
                ((&N - &N / (&1 + d)) * (&1 + log V) pow 3 + V pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      SUBGOAL_THEN `&0 <= &N - &N / (&1 + d)` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_SUB_LE] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &1 + d`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= n * d ==> n <= n * (&1 + d)`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MP_TAC(SPEC `V:real` LOG_POS) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + z <= y + z:real`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_SUB_LE] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &1 + d`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= n * d ==> n <= n * (&1 + d)`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `n - x <= d * n <=> n - d * n <= x:real`] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &1 + d`] THEN
        REWRITE_TAC[REAL_ARITH
         `(n - d * n) * (&1 + d) = n - n * (d:real) pow 2`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x:real`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
        MATCH_MP_TAC REAL_POW_LE THEN MP_TAC(SPEC `V:real` LOG_POS) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt Y <= L * (sqrt d * b * sqrt(&N) + V)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(L:real) pow 2 * ((d * &N) * b pow 2 + V pow 2)` THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `sd = sqrt d` THEN ABBREV_TAC `sn = sqrt(&N)` THEN
    MAP_EVERY (fun t -> FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = t))) [`d:real`; `&N:real`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
    SUBGOAL_THEN
     `(L * (sd * b * sn + V)) pow 2 -
      L pow 2 * ((sd pow 2 * sn pow 2) * b pow 2 + V pow 2) =
      &2 * L pow 2 * (sd * b * sn * V)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&4 * &N + &36 * &k pow 2) <= &2 * sqrt(&N) + &6 * &k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o
      RAND_CONV) [SYM th]) o check (fun th -> rhs(concl th) = `&N:real`)) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
    SUBGOAL_THEN
     `(&2 * sqrt(&N) + &6 * &k) pow 2 -
      (&4 * sqrt(&N) pow 2 + &36 * &k pow 2) = &24 * &k * sqrt(&N)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&8 * &k * (&2 * sqrt(&N) + &6 * &k) *
              (L * (sqrt d * b * sqrt(&N) + V))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN ABBREV_TAC `sn = sqrt(&N)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rhs(concl th) = `&N:real`)) THEN
  REAL_ARITH_TAC);;

let TYPE2_CUMULATIVE = prove
 (`!N U V d J k L b.
     1 <= N /\ &1 <= V /\ &0 < U /\ &0 < d /\ d <= &1 /\ &1 <= d * U /\
     &N <= bv_grid U d J /\ 1 <= k /\ log(&N) <= L /\ &0 <= b /\
     (&1 + log V) pow 3 <= b pow 2
     ==> sum(1..k) (\r. &r / &(phi r) *
           sum {c | primitive_character r c}
             (\c. norm(vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) * c m *
                       vsum(1..N DIV m) (\k. Cx(vaughan_e V k) * c k)))))
         <= (&J + &1) * L * sqrt d * b *
            (&8 * &N + &24 * &k * &N / sqrt V + &24 * &k * &N / sqrt U +
             &72 * &k pow 2 * sqrt(&N)) +
            &k * &16 * L * (sqrt d * b * &N + V * sqrt(&N)) +
            &k pow 2 * &48 * L * (sqrt d * b * sqrt(&N) + V)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0..J) (\j. sum(1..k) (\r. &r / &(phi r) *
       sum {c | primitive_character r c}
         (\c. norm(bv_A N U d j c) * norm(bv_B V c (bv_grid_K N U d j))))) +
    sum(1..k) (\r. &r / &(phi r) *
       sum {c | primitive_character r c}
         (\c. norm(vsum(1..N) (\n. Cx(bv_g N U V d n) * c n))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum(1..k) (\r. &r / &(phi r) *
        sum {c | primitive_character r c}
          (\c. sum(0..J) (\j. norm(bv_A N U d j c) *
                              norm(bv_B V c (bv_grid_K N U d j))) +
               norm(vsum(1..N) (\n. Cx(bv_g N U V d n) * c n))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS] THEN
      X_GEN_TAC `c:num->complex` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_TAC THEN
      MP_TAC(SPECL [`N:num`; `U:real`; `V:real`; `d:real`; `J:num`;
                    `c:num->complex`] TYPE2_SPLIT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[primitive_character; DIRICHLET_CHARACTER_MUL];
        DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(x:complex) <= a ==> norm(x + y) <= a + norm y`) THEN
      MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SIMP_TAC[SUM_ADD; FINITE_PRIMITIVE_CHARACTERS; REAL_ADD_LDISTRIB;
             SUM_ADD_NUMSEG] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..k) (\r. sum(0..J) (\j. &r / &(phi r) *
       sum {c | primitive_character r c}
         (\c. norm(bv_A N U d j c) *
              norm(bv_B V c (bv_grid_K N U d j)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL
       [`\c:num->complex j:num. norm(bv_A N U d j c) *
                                norm(bv_B V c (bv_grid_K N U d j))`;
        `{c | primitive_character r c}`; `0..J`] SUM_SWAP) THEN
      REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; FINITE_NUMSEG];
      GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
    MATCH_MP_TAC TYPE2_DELTA_BOUND THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..J) (\j. L * sqrt d * b *
            (&8 * &N + &24 * &k * &N / sqrt V + &24 * &k * &N / sqrt U +
             &72 * &k pow 2 * sqrt(&N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC TYPE2_BOX_BOUND THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]]);;

let TYPE2_TOTAL = prove
 (`!N U V d J a D L b.
     1 <= N /\ &1 <= V /\ &0 < U /\ &0 < d /\ d <= &1 /\ &1 <= d * U /\
     &N <= bv_grid U d J /\ 1 <= a /\ a <= D /\ log(&N) <= L /\ &0 <= b /\
     (&1 + log V) pow 3 <= b pow 2
     ==> bv_sum a D
          (\c. norm(vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) * c m *
                       vsum(1..N DIV m) (\k. Cx(vaughan_e V k) * c k))))
         <= ((&J + &1) * L * sqrt d * b * &8 * &N) / &a +
            ((&J + &1) * L * sqrt d * b *
             (&24 * &N / sqrt V + &24 * &N / sqrt U) +
             &16 * L * (sqrt d * b * &N + V * sqrt(&N))) *
            (&2 + log(&D)) +
            &2 * ((&J + &1) * L * sqrt d * b * &72 * sqrt(&N) +
                  &48 * L * (sqrt d * b * sqrt(&N) + V)) * &D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt U /\ &0 < sqrt V /\ &0 <= sqrt d /\ &0 <= sqrt(&N)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[bv_sum] THEN
  ABBREV_TAC
   `t = \r. &r / &(phi r) *
        sum {c | primitive_character r c}
          (\c. norm(vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) * c m *
                  vsum(1..N DIV m) (\k. Cx(vaughan_e V k) * c k))))` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(a..D) (\r. t r / &r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_FIELD
     `!x y r p. ~(r = &0) /\ x = y ==> inv p * x = (r / p * y) / r`) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ABEL_RECIPROCAL_BOUND THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!r. &0 <= (t:num->real) r` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; NORM_POS_LE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_DIV;
                  MATCH_MP_TAC REAL_LE_ADD; CONJ_TAC]) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_POW_2; REAL_LT_IMP_LE];
    REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_DIV;
                  MATCH_MP_TAC REAL_LE_ADD; CONJ_TAC]) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_POW_2; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_DIV;
                  MATCH_MP_TAC REAL_LE_ADD; CONJ_TAC]) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_POW_2; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..k) (t:num->real)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "t" THEN
  W(MP_TAC o PART_MATCH (lhand o rand) TYPE2_CUMULATIVE o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The bound for the twisted psi sums.                                       *)
(* ------------------------------------------------------------------------- *)

let BV_PSI_BOUND = prove
 (`!N U V d J a D L b.
     1 <= N /\ &1 <= V /\ &1 <= U /\ &0 < d /\ d <= &1 /\ &1 <= d * U /\
     &N <= bv_grid U d J /\ 2 <= a /\ a <= D /\ log(&N) <= L /\ &0 <= b /\
     (&1 + log V) pow 3 <= b pow 2
     ==> bv_sum a D (\c. norm(vsum(1..N) (\n. Cx(mangoldt n) * c n)))
         <= &D * (&18 * U + &D * (&2 * U * V * log(U * V) +
                                  &4 * V * log(&N + &1))) +
            ((&J + &1) * L * sqrt d * b * &8 * &N) / &a +
            ((&J + &1) * L * sqrt d * b *
             (&24 * &N / sqrt V + &24 * &N / sqrt U) +
             &16 * L * (sqrt d * b * &N + V * sqrt(&N))) *
            (&2 + log(&D)) +
            &2 * ((&J + &1) * L * sqrt d * b * &72 * sqrt(&N) +
                  &48 * L * (sqrt d * b * sqrt(&N) + V)) * &D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= U * V /\ &0 <= log(U * V) /\ &0 <= log(&N + &1)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ r ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_LE_ADDL; REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `bv_sum a D (\c. (&18 * U + &D * (&2 * U * V * log(U * V) +
                                    &4 * V * log(&N + &1))) +
      norm(vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) * c m *
                       vsum(1..N DIV m) (\k. Cx(vaughan_e V k) * c k))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BV_SUM_LE THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `c:num->complex`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `!m n. (c:num->complex)(m * n) = c m * c n` ASSUME_TAC THENL
     [ASM_MESON_TAC[primitive_character; DIRICHLET_CHARACTER_MUL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VAUGHAN_VSUM] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:complex) + norm(b) + norm(c) <= t
      ==> norm(a + b - c + d) <= t + norm d`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&18 * U + &r * (&2 * U * V * log(U * V) +
                               &4 * V * log(&N + &1))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ADD_LDISTRIB; GSYM REAL_ADD_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC VAUGHAN_S1_BOUND THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[primitive_character; DIRICHLET_CHARACTER_NORM_LE];
        ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MP_TAC(SPECL [`V:real`; `N:num`; `r:num`; `c:num->complex`]
          VAUGHAN_S3_BOUND) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_MUL_AC];
        MP_TAC(SPECL [`U:real`; `V:real`; `N:num`; `r:num`; `c:num->complex`]
          VAUGHAN_S2_BOUND) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_MUL_AC]];
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> u + x <= u + y`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [BV_SUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BV_SUM_CONST_LE THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC TYPE2_TOTAL THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* From residue classes to primitive characters.                             *)
(* ------------------------------------------------------------------------- *)

let PRIMES_LE_REAL = prove
 (`!x. {p | prime p /\ &p <= &x} = {p | prime p /\ p <= x}`,
  REWRITE_TAC[REAL_OF_NUM_LE]);;

let PRIMITIVE_TWIST_PI_BOUND = prove
 (`!x d r (c:num->complex).
     1 <= d /\ primitive_character r c
     ==> norm(vsum {p | prime p /\ p <= x}
                   (\p. if coprime(p,d) then c p else Cx(&0)))
         <= norm(vsum {p | prime p /\ &p <= &x} c) + log(&d) / log(&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&x:real`; `&0:real`; `d:num`; `c:num->complex`]
    PRIME_INTERVAL_TWIST) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[primitive_character; DIRICHLET_CHARACTER_NORM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p | prime p /\ &p <= &0} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; REAL_OF_NUM_LE] THEN
    MESON_TAC[PRIME_0; LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p | prime p /\ &0 < &p /\ &p <= &x} = {p | prime p /\ p <= x}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 0 < p`];
    REWRITE_TAC[VSUM_CLAUSES; NORM_0; REAL_ADD_LID]]);;

let ABS_CARD_DIFF_LE = prove
 (`!a b c w. a <= b /\ b <= a + c /\ &c <= w ==> abs(&a - &b) <= w`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let BV_AP_DISCREPANCY = prove
 (`!x d a. 1 <= d /\ coprime(a,d)
     ==> abs(&(CARD {p | prime p /\ p <= x /\ (p == a) (mod d)}) -
             &(CARD {p | prime p /\ p <= x}) / &(phi d))
         <= inv(&(phi d)) *
            sum {r | r divides d /\ ~(r = 1)}
              (\r. sum {c | primitive_character r c}
                     (\c. norm(vsum {p | prime p /\ &p <= &x} c))) +
            inv(&(phi d)) * (&d + &1) * log(&d) / log(&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num`; `a:num`; `\p:num. p`; `\p:num. &1`;
                 `{p | prime p /\ p <= x}`] CHARACTER_DISCREPANCY_BOUND) THEN
  ASM_REWRITE_TAC[FINITE_ATMOST; COMPLEX_MUL_LID; ETA_AX] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
  SIMP_TAC[GSYM CARD_EQ_SUM; FINITE_PRIMES_LE_RESTRICT] THEN
  ABBREV_TAC `G = sum {r | r divides d /\ ~(r = 1)}
    (\r. sum {c | primitive_character r c}
           (\c. norm (vsum {p | prime p /\ &p <= &x} c)))` THEN
  ABBREV_TAC `A0 = &(CARD {p | prime p /\ p <= x /\ (p == a) (mod d)})` THEN
  ABBREV_TAC `C0 = &(CARD {p | prime p /\ p <= x /\ coprime (p,d)})` THEN
  ABBREV_TAC `P0 = &(CARD {p | prime p /\ p <= x})` THEN
  ABBREV_TAC `S0 = sum ({c | dirichlet_character d c} DELETE chi_0 d)
                       (\c. norm (vsum {p | prime p /\ p <= x} c))` THEN
  SUBGOAL_THEN `FINITE {r | r divides d /\ ~(r = 1)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r | r divides d}` THEN
    CONJ_TAC THENL [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC;
                    SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&d) / log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `S0 <= G + &d * log(&d) / log(&2)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "G"] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {r | r divides d /\ ~(r = 1)}
      (\r. sum {c | primitive_character r c}
        (\c. norm(vsum {p | prime p /\ p <= x}
                (\n. if coprime(n,d) then c n else Cx(&0)))))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`d:num`;
        `\c:num->complex. norm(vsum {p | prime p /\ p <= x} c)`]
        PRIMITIVE_REDUCTION_SUM) THEN
      ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {r | r divides d /\ ~(r = 1)}
      (\r. sum {c | primitive_character r c}
        (\c. norm(vsum {p | prime p /\ &p <= &x} c) +
             log(&d) / log(&2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_LE THEN
      REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; IN_ELIM_THM] THEN
      X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
      MATCH_MP_TAC PRIMITIVE_TWIST_PI_BOUND THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[SUM_ADD; FINITE_PRIMITIVE_CHARACTERS] THEN
    ASM_SIMP_TAC[SUM_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y <= x + z`) THEN
    SIMP_TAC[SUM_CONST; FINITE_PRIMITIVE_CHARACTERS] THEN
    REWRITE_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {r | r divides d /\ ~(r = 1)} (\r. &(phi r))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC CARD_PRIMITIVE_CHARACTERS_LE THEN
      REWRITE_TAC[ARITH_RULE `1 <= r <=> ~(r = 0)`] THEN
      ASM_MESON_TAC[DIVIDES_ZERO; ARITH_RULE `1 <= d ==> ~(d = 0)`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {r | r divides d} (\r. &(phi r))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[REAL_POS] THEN
      CONJ_TAC THENL [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC;
                      SET_TAC[]];
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUM; FINITE_DIVISORS;
                   ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
      ASM_SIMP_TAC[REWRITE_RULE[ETA_AX] PHI_DIVISORSUM;
                   ARITH_RULE `1 <= d ==> ~(d = 0)`; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(C0 - P0) <= log(&d) / log(&2)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C0"; "P0"] THEN
    MATCH_MP_TAC ABS_CARD_DIFF_LE THEN
    EXISTS_TAC `CARD {p | prime p /\ p divides d}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_ATMOST] THEN
      SET_TAC[];
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD({p | prime p /\ p <= x /\ coprime(p,d)} UNION
                       {p | prime p /\ p divides d})` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
          MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM];
          REWRITE_TAC[FINITE_UNION; FINITE_PRIMES_LE_RESTRICT] THEN
          MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC];
        MATCH_MP_TAC CARD_UNION_LE THEN
        REWRITE_TAC[FINITE_PRIMES_LE_RESTRICT] THEN
        MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC];
      MATCH_MP_TAC OMEGA_LE_LOG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[real_div] THEN
  SUBGOAL_THEN `&0 <= inv(&(phi d))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&(phi d)) * S0 <=
                inv(&(phi d)) * (G + &d * log(&d) * inv(log(&2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv(&(phi d)) * C0 - inv(&(phi d)) * P0) <=
                inv(&(phi d)) * log(&d) * inv(log(&2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BV_AP_TOTAL = prove
 (`!x D a. 1 <= D /\ (!d. coprime(a d,d))
     ==> sum(1..D) (\d. abs(&(CARD {p | prime p /\ p <= x /\
                                       (p == a d) (mod d)}) -
                            &(CARD {p | prime p /\ p <= x}) / &(phi d)))
         <= &4 * (&1 + log(&D)) *
            bv_sum 2 D (\c. norm(vsum {p | prime p /\ &p <= &x} c)) +
            &2 * &D pow 2 * log(&D) / log(&2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = \r. sum {c | primitive_character r c}
                        (\c. norm(vsum {p | prime p /\ &p <= &x} c))` THEN
  SUBGOAL_THEN `!r. &0 <= (G:num->real) r` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "G" THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&D) / log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..D) (\d. inv(&(phi d)) *
                sum {r | r divides d /\ ~(r = 1)} (\r. (G:num->real) r)) +
              sum(1..D) (\d. &2 * &D * log(&D) / log(&2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`x:num`; `d:num`; `(a:num->num) d`] BV_AP_DISCREPANCY) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    ABBREV_TAC `u = abs(&(CARD {p | prime p /\ p <= x /\
                                   (p == a d) (mod d)}) -
                        &(CARD {p | prime p /\ p <= x}) / &(phi d))` THEN
    ABBREV_TAC `v = inv (&(phi d)) * sum {r | r divides d /\ ~(r = 1)}
       (\r. sum {c | primitive_character r c}
              (\c. norm (vsum {p | prime p /\ &p <= &x} c)))` THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> u <= x + y ==> u <= x + z`) THEN
    SUBGOAL_THEN `&1 <= &(phi d)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN
       MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * (&d + &1) * log(&D) / log(&2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN
        MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
          REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
          REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC LOG_POS THEN
          REAL_ARITH_TAC]];
      REWRITE_TAC[REAL_MUL_LID] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&d <= &D /\ &1 <= &D` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`\r d:num. (G:num->real) r`; `D:num`] BILINEAR_REINDEX) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[bv_sum] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[BETA_RULE(REWRITE_RULE[FUN_EQ_THM] th)])
    o check (fun th -> rhs(concl th) = `G:num->real`)) THEN
  ABBREV_TAC `W = sum(2..D) (\r. inv(&(phi r)) * (G:num->real) r)` THEN
  SUBGOAL_THEN `&0 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..D) (\k. inv(&(phi k)) * W)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_RMUL] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SUM_INV_PHI_LE]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN EXPAND_TAC "W" THEN
  SUBGOAL_THEN `1 <= D DIV k /\ D DIV k <= D` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= k ==> ~(k = 0)`;
                 MULT_CLAUSES; DIV_LE];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; ASSUME `1 <= D DIV k`] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2..D DIV k) (\r. inv(&(phi r)) * (G:num->real) r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN GEN_TAC THEN
      UNDISCH_TAC `D DIV k <= D` THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]]]);;

(* ------------------------------------------------------------------------- *)
(* From pi to theta to psi.                                                  *)
(* ------------------------------------------------------------------------- *)

let PI_THETA_WEIGHTED = prove
 (`!x a b B.
     2 <= x /\ &0 <= B /\
     (!n. 2 <= n /\ n <= x
          ==> bv_sum a b (\c. norm(vsum(1..n)
                (\m. Cx(if prime m then log(&m) else &0) * c m))) <= B)
     ==> bv_sum a b (\c. norm(vsum {p | prime p /\ p <= x} c)) <= &2 * B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `bv_sum a b (\c. inv(log(&x + &1)) *
        norm(vsum(1..x) (\m. Cx(if prime m then log(&m) else &0) * c m)) +
      sum(2..x) (\k. (inv(log(&k)) - inv(log(&k + &1))) *
        norm(vsum(1..k)
               (\m. Cx(if prime m then log(&m) else &0) * c m))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BV_SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PI_THETA_NORM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BV_SUM_ADD; BV_SUM_LMUL] THEN
  SIMP_TAC[BV_SUM_SUM; FINITE_NUMSEG; BV_SUM_LMUL] THEN
  SUBGOAL_THEN `!k. 2 <= k ==> &0 <= inv(log(&k)) - inv(log(&k + &1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(log(&x + &1)) * B +
              sum(2..x) (\k. (inv(log(&k)) - inv(log(&k + &1))) * B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC LOG_POS THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  SUBGOAL_THEN `sum(2..x) (\k. inv(log(&k)) - inv(log(&k + &1))) =
                inv(log(&2)) - inv(log(&x + &1))` SUBST1_TAC THENL
   [MP_TAC(SPECL [`2`; `x:num`]
      (INST [`\k. inv(log(&k))`,`f:num->real`] SUM_DIFFS_ALT)) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN REWRITE_TAC[SUM_NEG] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC LOG_2_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(log(&2)) <= &2` MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `i * B + (l - i) * B = l * (B:real)`] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[]);;

let THETA_PSI_BV = prove
 (`!n a b. 1 <= n /\ 1 <= a
     ==> bv_sum a b (\c. norm(vsum(1..n)
                (\m. Cx(if prime m then log(&m) else &0) * c m)))
         <= bv_sum a b (\c. norm(vsum(1..n) (\m. Cx(mangoldt m) * c m))) +
            &b * (sqrt(&n) * log(&n) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `bv_sum a b (\c. norm(vsum(1..n) (\m. Cx(mangoldt m) * c m)) +
                              sqrt(&n) * log(&n) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BV_SUM_LE THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `c:num->complex`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(y - x:complex) <= e ==> norm x <= norm y + e`) THEN
    REWRITE_TAC[GSYM VSUM_SUB_NUMSEG; GSYM COMPLEX_SUB_RDISTRIB;
                GSYM CX_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..n) (\m. mangoldt m -
                               (if prime m then log(&m) else &0))` THEN
    ASM_SIMP_TAC[PRIME_POWER_SUM_BOUND] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    SUBGOAL_THEN `&0 <= mangoldt m - (if prime m then log(&m) else &0)`
    ASSUME_TAC THENL
     [COND_CASES_TAC THENL
       [MP_TAC(SPECL [`m:num`; `1`] MANGOLDT_PRIMEPOW) THEN
        ASM_REWRITE_TAC[EXP_1; LE_REFL] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_SUB_RZERO; MANGOLDT_POS_LE]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; REAL_LE_REFL;
                 REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    ASM_MESON_TAC[primitive_character; DIRICHLET_CHARACTER_NORM_LE];
    ALL_TAC] THEN
  REWRITE_TAC[BV_SUM_ADD] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC BV_SUM_CONST_LE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC[SQRT_POS_LE; REAL_POS; REAL_LE_POW_2]);;

(* ------------------------------------------------------------------------- *)
(* Small moduli: Siegel-Walfisz.                                             *)
(* ------------------------------------------------------------------------- *)

let BV_SMALL_PART = prove
 (`!A1 B1. ?C. &0 <= C /\
         !x R. 2 <= x /\ &R <= log(&x) pow B1
               ==> bv_sum 2 R (\c. norm(vsum {p | prime p /\ &p <= &x} c))
                   <= &R * C * &x / log(&x) pow A1`,
  MP_TAC SW_UNIFORM THEN
  DISCH_THEN(fun th -> REPEAT GEN_TAC THEN
    MP_TAC(SPECL [`A1:num`; `B1:num`] th)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `bv_sum 2 R (\c. C * &x / log(&x) pow A1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC BV_SUM_LE THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `c:num->complex`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_LE_REFL; LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&R:real` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_MESON_TAC[primitive_character];
      MATCH_MP_TAC PRIMITIVE_CHARACTER_NONPRINCIPAL THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC BV_SUM_CONST_LE THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Choice of the parameters and assembly.                                    *)
(* ------------------------------------------------------------------------- *)

let BV_PSI_ARITH = prove
 (`!k M L x sx N sN D J a lD lN lUV cb K1 K2.
     &1 <= L /\ L <= M /\ &1 <= x /\ &0 <= sx /\ sx pow 2 = x /\
     &1 <= N /\ N <= x /\ &0 <= sN /\ sN <= sx /\
     &0 <= D /\ D * M pow 23 <= sx /\ &0 <= J /\ J + &1 <= &4 * M pow 11 /\
     M pow 10 <= a /\ &0 <= lD /\ lD <= L /\ &0 <= lN /\ lN <= &2 * L /\
     &0 <= lUV /\ lUV <= &44 * &k * M /\ &0 <= cb /\
     M pow 25 <= K1 * sx /\ M <= K2 * sx
     ==> D * (&18 * M pow 22 +
              D * (&2 * M pow 22 * M pow 22 * lUV + &4 * M pow 22 * lN)) +
         ((J + &1) * L * inv(M pow 5) * (cb * M pow 2) * &8 * N) / a +
         ((J + &1) * L * inv(M pow 5) * (cb * M pow 2) *
          (&24 * N / M pow 11 + &24 * N / M pow 11) +
          &16 * L * (inv(M pow 5) * (cb * M pow 2) * N + M pow 22 * sN)) *
         (&2 + lD) +
         &2 * ((J + &1) * L * inv(M pow 5) * (cb * M pow 2) * &72 * sN +
               &48 * L * (inv(M pow 5) * (cb * M pow 2) * sN + M pow 22)) * D
         <= (&26 + &88 * &k + &1328 * cb + &48 * K1 + &96 * K2) * x / M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= M /\ &0 < M` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sx` ASSUME_TAC THENL
   [ASM_CASES_TAC `sx < &1` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `sx pow 2 <= sx * &1` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sx <= x` ASSUME_TAC THENL
   [SUBGOAL_THEN `sx * &1 <= sx * sx` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RID; GSYM REAL_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(M pow 5) /\ &0 <= M pow 2 /\ &0 <= L /\
                &0 <= J + &1 /\ &0 <= N /\ &0 <= M pow 22`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `D * M pow 22 <= sx / M` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `(D * M pow 22) * M = D * (M:real) pow 23` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `23 = 22 + 1`; REAL_POW_ADD; REAL_POW_1] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D * M pow 22` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(D * M pow 22) pow 2 <= x / M pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((sx:real) / M) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_POW_DIV; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a1 <= (&26 + &88 * k) * y /\ a2 <= &32 * cb * y /\
    a3 <= (&624 * cb + &48 * K1) * y /\ a4 <= (&672 * cb + &96 * K2) * y
    ==> a1 + a2 + a3 + a4 <=
        (&26 + &88 * k + &1328 * cb + &48 * K1 + &96 * K2) * y`) THEN
  REPEAT CONJ_TAC THENL
   [
    SUBGOAL_THEN `&0 <= x / M pow 2 /\ &0 <= (D * M pow 22) pow 2 /\
                  inv(M pow 22) <= &1 /\ &0 <= inv(M pow 22) /\ x / M <= x /\
                  &0 <= x / M`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `D * (&18 * M pow 22 +
           D * (&2 * M pow 22 * M pow 22 * lUV + &4 * M pow 22 * lN)) =
      &18 * (D * M pow 22) + &2 * ((D * M pow 22) pow 2 * lUV) +
      &4 * ((D * M pow 22) pow 2 * (lN * inv(M pow 22)))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `u <= y /\ v <= &44 * k * y /\ w <= &2 * y
      ==> &18 * u + &2 * v + &4 * w <= (&26 + &88 * k) * y`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sx / M:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(x / M pow 2) * (&44 * &k * M):real` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M` THEN
        CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(x / M pow 2) * ((&2 * M) * &1):real` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M` THEN
        CONV_TAC REAL_FIELD]];
    SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(M:real) pow 10` THEN
      ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(((&4 * M pow 11) * M * inv(M pow 5) * (cb * M pow 2) *
                  &8 * x) / M pow 10):real` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
        REPEAT(MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC) THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M` THEN
      CONV_TAC REAL_FIELD];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(((&4 * M pow 11) * M * inv(M pow 5) * (cb * M pow 2) *
                  (&24 * x / M pow 11 + &24 * x / M pow 11) +
                  &16 * M * (inv(M pow 5) * (cb * M pow 2) * x +
                             M pow 22 * sx)) * (&3 * M)):real` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
        REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC;
                      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC]) THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC]) THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `M pow 24 * sx <= K1 * x / M` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `K1 * x / M = (K1 * x) / (M:real)`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      SUBGOAL_THEN `(M pow 24 * sx) * M = M pow 25 * (sx:real)`
      SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE `25 = 24 + 1`; REAL_POW_ADD; REAL_POW_1] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(K1 * sx) * sx:real` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
          [SYM th]) o check (fun th -> rhs(concl th) = `x:real`)) THEN
        REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC; REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&624 * cb * x / M + &48 * (M pow 24 * sx)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M` THEN
      CONV_TAC REAL_FIELD;
      UNDISCH_TAC `M pow 24 * sx <= K1 * x / M` THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `D <= sx / M pow 23` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * (((&4 * M pow 11) * M * inv(M pow 5) * (cb * M pow 2) *
                        &72 * sx +
                        &48 * M * (inv(M pow 5) * (cb * M pow 2) * sx +
                                   M pow 22)) *
                       (sx / M pow 23))):real` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC]) THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
        REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC;
                      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC]) THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC]) THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `sx <= K2 * x / M` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `K2 * x / M = (K2 * x) / (M:real)`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sx * (K2 * sx):real` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
          [SYM th]) o check (fun th -> rhs(concl th) = `x:real`)) THEN
        REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `x / M pow 14 <= x / M /\ x / M pow 25 <= x / M`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&576 * cb * (x / M pow 14) + &96 * cb * (x / M pow 25) +
                &96 * sx` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o
        check (fun th -> rhs(concl th) = `x:real`)) THEN
      UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `cb * a <= cb * y /\ cb * b <= cb * y /\ s <= K2 * y
      ==> &576 * cb * a + &96 * cb * b + &96 * s <=
          (&672 * cb + &96 * K2) * y`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_ARITH `K2 * x / M = K2 * (x / M:real)`]]]);;

let BV_PARAM_FACTS = prove
 (`!k L M. 1 <= k /\ &1 <= L /\ M = L pow k
           ==> &1 <= M /\ L <= M /\
               sqrt(M pow 22) = M pow 11 /\
               sqrt(inv(M pow 10)) = inv(M pow 5) /\
               &1 <= inv(M pow 10) * M pow 22 /\
               inv(M pow 10) <= &1 /\ &0 < inv(M pow 10) /\
               &1 <= M pow 22 /\
               log(M pow 22 * M pow 22) <= &44 * &k * M /\
               &0 <= log(M pow 22 * M pow 22) /\
               (&1 + log(M pow 22)) pow 3 <=
               ((&1 + &22 * &k) pow 2 * M pow 2) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `L <= M` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= M /\ &0 < M` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log L <= L` ASSUME_TAC THENL
   [MP_TAC(SPEC `L - &1` LOG_LE) THEN
    REWRITE_TAC[REAL_ARITH `&1 + (L - &1) = L`] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log M <= &k * M` ASSUME_TAC THENL
   [UNDISCH_TAC `L <= M` THEN
    ASM_SIMP_TAC[LOG_POW; REAL_ARITH `&1 <= L ==> &0 < L`] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log M` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o
    check (fun th -> concl th = `M = (L:real) pow k`)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= M pow 22 /\ &1 <= M pow 12` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN
    SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; ASSUME `&0 < M`] THEN
    REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[SQRT_INV] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN
    SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; ASSUME `&0 < M`] THEN
    REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `inv((M:real) pow 10) * M pow 22 = M pow 12` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[LOG_POW] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[LOG_POW] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&1 + &22 * &k) * M) pow 3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&1 <= M /\ y <= &22 * &k * M ==> &1 + y <= (&1 + &22 * &k) * M`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + &22 * &k) pow 2 * M pow 2) pow 2 =
                ((&1 + &22 * &k) * (M:real)) pow 4` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL; REAL_POW_POW] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= M /\ &0 <= x * M ==> &1 <= (&1 + x) * M`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[REAL_LE_MUL; REAL_POS] THEN ASM_REAL_ARITH_TAC);;

let BV_LARGE_PART = prove
 (`!A x L M D R0 J.
     8 <= x /\ log(&x) = L /\ &1 <= L /\ L pow (A + 1) = M /\
     &D * M pow 23 <= sqrt(&x) /\ M pow 10 < &R0 + &1 /\ 1 <= R0 /\
     &2 * L * M pow 10 <= &J /\ &J + &1 <= &4 * M pow 11
     ==> bv_sum (R0 + 1) D (\c. norm(vsum {p | prime p /\ p <= x} c))
         <= &2 * ((&26 + &88 * &(A + 1) +
                   &1328 * (&1 + &22 * &(A + 1)) pow 2 +
                   &48 * (&2 * &(25 * (A + 1))) pow (25 * (A + 1)) +
                   &96 * (&2 * &(A + 1)) pow (A + 1)) * &x / M +
                  &D * (sqrt(&x) * L pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A + 1`; `L:real`; `M:real`] BV_PARAM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `KK = &26 + &88 * &(A + 1) +
                   &1328 * (&1 + &22 * &(A + 1)) pow 2 +
                   &48 * (&2 * &(25 * (A + 1))) pow (25 * (A + 1)) +
                   &96 * (&2 * &(A + 1)) pow (A + 1)` THEN
  SUBGOAL_THEN `&0 < M /\ &0 <= sqrt(&x) /\ sqrt(&x) pow 2 = &x /\ &1 <= &x`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[SQRT_POS_LE; REAL_POS];
      SIMP_TAC[SQRT_POW_2; REAL_POS];
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= KK` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= KK * &x / M + &D * (sqrt(&x) * L pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `D <= R0:num` THENL
   [REWRITE_TAC[bv_sum] THEN
    SUBGOAL_THEN `sum(R0 + 1..D) (\r. inv(&(phi r)) *
                    sum {c | primitive_character r c}
                      (\c. norm(vsum {p | prime p /\ p <= x} c))) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  MATCH_MP_TAC PI_THETA_WEIGHTED THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &n /\ &n <= &x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&n) <= L /\ &0 <= log(&n)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> rhs(concl th) = `L:real`)) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `bv_sum (R0 + 1) D
                (\c. norm(vsum(1..n) (\m. Cx(mangoldt m) * c m))) +
              &D * (sqrt(&n) * log(&n) pow 2)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC THETA_PSI_BV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS; REAL_LE_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]]] THEN
  MP_TAC(SPECL [`n:num`; `(M:real) pow 22`; `(M:real) pow 22`;
                `inv((M:real) pow 10)`; `J:num`; `R0 + 1`; `D:num`; `L:real`;
                `(&1 + &22 * &(A + 1)) pow 2 * (M:real) pow 2`]
               BV_PSI_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&x:real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BV_GRID_COVER THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
      ASM_ARITH_TAC;
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  EXPAND_TAC "KK" THEN MATCH_MP_TAC BV_PSI_ARITH THEN
  EXISTS_TAC `sqrt(&x)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 <= &D /\ &D <= &x` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&D * M pow 23` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POS] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[SQRT_POS_LE; REAL_POS];
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POS];
    REWRITE_TAC[REAL_POS];
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = `L:real`)) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = `L:real`)) THEN
    SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&1 <= x ==> &0 < x`;
             ASSUME `&1 <= &x`] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&x + &1` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `&8 <= &x` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&x * &2` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_LE_POW_2];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = `M:real`)) THEN
    REWRITE_TAC[REAL_POW_POW] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = `L:real`)) THEN
    ONCE_REWRITE_TAC[ARITH_RULE `(A + 1) * 25 = 25 * (A + 1)`] THEN
    MATCH_MP_TAC LOG_POW_LE_SQRT THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = `M:real`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = `L:real`)) THEN
    MATCH_MP_TAC LOG_POW_LE_SQRT THEN ASM_REWRITE_TAC[]]);;

let BV_FINAL_ARITH = prove
 (`!A L M x sx D R0 CS KK lD.
     &1 <= L /\ L pow (A + 1) = M /\ &1 <= x /\ &0 <= sx /\ sx pow 2 = x /\
     &1 <= D /\ D * M pow 23 <= sx /\ &0 <= R0 /\ R0 <= M pow 10 /\
     &0 <= CS /\ &0 <= KK /\ &0 <= lD /\ lD <= L
     ==> &4 * (&1 + lD) *
         (R0 * CS * x / L pow (11 * (A + 1)) +
          &2 * (KK * x / M + D * (sx * L pow 2))) +
         &2 * D pow 2 * lD / log(&2)
         <= (&8 * (CS + &2 * KK + &2) + &4) * x / L pow A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < L /\ L <= M /\ &1 <= M /\ &0 < M` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `L <= M` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> rhs(concl th) = `M:real`)) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real) / L pow A = x * L / M /\
                L pow (11 * (A + 1)) = (M:real) pow 11` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rhs(concl th) = `M:real`)) THEN
    REWRITE_TAC[REAL_POW_POW] THEN
    REWRITE_TAC[ARITH_RULE `(A + 1) * 11 = 11 * (A + 1)`] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= sx /\ sx <= x` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= sx` ASSUME_TAC THENL
     [ASM_CASES_TAC `sx < &1` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `sx pow 2 <= sx * &1` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sx * &1 <= sx * sx` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RID; GSYM REAL_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `D <= sx / M pow 23` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `R0 * CS * x / M pow 11 <= CS * (x / M)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(M pow 10 * CS * x / M pow 11):real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `D * (sx * L pow 2) <= x / M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((sx:real) / M pow 23) * (sx * M pow 22)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(M:real) pow 2` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o
        check (fun th -> rhs(concl th) = `x:real`)) THEN
      UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC LOG_2_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `lD / log(&2) <= &2 * L` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 / &2 <= l ==> &0 < l`] THEN
    SUBGOAL_THEN `&0 <= L * (&2 * log(&2) - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `D pow 2 <= x / M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((sx:real) / M pow 23) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_POW_DIV] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_POW] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x / M /\ &0 <= x * L / M` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * D pow 2 * lD / log(&2) <= &4 * (x * L / M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * ((x:real) / M) * (&2 * L)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 * (&1 + lD) *
    (R0 * CS * x / M pow 11 + &2 * (KK * x / M + D * (sx * L pow 2)))
    <= &8 * (CS + &2 * KK + &2) * (x * L / M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * (&2 * L) * ((CS + &2 * KK + &2) * ((x:real) / M))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REPEAT(FIRST [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC;
                      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC]) THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LE_POW_2; REAL_POW_LE; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `KK * x / M = KK * ((x:real) / M)` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BV_TRIVIAL = prove
 (`!x a D. sum(1..D) (\d. abs(&(CARD {p | prime p /\ p <= x /\
                                        (p == a d) (mod d)}) -
                             &(CARD {p | prime p /\ p <= x}) / &(phi d)))
           <= &2 * &D * &x`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..D) (\d. &2 * &x)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(CARD {p | prime p /\ p <= x /\ (p == a d) (mod d)}) <= &x /\
                &(CARD {p | prime p /\ p <= x}) <= &x /\
                &1 <= &(phi d)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..x)` THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]] THEN
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..x)` THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]] THEN
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= a /\ a <= x /\ &0 <= b /\ b <= x ==> abs(a - b) <= &2 * x`) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&x:real` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]]);;

let BV_SMALL_X = prove
 (`!A x D (a:num->num) C0.
     2 <= x /\ x < 8 /\ &D <= sqrt(&x) / log(&x) pow (23 * (A + 1)) /\
     &0 <= C0
     ==> sum(1..D) (\d. abs(&(CARD {p | prime p /\ p <= x /\
                                       (p == a d) (mod d)}) -
                            &(CARD {p | prime p /\ p <= x}) / &(phi d)))
         <= (&6 * &2 pow (23 * (A + 1)) * &8 pow A + C0) * &x /
            log(&x) pow A`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * &D * &x` THEN REWRITE_TAC[BV_TRIVIAL] THEN
  MP_TAC LOG_2_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= log(&x) /\ log(&x) <= &8` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&x:real` THEN
      CONJ_TAC THENL
       [MP_TAC(SPEC `&x - &1` LOG_LE) THEN
        REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x:real`] THEN
        ANTS_TAC THENL
         [REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
          REAL_ARITH_TAC];
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&x)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&D <= &3 * &2 pow (23 * (A + 1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&x) / log(&x) pow (23 * (A + 1))` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&x) pow A <= &8 pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&x) pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 <= c ==> a <= b + c`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE]] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&6 * &2 pow (23 * (A + 1)) * &x` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&6 * &2 pow (23 * (A + 1)) * &x =
                  &2 * (&3 * &2 pow (23 * (A + 1))) * &x` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a * b / c = (a * b) / c:real`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `(&6 * &2 pow (23 * (A + 1)) * &8 pow A) * &x =
                (&6 * &2 pow (23 * (A + 1)) * &x) * &8 pow A`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  SIMP_TAC[REAL_POS; REAL_POW_LE]);;

let pi_upto = new_definition
 `pi_upto x = CARD {p | prime p /\ p <= x}`;;

let pi_ap = new_definition
 `pi_ap x d a = CARD {p | prime p /\ p <= x /\ (p == a) (mod d)}`;;

let BOMBIERI_VINOGRADOV = prove
 (`!A. ?B C. !x a.
        2 <= x /\ (!d. coprime(a d,d))
        ==> sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                (\d. abs(&(pi_ap x d (a d)) - &(pi_upto x) / &(phi d)))
            <= C * &x / log(&x) pow A`,
  REWRITE_TAC[pi_ap; pi_upto] THEN X_GEN_TAC `A:num` THEN
  MP_TAC(SPECL [`11 * (A + 1)`; `10 * (A + 1)`] BV_SMALL_PART) THEN
  DISCH_THEN(X_CHOOSE_THEN `CS:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `KK = &26 + &88 * &(A + 1) +
                   &1328 * (&1 + &22 * &(A + 1)) pow 2 +
                   &48 * (&2 * &(25 * (A + 1))) pow (25 * (A + 1)) +
                   &96 * (&2 * &(A + 1)) pow (A + 1)` THEN
  SUBGOAL_THEN `&0 <= KK` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `23 * (A + 1)` THEN
  EXISTS_TAC `&6 * &2 pow (23 * (A + 1)) * &8 pow A +
              (&8 * (CS + &2 * KK + &2) + &4)` THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `a:num->num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `sqrt(&x) / log(&x) pow (23 * (A + 1))` NUMSEG_REAL_FLOOR) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &8 * (CS + &2 * KK + &2) + &4` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `x < 8` THENL
   [MATCH_MP_TAC BV_SMALL_X THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ABBREV_TAC `L = log(&x)` THEN
  SUBGOAL_THEN `&1 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&8)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `log(&8) = &3 * log(&2)` SUBST1_TAC THENL
       [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `M = (L:real) pow (A + 1)` THEN
  SUBGOAL_THEN `&1 <= M /\ L <= M` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real) pow (23 * (A + 1)) = M pow 23 /\
                (L:real) pow (10 * (A + 1)) = M pow 10`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[REAL_POW_POW] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &x / L pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `D = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `~(1 = 0)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  MP_TAC(SPEC `(M:real) pow 10` FLOOR_POS) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `R0:num`) THEN
  MP_TAC(SPEC `(M:real) pow 10` FLOOR) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= M pow 10 /\ &1 <= M pow 11` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= R0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &R0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&2 * L * (M:real) pow 10` FLOOR_POS) THEN ANTS_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `J0:num`) THEN
  MP_TAC(SPEC `&2 * L * (M:real) pow 10` FLOOR) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&D * M pow 23 <= sqrt(&x)` ASSUME_TAC THENL
   [UNDISCH_TAC `&D <= sqrt (&x) / L pow (23 * (A + 1))` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT;
                 REAL_ARITH `&1 <= M ==> &0 < M`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * (&1 + log(&D)) *
              bv_sum 2 D (\c. norm(vsum {p | prime p /\ &p <= &x} c)) +
              &2 * &D pow 2 * log(&D) / log(&2)` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC BV_AP_TOTAL THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * (&1 + log(&D)) *
              (&R0 * CS * &x / L pow (11 * (A + 1)) +
               &2 * (KK * &x / M + &D * (sqrt(&x) * L pow 2))) +
              &2 * &D pow 2 * log(&D) / log(&2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c:real`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &0 <= &1 + y`) THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `bv_sum 2 R0 (\c. norm(vsum {p | prime p /\ &p <= &x} c)) +
                bv_sum (R0 + 1) D
                  (\c. norm(vsum {p | prime p /\ &p <= &x} c))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BV_SUM_SPLIT_LE THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [EXPAND_TAC "L" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[PRIMES_LE_REAL] THEN EXPAND_TAC "KK" THEN
      MATCH_MP_TAC BV_LARGE_PART THEN
      EXISTS_TAC `J0 + 1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&2 * L * M pow 10 <= &2 * M pow 11` MP_TAC THENL
       [REWRITE_TAC[ARITH_RULE `11 = SUC 10`; real_pow] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN
                        ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&8 * (CS + &2 * KK + &2) + &4) * &x / L pow A` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BV_FINAL_ARITH THEN
    ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      SIMP_TAC[SQRT_POS_LE; REAL_POS];
      SIMP_TAC[SQRT_POW_2; REAL_POS];
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      EXPAND_TAC "L" THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&D * M pow 23` THEN
        ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LSQRT THEN
        REWRITE_TAC[REAL_POS; REAL_OF_NUM_POW; REAL_OF_NUM_LE; EXP_2;
                    LE_SQUARE_REFL]]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= a + b:real`) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE]]);;
