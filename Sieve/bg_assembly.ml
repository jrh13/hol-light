(* ========================================================================= *)
(* Bounded gaps between primes, part 5: assembling the bounds.               *)
(*                                                                           *)
(* * S1_ASSEMBLED: S1 <= (N/W) (Gamma^k + prod_P (1 + k u) (exp(k^2 eta) -   *)
(*   1)) + 2 (R prod_P (1 + 3 k / p))^2 (S1_TOTAL, S1_MAIN_TERM,             *)
(*   S1_WEIGHT_UPPER, RANKIN_COL_SET).                                       *)
(* * S2_ASSEMBLED: S2(m) is at least (pi(x2) - pi(x1)) / prod_{p <= D0}      *)
(*   (p - 1) times the main term minus E2, minus (prod_P (1 + u) prod_P (1 + *)
(*   k u))^2 sum_t (k + 1)^(2|t|) (bv_disc x2 + bv_disc x1).                 *)
(* * BV_ASSEMBLED: the discrepancy sum at one x is at most M C x / log^A x + *)
(*   3 x / prod_{p <= D0} (p - 1) prod_P (1 + (k + 1)^4 u) / M (an M versus  *)
(*   w^2 / M split per modulus, Bombieri-Vinogradov and BV_DISC_TRIVIAL).    *)
(* * PNT_DIFF: N / (4 log N) <= pi(2 N + h - 1) - pi(N + h - 1) and          *)
(*   pi(2 N + h - 1) <= 4 N / log N, uniformly in h <= H, for N large.       *)
(* * The admissible tuple h i = i k! with nu = prod_{k < q <= D0} q          *)
(*   (TUPLE_NU_OK, TUPLE_MAYNARD_HDIST); MANY_PRIMES_WEIGHTS: if the weights *)
(*   are >= 0 and sum_m S2(m) > r S1, some n has at least r + 1 primes among *)
(*   the n + h i.                                                            *)
(* * MAYNARD_GDY_FACTS collects the weight bounds for G = maynard_gdy J l0   *)
(*   in terms of s = c0 l0; F1_MAIN (the main terms of sum_m S2(m) are at    *)
(*   least 3 r (N/W) Gamma^k when 300 r K Kp <= (J - 1)^2) and F2_LEMMA ...  *)
(*   F5_LEMMA (each error term is <= (N/W) Gamma^k / 10, under explicit      *)
(*   conditions on D0 and N).                                                *)
(* ========================================================================= *)

needs "Sieve/bg_dyadic.ml";;
needs "Sieve/chen_sb.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The upper bound for S1.                                                   *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_DIFF_EXP = prove
 (`!(f:A->real) g e s.
     FINITE s /\
     (!x. x IN s ==> &1 <= f x /\ f x <= g x /\ g x <= f x * (&1 + e x) /\
                     &0 <= e x)
     ==> product s g - product s f <= product s f * (exp(sum s e) - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `product s g <= product s f * exp(sum s (e:A->real))` MP_TAC
  THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product s (\x. (f:A->real) x * (&1 + e x))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_MUL; REAL_EXP_SUM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[REAL_EXP_LE_X] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let S1_E1_BOUND = prove
 (`!k P. FINITE P /\ (!p. p IN P ==> 2 <= p)
         ==> product P (\p. &1 + &k * (inv(&p - &1) +
                                      (&k - &1) * inv(&p - &1) pow 2)) -
             product P (\p. &1 + &k * inv(&p - &1))
             <= product P (\p. &1 + &k * inv(&p - &1)) *
                (exp(&k pow 2 * sum P (\p. inv(&p - &1) pow 2)) - &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC PRODUCT_DIFF_EXP THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= inv(&p - &1)` MP_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`inv(&p - &1)`,`v:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= &k * (&k - &1)` ASSUME_TAC THENL
   [ASM_CASES_TAC `k = 0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&k * (&k - &1)) * v pow 2 /\ &0 <= &k * v /\
                &0 <= (&k * v) pow 3 /\ &0 <= &k * v pow 2 /\
                &0 <= &k pow 2 * v pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `&0 <= (&k * (&k - &1)) * v pow 2` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 <= (&k * v) pow 3` THEN
    UNDISCH_TAC `&0 <= &k * v pow 2` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let COL_WEIGHT_BOUNDS = prove
 (`!G k c. (!r. &0 <= G r /\ G r <= &1)
           ==> &0 <= col_weight G k c /\ col_weight G k c <= &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[col_weight] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG];
    MATCH_MP_TAC PRODUCT_LE_1 THEN ASM_SIMP_TAC[FINITE_NUMSEG]]);;

let S1_COMBINE = prove
 (`!S M D E Eb G c Er Erb.
     &0 <= c /\ E <= Eb /\ D <= G /\ abs(M - D) <= E /\
     abs(S - c * M) <= &2 * Er /\ Er <= Erb
     ==> S <= c * (G + Eb) + &2 * Erb`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c * M <= c * (G + Eb)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let S1_ASSEMBLED = prove
 (`!h k P R W nu N (G:num->real).
     1 <= W /\ FINITE P /\ (!p. p IN P ==> prime p /\ ~(p divides W)) /\
     maynard_hdist h k P /\ (!r. &0 <= G r /\ G r <= &1) /\ &0 < R
     ==> sum {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}
             (\n. sum {c | c IN col_set k P /\
                           &(nproduct (col_supp c) (\p. p)) < R}
                      (\c. col_weight G k c / product (col_supp c)
                             (\p. &p - &1) *
                           product (col_supp c)
                             (\p. maynard_lfac h c p n)) pow 2)
         <= &N / &W *
            (sum {A | A SUBSET P}
                 (\A. G(nproduct A (\p. p)) pow 2 *
                      product A (\p. inv(&p - &1))) pow k +
             product P (\p. &1 + &k * inv(&p - &1)) *
             (exp(&k pow 2 * sum P (\p. inv(&p - &1) pow 2)) - &1)) +
            &2 * (R * product P (\p. &1 + &k * (&3 / &p))) pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `fam = {c | c IN col_set k P /\
                         &(nproduct (col_supp c) (\p:num. p)) < R}` THEN
  SUBGOAL_THEN `fam SUBSET col_set k P /\ FINITE(fam:(num->num)->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "fam" THEN CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[FINITE_COL_SET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. c IN fam ==> FINITE(col_supp c) /\ col_supp c SUBSET P`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `col_supp c SUBSET P` ASSUME_TAC THENL
     [SUBGOAL_THEN `(c:num->num) IN col_set k P` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ASM_MESON_TAC[FINITE_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> 2 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. &0 < product (col_supp c) (\p. &p - &1) \/ ~(c IN fam)`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:num->num` THEN ASM_CASES_TAC `(c:num->num) IN fam` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->num`; `W:num`; `nu:num`; `N:num`;
                 `fam:(num->num)->bool`;
                 `\c. col_weight (G:num->real) k c /
                      product (col_supp c) (\p. &p - &1)`] S1_TOTAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`c:num->num`; `c':num->num`; `p:num`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `maynard_hdist h k P` THEN REWRITE_TAC[maynard_hdist] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:num->num) IN col_set k P /\ (c':num->num) IN col_set k P`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(p:num) IN col_supp c` THEN
    UNDISCH_TAC `(p:num) IN col_supp c'` THEN
    REWRITE_TAC[col_set; col_supp; IN_ELIM_THM; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THENL
     [ASM SET_TAC[]; ASM_ARITH_TAC; ASM_MESON_TAC[]; ASM_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `P:num->bool`; `fam:(num->num)->bool`;
                 `col_weight (G:num->real) k`; `&1`] S1_MAIN_TERM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`G:num->real`; `k:num`; `c:num->num`] COL_WEIGHT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `P:num->bool`; `fam:(num->num)->bool`;
                 `G:num->real`] S1_WEIGHT_UPPER) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `P:num->bool`] S1_E1_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM col_weight; REAL_POW_ONE; REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `sum fam (\c. sum fam (\c'.
      abs(col_weight (G:num->real) k c / product (col_supp c) (\p. &p - &1)) *
      abs(col_weight G k c' / product (col_supp c') (\p. &p - &1)) *
      &3 pow CARD(col_supp c UNION col_supp c') *
      product (col_supp c) (\p. &p - &1) *
      product (col_supp c') (\p. &p - &1)))
    <= (R * product P (\p. &1 + &k * &3 / &p)) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum fam (\c:num->num. &3 pow CARD(col_supp c)) pow 2` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_2; REAL_MUL_SUM] THEN
      MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `c':num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`G:num->real`; `k:num`; `c:num->num`]
               COL_WEIGHT_BOUNDS) THEN
      MP_TAC(SPECL [`G:num->real`; `k:num`; `c':num->num`]
               COL_WEIGHT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < product (col_supp c) (\p. &p - &1) /\
                    &0 < product (col_supp c') (\p. &p - &1)`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&3 pow CARD(col_supp c UNION col_supp c') <=
                    &3 pow CARD(col_supp c) * &3 pow CARD(col_supp c')`
      MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_POW_ADD] THEN MATCH_MP_TAC REAL_POW_MONO THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC CARD_UNION_LE THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPEC `CARD(col_supp c UNION col_supp c')`
             (SPEC `&3` REAL_POW_LE)) THEN
      SPEC_TAC(`&3 pow CARD(col_supp c UNION col_supp c')`,`t:real`) THEN
      SPEC_TAC(`product (col_supp c) (\p. &p - &1)`,`a:real`) THEN
      SPEC_TAC(`product (col_supp c') (\p. &p - &1)`,`b:real`) THEN
      SPEC_TAC(`col_weight (G:num->real) k c`,`y:real`) THEN
      SPEC_TAC(`col_weight (G:num->real) k c'`,`z:real`) THEN
      REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH `&0 <= &3`] THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < a ==> abs a = a`;
                   REAL_ARITH `&0 <= y ==> abs y = y`] THEN
      SUBGOAL_THEN `(y:real) / a * z / b * t * a * b = (y * z) * t`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < b` THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `t:real` THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `y * z <= &1 * &1 ==> y * z <= &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `P:num->bool`; `R:real`; `&3`] RANKIN_COL_SET) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[ARITH_RULE `2 <= p ==> 1 <= p`];
                      REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Ns = {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}` THEN
  ABBREV_TAC `PS = {A:num->bool | A SUBSET P}` THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC S1_COMBINE THEN
  MAP_EVERY EXISTS_TAC
   [`sum fam (\c. sum fam (\c'.
       col_weight (G:num->real) k c / product (col_supp c) (\p. &p - &1) *
       col_weight G k c' / product (col_supp c') (\p. &p - &1) *
       col_corr c c'))`;
    `sum fam (\c. col_weight (G:num->real) k c pow 2 /
                  product (col_supp c) (\p. &p - &1))`;
    `product P (\p. &1 + &k * (inv(&p - &1) +
                              (&k - &1) * inv(&p - &1) pow 2)) -
     product P (\p. &1 + &k * inv(&p - &1))`;
    `sum fam (\c. sum fam (\c'.
      abs(col_weight (G:num->real) k c / product (col_supp c) (\p. &p - &1)) *
      abs(col_weight G k c' / product (col_supp c') (\p. &p - &1)) *
      &3 pow CARD(col_supp c UNION col_supp c') *
      product (col_supp c) (\p. &p - &1) *
      product (col_supp c') (\p. &p - &1)))`]
  THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* The lower bound for S2.                                                   *)
(* ------------------------------------------------------------------------- *)

let S2_E2_BOUND = prove
 (`!k P. FINITE P /\ (!p. p IN P ==> 2 <= p) /\ 1 <= k
         ==> (&1 * product P (\p. &1 + inv(&p - &1))) pow 2 *
             (product P (\p. &1 + (&k - &1) *
                (&2 * inv(&p - &1) pow 2 +
                 (inv(&p - &1) + inv(&p - &1) pow 2) +
                 (&k - &2) * (&3 * inv(&p - &1) pow 2))) -
              product P (\p. &1 + (&k - &1) *
                                  (inv(&p - &1) + inv(&p - &1) pow 2)))
             <= product P (\p. &1 + inv(&p - &1)) pow (k + 1) *
                exp(&k * sum P (\p. inv(&p - &1) pow 2)) *
                (exp(&3 * &k pow 2 * sum P (\p. inv(&p - &1) pow 2)) - &1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `eta = sum P (\p. inv(&p - &1) pow 2)` THEN
  SUBGOAL_THEN `&0 <= eta` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> &0 <= inv(&p - &1)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ABBREV_TAC `D3 = product P (\p. &1 + (&k - &1) *
                                     (inv(&p - &1) + inv(&p - &1) pow 2))` THEN
  ABBREV_TAC `Q = product P (\p. &1 + inv(&p - &1))` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> &0 <= &1 + x`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product P (\p. &1 + (&k - &1) *
       (&2 * inv(&p - &1) pow 2 + (inv(&p - &1) + inv(&p - &1) pow 2) +
        (&k - &2) * (&3 * inv(&p - &1) pow 2))) - D3
    <= D3 * (exp(&3 * &k pow 2 * eta) - &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "D3" THEN EXPAND_TAC "eta" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC PRODUCT_DIFF_EXP THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
      can (find_term ((=) `inv:real->real`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`inv(&p - &1)`,`v:real`) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&k - &1) * (&3 * &k - &4)` MP_TAC THENL
     [ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      SUBGOAL_THEN `&2 <= &k` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `&1 <= &k` THEN SPEC_TAC(`&k:real`,`a:real`) THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (a - &1) * (v + v pow 2) /\
                  &0 <= ((a - &1) * (&3 * a - &4)) * v pow 2 /\
                  &0 <= (&7 * a - &4) * v pow 2 /\
                  &0 <= &3 * a pow 2 * v pow 2 /\
                  &0 <= (&3 * a pow 2 * v pow 2) * ((a - &1) * (v + v pow 2))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= (a - &1) * (v + v pow 2)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &3 * a pow 2 * v pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN
                          REWRITE_TAC[REAL_LE_POW_2]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `D3 <= Q pow (k - 1) * exp(&k * eta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product P (\p. &1 + &(k - 1) * inv(&p - &1)) *
                product P (\p. &1 + &(k - 1) * inv(&p - &1) pow 2)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "D3" THEN
      SIMP_TAC[GSYM PRODUCT_MUL; ASSUME `FINITE(P:num->bool)`] THEN
      MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
        can (find_term ((=) `inv:real->real`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`inv(&p - &1)`,`v:real`) THEN GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (&k - &1) * (v + v pow 2) /\
                    &0 <= (&k - &1) pow 2 * v pow 3`
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POW_LE; REAL_LE_ADD] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`)
      THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS];
      EXPAND_TAC "Q" THEN MATCH_MP_TAC PRODUCT_BERNOULLI THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`)
      THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(sum P (\p. &(k - 1) * inv(&p - &1) pow 2))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_LE THEN
      ASM_REWRITE_TAC[REAL_EXP_LE_X] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; SUM_LMUL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= exp(&3 * &k pow 2 * eta) - &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `&3 * &k pow 2 * eta` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `&0 <= &3 * &k pow 2 * eta` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real) pow (k + 1) = Q pow 2 * Q pow (k - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Q pow 2 * D3 * (exp(&3 * &k pow 2 * eta) - &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

let S2_COMBINE = prove
 (`!c S ML D Tm E Eb Wl Er.
     &0 <= c
     ==> abs(S - c * ML) <= Er ==> ML = D ==> Tm - E <= D ==> Wl <= Tm ==>
         E <= Eb ==> c * (Wl - Eb) - Er <= S`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c * (Wl - Eb) <= c * ML` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let S2_ASSEMBLED = prove
 (`!h k m Wp P nu N R Rt (G:num->real).
     FINITE Wp /\ (!p. p IN Wp ==> prime p) /\
     FINITE P /\ (!p. p IN P ==> prime p) /\ DISJOINT Wp P /\
     maynard_hdist h k P /\ m IN 1..k /\
     (!p. p IN Wp ==> ~(p divides nu + h m)) /\ 1 <= N /\
     (!p. p IN P ==> p < N) /\
     (!r. &0 <= G r /\ G r <= &1) /\
     (!r s. 1 <= r /\ r <= s ==> G s <= G r) /\
     (!r. Rt <= &r ==> G r = &0) /\ &1 < Rt /\ Rt < R
     ==> ?a. (!d. coprime(a d,d)) /\
             (&(pi_upto ((2 * N + h m) - 1)) - &(pi_upto ((N + h m) - 1))) /
             product Wp (\p. &p - &1) *
             (sum {A | A SUBSET P}
                  (\A. G(nproduct A (\p. p)) *
                       product A (\p. inv(&p - &1))) pow 2 *
              (sum {A | A SUBSET P}
                   (\A. G(nproduct A (\p. p)) pow 2 *
                        product A (\p. inv(&p - &1))) pow (k - 1) *
               (&1 - (&k - &1) pow 2 * sum P (\p. inv(&p - &1) pow 2) -
                &2 * (&k - &1) * sum P (\p. inv(&p - &1) pow 2)) -
               (&k - &1) *
               sum {A | A SUBSET P}
                   (\A. (G(nproduct A (\p. p)) pow 2 *
                         product A (\p. inv(&p - &1))) *
                        log(&(nproduct A (\p. p)))) *
               sum {A | A SUBSET P}
                   (\A. G(nproduct A (\p. p)) pow 2 *
                        product A (\p. inv(&p - &1))) pow (k - 2) /
               log(R / Rt)) -
              product P (\p. &1 + inv(&p - &1)) pow (k + 1) *
              exp(&k * sum P (\p. inv(&p - &1) pow 2)) *
              (exp(&3 * &k pow 2 * sum P (\p. inv(&p - &1) pow 2)) - &1)) -
             (product P (\p. &1 + inv(&p - &1)) *
              product P (\p. &1 + &k * inv(&p - &1))) pow 2 *
             sum {t | t SUBSET P /\ &(nproduct t (\p. p)) < R pow 2}
                 (\t. (&k + &1) pow (2 * CARD t) *
                      (bv_disc ((2 * N + h m) - 1)
                              (nproduct (Wp UNION t) (\p. p))
                              (a (nproduct (Wp UNION t) (\p. p))) +
                       bv_disc ((N + h m) - 1) (nproduct (Wp UNION t) (\p. p))
                              (a (nproduct (Wp UNION t) (\p. p)))))
             <= sum {n | n IN {n | N <= n /\ n < 2 * N /\
                                   (n == nu) (mod (nproduct Wp (\p. p)))} /\
                         prime(n + h m)}
                    (\n. sum {c | c IN col_set k P /\
                                  &(nproduct (col_supp c) (\p. p)) < R}
                             (\c. col_weight G k c /
                                  product (col_supp c) (\p. &p - &1) *
                                  product (col_supp c)
                                    (\p. maynard_lfac h c p n))
                         pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `fam = {c | c IN col_set k P /\
                         &(nproduct (col_supp c) (\p:num. p)) < R}` THEN
  SUBGOAL_THEN `fam SUBSET col_set k P` ASSUME_TAC THENL
   [EXPAND_TAC "fam" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> 2 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->num`; `k:num`; `m:num`; `Wp:num->bool`;
                 `P:num->bool`; `nu:num`; `N:num`; `fam:(num->num)->bool`;
                 `\c. col_weight (G:num->real) k c /
                      product (col_supp c) (\p. &p - &1)`;
                 `product P (\p. &1 + inv(&p - &1)) *
                  product P (\p. &1 + &k * inv(&p - &1))`;
                 `R:real`] S2_ERROR_SUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "fam" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `P:num->bool`; `fam:(num->num)->bool`;
                   `col_weight (G:num->real) k`; `&1`; `c:num->num`]
           MAYNARD_LAMBDA_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `d:num->num` THEN DISCH_TAC THEN
        MP_TAC(SPECL [`G:num->real`; `k:num`; `d:num->num`]
               COL_WEIGHT_BOUNDS) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `a:num->num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 <= (&(pi_upto ((2 * N + (h:num->num) m) - 1)) -
           &(pi_upto ((N + h m) - 1))) / product Wp (\p. &p - &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC PI_UPTO_MONO THEN ARITH_TAC;
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `2 <= p` MP_TAC THENL
       [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `P:num->bool`] S2_E2_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `R:real`; `Rt:real`;
                 `G:num->real`] S2_WEIGHT_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `fam:(num->num)->bool`;
                 `col_weight (G:num->real) k`; `&1`] S2_MAIN_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`G:num->real`; `k:num`; `c:num->num`] COL_WEIGHT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->num`; `k:num`; `m:num`; `P:num->bool`;
                 `fam:(num->num)->bool`;
                 `\c. col_weight (G:num->real) k c /
                      product (col_supp c) (\p. &p - &1)`]
                        S2_MAIN_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `bv_disc`)) (concl th))) THEN
  EXPAND_TAC "fam" THEN
  MATCH_ACCEPT_TAC(MATCH_MP S2_COMBINE (ASSUME
   `&0 <= (&(pi_upto ((2 * N + (h:num->num) m) - 1)) -
           &(pi_upto ((N + h m) - 1))) / product Wp (\p. &p - &1)`)));;

(* ------------------------------------------------------------------------- *)
(* The Bombieri-Vinogradov error.                                            *)
(* ------------------------------------------------------------------------- *)

let BV_ASSEMBLED = prove
 (`!Wp P k R x (a:num->num) M B Cb A.
     FINITE Wp /\ (!p. p IN Wp ==> prime p) /\
     FINITE P /\ (!p. p IN P ==> prime p) /\ DISJOINT Wp P /\
     &0 < M /\
     sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
         (\d. abs(&(pi_ap x d (a d)) - &(pi_upto x) / &(phi d)))
     <= Cb * &x / log(&x) pow A /\
     &(nproduct Wp (\p. p)) * R pow 2 <= sqrt(&x) / log(&x) pow B /\
     sqrt(&x) / log(&x) pow B <= &x
     ==> sum {t | t SUBSET P /\ &(nproduct t (\p. p)) < R pow 2}
             (\t. (&k + &1) pow (2 * CARD t) *
                  bv_disc x (nproduct (Wp UNION t) (\p. p))
                         (a (nproduct (Wp UNION t) (\p. p))))
         <= M * (Cb * &x / log(&x) pow A) +
            &3 * &x / product Wp (\p. &p - &1) *
            product P (\p. &1 + (&k + &1) pow 4 * inv(&p - &1)) / M`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ts = {t | t SUBSET P /\
                     &(nproduct t (\p:num. p)) < R pow 2}` THEN
  ABBREV_TAC `dd = \t. nproduct (Wp UNION t) (\p:num. p)` THEN
  SUBGOAL_THEN `FINITE(Ts:(num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:num->bool | t SUBSET P}` THEN
    SIMP_TAC[FINITE_POWERSET; ASSUME `FINITE(P:num->bool)`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN Ts
        ==> FINITE t /\ t SUBSET P /\
            (!p. p IN Wp UNION t ==> prime p) /\ FINITE(Wp UNION t) /\
            1 <= (dd:(num->bool)->num) t /\
            &(dd t) <= sqrt(&x) / log(&x) pow B /\ dd t <= x /\
            &(phi(dd t)) = product Wp (\p. &p - &1) *
                           product t (\p. &p - &1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:num->bool` THEN EXPAND_TAC "Ts" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT Wp (t:num->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT Wp (P:num->bool)` THEN
      UNDISCH_TAC `t SUBSET (P:num->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(!p. p IN Wp UNION t ==> prime p)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(nproduct (Wp UNION t) (\p:num. p)) <=
                  sqrt(&x) / log(&x) pow B`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(nproduct Wp (\p:num. p)) * R pow 2` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[NPRODUCT_UNION] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
      MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `2 <= p ==> 0 < p`) THEN
      MATCH_MP_TAC PRIME_GE_2 THEN ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_PHI_NPRODUCT_PRIMES; FINITE_UNION] THEN
      ASM_SIMP_TAC[PRODUCT_UNION]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum Ts (\t. M * bv_disc x ((dd:(num->bool)->num) t) (a (dd t)) +
                ((&k + &1) pow (2 * CARD t)) pow 2 *
                bv_disc x (dd t) (a (dd t)) / M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC W_M_TRICK THEN
    ASM_REWRITE_TAC[BV_DISC_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                    (\d. bv_disc x d (a d))` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[bv_disc] THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (IMAGE (dd:(num->bool)->num) Ts) (\d. bv_disc x d (a d))`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
      ANTS_TAC THENL
       [MAP_EVERY X_GEN_TAC [`t1:num->bool`; `t2:num->bool`] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `Wp UNION t1 = Wp UNION (t2:num->bool)` MP_TAC THENL
         [MATCH_MP_TAC NPRODUCT_PRIMES_INJ THEN
          UNDISCH_TAC `(dd:(num->bool)->num) t1 = dd t2` THEN
          EXPAND_TAC "dd" THEN REWRITE_TAC[] THEN DISCH_TAC THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(t1:num->bool) IN Ts` THEN
        UNDISCH_TAC `(t2:num->bool) IN Ts` THEN EXPAND_TAC "Ts" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        UNDISCH_TAC `DISJOINT Wp (P:num->bool)` THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[BV_DISC_POS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..x` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      X_GEN_TAC `d:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Ts (\t. (&3 * &x / product Wp (\p. &p - &1) / M) *
                          product t (\p. (&k + &1) pow 4 * inv(&p - &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:num->bool` o check (fun th ->
      can (find_term ((=) `phi`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`x:num`; `(dd:(num->bool)->num) t`;
                  `(a:num->num)((dd:(num->bool)->num) t)`]
                    BV_DISC_TRIVIAL) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&0 < product Wp (\p. &p - &1) /\ &0 < product t (\p. &p - &1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      (SUBGOAL_THEN `2 <= p` MP_TAC THENL
        [MATCH_MP_TAC PRIME_GE_2 THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
         ASM_REWRITE_TAC[IN_UNION];
         REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC]);
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_MUL; PRODUCT_CONST; PRODUCT_INV] THEN
    REWRITE_TAC[REAL_POW_POW; ARITH_RULE `(2 * n) * 2 = 4 * n`] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
    SUBGOAL_THEN `&0 <= ((&k + &1) pow 4) pow CARD(t:num->bool)` MP_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_POW_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`x:num`; `(dd:(num->bool)->num) t`;
                  `(a:num->num)((dd:(num->bool)->num) t)`] BV_DISC_POS) THEN
    UNDISCH_TAC `&0 < product Wp (\p. &p - &1)` THEN
    UNDISCH_TAC `&0 < product t (\p. &p - &1)` THEN
    SPEC_TAC(`((&k + &1) pow 4) pow CARD(t:num->bool)`,`w:real`) THEN
    SPEC_TAC(`bv_disc x ((dd:(num->bool)->num) t) (a (dd t))`,`g:real`) THEN
    SPEC_TAC(`product Wp (\p. &p - &1)`,`pw:real`) THEN
    SPEC_TAC(`product t (\p. &p - &1)`,`pt:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `(&3 * &x / pw / M) * w * inv pt = w * (&3 * &x / (pw * pt)) / M`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < M` THEN UNDISCH_TAC `&0 < pw` THEN
      UNDISCH_TAC `&0 < pt` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&3 * &x / product Wp (\p. &p - &1) / M) *
              product P (\p. &1 + (&k + &1) pow 4 * inv(&p - &1))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[real_div; REAL_MUL_AC; REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_ADD_EXPAND; ASSUME `FINITE(P:num->bool)`] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  SIMP_TAC[FINITE_POWERSET; ASSUME `FINITE(P:num->bool)`] THEN CONJ_TAC THENL
   [EXPAND_TAC "Ts" THEN SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_INV_EQ] THEN
  SUBGOAL_THEN `2 <= p` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Primes in [N + h, 2 N + h).                                               *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_LOG_GE_SEQUENTIALLY = prove
 (`!c. eventually (\N. c <= log(&N)) sequentially`,
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; EVENTUALLY_LOG_GE]);;

let PNT_DIFF = prove
 (`!H. eventually
         (\N. !h0. h0 <= H
                   ==> &N / (&4 * log(&N)) <=
                       &(pi_upto((2 * N + h0) - 1)) -
                       &(pi_upto((N + h0) - 1)) /\
                       &(pi_upto((2 * N + h0) - 1)) <= &4 * &N / log(&N))
         sequentially`,
  GEN_TAC THEN
  MP_TAC(SPEC `&1 / &20` PI_UPTO_ASYMPTOTIC) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 / &20`] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `&10` EVENTUALLY_LOG_GE_SEQUENTIALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2 + 20 * (H + 1)` THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `h0:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&10 <= log(&N)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&20 * &(H + 1) <= &N /\ &h0 <= &H` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &H` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&1) <= &3` ASSUME_TAC THENL
   [MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * &N) <= &11 / &10 * log(&N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &2`] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &10 <= y ==> x + y <= &11 / &10 * y`)
    THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
      MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
      REWRITE_TAC[LOG_EXP; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `x2 = (2 * N + h0) - 1` THEN
  ABBREV_TAC `x1 = (N + h0) - 1` THEN
  SUBGOAL_THEN
   `N1 <= x1 /\ N1 <= x2 /\ &x2 = &2 * &N + &h0 - &1 /\
    &x1 = &N + &h0 - &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x1"; "x2"] THEN
    SUBGOAL_THEN `1 <= 2 * N + h0 /\ 1 <= N + h0` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - &1 / &20) * &x2 / log(&x2) <= &(pi_upto x2) /\
    &(pi_upto x2) <= (&1 + &1 / &20) * &x2 / log(&x2) /\
    &(pi_upto x1) <= (&1 + &1 / &20) * &x1 / log(&x1)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&20 <= &N /\ &20 * &H <= &N` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&20 * &(H + 1) <= &N` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&19 / &11 * (&N / log(&N)) <= &x2 / log(&x2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * &N - &1) / log(&2 * &N - &1)` THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC X_DIV_LOG_MONO THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * &N - &1) / (&11 / &10 * log(&N))` THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `&19 / &11 * (&N / log(&N)) = (&19 / &11 * &N) / log(&N) /\
        (&2 * &N - &1) / (&11 / &10 * log(&N)) =
        (&10 / &11 * (&2 * &N - &1)) / log(&N)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [UNDISCH_TAC `&0 < log(&N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < log(&2 * &N - &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV_DENOM; REAL_ARITH `&20 <= x ==> &0 < &2 * x - &1`;
                 REAL_LT_MUL; REAL_ARITH `&0 < &11 / &10`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&2 * &N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&x1 / log(&x1) <= &21 / &20 * (&N / log(&N))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&N + &H) / log(&N + &H)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC X_DIV_LOG_MONO THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&N + &H) / log(&N)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < log(&N + &H)` ASSUME_TAC THENL
       [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV_DENOM;
                   REAL_ARITH `&20 <= x /\ &0 <= h ==> &0 < x + h`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&21 / &20 * (&N / log(&N)) = (&21 / &20 * &N) / log(&N)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < log(&N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&x2 / log(&x2) <= &41 / &20 * (&N / log(&N))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * &N + &H) / log(&2 * &N + &H)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC X_DIV_LOG_MONO THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * &N + &H) / log(&N)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < log(&2 * &N + &H)` ASSUME_TAC THENL
       [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV_DENOM;
                   REAL_ARITH `&20 <= x /\ &0 <= h ==> &0 < &2 * x + h`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&41 / &20 * (&N / log(&N)) = (&41 / &20 * &N) / log(&N)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < log(&N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&N / (&4 * log(&N)) = (&N / log(&N)) / &4` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < log(&N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * &N / log(&N) = &4 * (&N / log(&N))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The admissible tuple; many primes from the weights.                       *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_ADD_CANCEL = prove
 (`!p v x. (p divides x ==> (p divides v + x <=> p divides v)) /\
           (p divides v ==> (p divides v + x <=> p divides x))`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THEN EQ_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUMBER_RULE);;

let TUPLE_NU_OK = prove
 (`!k D0 p m.
     prime p /\ p <= D0 /\ m IN 1..k
     ==> ~(p divides nproduct {q | prime q /\ k < q /\ q <= D0} (\q. q) +
                     m * FACT k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE {q | prime q /\ k < q /\ q <= D0} /\
                (!q. q IN {q | prime q /\ k < q /\ q <= D0} ==> prime q)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{q:num | q <= D0}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LE] THEN SET_TAC[];
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  ASM_CASES_TAC `p:num <= k` THENL
   [SUBGOAL_THEN `p divides m * FACT k` ASSUME_TAC THENL
     [MATCH_MP_TAC DIVIDES_LMUL THEN ASM_SIMP_TAC[DIVIDES_FACT_PRIME];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(p divides nproduct {q | prime q /\ k < q /\ q <= D0} (\q. q))`
    MP_TAC THENL
     [ASM_SIMP_TAC[PRIME_DIVIDES_NPRODUCT_PRIMES] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[DIVIDES_ADD_CANCEL]];
    SUBGOAL_THEN
     `p divides nproduct {q | prime q /\ k < q /\ q <= D0} (\q. q)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[PRIME_DIVIDES_NPRODUCT_PRIMES] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[DIVIDES_ADD_CANCEL; PRIME_DIVPROD_EQ; DIVIDES_FACT_PRIME] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC]);;

let TUPLE_MAYNARD_HDIST = prove
 (`!k P. (!p. p IN P ==> prime p /\ k < p)
         ==> maynard_hdist (\i. i * FACT k) k P`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[maynard_hdist; IN_NUMSEG] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(i:num == j) (mod p)` MP_TAC THENL
   [MATCH_MP_TAC CONG_MULT_RCANCEL THEN EXISTS_TAC `FACT k` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_SIMP_TAC[PRIME_COPRIME_EQ; DIVIDES_FACT_PRIME] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `p:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MANY_PRIMES_WEIGHTS = prove
 (`!A (w:num->real) (h:num->num) k r.
     FINITE A /\ (!n. n IN A ==> &0 <= w n) /\
     &r * sum A w < sum (1..k) (\m. sum {n | n IN A /\ prime(n + h m)} w)
     ==> ?n. n IN A /\ r + 1 <= CARD {i | i IN 1..k /\ prime(n + h i)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE
   [NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`; NOT_LE]) THEN
  UNDISCH_TAC
   `&r * sum A (w:num->real) <
    sum (1..k) (\m. sum {n | n IN A /\ prime(n + (h:num->num) m)} w)` THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  SUBGOAL_THEN
   `sum (1..k) (\m. sum {n | n IN A /\ prime(n + (h:num->num) m)} w) =
    sum A (\n. sum (1..k) (\i. if prime(n + h i) then (w:num->real) n
                                else &0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_RESTRICT_SET] THEN
    MP_TAC(ISPECL [`\m n. if prime(n + (h:num->num) m) then (w:num->real) n
                          else &0`; `1..k`; `A:num->bool`] SUM_SWAP) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bounds for the dyadic weight in terms of s = c0 l0.                       *)
(* ------------------------------------------------------------------------- *)

let MERTENS_C0_C1 = prove
 (`!D0. product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) *
        product {p | prime p /\ p <= D0} (\p. &1 + inv(&p - &1)) = &1`,
  GEN_TAC THEN SIMP_TAC[GSYM PRODUCT_MUL; FINITE_ATMOST] THEN
  MATCH_MP_TAC PRODUCT_EQ_1 THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2; REAL_OF_NUM_LE]; CONV_TAC REAL_FIELD]);;

let MERTENS_C0_BOUNDS = prove
 (`!D0. &0 < product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) /\
        product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) <= &1`,
  GEN_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT; MATCH_MP_TAC PRODUCT_LE_1] THEN
  REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
    [ASM_MESON_TAC[PRIME_GE_2; REAL_OF_NUM_LE]; ALL_TAC] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `&0 < inv(&p) /\ inv(&p) < &1` MP_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
     REAL_ARITH_TAC]));;

let MAYNARD_GDY_FACTS = prove
 (`!Kt M2 J Kp k D0 R l0 c0 P Lam Gam M1 Q eta.
     ((\n. product {p | prime p /\ p <= n}
                   (\p. &1 + inv(&p * (&p - &1)))) ---> Kt) sequentially /\
     (!D0 R. 2 <= D0 /\ &D0 < R
             ==> product {p | prime p /\ D0 < p /\ &p < R}
                         (\p. &1 + inv(&p - &1))
                 <= product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) *
                    M2 * log R) /\
     1 <= J /\ 1 <= k /\ 2 * 2 EXP J <= Kp * k /\ 2 <= D0 /\ &D0 < R /\
     log R / (&Kp * &k) = l0 /\
     product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) = c0 /\
     {p | prime p /\ D0 < p /\ &p < R} = P /\
     sum {A | A SUBSET P}
         (\A. maynard_gdy J l0 (nproduct A (\p. p)) *
              product A (\p. inv(&p - &1)))
     = Lam /\
     sum {A | A SUBSET P}
         (\A. maynard_gdy J l0 (nproduct A (\p. p)) pow 2 *
              product A (\p. inv(&p - &1))) = Gam /\
     sum {A | A SUBSET P}
         (\A. (maynard_gdy J l0 (nproduct A (\p. p)) pow 2 *
               product A (\p. inv(&p - &1))) *
              log(&(nproduct A (\p. p)))) = M1 /\
     product P (\p. &1 + inv(&p - &1)) = Q /\
     sum P (\p. inv(&p - &1) pow 2) = eta /\
     &1 + log(&(nproduct {p | prime p /\ p <= D0} (\p. p))) <= l0
     ==> &0 < c0 /\ c0 <= &1 /\ &1 <= l0 /\ log R = &Kp * &k * l0 /\
         (c0 * l0) / &4 <= Gam /\ Gam <= &4 * Kt * (c0 * l0) /\
         (c0 * l0) * (&J - &1) <= Lam /\
         M1 <= &6 * Kt * &J * (c0 * l0) * l0 /\
         Q <= M2 * &Kp * &k * (c0 * l0) /\ eta <= &2 / &D0 /\
         &1 < maynard_dyx l0 J /\ maynard_dyx l0 J < R /\
         &Kp * &k * l0 / &2 <= log(R / maynard_dyx l0 J) /\
         FINITE P /\ (!p. p IN P ==> prime p /\ D0 < p) /\
         (!p. prime p /\ D0 < p /\ &p < maynard_dyx l0 J ==> p IN P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `D0:num` DYW_FACTS) THEN
  MP_TAC(SPEC `D0:num` MERTENS_C0_BOUNDS) THEN
  MP_TAC(SPEC `D0:num` MERTENS_C0_C1) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `W = nproduct {p | prime p /\ p <= D0} (\p. p)` THEN
  ABBREV_TAC `c1 = product {p | prime p /\ p <= D0} (\p. &1 + inv(&p - &1))`
  THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= Kt` ASSUME_TAC THENL
   [ASM_MESON_TAC[TITCHMARSH_K_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= &Kp * &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 * 2 EXP J` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `2 <= 2 EXP J` MP_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 1` THEN
    CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= l0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&Kp = &0) /\ ~(&k = &0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `2 * 2 EXP J <= 0 * k` THEN
    REWRITE_TAC[MULT_CLAUSES; LE; MULT_EQ_0; EXP_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log R = &Kp * &k * l0` ASSUME_TAC THENL
   [EXPAND_TAC "l0" THEN UNDISCH_TAC `~(&Kp = &0)` THEN
    UNDISCH_TAC `~(&k = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p /\ D0 < p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    MP_TAC(SPEC `R:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | p < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_MESON_TAC[REAL_LTE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < maynard_dyx l0 J /\ maynard_dyx l0 J < R /\
                &Kp * &k * l0 / &2 <= log(R / maynard_dyx l0 J)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * &2 pow J <= &Kp * &k /\ &1 <= &2 pow J`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW2] THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&D0` THEN
      ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < l0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MAYNARD_DYX_GT_1 THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV
       [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < R`))] THEN
      REWRITE_TAC[maynard_dyx; REAL_EXP_MONO_LT] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[LOG_DIV; MAYNARD_DYX_POS; LOG_MAYNARD_DYX] THEN
      SUBGOAL_THEN `(&2 pow J - &1) * l0 <= (&Kp * &k / &2) * l0`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. prime p /\ D0 < p /\ &p < maynard_dyx l0 J ==> p IN P`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kt /\ &0 <= l0 /\ &0 <= log(&W) /\ &1 <= &J`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`J:num`; `l0:real`; `D0:num`; `P:num->bool`]
           GAMMA_DY_LOWER) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `maynard_dyx l0 1` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MAYNARD_DYX_MONO THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MP_TAC(SPECL [`Kt:real`; `J:num`; `l0:real`; `D0:num`; `P:num->bool`]
           GAMMA_DY_UPPER) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((Gam:real) * c1) * c0 = Gam`
    (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THENL
     [UNDISCH_TAC `c0 * c1 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Kt * ((&1 + log(&W)) + &3 * l0)) * c0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Kt * (&4 * l0)) * c0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]];
    MP_TAC(SPECL [`J:num`; `l0:real`; `D0:num`; `P:num->bool`]
           LAMBDA_DY_LOWER) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[REAL_MUL_ASSOC]];
    MP_TAC(SPECL [`Kt:real`; `J:num`; `l0:real`; `D0:num`; `P:num->bool`]
           M1_DY_UPPER) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((M1:real) * c1) * c0 = M1`
    (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THENL
     [UNDISCH_TAC `c0 * c1 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Kt * l0 * (&3 * (&1 + log(&W)) + &3 * &J * l0)) * c0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Kt * l0 * (&6 * &J * l0)) * c0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `l0 <= &J * l0` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`D0:num`; `R:real`] o check (fun th ->
      can (find_term ((=) `M2:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_AC];
    MP_TAC(SPECL [`D0:num`; `R:real`] ETA_BOUND) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Main term and error terms against (N/W) Gamma^k.                          *)
(* ------------------------------------------------------------------------- *)

let F1_TAIL = prove
 (`!k M1 Gam logRR s Kt J Kp l0.
     2 <= k /\ &0 < s /\ &0 < l0 /\ &0 < Kt /\ &0 < &J /\
     &0 <= M1 /\ M1 <= &6 * Kt * &J * s * l0 /\
     &Kp * &k * l0 / &2 <= logRR /\ &320 * Kt * &J <= &Kp /\
     s / &4 <= Gam
     ==> (&k - &1) * M1 * Gam pow (k - 2) / logRR <=
         &3 / &20 * Gam pow (k - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Gam /\ &0 < &Kp /\ &2 <= &k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&320 * Kt * &J` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < logRR` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&Kp * &k * l0 / &2` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LT_DIV) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Gam:real) pow (k - 1) = Gam * Gam pow (k - 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Gam pow (k - 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((&k - &1) * M1) / logRR <= &3 / &20 * Gam` MP_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN
    MP_TAC(MATCH_MP REAL_LE_RMUL (CONJ
      (ASSUME `((&k - &1) * M1) / logRR <= &3 / &20 * Gam`)
      (ASSUME `&0 <= Gam pow (k - 2)`))) THEN
    MATCH_MP_TAC(REAL_ARITH `a = b /\ c = d ==> a <= c ==> b <= d`) THEN
    CONJ_TAC THEN REWRITE_TAC[real_div; REAL_MUL_AC]] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&k - &1) * (&6 * Kt * &J * s * l0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&3 / &20 * s / &4) * (&Kp * &k * l0 / &2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV) THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `&0 <= (&Kp - &320 * Kt * &J) * (s * l0 * &k)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kt * &J * s * l0` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let F1_MAIN = prove
 (`!r k Lam Gam M1 logRR a s Kt J Kp l0 Nr Wr PW Lr c0.
     2 <= k /\ &0 < s /\ &0 < l0 /\ &0 < Kt /\ &1 <= &J /\
     &0 <= M1 /\ M1 <= &6 * Kt * &J * s * l0 /\
     &Kp * &k * l0 / &2 <= logRR /\ &320 * Kt * &J <= &Kp /\
     s / &4 <= Gam /\ Gam <= &4 * Kt * s /\ s * (&J - &1) <= Lam /\
     &19 / &20 <= a /\ &0 < Nr /\ &0 < Wr /\ c0 * Wr = PW /\ c0 * l0 = s /\
     &0 < c0 /\ &5 * &Kp * &k * l0 = Lr /\
     &300 * &r * Kt * &Kp <= (&J - &1) pow 2
     ==> &3 * &r * (Nr / Wr * Gam pow k) <=
         (&k * Nr / (&4 * Lr * PW)) *
         (Lam pow 2 *
          (Gam pow (k - 1) * a - (&k - &1) * M1 * Gam pow (k - 2) / logRR))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `M1:real`; `Gam:real`; `logRR:real`; `s:real`;
                `Kt:real`; `J:num`; `Kp:num`; `l0:real`] F1_TAIL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < Gam /\ &0 < &Kp /\ &2 <= &k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&320 * Kt * &J` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Gam:real) pow k = Gam * Gam pow (k - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `G1 = (Gam:real) pow (k - 1)` THEN
  SUBGOAL_THEN `&0 < G1` ASSUME_TAC THENL
   [EXPAND_TAC "G1" THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b = (&k - &1) * M1 * Gam pow (k - 2) / logRR` THEN
  SUBGOAL_THEN `&4 / &5 * G1 <= G1 * a - b` ASSUME_TAC THENL
   [SUBGOAL_THEN `&19 / &20 * G1 <= G1 * a` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s * (&J - &1)) pow 2 <= Lam pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Gam pow k / (&4 * Kt * s) <= G1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &4 * Kt * s` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&k * Nr / (&4 * Lr * PW))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Lr"; "PW"] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    SIMP_TAC[REAL_LT_IMP_LE; ASSUME `&0 < Nr`] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&k * Nr / (&4 * Lr * PW)) *
              ((s * (&J - &1)) pow 2 *
               (&4 / &5 * (Gam pow k / (&4 * Kt * s))))`
  THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[ASSUME `&0 <= (&k * Nr / (&4 * Lr * PW))`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_LE_POW_2;
                ASSUME `(s * (&J - &1)) pow 2 <= Lam pow 2`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
       REWRITE_TAC[REAL_ARITH `&0 <= &4 / &5`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN
   `(&k * Nr / (&4 * Lr * PW)) *
    ((s * (&J - &1)) pow 2 * (&4 / &5 * (Gam pow k / (&4 * Kt * s)))) =
    (&J - &1) pow 2 / (&100 * Kt * &Kp) * (Nr / Wr * Gam pow k)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Lr"; "PW"; "s"] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < c0`; `&0 < l0`; `&0 < Wr`; `&0 < Kt`;
                           `&0 < &Kp`; `&2 <= &k`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &100 * Kt * &Kp` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]]);;

let POW_RATIO_BOUND = prove
 (`!k Q Gam s q1.
     &0 < s /\ &0 <= Q /\ Q <= q1 * s /\ s / &4 <= Gam
     ==> Q pow k <= (&4 * q1) pow k * Gam pow k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= q1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `q1:real`; `s:real`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(q1:real) * s` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&4 * q1) * Gam = (q1:real) * (&4 * Gam)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let F4_LEMMA = prove
 (`!k Q Gam s q1 e Nr Wr.
     &0 < s /\ &0 <= Q /\ Q <= q1 * s /\ s / &4 <= Gam /\ &0 <= e /\
     &0 < Nr /\ &0 < Wr /\ &10 * (&4 * q1) pow k * e <= &1
     ==> Nr / Wr * (Q pow k * e) <= (Nr / Wr * Gam pow k) / &10`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `Q:real`; `Gam:real`; `s:real`; `q1:real`]
         POW_RATIO_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < Nr / Wr /\ &0 <= Gam pow k` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV] THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]
  THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ;
    REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&4 * (q1:real)) pow k * Gam pow k) * e` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Gam pow k * inv(&10) * (&1 - &10 * (&4 * q1) pow k * e)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let F2_LEMMA = prove
 (`!k Q Gam s q1 e c0 l0 Nr Wr PW Lr Kp.
     1 <= k /\ &0 < s /\ &0 <= Q /\ Q <= q1 * s /\ s / &4 <= Gam /\
     &0 <= e /\ &0 < Nr /\ &0 < Wr /\ c0 * Wr = PW /\ c0 * l0 = s /\
     &0 < c0 /\ &0 < l0 /\ &5 * &Kp * &k * l0 = Lr /\ &0 < &Kp /\
     &8 * q1 * (&4 * q1) pow k * e <= &Kp
     ==> (&k * &4 * Nr / (Lr * PW)) * (Q pow (k + 1) * e) <=
         (Nr / Wr * Gam pow k) / &10`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `Q:real`; `Gam:real`; `s:real`; `q1:real`]
         POW_RATIO_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= q1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `q1:real`; `s:real`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Gam /\ &1 <= &k` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&k * &4 * Nr / (Lr * PW))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Lr"; "PW"] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&k * &4 * Nr / (Lr * PW)) *
              (((q1:real) * s) * ((&4 * q1) pow k * Gam pow k) * e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[ASSUME `&0 <= (&k * &4 * Nr / (Lr * PW))`] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&k * &4 * Nr / (Lr * PW)) *
    (((q1:real) * s) * ((&4 * q1) pow k * Gam pow k) * e) =
    (&4 / &5 * q1 * (&4 * q1) pow k * e / &Kp) * (Nr / Wr * Gam pow k)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Lr"; "PW"; "s"] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < c0`; `&0 < l0`; `&0 < Wr`; `&0 < &Kp`;
                           `&1 <= &k`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `x / &10 = inv(&10) * x`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&4 / &5 * q1 * (&4 * q1) pow k * e / &Kp =
                  (&8 * q1 * (&4 * q1) pow k * e) / (&10 * &Kp)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &Kp` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &10 * &Kp` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]]);;

let POW_LOWER_SCALE = prove
 (`!k Gam s. &0 < s /\ s / &4 <= Gam ==> s pow k <= &4 pow k * Gam pow k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

let F5_LEMMA = prove
 (`!k Q Gam s q1 Nr Wr R B3.
     &0 < s /\ &0 <= Q /\ Q <= q1 * s /\ s / &4 <= Gam /\ &0 < Nr /\
     &0 < Wr /\ &0 <= R /\ &0 <= B3 /\ B3 <= Q pow (3 * k) /\
     &20 * Wr * R pow 2 * &4 pow k * (q1 * s) pow (6 * k) <= Nr * s pow k
     ==> &2 * (R * B3) pow 2 <= (Nr / Wr * Gam pow k) / &10`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= q1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `q1:real`; `s:real`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(R * B3) pow 2 <= R pow 2 * (q1 * s) pow (6 * k)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_POW_MUL] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[ARITH_RULE `6 * k = (3 * k) * 2`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Q:real) pow (3 * k)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `Gam:real`; `s:real`] POW_LOWER_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &4 pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&20 * Wr * R pow 2 * &4 pow k * (q1 * s) pow (6 * k) <=
    Nr * (&4 pow k * Gam pow k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Nr:real) * s pow k` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&20 * Wr * R pow 2 * (q1 * s) pow (6 * k) <= Nr * Gam pow k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `(&4:real) pow k` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `Nr:real`))
      (concl th) && can (find_term ((=) `R:real`)) (concl th))) THEN
    REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Nr / Wr * Gam pow k) / &10 = (Nr * Gam pow k) / (&10 * Wr)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < Wr` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &10 * Wr` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `Wr * (R * B3) pow 2 <= Wr * (R pow 2 * (q1 * s) pow (6 * k))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC
   `&20 * Wr * R pow 2 * (q1 * s) pow (6 * k) <= Nr * Gam pow k` THEN
  REAL_ARITH_TAC);;

let F3_LEMMA = prove
 (`!k Q Gam s q1 Nr Wr PW L M Cb A E0 X.
     &0 < s /\ &0 <= Q /\ Q <= q1 * s /\ s / &4 <= Gam /\ &0 < Nr /\
     &0 < Wr /\ &0 < PW /\ &0 < M /\ &0 <= Cb /\ &0 < L /\
     X <= Nr * (&k * Q pow (2 * k + 2) *
                (&6 * &2 pow A * M * Cb / L pow A +
                 &18 * Q pow E0 / (PW * M))) /\
     &10 * Wr * &4 pow k *
     (&k * (q1 * s) pow (2 * k + 2) *
      (&6 * &2 pow A * M * Cb / L pow A + &18 * (q1 * s) pow E0 / (PW * M)))
     <= s pow k
     ==> X <= (Nr / Wr * Gam pow k) / &10`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= q1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `q1:real`; `s:real`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Y = &k * (q1 * s) pow (2 * k + 2) *
                  (&6 * &2 pow A * M * Cb / L pow A +
                   &18 * (q1 * s) pow E0 / (PW * M))` THEN
  SUBGOAL_THEN
   `&k * Q pow (2 * k + 2) *
    (&6 * &2 pow A * M * Cb / L pow A + &18 * Q pow E0 / (PW * M)) <= Y`
  ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]
    THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y <= x + z`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &18`] THEN
      SUBGOAL_THEN `&0 < PW * M` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `Gam:real`; `s:real`] POW_LOWER_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&10 * Wr * Y <= Gam pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `(&4:real) pow k` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s:real) pow k` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `Wr:real`))
      (concl th) && can (find_term ((=) `(&4:real) pow k`)) (concl th))) THEN
    REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Nr / Wr * Gam pow k) / &10 = (Nr * Gam pow k) / (&10 * Wr)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < Wr` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &10 * Wr` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Nr * Y) * (&10 * Wr)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Nr * (&k * Q pow (2 * k + 2) *
                (&6 * &2 pow A * M * Cb / L pow A +
                 &18 * Q pow E0 / (PW * M)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Nr * Y) * (&10 * Wr) = Nr * (&10 * Wr * Y)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;
