(* ========================================================================= *)
(* Exp-form bounds for the auxiliary function and the Liouville bound.       *)
(*                                                                           *)
(* Purpose: BAKER_AUX_EXP_BOUND and BAKER_APPROX_EXP_BOUND restate           *)
(* BAKER_AUX_BOUND and BAKER_AUX_ALG_APPROX with all factors bounded by      *)
(* exponentials: CARD = h (L + 1)^(n + 1) <= exp(h + (n + 1) L),             *)
(* 2^x <= exp x, and the powers of m 0 + L |beta 0| and of                   *)
(* L (1 + |beta r|) |lg r| are at most                                       *)
(* (2 k Bb Lam)^(2 k) = exp(2 k log(2 k Bb Lam)) when nsum m <= k.           *)
(* LIOUVILLE_EXP_LOWER bounds the right-hand side of INTPOLY_LIOUVILLE below *)
(* by exp(--(D (log D + log b + sum_r nn r log((d r + 1) H r^3)))) with      *)
(* D = nproduct v d; LIOUVILLE_EXP_LOWER_MONO gives its monotonicity in b,   *)
(* nn and H.                                                                 *)
(*                                                                           *)
(* Main results: BAKER_AUX_EXP_BOUND, BAKER_APPROX_EXP_BOUND,                *)
(*   LIOUVILLE_EXP_LOWER, LIOUVILLE_EXP_LOWER_MONO,                          *)
(*   CARD_BAKER_INDEX_EXP_BOUND; the elementary bounds REAL_LE_EXP_SELF,     *)
(*   FACT_LE_SELF_EXP, PRODUCT_GE_1.                                         *)
(*                                                                           *)
(* Uses: Baker/lemmas.ml (REAL_TWO_POW_LE_EXP), Baker/auxiliary.ml           *)
(*   (BAKER_AUX_BOUND, BAKER_AUX_ALG_APPROX, FACT_LE_POW),                   *)
(*   Baker/aux_arith.ml (CARD_BAKER_INDEX).                                  *)
(* ========================================================================= *)

needs "Baker/aux_arith.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary exponential bounds.                                            *)
(* ------------------------------------------------------------------------- *)

let REAL_LE_EXP_SELF = prove
 (`!x. x <= exp x`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

let FACT_LE_SELF_EXP = prove
 (`!n. FACT n <= n EXP n`,
  MESON_TAC[FACT_LE_POW; LE_REFL]);;

let PRODUCT_GE_1 = prove
 (`!(f:A->real) s.
        FINITE s /\ (!x. x IN s ==> &1 <= f x) ==> &1 <= product s f`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `product (s:A->bool) (\x. &1)` THEN
  CONJ_TAC THENL [REWRITE_TAC[PRODUCT_ONE; REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* The auxiliary function: the factors of BAKER_AUX_BOUND and                *)
(* BAKER_AUX_ALG_APPROX bounded by exponentials.                             *)
(* ------------------------------------------------------------------------- *)

let CARD_BAKER_INDEX_EXP_BOUND = prove
 (`!h L n. &(CARD(baker_index h L n)) <= exp(&h) * exp(&(n + 1) * &L)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CARD_BAKER_INDEX; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[REAL_EXP_N] THEN
  SUBGOAL_THEN `exp(&L) pow (n + 1) = exp(&L) * exp(&L) pow n`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM ADD1; real_pow]; ALL_TAC] THEN
  SUBGOAL_THEN `&(L + 1) <= exp(&L)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    MP_TAC(SPEC `&L:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS; REAL_LE_EXP_SELF] THEN
  CONJ_TAC THENL [SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_POW_LE2]);;

let BAKER_POWERS_EXP_BOUND = prove
 (`!n L k (beta:num->complex) (lg:num->complex) m Bb Lam.
        1 <= n /\ 1 <= L /\ L <= k /\ &1 <= Bb /\ &1 <= Lam /\
        (!j. j < n ==> norm(beta j) <= Bb) /\
        (!r. r IN 1..n ==> norm(lg r) <= Lam) /\
        nsum(0..n-1) m <= k
        ==> (&(m 0) + &L * norm(beta 0)) pow (m 0) *
            product(1..n-1)
              (\r. (&L * (&1 + norm(beta r)) * norm(lg r)) pow (m r))
            <= exp(&(2 * k) * log(&2 * &k * Bb * Lam))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&L <= &k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &k * (Bb - &1) /\ &0 <= (&k * Bb) * (Lam - &1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = &2 * &k * Bb * Lam` THEN
  SUBGOAL_THEN `&1 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&(2 * k) * log c) = c pow (2 * k)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_N] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m 0 + nsum(1..n-1) m <= k` ASSUME_TAC THENL
   [UNDISCH_TAC `nsum(0..n-1) m <= k` THEN
    SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `c pow (m 0) * product(1..n-1) (\r. c pow (m r))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[GSYM REAL_POW_NSUM; FINITE_NUMSEG; GSYM REAL_POW_ADD] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; NORM_POS_LE];
    MATCH_MP_TAC REAL_POW_LE2 THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; NORM_POS_LE] THEN
    SUBGOAL_THEN `&(m 0) <= &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&L * norm((beta:num->complex) 0) <= &k * Bb` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS; NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; NORM_POS_LE];
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&0 <= &L * (&1 + norm((beta:num->complex) r)) * norm((lg:num->complex) r)`
    ASSUME_TAC THENL
     [SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; NORM_POS_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN
    TRANS_TAC REAL_LE_TRANS `&k * (&2 * Bb) * Lam` THEN CONJ_TAC THENL
     [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LE_ADD; NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_LE_ADD; REAL_POS; NORM_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 <= b /\ x <= b ==> &1 + x <= &2 * b`) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC]]);;

let BAKER_EXP_BOUND_ARITH = prove
 (`!c p t2 t3 t4 t5 e0 e1 e2 e3 e4:real.
        &0 <= c /\ c <= e0 * e1 /\ &0 <= p /\ &0 <= t2 /\ t2 <= e2 /\
        &0 <= t3 /\ &0 <= t4 /\ t3 * t4 <= e3 /\ &0 <= t5 /\ t5 <= e4
        ==> c * (p * t2 * t3 * t4 * t5) <= p * e0 * e1 * e2 * e3 * e4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(c:real) * (p * t2 * t3 * t4 * t5) = p * (c * (t2 * ((t3 * t4) * t5)))`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:real) * e0 * e1 * e2 * e3 * e4 = p * ((e0 * e1) * (e2 * (e3 * e4)))`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_MUL]));;

let BAKER_AUX_BOUND_POS = prove
 (`!n h L (beta:num->complex) (lg:num->complex) m N P X.
        &0 <= P
        ==> &0 <= &(CARD(baker_index h L n)) *
                  (P * &2 pow ((L + 2) * (N + h)) *
                   (&(m 0) + &L * norm(beta 0)) pow (m 0) *
                   product(1..n-1)
                     (\r. (&L * (&1 + norm(beta r)) * norm(lg r)) pow (m r)) *
                   exp X)`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE] THEN
  TRY(MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[]) THEN
  MATCH_MP_TAC REAL_POW_LE THEN
  SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; NORM_POS_LE]);;

let BAKER_AUX_EXP_COMMON = prove
 (`!n h L k (beta:num->complex) (lg:num->complex) m N P Bb Lam X Y.
        1 <= n /\ 1 <= L /\ L <= k /\ &1 <= Bb /\ &1 <= Lam /\ &0 <= P /\
        (!j. j < n ==> norm(beta j) <= Bb) /\
        (!r. r IN 1..n ==> norm(lg r) <= Lam) /\
        nsum(0..n-1) m <= k /\ X <= Y
        ==> &(CARD(baker_index h L n)) *
            (P * &2 pow ((L + 2) * (N + h)) *
             (&(m 0) + &L * norm(beta 0)) pow (m 0) *
             product(1..n-1)
               (\r. (&L * (&1 + norm(beta r)) * norm(lg r)) pow (m r)) *
             exp X)
            <= P * exp(&h + &(n + 1) * &L + &(L + 2) * &(N + h) +
                       &(2 * k) * log(&2 * &k * Bb * Lam) + Y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_ADD] THEN
  MATCH_MP_TAC BAKER_EXP_BOUND_ARITH THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_EXP_MONO_LE;
                  CARD_BAKER_INDEX_EXP_BOUND] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_TWO_POW_LE_EXP];
    MATCH_MP_TAC REAL_POW_LE THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; NORM_POS_LE];
    MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; NORM_POS_LE];
    MATCH_MP_TAC BAKER_POWERS_EXP_BOUND THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Exp-form bounds for baker_aux and for its difference with the             *)
(* algebraic counterpart baker_alg.                                          *)
(* ------------------------------------------------------------------------- *)

let BAKER_AUX_EXP_BOUND = prove
 (`!n h L k p beta lg m z N P Bb Lam.
        1 <= n /\ 1 <= L /\ L <= k /\ &1 <= Bb /\ &1 <= Lam /\ &0 <= P /\
        (!x. x IN baker_index h L n ==> abs(p x) <= P) /\
        (!j. j < n ==> norm(beta j) <= Bb) /\
        (!r. r IN 1..n ==> norm(lg r) <= Lam) /\
        sum(1..n) (\r. norm(lg r)) <= Lam /\
        norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n) <= &1 /\
        nsum(0..n-1) m <= k /\ norm z + &1 <= &N
        ==> norm(baker_aux n h L p beta lg m z) <=
            P * exp(&h + &(n + 1) * &L + &(L + 2) * &(N + h) +
                    &(2 * k) * log(&2 * &k * Bb * Lam) +
                    &N * &L * (Lam + &1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `p:num#num#(num->num)->real`;
                `beta:num->complex`; `lg:num->complex`; `m:num->num`;
                `z:complex`; `N:num`; `P:real`] BAKER_AUX_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c:real`) THEN
  MATCH_MP_TAC BAKER_AUX_EXP_COMMON THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]) THEN
  ASM_REAL_ARITH_TAC);;

let BAKER_APPROX_EXP_BOUND = prove
 (`!n h L k p beta lg m z N P Bb Lam d0.
        1 <= n /\ 1 <= L /\ L <= k /\ &1 <= Bb /\ &1 <= Lam /\ &0 <= P /\
        (!x. x IN baker_index h L n ==> abs(p x) <= P) /\
        (!j. j < n ==> norm(beta j) <= Bb) /\
        (!r. r IN 1..n ==> norm(lg r) <= Lam) /\
        sum(1..n) (\r. norm(lg r)) <= Lam /\ &0 <= d0 /\
        norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n) <= d0 /\
        nsum(0..n-1) m <= k /\ norm z + &1 <= &N
        ==> norm(baker_aux n h L p beta lg m z -
                 cproduct(1..n-1) (\r. lg r pow (m r)) *
                 baker_alg n h L p beta lg m z) <=
            P * exp(&h + &(n + 1) * &L + &(L + 2) * &(N + h) +
                    &(2 * k) * log(&2 * &k * Bb * Lam) + &N * &L * Lam) *
            (&N * &L * d0 * exp(&N * &L * d0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `p:num#num#(num->num)->real`;
                `beta:num->complex`; `lg:num->complex`; `m:num->num`;
                `z:complex`; `N:num`; `P:real`] BAKER_AUX_ALG_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c:real`) THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BAKER_AUX_BOUND_POS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BAKER_AUX_EXP_COMMON THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]) THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[REAL_LE_MUL; REAL_POS; NORM_POS_LE; REAL_EXP_POS_LE];
    ABBREV_TAC `dd = norm((beta:num->complex) 0 +
                          vsum(1..n-1) (\r. beta r * (lg:num->complex) r) -
                          lg n)` THEN
    SUBGOAL_THEN `&0 <= dd` ASSUME_TAC THENL
     [EXPAND_TAC "dd" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&N * &L * dd <= &N * &L * d0` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_MONO_LE; GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]]);;

(* ------------------------------------------------------------------------- *)
(* The Liouville bound in exp form: with D = nproduct v d,                   *)
(* D! <= D^D and H r H r (1 + d r H r) <= (d r + 1) H r^3.                   *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_HEIGHT_ARITH = prove
 (`!x y. &1 <= x /\ &0 <= y
         ==> &0 <= x * x * (&1 + y * x) /\
             x * x * (&1 + y * x) <= (y + &1) * x pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_ADD; REAL_POS];
    MP_TAC(SPECL [`x * x:real`; `x - &1`] REAL_LE_MUL) THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let LIOUVILLE_EXP_ARITH = prove
 (`!D b Q R W.
        1 <= D /\ &1 <= b /\ &1 <= Q /\ &1 <= R /\ b * Q * R <= W
        ==> &0 < &(FACT D) * max (&1) (b * Q * R) pow (D - 1) * Q /\
            &(FACT D) * max (&1) (b * Q * R) pow (D - 1) * Q <=
            (&D * W) pow D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Q * (R - &1) /\ &0 <= (b - &1) * (Q * R)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= b * Q * R /\ Q <= W` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `max (&1) (b * Q * R) = b * Q * R` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b * Q * R /\ &0 <= b * Q * R /\ &0 < Q /\ &0 <= Q`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_OF_NUM_LT; FACT_LT];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_POW_MUL] THEN
  SUBGOAL_THEN `W pow D = W pow (D - 1) * W` SUBST1_TAC THENL
   [SUBGOAL_THEN `D = (D - 1) + 1`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[REAL_POW_ADD; REAL_POW_1]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_POS; REAL_OF_NUM_POW; REAL_OF_NUM_LE; FACT_LE_SELF_EXP] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_LE2]);;

let LIOUVILLE_PRODUCT_BOUND = prove
 (`!v (d:num->num) (H:num->real) (nn:num->num).
        FINITE v /\ (!r. r IN v ==> &1 <= H r)
        ==> &1 <= product v (\r. H r pow nn r) /\
            &1 <= product v (\r. (H r * (&1 + &(d r) * H r)) pow nn r) /\
            product v (\r. H r pow nn r) *
            product v (\r. (H r * (&1 + &(d r) * H r)) pow nn r) <=
            product v (\r. (&(d r + 1) * H r pow 3) pow nn r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_GE_1 THEN ASM_SIMP_TAC[REAL_POW_LE_1];
    MATCH_MP_TAC PRODUCT_GE_1 THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN
    SUBGOAL_THEN `&1 <= (H:num->real) r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM PRODUCT_MUL; GSYM REAL_POW_MUL] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`(H:num->real) r`; `&((d:num->num) r):real`]
      LIOUVILLE_HEIGHT_ARITH) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POS]; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_LE2]]);;

let LIOUVILLE_EXP_IDENTITY = prove
 (`!v (d:num->num) (H:num->real) (nn:num->num) b D.
        FINITE v /\ (!r. r IN v ==> &1 <= H r) /\ &1 <= b /\ 1 <= D
        ==> exp(&D * (log(&D) + log b +
                      sum v (\r. &(nn r) * log(&(d r + 1) * H r pow 3)))) =
            (&D * b * product v (\r. (&(d r + 1) * H r pow 3) pow nn r))
            pow D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_EXP_N; REAL_EXP_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; ARITH_RULE `1 <= D ==> 0 < D`;
               REAL_ARITH `&1 <= b ==> &0 < b`; REAL_EXP_SUM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_EXP_N] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EXP_LOG THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x`) THEN ASM_SIMP_TAC[]);;

let LIOUVILLE_EXP_LOWER = prove
 (`!v (d:num->num) (H:num->real) (nn:num->num) b.
        FINITE v /\ (!r. r IN v ==> 1 <= d r /\ &1 <= H r) /\ &1 <= b
        ==> exp(--(&(nproduct v d) *
                   (log(&(nproduct v d)) + log b +
                    sum v (\r. &(nn r) * log(&(d r + 1) * H r pow 3)))))
            <= inv(&(FACT(nproduct v d)) *
                   (max (&1) (b * product v (\r. H r pow nn r) *
                              product v (\r. (H r * (&1 + &(d r) * H r))
                                             pow nn r)))
                   pow (nproduct v d - 1) *
                   product v (\r. H r pow nn r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_NEG] THEN
  ABBREV_TAC `D = nproduct v (d:num->num)` THEN
  SUBGOAL_THEN `1 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= n ==> 0 < n`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`v:num->bool`; `d:num->num`; `H:num->real`; `nn:num->num`;
                `b:real`; `D:num`] LIOUVILLE_EXP_IDENTITY) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`v:num->bool`; `d:num->num`; `H:num->real`; `nn:num->num`]
    LIOUVILLE_PRODUCT_BOUND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Q = product v (\r. (H:num->real) r pow nn r)` THEN
  ABBREV_TAC
   `R = product v (\r. ((H:num->real) r * (&1 + &(d r) * H r)) pow nn r)` THEN
  ABBREV_TAC
   `W = product v (\r. (&(d r + 1) * (H:num->real) r pow 3) pow nn r)` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`D:num`; `b:real`; `Q:real`; `R:real`; `b * W:real`]
    LIOUVILLE_EXP_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity of the exp-form Liouville bound in b, nn and H.              *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_EXP_LOWER_MONO = prove
 (`!v (d:num->num) (H:num->real) (H':num->real) (nn:num->num)
    (nn':num->num) b b'.
        FINITE v /\ (!r. r IN v ==> 1 <= d r) /\ &1 <= b /\ b <= b' /\
        (!r. r IN v ==> nn r <= nn' r /\ &1 <= H r /\ H r <= H' r)
        ==> exp(--(&(nproduct v d) *
                   (log(&(nproduct v d)) + log b' +
                    sum v (\r. &(nn' r) * log(&(d r + 1) * H' r pow 3)))))
            <= exp(--(&(nproduct v d) *
                      (log(&(nproduct v d)) + log b +
                       sum v (\r. &(nn r) * log(&(d r + 1) * H r pow 3)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= x' /\ y <= y' ==> a + x + y <= a + x' + y':real`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &((d:num->num) r + 1) * (H:num->real) r pow 3`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE; REAL_POW_LE_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE; LOG_POS] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;
