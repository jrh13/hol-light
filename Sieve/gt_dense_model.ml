(* ========================================================================= *)
(* The dense model theorem, proved by multiplicative weights (for the        *)
(* Green-Tao theorem).                                                       *)
(*                                                                           *)
(* The mean fmean X g = sum X g / |X| over a finite set and its basic        *)
(* lemmas (FMEAN_ADD, FMEAN_LE, FMEAN_SUM, ...) are those of                 *)
(* Library/szemeredi.ml.                                                     *)
(* * Multiplicative weights: mw_weight (SUC t) s = mw_weight t s *           *)
(*   exp(h * adv p_t s), where p_t = mw_dist t are the normalised weights    *)
(*   and the gains adv p s in [-B, B] may depend on p.  MW_REGRET: if        *)
(*   h B <= 1 then for every strategy s0                                     *)
(*     sum_{t<T} adv p_t s0                                                  *)
(*       <= sum_{t<T} <p_t, adv p_t> + log |S| / h + 4 T h B^2               *)
(*   (REAL_EXP_QUAD_BOUND: exp x <= 1 + x + 4 x^2 on [-1, 1]).               *)
(* * POS_PART_POLY: max(z, 0) is within e of a polynomial on [-1, 1]         *)
(*   (Stone-Weierstrass).  MIX_POWER_BOUND, DMT_POLY_BOUND: for a convex     *)
(*   combination phib = sum_s p(s) th_s the correlation <nu - 1, P(phib)>    *)
(*   is controlled by the correlations of nu - 1 with products of at most    *)
(*   deg P test functions; DMT_BEST_RESPONSE: [phib > 0] is a best           *)
(*   response up to e / 3.                                                   *)
(* * DENSE_MODEL (Green-Tao-Ziegler, in the form of Reingold, Trevisan,      *)
(*   Tulsiani and Vadhan): for 0 < e <= 1 there are D and e' > 0 such that   *)
(*   if S is a finite set of test functions th_s : X -> [-1, 1], 0 <= f <=   *)
(*   nu on X and |<nu - 1, th_s1 ... th_sd>| <= e' for all d <= D, then      *)
(*   some ft : X -> [0, 1] has <f - ft, th_s> <= e for all s IN S.           *)
(*   Multiplicative weights over S replace the separating hyperplane (the    *)
(*   dimension |X| is a variable): ft is an average of best responses.       *)
(* ========================================================================= *)

needs "Sieve/bg_s1.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Multiplicative weights and the regret bound.                              *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_QUAD_BOUND = prove
 (`!x. abs x <= &1 ==> exp x <= &1 + x + &4 * x pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `Cx x`] TAYLOR_CEXP) THEN
  SUBGOAL_THEN `vsum(0..1) (\k. Cx x pow k / Cx(&(FACT k))) = Cx(&1 + x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[num_CONV `1`; VSUM_CLAUSES_NUMSEG; FACT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_RID; COMPLEX_DIV_1; CX_ADD] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CX_EXP; GSYM CX_SUB; RE_CX; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[num_CONV `1`; FACT; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_DIV_1] THEN
  SUBGOAL_THEN `exp(abs x) <= &4` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1)` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `exp(&1) = exp(inv(&2)) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(inv(&2)) <= &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * inv(&2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  SUBGOAL_THEN `&0 <= x pow 2` MP_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SPEC_TAC(`exp(abs x)`,`a:real`) THEN GEN_TAC THEN
  SPEC_TAC(`(x:real) pow 2`,`y:real`) THEN GEN_TAC THEN
  SPEC_TAC(`exp x`,`e:real`) THEN GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `a * y <= &4 * y` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let mw_weight = new_recursive_definition num_RECURSION
 `(mw_weight 0 (adv:(A->real)->A->real) (S:A->bool) h (s:A) = &1) /\
  (mw_weight (SUC t) adv S h s =
     mw_weight t adv S h s *
     exp(h * adv (\s'. mw_weight t adv S h s' /
                       sum S (mw_weight t adv S h)) s))`;;

let mw_dist = new_definition
 `mw_dist t (adv:(A->real)->A->real) (S:A->bool) h =
    \s. mw_weight t adv S h s / sum S (mw_weight t adv S h)`;;

let MW_WEIGHT_SUC = prove
 (`!t (adv:(A->real)->A->real) S h s.
        mw_weight (SUC t) adv S h s =
        mw_weight t adv S h s * exp(h * adv (mw_dist t adv S h) s)`,
  REWRITE_TAC[mw_weight; mw_dist]);;

let MW_WEIGHT_EXPLICIT = prove
 (`!t (adv:(A->real)->A->real) S h s.
        mw_weight t adv S h s =
        exp(h * sum {i | i < t} (\i. adv (mw_dist i adv S h) s))`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MW_WEIGHT_SUC] THENL
   [REWRITE_TAC[mw_weight; LT; EMPTY_GSPEC; SUM_CLAUSES; REAL_MUL_RZERO;
                REAL_EXP_0];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_EXP_ADD;
   GSYM REAL_ADD_LDISTRIB] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LT; SET_RULE `{i:num | i = t \/ P i} = t INSERT {i | P i}`] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);;

let MW_WEIGHT_POS = prove
 (`!t (adv:(A->real)->A->real) S h s. &0 < mw_weight t adv S h s`,
  REWRITE_TAC[MW_WEIGHT_EXPLICIT; REAL_EXP_POS_LT]);;

let MW_SUM_POS = prove
 (`!t (adv:(A->real)->A->real) S h.
        FINITE S /\ ~(S = {}) ==> &0 < sum S (mw_weight t adv S h)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SIMP_TAC[MW_WEIGHT_POS; REAL_LT_IMP_LE];
    ASM_MESON_TAC[MW_WEIGHT_POS; MEMBER_NOT_EMPTY]]);;

let MW_DIST_PROB = prove
 (`!t (adv:(A->real)->A->real) S h.
        FINITE S /\ ~(S = {})
        ==> (!s. &0 <= mw_dist t adv S h s) /\
            sum S (mw_dist t adv S h) = &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:num`; `adv:(A->real)->A->real`; `S:A->bool`; `h:real`]
         MW_SUM_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mw_dist] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[MW_WEIGHT_POS; REAL_LT_IMP_LE];
    REWRITE_TAC[real_div; SUM_RMUL; ETA_AX] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC]);;

let MW_SUM_STEP = prove
 (`!t (adv:(A->real)->A->real) S h B.
        FINITE S /\ ~(S = {}) /\ &0 <= h /\ h * B <= &1 /\
        (!p s. s IN S ==> abs(adv p s) <= B)
        ==> sum S (mw_weight (SUC t) adv S h) <=
            sum S (mw_weight t adv S h) *
            exp(h * sum S (\s. mw_dist t adv S h s *
                               adv (mw_dist t adv S h) s) +
                &4 * h pow 2 * B pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `W = sum S (mw_weight t (adv:(A->real)->A->real) S h)` THEN
  ABBREV_TAC `p = mw_dist t (adv:(A->real)->A->real) S h` THEN
  ABBREV_TAC `u = (adv:(A->real)->A->real) p` THEN
  SUBGOAL_THEN `&0 < W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_SIMP_TAC[MW_SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:A. mw_weight t adv S h s = W * p s` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "p" THEN REWRITE_TAC[mw_dist] THEN
    UNDISCH_TAC `&0 < W` THEN EXPAND_TAC "W" THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:A. &0 <= p s` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_MESON_TAC[MW_DIST_PROB]; ALL_TAC] THEN
  SUBGOAL_THEN `sum S (p:A->real) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_MESON_TAC[MW_DIST_PROB]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum S
    (\s:A. W * p s * (&1 + h * u s + &4 * h pow 2 * B pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:A` THEN DISCH_TAC THEN
    REWRITE_TAC[MW_WEIGHT_SUC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((u:A->real) s) <= B` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 + h * (u:A->real) s + &4 * (h * u s) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_QUAD_BOUND THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(h:real) * B` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> &1 + x + &4 * a <= &1 + x +
      &4 * b`) THEN
    REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = &4 * h pow 2 * B pow 2` THEN
  SUBGOAL_THEN
   `!s:A. W * p s * (&1 + h * u s + c) =
          (W * (&1 + c)) * p s + (W * h) * (p s * u s)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL] THEN
  ABBREV_TAC `q = sum S (\s:A. p s * u s)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `W * (&1 + (h * q + c))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_EXP_LE_X]]);;

let MW_SUM_BOUND = prove
 (`!Tn (adv:(A->real)->A->real) S h B.
        FINITE S /\ ~(S = {}) /\ &0 <= h /\ h * B <= &1 /\
        (!p s. s IN S ==> abs(adv p s) <= B)
        ==> sum S (mw_weight Tn adv S h) <=
            &(CARD S) *
            exp(h * sum {t | t < Tn}
                        (\t. sum S (\s. mw_dist t adv S h s *
                                        adv (mw_dist t adv S h) s)) +
                &Tn * &4 * h pow 2 * B pow 2)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `mw_weight 0 (adv:(A->real)->A->real) S h = \s. &1`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; mw_weight]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST; LT; EMPTY_GSPEC; SUM_CLAUSES] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_LID; REAL_EXP_0;
                REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum S (mw_weight Tn (adv:(A->real)->A->real) S h) *
              exp(h * sum S (\s. mw_dist Tn adv S h s *
                                 adv (mw_dist Tn adv S h) s) +
                  &4 * h pow 2 * B pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MW_SUM_STEP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`adv:(A->real)->A->real`; `S:A->bool`;
                                `h:real`; `B:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&(CARD(S:A->bool)) *
               exp(h * sum {t | t < Tn}
                         (\t. sum S (\s. mw_dist t adv S h s *
                                         adv (mw_dist t adv S h) s)) +
                   &Tn * &4 * h pow 2 * B pow 2)) *
              exp(h * sum S (\s. mw_dist Tn adv S h s *
                                 adv (mw_dist Tn adv S h) s) +
                  &4 * h pow 2 * B pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LT; SET_RULE `{i:num | i = t \/ P i} = t INSERT {i | P i}`] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!h a b n c:real. (h * a + n * c) + (h * b + c) =
                     h * (b + a) + (n + &1) * c`));;

let MW_REGRET = prove
 (`!Tn (adv:(A->real)->A->real) S h B s0.
        FINITE S /\ s0 IN S /\ &0 < h /\ h * B <= &1 /\
        (!p s. s IN S ==> abs(adv p s) <= B)
        ==> sum {t | t < Tn} (\t. adv (mw_dist t adv S h) s0) <=
            sum {t | t < Tn}
                (\t. sum S (\s. mw_dist t adv S h s *
                                adv (mw_dist t adv S h) s)) +
            log(&(CARD S)) / h + &4 * &Tn * h * B pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(S:A->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(CARD(S:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`Tn:num`; `adv:(A->real)->A->real`; `S:A->bool`; `h:real`;
                `B:real`] MW_SUM_BOUND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `Q = sum {t | t < Tn}
                      (\t. sum S (\s. mw_dist t
                        (adv:(A->real)->A->real) S h s *
                                      adv (mw_dist t adv S h) s))` THEN
  ABBREV_TAC `U = sum {t | t < Tn}
                      (\t. (adv:(A->real)->A->real)
                        (mw_dist t adv S h) s0)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `exp(h * U) <= &(CARD(S:A->bool)) *
                exp(h * Q + &Tn * &4 * h pow 2 * B pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum S (mw_weight Tn (adv:(A->real)->A->real) S h)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`{s0:A}`; `S:A->bool`;
                   `mw_weight Tn (adv:(A->real)->A->real) S h`]
           SUM_SUBSET_SIMPLE) THEN
    ASM_SIMP_TAC[SUM_SING; SING_SUBSET; MW_WEIGHT_POS; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[GSYM MW_WEIGHT_EXPLICIT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LOG_MONO_LE_IMP o
    CONJ (SPEC `(h:real) * U` REAL_EXP_POS_LT)) THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `U <= Q + log(&(CARD(S:A->bool))) / h + &4 * &Tn * h * B pow 2`
  (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `h * U <= h * (Q + log(&(CARD(S:A->bool))) / h +
                              &4 * &Tn * h * B pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&(CARD(S:A->bool))) +
                (h * Q + &Tn * &4 * h pow 2 * B pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial approximation of the positive part; means.                     *)
(* ------------------------------------------------------------------------- *)

let POS_PART_POLY = prove
 (`!e. &0 < e
       ==> ?m c. !z. abs z <= &1
                     ==> abs(max z (&0) - sum(0..m) (\i. c i * z pow i)) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real. max z (&0)`; `real_interval[-- &1,&1]`; `e:real`]
         REAL_STONE_WEIERSTRASS_POLYNOMIAL_FUNCTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[polynomial_function] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `c:num->real`)) ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `c:num->real`] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real`) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let SUM_MIX_POWER = prove
 (`!(X:A->bool) (S:B->bool) p th w i.
        FINITE X /\ FINITE S
        ==> sum X (\x. w x * sum S (\s. p s * th s x) pow i) =
            sum (cartesian_product {j | j < i} (\j. S))
                (\sq. product {j | j < i} (\j. p (sq j)) *
                      sum X (\x. w x * product {j | j < i}
                                               (\j. th (sq j) x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:A. sum (S:B->bool) (\s. p s * th s x) pow i =
          sum (cartesian_product {j | j < i} (\j. S))
              (\sq. product {j | j < i} (\j. p (sq j)) *
                    product {j | j < i} (\j. th (sq j) x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`{j:num | j < i}`; `\j:num. (S:B->bool)`;
                   `\j:num s:B. p s * th s (x:A):real`]
           PRODUCT_SUM_CARTESIAN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG_LT] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!a b c:real. a * b * c = b * a * c`));;

let MIX_POWER_BOUND = prove
 (`!(X:A->bool) (S:B->bool) p th w i e.
        FINITE X /\ FINITE S /\ (!s. s IN S ==> &0 <= p s) /\
        sum S p = &1 /\
        (!sq. (!j. j < i ==> sq j IN S)
              ==> abs(sum X (\x. w x * product {j | j < i}
                                                 (\j. th (sq j) x))) <= e)
        ==> abs(sum X (\x. w x * sum S (\s. p s * th s x) pow i)) <= e`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUM_MIX_POWER] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (cartesian_product {j:num | j < i} (\j. (S:B->bool)))
                  (\sq. product {j:num | j < i} (\j. p (sq j)) * e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN
    ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG_LT] THEN
    X_GEN_TAC `sq:num->B` THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_ABS_REFL] THEN
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SUM_RMUL] THEN
    MP_TAC(ISPECL [`{j:num | j < i}`; `\j:num. (S:B->bool)`;
                   `\j:num. (p:B->real)`] PRODUCT_SUM_CARTESIAN) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; ETA_AX] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG_LT] THEN
    ASM_REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_LE_REFL]]);;

let FMEAN_MIX_POWER_BOUND = prove
 (`!(X:A->bool) (S:B->bool) p th w i e.
        FINITE X /\ ~(X = {}) /\ FINITE S /\ (!s. s IN S ==> &0 <= p s) /\
        sum S p = &1 /\
        (!sq. (!j. j < i ==> sq j IN S)
              ==> abs(fmean X (\x. w x * product {j | j < i}
                                                  (\j. th (sq j) x))) <= e)
        ==> abs(fmean X (\x. w x * sum S (\s. p s * th s x) pow i)) <= e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(CARD(X:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[fmean; REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC MIX_POWER_BOUND THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `sq:num->B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sq:num->B`) THEN
  ASM_REWRITE_TAC[fmean; REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

let DMT_POLY_BOUND = prove
 (`!(X:A->bool) (S:B->bool) th nu p m c e'.
        FINITE X /\ ~(X = {}) /\ FINITE S /\
        (!s. s IN S ==> &0 <= p s) /\ sum S p = &1 /\
        (!d sq. d <= m /\ (!j. j < d ==> sq j IN S)
                ==> abs(fmean X (\x. (nu x - &1) *
                                     product {j | j < d} (\j. th (sq j) x)))
                    <= e')
        ==> abs(fmean X (\x. (nu x - &1) *
                             sum(0..m) (\i. c i *
                                            sum S (\s. p s * th s x) pow i)))
            <= sum(0..m) (\i. abs(c i)) * e'`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `w * c * z:real = c * (w * z)`] THEN
  ASM_SIMP_TAC[FMEAN_SUM; FINITE_NUMSEG; FMEAN_LMUL] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_ABS_LE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC FMEAN_MIX_POWER_BOUND THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The dense model theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let DMT_BEST_RESPONSE = prove
 (`!(X:A->bool) (S:B->bool) th nu f p m c e e'.
        FINITE X /\ ~(X = {}) /\ FINITE S /\ &0 <= e /\
        (!s. s IN S ==> &0 <= p s) /\ sum S p = &1 /\
        (!s x. s IN S /\ x IN X ==> abs(th s x) <= &1) /\
        (!x. x IN X ==> &0 <= f x /\ f x <= nu x) /\
        (!z. abs z <= &1
             ==> abs(max z (&0) - sum(0..m) (\i. c i * z pow i)) <= e / &8) /\
        (!d sq. d <= m /\ (!j. j < d ==> sq j IN S)
                ==> abs(fmean X (\x. (nu x - &1) *
                                     product {j | j < d} (\j. th (sq j) x)))
                    <= e')
        ==> fmean X (\x. (f x - (if &0 < sum S (\s. p s * th s x) then &1
                                 else &0)) *
                         sum S (\s. p s * th s x))
            <= e / &8 + sum(0..m) (\i. abs(c i)) * e' + e / &8 * (&1 + e')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `fmean X (nu:A->real) <= &1 + e'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `\j:num. (ARB:B)`]) THEN
    REWRITE_TAC[LE_0; LT; EMPTY_GSPEC; PRODUCT_CLAUSES; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[FMEAN_SUB; FMEAN_CONST; ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:A->bool`; `S:B->bool`; `th:B->A->real`; `nu:A->real`;
                 `p:B->real`; `m:num`; `c:num->real`; `e':real`]
         DMT_POLY_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = sum(0..m) (\i. abs((c:num->real) i))` THEN
  ABBREV_TAC `q = \x:A. sum (S:B->bool) (\s. p s * th s x)` THEN
  SUBGOAL_THEN `!x:A. sum (S:B->bool) (\s. p s * th s x) = q x`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `P = \z. sum(0..m) (\i. (c:num->real) i * z pow i)` THEN
  SUBGOAL_THEN `!z. sum(0..m) (\i. (c:num->real) i * z pow i) = P z`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x:A. x IN X ==> abs(q x) <= &1` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "q" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (S:B->bool) (\s. p s * &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:B` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x <= x`; REAL_LE_REFL];
      ASM_REWRITE_TAC[REAL_MUL_RID; ETA_AX; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fmean X (\x:A. (f x - (if &0 < q x then &1 else &0)) * q x) <=
    fmean X (\x. (nu x - &1) * P(q x) +
                 (P(q x) - max (q x) (&0)) + e / &8 * nu x)`
  MP_TAC THENL
   [MATCH_MP_TAC FMEAN_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `max ((q:A->real) x) (&0) <= P(q x) + e / &8` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(q:A->real) x` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `max:real->real->real`))
                             (concl th))) THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= f x /\ f x <= (nu:A->real) x` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `max ((q:A->real) x) (&0) = q x`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
      THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `f x * (q:A->real) x <= nu x * q x` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `nu x * (q:A->real) x <= nu x * (P(q x) + e / &8)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `max ((q:A->real) x) (&0) = &0`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
      THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `f x * (q:A->real) x <= &0` MP_TAC THENL
       [REWRITE_TAC[REAL_ARITH `a * b <= &0 <=> &0 <= a * --b`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= nu x * (P((q:A->real) x) + e / &8)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ASM_SIMP_TAC[FMEAN_ADD; FMEAN_LMUL] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `fmean X (\x:A. P((q:A->real) x) - max (q x) (&0)) <= e / &8`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `fmean X (\x:A. e / &8)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(q:A->real) x` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `max:real->real->real`))
                             (concl th))) THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[FMEAN_CONST; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `e / &8 * fmean X (nu:A->real) <= e / &8 * (&1 + e')`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `abs(fmean X (\x:A. (nu x - &1) * P((q:A->real) x))) <= R * e'` THEN
  ASM_REAL_ARITH_TAC);;

let FMEAN_MIX = prove
 (`!(X:A->bool) (S:B->bool) p g th.
        FINITE X /\ FINITE S
        ==> sum S (\s. p s * fmean X (\x. g x * th s x)) =
            fmean X (\x. g x * sum S (\s. p s * th s x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[FMEAN_SUM] THEN MATCH_MP_TAC SUM_EQ THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FMEAN_LMUL] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC);;

let FMEAN_AVERAGE = prove
 (`!(X:A->bool) Tn g hh k.
        FINITE X /\ 1 <= Tn
        ==> fmean X (\x. (g x - sum {t | t < Tn} (\t. hh t x) / &Tn) * k x) =
            sum {t | t < Tn} (\t. fmean X (\x. (g x - hh t x) * k x)) / &Tn`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM FMEAN_SUM; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM FMEAN_LMUL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
  SIMP_TAC[SUM_RMUL; SUM_SUB; FINITE_NUMSEG_LT; GSYM REAL_SUB_RDISTRIB] THEN
  SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  SPEC_TAC(`sum {t | t < Tn} (\t. (hh:num->A->real) t x)`,`ss:real`) THEN
  GEN_TAC THEN
  SUBGOAL_THEN `~(&Tn = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let DENSE_MODEL = prove
 (`!e. &0 < e /\ e <= &1
       ==> ?D e'. &0 < e' /\
           !(X:A->bool) (S:B->bool) th nu f.
             FINITE X /\ ~(X = {}) /\ FINITE S /\ ~(S = {}) /\
             (!s x. s IN S /\ x IN X ==> abs(th s x) <= &1) /\
             (!x. x IN X ==> &0 <= f x /\ f x <= nu x) /\
             (!d sq. d <= (D:num) /\ (!j. j < d ==> sq j IN S)
                     ==> abs(fmean X (\x. (nu x - &1) *
                                          product {j | j < d}
                                                  (\j. th (sq j) x)))
                         <= e')
             ==> ?ft. (!x. &0 <= ft x /\ ft x <= &1) /\
                      !s. s IN S ==> fmean X (\x. (f x - ft x) * th s x) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e / &8` POS_PART_POLY) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `c:num->real`)) THEN
  ABBREV_TAC `R = sum(0..m) (\i. abs((c:num->real) i))` THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_ABS_POS];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `e / (&24 * (R + &1))`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e' = e / (&24 * (R + &1))` THEN
  SUBGOAL_THEN `&0 <= e' /\ e' <= &1 / &24 /\ R * e' <= e / &24`
  STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "e'" THEN
    SUBGOAL_THEN `&0 < R + &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &24`] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `R * e / (&24 * (R + &1)) = (R / (R + &1)) * (e / &24)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < R + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `fmean X (nu:A->real) <= &1 + e'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `\j:num. (ARB:B)`]) THEN
    REWRITE_TAC[LE_0; LT; EMPTY_GSPEC; PRODUCT_CLAUSES; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[FMEAN_SUB; FMEAN_CONST; ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `br = \(p:B->real) (x:A).
                     if &0 < sum S (\s. p s * th s x) then &1 else &0` THEN
  ABBREV_TAC `adv = \(p:B->real) (s:B).
                      fmean X (\x:A. (f x - br p x) * th s x)` THEN
  SUBGOAL_THEN `!p s. s IN S ==> abs((adv:(B->real)->B->real) p s) <= &3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "adv" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `fmean X (\x:A. nu x + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `fmean X
        (\x:A. abs((f x - br (p:B->real) x) * th (s:B) x))` THEN
      ASM_SIMP_TAC[FMEAN_ABS_LE] THEN MATCH_MP_TAC FMEAN_LE THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN
      EXPAND_TAC "br" THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o
        check (fun th -> can (find_term ((=) `nu:A->real`)) (concl th) &&
                         is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[FMEAN_ADD; FMEAN_CONST; ETA_AX] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `h = e / &216` THEN
  SUBGOAL_THEN `&0 < h /\ h * &3 <= &1 /\ &4 * h * &3 pow 2 = e / &6`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&6 * log(&(CARD(S:B->bool))) / (h * e) + &1`
    REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `Tn:num`) THEN
  SUBGOAL_THEN `&1 <= &(CARD(S:B->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&(CARD(S:B->bool)))` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &Tn /\ log(&(CARD(S:B->bool))) / h <= &Tn * e / &6`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &6 * log(&(CARD(S:B->bool))) / (h * e)` ASSUME_TAC
    THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&6 * log(&(CARD(S:B->bool))) / (h * e)) * e / &6 * h` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MAP_EVERY UNDISCH_TAC [`&0 < h`; `&0 < e`] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a * e / &6 * h = a * (e / &6 * h)`;
                REAL_ARITH `(t * e / &6) * h = t * (e / &6 * h)`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `\x:A. sum {t | t < Tn}
                       (\t. br (mw_dist t (adv:(B->real)->B->real) S h) x) /
                    &Tn` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &Tn` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                 REAL_MUL_LID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "br" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum {t | t < Tn} (\t:num. &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
        REPEAT STRIP_TAC THEN EXPAND_TAC "br" THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REAL_ARITH_TAC;
        SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `s0:B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Tn:num`; `adv:(B->real)->B->real`; `S:B->bool`; `h:real`;
                 `&3`; `s0:B`] MW_REGRET) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!t. sum S (\s. mw_dist t (adv:(B->real)->B->real) S h s *
                   adv (mw_dist t adv S h) s) <= e / &3`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:num` THEN
    MP_TAC(ISPECL [`t:num`; `adv:(B->real)->B->real`; `S:B->bool`; `h:real`]
           MW_DIST_PROB) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `p = mw_dist t (adv:(B->real)->B->real) S h` THEN
    STRIP_TAC THEN EXPAND_TAC "adv" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FMEAN_MIX] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &8 + R * e' + e / &8 * (&1 + e')` THEN CONJ_TAC THENL
     [EXPAND_TAC "br" THEN REWRITE_TAC[] THEN
      EXPAND_TAC "R" THEN MATCH_MP_TAC DMT_BEST_RESPONSE THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `e / &8 * e' <= e / &8 * (&1 / &24)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {t | t < Tn}
        (\t. sum S (\s. mw_dist t (adv:(B->real)->B->real) S h s *
                        adv (mw_dist t adv S h) s)) <= &Tn * e / &3`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {t | t < Tn} (\t:num. e / &3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
      SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `fmean X (\x:A. (f x - sum {t | t < Tn}
                           (\t. br (mw_dist t
                             (adv:(B->real)->B->real) S h) x) /
                         &Tn) * th s0 x) =
    sum {t | t < Tn} (\t. adv (mw_dist t adv S h) s0) / &Tn`
  SUBST1_TAC THENL
   [EXPAND_TAC "adv" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC FMEAN_AVERAGE THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Tn` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `&4 * &Tn * h * &3 pow 2 = &Tn * e / &6` ASSUME_TAC THENL
   [UNDISCH_TAC `&4 * h * &3 pow 2 = e / &6` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC(MATCH_MP (REAL_ARITH
   `!u a b c e t:real. u <= a + b + c
                  ==> &0 <= e * t /\ a <= t * e / &3 /\ b <= t * e / &6 /\
                      c = t * e / &6
                      ==> u <= e * t`) th)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
