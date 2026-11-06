(* ========================================================================= *)
(* Bounded gaps between primes, part 3: the product weights.                 *)
(*                                                                           *)
(* The weights are y c = col_weight G k c = prod_{i = 1..k} G(prod col_class *)
(* c i), col_class c i = {p | c p = i}, for G >= 0 decreasing on r >= 1 and  *)
(* zero for r >= Rt.  With u = 1/(p - 1) and A ranging over the subsets of   *)
(* P:                                                                        *)
(*   Lambda = sum_A G(prod A) prod_A u,  Gamma = sum_A G(prod A)^2 prod_A u, *)
(*   M1 = sum_A G(prod A)^2 prod_A u log(prod A),  eta = sum_P u^2.          *)
(*                                                                           *)
(* * recip_phi_sum P x = sum_{t SUBSET P, prod t < x} prod_t u:              *)
(*   RECIP_PHI_SUM_LOWER (c0 log x <= recip_phi_sum P x, c0 = prod_{p <= D0} *)
(*   (1 - 1/p), when P contains the primes in (D0, x)) and                   *)
(*   RECIP_PHI_SUM_UPPER (from SUM_INV_PHI_UPPER, with the Titchmarsh        *)
(*   constant Kt).                                                           *)
(* * Sums over tuples x IN cartesian_product Ix (\i. {A | A SUBSET P}):      *)
(*   TUPLE_SUM_POWER, TUPLE_SUM_FIRST_MOMENT, TUPLE_PAIR_BOUND,              *)
(*   TUPLE_NONDISJOINT_BOUND (tuples with two intersecting components),      *)
(*   TUPLE_TAIL_MARKOV, TUPLE_SIGMA_BOUND and TUPLE_GOOD_LOWER.              *)
(* * S1_WEIGHT_UPPER: sum_c y c^2 / prod (p - 1) <= Gamma^k (the colour      *)
(*   classes embed colourings into k-tuples of sets, COL_SET_TUPLE_INJ).     *)
(* * For S2: col_ext and col_of_sets build colourings from sets and tuples;  *)
(*   T_LOWER, LAMBDA_DISJOINT_LOWER, S2_TERMWISE, COL_OF_SETS_SUM_LOWER and  *)
(*   S2_WEIGHT_LOWER:                                                        *)
(*     sum_e rho(e) T(e)^2 >= Lambda^2 (Gamma^(k - 1) (1 - (k - 1)^2 eta     *)
(*                            - 2 (k - 1) eta) - (k - 1) M1 Gamma^(k - 2) /  *)
(*                            log(R / Rt)).                                  *)
(* ========================================================================= *)

needs "Sieve/bg_s2.ml";;
needs "Sieve/titchmarsh.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Sums of prod 1/(p - 1) over subsets with bounded product.                 *)
(* ------------------------------------------------------------------------- *)

let recip_phi_sum = new_definition
 `recip_phi_sum P x = sum {t | t SUBSET P /\ &(nproduct t (\p. p)) < x}
                 (\t. product t (\p. inv(&p - &1)))`;;

let RECIP_PHI_SUM_POS = prove
 (`!P x. FINITE P /\ (!p. p IN P ==> 2 <= p) ==> &0 <= recip_phi_sum P x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[recip_phi_sum] THEN
  MATCH_MP_TAC SUM_POS_LE THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

let RECIP_PHI_SUM_LOWER = prove
 (`!D0 P x.
     FINITE P /\ (!p. p IN P ==> prime p) /\
     (!p. prime p /\ D0 < p /\ &p < x ==> p IN P) /\ &1 <= x
     ==> product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) * log x
         <= recip_phi_sum P x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Wp = {p | prime p /\ p <= D0}` THEN
  SUBGOAL_THEN `FINITE(Wp:num->bool) /\ (!p. p IN Wp ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Wp" THEN SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC `W = nproduct Wp (\p:num. p)` THEN
  SUBGOAL_THEN `1 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`W:num`; `x:real`] SELBERG_G_ONE_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(phi W) / &W = product Wp (\p. &1 - inv(&p))`
  SUBST1_TAC THENL
   [EXPAND_TAC "W" THEN
    SIMP_TAC[REAL_PHI_NPRODUCT_PRIMES; REAL_OF_NUM_NPRODUCT;
             ASSUME `FINITE(Wp:num->bool)`;
             ASSUME `!p. p IN Wp ==> prime p`] THEN
    SIMP_TAC[GSYM PRODUCT_DIV; ASSUME `FINITE(Wp:num->bool)`] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN SUBGOAL_THEN `~(&p = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[selberg_G; recip_phi_sum; selberg_H] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET {p | prime p /\ &p < x /\ ~(p divides W)} /\
                       &(nproduct t (\p. p)) < x}
                  (\t. product t (\p. inv(&p - &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[selberg_H] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN `prime p` (fun th -> MESON_TAC[th; PRIME_GE_2]) THEN
      ASM SET_TAC[];
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{t:num->bool | t SUBSET P}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:num->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `prime p /\ &p < x /\ ~(p divides W)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(p divides W)` THEN EXPAND_TAC "W" THEN
    ASM_SIMP_TAC[PRIME_DIVIDES_NPRODUCT_PRIMES] THEN EXPAND_TAC "Wp" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; NOT_LE];
    X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `prime p` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC]);;

let RECIP_PHI_SUM_UPPER = prove
 (`!Kt D0 P x.
     ((\n. product {p | prime p /\ p <= n}
                   (\p. &1 + inv(&p * (&p - &1)))) ---> Kt) sequentially /\
     FINITE P /\ (!p. p IN P ==> prime p /\ D0 < p) /\ &1 <= x
     ==> recip_phi_sum P x *
         product {p | prime p /\ p <= D0} (\p. &1 + inv(&p - &1))
         <= Kt * (&1 + log(&(nproduct {p | prime p /\ p <= D0} (\p. p)) * x))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Wp = {p | prime p /\ p <= D0}` THEN
  SUBGOAL_THEN `FINITE(Wp:num->bool) /\ (!p. p IN Wp ==> prime p) /\
                DISJOINT Wp (P:num->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Wp" THEN SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[NOT_LE];
    ALL_TAC] THEN
  ABBREV_TAC `W = nproduct Wp (\p:num. p)` THEN
  SUBGOAL_THEN `1 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &W * x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE; LE_0];
    ALL_TAC] THEN
  MP_TAC(SPEC `&W * x` NUM_RANGE_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= Kt` ASSUME_TAC THENL
   [ASM_MESON_TAC[TITCHMARSH_K_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&W * x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..n) (\d. inv(&(phi d)))` THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUM_CLAUSES] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kt * (&1 + log(&n))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_INV_PHI_UPPER THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> &1 + a <= &1 + b`) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_ARITH_TAC]] THEN
  ASM_SIMP_TAC[PRODUCT_ADD_EXPAND; recip_phi_sum] THEN
  ABBREV_TAC `T1 = {t | t SUBSET P /\ &(nproduct t (\p:num. p)) < x}` THEN
  ABBREV_TAC `T2 = {k:num->bool | k SUBSET Wp}` THEN
  SUBGOAL_THEN `FINITE(T1:(num->bool)->bool) /\ FINITE(T2:(num->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN
    SIMP_TAC[FINITE_POWERSET; ASSUME `FINITE(Wp:num->bool)`] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t:num->bool | t SUBSET P}` THEN
    SIMP_TAC[FINITE_POWERSET; ASSUME `FINITE(P:num->bool)`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!t. t IN T1 ==> FINITE t /\ t SUBSET P /\
             &(nproduct t (\p:num. p)) < x) /\
    (!k. k IN T2 ==> FINITE k /\ k SUBSET (Wp:num->bool))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[FINITE_SUBSET; ASSUME `FINITE(P:num->bool)`;
              ASSUME `FINITE(Wp:num->bool)`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_SUM] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_PRODUCT o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (IMAGE (\(t,k). nproduct (t UNION k) (\p:num. p))
               {t,k | t IN T1 /\ k IN T2})
        (\d. inv(&(phi d)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
      MAP_EVERY X_GEN_TAC
       [`t1:num->bool`; `k1:num->bool`; `t2:num->bool`; `k2:num->bool`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `t1 SUBSET (P:num->bool) /\ t2 SUBSET P /\ k1 SUBSET Wp /\
                    k2 SUBSET (Wp:num->bool) /\ FINITE t1 /\ FINITE t2 /\
                    FINITE k1 /\ FINITE k2`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `t1 UNION k1 = t2 UNION (k2:num->bool)` MP_TAC THENL
       [MATCH_MP_TAC NPRODUCT_PRIMES_INJ THEN
         ASM_REWRITE_TAC[FINITE_UNION] THEN
        REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[SUBSET];
        ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT Wp (P:num->bool)` THEN
      MAP_EVERY UNDISCH_TAC
       [`t1 SUBSET (P:num->bool)`; `t2 SUBSET (P:num->bool)`;
        `k1 SUBSET (Wp:num->bool)`; `k2 SUBSET (Wp:num->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM;
     IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:num->bool`; `k:num->bool`] THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    SUBGOAL_THEN `t SUBSET (P:num->bool) /\ k SUBSET (Wp:num->bool) /\
                  FINITE t /\ FINITE k`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(!p. p IN t UNION k ==> prime p) /\ DISJOINT t (k:num->bool)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNION] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET];
        UNDISCH_TAC `DISJOINT Wp (P:num->bool)` THEN
        MAP_EVERY UNDISCH_TAC [`t SUBSET (P:num->bool)`;
                               `k SUBSET (Wp:num->bool)`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_PHI_NPRODUCT_PRIMES; FINITE_UNION; GSYM PRODUCT_INV] THEN
    ASM_SIMP_TAC[PRODUCT_UNION];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:num->bool`; `k:num->bool`] THEN STRIP_TAC THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    can (find_term ((=) `1..n`)) (concl th))) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `t SUBSET (P:num->bool) /\ k SUBSET (Wp:num->bool) /\
                FINITE t /\ FINITE k /\ &(nproduct t (\p:num. p)) < x`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT t (k:num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT Wp (P:num->bool)` THEN
    MAP_EVERY UNDISCH_TAC [`t SUBSET (P:num->bool)`;
     `k SUBSET (Wp:num->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NPRODUCT_UNION] THEN
  SUBGOAL_THEN `1 <= nproduct t (\p:num. p) /\ 1 <= nproduct k (\p:num. p) /\
                nproduct k (\p:num. p) <= W`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ;
      SUBSET];
      MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ;
       SUBSET];
      EXPAND_TAC "W" THEN MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `x * &(nproduct k (\p:num. p))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Sums over tuples of subsets.                                              *)
(* ------------------------------------------------------------------------- *)

let TUPLE_SUM_POWER = prove
 (`!(Ix:A->bool) (S:B->bool) (f:B->real).
     FINITE Ix /\ FINITE S
     ==> sum (cartesian_product Ix (\i. S)) (\x. product Ix (\i. f(x i))) =
         sum S f pow CARD Ix`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Ix:A->bool`; `\i:A. (S:B->bool)`; `\i:A. (f:B->real)`]
         PRODUCT_SUM_CARTESIAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[PRODUCT_CONST; ETA_AX]);;

let PRODUCT_DELETE_COND = prove
 (`!s (j:A) (g:A->real) h.
     product (s DELETE j) (\i. if i = j then g i else h i) =
     product (s DELETE j) h`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[IN_DELETE]);;

let TUPLE_SUM_FIRST_MOMENT = prove
 (`!(Ix:A->bool) (S:B->bool) (f:B->real) (l:B->real).
     FINITE Ix /\ FINITE S
     ==> sum (cartesian_product Ix (\i. S))
             (\x. product Ix (\i. f(x i)) * sum Ix (\i. l(x i))) =
         &(CARD Ix) * sum S (\a. f a * l a) * sum S f pow (CARD Ix - 1)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!j:A. j IN Ix
        ==> sum (cartesian_product (Ix:A->bool) (\i. (S:B->bool)))
                (\x. product Ix (\i. (f:B->real)(x i)) * (l:B->real)(x j)) =
            sum S (\a. f a * l a) * sum S f pow (CARD Ix - 1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`Ix:A->bool`; `\i:A. (S:B->bool)`;
                   `\i:A a:B. if i = j then (f:B->real) a * (l:B->real) a
                              else f a`] PRODUCT_SUM_CARTESIAN) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `(a:real) = a' /\ (b:real) = b' ==> a = b ==> b' = a'`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `Ix = (j:A) INSERT (Ix DELETE j)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
      SUBGOAL_THEN
       `product (Ix DELETE j)
          (\i:A. sum S (\a:B. if i = j then f a * l a else f a)) =
        product (Ix DELETE j) (\i. sum S (f:B->real))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[IN_DELETE] THEN
        REWRITE_TAC[ETA_AX];
        ASM_SIMP_TAC[PRODUCT_CONST; FINITE_DELETE; CARD_DELETE] THEN
        ASM_SIMP_TAC[SET_RULE `(j:A) IN s ==> j INSERT (s DELETE j) = s`]];
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:A->B` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `Ix = (j:A) INSERT (Ix DELETE j)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
      REWRITE_TAC[PRODUCT_DELETE_COND] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (Ix:A->bool) (\j. sum S (\a. (f:B->real) a * (l:B->real) a) *
                                    sum S f pow (CARD Ix - 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[SUM_CONST] THEN REAL_ARITH_TAC]);;

let SUM_SUBSETS_CONTAINING = prove
 (`!P p (f:(num->bool)->real) u.
     FINITE P /\ (!A. A SUBSET P ==> &0 <= f A) /\ &0 <= u /\
     (!A. A SUBSET P /\ p IN A ==> f A <= u * f (A DELETE p))
     ==> sum {A | A SUBSET P /\ p IN A} f <= u * sum {A | A SUBSET P} f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {A:num->bool | A SUBSET P /\ p IN A}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{A:num->bool | A SUBSET P}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {A | A SUBSET P /\ p IN A}
                  (\A. u * (f:(num->bool)->real) (A DELETE p))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (\A. A DELETE p) {A | A SUBSET P /\ p IN A})
                  (f:(num->bool)->real)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SET_TAC[];
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let PRODUCT_TWO_POINTS = prove
 (`!(Ix:A->bool) i j a.
     FINITE Ix /\ i IN Ix /\ j IN Ix /\ ~(i = j)
     ==> product Ix (\l. if l = i \/ l = j then a else &1) = a pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM PRODUCT_RESTRICT_SET] THEN
  SUBGOAL_THEN `{l:A | l IN Ix /\ (l = i \/ l = j)} = {i,j}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CONST; FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES;
               IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let TUPLE_PAIR_BOUND = prove
 (`!(Ix:A->bool) P (f:(num->bool)->real) u i j p.
     FINITE Ix /\ FINITE P /\ (!A. A SUBSET P ==> &0 <= f A) /\ &0 <= u /\
     (!A. A SUBSET P /\ p IN A ==> f A <= u * f (A DELETE p)) /\
     i IN Ix /\ j IN Ix /\ ~(i = j)
     ==> sum (cartesian_product Ix (\l. {A | A SUBSET P}))
             (\x. (if p IN x i /\ p IN x j then &1 else &0) *
                  product Ix (\l. f(x l)))
         <= u pow 2 * sum {A | A SUBSET P} f pow CARD Ix`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = \l:A. if l = i \/ l = j then {A | A SUBSET P /\ p IN A}
                        else {A:num->bool | A SUBSET P}` THEN
  SUBGOAL_THEN `!l:A. FINITE((s:A->(num->bool)->bool) l)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "s" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{A:num->bool | A SUBSET P}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (cartesian_product Ix (s:A->(num->bool)->bool))
                  (\x. product Ix (\l. f(x l)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET; REAL_MUL_LZERO] THEN
    ONCE_REWRITE_TAC[MESON[REAL_MUL_LID; REAL_MUL_LZERO]
     `(if b then &1 else &0) * x = (if b then x else &0)`] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "s" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CARTESIAN_PRODUCT] THEN
    X_GEN_TAC `x:A->num->bool` THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [X_GEN_TAC `l:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `l:A`) THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      CONJ_TAC THENL
       [X_GEN_TAC `l:A` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `l:A`) THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN SIMP_TAC[IN_ELIM_THM];
        FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:A` th) THEN
                                MP_TAC(SPEC `j:A` th)) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ix:A->bool`; `s:A->(num->bool)->bool`;
                 `\l:A. (f:(num->bool)->real)`] PRODUCT_SUM_CARTESIAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product Ix (\l:A. (if l = i \/ l = j then u else &1) *
                         sum {A | A SUBSET P} (f:(num->bool)->real))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:A` THEN DISCH_TAC THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN
     `&0 <= sum {A | A SUBSET P} (f:(num->bool)->real) /\
      &0 <= sum {A | A SUBSET P /\ p IN A} f`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_LE_REFL] THEN
    MATCH_MP_TAC SUM_SUBSETS_CONTAINING THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PRODUCT_MUL; PRODUCT_CONST; PRODUCT_TWO_POINTS] THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

let ELEMENT_LE_SUM = prove
 (`!(s:A->bool) f a. FINITE s /\ a IN s /\ (!x. x IN s ==> &0 <= f x)
                     ==> f a <= sum s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `s:A->bool`; `a:A`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sum (s DELETE (a:A)) f` MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[IN_DELETE]; REAL_ARITH_TAC]);;

let TUPLE_NONDISJOINT_BOUND = prove
 (`!(Ix:A->bool) P (f:(num->bool)->real) (u:num->real).
     FINITE Ix /\ FINITE P /\ (!A. A SUBSET P ==> &0 <= f A) /\
     (!p. p IN P ==> &0 <= u p) /\
     (!A p. A SUBSET P /\ p IN A ==> f A <= u p * f (A DELETE p))
     ==> sum {x | x IN cartesian_product Ix (\i. {A | A SUBSET P}) /\
                  ?i j p. i IN Ix /\ j IN Ix /\ ~(i = j) /\ p IN P /\
                          p IN x i /\ p IN x j}
             (\x. product Ix (\i. f(x i)))
         <= &(CARD Ix) pow 2 * sum P (\p. u p pow 2) *
            sum {A | A SUBSET P} f pow CARD Ix`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Cp = cartesian_product (Ix:A->bool)
                                      (\i. {A:num->bool | A SUBSET P})` THEN
  SUBGOAL_THEN `FINITE(Cp:(A->num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_SIMP_TAC[FINITE_POWERSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN Cp ==> &0 <= product Ix (\i:A. (f:(num->bool)->real)(x i))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ind = \x:A->num->bool i j p.
                 if ~(i = j) /\ p IN x i /\ p IN x j then &1 else &0` THEN
  SUBGOAL_THEN `!x i j p. &0 <= (ind:(A->num->bool)->A->A->num->real) x i j p`
  ASSUME_TAC THENL
   [EXPAND_TAC "ind" THEN REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Cp (\x. sum Ix (\i. sum Ix (\j. sum P (\p.
     (ind:(A->num->bool)->A->A->num->real) x i j p *
     product Ix (\i:A. (f:(num->bool)->real)(x i))))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {x | x IN Cp /\ ?i j p. i IN Ix /\ j IN Ix /\ ~(i = j) /\
                          p IN P /\ p IN x i /\ p IN x j}
     (\x. sum Ix (\i. sum Ix (\j. sum P (\p.
       (ind:(A->num->bool)->A->A->num->real) x i j p *
       product Ix (\i:A. (f:(num->bool)->real)(x i))))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A->num->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `i0:A` (X_CHOOSE_THEN `j0:A`
         (X_CHOOSE_THEN `p0:num` STRIP_ASSUME_TAC)))) THEN
      ASM_SIMP_TAC[SUM_RMUL; FINITE_NUMSEG] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum Ix (\j. sum P (\p.
        (ind:(A->num->bool)->A->A->num->real) x i0 j p))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC(BETA_RULE(ISPECL [`Ix:A->bool`;
          `\i. sum Ix (\j. sum P (\p.
             (ind:(A->num->bool)->A->A->num->real) x i j p))`;
          `i0:A`] ELEMENT_LE_SUM)) THEN
        ASM_SIMP_TAC[SUM_POS_LE]] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum P (\p. (ind:(A->num->bool)->A->A->num->real) x i0 j0 p)`
      THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC(BETA_RULE(ISPECL [`Ix:A->bool`;
          `\j. sum P (\p. (ind:(A->num->bool)->A->A->num->real) x i0 j p)`;
          `j0:A`] ELEMENT_LE_SUM)) THEN
        ASM_SIMP_TAC[SUM_POS_LE]] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(ind:(A->num->bool)->A->A->num->real) x i0 j0 p0` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "ind" THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        MATCH_MP_TAC(BETA_RULE(ISPECL [`P:num->bool`;
          `\p. (ind:(A->num->bool)->A->A->num->real) x i0 j0 p`;
          `p0:num`] ELEMENT_LE_SUM)) THEN
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `x:A->num->bool` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
      STRIP_TAC THEN REPEAT(MATCH_MP_TAC SUM_POS_LE THEN GEN_TAC THEN
                             DISCH_TAC THEN BETA_TAC) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum Cp (\x. sum Ix (\i. sum Ix (\j. sum P (\p.
       (ind:(A->num->bool)->A->A->num->real) x i j p *
       product Ix (\i:A. (f:(num->bool)->real)(x i)))))) =
    sum Ix (\i. sum Ix (\j. sum P (\p. sum Cp (\x.
       ind x i j p * product Ix (\i:A. f(x i))))))`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Ix (\i:A. sum Ix (\j:A. sum P (\p.
     u p pow 2 *
     sum {A | A SUBSET P} (f:(num->bool)->real) pow CARD Ix)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    EXPAND_TAC "ind" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:A = j` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; SUM_0] THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SUM_POS_LE THEN
      ASM_SIMP_TAC[IN_ELIM_THM];
      EXPAND_TAC "Cp" THEN MATCH_MP_TAC TUPLE_PAIR_BOUND THEN
      ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[SUM_CONST; SUM_RMUL] THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_AC; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Colour classes; the weights in S1.                                        *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_GROUP_REAL = prove
 (`!(f:A->B) (g:A->real) s t.
     FINITE s /\ IMAGE f s SUBSET t
     ==> product t (\y. product {x | x IN s /\ f x = y} g) = product s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `( * ):real->real->real` ITERATE_IMAGE_GEN) THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL; GSYM product] THEN
  DISCH_THEN(MP_TAC o SPECL [`f:A->B`; `g:A->real`; `s:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PRODUCT_SUPERSET THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:A->B) x = y} = {}` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[PRODUCT_CLAUSES]]);;

let col_class = new_definition
 `col_class (c:num->num) i = {p | c p = i}`;;

let COL_SUPP_PRODUCT_CLASS = prove
 (`!k P (c:num->num) (u:num->real).
     FINITE P /\ c IN col_set k P
     ==> product (col_supp c) u =
         product (1..k) (\i. product (col_class c i) u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(col_supp c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:num->num`; `u:num->real`; `col_supp c`; `1..k`]
         PRODUCT_GROUP_REAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    ASM_CASES_TAC `(p:num) IN P` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[col_class; col_supp; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_TAC THEN ASM_ARITH_TAC);;

let COL_SET_TUPLE_INJ = prove
 (`!k P (c1:num->num) c2.
     c1 IN col_set k P /\ c2 IN col_set k P /\
     (!i. i IN 1..k ==> col_class c1 i = col_class c2 i)
     ==> c1 = c2`,
  REWRITE_TAC[col_set; col_class; IN_ELIM_THM; EXTENSION; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN
  SUBGOAL_THEN
   `!c:num->num. (!p. (p IN P ==> c p <= k) /\ (~(p IN P) ==> c p = 0))
                 ==> ~(c p = 0) ==> 1 <= c p /\ c p <= k`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    ASM_CASES_TAC `(p:num) IN P` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(c1:num->num) p = 0` THEN
  ASM_CASES_TAC `(c2:num->num) p = 0` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let S1_WEIGHT_UPPER = prove
 (`!k P fam (G:num->real).
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\ fam SUBSET col_set k P /\
     (!r. &0 <= G r)
     ==> sum fam (\c. product (1..k) (\i. G(nproduct (col_class c i) (\p. p)))
                      pow 2 / product (col_supp c) (\p. &p - &1))
         <= sum {A | A SUBSET P}
                (\A. G(nproduct A (\p. p)) pow 2 *
                     product A (\p. inv(&p - &1))) pow k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  ABBREV_TAC `f = \A. (G:num->real)(nproduct A (\p. p)) pow 2 *
                      product A (\p. inv(&p - &1))` THEN
  SUBGOAL_THEN `!A. A SUBSET P ==> &0 <= (f:(num->bool)->real) A`
  ASSUME_TAC THENL
   [X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum fam (\c. product (1..k) (\i. (f:(num->bool)->real) (col_class c i)))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:num->num) IN col_set k P` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN ASM_SIMP_TAC[GSYM PRODUCT_INV;
     FINITE_SUBSET] THEN
    SUBGOAL_THEN `FINITE(col_supp c)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
      REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM PRODUCT_INV] THEN
    MP_TAC(ISPECL [`k:num`; `P:num->bool`; `c:num->num`;
                   `\p:num. inv(&p - &1)`] COL_SUPP_PRODUCT_CLASS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tup = \c:num->num. RESTRICTION (1..k) (col_class c)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (tup:(num->num)->num->num->bool) fam)
                  (\x. product (1..k) (\i. (f:(num->bool)->real) (x i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`c1:num->num`; `c2:num->num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC COL_SET_TUPLE_INJ THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `P:num->bool`] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      UNDISCH_TAC `(tup:(num->num)->num->num->bool) c1 = tup c2` THEN
      EXPAND_TAC "tup" THEN REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
      EXPAND_TAC "tup" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[RESTRICTION]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1..k`; `{A:num->bool | A SUBSET P}`; `f:(num->bool)->real`]
         TUPLE_SUM_POWER) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_POWERSET; CARD_NUMSEG_1] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_POWERSET];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CARTESIAN_PRODUCT] THEN
    X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN EXPAND_TAC "tup" THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[RESTRICTION; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(c:num->num) IN col_set k P` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `i IN 1..k` THEN
    REWRITE_TAC[col_set; col_class; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    MESON_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Building colourings from sets and tuples.                                 *)
(* ------------------------------------------------------------------------- *)

let col_ext = new_definition
 `col_ext m (e:num->num) A = \p. if p IN A then m else e p`;;

let COL_EXT_PROPS = prove
 (`!k m P (e:num->num) A.
     m IN 1..k /\ e IN col_set k P /\ (!p. ~(e p = m)) /\
     A SUBSET P /\ DISJOINT A (col_supp e)
     ==> col_ext m e A IN col_set k P /\ col_strip m (col_ext m e A) = e /\
         col_supp(col_ext m e A) = col_supp e UNION A /\
         col_class (col_ext m e A) m = A /\
         (!i. ~(i = m)
              ==> col_class (col_ext m e A) i = col_class e i DIFF A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN A ==> p IN P /\ (e:num->num) p = 0` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT A (col_supp(e:num->num))` THEN
    UNDISCH_TAC `A SUBSET (P:num->bool)` THEN
    REWRITE_TAC[DISJOINT; SUBSET; col_supp; EXTENSION; IN_INTER; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(e:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_ext; IN_ELIM_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `(p:num) IN A` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[col_strip; col_ext; FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `(p:num) IN A` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[col_supp; col_ext; EXTENSION; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `(p:num) IN A` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[col_class; col_ext; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `(p:num) IN A` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[col_class; col_ext; EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `(p:num) IN A` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let col_weight = new_definition
 `col_weight (G:num->real) k c =
  product (1..k) (\i. G(nproduct (col_class c i) (\p. p)))`;;

let COL_CLASS_SUBSET_SUPP = prove
 (`!c i. ~(i = 0) ==> col_class c i SUBSET col_supp c`,
  REWRITE_TAC[col_class; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let T_LOWER = prove
 (`!k m P R Rt (G:num->real) (e:num->num).
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\ m IN 1..k /\
     e IN col_set k P /\ (!p. ~(e p = m)) /\
     (!r. &0 <= G r) /\ (!r. Rt <= &r ==> G r = &0) /\ &0 < Rt /\
     &(nproduct (col_supp e) (\p. p)) * Rt <= R
     ==> product ((1..k) DELETE m) (\i. G(nproduct (col_class e i) (\p. p))) *
         product (col_supp e) (\p. inv(&p - &1)) *
         sum {A | A SUBSET P /\ DISJOINT A (col_supp e)}
             (\A. G(nproduct A (\p. p)) * product A (\p. inv(&p - &1)))
         <= sum {a | a IN {c | c IN col_set k P /\
                               &(nproduct (col_supp c) (\p. p)) < R} /\
                     col_strip m a = e}
                (\a. col_weight G k a / product (col_supp a) (\p. &p - &1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> &1 <= &p - &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `col_supp e SUBSET (P:num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(e:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(col_supp(e:num->num))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `As = {A | A SUBSET P /\ DISJOINT A (col_supp e) /\
                        &(nproduct A (\p:num. p)) < Rt}` THEN
  SUBGOAL_THEN `FINITE(As:(num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "As" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{A:num->bool | A SUBSET P}` THEN
    SIMP_TAC[FINITE_POWERSET; ASSUME `FINITE(P:num->bool)`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. A IN As ==> A SUBSET P /\ DISJOINT A (col_supp e) /\ FINITE A /\
                    &(nproduct A (\p:num. p)) < Rt`
  ASSUME_TAC THENL
   [EXPAND_TAC "As" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[FINITE_SUBSET; ASSUME `FINITE(P:num->bool)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. A IN As
        ==> col_weight G k (col_ext m e A) /
            product (col_supp(col_ext m e A)) (\p. &p - &1)
            = product ((1..k) DELETE m)
                 (\i. (G:num->real)(nproduct (col_class e i) (\p. p))) *
              product (col_supp e) (\p. inv(&p - &1)) *
              (G:num->real)(nproduct A (\p. p)) *
              product A (\p. inv(&p - &1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `A:num->bool` o check (fun th ->
      can (find_term ((=) `As:(num->bool)->bool`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `e:num->num`;
                   `A:num->bool`] COL_EXT_PROPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[col_weight] THEN
    SUBGOAL_THEN `FINITE(1..k) /\ m IN 1..k` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP (ISPECL
      [`\i. (G:num->real)(nproduct (col_class (col_ext m e A) i) (\p. p))`;
       `1..k`; `m:num`] PRODUCT_DELETE)
      (CONJ (ASSUME `FINITE(1..k)`) th))]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `product ((1..k) DELETE m)
        (\i. (G:num->real)(nproduct (col_class (col_ext m e A) i) (\p. p))) =
      product ((1..k) DELETE m) (\i. G(nproduct (col_class e i) (\p. p)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN
      REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `col_class e i DIFF A = col_class (e:num->num) i`
       (fun th -> REWRITE_TAC[th])
      THEN MP_TAC(SPECL [`e:num->num`; `i:num`] COL_CLASS_SUBSET_SUPP) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT A (col_supp(e:num->num))` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (col_supp e) (A:num->bool)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_UNION] THEN
    SUBGOAL_THEN
     `&0 < product (col_supp e) (\p. &p - &1) /\
      &0 < product A (\p. &p - &1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x`) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[PRODUCT_INV; ASSUME `FINITE(col_supp(e:num->num))`;
             ASSUME `FINITE(A:num->bool)`] THEN
    UNDISCH_TAC `&0 < product (col_supp e) (\p. &p - &1)` THEN
    UNDISCH_TAC `&0 < product A (\p. &p - &1)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum As (\A. col_weight G k (col_ext m e A) /
                          product (col_supp(col_ext m e A))
                            (\p. &p - &1))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum As (\A. product ((1..k) DELETE m)
                 (\i. (G:num->real)(nproduct (col_class e i) (\p. p))) *
              product (col_supp e) (\p. inv(&p - &1)) *
                            (G:num->real)(nproduct A (\p. p)) *
                            product A (\p. inv(&p - &1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
       [EXPAND_TAC "As" THEN SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `A:num->bool` THEN EXPAND_TAC "As" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `Rt <= &(nproduct A (\p:num. p))` ASSUME_TAC THENL
       [UNDISCH_TAC `~(A SUBSET (P:num->bool) /\
                       DISJOINT A (col_supp(e:num->num)) /\
                      &(nproduct A (\p:num. p)) < Rt)` THEN
        ASM_REWRITE_TAC[REAL_NOT_LT];
        ALL_TAC] THEN
      SUBGOAL_THEN `(G:num->real)(nproduct A (\p. p)) = &0` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
      MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (col_ext m e) As)
                  (\a. col_weight G k a / product (col_supp a)
                         (\p. &p - &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`A1:num->bool`; `A2:num->bool`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `A1 SUBSET (P:num->bool) /\
                    DISJOINT A1 (col_supp(e:num->num)) /\
                    A2 SUBSET P /\ DISJOINT A2 (col_supp e)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `e:num->num`;
                     `A1:num->bool`] COL_EXT_PROPS) THEN
      MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `e:num->num`;
                     `A2:num->bool`] COL_EXT_PROPS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_SIMP_TAC[FINITE_COL_SET];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `A:num->bool` o check (fun th ->
      can (find_term ((=) `As:(num->bool)->bool`)) (concl th) &&
      is_forall (concl th) &&
      not (can (find_term ((=) `col_weight`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `e:num->num`;
                   `A:num->bool`] COL_EXT_PROPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `DISJOINT (col_supp e) (A:num->bool)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[NPRODUCT_UNION; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&(nproduct (col_supp e) (\p:num. p)) * Rt` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 0 < q`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `col_supp e SUBSET (P:num->bool)` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `a:num->num` THEN
  STRIP_TAC THEN REWRITE_TAC[col_weight] THEN MATCH_MP_TAC REAL_LE_DIV THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `col_supp a SUBSET (P:num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(q:num) IN col_supp a` THEN
    UNDISCH_TAC `col_supp a SUBSET (P:num->bool)` THEN SET_TAC[]]);;

let LAMBDA_DISJOINT_LOWER = prove
 (`!P S (h:(num->bool)->real) (u:num->real).
     FINITE P /\ S SUBSET P /\ (!A. A SUBSET P ==> &0 <= h A) /\
     (!p. p IN P ==> &0 <= u p) /\
     (!A p. A SUBSET P /\ p IN A ==> h A <= u p * h (A DELETE p))
     ==> sum {A | A SUBSET P} h - sum S u * sum {A | A SUBSET P} h
         <= sum {A | A SUBSET P /\ DISJOINT A S} h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {A:num->bool | A SUBSET P}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {A | A SUBSET P /\ DISJOINT A S} (h:(num->bool)->real) =
    sum {A | A SUBSET P} (\A. if DISJOINT A S then h A else &0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x - y <= c ==> x - c <= y`) THEN
  ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {A | A SUBSET P}
                  (\A. sum S (\p. if p IN A then (h:(num->bool)->real) A
                                  else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (h:(num->bool)->real) A` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL] THEN MATCH_MP_TAC SUM_POS_LE THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
     NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
    MP_TAC(BETA_RULE(ISPECL [`S:num->bool`;
       `\p. if p IN A then (h:(num->bool)->real) A else &0`; `q:num`]
       ELEMENT_LE_SUM)) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      SIMP_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{A | A IN {A | A SUBSET P} /\ p IN A} =
                {A:num->bool | A SUBSET P /\ p IN A}`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:num) IN P` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSETS_CONTAINING THEN ASM_SIMP_TAC[]);;

let col_of_sets = new_definition
 `col_of_sets (Ix:num->bool) (x:num->num->bool) =
    \p. if ?i. i IN Ix /\ p IN x i then @i. i IN Ix /\ p IN x i else 0`;;

let COL_OF_SETS_PROPS = prove
 (`!k P Ix (x:num->num->bool).
     Ix SUBSET 1..k /\ x IN cartesian_product Ix (\i. {A | A SUBSET P}) /\
     (!i j. i IN Ix /\ j IN Ix /\ ~(i = j) ==> DISJOINT (x i) (x j))
     ==> col_of_sets Ix x IN col_set k P /\
         (!i. i IN Ix ==> col_class (col_of_sets Ix x) i = x i) /\
         (!i. ~(i = 0) /\ ~(i IN Ix) ==> col_class (col_of_sets Ix x) i = {})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM; SUBSET; IN_NUMSEG;
              DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!p i. i IN Ix /\ p IN (x:num->num->bool) i ==> col_of_sets Ix x p = i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[col_of_sets] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    SELECT_ELIM_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. ~(?i. i IN Ix /\ p IN (x:num->num->bool) i) ==> col_of_sets Ix x p = 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[col_of_sets] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. col_of_sets Ix (x:num->num->bool) p = 0 \/
        (col_of_sets Ix x p IN Ix /\ p IN x (col_of_sets Ix x p))`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `?i. i IN Ix /\ p IN (x:num->num->bool) i` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      DISJ2_TAC THEN
      SUBGOAL_THEN `col_of_sets Ix (x:num->num->bool) p = i` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[col_set; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `p:num`) THEN
    ASM_REWRITE_TAC[LE_0] THEN
    SUBGOAL_THEN `p IN P /\ col_of_sets Ix (x:num->num->bool) p <= k`
      (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[col_class; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `p:num`) THENL
       [SUBGOAL_THEN `1 <= i` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_ARITH_TAC;
        ASM_MESON_TAC[]];
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[col_class; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tails of tuple sums.                                                      *)
(* ------------------------------------------------------------------------- *)

let TUPLE_TAIL_MARKOV = prove
 (`!(Ix:A->bool) P (f:(num->bool)->real) L.
     FINITE Ix /\ FINITE P /\ (!p. p IN P ==> 1 <= p) /\
     (!A. A SUBSET P ==> &0 <= f A) /\ &0 < L
     ==> sum {x | x IN cartesian_product Ix (\i. {A | A SUBSET P}) /\
                  L < sum Ix (\i. log(&(nproduct (x i) (\p. p))))}
             (\x. product Ix (\i. f(x i)))
         <= &(CARD Ix) *
            sum {A | A SUBSET P} (\A. f A * log(&(nproduct A (\p. p)))) *
            sum {A | A SUBSET P} f pow (CARD Ix - 1) / L`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Cp = cartesian_product (Ix:A->bool)
                                      (\i. {A:num->bool | A SUBSET P})` THEN
  SUBGOAL_THEN `FINITE(Cp:(A->num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_SIMP_TAC[FINITE_POWERSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!A. A SUBSET P ==> &0 <= log(&(nproduct A (\p:num. p)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= p ==> 0 < p`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN Cp ==> &0 <= product Ix (\i:A. (f:(num->bool)->real)(x i)) /\
                   &0 <= sum Ix (\i. log(&(nproduct (x i) (\p:num. p))))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Cp (\x. product Ix (\i:A. (f:(num->bool)->real)(x i)) *
                         sum Ix (\i. log(&(nproduct (x i) (\p:num. p))))) / L`
  THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {x | x IN Cp /\
                  L < sum Ix (\i:A. log(&(nproduct (x i) (\p:num. p))))}
                  (\x. product Ix (\i. (f:(num->bool)->real)(x i)) *
                       sum Ix (\i. log(&(nproduct (x i) (\p:num. p)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A->num->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ix:A->bool`; `{A:num->bool | A SUBSET P}`;
                 `f:(num->bool)->real`;
                 `\A. log(&(nproduct A (\p:num. p)))`]
         TUPLE_SUM_FIRST_MOMENT) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_LE_REFL]);;

let TUPLE_SIGMA_BOUND = prove
 (`!(Ix:A->bool) P (f:(num->bool)->real) (u:num->real).
     FINITE Ix /\ FINITE P /\ (!A. A SUBSET P ==> &0 <= f A) /\
     (!p. p IN P ==> &0 <= u p) /\
     (!A p. A SUBSET P /\ p IN A ==> f A <= u p * f (A DELETE p))
     ==> sum (cartesian_product Ix (\i. {A | A SUBSET P}))
             (\x. product Ix (\i. f(x i)) * sum Ix (\i. sum (x i) u))
         <= &(CARD Ix) * sum P (\p. u p pow 2) *
            sum {A | A SUBSET P} f pow CARD Ix`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Ix:A->bool`; `{A:num->bool | A SUBSET P}`;
                 `f:(num->bool)->real`; `\A. sum A (u:num->real)`]
         TUPLE_SUM_FIRST_MOMENT) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `Ix:A->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES; REAL_MUL_LZERO; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= CARD(Ix:A->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; CARD_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum {A | A SUBSET P} (f:(num->bool)->real)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {A | A SUBSET P} (f:(num->bool)->real) pow CARD(Ix:A->bool) =
    sum {A | A SUBSET P} f * sum {A | A SUBSET P} f pow (CARD Ix - 1)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [MATCH_MP (ARITH_RULE `1 <= n ==> n = SUC(n - 1)`)
               (ASSUME `1 <= CARD(Ix:A->bool)`)] THEN
    REWRITE_TAC[real_pow];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum P (\p. u p * sum {A | A SUBSET P /\ p IN A}
                                   (f:(num->bool)->real))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SIMP_TAC[GSYM SUM_LMUL; SUM_RMUL] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {A | A SUBSET P} (\A. sum P (\p.
       if p IN A then (f:(num->bool)->real) A * u p else &0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `A:num->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RESTRICT_SET] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
      W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM SUM_LMUL; GSYM CONJ_ASSOC] THEN
      MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SUM_SUBSETS_CONTAINING THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The weights in S2.                                                        *)
(* ------------------------------------------------------------------------- *)

let COL_SUPP_SUM_CLASS = prove
 (`!k P (c:num->num) (u:num->real).
     FINITE P /\ c IN col_set k P
     ==> sum (col_supp c) u = sum (1..k) (\i. sum (col_class c i) u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(col_supp c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:num->num`; `u:num->real`; `col_supp c`; `1..k`]
         SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    ASM_CASES_TAC `(p:num) IN P` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[col_class; col_supp; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_TAC THEN ASM_ARITH_TAC);;

let COL_OF_SETS_QUANTITIES = prove
 (`!k m P (x:num->num->bool).
     FINITE P /\ m IN 1..k /\
     x IN cartesian_product ((1..k) DELETE m) (\i. {A | A SUBSET P}) /\
     (!i j. i IN (1..k) DELETE m /\ j IN (1..k) DELETE m /\ ~(i = j)
            ==> DISJOINT (x i) (x j))
     ==> col_of_sets ((1..k) DELETE m) x IN col_set k P /\
         (!p. ~(col_of_sets ((1..k) DELETE m) x p = m)) /\
         (!u:num->real. product
            (col_supp (col_of_sets ((1..k) DELETE m) x)) u =
                        product ((1..k) DELETE m) (\i. product (x i) u)) /\
         (!u:num->real. sum (col_supp (col_of_sets ((1..k) DELETE m) x)) u =
                        sum ((1..k) DELETE m) (\i. sum (x i) u)) /\
         (!i. i IN (1..k) DELETE m
              ==> col_class (col_of_sets ((1..k) DELETE m) x) i = x i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `P:num->bool`; `(1..k) DELETE m`;
                 `x:num->num->bool`] COL_OF_SETS_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `e = col_of_sets ((1..k) DELETE m) (x:num->num->bool)` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `col_class e m = {}` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG; IN_DELETE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `col_class e m = {}` THEN
    REWRITE_TAC[col_class; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `u:num->real` THEN
    MP_TAC(ISPECL [`k:num`; `P:num->bool`; `e:num->num`; `u:num->real`]
           COL_SUPP_PRODUCT_CLASS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL
             [`\i. product (col_class e i) (u:num->real)`; `1..k`; `m:num`]
           PRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; PRODUCT_CLAUSES; REAL_MUL_LID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[];
    X_GEN_TAC `u:num->real` THEN
    MP_TAC(ISPECL [`k:num`; `P:num->bool`; `e:num->num`; `u:num->real`]
           COL_SUPP_SUM_CLASS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`\i. sum (col_class e i) (u:num->real)`; `1..k`; `m:num`]
           SUM_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; SUM_CLAUSES; REAL_SUB_RZERO] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]]);;

let SQUARE_LOWER_ARITH = prove
 (`!Sp Tt om Le L s Ff.
     &0 <= Sp /\ &0 <= om /\ om * Le <= Tt /\ L - s * L <= Le /\ &0 <= L /\
     &0 <= Le /\ Ff <= Sp * om pow 2 /\ &0 <= Ff
     ==> Ff * L pow 2 * (&1 - &2 * s) <= Sp * Tt pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Sp * Tt pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_CASES_TAC `&1 - &2 * s <= &0` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x * --c ==> x * c <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= L * (&1 - s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `om * (L * (&1 - s)) <= Tt` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(om:real) * Le` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(om * (L * (&1 - s))) pow 2 <= Tt pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Sp:real) * (om * (L * (&1 - s))) pow 2` THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((Sp:real) * om pow 2) * L pow 2 * (&1 - &2 * s)` THEN
    CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `&0 <= s * s` MP_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE]; REAL_ARITH_TAC]);;

let GU_DECREASE = prove
 (`!(G:num->real) P A p n.
     (!r. &0 <= G r) /\ (!r s. 1 <= r /\ r <= s ==> G s <= G r) /\
     FINITE P /\ (!q. q IN P ==> 2 <= q) /\ A SUBSET P /\ p IN A
     ==> G(nproduct A (\q. q)) pow n * product A (\q. inv(&q - &1))
         <= inv(&p - &1) *
            (G(nproduct (A DELETE p) (\q. q)) pow n *
             product (A DELETE p) (\q. inv(&q - &1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(A:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN A ==> &0 <= inv(&q - &1)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `2 <= q` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\q:num. inv(&q - &1)`; `A:num->bool`; `p:num`]
         PRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH `a * b * c = b * a * c:real`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[FINITE_DELETE;
     IN_DELETE]] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`\q:num. q`; `A:num->bool`; `p:num`] NPRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `1 <= p /\ 1 <= nproduct (A DELETE p) (\q:num. q)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM SET_TAC[]; ARITH_TAC];
      REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
      MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_SIMP_TAC[FINITE_DELETE] THEN
      X_GEN_TAC `q:num` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      SUBGOAL_THEN `2 <= q` MP_TAC THENL [ASM SET_TAC[]; ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 1 * n`] THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]);;

let RHO_U2_GE_U = prove
 (`!p. 2 <= p
       ==> inv(&p - &1)
           <= (&p pow 2 - &p - &1) / (&p - &1) * inv(&p - &1) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SPEC_TAC(`&p:real`,`y:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < y - &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(y pow 2 - y - &1) / (y - &1) * inv(y - &1) pow 2 =
    (y pow 2 - y - &1) / (y - &1) pow 3 /\
    inv(y - &1) = (y - &1) pow 2 / (y - &1) pow 3`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < y - &1` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

let TCOL_SQUARE_FACTOR = prove
 (`!k m P (G:num->real) (x:num->num->bool) (e:num->num).
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\
     x IN cartesian_product ((1..k) DELETE m) (\i. {A | A SUBSET P}) /\
     (!u:num->real. product (col_supp e) u =
                    product ((1..k) DELETE m) (\i. product (x i) u)) /\
     (!i. i IN (1..k) DELETE m ==> col_class e i = x i)
     ==> product ((1..k) DELETE m)
           (\i. G(nproduct (x i) (\p. p)) pow 2 *
                product (x i) (\p. inv(&p - &1)))
         <= product (col_supp e) (\p. (&p pow 2 - &p - &1) / (&p - &1)) *
            (product ((1..k) DELETE m)
               (\i. G(nproduct (col_class e i) (\p. p))) *
             product (col_supp e) (\p. inv(&p - &1))) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> &1 <= &p - &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN (1..k) DELETE m ==> FINITE((x:num->num->bool) i) /\
                                         (x i) SUBSET P`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(x:num->num->bool) IN
       cartesian_product ((1..k) DELETE m) (\i. {A:num->bool | A SUBSET P})`
    THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product ((1..k) DELETE m)
     (\i. (G:num->real)(nproduct (x i) (\p. p)) pow 2 *
          product ((x:num->num->bool) i)
            (\p. (&p pow 2 - &p - &1) / (&p - &1) * inv(&p - &1) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN
    SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term ((=) `FINITE:(num->bool)->bool`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!p. p IN (x:num->num->bool) i ==> &1 <= &p - &1`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RHO_U2_GE_U THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  REWRITE_TAC[ASSUME `!u:num->real. product (col_supp e) u =
     product ((1..k) DELETE m) (\i. product ((x:num->num->bool) i) u)`] THEN
  SUBGOAL_THEN
   `product ((1..k) DELETE m)
      (\i. (G:num->real)(nproduct (col_class e i) (\p. p))) =
    product ((1..k) DELETE m) (\i. G(nproduct ((x:num->num->bool) i) (\p. p)))`
  SUBST1_TAC THENL [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `product ((1..k) DELETE m)
     (\i. ((G:num->real)(nproduct (x i) (\p. p)) * G(nproduct (x i) (\p. p))) *
          (product ((x:num->num->bool) i)
             (\p. (&p pow 2 - &p - &1) / (&p - &1)) *
           (product (x i) (\p. inv(&p - &1)) *
            product (x i) (\p. inv(&p - &1)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[PRODUCT_MUL];
    SIMP_TAC[PRODUCT_MUL; FINITE_DELETE; FINITE_NUMSEG] THEN
    CONV_TAC REAL_RING]);;

let S2_TERMWISE = prove
 (`!k m P R Rt (G:num->real) (x:num->num->bool).
     FINITE P /\ (!p. p IN P ==> prime p) /\ m IN 1..k /\
     (!r. &0 <= G r) /\ (!r s. 1 <= r /\ r <= s ==> G s <= G r) /\
     (!r. Rt <= &r ==> G r = &0) /\ &0 < Rt /\
     x IN cartesian_product ((1..k) DELETE m) (\i. {A | A SUBSET P}) /\
     (!i j. i IN (1..k) DELETE m /\ j IN (1..k) DELETE m /\ ~(i = j)
            ==> DISJOINT (x i) (x j)) /\
     product ((1..k) DELETE m) (\i. &(nproduct (x i) (\p. p))) * Rt <= R
     ==> product ((1..k) DELETE m)
           (\i. G(nproduct (x i) (\p. p)) pow 2 *
                product (x i) (\p. inv(&p - &1))) *
         sum {A | A SUBSET P}
             (\A. G(nproduct A (\p. p)) * product A (\p. inv(&p - &1))) pow 2 *
         (&1 - &2 * sum ((1..k) DELETE m)
                        (\i. sum (x i) (\p. inv(&p - &1))))
         <= product (col_supp (col_of_sets ((1..k) DELETE m) x))
                    (\p. (&p pow 2 - &p - &1) / (&p - &1)) *
            sum {a | a IN {c | c IN col_set k P /\
                               &(nproduct (col_supp c) (\p. p)) < R} /\
                     col_strip m a = col_of_sets ((1..k) DELETE m) x}
                (\a. col_weight G k a / product (col_supp a)
                       (\p. &p - &1)) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `x:num->num->bool`]
         COL_OF_SETS_QUANTITIES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `e = col_of_sets ((1..k) DELETE m) (x:num->num->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> 2 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> &1 <= &p - &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `col_supp e SUBSET (P:num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(e:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(col_supp(e:num->num))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SQUARE_LOWER_ARITH THEN
  EXISTS_TAC `product ((1..k) DELETE m)
                (\i. (G:num->real)(nproduct (col_class e i) (\p. p))) *
              product (col_supp e) (\p. inv(&p - &1))` THEN
  EXISTS_TAC `sum {A | A SUBSET P /\ DISJOINT A (col_supp e)}
                (\A. (G:num->real)(nproduct A (\p. p)) *
                     product A (\p. inv(&p - &1)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `2 <= p`)) (concl th))) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SPEC_TAC(`&p:real`,`y:real`) THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POW_2] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&0 <= (y - &2) * y` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC T_LOWER THEN
    EXISTS_TAC `Rt:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!i. i IN (1..k) DELETE m ==> FINITE((x:num->num->bool) i)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(x:num->num->bool) IN
         cartesian_product ((1..k) DELETE m) (\i. {A:num->bool | A SUBSET P})`
      THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[FINITE_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(nproduct (col_supp e) (\p:num. p)) =
      product ((1..k) DELETE m) (\i. &(nproduct (x i) (\p:num. p)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT] THEN MATCH_MP_TAC PRODUCT_EQ THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_NPRODUCT THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `sum ((1..k) DELETE m)
                    (\i. sum ((x:num->num->bool) i) (\p. inv(&p - &1))) =
                  sum (col_supp e) (\p. inv(&p - &1))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LAMBDA_DISJOINT_LOWER THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM SET_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`G:num->real`; `P:num->bool`; `A:num->bool`; `p:num`;
                     `1`] GU_DECREASE) THEN
      ASM_REWRITE_TAC[REAL_POW_1]];
    MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM SET_TAC[];
    MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM SET_TAC[];
    MATCH_MP_TAC TCOL_SQUARE_FACTOR THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `(x:num->num->bool) i SUBSET P` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:num->num->bool) IN
         cartesian_product ((1..k) DELETE m) (\i. {A:num->bool | A SUBSET P})`
      THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM SET_TAC[]]);;

let TUPLE_GOOD_LOWER = prove
 (`!(Ix:A->bool) P (f:(num->bool)->real) (u:num->real) L.
     FINITE Ix /\ FINITE P /\ (!p. p IN P ==> 1 <= p) /\
     (!A. A SUBSET P ==> &0 <= f A) /\ (!p. p IN P ==> &0 <= u p) /\
     (!A p. A SUBSET P /\ p IN A ==> f A <= u p * f (A DELETE p)) /\
     &0 < L
     ==> sum {A | A SUBSET P} f pow CARD Ix -
         &(CARD Ix) pow 2 * sum P (\p. u p pow 2) *
         sum {A | A SUBSET P} f pow CARD Ix -
         &(CARD Ix) *
         sum {A | A SUBSET P} (\A. f A * log(&(nproduct A (\p. p)))) *
         sum {A | A SUBSET P} f pow (CARD Ix - 1) / L
         <= sum {x | x IN cartesian_product Ix (\i. {A | A SUBSET P}) /\
                     (!i j. i IN Ix /\ j IN Ix /\ ~(i = j)
                            ==> DISJOINT (x i) (x j)) /\
                     sum Ix (\i. log(&(nproduct (x i) (\p. p)))) <= L}
                (\x. product Ix (\i. f(x i)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Ix:A->bool`; `{A:num->bool | A SUBSET P}`;
                 `f:(num->bool)->real`] TUPLE_SUM_POWER) THEN
  MP_TAC(ISPECL [`Ix:A->bool`; `P:num->bool`; `f:(num->bool)->real`;
                 `u:num->real`] TUPLE_NONDISJOINT_BOUND) THEN
  MP_TAC(ISPECL [`Ix:A->bool`; `P:num->bool`; `f:(num->bool)->real`;
                 `L:real`] TUPLE_TAIL_MARKOV) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN
  ABBREV_TAC `PS = {A:num->bool | A SUBSET P}` THEN
  ABBREV_TAC `Cp = cartesian_product (Ix:A->bool)
                                     (\i. PS:(num->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE(Cp:(A->num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    EXPAND_TAC "PS" THEN ASM_SIMP_TAC[FINITE_POWERSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN Cp ==> &0 <= product Ix (\i:A. (f:(num->bool)->real)(x i))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Cp"; "PS"] THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Xg = {x | x IN Cp /\
                        (!i j. i IN Ix /\ j IN Ix /\ ~(i = j)
                               ==> DISJOINT (x i) (x j)) /\
                        sum (Ix:A->bool)
                            (\i. log(&(nproduct (x i) (\p. p)))) <= L}` THEN
  ABBREV_TAC `Nd = {x | x IN Cp /\
                        ?i j p. i IN Ix /\ j IN Ix /\ ~(i = j) /\ p IN P /\
                                p IN (x:A->num->bool) i /\ p IN x j}` THEN
  ABBREV_TAC `Tl = {x | x IN Cp /\
                        L < sum (Ix:A->bool)
                                (\i. log(&(nproduct (x i) (\p. p))))}` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(Xg:(A->num->bool)->bool) SUBSET Cp /\ Nd SUBSET Cp /\ Tl SUBSET Cp`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Xg"; "Nd"; "Tl"] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cp DIFF (Xg:(A->num->bool)->bool) SUBSET Nd UNION Tl`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Xg"; "Nd"; "Tl"; "Cp"; "PS"] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM; IN_CARTESIAN_PRODUCT;
                DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum Cp (\x. product Ix (\i:A. (f:(num->bool)->real)(x i))) <=
    sum Xg (\x. product Ix (\i. f(x i))) +
    sum Nd (\x. product Ix (\i. f(x i))) +
    sum Tl (\x. product Ix (\i. f(x i)))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`\x. product Ix (\i:A. (f:(num->bool)->real)(x i))`;
                   `Cp:(A->num->bool)->bool`; `Xg:(A->num->bool)->bool`]
           SUM_DIFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`Nd:(A->num->bool)->bool`; `Tl:(A->num->bool)->bool`;
                   `\x. product Ix (\i:A. (f:(num->bool)->real)(x i))`]
           SUM_INCL_EXCL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&0 <= sum (Nd INTER Tl)
                (\x. product Ix (\i:A. (f:(num->bool)->real)(x i)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_INTER] THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum (Cp DIFF Xg) (\x. product Ix (\i:A. (f:(num->bool)->real)(x i))) <=
      sum (Nd UNION Tl) (\x. product Ix (\i. f(x i)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF; IN_UNION] THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let LOG_SUM_PRODUCT_LE = prove
 (`!(Ix:A->bool) (x:A->num->bool) P R Rt.
     FINITE Ix /\ FINITE P /\ (!p. p IN P ==> 1 <= p) /\
     (!i. i IN Ix ==> x i SUBSET P) /\ &0 < Rt /\ &0 < R /\
     sum Ix (\i. log(&(nproduct (x i) (\p. p)))) <= log(R / Rt)
     ==> product Ix (\i. &(nproduct (x i) (\p. p))) * Rt <= R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN Ix ==> &0 < &(nproduct ((x:A->num->bool) i) (\p. p))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
    SUBGOAL_THEN `FINITE((x:A->num->bool) i)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN
    ASM_MESON_TAC[SUBSET; ARITH_RULE `1 <= p ==> ~(p = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < product Ix (\i. &(nproduct ((x:A->num->bool) i) (\p. p)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN
   `log(product Ix (\i. &(nproduct ((x:A->num->bool) i) (\p. p)))) <=
    log(R / Rt)`
  MP_TAC THENL
   [ASM_SIMP_TAC[LOG_PRODUCT]; ASM_SIMP_TAC[LOG_MONO_LE; REAL_LT_DIV]]);;

let COL_OF_SETS_SUM_LOWER = prove
 (`!k m P R Rt (wf:(num->num)->real) X.
     FINITE P /\ (!p. p IN P ==> 1 <= p) /\ m IN 1..k /\ &1 < Rt /\
     (!e. e IN col_set k P ==> &0 <= wf e) /\
     X SUBSET {x | x IN cartesian_product ((1..k) DELETE m)
                                          (\i. {A | A SUBSET P}) /\
                   (!i j. i IN (1..k) DELETE m /\ j IN (1..k) DELETE m /\
                          ~(i = j) ==> DISJOINT (x i) (x j)) /\
                   product ((1..k) DELETE m)
                           (\i. &(nproduct (x i) (\p. p))) * Rt <= R}
     ==> sum X (\x. wf(col_of_sets ((1..k) DELETE m) x)) <=
         sum (IMAGE (col_strip m)
                    {c | c IN col_set k P /\
                     &(nproduct (col_supp c) (\p. p)) < R})
             wf`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `fam = {c | c IN col_set k P /\
                         &(nproduct (col_supp c) (\p:num. p)) < R}` THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "fam" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_SIMP_TAC[FINITE_COL_SET];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(X:(num->num->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `cartesian_product ((1..k) DELETE m)
                                  (\i. {A:num->bool | A SUBSET P})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
      ASM_SIMP_TAC[FINITE_POWERSET; FINITE_DELETE; FINITE_NUMSEG];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN X
        ==> x IN cartesian_product ((1..k) DELETE m) (\i. {A | A SUBSET P}) /\
            (!i j. i IN (1..k) DELETE m /\ j IN (1..k) DELETE m /\
                   ~(i = j) ==> DISJOINT (x i) (x j)) /\
            product ((1..k) DELETE m)
                    (\i. &(nproduct (x i) (\p. p))) * Rt <= R`
  ASSUME_TAC THENL
   [UNDISCH_TAC `X SUBSET {x | x IN cartesian_product ((1..k) DELETE m)
                                          (\i. {A | A SUBSET P}) /\
                   (!i j. i IN (1..k) DELETE m /\ j IN (1..k) DELETE m /\
                          ~(i = j) ==> DISJOINT (x i) (x j)) /\
                   product ((1..k) DELETE m)
                           (\i. &(nproduct (x i) (\p:num. p))) * Rt <= R}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN X ==> col_of_sets ((1..k) DELETE m) x IN IMAGE (col_strip m) fam`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num->num->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num->num->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `X:(num->num->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `x:num->num->bool`]
           COL_OF_SETS_QUANTITIES) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `e = col_of_sets ((1..k) DELETE m) (x:num->num->bool)` THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `e:num->num` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[col_strip; FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "fam" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!i. i IN (1..k) DELETE m ==> FINITE((x:num->num->bool) i)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(x:num->num->bool) IN
         cartesian_product ((1..k) DELETE m) (\i. {A:num->bool | A SUBSET P})`
      THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[FINITE_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `FINITE(col_supp(e:num->num))` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(e:num->num) IN col_set k P` THEN
      REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(nproduct (col_supp e) (\p:num. p)) =
      product ((1..k) DELETE m) (\i. &(nproduct (x i) (\p:num. p)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT] THEN MATCH_MP_TAC PRODUCT_EQ THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_NPRODUCT THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < product ((1..k) DELETE m) (\i. &(nproduct (x i) (\p:num. p)))`
    MP_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LT THEN
      SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
      ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN
      UNDISCH_TAC `(x:num->num->bool) IN
         cartesian_product ((1..k) DELETE m) (\i. {A:num->bool | A SUBSET P})`
      THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[SUBSET; ARITH_RULE `1 <= p ==> ~(p = 0)`];
      ALL_TAC] THEN
    UNDISCH_TAC `&1 < Rt` THEN
    UNDISCH_TAC `product ((1..k) DELETE m)
                   (\i. &(nproduct ((x:num->num->bool) i) (\p. p))) * Rt <= R`
    THEN
    SPEC_TAC(`product ((1..k) DELETE m)
                (\i. &(nproduct ((x:num->num->bool) i) (\p. p)))`,
             `z:real`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `z * &1 < z * Rt` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN X /\ y IN X /\
          col_of_sets ((1..k) DELETE m) x =
          col_of_sets ((1..k) DELETE m) y ==> x = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:num->num->bool`; `y:num->num->bool`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `!z. z IN X ==> !i. i IN (1..k) DELETE m
                         ==> col_class (col_of_sets ((1..k) DELETE m) z) i =
                             (z:num->num->bool) i`
    ASSUME_TAC THENL
     [X_GEN_TAC `z:num->num->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `z:num->num->bool`]
             COL_OF_SETS_QUANTITIES) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CARTESIAN_PRODUCT_EQ_MEMBERS THEN
    MAP_EVERY EXISTS_TAC [`(1..k) DELETE m`;
                          `\i:num. {A:num->bool | A SUBSET P}`] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (IMAGE (col_of_sets ((1..k) DELETE m)) X) (wf:(num->num)->real)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(ISPECL [`col_of_sets ((1..k) DELETE m)`; `wf:(num->num)->real`;
                   `X:(num->num->bool)->bool`] SUM_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `a:num->num`]
         COL_STRIP_SET) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(a:num->num) IN fam` THEN EXPAND_TAC "fam" THEN
  SIMP_TAC[IN_ELIM_THM]);;

let S2_WEIGHT_LOWER = prove
 (`!k m P R Rt (G:num->real).
     FINITE P /\ (!p. p IN P ==> prime p) /\ m IN 1..k /\
     (!r. &0 <= G r) /\ (!r s. 1 <= r /\ r <= s ==> G s <= G r) /\
     (!r. Rt <= &r ==> G r = &0) /\ &1 < Rt /\ Rt < R
     ==> sum {A | A SUBSET P}
             (\A. G(nproduct A (\p. p)) * product A (\p. inv(&p - &1))) pow 2 *
         (sum {A | A SUBSET P}
              (\A. G(nproduct A (\p. p)) pow 2 * product A (\p. inv(&p - &1)))
          pow (k - 1) *
          (&1 - (&k - &1) pow 2 * sum P (\p. inv(&p - &1) pow 2) -
           &2 * (&k - &1) * sum P (\p. inv(&p - &1) pow 2)) -
          (&k - &1) *
          sum {A | A SUBSET P}
              (\A. (G(nproduct A (\p. p)) pow 2 *
                    product A (\p. inv(&p - &1))) *
                   log(&(nproduct A (\p. p)))) *
          sum {A | A SUBSET P}
              (\A. G(nproduct A (\p. p)) pow 2 * product A (\p. inv(&p - &1)))
          pow (k - 2) / log(R / Rt))
         <= sum (IMAGE (col_strip m)
                       {c | c IN col_set k P /\
                            &(nproduct (col_supp c) (\p. p)) < R})
                (\e. product (col_supp e)
                       (\p. (&p pow 2 - &p - &1) / (&p - &1)) *
                     sum {a | a IN {c | c IN col_set k P /\
                                        &(nproduct (col_supp c)
                                            (\p. p)) < R} /\
                              col_strip m a = e}
                         (\a. col_weight G k a / product (col_supp a)
                                (\p. &p - &1))
                     pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> 2 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> &0 <= inv(&p - &1)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Rt /\ &0 < R /\ &0 < log(R / Rt)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < Rt /\ &0 < R` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS_LT THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0) /\ 1 <= k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD((1..k) DELETE m) = k - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE; FINITE_NUMSEG; CARD_NUMSEG_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!A p. A SUBSET P /\ p IN A
          ==> (G:num->real)(nproduct A (\p. p)) pow 2 *
              product A (\p. inv(&p - &1)) <=
              inv(&p - &1) *
              (G(nproduct (A DELETE p) (\p. p)) pow 2 *
               product (A DELETE p) (\p. inv(&p - &1)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GU_DECREASE THEN
    EXISTS_TAC `P:num->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. A SUBSET P ==> &0 <= (G:num->real)(nproduct A (\p. p)) pow 2 *
                              product A (\p. inv(&p - &1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `X2 = {x | x IN cartesian_product ((1..k) DELETE m)
                                     (\i. {A:num->bool | A SUBSET P}) /\
              (!i j. i IN (1..k) DELETE m /\ j IN (1..k) DELETE m /\
                     ~(i = j) ==> DISJOINT (x i) (x j)) /\
              sum ((1..k) DELETE m)
                  (\i. log(&(nproduct (x i) (\p:num. p)))) <=
              log(R / Rt)}` THEN
  SUBGOAL_THEN
   `X2 SUBSET cartesian_product ((1..k) DELETE m)
                                (\i. {A:num->bool | A SUBSET P})`
  ASSUME_TAC THENL
   [EXPAND_TAC "X2" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(cartesian_product ((1..k) DELETE m)
                             (\i. {A:num->bool | A SUBSET P}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_SIMP_TAC[FINITE_POWERSET; FINITE_DELETE; FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(X2:(num->num->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN X2
        ==> x IN cartesian_product ((1..k) DELETE m)
                                   (\i. {A:num->bool | A SUBSET P}) /\
            (!i j. i IN (1..k) DELETE m /\ j IN (1..k) DELETE m /\
                   ~(i = j) ==> DISJOINT (x i) (x j)) /\
            product ((1..k) DELETE m)
                    (\i. &(nproduct (x i) (\p:num. p))) * Rt <= R`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num->num->bool` THEN EXPAND_TAC "X2" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOG_SUM_PRODUCT_LE THEN EXISTS_TAC `P:num->bool` THEN
    ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG;
                 ARITH_RULE `2 <= p ==> 1 <= p`] THEN
    UNDISCH_TAC `(x:num->num->bool) IN
       cartesian_product ((1..k) DELETE m) (\i. {A:num->bool | A SUBSET P})`
    THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum X2 (\x. product (col_supp (col_of_sets ((1..k) DELETE m) x))
                  (\p. (&p pow 2 - &p - &1) / (&p - &1)) *
                sum {a | a IN {c | c IN col_set k P /\
                                   &(nproduct (col_supp c) (\p. p)) < R} /\
                         col_strip m a = col_of_sets ((1..k) DELETE m) x}
                    (\a. col_weight (G:num->real) k a /
                         product (col_supp a) (\p. &p - &1)) pow 2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL
     [`k:num`; `m:num`; `P:num->bool`; `R:real`; `Rt:real`;
      `\e. product (col_supp e) (\p. (&p pow 2 - &p - &1) / (&p - &1)) *
           sum {a | a IN {c | c IN col_set k P /\
                              &(nproduct (col_supp c) (\p. p)) < R} /\
                    col_strip m a = e}
               (\a. col_weight (G:num->real) k a /
                    product (col_supp a) (\p. &p - &1)) pow 2`;
      `X2:(num->num->bool)->bool`] COL_OF_SETS_SUM_LOWER) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `2 <= p ==> 1 <= p`] THEN CONJ_TAC THENL
       [X_GEN_TAC `e:num->num` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        SUBGOAL_THEN `col_supp e SUBSET (P:num->bool)` ASSUME_TAC THENL
         [UNDISCH_TAC `(e:num->num) IN col_set k P` THEN
          REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC PRODUCT_POS_LE THEN
        CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
        SPEC_TAC(`&p:real`,`y:real`) THEN GEN_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POW_2] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `&0 <= (y - &2) * y` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC];
          ASM_REAL_ARITH_TAC];
        GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_SIMP_TAC[]];
      DISCH_THEN MATCH_ACCEPT_TAC]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum X2 (\x. product ((1..k) DELETE m)
                  (\i. (G:num->real)(nproduct (x i) (\p. p)) pow 2 *
                       product (x i) (\p. inv(&p - &1))) *
                sum {A | A SUBSET P}
                    (\A. G(nproduct A (\p. p)) *
                         product A (\p. inv(&p - &1))) pow 2 *
                (&1 - &2 * sum ((1..k) DELETE m)
                               (\i. sum (x i) (\p. inv(&p - &1)))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:num->num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC S2_TERMWISE THEN EXISTS_TAC `Rt:real` THEN
    ASM_SIMP_TAC[]] THEN
  REWRITE_TAC[REAL_ARITH `!a l s:real. a * l * (&1 - &2 * s) =
                                       l * a - &2 * l * (a * s)`] THEN
  SIMP_TAC[SUM_SUB; SUM_LMUL; ASSUME `FINITE(X2:(num->num->bool)->bool)`] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`(1..k) DELETE m`; `P:num->bool`;
     `\A. (G:num->real)(nproduct A (\p. p)) pow 2 *
          product A (\p. inv(&p - &1))`;
     `\p:num. inv(&p - &1)`; `log(R / Rt)`] TUPLE_GOOD_LOWER)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG;
                 ARITH_RULE `2 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`(1..k) DELETE m`; `P:num->bool`;
     `\A. (G:num->real)(nproduct A (\p. p)) pow 2 *
          product A (\p. inv(&p - &1))`;
     `\p:num. inv(&p - &1)`] TUPLE_SIGMA_BOUND)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum X2 (\x. product ((1..k) DELETE m)
                  (\i. (G:num->real)(nproduct (x i) (\p. p)) pow 2 *
                       product (x i) (\p. inv(&p - &1))) *
                sum ((1..k) DELETE m) (\i. sum (x i) (\p. inv(&p - &1)))) <=
    sum (cartesian_product ((1..k) DELETE m)
                           (\i. {A:num->bool | A SUBSET P}))
        (\x. product ((1..k) DELETE m)
               (\i. G(nproduct (x i) (\p. p)) pow 2 *
                    product (x i) (\p. inv(&p - &1))) *
             sum ((1..k) DELETE m) (\i. sum (x i) (\p. inv(&p - &1))))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:num->num->bool` THEN REWRITE_TAC[IN_DIFF] THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG];
      MATCH_MP_TAC SUM_POS_LE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(k - 1) = &k - &1 /\ k - 1 - 1 = k - 2` (CONJUNCTS_THEN
    SUBST1_TAC) THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `PS = {A:num->bool | A SUBSET P}` THEN
  ABBREV_TAC `La = sum PS (\A. (G:num->real)(nproduct A (\p. p)) *
                               product A (\p. inv(&p - &1)))` THEN
  ABBREV_TAC `Ga = sum PS (\A. (G:num->real)(nproduct A (\p. p)) pow 2 *
                               product A (\p. inv(&p - &1)))` THEN
  ABBREV_TAC `M1 = sum PS (\A. ((G:num->real)(nproduct A (\p. p)) pow 2 *
                                product A (\p. inv(&p - &1))) *
                               log(&(nproduct A (\p. p))))` THEN
  ABBREV_TAC `eta = sum P (\p. inv(&p - &1) pow 2)` THEN
  ABBREV_TAC `SX = sum X2 (\x. product ((1..k) DELETE m)
                    (\i. (G:num->real)(nproduct (x i) (\p. p)) pow 2 *
                         product (x i) (\p. inv(&p - &1))))` THEN
  ABBREV_TAC `SXs = sum X2 (\x. product ((1..k) DELETE m)
                    (\i. (G:num->real)(nproduct (x i) (\p. p)) pow 2 *
                         product (x i) (\p. inv(&p - &1))) *
                    sum ((1..k) DELETE m) (\i. sum (x i) (\p. inv(&p - &1))))`
  THEN
  ABBREV_TAC `SC = sum (cartesian_product ((1..k) DELETE m) (\i. PS))
                   (\x. product ((1..k) DELETE m)
                    (\i. (G:num->real)(nproduct (x i) (\p. p)) pow 2 *
                         product (x i) (\p. inv(&p - &1))) *
                    sum ((1..k) DELETE m) (\i. sum (x i) (\p. inv(&p - &1))))`
  THEN
  ABBREV_TAC `L = log(R / Rt)` THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x * a <= x * (b - &2 * c)
                           ==> x * a <= x * b - &2 * x * c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_REAL_ARITH_TAC);;
