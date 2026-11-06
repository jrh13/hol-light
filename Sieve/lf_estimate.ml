(* ========================================================================= *)
(* Linear forms in many variables, part 3: the linear forms estimate.        *)
(*                                                                           *)
(* selberg_lamsum D P n = sum_{A SUBSET P, prod A | n} lambda_A (Selberg's   *)
(* sieve sum) and the majorant is gtnu W b D P n = Y selberg_lamsum(W n +    *)
(* b)^2.                                                                     *)
(* * LF_BOX_EXPAND, LF_BOX_COUNT_CRT: the box sum of prod_j                  *)
(*   selberg_lamsum(psi_j(x))^2 is a double sum over tuples T1, T2 of        *)
(*   congruence counts, each given by LF_BOX_APPROX with modulus prod of the *)
(*   union of the T1 j, T2 j (at most R^(2 m) when prod A <= R on D).        *)
(* * LF_BOX_ESTIMATE: for affine forms nondegenerate mod every p IN P        *)
(*   (primes >= 3), m = |Js|,                                                *)
(*     |sum_box prod_j selberg_lamsum(psi_j(x))^2 - |box| Y^-m|              *)
(*       <= |box| Y^-m (prod_P (1 + 19^m / p^2) - 1)                         *)
(*          + R^(2 m) (prod_i (M i + R^(2 m)) - prod_i (M i)).               *)
(* * Z_N: TRANSLATE_AVERAGE averages over the translates x + [0, M)^t.  If   *)
(*   every psi_j(x) mod N is at distance >= t K M from 0 mod N the           *)
(*   translate meets one affine form per j (PER_X_GOOD); otherwise gtnu is   *)
(*   at most a sum of three such terms (PER_X_UPPER); the bad x are          *)
(*   counted by the fibres of a form mod a prime N (FIBER_COUNT,             *)
(*   BAD_FORM_COUNT).                                                        *)
(* * LF_ZN_BOUND: for affine forms psi_j and a residue b_j per form, with    *)
(*   E = lf_err t M P D R m,                                                 *)
(*     M^t |sum_{Z_N^t} prod_j gtnu W b_j D P (psi_j(x) mod N) - N^t|        *)
(*       <= N^t E + 2 m t K M N^(t - 1) (3^m (M^t + E) + M^t).               *)
(* ========================================================================= *)

needs "Sieve/lf_selberg.ml";;
needs "Sieve/pairs_sieve.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Counting congruences in boxes.                                            *)
(* ------------------------------------------------------------------------- *)

let LF_FORM_MOD_GEN = prove
 (`!k (b:num->int) b0 x d Dm.
        FINITE k /\ ~(Dm = 0) /\ d divides Dm
        ==> ((&d:int) divides lf_form k b b0 x <=>
             (&d:int) divides lf_form k b b0 (\i. x i MOD Dm))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `lf_form k (b:num->int) b0 x - lf_form k b b0 (\i. x i MOD Dm) =
    &Dm * isum k (\i. b i * &(x i DIV Dm))`
  MP_TAC THENL
   [REWRITE_TAC[lf_form; INT_ARITH `(a + c) - (b + c):int = a - b`] THEN
    ASM_SIMP_TAC[GSYM LF_ISUM_SUB; GSYM LF_ISUM_LMUL] THEN
    MATCH_MP_TAC LF_ISUM_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`(x:num->num) i`; `Dm:num`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o
                                          RAND_CONV) [CONJUNCT1 th]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(d:num) divides Dm` THEN REWRITE_TAC[num_divides] THEN
  CONV_TAC INTEGER_RULE);;

let CARD_INTERVAL_FROM = prove
 (`!a M. CARD {x | a <= x /\ x < a + M} = M`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x | (a:num) <= x /\ x < a + M} =
                IMAGE (\i. a + i) {i:num | i < M}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `x - a:num` THEN ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC);;

let CARD_LF_BOX = prove
 (`!t a M. &(CARD(lf_box t a M)) = product {i | i < t} (\i. &(M i))`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CARD_EQ_SUM; FINITE_LF_BOX] THEN REWRITE_TAC[lf_box] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_CARTESIAN_CARD o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x:num | x < a(i:num) + M i}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CARD_INTERVAL_FROM]]);;

let NPRODUCT_SUBSET_DIVIDES = prove
 (`!s t. FINITE t /\ s SUBSET t
         ==> nproduct s (\p:num. p) divides nproduct t (\p. p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = s UNION (t DIFF s):num->bool` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:num->bool) /\ FINITE(t DIFF s:num->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF]; ALL_TAC] THEN
  ASM_SIMP_TAC[NPRODUCT_UNION;
               SET_RULE `DISJOINT (s:num->bool) (t DIFF s)`] THEN
  MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]);;

let LF_NCOUNT_LE_POW = prove
 (`!k p B B0 J. FINITE k ==> lf_ncount k p B B0 J <= &p pow CARD k`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lf_ncount k p B B0 {}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LF_NCOUNT_MONO THEN ASM_REWRITE_TAC[EMPTY_SUBSET];
    ASM_SIMP_TAC[LF_NCOUNT_EMPTY; REAL_LE_REFL]]);;
let PRODUCT_POW_FINITE = prove
 (`!(f:A->real) n s.
        FINITE s ==> product s (\x. f x pow n) = product s f pow n`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_POW_ONE; REAL_POW_MUL]);;

let LF_BOX_COUNT_CRT = prove
 (`!t a M U (B:num->num->int) B0 (Dt:num->num->bool) Js.
     FINITE U /\ (!p. p IN U ==> prime p) /\ (!j. j IN Js ==> Dt j SUBSET U)
     ==> abs(sum (lf_box t a M)
                 (\x. if !j. j IN Js
                             ==> (&(nproduct (Dt j) (\p. p)):int) divides
                                 lf_form {i | i < t} (B j) (B0 j) x
                      then &1 else &0) -
             product {i | i < t} (\i. &(M i)) *
             product U (\p. lf_ncount {i | i < t} p B B0
                              {j | j IN Js /\ p IN Dt j} / &p pow t))
         <= product {i | i < t} (\i. &(M i) + &(nproduct U (\p. p))) -
            product {i | i < t} (\i. &(M i))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Dm = nproduct U (\p:num. p)` THEN
  SUBGOAL_THEN `~(Dm = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "Dm" THEN ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN
    ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Dm` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `g = \x. if !j. j IN Js
                   ==> (&(nproduct ((Dt:num->num->bool) j) (\p. p)):int)
                       divides lf_form {i | i < t} ((B:num->num->int) j)
                                     ((B0:num->int) j) x
            then &1 else &0` THEN
  MP_TAC(ISPECL [`t:num`; `a:num->num`; `M:num->num`; `Dm:num`;
                 `g:(num->num)->real`] LF_BOX_APPROX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(MESON[] `(!j:num. P j ==> (Q j <=> R j))
                          ==> ((!j. P j ==> Q j) <=> (!j. P j ==> R j))`) THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{i:num | i < t}`; `(B:num->num->int) j`;
                   `(B0:num->int) j`; `x:num->num`;
                   `nproduct ((Dt:num->num->bool) j) (\p. p)`; `Dm:num`]
                  LF_FORM_MOD_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN EXPAND_TAC "Dm" THEN
      MATCH_MP_TAC NPRODUCT_SUBSET_DIVIDES THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC LF_FORM_EQ THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (cartesian_product {i:num | i < t} (\i. {r:num | r < Dm})) g =
    product U (\p. lf_ncount {i:num | i < t} p (B:num->num->int) B0
                          {j | j IN Js /\ p IN (Dt:num->num->bool) j})`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN EXPAND_TAC "Dm" THEN MATCH_MP_TAC DENSITY_CRT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (cartesian_product {i:num | i < t} (\i. {r:num | r < Dm}))
     (\z. abs(g z)) =
    sum (cartesian_product {i:num | i < t} (\i. {r:num | r < Dm})) g`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `z:num->num` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
    `Nc = product U (\p. lf_ncount {i:num | i < t} p (B:num->num->int) B0
                          {j | j IN Js /\ p IN (Dt:num->num->bool) j})` THEN
  SUBGOAL_THEN `product U (\p. lf_ncount {i:num | i < t} p (B:num->num->int) B0
                          {j | j IN Js /\ p IN (Dt:num->num->bool) j} /
                            &p pow t) =
                Nc / &Dm pow t` SUBST1_TAC THENL
   [EXPAND_TAC "Nc" THEN ASM_SIMP_TAC[PRODUCT_DIV; PRODUCT_POW_FINITE] THEN
    EXPAND_TAC "Dm" THEN ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `product {i:num | i < t} (\i. &(M i) / &Dm) =
                product {i:num | i < t} (\i. &(M i)) / &Dm pow t /\
                product {i:num | i < t} (\i. &(M i) / &Dm + &1) * &Dm pow t =
                product {i:num | i < t} (\i. &(M i) + &Dm)`
  (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THENL
   [SIMP_TAC[PRODUCT_DIV; FINITE_NUMSEG_LT; PRODUCT_CONST; CARD_NUMSEG_LT] THEN
    MP_TAC(ISPECL [`\i:num. &(M i) / &Dm + &1`; `\i:num. &Dm`;
                   `{i:num | i < t}`] PRODUCT_MUL) THEN
    SIMP_TAC[FINITE_NUMSEG_LT; PRODUCT_CONST; CARD_NUMSEG_LT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC PRODUCT_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < &Dm` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `Nc <= &Dm pow t` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `product U (\p. lf_ncount {i | i < t} p (B:num->num->int) B0
                       {j | j IN Js /\ p IN (Dt:num->num->bool) j}) <=
      product U (\p. &p pow t)` MP_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[LF_NCOUNT_POS] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`{i:num | i < t}`; `x:num`; `B:num->num->int`;
                     `B0:num->int`;
                     `{j | j IN Js /\ x IN (Dt:num->num->bool) j}`]
                    LF_NCOUNT_LE_POW) THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Dm" THEN
      ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; PRODUCT_POW_FINITE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `product {i:num | i < t} (\i. &(M i)) / &Dm pow t <=
                product {i:num | i < t} (\i. &(M i) / &Dm + &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product {i:num | i < t} (\i. &(M i) / &Dm)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SIMP_TAC[PRODUCT_DIV; FINITE_NUMSEG_LT; PRODUCT_CONST; CARD_NUMSEG_LT];
      MATCH_MP_TAC PRODUCT_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      X_GEN_TAC `x:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= &(M(x:num)) / &Dm` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Nc` ASSUME_TAC THENL
   [EXPAND_TAC "Nc" THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_REWRITE_TAC[LF_NCOUNT_POS];
    ALL_TAC] THEN
  ABBREV_TAC `PM = product {i:num | i < t} (\i. &(M i))` THEN
  ABBREV_TAC `PM1 = product {i:num | i < t} (\i. &(M i) / &Dm + &1)` THEN
  ABBREV_TAC `PMD = product {i:num | i < t} (\i. &(M i) + &Dm)` THEN
  ABBREV_TAC `Sg = sum (lf_box t a M) (g:(num->num)->real)` THEN
  SUBGOAL_THEN `&0 < &Dm pow t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `PM / &Dm pow t * Nc = PM * Nc / &Dm pow t` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(PM1 - PM / &Dm pow t) * Nc` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(PM1 - PM / &Dm pow t) * &Dm pow t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_SUB_RDISTRIB] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Expanding the squared sieve sums.                                         *)
(* ------------------------------------------------------------------------- *)

let selberg_lamsum = new_definition
 `selberg_lamsum D P (n:int) =
    sum {A | A SUBSET P}
        (\A. if (&(nproduct A (\p. p)):int) divides n
             then selberg_weight (\p:num. inv(&p)) D A else &0)`;;

let SELBERG_LAMSUM_SQ = prove
 (`!D P n. FINITE P /\ (!p. p IN P ==> prime p)
           ==> selberg_lamsum D P n pow 2 =
               sum {A | A SUBSET P}
                 (\A. sum {A' | A' SUBSET P}
                   (\A'. selberg_weight (\p:num. inv(&p)) D A *
                         selberg_weight (\p:num. inv(&p)) D A' *
                         (if (&(nproduct (A UNION A') (\p. p)):int) divides n
                          then &1 else &0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_lamsum; REAL_POW_2] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `A:num->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `A':num->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((&(nproduct (A UNION A') (\p. p)):int) divides n) <=>
    ((&(nproduct A (\p. p)):int) divides n) /\
    ((&(nproduct A' (\p:num. p)):int) divides n)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `FINITE(A:num->bool) /\ FINITE(A':num->bool) /\
                  (!p. p IN A ==> prime p) /\ (!p. p IN A' ==> prime p) /\
                  (!p. p IN A UNION A' ==> prime p)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[FINITE_SUBSET; SUBSET];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INT_NPRODUCT_DIVIDES; FINITE_UNION] THEN
    REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(&(nproduct A (\p:num. p)):int) divides n` THEN
  ASM_CASES_TAC `(&(nproduct A' (\p:num. p)):int) divides n` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LF_BOX_EXPAND = prove
 (`!t a M P D Js (B:num->num->int) B0.
     FINITE P /\ (!p. p IN P ==> prime p) /\ FINITE Js
     ==> sum (lf_box t a M)
             (\x. product Js
                    (\j. selberg_lamsum D P
                           (lf_form {i | i < t} (B j) (B0 j) x)
                                  pow 2)) =
         sum (cartesian_product Js (\j. {A | A SUBSET P}))
           (\T1. sum (cartesian_product Js (\j. {A | A SUBSET P}))
             (\T2. product Js (\j. selberg_weight (\p. inv(&p)) D (T1 j) *
                                    selberg_weight (\p. inv(&p)) D (T2 j)) *
                   sum (lf_box t a M)
                       (\x. if !j. j IN Js
                                   ==> (&(nproduct (T1 j UNION T2 j)
                                                   (\p. p)):int) divides
                                       lf_form {i | i < t} (B j) (B0 j) x
                            then &1 else &0)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `lmw = selberg_weight (\p:num. inv(&p)) D` THEN
  ABBREV_TAC `C = cartesian_product Js
    (\j:num. {A:num->bool | A SUBSET P})` THEN
  SUBGOAL_THEN `FINITE(C:(num->num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_SIMP_TAC[FINITE_POWERSET];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (lf_box t a M)
        (\x. sum C (\T1. sum C (\T2.
               product Js (\j. (lmw:(num->bool)->real) (T1 j) * lmw (T2 j)) *
               (if !j. j IN Js
                       ==> (&(nproduct (T1 j UNION T2 j) (\p. p)):int) divides
                           lf_form {i | i < t} ((B:num->num->int) j)
                                 ((B0:num->int) j) x
                then &1 else &0))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[SELBERG_LAMSUM_SQ] THEN
    MP_TAC(ISPECL
     [`Js:num->bool`; `\j:num. {A:num->bool | A SUBSET P}`;
      `\j:num A:num->bool.
         sum {A' | A' SUBSET P}
             (\A'. (lmw:(num->bool)->real) A * lmw A' *
                   (if (&(nproduct (A UNION A') (\p. p)):int) divides
                       lf_form {i | i < t} ((B:num->num->int) j)
                         ((B0:num->int) j) x
                    then &1 else &0))`] PRODUCT_SUM_CARTESIAN) THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `T1:num->num->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`Js:num->bool`; `\j:num. {A:num->bool | A SUBSET P}`;
      `\j:num A':num->bool.
         (lmw:(num->bool)->real) ((T1:num->num->bool) j) * lmw A' *
         (if (&(nproduct (T1 j UNION A') (\p. p)):int) divides
             lf_form {i | i < t} ((B:num->num->int) j) ((B0:num->int) j) x
          then &1 else &0)`] PRODUCT_SUM_CARTESIAN) THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `T2:num->num->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PRODUCT_MUL; GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[PRODUCT_INDICATOR];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_LF_BOX] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `T1:num->num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_LF_BOX] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `T2:num->num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[SUM_LMUL]);;

(* ------------------------------------------------------------------------- *)
(* The linear forms estimate on boxes.                                       *)
(* ------------------------------------------------------------------------- *)

let NPRODUCT_UNIONS_LE = prove
 (`!(S:A->num->bool) Js.
        FINITE Js /\ (!j. j IN Js ==> FINITE(S j) /\ !p. p IN S j ==> 1 <= p)
        ==> nproduct (UNIONS (IMAGE S Js)) (\p. p) <=
            nproduct Js (\j. nproduct (S j) (\p. p))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; UNIONS_0; NPRODUCT_CLAUSES; LE_REFL] THEN
  REWRITE_TAC[FORALL_IN_INSERT; UNIONS_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `J:A->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES] THEN
  SUBGOAL_THEN `FINITE(UNIONS (IMAGE (S:A->num->bool) J))` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nproduct ((S:A->num->bool) a) (\p. p) *
              nproduct (UNIONS (IMAGE S J)) (\p. p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NPRODUCT_UNION_LE THEN ASM_REWRITE_TAC[IN_UNION] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]]);;

let SELBERG_FAMILY_CARD_LE = prove
 (`!P D R. FINITE P /\ (!p. p IN P ==> prime p) /\ selberg_family P D /\
           (!A. A IN D ==> nproduct A (\p. p) <= R)
           ==> CARD D <= R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(D:(num->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SELBERG_FAMILY_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `!A:num->bool. A IN D ==> FINITE A /\ !p. p IN A ==> prime p`
  ASSUME_TAC THENL
   [UNDISCH_TAC `selberg_family P (D:(num->bool)->bool)` THEN
    REWRITE_TAC[selberg_family; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[FINITE_SUBSET; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\A:num->bool. nproduct A (\p. p)) D)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_PRIMES_INJ THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..R)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
  X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
  MATCH_MP_TAC NPRODUCT_POS_LT THEN
  ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ]);;

let LF_SUPPORT_SUM = prove
 (`!Js P (D:(num->bool)->bool).
        FINITE Js /\ FINITE P /\ selberg_family P D
        ==> sum (cartesian_product Js (\j:num. {A | A SUBSET P}))
                (\T1. if !j. j IN Js ==> T1 j IN D then &1 else &0) =
            &(CARD D) pow CARD Js`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Js:num->bool`; `\j:num. {A:num->bool | A SUBSET P}`;
                 `\j:num A:num->bool. if A IN D then &1 else &0`]
         PRODUCT_SUM_CARTESIAN) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; PRODUCT_INDICATOR] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `sum {A:num->bool | A SUBSET P}
                    (\A. if A IN D then &1 else &0) = &(CARD D)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN `{A:num->bool | A IN {A | A SUBSET P} /\ A IN D} = D`
    SUBST1_TAC THENL
     [UNDISCH_TAC `selberg_family P (D:(num->bool)->bool)` THEN
      REWRITE_TAC[selberg_family] THEN SET_TAC[];
      ASM_MESON_TAC[CARD_EQ_SUM; SELBERG_FAMILY_FINITE]];
    ASM_SIMP_TAC[PRODUCT_CONST]]);;

let LF_WEIGHT_ABS = prove
 (`!P D Js (T1:num->num->bool) T2.
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
        selberg_family P D /\
        (!j. j IN Js ==> T1 j SUBSET P /\ T2 j SUBSET P)
        ==> abs(product Js (\j. selberg_weight (\p. inv(&p)) D (T1 j) *
                                selberg_weight (\p. inv(&p)) D (T2 j)))
            <= (if !j. j IN Js ==> T1 j IN D /\ T2 j IN D then &1 else &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `P:num->bool` INV_PRIME_RANGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_ABS] THEN MATCH_MP_TAC PRODUCT_LE_1 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    CONJ_TAC THEN MATCH_MP_TAC SELBERG_WEIGHT_BOUND THEN
    EXISTS_TAC `P:num->bool` THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> abs x <= &0`) THEN
    ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN
    ASM_MESON_TAC[SELBERG_WEIGHT_SUPPORT]]);;

let LF_PAIR_ERROR = prove
 (`!t a M P D R Js (B:num->num->int) B0 (T1:num->num->bool) T2.
        FINITE P /\ (!p. p IN P ==> prime p) /\ FINITE Js /\
        selberg_family P D /\ (!A. A IN D ==> nproduct A (\p. p) <= R) /\
        (!j. j IN Js ==> T1 j IN D /\ T2 j IN D)
        ==> abs(sum (lf_box t a M)
                    (\x. if !j. j IN Js
                                ==> (&(nproduct (T1 j UNION T2 j) (\p. p)):int)
                                    divides lf_form {i | i < t} (B j) (B0 j) x
                         then &1 else &0) -
                product {i | i < t} (\i. &(M i)) *
                product P (\p. lf_ncount {i | i < t} p B B0
                                 {j | j IN Js /\ p IN T1 j UNION T2 j} /
                               &p pow t))
            <= product {i | i < t} (\i. &(M i) + &R pow (2 * CARD Js)) -
               product {i | i < t} (\i. &(M i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. j IN Js ==> (T1:num->num->bool) j SUBSET P /\
                                T2 j SUBSET P`
  ASSUME_TAC THENL
   [UNDISCH_TAC `selberg_family P (D:(num->bool)->bool)` THEN
    REWRITE_TAC[selberg_family; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> 1 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]; ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS
    (IMAGE (\j. (T1:num->num->bool) j UNION T2 j) Js)` THEN
  SUBGOAL_THEN `(U:num->bool) SUBSET P` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; UNION_SUBSET] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(U:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:num`; `a:num->num`; `M:num->num`; `U:num->bool`;
                 `B:num->num->int`; `B0:num->int`;
                 `\j. (T1:num->num->bool) j UNION T2 j`; `Js:num->bool`]
         LF_BOX_COUNT_CRT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product U (\p. lf_ncount {i | i < t} p B B0
                     {j | j IN Js /\ p IN (T1:num->num->bool) j UNION T2 j} /
                   &p pow t) =
    product P (\p. lf_ncount {i | i < t} p B B0
                     {j | j IN Js /\ p IN T1 j UNION T2 j} /
                   &p pow t)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_SUPERSET THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{j | j IN Js /\ p IN (T1:num->num->bool) j UNION T2 j} = {}`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(p IN (U:num->bool))` THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIONS;
                  IN_IMAGE] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[LF_NCOUNT_EMPTY; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    MATCH_MP_TAC REAL_DIV_REFL THEN
    REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> abs x <= y - m ==> abs x <= z - m`) THEN
  MATCH_MP_TAC PRODUCT_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS];
                  ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_LADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  MP_TAC(ISPECL [`\j. (T1:num->num->bool) j UNION T2 j`; `Js:num->bool`]
         NPRODUCT_UNIONS_LE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_UNION; FINITE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `(y:num) <= z ==> (x:num) <= y ==> x <= z`) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `nproduct Js (\j:num. R * R)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NPRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `nproduct ((T1:num->num->bool) j) (\p. p) *
                nproduct (T2 j) (\p. p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_UNION_LE THEN REWRITE_TAC[IN_UNION] THEN
      ASM_MESON_TAC[FINITE_SUBSET; SUBSET];
      MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[NPRODUCT_CONST; EXP_MULT; EXP_2; LE_REFL]]);;

let LF_ERROR_TERM = prove
 (`!w c m l e. abs w <= &1 /\ abs(c - m * l) <= e
               ==> abs(w * c - m * (w * l)) <= e`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_RING `(w:real) * c - m * (w * l) = w * (c - m * l)`] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let LF_ERROR_ZERO = prove
 (`!w c m l e. abs w <= &0 /\ &0 <= e ==> abs(w * c - m * (w * l)) <= e`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `w = &0` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ABS_0]);;

let LF_ERROR_SUM = prove
 (`!t a M P D R Js (B:num->num->int) B0.
    FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
    selberg_family P D /\ (!A. A IN D ==> nproduct A (\p. p) <= R)
    ==> abs(sum (cartesian_product Js (\j. {A | A SUBSET P}))
             (\T1. sum (cartesian_product Js (\j. {A | A SUBSET P}))
              (\T2. product Js (\j. selberg_weight (\p. inv(&p)) D (T1 j) *
                                    selberg_weight (\p. inv(&p)) D (T2 j)) *
                    sum (lf_box t a M)
                     (\x. if !j. j IN Js
                                 ==> (&(nproduct (T1 j UNION T2 j) (\p. p))
                                      :int) divides
                                     lf_form {i | i < t} (B j) (B0 j) x
                          then &1 else &0))) -
            product {i | i < t} (\i. &(M i)) *
            sum (cartesian_product Js (\j. {A | A SUBSET P}))
             (\T1. sum (cartesian_product Js (\j. {A | A SUBSET P}))
              (\T2. product Js (\j. selberg_weight (\p. inv(&p)) D (T1 j) *
                                    selberg_weight (\p. inv(&p)) D (T2 j)) *
                    product P (\p. lf_ncount {i | i < t} p B B0
                                     {j | j IN Js /\ p IN T1 j UNION T2 j} /
                                   &p pow t))))
        <= &R pow (2 * CARD Js) *
           (product {i | i < t} (\i. &(M i) + &R pow (2 * CARD Js)) -
            product {i | i < t} (\i. &(M i)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `CT = cartesian_product Js
    (\j:num. {A:num->bool | A SUBSET P})` THEN
  SUBGOAL_THEN `FINITE(CT:(num->num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "CT" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_SIMP_TAC[FINITE_POWERSET];
    ALL_TAC] THEN
  ABBREV_TAC `Er = product {i | i < t}
                   (\i. &((M:num->num) i) + &R pow (2 * CARD(Js:num->bool))) -
                 product {i | i < t} (\i. &(M i))` THEN
  SUBGOAL_THEN `&0 <= Er` ASSUME_TAC THENL
   [EXPAND_TAC "Er" THEN REWRITE_TAC[REAL_SUB_LE] THEN
    MATCH_MP_TAC PRODUCT_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; REAL_POS] THEN
    REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
    MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f g c. sum (CT:(num->num->bool)->bool) f - c * sum CT g =
                        sum CT (\x. f x - c * g x)`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[SUM_SUB; SUM_LMUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum CT (\T1:num->num->bool. sum CT (\T2:num->num->bool.
      (if !j. j IN Js ==> T1 j IN D then &1 else &0) *
      (if !j. j IN Js ==> T2 j IN D then &1 else &0) * Er))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_LMUL; SUM_RMUL] THEN
    MP_TAC(SPECL [`Js:num->bool`; `P:num->bool`; `D:(num->bool)->bool`]
           LF_SUPPORT_SUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `n + n = 2 * n`] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC SELBERG_FAMILY_CARD_LE THEN EXISTS_TAC `P:num->bool` THEN
    ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `T1:num->num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `T2:num->num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!j. j IN Js ==> (T1:num->num->bool) j SUBSET P /\
                                T2 j SUBSET P`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(T1:num->num->bool) IN CT` THEN
    UNDISCH_TAC `(T2:num->num->bool) IN CT` THEN EXPAND_TAC "CT" THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:num->bool`; `D:(num->bool)->bool`; `Js:num->bool`;
                `T1:num->num->bool`; `T2:num->num->bool`] LF_WEIGHT_ABS) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `!j. j IN Js ==> (T1:num->num->bool) j IN D /\ T2 j IN D` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(!j. j IN Js ==> (T1:num->num->bool) j IN D) /\
                  (!j. j IN Js ==> (T2:num->num->bool) j IN D)`
    (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC THEN
    MATCH_MP_TAC LF_ERROR_TERM THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Er" THEN MATCH_MP_TAC LF_PAIR_ERROR THEN
    EXISTS_TAC `D:(num->bool)->bool` THEN ASM_SIMP_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC LF_ERROR_ZERO THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_POS]]);;

let LF_COMBINE = prove
 (`!m s1 sg y z e3.
        &0 <= m /\ abs(sg - y) <= z /\ abs(s1 - m * sg) <= e3
        ==> abs(s1 - m * y) <= m * z + e3`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(s1 - m * sg) <= e3 /\ abs(m * sg - m * y) <= m * z
    ==> abs(s1 - m * y) <= m * z + e3`) THEN
  ASM_REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs m = m` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let LF_BOX_ESTIMATE = prove
 (`!t a M P D R Js (B:num->num->int) B0.
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
        selberg_family P D /\ (!A. A IN D ==> nproduct A (\p. p) <= R) /\
        2 <= t /\ (!p. p IN P ==> lf_fam_ok p t Js B)
        ==> abs(sum (lf_box t a M)
                    (\x. product Js
                          (\j. selberg_lamsum D P
                                 (lf_form {i | i < t} (B j) (B0 j) x)
                               pow 2)) -
                product {i | i < t} (\i. &(M i)) *
                inv(sum D (selberg_H (\p. inv(&p)))) pow CARD Js)
            <= product {i | i < t} (\i. &(M i)) *
               inv(sum D (selberg_H (\p. inv(&p)))) pow CARD Js *
               (product P (\p. &1 + &19 pow CARD Js / &p pow 2) - &1) +
               &R pow (2 * CARD Js) *
               (product {i | i < t} (\i. &(M i) + &R pow (2 * CARD Js)) -
                product {i | i < t} (\i. &(M i)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> prime p` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LF_BOX_EXPAND] THEN
  MP_TAC(SPECL [`t:num`; `a:num->num`; `M:num->num`; `P:num->bool`;
                `D:(num->bool)->bool`; `R:num`; `Js:num->bool`;
                `B:num->num->int`; `B0:num->int`] LF_ERROR_SUM) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`t:num`; `P:num->bool`; `D:(num->bool)->bool`;
                `Js:num->bool`; `B:num->num->int`; `B0:num->int`]
         MS_EXPANSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`t:num`; `P:num->bool`; `D:(num->bool)->bool`;
                `Js:num->bool`; `B:num->num->int`; `B0:num->int`]
         MS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= product {i | i < t} (\i. &((M:num->num) i))` MP_TAC
  THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN MATCH_ACCEPT_TAC LF_COMBINE);;

(* ------------------------------------------------------------------------- *)
(* The majorant and the translates in Z_N.                                   *)
(* ------------------------------------------------------------------------- *)

let TRANSLATE_SUM = prove
 (`!t N (y:num->num) (Fz:(num->num)->real).
        ~(N = 0)
        ==> sum (cartesian_product {i | i < t} (\i. {r | r < N}))
                (\x. Fz (\i. if i < t then (x i + y i) MOD N else ARB)) =
            sum (cartesian_product {i | i < t} (\i. {r | r < N})) Fz`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ZN = cartesian_product {i | i < t}
    (\i:num. {r:num | r < N})` THEN
  ABBREV_TAC `tr = \x:num->num. (\i. if i < t then (x i + (y:num->num) i) MOD N
                                    else ARB)` THEN
  SUBGOAL_THEN `(\x. (Fz:(num->num)->real)
                       (\i. if i < t then (x i + y i) MOD N else ARB)) =
                Fz o (tr:(num->num)->(num->num))`
  SUBST1_TAC THENL
   [EXPAND_TAC "tr" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(ZN:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ZN" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:num->num. x IN ZN ==> (tr:(num->num)->(num->num)) x IN ZN`
  ASSUME_TAC THENL
   [EXPAND_TAC "ZN" THEN EXPAND_TAC "tr" THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
    ASM_SIMP_TAC[MOD_LT_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x x':num->num. x IN ZN /\ x' IN ZN /\
                (tr:(num->num)->(num->num)) x = tr x' ==> x = x'`
  ASSUME_TAC THENL
   [EXPAND_TAC "ZN" THEN EXPAND_TAC "tr" THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
    MAP_EVERY X_GEN_TAC [`x:num->num`; `z:num->num`] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `(i:num) < t` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `N:num` THEN
    ASM_SIMP_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM(SPEC `(y:num->num) i` CONG_ADD_RCANCEL_EQ)] THEN
    REWRITE_TAC[CONG] THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tr:(num->num)->(num->num)`; `Fz:(num->num)->real`;
                 `ZN:(num->num)->bool`] SUM_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[]);;

let TRANSLATE_AVERAGE = prove
 (`!t N M (Fz:(num->num)->real).
        ~(N = 0)
        ==> &M pow t *
            sum (cartesian_product {i | i < t} (\i. {r | r < N})) Fz =
            sum (cartesian_product {i | i < t} (\i. {r | r < N}))
             (\x. sum (cartesian_product {i | i < t} (\i. {r | r < M}))
                   (\y. Fz (\i. if i < t then (x i + y i) MOD N else ARB)))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[TRANSLATE_SUM] THEN
  SIMP_TAC[SUM_CONST; FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG_LT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[CARD_EQ_SUM; FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG_LT] THEN
  SIMP_TAC[SUM_CARTESIAN_ONE; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]);;

let LF_ISUM_CONG = prove
 (`!k (f:A->int) g n.
        FINITE k /\ (!i. i IN k ==> (f i == g i) (mod n))
        ==> (isum k f == isum k g) (mod n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`k:A->bool`,`k:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ISUM_CLAUSES; FORALL_IN_INSERT;
   INTEGER_RULE `(x:int == x) (mod n)`] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == d) (mod n)
    ==> (a + c == b + d) (mod n)`) THEN
  ASM_SIMP_TAC[]);;

let LF_FORM_TRANSLATE_CONG = prove
 (`!t N (c:num->int) c0 x y.
        (lf_form {i | i < t} c c0
               (\i. if i < t then (x i + y i) MOD N else ARB) ==
         lf_form {i | i < t} c c0 x + lf_form {i | i < t} c (&0) y) (mod &N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lf_form; INT_ADD_RID] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!a b d c0 n:int. (a == b + d) (mod n) ==>
     (a + c0 == (b + c0) + d) (mod n)`) THEN
  SIMP_TAC[GSYM LF_ISUM_ADD; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC LF_ISUM_CONG THEN REWRITE_TAC[FINITE_NUMSEG_LT;
   IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_ADD] THEN
  MP_TAC(SPECL [`&((x:num->num) i) + &((y:num->num) i):int`; `&N:int`]
         INT_REM_MOD_SELF) THEN
  CONV_TAC INTEGER_RULE);;

let gtnu = new_definition
 `gtnu W b D P (n:int) =
    sum D (selberg_H (\p:num. inv(&p))) *
    selberg_lamsum D P (&W * n + &b) pow 2`;;

let GTNU_LF_FORM = prove
 (`!W b D P t (c:num->int) a y.
        gtnu W b D P (a + lf_form {i | i < t} c (&0) y) =
        sum D (selberg_H (\p. inv(&p))) *
        selberg_lamsum D P
          (lf_form {i | i < t} (\i. &W * c i) (&W * a + &b) y) pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gtnu] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[lf_form; GSYM INT_MUL_ASSOC] THEN
  SIMP_TAC[LF_ISUM_LMUL; FINITE_NUMSEG_LT] THEN CONV_TAC INT_RING);;

let GTNU_POS = prove
 (`!W b D P n. FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\
             selberg_family P D
             ==> &0 <= gtnu W b D P n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gtnu] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN
  MATCH_MP_TAC SELBERG_G_GE_1 THEN EXISTS_TAC `P:num->bool` THEN
  MP_TAC(SPEC `P:num->bool` INV_PRIME_RANGE) THEN ASM_SIMP_TAC[]);;

let LF_SCALE = prove
 (`!y s m e1 e2. &0 < y /\ abs(s - m * inv y) <= m * inv y * e1 + e2
                 ==> abs(y * s - m) <= m * e1 + y * e2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:real) * s - m = y * (s - m * inv y)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs y = y` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(y:real) * (m * inv y * e1 + e2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < y` THEN
    CONV_TAC REAL_FIELD]);;

let LF_BOX_ZERO = prove
 (`!t M. lf_box t (\i. 0) (\i. M) =
         cartesian_product {i | i < t} (\i. {r | r < M})`,
  REWRITE_TAC[lf_box; LE_0; ADD_CLAUSES]);;

let lf_err = new_definition
 `lf_err t M P D R m =
    &M pow t * (product P (\p. &1 + &19 pow m / &p pow 2) - &1) +
    sum D (selberg_H (\p:num. inv(&p))) pow m * &R pow (2 * m) *
    ((&M + &R pow (2 * m)) pow t - &M pow t)`;;

let LF_NU_BOX = prove
 (`!t M P D R W (b:num->num) Js (c:num->num->int) a.
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
        selberg_family P D /\ (!A. A IN D ==> nproduct A (\p. p) <= R) /\
        2 <= t /\ (!p. p IN P ==> lf_fam_ok p t Js (\j i. &W * c j i))
        ==> abs(sum (cartesian_product {i | i < t} (\i. {r | r < M}))
                    (\y. product Js
                          (\j. gtnu W (b j) D P
                                (a j + lf_form {i | i < t} (c j) (&0) y))) -
                &M pow t)
            <= lf_err t M P D R (CARD Js)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lf_err] THEN
  SUBGOAL_THEN `&1 <= sum D (selberg_H (\p:num. inv(&p)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SELBERG_G_GE_1 THEN EXISTS_TAC `P:num->bool` THEN
    MP_TAC(SPEC `P:num->bool` INV_PRIME_RANGE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GTNU_LF_FORM] THEN ASM_SIMP_TAC[PRODUCT_MUL; PRODUCT_CONST] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC LF_SCALE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`t:num`; `\i:num. 0`; `\i:num. (M:num)`; `P:num->bool`;
                `D:(num->bool)->bool`; `R:num`; `Js:num->bool`;
                `\j i. &W * (c:num->num->int) j i`;
                `\j. &W * (a:num->int) j + &((b:num->num) j)`]
         LF_BOX_ESTIMATE) THEN
  ASM_REWRITE_TAC[LF_BOX_ZERO] THEN
  SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  REWRITE_TAC[REAL_POW_INV]);;

(* ------------------------------------------------------------------------- *)
(* Good and bad translates.                                                  *)
(* ------------------------------------------------------------------------- *)

let LF_ISUM_ABS_LE = prove
 (`!k (f:A->int) b. FINITE k /\ (!i. i IN k ==> abs(f i) <= b)
                    ==> abs(isum k f) <= &(CARD k) * b`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`k:A->bool`,`k:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ISUM_CLAUSES; CARD_CLAUSES; FORALL_IN_INSERT; INT_ABS_NUM;
           INT_MUL_LZERO; INT_LE_REFL] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ADD_RDISTRIB; INT_MUL_LID] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let LF_FORM_BOX_BOUND = prove
 (`!t M K (c:num->int) y.
        y IN cartesian_product {i | i < t} (\i. {r | r < M}) /\
        (!i. i < t ==> abs(c i) <= &K)
        ==> abs(lf_form {i | i < t} c (&0) y) <= &(t * K * M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lf_form; INT_ADD_RID] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `&(CARD {i:num | i < t}) * &(K * M):int` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LF_ISUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[INT_ABS_MUL; INT_ABS_NUM; GSYM INT_OF_NUM_MUL] THEN
    MATCH_MP_TAC INT_LE_MUL2 THEN ASM_SIMP_TAC[INT_ABS_POS; INT_POS] THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN
    UNDISCH_TAC `(y:num->num) IN
                 cartesian_product {i:num | i < t} (\i. {r:num | r < M})` THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[LT_IMP_LE];
    REWRITE_TAC[CARD_NUMSEG_LT; INT_OF_NUM_MUL; INT_LE_REFL; MULT_ASSOC]]);;

let GOOD_REM = prove
 (`!n v N L. &L <= n /\ n + &L < &N /\ abs v <= &L
             ==> (n + v) rem &N = n + v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_EQ_SELF; INT_ABS_NUM] THEN
  ASM_INT_ARITH_TAC);;

let ALL_REM = prove
 (`!n v N. &0 <= n /\ n < &N /\ abs v < &N
           ==> ?l. l < 3 /\ (n + v) rem &N = (n + (&l - &1) * &N) + v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE; INT_ABS_NUM] THEN
  SUBGOAL_THEN `!l. ((n:int) + v == (n + (&l - &1) * &N) + v) (mod &N)`
  ASSUME_TAC THENL [GEN_TAC THEN CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(n:int) + v < &0` THENL
   [EXISTS_TAC `2` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(n:int) + v < &N` THENL
   [EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
    EXISTS_TAC `0` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC]);;

let NU_REM_BOUND = prove
 (`!W b D P n v N.
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\
        selberg_family P D /\ &0 <= n /\ n < &N /\ abs v < &N
        ==> gtnu W b D P ((n + v) rem &N) <=
            sum {l | l < 3} (\l. gtnu W b D P ((n + (&l - &1) * &N) + v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:int`; `v:int`; `N:num`] ALL_REM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`{l:num}`; `{l:num | l < 3}`;
                 `\l:num. gtnu W b D P ((n + (&l - &1) * &N) + v)`]
         SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; FINITE_NUMSEG_LT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[SING_SUBSET; IN_ELIM_THM; GTNU_POS]);;

let PRODUCT_NU_REM_BOUND = prove
 (`!W (b:num->num) D P N Js (n:num->int) (v:num->int).
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\
        selberg_family P D /\ FINITE Js /\
        (!j. j IN Js ==> &0 <= n j /\ n j < &N /\ abs(v j) < &N)
        ==> product Js (\j. gtnu W (b j) D P ((n j + v j) rem &N)) <=
            sum (cartesian_product Js (\j. {l | l < 3}))
                (\lt. product Js
                       (\j. gtnu W (b j) D P
                              ((n j + (&(lt j) - &1) * &N) + v j)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product Js (\j. sum {l | l < 3}
                (\l. gtnu W ((b:num->num) j) D P
                  (((n:num->int) j + (&l - &1) * &N) + v j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[GTNU_POS; NU_REM_BOUND];
    MP_TAC(ISPECL [`Js:num->bool`; `\j:num. {l:num | l < 3}`;
                   `\j l. gtnu W ((b:num->num) j) D P
                             (((n:num->int) j + (&l - &1) * &N) +
                                      v j)`]
           PRODUCT_SUM_CARTESIAN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_LE_REFL]]);;

let PER_X_UPPER = prove
 (`!t M P D R W (b:num->num) N Js (c:num->num->int) (n:num->int).
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
        selberg_family P D /\ (!A. A IN D ==> nproduct A (\p. p) <= R) /\
        2 <= t /\ (!p. p IN P ==> lf_fam_ok p t Js (\j i. &W * c j i)) /\
        (!j. j IN Js ==> &0 <= n j /\ n j < &N) /\
        (!j y. j IN Js /\
               y IN cartesian_product {i | i < t} (\i. {r | r < M})
               ==> abs(lf_form {i | i < t} (c j) (&0) y) < &N)
        ==> sum (cartesian_product {i | i < t} (\i. {r | r < M}))
                (\y. product Js
                      (\j. gtnu W (b j) D P
                             ((n j + lf_form {i | i < t} (c j) (&0) y)
                                       rem &N)))
            <= &3 pow CARD Js * (&M pow t + lf_err t M P D R (CARD Js))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Bx = cartesian_product {i | i < t}
    (\i:num. {r:num | r < M})` THEN
  SUBGOAL_THEN `FINITE(Bx:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Bx" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  ABBREV_TAC `Lt = cartesian_product (Js:num->bool) (\j. {l:num | l < 3})` THEN
  SUBGOAL_THEN `FINITE(Lt:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Lt" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum Bx (\y. sum Lt (\lt. product Js
      (\j. gtnu W ((b:num->num) j) D P
             (((n:num->int) j + (&((lt:num->num) j) - &1) * &N) +
                       lf_form {i | i < t} ((c:num->num->int) j)
                         (&0) y))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:num->num` THEN DISCH_TAC THEN EXPAND_TAC "Lt" THEN
    MATCH_MP_TAC PRODUCT_NU_REM_BOUND THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Lt (\lt:num->num. &M pow t +
                                    lf_err t M P D R
                                      (CARD(Js:num->bool)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `lt:num->num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`t:num`; `M:num`; `P:num->bool`; `D:(num->bool)->bool`;
                  `R:num`; `W:num`; `b:num->num`; `Js:num->bool`;
                  `c:num->num->int`;
                  `\j. (n:num->int) j + (&((lt:num->num) j) - &1) * &N`]
           LF_NU_BOX) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_ACCEPT_TAC(REAL_ARITH `!s m e. abs(s - m) <= e ==> s <= m + e`);
    ASM_SIMP_TAC[SUM_CONST] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CARD_EQ_SUM] THEN EXPAND_TAC "Lt" THEN
    ASM_SIMP_TAC[SUM_CARTESIAN_ONE]]);;

let PER_X_GOOD = prove
 (`!t M P D R W (b:num->num) N L Js (c:num->num->int) (n:num->int).
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
        selberg_family P D /\ (!A. A IN D ==> nproduct A (\p. p) <= R) /\
        2 <= t /\ (!p. p IN P ==> lf_fam_ok p t Js (\j i. &W * c j i)) /\
        (!j. j IN Js ==> &L <= n j /\ n j + &L < &N) /\
        (!j y. j IN Js /\
               y IN cartesian_product {i | i < t} (\i. {r | r < M})
               ==> abs(lf_form {i | i < t} (c j) (&0) y) <= &L)
        ==> abs(sum (cartesian_product {i | i < t} (\i. {r | r < M}))
                    (\y. product Js
                          (\j. gtnu W (b j) D P
                            ((n j + lf_form {i | i < t} (c j) (&0) y)
                                           rem &N))) -
                &M pow t)
            <= lf_err t M P D R (CARD Js)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:num`; `M:num`; `P:num->bool`; `D:(num->bool)->bool`;
                `R:num`; `W:num`; `b:num->num`; `Js:num->bool`;
                `c:num->num->int`; `n:num->int`] LF_NU_BOX) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> abs(y - m) <= e ==> abs(x - m) <= e`) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `y:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC GOOD_REM THEN EXISTS_TAC `L:num` THEN
  ASM_SIMP_TAC[]);;

let FIBER_COUNT = prove
 (`!t N (c:num->int) c0 i0 r.
        prime N /\ i0 < t /\ ~((&N:int) divides c i0) /\ r < N
        ==> sum (cartesian_product {i | i < t} (\i. {r | r < N}))
                (\x. if lf_form {i | i < t} c c0 x rem &N = &r
                     then &1 else &0) =
            &N pow (t - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{i:num | i < t}`; `N:num`; `c:num->int`;
                 `c0 + -- &r:int`;
                 `i0:num`] COUNT_ONE_FORM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; CARD_NUMSEG_LT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(&N:int = &0) /\ &r:int < abs(&N)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_ABS_NUM; INT_OF_NUM_LT] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_REM_UNIQUE; INT_POS] THEN
  REWRITE_TAC[lf_form; INTEGER_RULE
   `!a b c n:int. (a + c == b) (mod n) <=> n divides (a + (c + --b))`]);;

let BAD_RESIDUES_CARD = prove
 (`!N L. CARD {r:num | r < N /\ (r < L \/ N <= r + L)} <= 2 * L`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD({r:num | r < L} UNION IMAGE (\s. N - 1 - s)
    {s | s < L})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN EXISTS_TAC `N - 1 - r` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD{r:num | r < L} +
      CARD(IMAGE (\s. N - 1 - s) {s | s < L})` THEN
    SIMP_TAC[CARD_UNION_LE; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `a = L /\ b <= L ==> a + b <= 2 * L`) THEN
    SIMP_TAC[CARD_NUMSEG_LT] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD{s:num | s < L}` THEN
    SIMP_TAC[CARD_IMAGE_LE; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; LE_REFL]]);;

let BAD_FORM_COUNT = prove
 (`!t N L (c:num->int) c0 i0.
        prime N /\ i0 < t /\ ~((&N:int) divides c i0)
        ==> sum (cartesian_product {i | i < t} (\i. {r | r < N}))
                (\x. if &L <= lf_form {i | i < t} c c0 x rem &N /\
                        lf_form {i | i < t} c c0 x rem &N + &L < &N
                     then &0 else &1)
            <= &2 * &L * &N pow (t - 1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ZN = cartesian_product {i | i < t}
    (\i:num. {r:num | r < N})` THEN
  ABBREV_TAC `BS = {r:num | r < N /\ (r < L \/ N <= r + L)}` THEN
  SUBGOAL_THEN `FINITE(ZN:(num->num)->bool) /\ FINITE(BS:num->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ZN" THEN EXPAND_TAC "BS" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
      REWRITE_TAC[FINITE_NUMSEG_LT];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:num | r < N}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum ZN (\x. sum BS (\r. if lf_form {i | i < t} (c:num->int) c0 x
                                         rem &N = &r then &1 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    COND_CASES_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `v = lf_form {i | i < t} (c:num->int) c0 x rem &N` THEN
    SUBGOAL_THEN `&0 <= (v:int) /\ v < &N` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN CONJ_TAC THENL
       [MATCH_MP_TAC INT_REM_POS; MATCH_MP_TAC INT_LT_REM] THEN
      REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT] THEN
      ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
      ALL_TAC] THEN
    MP_TAC(SPEC `v:int` INT_OF_NUM_OF_INT) THEN ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`num_of_int v`,`r0:num`) THEN GEN_TAC THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPECL [`{r0:num}`; `BS:num->bool`;
                   `\r:num. if (&r0:int) = &r then &1 else &0`]
           SUM_SUBSET_SIMPLE) THEN
    ASM_REWRITE_TAC[SUM_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SING_SUBSET; IN_DIFF] THEN CONJ_TAC THENL
     [EXPAND_TAC "BS" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      UNDISCH_TAC `~(&L <= (&r0:int) /\ (&r0:int) + &L < &N)` THEN
      UNDISCH_TAC `(&r0:int) < &N` THEN
      REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_ADD; INT_OF_NUM_LT] THEN
      ARITH_TAC;
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum BS (\r:num. &N pow (t - 1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    EXPAND_TAC "ZN" THEN MATCH_MP_TAC FIBER_COUNT THEN
    EXISTS_TAC `i0:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(r:num) IN BS` THEN EXPAND_TAC "BS" THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  EXPAND_TAC "BS" THEN REWRITE_TAC[BAD_RESIDUES_CARD]);;

let LF_FORM_TRANSLATE_REM = prove
 (`!t N (c:num->int) c0 x y.
        lf_form {i | i < t} c c0
              (\i. if i < t then (x i + y i) MOD N else ARB) rem &N =
        (lf_form {i | i < t} c c0 x rem &N + lf_form {i | i < t} c (&0) y)
        rem &N`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!a b c r n:int. (a == b + c) (mod n) /\ (r == b) (mod n)
                    ==> (a == r + c) (mod n)`) THEN
  EXISTS_TAC `lf_form {i | i < t} (c:num->int) c0 x` THEN
  REWRITE_TAC[LF_FORM_TRANSLATE_CONG; INT_REM_MOD_SELF]);;

let LF_ERR_POS = prove
 (`!t M P D R m.
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ selberg_family P D
        ==> &0 <= lf_err t M P D R m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lf_err] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `product P (\p:num. &1)` THEN
    CONJ_TAC THENL [REWRITE_TAC[PRODUCT_ONE; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[REAL_POS] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN
    MATCH_MP_TAC SELBERG_G_GE_1 THEN EXISTS_TAC `P:num->bool` THEN
    MP_TAC(SPEC `P:num->bool` INV_PRIME_RANGE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS]);;

let BAD_INDICATOR = prove
 (`!Js (Pj:num->bool).
        FINITE Js
        ==> (if !j. j IN Js ==> Pj j then &0 else &1) <=
            sum Js (\j. if Pj j then &0 else &1)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  REWRITE_TAC[NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`{j:num}`; `Js:num->bool`;
                 `\j:num. if Pj j then &0 else &1`] SUM_SUBSET_SIMPLE) THEN
  ASM_REWRITE_TAC[SUM_SING; SING_SUBSET; IN_DIFF] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let PER_X_BOUND = prove
 (`!t M P D R W (b:num->num) N K Js (c:num->num->int) (c0:num->int) x.
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
        selberg_family P D /\ (!A. A IN D ==> nproduct A (\p. p) <= R) /\
        2 <= t /\ (!p. p IN P ==> lf_fam_ok p t Js (\j i. &W * c j i)) /\
        t * K * M < N /\ (!j i. j IN Js /\ i < t ==> abs(c j i) <= &K)
        ==> abs(sum (cartesian_product {i | i < t} (\i. {r | r < M}))
                    (\y. product Js
                          (\j. gtnu W (b j) D P
                                (lf_form {i | i < t} (c j) (c0 j)
                                   (\i. if i < t then (x i + y i) MOD N
                                        else ARB) rem &N))) -
                &M pow t)
            <= lf_err t M P D R (CARD Js) +
               (if !j. j IN Js
                       ==> &(t * K * M) <=
                           lf_form {i | i < t} (c j) (c0 j) x rem &N /\
                           lf_form {i | i < t} (c j) (c0 j) x rem &N +
                           &(t * K * M) < &N
                then &0 else &1) *
               (&3 pow CARD Js * (&M pow t + lf_err t M P D R (CARD Js)) +
                &M pow t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LF_FORM_TRANSLATE_REM] THEN
  SUBGOAL_THEN
   `!j y. j IN Js /\ y IN cartesian_product {i | i < t} (\i. {r | r < M})
          ==> abs(lf_form {i | i < t} ((c:num->num->int) j) (&0) y) <=
              &(t * K * M)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LF_FORM_BOX_BOUND THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lf_err t M P D R (CARD(Js:num->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC LF_ERR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    MP_TAC(SPECL [`t:num`; `M:num`; `P:num->bool`; `D:(num->bool)->bool`;
                  `R:num`; `W:num`; `b:num->num`; `N:num`;
                  `(t:num) * (K:num) * (M:num)`;
                  `Js:num->bool`;
                  `c:num->num->int`;
                  `\j. lf_form {i | i < t} ((c:num->num->int) j)
                           ((c0:num->int) j) x rem &N`]
           PER_X_GOOD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  MP_TAC(SPECL [`t:num`; `M:num`; `P:num->bool`; `D:(num->bool)->bool`;
                `R:num`; `W:num`; `b:num->num`; `N:num`; `Js:num->bool`;
                `c:num->num->int`;
                `\j. lf_form {i | i < t} ((c:num->num->int) j)
                         ((c0:num->int) j) x rem &N`]
         PER_X_UPPER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(&N:int = &0) /\ &0:int < &N` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
        ASM_SIMP_TAC[INT_REM_POS; INT_LT_REM]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_LET_TRANS THEN
      EXISTS_TAC `&(t * K * M):int` THEN ASM_SIMP_TAC[INT_OF_NUM_LT]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!g u m e. &0 <= g /\ &0 <= m /\ &0 <= e
              ==> g <= u ==> abs(g - m) <= e + (u + m)`) THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC SUM_POS_LE THEN
  SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG_LT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
  ASM_SIMP_TAC[GTNU_POS]);;

(* ------------------------------------------------------------------------- *)
(* The linear forms bound on Z_N.                                            *)
(* ------------------------------------------------------------------------- *)

let LF_ZN_BOUND = prove
 (`!t M P D R W (b:num->num) N K Js (c:num->num->int) (c0:num->int).
        FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
        selberg_family P D /\ (!A. A IN D ==> nproduct A (\p. p) <= R) /\
        2 <= t /\ (!p. p IN P ==> lf_fam_ok p t Js (\j i. &W * c j i)) /\
        prime N /\ t * K * M < N /\
        (!j i. j IN Js /\ i < t ==> abs(c j i) <= &K) /\
        (!j. j IN Js ==> ?i. i < t /\ ~((&N:int) divides c j i))
        ==> &M pow t *
            abs(sum (cartesian_product {i | i < t} (\i. {r | r < N}))
                    (\x. product Js
                          (\j. gtnu W (b j) D P (lf_form {i | i < t}
                            (c j) (c0 j) x
                                           rem &N))) -
                &N pow t)
            <= &N pow t * lf_err t M P D R (CARD Js) +
               (&(CARD Js) * &2 * &(t * K * M) * &N pow (t - 1)) *
               (&3 pow CARD Js * (&M pow t + lf_err t M P D R (CARD Js)) +
                &M pow t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:num`; `N:num`; `M:num`;
                 `\x:num->num. product Js
                    (\j. gtnu W ((b:num->num) j) D P
                         (lf_form {i | i < t} ((c:num->num->int) j)
                                      ((c0:num->int) j) x rem &N))`]
         TRANSLATE_AVERAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `ZN = cartesian_product {i | i < t}
    (\i:num. {r:num | r < N})` THEN
  SUBGOAL_THEN `FINITE(ZN:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ZN" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD(ZN:(num->num)->bool)) = &N pow t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_SUM] THEN EXPAND_TAC "ZN" THEN
    SIMP_TAC[SUM_CARTESIAN_ONE; FINITE_NUMSEG_LT; CARD_NUMSEG_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum ZN (\x. lf_err t M P D R (CARD(Js:num->bool)) +
                (if !j. j IN Js
                        ==> &(t * K * M) <=
                            lf_form {i | i < t} ((c:num->num->int) j)
                              ((c0:num->int) j) x
                            rem &N /\
                            lf_form {i | i < t} (c j) (c0 j) x rem &N +
                            &(t * K * M) < &N
                 then &0 else &1) *
                (&3 pow CARD Js * (&M pow t + lf_err t M P D R (CARD Js)) +
                 &M pow t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `abs(sum ZN (\x. sum (cartesian_product {i | i < t} (\i. {r | r < M}))
           (\y. product Js (\j. gtnu W ((b:num->num) j) D P
              (lf_form {i | i < t} ((c:num->num->int) j) ((c0:num->int) j)
                 (\i. if i < t then (x i + y i) MOD N else ARB) rem &N))) -
           &M pow t))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_SUB; SUM_CONST] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) &&
        can (term_match [] `&M pow t * x:real`) (lhand(concl th)))) THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      REWRITE_TAC[REAL_ARITH `!m s n:real. m * s - n * m = m * (s - n)`] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM];
      MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC PER_X_BOUND THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_CONST; SUM_RMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> n * e + x <= n * e + y`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_ADD THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC LF_ERR_POS THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum ZN (\x. sum Js (\j.
       if &(t * K * M) <= lf_form {i | i < t} ((c:num->num->int) j)
         ((c0:num->int) j) x
                          rem &N /\
          lf_form {i | i < t} (c j) (c0 j) x rem &N + &(t * K * M) < &N
       then &0 else &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BAD_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Js (\j:num. &2 * &(t * K * M) * &N pow (t - 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `!j. j IN Js
                     ==> ?i. i < t /\
                       ~((&N:int) divides (c:num->num->int) j i)` THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "ZN" THEN MATCH_MP_TAC BAD_FORM_COUNT THEN
    EXISTS_TAC `i0:num` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_ASSOC; REAL_LE_REFL]]);;
