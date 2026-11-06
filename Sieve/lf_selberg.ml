(* ========================================================================= *)
(* Linear forms in many variables, part 2: sums of Selberg weights.          *)
(*                                                                           *)
(* The weights are lambda = selberg_weight g D (selberg.ml) for a family D   *)
(* of subsets of s closed under subsets; Y = sum_D selberg_H g.  Below       *)
(* g p = 1 / p and the squarefree d = prod A correspond to the A IN D.       *)
(* * SELBERG_DIAG2 (bilinear diagonalisation):                               *)
(*     sum_{t1, t2} a(t1) b(t2) prod_{t1 UNION t2} g                         *)
(*     = sum_k prod_k (1/g - 1) (sum_{t >= k} prod_t g a(t))                 *)
(*                              (sum_{t >= k} prod_t g b(t)).                *)
(* * One-form sums selberg_tsum g lambda s V V' (over t1 >= V, t2 >= V' of   *)
(*   lambda t1 lambda t2 prod_{t1 UNION t2} g): SELBERG_TSUM_DIAG,           *)
(*   SELBERG_TSUM_SELBERG in the dual variables selberg_y, and               *)
(*   SELBERG_TSUM_BOUND: |selberg_tsum| <= selberg_ebound g V V' / Y.  The   *)
(*   sums selberg_lfcsum constrained to t1 UNION t2 >= Q (inclusion-         *)
(*   exclusion over Q): SELBERG_LFCSUM_BOUND, SELBERG_LFCSUM_MAIN (= 1/Y for *)
(*   Q = {}) and SELBERG_LFCSUM_PRIME_BOUND (|selberg_lfcsum Q| <= prod_Q    *)
(*   (9/p) / Y).                                                             *)
(* * Local factors selberg_kappa t p B B0 J = p^|J| lf_ncount / p^t and      *)
(*   their Moebius inversion selberg_smob on the subset lattice              *)
(*   (SELBERG_SMOB_INVERSION).  For families nondegenerate mod p             *)
(*   (lf_fam_ok): selberg_kappa = 1 for |J| <= 2, 0 <= selberg_kappa <=      *)
(*   p^(|J| - 2); so selberg_smob selberg_kappa vanishes for 1 <= |J| <= 2   *)
(*   and is at most 2^|J| p^(|J| - 2) (LALPHA_ZERO, LALPHA_BOUND).           *)
(* * MS_EXPANSION: the main term                                             *)
(*     sum_{T1, T2} prod_j lambda(T1 j) lambda(T2 j) prod_P lf_ncount / p^t  *)
(*   is exactly a sum over assignments sg : P -> subsets of Js of            *)
(*   prod_P selberg_smob selberg_kappa (sg p) prod_j selberg_lfcsum (...);   *)
(*   with LOCAL_SUM_BOUND, MS_BOUND: it is Y^-m (1 + e), |e| <= prod_P (1 +  *)
(*   19^m / p^2) - 1.                                                        *)
(* ========================================================================= *)

needs "Sieve/lf_local.ml";;
needs "Sieve/selberg.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The bilinear diagonalisation of the Selberg form.                         *)
(* ------------------------------------------------------------------------- *)

let SELBERG_DIAG2 = prove
 (`!(g:A->real) (a:(A->bool)->real) (b:(A->bool)->real) s.
        FINITE s /\ (!p. p IN s ==> &0 < g p)
        ==> sum {t1 | t1 SUBSET s}
                (\t1. sum {t2 | t2 SUBSET s}
                          (\t2. a t1 * b t2 * product (t1 UNION t2) g)) =
            sum {k | k SUBSET s}
                (\k. product k (\p. inv(g p) - &1) *
                     sum {t | t SUBSET s /\ k SUBSET t}
                         (\t. product t g * a t) *
                     sum {t | t SUBSET s /\ k SUBSET t}
                         (\t. product t g * b t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {t:A->bool | t SUBSET s}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t1 t2. t1 SUBSET s /\ t2 SUBSET s
            ==> product (t1 UNION t2) g =
                product t1 g * product t2 (g:A->real) *
                sum {k | k SUBSET s}
                    (\k. if k SUBSET t1 /\ k SUBSET t2
                         then product k (\p. inv(g p) - &1) else &0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `FINITE(t1:A->bool) /\ FINITE(t2:A->bool) /\
                  FINITE(t1 INTER t2:A->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; FINITE_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < product (t1 INTER t2) (g:A->real)` ASSUME_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum {k | k SUBSET s}
          (\k. if k SUBSET t1 /\ k SUBSET t2
               then product k (\p. inv((g:A->real) p) - &1) else &0) =
      inv(product (t1 INTER t2) g)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUBSET_INTER] THEN
      MP_TAC(ISPECL [`\k:A->bool. product k (\p. inv((g:A->real) p) - &1)`;
                     `s:A->bool`; `t1 INTER t2:A->bool`]
             SUM_POWERSET_RESTRICT) THEN
      ANTS_TAC THENL [ASM SET_TAC[];
                      DISCH_THEN(SUBST1_TAC o SYM o BETA_RULE)] THEN
      ASM_SIMP_TAC[GSYM PRODUCT_ADD_EXPAND; GSYM PRODUCT_INV] THEN
      MATCH_MP_TAC PRODUCT_EQ THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:A->real`; `t1:A->bool`; `t2:A->bool`]
           PRODUCT_UNION_INTER) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < product (t1 INTER t2) (g:A->real)`
    THEN ABBREV_TAC `Pi = product (t1 INTER t2) (g:A->real)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {t1 | t1 SUBSET s}
        (\t1. sum {t2 | t2 SUBSET s}
                  (\t2. sum {k | k SUBSET s}
                            (\k. product k (\p. inv(g p) - &1) *
                                 (if k SUBSET t1 then product t1 g * a t1
                                  else &0) *
                                 (if k SUBSET t2 then product t2 (g:A->real) *
                                    (b:(A->bool)->real) t2 else &0))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t1:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t2:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `k SUBSET (t1:A->bool)` THEN
    ASM_CASES_TAC `k SUBSET (t2:A->bool)` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {t1 | t1 SUBSET s}
        (\t1. sum {k | k SUBSET s}
                  (\k. sum {t2 | t2 SUBSET s}
                           (\t2. product k (\p. inv(g p) - &1) *
                                 (if k SUBSET t1 then product t1 g * a t1
                                  else &0) *
                                 (if k SUBSET t2 then product t2 (g:A->real) *
                                    (b:(A->bool)->real) t2 else &0))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  REWRITE_TAC[SUM_LMUL; SUM_RMUL; GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `{t:A->bool | t SUBSET s /\ k SUBSET t} =
                {t | t IN {t | t SUBSET s} /\ k SUBSET t}` SUBST1_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[SUM_RESTRICT_SET]);;

(* ------------------------------------------------------------------------- *)
(* One-form sums.                                                            *)
(* ------------------------------------------------------------------------- *)

let selberg_tsum = new_definition
 `selberg_tsum (g:A->real) (lmw:(A->bool)->real) s V V' =
    sum {t1 | t1 SUBSET s}
        (\t1. sum {t2 | t2 SUBSET s}
                  (\t2. (if V SUBSET t1 then lmw t1 else &0) *
                        (if V' SUBSET t2 then lmw t2 else &0) *
                        product (t1 UNION t2) g))`;;

let SELBERG_TSUM_DIAG = prove
 (`!(g:A->real) lmw s V V'.
        FINITE s /\ (!p. p IN s ==> &0 < g p)
        ==> selberg_tsum g lmw s V V' =
            sum {k | k SUBSET s}
                (\k. product k (\p. inv(g p) - &1) *
                     sum {t | t SUBSET s /\ V UNION k SUBSET t}
                         (\t. product t g * lmw t) *
                     sum {t | t SUBSET s /\ V' UNION k SUBSET t}
                         (\t. product t g * lmw t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_tsum] THEN
  ASM_SIMP_TAC[SELBERG_DIAG2] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN BINOP_TAC THEN REWRITE_TAC[] THEN BINOP_TAC THEN
  REWRITE_TAC[UNION_SUBSET; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{t:A->bool | t SUBSET s /\ P t /\ k SUBSET t} =
    {t | t IN {t | t SUBSET s /\ k SUBSET t} /\ P t}`] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO]);;

let selberg_y = new_definition
 `selberg_y (g:A->real) D u =
    if u IN D then (-- &1) pow CARD u * selberg_H g u / sum D (selberg_H g)
    else &0`;;

let SELBERG_TSUM_SELBERG = prove
 (`!(g:A->real) s D V V'.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ V SUBSET s /\ V' SUBSET s
        ==> selberg_tsum g (selberg_weight g D) s V V' =
            sum {k | k SUBSET s}
                (\k. product k (\p. inv(g p) - &1) *
                     selberg_y g D (V UNION k) * selberg_y g D (V' UNION k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p:A. p IN s ==> &0 < g p` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SELBERG_TSUM_DIAG] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[selberg_y] THEN
  BINOP_TAC THEN REWRITE_TAC[] THEN BINOP_TAC THEN
  MATCH_MP_TAC SELBERG_WEIGHT_Y THEN ASM_REWRITE_TAC[UNION_SUBSET]);;

let SELBERG_Y_ABS = prove
 (`!(g:A->real) s D u.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ u SUBSET s
        ==> abs(selberg_y g D u) <=
            (if u IN D then selberg_H g u else &0) / sum D (selberg_H g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_y] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_ABS_0; real_div; REAL_MUL_LZERO; REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_NUM;
              REAL_POW_ONE; REAL_MUL_LID; REAL_ABS_INV] THEN
  SUBGOAL_THEN `&0 < selberg_H (g:A->real) u /\ &1 <= sum D (selberg_H g)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SELBERG_H_POS; SELBERG_G_GE_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_ARITH `&1 <= x ==> abs x = x`; REAL_LE_REFL]);;

let SELBERG_H_UNION_SPLIT = prove
 (`!(g:A->real) V k.
        FINITE V /\ FINITE k
        ==> selberg_H g (V UNION k) =
            selberg_H g V *
            product k (\p. if p IN V then &1 else g p / (&1 - g p))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_H] THEN
  SUBGOAL_THEN `V UNION k = V UNION {p:A | p IN k /\ ~(p IN V)}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT] THEN SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PRODUCT_RESTRICT_SET] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let SELBERG_TSUM_ABS_LE = prove
 (`!(g:A->real) s D V V'.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ V SUBSET s /\ V' SUBSET s
        ==> abs(selberg_tsum g (selberg_weight g D) s V V') <=
            sum {k | k SUBSET s}
                (\k. product k (\p. inv(g p) - &1) *
                     (if V UNION k IN D then selberg_H g (V UNION k) else &0) *
                     selberg_H g (V' UNION k) / sum D (selberg_H g) pow 2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SELBERG_TSUM_SELBERG] THEN
  MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
  X_GEN_TAC `k:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ABBREV_TAC `Y = sum D (selberg_H (g:A->real))` THEN
  SUBGOAL_THEN `&1 <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN ASM_MESON_TAC[SELBERG_G_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product k (\p:A. inv(g p) - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (g:A->real) p /\ g p < &1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_INV_1_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= selberg_H (g:A->real) (V' UNION k)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SELBERG_H_POS THEN
    EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[UNION_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `D:(A->bool)->bool`;
                 `V UNION k:A->bool`] SELBERG_Y_ABS) THEN
  MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `D:(A->bool)->bool`;
                 `V' UNION k:A->bool`] SELBERG_Y_ABS) THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  SUBGOAL_THEN `(if V' UNION k IN D then selberg_H (g:A->real) (V' UNION k)
                 else &0) <= selberg_H g (V' UNION k)` MP_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (if V UNION k IN D then selberg_H (g:A->real) (V UNION k)
                       else &0)` MP_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SELBERG_H_POS THEN
    EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[UNION_SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `A1 = (if V UNION k IN D then selberg_H (g:A->real) (V UNION k)
                    else &0)` THEN
  ABBREV_TAC `A2 = (if V' UNION k IN D then selberg_H (g:A->real) (V' UNION k)
                    else &0)` THEN
  ABBREV_TAC `B2 = selberg_H (g:A->real) (V' UNION k)` THEN
  ABBREV_TAC `y1 = selberg_y (g:A->real) D (V UNION k)` THEN
  ABBREV_TAC `y2 = selberg_y (g:A->real) D (V' UNION k)` THEN
  ABBREV_TAC `Pk = product k (\p:A. inv(g p) - &1)` THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  SUBGOAL_THEN `(Pk:real) * A1 * B2 / Y pow 2 = Pk * (A1 / Y) * (B2 / Y)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= Y` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(A2:real) / Y` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < Y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ]);;

let selberg_cfun = new_definition
 `selberg_cfun (g:num->real) V V' p =
    (inv(g p) - &1) * (if p IN V then &1 else g p / (&1 - g p)) *
    (if p IN V' then &1 else g p / (&1 - g p))`;;

let SELBERG_CFUN_POS = prove
 (`!g V V' p. &0 < g p /\ g p < &1 ==> &0 <= selberg_cfun g V V' p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_cfun] THEN
  SUBGOAL_THEN `&0 <= (g:num->real) p / (&1 - g p)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_INV_1_LE THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]);;

let SELBERG_H_PAIR_SPLIT = prove
 (`!(g:num->real) V V' k.
        FINITE V /\ FINITE V' /\ FINITE k
        ==> product k (\p. inv(g p) - &1) *
            selberg_H g (V UNION k) * selberg_H g (V' UNION k) =
            selberg_H g V * selberg_H g V' * product k (selberg_cfun g V V')`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SELBERG_H_UNION_SPLIT] THEN
  SUBGOAL_THEN
   `selberg_cfun (g:num->real) V V' =
    (\p. (inv(g p) - &1) *
         ((if p IN V then &1 else g p / (&1 - g p)) *
          (if p IN V' then &1 else g p / (&1 - g p))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; selberg_cfun]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_MUL] THEN REAL_ARITH_TAC);;

let TSUM_TERM_LE = prove
 (`!(g:num->real) s D V V' k.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ V SUBSET s /\ V' SUBSET s /\ k SUBSET s
        ==> product k (\p. inv(g p) - &1) *
            (if V UNION k IN D then selberg_H g (V UNION k) else &0) *
            selberg_H g (V' UNION k)
            <= selberg_H g V * selberg_H g V' *
               product (k INTER (V UNION V')) (selberg_cfun g V V') *
               (if k DIFF (V UNION V') IN D
                then product (k DIFF (V UNION V'))
                  (selberg_cfun g V V') else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(V:num->bool) /\ FINITE(V':num->bool) /\
                FINITE(k:num->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN k ==> &0 <= selberg_cfun (g:num->real) V V' p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELBERG_CFUN_POS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= selberg_H (g:num->real) V /\ &0 <= selberg_H g V' /\
                &0 <= product (k INTER (V UNION V')) (selberg_cfun g V V') /\
                &0 <= product (k DIFF (V UNION V')) (selberg_cfun g V V')`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC PRODUCT_POS_LE THEN
        ASM_SIMP_TAC[FINITE_INTER; FINITE_DIFF] THEN
        REWRITE_TAC[IN_INTER; IN_DIFF] THEN ASM_MESON_TAC[]) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SELBERG_H_POS THEN
    EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product k (selberg_cfun (g:num->real) V V') =
    product (k INTER (V UNION V')) (selberg_cfun g V V') *
    product (k DIFF (V UNION V')) (selberg_cfun g V V')`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(k:num->bool) DIFF (V UNION V') =
                  k INTER (s DIFF (V UNION V'))`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PRODUCT_INTER_UNION THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `V UNION k IN (D:(num->bool)->bool)` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THENL
   [SUBGOAL_THEN `k DIFF (V UNION V') IN (D:(num->bool)->bool)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `selberg_family s (D:(num->bool)->bool)` THEN
      REWRITE_TAC[selberg_family] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `V UNION k:num->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g:num->real`; `V:num->bool`; `V':num->bool`;
                  `k:num->bool`] SELBERG_H_PAIR_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_REFL];
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[]]);;

let SELBERG_CFUN_OUTSIDE = prove
 (`!(g:num->real) V V' p.
        &0 < g p /\ g p < &1 /\ ~(p IN V) /\ ~(p IN V')
        ==> selberg_cfun g V V' p = g p / (&1 - g p)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[selberg_cfun] THEN
  SUBGOAL_THEN `~((g:num->real) p = &0) /\ ~(&1 - g p = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let SELBERG_CFUN_INSIDE = prove
 (`!(g:num->real) V V' p.
        &0 < g p /\ g p < &1 /\ (p IN V \/ p IN V')
        ==> &1 + selberg_cfun g V V' p =
            (if p IN V /\ p IN V' then inv(g p) else &2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[selberg_cfun] THEN
  SUBGOAL_THEN `~((g:num->real) p = &0) /\ ~(&1 - g p = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(p:num) IN V` THEN ASM_CASES_TAC `(p:num) IN V'` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD);;

let SELBERG_TSUM_BOUND = prove
 (`!(g:num->real) s D V V'.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ V SUBSET s /\ V' SUBSET s
        ==> abs(selberg_tsum g (selberg_weight g D) s V V') <=
            selberg_H g V * selberg_H g V' *
            product (V UNION V')
                    (\p. if p IN V /\ p IN V' then inv(g p) else &2) /
            sum D (selberg_H g)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SELBERG_TSUM_ABS_LE o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  ABBREV_TAC `Y = sum D (selberg_H (g:num->real))` THEN
  SUBGOAL_THEN `&1 <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN ASM_MESON_TAC[SELBERG_G_GE_1]; ALL_TAC] THEN
  ABBREV_TAC `U = V UNION V':num->bool` THEN
  SUBGOAL_THEN `FINITE(U:num->bool) /\ U SUBSET s /\
                FINITE(s DIFF U:num->bool) /\ DISJOINT U (s DIFF U) /\
                U UNION (s DIFF U) = s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[UNION_SUBSET] THEN
    ASM_SIMP_TAC[FINITE_DIFF] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_UNION]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {k:num->bool | k SUBSET s}
        (\k. (selberg_H (g:num->real) V * selberg_H g V' *
              product (k INTER U) (selberg_cfun g V V') *
              (if k INTER (s DIFF U) IN (D:(num->bool)->bool)
               then product (k INTER (s DIFF U))
                 (selberg_cfun g V V') else &0)) /
             Y pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    X_GEN_TAC `k:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * b * c * d:real = (a * b * c) * d`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `k INTER (s DIFF U) = (k:num->bool) DIFF U` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    EXPAND_TAC "U" THEN MATCH_MP_TAC TSUM_TERM_LE THEN
    EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; SUM_RMUL] THEN
  REWRITE_TAC[REAL_ARITH `a * b * c * d:real = (a * b) * (c * d)`] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN `{k:num->bool | k SUBSET s} = {k | k SUBSET U UNION (s DIFF U)}`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:num->bool`; `s DIFF U:num->bool`;
                 `\v:num->bool. product v (selberg_cfun (g:num->real) V V')`;
                 `\v:num->bool. if v IN (D:(num->bool)->bool)
                                then product v
                                  (selberg_cfun (g:num->real) V V')
                                else &0`] SUM_POWERSET_DISJOINT_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GSYM PRODUCT_ADD_EXPAND] THEN
  SUBGOAL_THEN
   `product U (\p. &1 + selberg_cfun (g:num->real) V V' p) =
    product U (\p. if p IN V /\ p IN V' then inv(g p) else &2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SELBERG_CFUN_INSIDE THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {v | v SUBSET s DIFF U}
        (\v. if v IN (D:(num->bool)->bool)
             then product v (selberg_cfun (g:num->real) V V') else &0) <= Y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {v | v IN {v | v SUBSET s DIFF U} /\
                         v IN (D:(num->bool)->bool)}
                    (selberg_H (g:num->real))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:num->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[selberg_H] THEN
      MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC SELBERG_CFUN_OUTSIDE THEN
      SUBGOAL_THEN `(p:num) IN s /\ ~(p IN V) /\ ~(p IN V')` STRIP_ASSUME_TAC
      THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      EXPAND_TAC "Y" THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SELBERG_FAMILY_FINITE]; ALL_TAC] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `v:num->bool` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SELBERG_H_POS THEN
      EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `selberg_family s (D:(num->bool)->bool)` THEN
      REWRITE_TAC[selberg_family; SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Sv = sum {v | v SUBSET s DIFF U}
        (\v. if v IN (D:(num->bool)->bool)
             then product v (selberg_cfun (g:num->real) V V') else &0)` THEN
  ABBREV_TAC `Pu = product U
    (\p. if p IN V /\ p IN V' then inv((g:num->real) p) else &2)` THEN
  SUBGOAL_THEN `&0 <= selberg_H (g:num->real) V * selberg_H g V' * Pu`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= selberg_H (g:num->real) V /\ &0 <= selberg_H g V'`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC SELBERG_H_POS THEN EXISTS_TAC `s:num->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Pu` ASSUME_TAC THENL
     [EXPAND_TAC "Pu" THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_POS] THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN
      SUBGOAL_THEN `&0 < (g:num->real) p` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Sv * inv(Y pow 2) <= inv Y` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < Y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
     REAL_POW_LT] THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV;
      REAL_LT_IMP_NZ; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((selberg_H (g:num->real) V * selberg_H g V') * Pu * Sv) * inv(Y pow 2) =
    (selberg_H g V * selberg_H g V' * Pu) * (Sv * inv(Y pow 2)) /\
    (selberg_H g V * selberg_H g V') * Pu * inv Y =
    (selberg_H g V * selberg_H g V' * Pu) * inv Y`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sums constrained to cover a set of primes.                                *)
(* ------------------------------------------------------------------------- *)

let selberg_lfcsum = new_definition
 `selberg_lfcsum (g:A->real) (lmw:(A->bool)->real) s Q V V' =
    sum {t1 | t1 SUBSET s}
        (\t1. sum {t2 | t2 SUBSET s}
                  (\t2. (if Q SUBSET t1 UNION t2 /\ V SUBSET t1 /\ V' SUBSET t2
                         then lmw t1 * lmw t2 else &0) *
                        product (t1 UNION t2) g))`;;

let SELBERG_LFCSUM_EMPTY = prove
 (`!(g:A->real) lmw s V V'. selberg_lfcsum g lmw s {} V V' =
                            selberg_tsum g lmw s V V'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[selberg_lfcsum; selberg_tsum; EMPTY_SUBSET] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t1:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t2:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `(V:A->bool) SUBSET t1` THEN
  ASM_CASES_TAC `(V':A->bool) SUBSET t2` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SELBERG_LFCSUM_INSERT = prove
 (`!(g:A->real) lmw s Q V V' p.
        FINITE s
        ==> selberg_lfcsum g lmw s (p INSERT Q) V V' =
            selberg_lfcsum g lmw s Q (p INSERT V) V' +
            selberg_lfcsum g lmw s Q V
              (p INSERT V') -
            selberg_lfcsum g lmw s Q (p INSERT V) (p INSERT V')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_lfcsum] THEN
  ASM_SIMP_TAC[GSYM SUM_ADD; GSYM SUM_SUB; FINITE_POWERSET] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t1:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM SUM_ADD; GSYM SUM_SUB; FINITE_POWERSET] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t2:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[INSERT_SUBSET; IN_UNION] THEN
  ASM_CASES_TAC `(p:A) IN t1` THEN ASM_CASES_TAC `(p:A) IN t2` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SELBERG_LFCSUM_INSERT_TRIVIAL = prove
 (`!(g:A->real) lmw s Q V V' p.
        p IN V UNION V'
        ==> selberg_lfcsum g lmw s (p INSERT Q) V V' =
            selberg_lfcsum g lmw s Q V V'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_lfcsum] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t1:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t2:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[INSERT_SUBSET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM SET_TAC[]);;

let selberg_ebound = new_definition
 `selberg_ebound (g:num->real) V V' =
    selberg_H g V * selberg_H g V' *
    product (V UNION V') (\p. if p IN V /\ p IN V' then inv(g p) else &2)`;;

let SELBERG_EBOUND_EMPTY = prove
 (`!g:num->real. selberg_ebound g {} {} = &1`,
  REWRITE_TAC[selberg_ebound; selberg_H; UNION_EMPTY; PRODUCT_CLAUSES] THEN
  REAL_ARITH_TAC);;

let SELBERG_EBOUND_INSERT = prove
 (`!(g:num->real) V V' p.
        FINITE V /\ FINITE V' /\ ~(p IN V) /\ ~(p IN V')
        ==> selberg_ebound g (p INSERT V) V' =
              selberg_ebound g V V' * &2 * g p / (&1 - g p) /\
            selberg_ebound g V (p INSERT V') =
              selberg_ebound g V V' * &2 * g p / (&1 - g p) /\
            selberg_ebound g (p INSERT V) (p INSERT V') =
              selberg_ebound g V V' * (g p / (&1 - g p)) pow 2 * inv(g p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[selberg_ebound; selberg_H] THEN
  REWRITE_TAC[SET_RULE `((p:num) INSERT V) UNION V' = p INSERT (V UNION V')`;
              SET_RULE `(V:num->bool) UNION (p INSERT V') =
                        p INSERT (V UNION V')`;
              SET_RULE `((p:num) INSERT V) UNION (p INSERT V') =
                        p INSERT (V UNION V')`] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_UNION; IN_UNION; IN_INSERT] THEN
  SUBGOAL_THEN
   `(!x:num. (x = p \/ x IN V) /\ x IN V' <=> x IN V /\ x IN V') /\
    (!x:num. x IN V /\ (x = p \/ x IN V') <=> x IN V /\ x IN V') /\
    (!x:num. (x = p \/ x IN V) /\ (x = p \/ x IN V') <=>
             x = p \/ x IN V /\ x IN V')`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `product (V UNION V')
      (\x. if x = p \/ x IN V /\ x IN V' then inv((g:num->real) x) else &2) =
    product (V UNION V')
      (\x. if x IN V /\ x IN V' then inv(g x) else &2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `x:num` THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:num = p)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `A = product (V UNION V')
                  (\p. if p IN V /\ p IN V' then inv((g:num->real) p)
                    else &2)` THEN
  ABBREV_TAC `B = product V (\p. (g:num->real) p / (&1 - g p))` THEN
  ABBREV_TAC `B' = product V' (\p. (g:num->real) p / (&1 - g p))` THEN
  ABBREV_TAC `h = (g:num->real) p / (&1 - g p)` THEN
  REAL_ARITH_TAC);;

let SELBERG_LFCSUM_BOUND = prove
 (`!(g:num->real) s D Q V V'.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ Q SUBSET s /\ V SUBSET s /\ V' SUBSET s
        ==> abs(selberg_lfcsum g (selberg_weight g D) s Q V V') <=
            selberg_ebound g V V' *
            product (Q DIFF (V UNION V'))
              (\p. &4 * g p / (&1 - g p) + (g p / (&1 - g p)) pow 2 / g p) /
            sum D (selberg_H g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(Q:num->bool)` MP_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(Q:num->bool) SUBSET s` THEN
  UNDISCH_TAC `(V':num->bool) SUBSET s` THEN
  UNDISCH_TAC `(V:num->bool) SUBSET s` THEN
  SPEC_TAC(`V':num->bool`,`V':num->bool`) THEN
  SPEC_TAC(`V:num->bool`,`V:num->bool`) THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d ==> e <=>
                        d ==> c ==> a /\ b ==> e`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  SPEC_TAC(`Q:num->bool`,`Q:num->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[EMPTY_DIFF; PRODUCT_CLAUSES; SELBERG_LFCSUM_EMPTY] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SELBERG_TSUM_BOUND o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[selberg_ebound; real_div; REAL_MUL_LID; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `Q:num->bool`] THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`V:num->bool`; `V':num->bool`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:num) IN V UNION V'` THENL
   [ASM_SIMP_TAC[SELBERG_LFCSUM_INSERT_TRIVIAL] THEN
    SUBGOAL_THEN `((x:num) INSERT Q) DIFF (V UNION V') = Q DIFF (V UNION V')`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SELBERG_LFCSUM_INSERT] THEN
  SUBGOAL_THEN `((x:num) INSERT Q) DIFF (V UNION V') =
                x INSERT (Q DIFF (V UNION V')) /\
                ~(x IN Q DIFF (V UNION V')) /\
                FINITE(Q DIFF (V UNION V')) /\
                Q DIFF ((x INSERT V) UNION V') = Q DIFF (V UNION V') /\
                Q DIFF (V UNION (x INSERT V')) = Q DIFF (V UNION V') /\
                Q DIFF ((x INSERT V) UNION (x INSERT V')) =
                Q DIFF (V UNION V')`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_DIFF] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(x:num) INSERT V`; `V':num->bool`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`V:num->bool`; `(x:num) INSERT V'`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(x:num) INSERT V`; `(x:num) INSERT V'`]) THEN
  ASM_REWRITE_TAC[INSERT_SUBSET] THEN
  SUBGOAL_THEN `FINITE(V:num->bool) /\ FINITE(V':num->bool) /\
                ~((x:num) IN V) /\ ~(x IN V')` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SELBERG_EBOUND_INSERT] THEN
  ABBREV_TAC `h = (g:num->real) x / (&1 - g x)` THEN
  ABBREV_TAC `E = selberg_ebound (g:num->real) V V'` THEN
  ABBREV_TAC `Pq = product (Q DIFF (V UNION V'))
      (\p. &4 * (g:num->real) p / (&1 - g p) + (g p / (&1 - g p)) pow 2
        / g p)` THEN
  ABBREV_TAC `Y = sum D (selberg_H (g:num->real))` THEN
  ABBREV_TAC `c1 = selberg_lfcsum (g:num->real) (selberg_weight g D) s Q
    (x INSERT V) V'` THEN
  ABBREV_TAC `c2 = selberg_lfcsum (g:num->real) (selberg_weight g D) s Q V
    (x INSERT V')` THEN
  ABBREV_TAC
    `c3 = selberg_lfcsum (g:num->real) (selberg_weight g D) s Q (x INSERT V)
    (x INSERT V')` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Local factors and their Moebius inversion.                                *)
(* ------------------------------------------------------------------------- *)

let selberg_smob = new_definition
 `selberg_smob (kap:(A->bool)->real) J =
    sum {J' | J' SUBSET J} (\J'. (-- &1) pow (CARD J + CARD J') * kap J')`;;

let SELBERG_SMOB_INVERSION = prove
 (`!(kap:(A->bool)->real) J.
        FINITE J ==> sum {J' | J' SUBSET J} (selberg_smob kap) = kap J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_smob] THEN
  SUBGOAL_THEN `FINITE {J':A->bool | J' SUBSET J}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {J' | J' SUBSET J}
        (\J'. sum {J'' | J'' SUBSET J}
                  (\J''. if J'' SUBSET J'
                         then (-- &1) pow (CARD J' + CARD J'') *
                              (kap:(A->bool)->real) J''
                         else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `J':A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[selberg_smob] THEN
    MATCH_MP_TAC SUM_POWERSET_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {J'' | J'' SUBSET J}
        (\J''. (kap:(A->bool)->real) J'' * (-- &1) pow CARD J'' *
               sum {J' | J'' SUBSET J' /\ J' SUBSET J}
                   (\J'. (-- &1) pow CARD J'))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `J'':A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{J':A->bool | J'' SUBSET J' /\ J' SUBSET J} =
      {J' | J' IN {J' | J' SUBSET J} /\ J'' SUBSET J'}`] THEN
    REWRITE_TAC[SUM_RESTRICT_SET] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `J':A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_POW_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_SUBSETS_BETWEEN_SIGN] THEN
  REWRITE_TAC[COND_RAND; REAL_MUL_RZERO] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {J'' | J'' SUBSET J}
                  (\x:A->bool. if x = J then (kap:(A->bool)->real) J
                    else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `x:A->bool = J` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_POW_ADD; REAL_POW_NEG; REAL_POW_ONE; EVEN_ADD] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SUM_DELTA; IN_ELIM_THM; SUBSET_REFL]]);;

let SELBERG_SMOB_EMPTY = prove
 (`!kap:(A->bool)->real. selberg_smob kap {} = kap {}`,
  REWRITE_TAC[selberg_smob; SUBSET_EMPTY; SING_GSPEC; SUM_SING;
              CARD_CLAUSES] THEN
  REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_LID]);;

let SELBERG_SMOB_ZERO = prove
 (`!(kap:(A->bool)->real) J.
        FINITE J /\ ~(J = {}) /\ (!J'. J' SUBSET J ==> kap J' = &1)
        ==> selberg_smob kap J = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_smob] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(-- &1) pow CARD(J:A->bool) *
              sum {J' | J' SUBSET J} (\J':A->bool. (-- &1) pow CARD J')` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_POW_ADD; REAL_MUL_RID];
    ASM_SIMP_TAC[SUM_POWERSET_SIGN; REAL_MUL_RZERO]]);;

let SELBERG_SMOB_BOUND = prove
 (`!(kap:(A->bool)->real) J c.
        FINITE J /\ (!J'. J' SUBSET J ==> abs(kap J') <= c)
        ==> abs(selberg_smob kap J) <= &2 pow CARD J * c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_smob] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {J' | J' SUBSET J} (\J':A->bool. c)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_NUM;
                REAL_POW_ONE; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[SUM_CONST; FINITE_POWERSET; CARD_POWERSET] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_LE_REFL]]);;

let SMALL_SET_CASES = prove
 (`!J:A->bool. FINITE J /\ CARD J <= 2
               ==> J = {} \/ (?a. J = {a}) \/ (?a b. ~(a = b) /\ J = {a,b})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(J:A->bool) HAS_SIZE CARD J` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  UNDISCH_TAC `CARD(J:A->bool) <= 2` THEN
  SPEC_TAC(`CARD(J:A->bool)`,`n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n <= 2 <=> n = 0 \/ n = 1 \/ n = 2`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV HAS_SIZE_CONV)) THEN ASM_MESON_TAC[]);;

let selberg_kappa = new_definition
 `selberg_kappa t p (B:num->num->int) (B0:num->int) (J:num->bool) =
    &p pow CARD J * lf_ncount {i | i < t} p B B0 J / &p pow t`;;

let lf_fam_ok = new_definition
 `lf_fam_ok p t Js (B:num->num->int) <=>
    (!j. j IN Js ==> lf_pnz p {i | i < t} (B j)) /\
    (!j j'. j IN Js /\ j' IN Js /\ ~(j = j')
            ==> lf_pind p {i | i < t} (B j) (B j') \/
                lf_pind p {i | i < t} (B j') (B j))`;;

let SELBERG_KAPPA_EMPTY = prove
 (`!t p B B0. prime p ==> selberg_kappa t p B B0 {} = &1`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[selberg_kappa; LF_NCOUNT_EMPTY; FINITE_NUMSEG_LT; CARD_CLAUSES;
           CARD_NUMSEG_LT; real_pow; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_DIV_REFL THEN MATCH_MP_TAC REAL_POW_NZ THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_0]);;

let SELBERG_KAPPA_SMALL = prove
 (`!t p Js (B:num->num->int) B0 J.
        prime p /\ 2 <= t /\ lf_fam_ok p t Js B /\ J SUBSET Js /\
        FINITE J /\ CARD J <= 2
        ==> selberg_kappa t p B B0 J = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&p pow t = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_NZ THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  UNDISCH_TAC `lf_fam_ok p t Js (B:num->num->int)` THEN
  REWRITE_TAC[lf_fam_ok] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `J:num->bool` SMALL_SET_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [ASM_SIMP_TAC[SELBERG_KAPPA_EMPTY];
    ASM_REWRITE_TAC[selberg_kappa] THEN
    SUBGOAL_THEN `lf_pnz p {i | i < t} ((B:num->num->int) a)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[LF_NCOUNT_SING; FINITE_NUMSEG_LT; CARD_NUMSEG_LT;
                 CARD_SING] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= t ==> 1 + t - 1 = t`; REAL_MUL_RINV];
    ASM_REWRITE_TAC[selberg_kappa] THEN
    SUBGOAL_THEN `(a:num) IN Js /\ b IN Js` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `lf_ncount {i | i < t} p (B:num->num->int) B0 {a,b} =
                  &p pow (t - 2)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [ASM_SIMP_TAC[LF_NCOUNT_PAIR; FINITE_NUMSEG_LT; CARD_NUMSEG_LT];
        ONCE_REWRITE_TAC[SET_RULE `{a:num,b} = {b,a}`] THEN
        ASM_SIMP_TAC[LF_NCOUNT_PAIR; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= t ==> SUC(SUC 0) + t - 2 = t`;
                 REAL_MUL_RINV]]);;

let SELBERG_KAPPA_BOUND = prove
 (`!t p Js (B:num->num->int) B0 J.
        prime p /\ 2 <= t /\ lf_fam_ok p t Js B /\ J SUBSET Js /\
        FINITE J /\ 2 <= CARD J
        ==> &0 <= selberg_kappa t p B B0 J /\
            selberg_kappa t p B B0 J <= &p pow (CARD J - 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p pow t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 0 < p`];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[selberg_kappa] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; REAL_POS];
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; LF_NCOUNT_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a b. a IN J /\ b IN J /\ ~(a:num = b)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(?a. s = {a}) /\ ~(s = {}) ==>
                           ?a b. a IN s /\ b IN s /\ ~(a:num = b)`) THEN
    CONJ_TAC THENL
     [STRIP_TAC THEN UNDISCH_TAC `2 <= CARD(J:num->bool)` THEN
      ASM_REWRITE_TAC[CARD_SING] THEN ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `2 <= CARD(J:num->bool)` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_ncount {i | i < t} p (B:num->num->int) B0 J <=
                &p pow (t - 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lf_ncount {i | i < t} p (B:num->num->int) B0 {a,b}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LF_NCOUNT_MONO THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `lf_fam_ok p t Js (B:num->num->int)` THEN
  REWRITE_TAC[lf_fam_ok] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[LF_NCOUNT_PAIR; FINITE_NUMSEG_LT; CARD_NUMSEG_LT;
      REAL_LE_REFL];
      ONCE_REWRITE_TAC[SET_RULE `{a:num,b} = {b,a}`] THEN
      ASM_SIMP_TAC[LF_NCOUNT_PAIR; FINITE_NUMSEG_LT; CARD_NUMSEG_LT;
                   REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[selberg_kappa; real_div; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&p pow CARD(J:num->bool) * &p pow (t - 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let LALPHA_ZERO = prove
 (`!t p Js (B:num->num->int) B0 J.
        prime p /\ 2 <= t /\ lf_fam_ok p t Js B /\ J SUBSET Js /\
        FINITE J /\ ~(J = {}) /\ CARD J <= 2
        ==> selberg_smob (selberg_kappa t p B B0) J = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELBERG_SMOB_ZERO THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELBERG_KAPPA_SMALL THEN
  EXISTS_TAC `Js:num->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[FINITE_SUBSET];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(J:num->bool)` THEN
    ASM_SIMP_TAC[CARD_SUBSET]]);;

let LALPHA_BOUND = prove
 (`!t p Js (B:num->num->int) B0 J.
        prime p /\ 2 <= t /\ lf_fam_ok p t Js B /\ J SUBSET Js /\
        FINITE J /\ 2 <= CARD J
        ==> abs(selberg_smob (selberg_kappa t p B B0) J) <=
            &2 pow CARD J * &p pow (CARD J - 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELBERG_SMOB_BOUND THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `J':num->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(J':num->bool) /\ J' SUBSET Js /\
                CARD J' <= CARD(J:num->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; SUBSET_TRANS; CARD_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &p pow (CARD(J:num->bool) - 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  ASM_CASES_TAC `CARD(J':num->bool) <= 2` THENL
   [MP_TAC(SPECL [`t:num`; `p:num`; `Js:num->bool`; `B:num->num->int`;
                  `B0:num->int`; `J':num->bool`] SELBERG_KAPPA_SMALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:num`; `p:num`; `Js:num->bool`; `B:num->num->int`;
                `B0:num->int`; `J':num->bool`] SELBERG_KAPPA_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&p pow (CARD(J':num->bool) - 2)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The assignment expansion.                                                 *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_SWAP = prove
 (`!(f:A->B->real) s t.
        FINITE s /\ FINITE t
        ==> product s (\i. product t (f i)) =
            product t (\j. product s (\i. f i j))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; PRODUCT_ONE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[]);;

let DENS_FACTOR = prove
 (`!t P Js (B:num->num->int) B0 (Dt:num->num->bool).
        FINITE P /\ (!p. p IN P ==> prime p) /\ FINITE Js /\
        (!j. j IN Js ==> Dt j SUBSET P)
        ==> product P (\p. lf_ncount {i | i < t} p B B0
                             {j | j IN Js /\ p IN Dt j} / &p pow t) =
            product P (\p. selberg_kappa t p B B0 {j | j IN Js /\ p IN Dt j}) *
            product Js (\j. product (Dt j) (\p. inv(&p)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!p. p IN P
        ==> lf_ncount {i | i < t} p (B:num->num->int) B0
                   {j | j IN Js /\ p IN (Dt:num->num->bool) j} / &p pow t =
            selberg_kappa t p B B0 {j | j IN Js /\ p IN Dt j} *
            product Js (\j. if p IN Dt j then inv(&p) else &1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_kappa] THEN
    SUBGOAL_THEN `~(&p = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ABBREV_TAC `Jp = {j | j IN Js /\ p IN (Dt:num->num->bool) j}` THEN
    SUBGOAL_THEN `product Js (\j. if p IN (Dt:num->num->bool) j
                                  then inv(&p) else &1) =
                  inv(&p) pow CARD(Jp:num->bool)`
    SUBST1_TAC THENL
     [EXPAND_TAC "Jp" THEN REWRITE_TAC[GSYM PRODUCT_RESTRICT_SET] THEN
      ASM_SIMP_TAC[PRODUCT_CONST; FINITE_RESTRICT];
      ALL_TAC] THEN
    ABBREV_TAC `c = lf_ncount {i | i < t} p (B:num->num->int) B0 Jp` THEN
    ABBREV_TAC `n = CARD(Jp:num->bool)` THEN
    REWRITE_TAC[REAL_POW_INV] THEN
    SUBGOAL_THEN `~(&p pow n = &0) /\ ~(&p pow t = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_NZ]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product P (\p. selberg_kappa t p (B:num->num->int) B0
                                {j | j IN Js /\ p IN (Dt:num->num->bool) j} *
                              product Js (\j. if p IN Dt j then inv(&p)
                                              else &1))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_MUL] THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM PRODUCT_RESTRICT_SET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM SET_TAC[]);;

let KAPPA_EXPAND = prove
 (`!t P Js (B:num->num->int) B0 (Dt:num->num->bool).
        FINITE P /\ FINITE Js
        ==> product P (\p. selberg_kappa t p B B0 {j | j IN Js /\ p IN Dt j}) =
            sum (cartesian_product P (\p. {J | J SUBSET Js}))
                (\sg. product P
                   (\p. if sg p SUBSET {j | j IN Js /\ p IN Dt j}
                        then selberg_smob (selberg_kappa t p B B0)
                          (sg p) else &0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`P:num->bool`; `\p:num. {J:num->bool | J SUBSET Js}`;
    `\p J. if J SUBSET {j | j IN Js /\ p IN (Dt:num->num->bool) j}
           then selberg_smob
             (selberg_kappa t p (B:num->num->int) B0) J else &0`]
   PRODUCT_SUM_CARTESIAN) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE {j | j IN Js /\ p IN (Dt:num->num->bool) j}`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SELBERG_SMOB_INVERSION] THEN
  MATCH_MP_TAC SUM_POWERSET_RESTRICT THEN SET_TAC[]);;

let MS_EXPANSION = prove
 (`!t P D Js (B:num->num->int) B0.
     FINITE P /\ (!p. p IN P ==> prime p) /\ FINITE Js
     ==> sum (cartesian_product Js (\j. {A | A SUBSET P}))
           (\T1. sum (cartesian_product Js (\j. {A | A SUBSET P}))
             (\T2. product Js (\j. selberg_weight (\p. inv(&p)) D (T1 j) *
                                    selberg_weight (\p. inv(&p)) D (T2 j)) *
                   product P (\p. lf_ncount {i | i < t} p B B0
                                    {j | j IN Js /\ p IN T1 j UNION T2 j} /
                                  &p pow t))) =
         sum (cartesian_product P (\p. {J | J SUBSET Js}))
             (\sg. product P
                     (\p. selberg_smob (selberg_kappa t p B B0) (sg p)) *
                   product Js (\j. selberg_lfcsum (\p. inv(&p))
                                        (selberg_weight (\p. inv(&p)) D) P
                                        {p | p IN P /\ j IN sg p} {} {}))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `lmw = selberg_weight (\p:num. inv(&p)) D` THEN
  ABBREV_TAC `C = cartesian_product Js
    (\j:num. {A:num->bool | A SUBSET P})` THEN
  ABBREV_TAC `S = cartesian_product P
    (\p:num. {J:num->bool | J SUBSET Js})` THEN
  SUBGOAL_THEN `FINITE(C:(num->num->bool)->bool) /\
                FINITE(S:(num->num->bool)->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN EXPAND_TAC "S" THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_SIMP_TAC[FINITE_POWERSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!T1 T2. T1 IN C /\ T2 IN C
            ==> product Js (\j. (lmw:(num->bool)->real) (T1 j) * lmw (T2 j)) *
                product P (\p. lf_ncount {i | i < t} p (B:num->num->int) B0
                                 {j | j IN Js /\ p IN T1 j UNION T2 j} /
                               &p pow t) =
                sum S (\sg. product P
                              (\p. selberg_smob
                                     (selberg_kappa t p B B0) (sg p)) *
                            product Js (\j. lmw (T1 j) * lmw (T2 j) *
                                            product (T1 j UNION T2 j)
                                                    (\p. inv(&p)) *
                                            (if {p | p IN P /\ j IN sg p}
                                                SUBSET T1 j UNION T2 j
                                             then &1 else &0)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:num`; `P:num->bool`; `Js:num->bool`;
                   `B:num->num->int`; `B0:num->int`;
                   `\j:num. (T1:num->num->bool) j UNION T2 j`]
                     DENS_FACTOR) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(T1:num->num->bool) IN C`;
                             `(T2:num->num->bool) IN C`] THEN
      EXPAND_TAC "C" THEN REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN
      REWRITE_TAC[UNION_SUBSET] THEN MESON_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[KAPPA_EXPAND] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `sg:num->num->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `product P (\p. if sg p SUBSET {j | j IN Js /\ p IN T1 j UNION T2 j}
                     then selberg_smob (selberg_kappa t p (B:num->num->int) B0)
                       (sg p) else &0) =
      product P (\p. selberg_smob (selberg_kappa t p B B0) (sg p)) *
      product Js (\j. if {p | p IN P /\ j IN sg p} SUBSET
                         (T1:num->num->bool) j UNION T2 j then &1 else &0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC
       `product P
          (\p. selberg_smob (selberg_kappa t p (B:num->num->int) B0) (sg p) *
                       (if sg p SUBSET {j | j IN Js /\ p IN T1 j UNION T2 j}
                        then &1 else &0))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[PRODUCT_MUL] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[PRODUCT_INDICATOR] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `!p x. p IN P /\ x IN (sg:num->num->bool) p ==> x IN Js`
      ASSUME_TAC THENL
       [UNDISCH_TAC `(sg:num->num->bool) IN S` THEN EXPAND_TAC "S" THEN
        REWRITE_TAC[cartesian_product; IN_ELIM_THM; SUBSET] THEN MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_MUL] THEN
    ABBREV_TAC `A1 = product Js (\j:num. (lmw:(num->bool)->real)
                                      ((T1:num->num->bool) j))` THEN
    ABBREV_TAC `A2 = product Js (\j:num. (lmw:(num->bool)->real)
                                      ((T2:num->num->bool) j))` THEN
    ABBREV_TAC
      `A3 = product P
         (\p. selberg_smob (selberg_kappa t p (B:num->num->int) B0)
                                        ((sg:num->num->bool) p))` THEN
    ABBREV_TAC `A4 = product Js (\j:num. if {p | p IN P /\ j IN sg p} SUBSET
                                        (T1:num->num->bool) j UNION T2 j
                                     then &1 else &0)` THEN
    ABBREV_TAC `A5 = product Js
      (\j:num. product ((T1:num->num->bool) j UNION T2 j)
                                             (\p. inv(&p)))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum C (\T1. sum C (\T2. sum S
     (\sg. product P
             (\p. selberg_smob
                    (selberg_kappa t p (B:num->num->int) B0) (sg p)) *
           product Js (\j. (lmw:(num->bool)->real) (T1 j) * lmw (T2 j) *
                           product (T1 j UNION T2 j) (\p. inv(&p)) *
                           (if {p | p IN P /\ j IN sg p}
                               SUBSET T1 j UNION T2 j then &1 else
                                 &0)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `T1:num->num->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `T2:num->num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum C (\T1. sum S (\sg. sum C
     (\T2. product P
             (\p. selberg_smob
                    (selberg_kappa t p (B:num->num->int) B0) (sg p)) *
           product Js (\j. (lmw:(num->bool)->real) (T1 j) * lmw (T2 j) *
                           product (T1 j UNION T2 j) (\p. inv(&p)) *
                           (if {p | p IN P /\ j IN sg p}
                               SUBSET T1 j UNION T2 j then &1 else
                                 &0)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `T1:num->num->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `sg:num->num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!j. selberg_lfcsum (\p. inv(&p)) (lmw:(num->bool)->real) P
             {p | p IN P /\ j IN (sg:num->num->bool) p} {} {} =
        sum {A | A SUBSET P}
            (\A. sum {Bs | Bs SUBSET P}
                     (\Bs. lmw A * lmw Bs * product (A UNION Bs)
                       (\p. inv(&p)) *
                          (if {p | p IN P /\ j IN sg p} SUBSET A UNION Bs
                           then &1 else &0)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[selberg_lfcsum; EMPTY_SUBSET] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `Bs:num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`Js:num->bool`; `\j:num. {A:num->bool | A SUBSET P}`;
    `\j:num A:num->bool.
       sum {Bs | Bs SUBSET P}
           (\Bs. (lmw:(num->bool)->real) A * lmw Bs *
                product (A UNION Bs) (\p. inv(&p)) *
                (if {p | p IN P /\ j IN (sg:num->num->bool) p}
                  SUBSET A UNION Bs
                 then &1 else &0))`] PRODUCT_SUM_CARTESIAN) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `T1:num->num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`Js:num->bool`; `\j:num. {A:num->bool | A SUBSET P}`;
    `\j:num Bs:num->bool.
       (lmw:(num->bool)->real) ((T1:num->num->bool) j) * lmw Bs *
       product (T1 j UNION Bs) (\p. inv(&p)) *
       (if {p | p IN P /\ j IN (sg:num->num->bool) p} SUBSET T1 j UNION Bs
        then &1 else &0)`] PRODUCT_SUM_CARTESIAN) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The bound for the main term.                                              *)
(* ------------------------------------------------------------------------- *)

let BETA_PRIME_BOUND = prove
 (`!p. 3 <= p
       ==> &0 <= &4 * inv(&p) / (&1 - inv(&p)) +
                 (inv(&p) / (&1 - inv(&p))) pow 2 / inv(&p) /\
           &4 * inv(&p) / (&1 - inv(&p)) +
           (inv(&p) / (&1 - inv(&p))) pow 2 / inv(&p) <= &9 / &p`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 <= &p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 * inv(&p) / (&1 - inv(&p)) + (inv(&p) / (&1 - inv(&p))) pow 2
     / inv(&p) =
    (&5 * &p - &4) / (&p - &1) pow 2`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&3 <= &p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&p - &1) pow 2 /\ &0 < &p` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_LT_IMP_LE;
               REAL_ARITH `&3 <= p ==> &0 <= &5 * p - &4`] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = (a * c) * b`] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= (&p - &3) * (&4 * &p - &3)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let INV_PRIME_RANGE = prove
 (`!P. (!p. p IN P ==> prime p /\ 3 <= p)
       ==> !p. p IN P ==> &0 < inv(&p) /\ inv(&p) < &1`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 <= &p` MP_TAC THENL
   [ASM_MESON_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC]);;

let SELBERG_LFCSUM_MAIN = prove
 (`!P D. FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\
         selberg_family P D
         ==> selberg_lfcsum (\p. inv(&p)) (selberg_weight (\p. inv(&p)) D)
               P {} {} {} =
             inv(sum D (selberg_H (\p. inv(&p))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SELBERG_LFCSUM_EMPTY; selberg_tsum; EMPTY_SUBSET] THEN
  MATCH_MP_TAC SELBERG_MAIN_TERM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC INV_PRIME_RANGE THEN ASM_REWRITE_TAC[]);;

let SELBERG_LFCSUM_PRIME_BOUND = prove
 (`!P D Q. FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\
           selberg_family P D /\ Q SUBSET P
           ==> abs(selberg_lfcsum (\p. inv(&p))
                     (selberg_weight (\p. inv(&p)) D) P
                        Q {} {}) <=
               product Q (\p. &9 / &p) / sum D (selberg_H (\p. inv(&p)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\p:num. inv(&p)`; `P:num->bool`; `D:(num->bool)->bool`;
                 `Q:num->bool`; `{}:num->bool`;
                  `{}:num->bool`] SELBERG_LFCSUM_BOUND) THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET; SELBERG_EBOUND_EMPTY; UNION_EMPTY; DIFF_EMPTY;
                  REAL_MUL_LID] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN MATCH_MP_TAC INV_PRIME_RANGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&1 <= sum D (selberg_H (\p:num. inv(&p)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SELBERG_G_GE_1 THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INV_PRIME_RANGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC PRODUCT_LE THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC BETA_PRIME_BOUND THEN
  ASM SET_TAC[]);;

let PRODUCT_SUBSETS_POWER = prove
 (`!(c:num->real) P Js (sg:num->num->bool).
        FINITE P /\ FINITE Js /\ (!p. p IN P ==> sg p SUBSET Js)
        ==> product Js (\j. product {p | p IN P /\ j IN sg p} c) =
            product P (\p. c p pow CARD(sg p))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product Js (\j:num. product P (\p:num.
                if j IN (sg:num->num->bool) p then (c:num->real) p
                  else &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[PRODUCT_RESTRICT_SET];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM PRODUCT_RESTRICT_SET] THEN
  SUBGOAL_THEN `{j | j IN Js /\ j IN (sg:num->num->bool) p} = sg p`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PRODUCT_CONST THEN ASM_MESON_TAC[FINITE_SUBSET]);;

let SUM_SUBSETS_POW = prove
 (`!Js c. FINITE Js
          ==> sum {J:num->bool | J SUBSET Js} (\J. c pow CARD J) =
              (&1 + c) pow CARD Js`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\j:num. c:real`; `Js:num->bool`] PRODUCT_ADD_EXPAND) THEN
  ASM_SIMP_TAC[PRODUCT_CONST] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(GSYM PRODUCT_CONST) THEN ASM_MESON_TAC[FINITE_SUBSET]);;

let LOCAL_SUM_BOUND = prove
 (`!t p Js (B:num->num->int) B0.
        prime p /\ 3 <= p /\ 2 <= t /\ FINITE Js /\ lf_fam_ok p t Js B
        ==> sum {J | J SUBSET Js}
                (\J. abs(selberg_smob (selberg_kappa t p B B0) J) *
                     (&9 / &p) pow CARD J)
            <= &1 + &19 pow CARD Js / &p pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p /\ &3 <= &p` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {J | J SUBSET Js}
                  (\J:num->bool. (if J = {} then &1 else &0) +
                                 &18 pow CARD J / &p pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    X_GEN_TAC `J:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(J:num->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &18 pow CARD(J:num->bool) / &p pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
      ALL_TAC] THEN
    ASM_CASES_TAC `J:num->bool = {}` THENL
     [ASM_REWRITE_TAC[SELBERG_SMOB_EMPTY; CARD_CLAUSES; real_pow;
                      REAL_MUL_RID] THEN
      ASM_SIMP_TAC[SELBERG_KAPPA_EMPTY; REAL_ABS_NUM] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_LID] THEN
    ASM_CASES_TAC `CARD(J:num->bool) <= 2` THENL
     [MP_TAC(SPECL [`t:num`; `p:num`; `Js:num->bool`; `B:num->num->int`;
                    `B0:num->int`; `J:num->bool`] LALPHA_ZERO) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[REAL_ABS_0; REAL_MUL_LZERO];
      ALL_TAC] THEN
    MP_TAC(SPECL [`t:num`; `p:num`; `Js:num->bool`; `B:num->num->int`;
                  `B0:num->int`; `J:num->bool`] LALPHA_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 pow CARD(J:num->bool) * &p pow (CARD J - 2)) *
                (&9 / &p) pow CARD J` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `CARD(J:num->bool) = (CARD J - 2) + 2` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_DIV; ARITH_RULE `(n + 2) - 2 = n`] THEN
    REWRITE_TAC[REAL_ARITH `&18 = &2 * &9`; REAL_POW_MUL] THEN
    UNDISCH_TAC `&0 < &p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; FINITE_POWERSET] THEN
  REWRITE_TAC[SUM_DELTA; IN_ELIM_THM; EMPTY_SUBSET] THEN
  REWRITE_TAC[real_div; SUM_RMUL] THEN
  ASM_SIMP_TAC[SUM_SUBSETS_POW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let MS_BOUND = prove
 (`!t P D Js (B:num->num->int) B0.
     FINITE P /\ (!p. p IN P ==> prime p /\ 3 <= p) /\ FINITE Js /\
     selberg_family P D /\ 2 <= t /\ (!p. p IN P ==> lf_fam_ok p t Js B)
     ==> abs(sum (cartesian_product P (\p. {J | J SUBSET Js}))
                 (\sg. product P
                         (\p. selberg_smob (selberg_kappa t p B B0) (sg p)) *
                       product Js (\j. selberg_lfcsum (\p. inv(&p))
                                            (selberg_weight (\p. inv(&p)) D) P
                                            {p | p IN P /\ j IN sg p} {} {})) -
             inv(sum D (selberg_H (\p. inv(&p)))) pow CARD Js)
         <= inv(sum D (selberg_H (\p. inv(&p)))) pow CARD Js *
            (product P (\p. &1 + &19 pow CARD Js / &p pow 2) - &1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `iY = inv(sum D (selberg_H (\p:num. inv(&p))))` THEN
  ABBREV_TAC `S = cartesian_product P
    (\p:num. {J:num->bool | J SUBSET Js})` THEN
  ABBREV_TAC `F0 = \sg:num->num->bool.
                     product P (\p. selberg_smob
                       (selberg_kappa t p (B:num->num->int) B0) (sg p)) *
                     product Js (\j. selberg_lfcsum (\p. inv(&p))
                                     (selberg_weight (\p. inv(&p)) D) P
                                     {p | p IN P /\ j IN sg p} {} {})` THEN
  ABBREV_TAC `sg0 = \p:num. if p IN P then {}:num->bool else ARB` THEN
  SUBGOAL_THEN `FINITE(S:(num->num->bool)->bool) /\ sg0 IN S`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
      ASM_SIMP_TAC[FINITE_POWERSET];
      EXPAND_TAC "sg0" THEN
      REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
      MESON_TAC[EMPTY_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(F0:(num->num->bool)->real) sg0 = iY pow CARD(Js:num->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN EXPAND_TAC "sg0" THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
    REWRITE_TAC[EMPTY_GSPEC] THEN
    SUBGOAL_THEN
      `product P (\p. selberg_smob (selberg_kappa t p (B:num->num->int) B0)
                                     (if p IN P then {} else ARB)) = &1`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ_1 THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[SELBERG_SMOB_EMPTY] THEN
      MATCH_MP_TAC SELBERG_KAPPA_EMPTY THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SELBERG_LFCSUM_MAIN; PRODUCT_CONST; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!j:num. {p | p IN P /\ j IN (if p IN P then {} else ARB)} =
                          {}:num->bool` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      MESON_TAC[NOT_IN_EMPTY];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SELBERG_LFCSUM_MAIN; PRODUCT_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= iY` ASSUME_TAC THENL
   [EXPAND_TAC "iY" THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC SELBERG_G_GE_1 THEN
    EXISTS_TAC `P:num->bool` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INV_PRIME_RANGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
    `fp = \p J. abs(selberg_smob (selberg_kappa t p (B:num->num->int) B0) J) *
                         (&9 / &p) pow CARD(J:num->bool)` THEN
  SUBGOAL_THEN
   `!sg. sg IN S
         ==> abs((F0:(num->num->bool)->real) sg) <=
             iY pow CARD(Js:num->bool) * product P (\p. fp p (sg p))`
  ASSUME_TAC THENL
   [X_GEN_TAC `sg:num->num->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!p. p IN P ==> (sg:num->num->bool) p SUBSET Js`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(sg:num->num->bool) IN S` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "F0" THEN EXPAND_TAC "fp" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PRODUCT_MUL] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[GSYM PRODUCT_ABS] THEN
    ABBREV_TAC
      `A = product P
         (\x. abs (selberg_smob (selberg_kappa t x (B:num->num->int) B0)
                                                ((sg:num->num->bool) x)))` THEN
    SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `c * a * d:real = a * (c * d)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `product P (\p. (&9 / &p) pow CARD((sg:num->num->bool) p)) =
      product Js (\j. product {p | p IN P /\ j IN sg p} (\p. &9 / &p))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_SUBSETS_POWER THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM PRODUCT_CONST; GSYM PRODUCT_MUL] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`P:num->bool`; `D:(num->bool)->bool`;
                  `{p | p IN P /\ j IN (sg:num->num->bool) p}`]
                 SELBERG_LFCSUM_PRIME_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[real_div] THEN REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum S F0 - iY pow CARD(Js:num->bool) =
                sum (S DELETE sg0) (F0:(num->num->bool)->real)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[SUM_DELETE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (S DELETE sg0)
                  (\sg:num->num->bool. iY pow CARD(Js:num->bool) *
                                       product P (\p. fp p (sg p)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL; SUM_DELETE] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_POW_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `product P (\p. (fp:num->(num->bool)->real) p (sg0 p)) = &1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_1 THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    EXPAND_TAC "fp" THEN EXPAND_TAC "sg0" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SELBERG_SMOB_EMPTY; CARD_CLAUSES; real_pow; REAL_MUL_RID] THEN
    SUBGOAL_THEN `prime p` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SELBERG_KAPPA_EMPTY; REAL_ABS_NUM];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - &1 <= y - &1`) THEN
  EXPAND_TAC "S" THEN
  MP_TAC(ISPECL [`P:num->bool`; `\p:num. {J:num->bool | J SUBSET Js}`;
                 `fp:num->(num->bool)->real`] PRODUCT_SUM_CARTESIAN) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN EXPAND_TAC "fp" THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
    EXPAND_TAC "fp" THEN MATCH_MP_TAC LOCAL_SUM_BOUND THEN
    ASM_MESON_TAC[]]);;
