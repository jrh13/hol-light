(* ========================================================================= *)
(* Selberg's Lambda^2 sieve ([N] 7.2) in the set-of-primes form of sieve.ml. *)
(*                                                                           *)
(* SELBERG_SIEVE: for 0 < g p < 1 on a finite set s of positive integers     *)
(* and z > 1,                                                                *)
(*   sifted A a s <= X / G + sum_{t SUBSET s, prod t < z^2} 4^|t| |r_t|,     *)
(*   G = sum_{t SUBSET s, prod t < z} prod_{p IN t} g p / (1 - g p),         *)
(* with Selberg's optimal weights (main term exactly 1/G, |lambda| <= 1).    *)
(* ========================================================================= *)

needs "Sieve/sieve.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Subset-lattice identities.                                                *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_ADD_EXPAND = prove
 (`!(f:A->real) s.
        FINITE s
        ==> product s (\p. &1 + f p) = sum {k | k SUBSET s} (\k. product k f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES; SUBSET_EMPTY; SING_GSPEC; SUM_SING];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; SUM_POWERSET_INSERT] THEN
  SUBGOAL_THEN
   `sum {k | k SUBSET s} (\k. product ((a:A) INSERT k) f) =
    f a * sum {k | k SUBSET s} (\k. product k f)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `k:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(k:A->bool) /\ ~((a:A) IN k)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ASM_SIMP_TAC[PRODUCT_CLAUSES]];
    ABBREV_TAC `S = sum {k | k SUBSET s} (\k. product k (f:A->real))` THEN
    REAL_ARITH_TAC]);;

let PRODUCT_UNION_INTER = prove
 (`!(g:A->real) t1 t2.
        FINITE t1 /\ FINITE t2
        ==> product (t1 UNION t2) g * product (t1 INTER t2) g =
            product t1 g * product t2 g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t1 UNION t2 = t1 UNION (t2 DIFF t1) /\
                DISJOINT t1 (t2 DIFF t1:A->bool) /\
                t2 = (t1 INTER t2) UNION (t2 DIFF t1) /\
                DISJOINT (t1 INTER t2) (t2 DIFF t1:A->bool)`
  STRIP_ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o
    RATOR_CONV o RAND_CONV) [th]) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o
    RATOR_CONV o RAND_CONV) [th]) THEN
  ASM_SIMP_TAC[PRODUCT_UNION; FINITE_DIFF; FINITE_INTER] THEN
  REAL_ARITH_TAC);;

let SUM_SUBSETS_BETWEEN_SIGN = prove
 (`!k u:A->bool.
        FINITE u /\ k SUBSET u
        ==> sum {t | k SUBSET t /\ t SUBSET u} (\t. (-- &1) pow CARD t) =
            if u = k then (-- &1) pow CARD k else &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{t | (k:A->bool) SUBSET t /\ t SUBSET u} =
                IMAGE (\v. k UNION v) {v | v SUBSET u DIFF k}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `t:A->bool`
    THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `t DIFF k:A->bool` THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
  SUBGOAL_THEN `FINITE(k:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN {v | v SUBSET u DIFF k}
        ==> (-- &1) pow CARD(k UNION v:A->bool) =
            (-- &1) pow CARD k * (-- &1) pow CARD v`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CARD_UNION THEN
    ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF; SET_RULE
     `(v:A->bool) SUBSET u DIFF k ==> k INTER v = {}`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_EQ; SUM_LMUL] THEN
  ASM_SIMP_TAC[SUM_POWERSET_SIGN; FINITE_DIFF] THEN
  SUBGOAL_THEN `u DIFF k = {} <=> u = (k:A->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The Lambda^2 convolution lambda+(t) = sum_{t1 UNION t2 = t} lam t1 lam t2 *)
(* and the upper bound sifted <= sum_t lambda+(t) |A_t|.                     *)
(* ------------------------------------------------------------------------- *)

let selberg_conv = new_definition
 `selberg_conv (lam:(A->bool)->real) t =
    sum {t1 | t1 SUBSET t}
        (\t1. sum {t2 | t2 SUBSET t}
                  (\t2. if t1 UNION t2 = t then lam t1 * lam t2 else &0))`;;

let SELBERG_CONV_EXTEND = prove
 (`!(lam:(A->bool)->real) t u.
        FINITE u /\ t SUBSET u
        ==> selberg_conv lam t =
            sum {t1 | t1 SUBSET u}
                (\t1. sum {t2 | t2 SUBSET u}
                          (\t2. if t1 UNION t2 = t then lam t1 * lam t2
                                else &0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_conv] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {t1 | t1 SUBSET t}
        (\t1. sum {t2 | t2 SUBSET u}
                  (\t2. if t1 UNION t2 = t then (lam:(A->bool)->real) t1 *
                        lam t2 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t1:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x:A->bool. P x ==> Q x) ==> {x | P x} SUBSET {x | Q x}`) THEN
      ASM_MESON_TAC[SUBSET_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t2:A->bool` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN UNDISCH_TAC `~(t2 SUBSET (t:A->bool))` THEN
    UNDISCH_TAC `t1 UNION t2 = (t:A->bool)` THEN SET_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x:A->bool. P x ==> Q x) ==> {x | P x} SUBSET {x | Q x}`) THEN
      ASM_MESON_TAC[SUBSET_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t1:A->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t2:A->bool` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN UNDISCH_TAC `~(t1 SUBSET (t:A->bool))` THEN
    UNDISCH_TAC `t1 UNION t2 = (t:A->bool)` THEN SET_TAC[]]);;

let SUM_SELBERG_CONV_GEN = prove
 (`!(lam:(A->bool)->real) c u.
        FINITE u
        ==> sum {t | t SUBSET u} (\t. selberg_conv lam t * c t) =
            sum {t1 | t1 SUBSET u}
                (\t1. sum {t2 | t2 SUBSET u}
                          (\t2. lam t1 * lam t2 * c(t1 UNION t2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {t:A->bool | t SUBSET u}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {t | t SUBSET u}
        (\t. sum {t1 | t1 SUBSET u}
                 (\t1. sum {t2 | t2 SUBSET u}
                           (\t2. if t1 UNION t2 = t
                                 then (lam:(A->bool)->real) t1 * lam t2 * c t
                                 else &0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SELBERG_CONV_EXTEND] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `t1:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t2:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t1:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t2:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV o RATOR_CONV o
                   RATOR_CONV o RAND_CONV) [EQ_SYM_EQ] THEN
  SUBGOAL_THEN
   `!t:A->bool. (if t = t1 UNION t2 then lam t1 * lam t2 * c t else &0) =
                (if t = t1 UNION t2 then (lam:(A->bool)->real) t1 * lam t2 *
                    (c:(A->bool)->real)(t1 UNION t2) else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN ASM_REWRITE_TAC[UNION_SUBSET]);;

let SUM_SELBERG_CONV = prove
 (`!(lam:(A->bool)->real) u.
        FINITE u
        ==> sum {t | t SUBSET u} (selberg_conv lam) =
            (sum {t | t SUBSET u} lam) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lam:(A->bool)->real`; `\t:A->bool. &1`; `u:A->bool`]
         SUM_SELBERG_CONV_GEN) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_POW_2; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[SUM_LMUL]);;

let SELBERG_CONV_EMPTY = prove
 (`!lam:(A->bool)->real. selberg_conv lam {} = lam {} pow 2`,
  REWRITE_TAC[selberg_conv; SUBSET_EMPTY; SING_GSPEC; SUM_SING; UNION_EMPTY;
              REAL_POW_2]);;

let SELBERG_LAMBDA_UPPER = prove
 (`!A a s lam.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\ FINITE s /\ lam {} = &1
        ==> sifted A a s <=
            sum {t | t SUBSET s} (\t. selberg_conv lam t * sieve_count A a t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIEVE_UPPER_GENERAL THEN
  ASM_REWRITE_TAC[SELBERG_CONV_EMPTY] THEN
  CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(u:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[ETA_AX; SUM_SELBERG_CONV; REAL_LE_POW_2]);;


(* ------------------------------------------------------------------------- *)
(* Diagonalisation of the quadratic form ([N] (7.3)-(7.4)).                  *)
(* ------------------------------------------------------------------------- *)

let SELBERG_DIAG = prove
 (`!(g:A->real) (lam:(A->bool)->real) s.
        FINITE s /\ (!p. p IN s ==> &0 < g p)
        ==> sum {t1 | t1 SUBSET s}
                (\t1. sum {t2 | t2 SUBSET s}
                          (\t2. lam t1 * lam t2 * product (t1 UNION t2) g)) =
            sum {k | k SUBSET s}
                (\k. product k (\p. inv(g p) - &1) *
                     (sum {t | t SUBSET s /\ k SUBSET t}
                          (\t. product t g * lam t)) pow 2)`,
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
                                 (if k SUBSET t1 then product t1 g * lam t1
                                  else &0) *
                                 (if k SUBSET t2 then product t2 (g:A->real) *
                                    (lam:(A->bool)->real) t2 else &0))))` THEN
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
                                 (if k SUBSET t1 then product t1 g * lam t1
                                  else &0) *
                                 (if k SUBSET t2 then product t2 (g:A->real) *
                                    (lam:(A->bool)->real) t2 else &0))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_POW_2; SUM_RESTRICT_SET] THEN
  REWRITE_TAC[SUM_LMUL; SUM_RMUL; GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `{t:A->bool | t SUBSET s /\ k SUBSET t} =
                {t | t IN {t | t SUBSET s} /\ k SUBSET t}` SUBST1_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[SUM_RESTRICT_SET]);;


(* ------------------------------------------------------------------------- *)
(* Selberg's weights for a downward closed family D of subsets of s.         *)
(* ------------------------------------------------------------------------- *)

let selberg_H = new_definition
 `selberg_H (g:A->real) t = product t (\p. g p / (&1 - g p))`;;

let selberg_family = new_definition
 `selberg_family (s:A->bool) D <=>
    D SUBSET {t | t SUBSET s} /\ {} IN D /\
    (!t u. t IN D /\ u SUBSET t ==> u IN D)`;;

let selberg_weight = new_definition
 `selberg_weight (g:A->real) D t =
    (-- &1) pow CARD t / product t g *
    sum {k | k IN D /\ t SUBSET k} (selberg_H g) / sum D (selberg_H g)`;;

let SELBERG_FAMILY_FINITE = prove
 (`!s D:(A->bool)->bool. FINITE s /\ selberg_family s D ==> FINITE D`,
  REWRITE_TAC[selberg_family] THEN MESON_TAC[FINITE_SUBSET; FINITE_POWERSET]);;

let SELBERG_H_POS = prove
 (`!g s t:A->bool.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\ t SUBSET s
        ==> &0 < selberg_H g t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_H] THEN
  MATCH_MP_TAC PRODUCT_POS_LT THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (g:A->real) p /\ g p < &1` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC);;

let SELBERG_G_GE_1 = prove
 (`!g s D:(A->bool)->bool.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D
        ==> &1 <= sum D (selberg_H g)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SELBERG_FAMILY_FINITE o
    CONJ (ASSUME `FINITE(s:A->bool)`)) THEN
  UNDISCH_TAC `selberg_family s (D:(A->bool)->bool)` THEN
  REWRITE_TAC[selberg_family] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {{}:A->bool} (selberg_H g)` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_SING; selberg_H; PRODUCT_CLAUSES; REAL_LE_REFL];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[SING_SUBSET; IN_DIFF] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SELBERG_H_POS THEN
    EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let SELBERG_WEIGHT_EMPTY = prove
 (`!g s D:(A->bool)->bool.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D
        ==> selberg_weight g D {} = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `D:(A->bool)->bool`]
         SELBERG_G_GE_1) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[selberg_weight; CARD_CLAUSES; real_pow; PRODUCT_CLAUSES;
              EMPTY_SUBSET] THEN
  REWRITE_TAC[SET_RULE `{k:A->bool | k IN D} = D`] THEN
  CONV_TAC REAL_FIELD);;

let SELBERG_WEIGHT_SUPPORT = prove
 (`!g s D t:A->bool.
        selberg_family s D /\ ~(t IN D) ==> selberg_weight g D t = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_weight] THEN
  SUBGOAL_THEN `{k:A->bool | k IN D /\ t SUBSET k} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[selberg_family];
    REWRITE_TAC[SUM_CLAUSES] THEN REAL_ARITH_TAC]);;

let SELBERG_WEIGHT_Y = prove
 (`!g s D k:A->bool.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ k SUBSET s
        ==> sum {t | t SUBSET s /\ k SUBSET t}
                (\t. product t g * selberg_weight g D t) =
            if k IN D then (-- &1) pow CARD k * selberg_H g k /
                           sum D (selberg_H g)
            else &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(D:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SELBERG_FAMILY_FINITE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `D:(A->bool)->bool`]
         SELBERG_G_GE_1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `G = sum D (selberg_H (g:A->real))` THEN
  SUBGOAL_THEN `FINITE {t:A->bool | t SUBSET s /\ k SUBSET t}` ASSUME_TAC
  THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {t:A->bool | t SUBSET s /\ k SUBSET t}
        (\t. sum D (\u. (-- &1) pow CARD t *
                        (if t SUBSET u then selberg_H (g:A->real) u
                         else &0))) / G` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `t:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[SUM_LMUL; GSYM SUM_RESTRICT_SET] THEN
    REWRITE_TAC[selberg_weight] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < product t (g:A->real)` MP_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LT THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN
    ABBREV_TAC `S = sum {x | x IN D /\ (t:A->bool) SUBSET x}
                        (selberg_H g)` THEN
    UNDISCH_TAC `&1 <= G` THEN REWRITE_TAC[real_div] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum D (\u. if u = k then (-- &1) pow CARD k *
                                       selberg_H (g:A->real) k
                                  else &0) / G` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:A->bool) SUBSET s` ASSUME_TAC THENL
     [ASM_MESON_TAC[selberg_family; SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * (if p then h else &0) =
                                 (if p then a else &0) * h`] THEN
    REWRITE_TAC[SUM_RMUL; GSYM SUM_RESTRICT_SET] THEN
    ASM_CASES_TAC `(k:A->bool) SUBSET u` THENL
     [SUBGOAL_THEN `{t:A->bool | t IN {t | t SUBSET s /\ k SUBSET t} /\
                                 t SUBSET u} =
                    {t | k SUBSET t /\ t SUBSET u}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`k:A->bool`; `u:A->bool`] SUM_SUBSETS_BETWEEN_SIGN) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO];
      SUBGOAL_THEN `{t:A->bool | t IN {t | t SUBSET s /\ k SUBSET t} /\
                                 t SUBSET u} = {}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[SUM_CLAUSES; REAL_MUL_LZERO] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    REWRITE_TAC[SUM_DELTA] THEN COND_CASES_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_ASSOC]]);;

let SELBERG_F_H = prove
 (`!g s k:A->bool.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\ k SUBSET s
        ==> product k (\p. inv(g p) - &1) * selberg_H g k = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_H] THEN
  SUBGOAL_THEN `FINITE(k:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN MATCH_MP_TAC PRODUCT_EQ_1 THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (g:A->real) p /\ g p < &1` MP_TAC THENL
   [ASM SET_TAC[]; CONV_TAC REAL_FIELD]);;

let SELBERG_MAIN_TERM = prove
 (`!g s D:(A->bool)->bool.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D
        ==> sum {t1 | t1 SUBSET s}
                (\t1. sum {t2 | t2 SUBSET s}
                          (\t2. selberg_weight g D t1 * selberg_weight g D t2 *
                                product (t1 UNION t2) g)) =
            inv(sum D (selberg_H g))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:A->real`; `selberg_weight (g:A->real) D`; `s:A->bool`]
         SELBERG_DIAG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `D:(A->bool)->bool`]
         SELBERG_G_GE_1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(D:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SELBERG_FAMILY_FINITE]; ALL_TAC] THEN
  ABBREV_TAC `G = sum D (selberg_H (g:A->real))` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {k:A->bool | k SUBSET s}
                  (\k. if k IN D then selberg_H g k / G pow 2 else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `D:(A->bool)->bool`;
                   `k:A->bool`] SELBERG_WEIGHT_Y) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_MUL_RZERO] THEN
    MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `k:A->bool`] SELBERG_F_H) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
    SUBGOAL_THEN `((-- &1) pow CARD(k:A->bool)) pow 2 = &1` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      REWRITE_TAC[GSYM REAL_POW_POW] THEN
      REWRITE_TAC[REAL_POW_2; REAL_ARITH `-- &1 * -- &1 = &1`; REAL_POW_ONE];
      ALL_TAC] THEN
    ABBREV_TAC `F1 = product k (\p. inv((g:A->real) p) - &1)` THEN
    ABBREV_TAC `H = selberg_H (g:A->real) k` THEN
    UNDISCH_TAC `&1 <= G` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{k:A->bool | k IN {k | k SUBSET s} /\ k IN D} = D`
  SUBST1_TAC THENL
   [UNDISCH_TAC `selberg_family s (D:(A->bool)->bool)` THEN
    REWRITE_TAC[selberg_family; EXTENSION; IN_ELIM_THM; SUBSET] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; SUM_RMUL] THEN ASM_REWRITE_TAC[ETA_AX] THEN
  UNDISCH_TAC `&1 <= G` THEN CONV_TAC REAL_FIELD);;

let SELBERG_H_SUM_SUBSETS = prove
 (`!g t:A->bool.
        FINITE t
        ==> sum {l | l SUBSET t} (selberg_H g) =
            product t (\p. &1 + g p / (&1 - g p))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PRODUCT_ADD_EXPAND] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[selberg_H]);;

let SELBERG_PAIR_INJECT = prove
 (`!g s D t:A->bool.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ t SUBSET s
        ==> sum {l | l SUBSET t} (selberg_H g) *
            sum {k | k IN D /\ t SUBSET k} (\k. selberg_H g (k DIFF t))
            <= sum D (selberg_H g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(D:(A->bool)->bool) /\ FINITE(t:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SELBERG_FAMILY_FINITE; FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:A->bool. k IN D ==> k SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[selberg_family; SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC `K = {k:A->bool | k IN D /\ t SUBSET k}` THEN
  SUBGOAL_THEN `FINITE(K:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `D:(A->bool)->bool` THEN ASM_REWRITE_TAC[SUBSET_RESTRICT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  SUBGOAL_THEN
   `!l k. l SUBSET t /\ k IN K
          ==> selberg_H (g:A->real) l * selberg_H g (k DIFF t) =
              selberg_H g (l UNION (k DIFF t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_H] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_UNION THEN
    SUBGOAL_THEN `(k:A->bool) SUBSET s` ASSUME_TAC THENL
     [UNDISCH_TAC `(k:A->bool) IN K` THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET];
      ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF];
      UNDISCH_TAC `(l:A->bool) SUBSET t` THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {l:A->bool | l SUBSET t}
                  (\l. sum K (\k. selberg_H (g:A->real) (l UNION (k DIFF t))))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `l:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A->bool` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {l:A->bool | l SUBSET t}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_PRODUCT o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC `PR = {l,j | l IN {l:A->bool | l SUBSET t} /\
                         (j:A->bool) IN K}` THEN
  SUBGOAL_THEN
   `!x y. x IN PR /\ y IN PR /\
          (\(l,k). l UNION (k DIFF t:A->bool)) x =
          (\(l,k). l UNION (k DIFF t)) y
          ==> x = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "PR" THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`l1:A->bool`; `k1:A->bool`; `l2:A->bool`;
                         `k2:A->bool`] THEN
    STRIP_TAC THEN UNDISCH_TAC `(l1:A->bool) SUBSET t` THEN
    UNDISCH_TAC `(l2:A->bool) SUBSET t` THEN
    UNDISCH_TAC `(t:A->bool) SUBSET k1` THEN
    UNDISCH_TAC `(t:A->bool) SUBSET k2` THEN
    UNDISCH_TAC `l1 UNION (k1 DIFF t) = l2 UNION (k2 DIFF (t:A->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (\(l,k). l UNION (k DIFF t:A->bool)) PR)
                  (selberg_H (g:A->real))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "PR" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`l:A->bool`; `k:A->bool`] THEN STRIP_TAC THEN
    UNDISCH_TAC `selberg_family s (D:(A->bool)->bool)` THEN
    REWRITE_TAC[selberg_family] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `k:A->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(l:A->bool) SUBSET t` THEN
    UNDISCH_TAC `(t:A->bool) SUBSET k` THEN SET_TAC[];
    REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SELBERG_H_POS THEN
    EXISTS_TAC `s:A->bool` THEN ASM_SIMP_TAC[]]);;

let SELBERG_WEIGHT_BOUND = prove
 (`!g s D t:A->bool.
        FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\
        selberg_family s D /\ t SUBSET s
        ==> abs(selberg_weight g D t) <= &1`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(t:A->bool) IN D` THENL
   [ALL_TAC;
    ASM_MESON_TAC[SELBERG_WEIGHT_SUPPORT; REAL_ABS_0; REAL_POS]] THEN
  SUBGOAL_THEN `FINITE(D:(A->bool)->bool) /\ FINITE(t:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SELBERG_FAMILY_FINITE; FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `D:(A->bool)->bool`]
         SELBERG_G_GE_1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `G = sum D (selberg_H (g:A->real))` THEN
  SUBGOAL_THEN `!k:A->bool. k IN D ==> k SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[selberg_family; SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:A->bool. k SUBSET s ==> &0 < selberg_H g k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELBERG_H_POS THEN
    EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = {k:A->bool | k IN D /\ t SUBSET k}` THEN
  SUBGOAL_THEN `FINITE(K:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `D:(A->bool)->bool` THEN ASM_REWRITE_TAC[SUBSET_RESTRICT];
    ALL_TAC] THEN
  ABBREV_TAC `S' = sum K (\k. selberg_H (g:A->real) (k DIFF t))` THEN
  ABBREV_TAC `P = sum {l:A->bool | l SUBSET t} (selberg_H g)` THEN
  SUBGOAL_THEN `sum K (selberg_H (g:A->real)) = selberg_H g t * S'`
  ASSUME_TAC THENL
   [EXPAND_TAC "S'" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:A->bool` THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[selberg_H] THEN
    SUBGOAL_THEN `FINITE(k:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `k = t UNION (k DIFF t:A->bool)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PRODUCT_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `selberg_H (g:A->real) t = product t g * P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    SIMP_TAC[ASSUME `FINITE(t:A->bool)`; SELBERG_H_SUM_SUBSETS] THEN
    REWRITE_TAC[selberg_H] THEN
    SIMP_TAC[ASSUME `FINITE(t:A->bool)`; GSYM PRODUCT_MUL] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (g:A->real) p /\ g p < &1` MP_TAC THENL
     [ASM SET_TAC[]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `P * S' <= G` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "S'"; "K"; "G"] THEN
    MATCH_MP_TAC SELBERG_PAIR_INJECT THEN EXISTS_TAC `s:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < product t (g:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= S' /\ &0 <= P` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "S'" THEN MATCH_MP_TAC SUM_POS_LE THEN
      EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(SET_RULE `(k:A->bool) SUBSET s ==> k DIFF t SUBSET s`) THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "P" THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `selberg_weight g D t = (-- &1) pow CARD(t:A->bool) * (P * S') / G`
  SUBST1_TAC THENL
   [REWRITE_TAC[selberg_weight] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < product t (g:A->real)` THEN UNDISCH_TAC `&1 <= G` THEN
    ABBREV_TAC `pg = product t (g:A->real)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG;
              REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
  SUBGOAL_THEN `abs(P * S') = P * S' /\ abs G = G` (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= G ==> &0 < G`] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The sieve inequality.                                                     *)
(* ------------------------------------------------------------------------- *)

let NPRODUCT_UNION_LE = prove
 (`!t1 t2. FINITE t1 /\ FINITE t2 /\ (!p. p IN t1 UNION t2 ==> 1 <= p)
           ==> nproduct (t1 UNION t2) (\p. p) <=
               nproduct t1 (\p. p) * nproduct t2 (\p. p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t1 UNION t2 = t1 UNION (t2 DIFF t1:num->bool)` SUBST1_TAC
  THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[NPRODUCT_UNION; FINITE_DIFF;
               SET_RULE `DISJOINT t1 (t2 DIFF t1:num->bool)`] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; ASM SET_TAC[]]);;

let SELBERG_CONV_BOUND = prove
 (`!(lam:(A->bool)->real) t.
        FINITE t /\ (!u. u SUBSET t ==> abs(lam u) <= &1)
        ==> abs(selberg_conv lam t) <= &4 pow CARD t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_conv] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t1:A->bool | t1 SUBSET t}
                  (\t1. sum {t2:A->bool | t2 SUBSET t} (\t2. &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    X_GEN_TAC `t1:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    X_GEN_TAC `t2:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_0; REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC RAND_CONV
     [REAL_ARITH `&1 = &1 * &1`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[SUM_CONST; FINITE_POWERSET; CARD_POWERSET] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

let SELBERG_CONV_ZERO = prove
 (`!(lam:(A->bool)->real) D t.
        (!u. ~(u IN D) ==> lam u = &0) /\
        ~(?t1 t2. t1 IN D /\ t2 IN D /\ t1 UNION t2 = t)
        ==> selberg_conv lam t = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_conv] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `t1:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `t2:A->bool` THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(t1:A->bool) IN D` THEN ASM_SIMP_TAC[REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `(t2:A->bool) IN D` THEN ASM_SIMP_TAC[REAL_MUL_RZERO] THEN
  ASM_MESON_TAC[]);;

let SELBERG_SIEVE_GENERAL = prove
 (`!A a s X g D.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\ FINITE s /\
        (!p. p IN s ==> &0 < g p /\ g p < &1) /\ selberg_family s D
        ==> sifted A a s <=
            X / sum D (selberg_H g) +
            sum {t | t SUBSET s}
                (\t. abs(selberg_conv (selberg_weight g D) t) *
                     abs(sieve_count A a t - X * product t g))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `lam = selberg_weight (g:num->real) D` THEN
  MP_TAC(ISPECL [`A:num->bool`; `a:num->real`; `s:num->bool`;
                 `lam:(num->bool)->real`] SELBERG_LAMBDA_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN
    MATCH_MP_TAC SELBERG_WEIGHT_EMPTY THEN EXISTS_TAC `s:num->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  SUBGOAL_THEN
   `sum {t | t SUBSET s} (\t. selberg_conv lam t * sieve_count A a t) =
    X * sum {t | t SUBSET s} (\t. selberg_conv lam t * product t g) +
    sum {t | t SUBSET s}
        (\t. selberg_conv lam t * (sieve_count A a t - X * product t g))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD; FINITE_POWERSET] THEN
    MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(ISPECL [`lam:(num->bool)->real`; `\t:num->bool. product t g`;
                   `s:num->bool`] SUM_SELBERG_CONV_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "lam" THEN
    MP_TAC(ISPECL [`g:num->real`; `s:num->bool`; `D:(num->bool)->bool`]
           SELBERG_MAIN_TERM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC);;

let SELBERG_SIEVE = prove
 (`!A a s X g z.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\ FINITE s /\
        (!p. p IN s ==> 1 <= p) /\
        (!p. p IN s ==> &0 < g p /\ g p < &1) /\ &1 < z
        ==> sifted A a s <=
            X / sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < z}
                    (selberg_H g) +
            sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < z pow 2}
                (\t. &4 pow CARD t *
                     abs(sieve_count A a t - X * product t g))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = {t | t SUBSET s /\ &(nproduct t (\p. p)) < z}` THEN
  SUBGOAL_THEN `selberg_family s (D:(num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[selberg_family; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[EMPTY_SUBSET];
      REWRITE_TAC[NPRODUCT_CLAUSES] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`t:num->bool`; `u:num->bool`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&(nproduct t (\p:num. p))` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->bool`; `a:num->real`; `s:num->bool`; `X:real`;
                 `g:num->real`; `D:(num->bool)->bool`]
         SELBERG_SIEVE_GENERAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= m + y ==> x <= m + z`) THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN
   `sum {t | t SUBSET s}
        (\t. abs(selberg_conv (selberg_weight g D) t) *
             abs(sieve_count A a t - X * product t g)) =
    sum {t | t IN {t | t SUBSET s} /\ &(nproduct t (\p. p)) < z pow 2}
        (\t. abs(selberg_conv (selberg_weight g D) t) *
             abs(sieve_count A a t - X * product t g))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    CONJ_TAC THENL [REWRITE_TAC[SUBSET_RESTRICT]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t:num->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_ABS_ZERO] THEN DISJ1_TAC THEN
    MATCH_MP_TAC SELBERG_CONV_ZERO THEN EXISTS_TAC `D:(num->bool)->bool` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELBERG_WEIGHT_SUPPORT THEN
      EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t1:num->bool`; `t2:num->bool`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(t SUBSET s /\ &(nproduct t (\p:num. p)) < z pow 2)` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&(nproduct t1 (\p:num. p)) * &(nproduct t2 (\p:num. p))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC NPRODUCT_UNION_LE THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ASM_MESON_TAC[FINITE_SUBSET];
        ASM SET_TAC[]];
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{t:num->bool | t SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC SELBERG_CONV_BOUND THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELBERG_WEIGHT_BOUND THEN
  EXISTS_TAC `s:num->bool` THEN ASM_MESON_TAC[SUBSET_TRANS]);;
