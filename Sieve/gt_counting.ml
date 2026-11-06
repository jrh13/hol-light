(* ========================================================================= *)
(* The sparse counting lemma on the simplex (Conlon, Fox and Zhao, Theorem   *)
(* 2.17, for the hypergraph of k-term progressions).                         *)
(*                                                                           *)
(* lf_index k = {(j, W) | j < k, W SUBSET J - {j}} indexes the edges of the  *)
(* weak 2-blow-up, and the linear forms condition lf_cond k N nu eta says    *)
(* |E_{x0,x1} prod_{(j,W) IN S} nu j (zn_mix W x0 x1) - 1| <= eta for every  *)
(* S SUBSET lf_index k.                                                      *)
(* * LF_PRODUCT_EXPAND: |E prod_C (a + b nu) - prod_C (a + b)| <=            *)
(*   prod_C (|a| + |b|) eta, by PRODUCT_ADD_SUBSETS.                         *)
(* * STRONG_LINEAR_FORMS (CFZ Lemma 6.3): if 0 <= G0 j, G1 j <= 1 + nu j     *)
(*   for j /= j1, and A_l = zn_avg N j1 (prod_{j /= j1} G_l j) are averages  *)
(*   over coordinate j1, then                                                *)
(*     |E_x (nu j1 x - 1) A0 x A1 x|^(2^(k-1))                               *)
(*       <= (2^|lf_index k| (1 + eta))^(2^(k-1)) eta.                        *)
(*   Proof: majorised Cauchy-Schwarz steps (WCS_MAJ, SLF_STEP) on the        *)
(*   quantities zn_slfq d, d SUBSET J, by induction on |J - d| (SLF_INDUCT), *)
(*   and LF_PRODUCT_EXPAND at d = J (SLF_BASE).                              *)
(* * zn_hsys k N Sp nu g h eps eta: 0 <= g j <= nu j, 0 <= h j <= 1,         *)
(*   zn_hdisc <= eps, lf_cond with error eta, and nu j = 1 for j outside Sp. *)
(*   COUNTING_STEP (densification, CFZ Section 6.3): with the averages       *)
(*   zn_dens over coordinate j1 of the products of the other edges, the      *)
(*   count difference is at most                                             *)
(*     eps + sqrt((3 eta + sqrt(3 eta) + 2 c + 4 delta)(1 + eta)),           *)
(*   where c bounds the count differences of the systems with sparse set     *)
(*   Sp - {j1} and delta the strong linear forms (SLF_SQUARE, ZN_DENS_L2).   *)
(*   The induction hypothesis is applied to systems whose edge j1 carries    *)
(*   the same [0, 1] function on both sides (IH_APPLY), so the discrepancy   *)
(*   claim of CFZ is not needed.                                             *)
(* * GT_COUNTING_LEMMA: for every gamma > 0 there are eps, eta > 0 such that *)
(*   |zn_hcount g - zn_hcount h| <= gamma for every system zn_hsys k N Sp nu *)
(*   g h eps eta (induction on |Sp| from DENSE_COUNT; COUNT_PARAM,           *)
(*   SLF_PARAM).                                                             *)
(* ========================================================================= *)

needs "Sieve/gt_hypergraph.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The linear forms condition on the weak 2-blow-up.                         *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_ADD_SUBSETS = prove
 (`!(a:A->real) b s.
        FINITE s
        ==> product s (\x. a x + b x) =
            sum {t | t SUBSET s} (\t. product (s DIFF t) a * product t b)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES; SUBSET_EMPTY; SING_GSPEC; SUM_SING;
                EMPTY_DIFF] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; POWERSET_CLAUSES] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE] THEN ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  SUBGOAL_THEN
   `!t. t SUBSET s
        ==> product ((x:A) INSERT s DIFF t) a = a x * product (s DIFF t) a /\
            product ((x INSERT s) DIFF (x INSERT t)) a = product
              (s DIFF t) a /\
            product (x INSERT t) b = b x * product t b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN `(x:A) INSERT s DIFF t = x INSERT (s DIFF t)` SUBST1_TAC
      THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_DIFF; IN_DIFF];
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
      SUBGOAL_THEN `~((x:A) IN t)` ASSUME_TAC THENL [ASM SET_TAC[];
       ALL_TAC] THEN
      ASM_MESON_TAC[PRODUCT_CLAUSES; FINITE_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {t | t SUBSET s}
        (\t. product ((x:A) INSERT s DIFF t) a * product t b) =
    a x * sum {t | t SUBSET s} (\t. product (s DIFF t) a * product t b) /\
    sum {t | t SUBSET s}
        (\t. product ((x INSERT s) DIFF (x INSERT t)) a *
             product (x INSERT t) b) =
    b x * sum {t | t SUBSET s} (\t. product (s DIFF t) a * product t b)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_ACCEPT_TAC REAL_ADD_RDISTRIB]);;

let lf_index = new_definition
 `lf_index k =
  {(j:num,W:num->bool) | j < k /\ W SUBSET ({l | l < k} DELETE j)}`;;

let lf_cond = new_definition
 `lf_cond k N (nu:num->(num->num)->real) eta <=>
    !S. S SUBSET lf_index k
        ==> abs(zn_mean2 k N (\x0 x1. product S
                                  (\p. nu (FST p) (zn_mix (SND p) x0 x1))) -
                &1) <= eta`;;

let FINITE_LF_INDEX = prove
 (`!k. FINITE(lf_index k)`,
  GEN_TAC THEN REWRITE_TAC[lf_index] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{j:num | j < k} CROSS {W:num->bool | W SUBSET {l | l < k}}` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT; FINITE_POWERSET] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
              IN_ELIM_THM; IN_DELETE] THEN
  MESON_TAC[]);;

let ZN_MEAN2_SUM = prove
 (`!k N (Ix:A->bool) f.
        FINITE Ix
        ==> zn_mean2 k N (\x0 x1. sum Ix (\i. f i x0 x1)) =
            sum Ix (\i. zn_mean2 k N (f i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_mean2] THEN
  ASM_SIMP_TAC[FMEAN_SUM; FINITE_ZN_TUP] THEN REWRITE_TAC[ETA_AX]);;

let ZN_MEAN2_LMUL = prove
 (`!k N c (f:(num->num)->(num->num)->real).
        zn_mean2 k N (\x0 x1. c * f x0 x1) = c * zn_mean2 k N f`,
  REWRITE_TAC[zn_mean2; FMEAN_LMUL]);;

let LF_PRODUCT_EXPAND = prove
 (`!k N (nu:num->(num->num)->real) eta C (a:num#(num->bool)->real) b.
        lf_cond k N nu eta /\ C SUBSET lf_index k
        ==> abs(zn_mean2 k N (\x0 x1. product C
                         (\p. a p + b p * nu (FST p) (zn_mix (SND p) x0 x1))) -
                product C (\p. a p + b p))
            <= product C (\p. abs(a p) + abs(b p)) * eta`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(C:num#(num->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_LF_INDEX]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_ADD_SUBSETS] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ZN_MEAN2_SUM o lhand o rand o lhand
    o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `sum {t | t SUBSET C}
      (\t. zn_mean2 k N (\x0 x1. product (C DIFF t) (a:num#(num->bool)->real) *
                           product t (\p. b p * nu (FST p)
                                                   (zn_mix (SND p) x0 x1)))) =
    sum {t | t SUBSET C}
      (\t. (product (C DIFF t) a * product t b) *
           zn_mean2 k N
             (\x0 x1. product t (\p. (nu:num->(num->num)->real) (FST p)
                                           (zn_mix (SND p) x0 x1))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:num#(num->bool)->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(t:num#(num->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_MUL; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[ZN_MEAN2_LMUL; GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SUM_SUB; FINITE_POWERSET] THEN
  REWRITE_TAC[REAL_ARITH `!x y:real. x * y - x = x * (y - &1)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET C}
                (\t. abs(product (C DIFF t) (a:num#(num->bool)->real) *
                         product t b) * eta)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    X_GEN_TAC `t:num#(num->bool)->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [lf_cond]) THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `t:num#(num->bool)->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  BINOP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_ABS THEN
  ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* Strong linear forms.                                                      *)
(* ------------------------------------------------------------------------- *)

let ZN_MEAN2_LE = prove
 (`!k N (f:(num->num)->(num->num)->real) g.
        (!x0 x1. x0 IN zn_tup k N /\ x1 IN zn_tup k N ==> f x0 x1 <= g x0 x1)
        ==> zn_mean2 k N f <= zn_mean2 k N g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_mean2] THEN
  MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FMEAN_LE THEN
  ASM_SIMP_TAC[FINITE_ZN_TUP]);;

let ZN_MEAN2_POS = prove
 (`!k N (f:(num->num)->(num->num)->real).
        (!x0 x1. x0 IN zn_tup k N /\ x1 IN zn_tup k N ==> &0 <= f x0 x1)
        ==> &0 <= zn_mean2 k N f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `\x0:num->num x1:num->num. &0`;
                 `f:(num->num)->(num->num)->real`] ZN_MEAN2_LE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[zn_mean2; fmean; SUM_0; real_div; REAL_MUL_LZERO]);;

let WCS_MAJ = prove
 (`!k N j (A:(num->num)->(num->num)->real) Y Yb.
        j < k /\ 1 <= N /\
        (!x0 x1 r. A x0 (zn_upd x1 j r) = A x0 x1) /\
        (!x0 x1 r. Y (zn_upd x0 j r) x1 = Y x0 x1) /\
        (!x0 x1 r. Y x0 (zn_upd x1 j r) = Y x0 x1) /\
        (!x0 x1 r. Yb (zn_upd x0 j r) x1 = Yb x0 x1) /\
        (!x0 x1 r. Yb x0 (zn_upd x1 j r) = Yb x0 x1) /\
        (!x0 x1. x0 IN zn_tup k N /\ x1 IN zn_tup k N
                 ==> &0 <= Y x0 x1 /\ Y x0 x1 <= Yb x0 x1)
        ==> &0 <= zn_mean2 k N (\x0 x1. A x0 x1 * A (zn_mix {j} x0 x1) x1 *
                                  Yb x0 x1) /\
            zn_mean2 k N (\x0 x1. A x0 x1 * Y x0 x1) pow 2 <=
            zn_mean2 k N
              (\x0 x1. A x0 x1 * A (zn_mix {j} x0 x1) x1 * Yb x0 x1) *
            zn_mean2 k N Yb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `j:num`; `A:(num->num)->(num->num)->real`;
                `Yb:(num->num)->(num->num)->real`]
                  ZN_MEAN2_SQUARE_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `j:num`; `A:(num->num)->(num->num)->real`;
                `Y:(num->num)->(num->num)->real`] ZN_MEAN2_AVG_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `a = \x0 x1. fmean {r | r < N}
                    (\r. (A:(num->num)->(num->num)->real)
                      (zn_upd x0 j r) x1)` THEN
  SUBGOAL_THEN
   `!x0 x1. fmean {r | r < N}
              (\r. (A:(num->num)->(num->num)->real) (zn_upd x0 j r) x1) =
            a x0 x1`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ZN_MEAN2_POS THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `zn_mean2 k N (\x0 x1. (a:(num->num)->(num->num)->real) x0 x1 pow 2 *
                              Y x0 x1) * zn_mean2 k N Y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ZN_MEAN2_WEIGHTED_CS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ZN_MEAN2_POS THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
    MATCH_MP_TAC ZN_MEAN2_LE THEN ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_POW_2];
    MATCH_MP_TAC ZN_MEAN2_POS THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC ZN_MEAN2_LE THEN ASM_SIMP_TAC[]]);;

let PRODUCT_LF_INDEX = prove
 (`!k (f:num->(num->bool)->real).
        product {j | j < k}
          (\j. product {V | V SUBSET ({l | l < k} DELETE j)} (f j)) =
        product (lf_index k) (\p. f (FST p) (SND p))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`{j:num | j < k}`;
                 `\j:num. {V:num->bool | V SUBSET ({l | l < k} DELETE j)}`;
                 `f:num->(num->bool)->real`]
     (MATCH_MP ITERATE_ITERATE_PRODUCT MONOIDAL_REAL_MUL)) THEN
  REWRITE_TAC[GSYM product] THEN
  SIMP_TAC[FINITE_NUMSEG_LT; FINITE_POWERSET; FINITE_DELETE] THEN
  DISCH_THEN SUBST1_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[lf_index; EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM];
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]]);;

let LF_COND_POS = prove
 (`!k N (nu:num->(num->num)->real) eta. lf_cond k N nu eta ==> &0 <= eta`,
  REWRITE_TAC[lf_cond] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{}:num#(num->bool)->bool`) THEN
  REWRITE_TAC[EMPTY_SUBSET] THEN REAL_ARITH_TAC);;

let ZN_MIX_UPD_OUT = prove
 (`!V x0 x1 j r. ~(j IN V) ==> zn_mix V x0 (zn_upd x1 j r) = zn_mix V x0 x1`,
  REWRITE_TAC[zn_mix; zn_upd; FUN_EQ_THM] THEN MESON_TAC[]);;

let ZN_DEPON_MIX_UPD = prove
 (`!k j V x0 x1 r (g:(num->num)->real).
        zn_depon ({l | l < k} DELETE j) g
        ==> g(zn_mix V (zn_upd x0 j r) x1) = g(zn_mix V x0 x1) /\
            g(zn_mix V x0 (zn_upd x1 j r)) = g(zn_mix V x0 x1)`,
  REWRITE_TAC[zn_depon] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[zn_mix; zn_upd; IN_DELETE] THEN MESON_TAC[]);;

let zn_slfh = new_definition
 `zn_slfh j1 (nu:num->(num->num)->real) (G0:num->(num->num)->real) G1
       (d:num->bool) j (V:num->bool) =
    if j = j1 then (\x. nu j1 x - &1)
    else if j IN d then (\x. &1 + nu j x)
    else if j1 IN V then G1 j else G0 j`;;

let zn_slfq = new_definition
 `zn_slfq k N j1 (nu:num->(num->num)->real) G0 G1 d =
    zn_mean2 k N (\x0 x1. product {j | j < k}
       (\j. product {V | V SUBSET (d DELETE j)}
              (\V. zn_slfh j1 nu G0 G1 d j V (zn_mix V x0 x1))))`;;

let ZN_SLFH_INSERT = prove
 (`!j1 (nu:num->(num->num)->real) G0 G1 d j j0 V.
        ~(j = j0) /\ ~(j0 = j1)
        ==> zn_slfh j1 nu G0 G1 (j0 INSERT d) j V =
            zn_slfh j1 nu G0 G1 d j V /\
            zn_slfh j1 nu G0 G1 (j0 INSERT d) j (j0 INSERT V) =
            zn_slfh j1 nu G0 G1 d j V`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_slfh; IN_INSERT] THEN
  ASM_MESON_TAC[]);;

let SLF_STEP = prove
 (`!k N j1 j0 (nu:num->(num->num)->real) G0 G1 d eta.
        1 <= N /\ j0 < k /\ d SUBSET {l | l < k} /\ j1 IN d /\ ~(j0 IN d) /\
        lf_cond k N nu eta /\
        (!j. j < k ==> zn_depon ({l | l < k} DELETE j) (nu j) /\
                       zn_depon ({l | l < k} DELETE j) (G0 j) /\
                       zn_depon ({l | l < k} DELETE j) (G1 j)) /\
        (!j x. j < k /\ ~(j = j1) /\ x IN zn_tup k N
               ==> &0 <= G0 j x /\ G0 j x <= &1 + nu j x /\
                   &0 <= G1 j x /\ G1 j x <= &1 + nu j x)
        ==> zn_slfq k N j1 nu G0 G1 d pow 2 <=
            zn_slfq k N j1 nu G0 G1 (j0 INSERT d) *
            (&2 pow CARD(lf_index k) * (&1 + eta))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(j0:num = j1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(d:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. product {l:num | l < k} f =
        f j0 * product ({l | l < k} DELETE j0) f`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_DELETE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC
   `A = \x0 x1. product ({l:num | l < k} DELETE j0)
         (\j. product {V | V SUBSET (d DELETE j)}
                (\V. zn_slfh j1 (nu:num->(num->num)->real) G0 G1 d j V
                          (zn_mix V x0 x1)))` THEN
  ABBREV_TAC
   `Y = \x0 x1. product {V | V SUBSET d}
         (\V. (if j1 IN V then (G1:num->(num->num)->real) j0 else G0 j0)
              (zn_mix V x0 x1))` THEN
  ABBREV_TAC
   `Yb = \x0 x1. product {V | V SUBSET d}
          (\V. &1 + (nu:num->(num->num)->real) j0 (zn_mix V x0 x1))` THEN
  SUBGOAL_THEN
   `zn_slfq k N j1 nu G0 G1 d =
    zn_mean2 k N (\x0 x1. (A:(num->num)->(num->num)->real) x0 x1 * Y x0 x1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[zn_slfq] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`] THEN
    MAP_EVERY EXPAND_TAC ["A"; "Y"] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SET_RULE `!a:num s. ~(a IN s) ==> s DELETE a = s`] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[zn_slfh] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `zn_slfq k N j1 nu G0 G1 (j0 INSERT d) =
    zn_mean2 k N (\x0 x1. (A:(num->num)->(num->num)->real) x0 x1 *
                    A (zn_mix {j0} x0 x1) x1 * Yb x0 x1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[zn_slfq] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`] THEN
    MAP_EVERY EXPAND_TAC ["A"; "Yb"] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[DELETE_INSERT] THEN
    ASM_SIMP_TAC[SET_RULE `!a:num s. ~(a IN s) ==> s DELETE a = s`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    SIMP_TAC[GSYM PRODUCT_MUL; FINITE_DELETE; FINITE_NUMSEG_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    BINOP_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[zn_slfh; IN_INSERT] THEN
      ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_SUBSETS_INSERT o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[ZN_SLFH_INSERT; ZN_MIX_INSERT_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\V:num->bool. (j0:num,V)) {V | V SUBSET d} SUBSET lf_index k /\
    FINITE(IMAGE (\V:num->bool. (j0:num,V)) {V | V SUBSET d})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; lf_index; IN_ELIM_PAIR_THM;
                IN_ELIM_THM] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `zn_mean2 k N (Yb:(num->num)->(num->num)->real) <=
                &2 pow CARD(lf_index k) * (&1 + eta)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `N:num`; `nu:num->(num->num)->real`; `eta:real`;
                   `IMAGE (\V:num->bool. (j0:num,V)) {V | V SUBSET d}`;
                   `\p:num#(num->bool). &1`; `\p:num#(num->bool). &1`]
                  LF_PRODUCT_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[PRODUCT_CONST; REAL_ABS_NUM; REAL_MUL_LID;
             ASSUME `FINITE(IMAGE (\V:num->bool. (j0:num,V))
                                  {V | V SUBSET d})`;
             REAL_ARITH `&1 + &1 = &2`] THEN
    SUBGOAL_THEN
     `!x0 x1. product (IMAGE (\V:num->bool. (j0:num,V)) {V | V SUBSET d})
                (\p. &1 + (nu:num->(num->num)->real) (FST p)
                                                   (zn_mix (SND p) x0 x1)) =
              product {V | V SUBSET d} (\V. &1 + nu j0 (zn_mix V x0 x1))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_IMAGE o lhand o snd) THEN
      ANTS_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF];
      ALL_TAC] THEN
    EXPAND_TAC "Yb" THEN
    MATCH_MP_TAC(REAL_ARITH
     `a * (&1 + e) <= b ==> abs(x - a) <= a * e ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_LF_INDEX];
      MP_TAC(ISPECL [`k:num`; `N:num`; `nu:num->(num->num)->real`;
                     `eta:real`] LF_COND_POS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `zn_depon ({l | l < k} DELETE j0) ((nu:num->(num->num)->real) j0) /\
    zn_depon ({l | l < k} DELETE j0) ((G0:num->(num->num)->real) j0) /\
    zn_depon ({l | l < k} DELETE j0) ((G1:num->(num->num)->real) j0) /\
    (!x. x IN zn_tup k N
         ==> &0 <= G0 j0 x /\ G0 j0 x <= &1 + nu j0 x /\
             &0 <= G1 j0 x /\ G1 j0 x <= &1 + nu j0 x)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o
    MATCH_MP (ISPECL [`k:num`; `j0:num`] ZN_DEPON_MIX_UPD))) THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j0:num`;
                 `A:(num->num)->(num->num)->real`;
                 `Y:(num->num)->(num->num)->real`;
                 `Yb:(num->num)->(num->num)->real`] WCS_MAJ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["A"; "Y"; "Yb"] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `V:num->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC ZN_MIX_UPD_OUT THEN ASM SET_TAC[];
      MATCH_MP_TAC PRODUCT_EQ THEN ASM_REWRITE_TAC[COND_RATOR];
      MATCH_MP_TAC PRODUCT_EQ THEN ASM_REWRITE_TAC[COND_RATOR];
      MATCH_MP_TAC PRODUCT_EQ THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PRODUCT_EQ THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_POS_LE; MATCH_MP_TAC PRODUCT_LE] THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN
      X_GEN_TAC `V:num->bool` THEN DISCH_TAC THEN REWRITE_TAC[COND_RATOR] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[ZN_MIX_IN_TUP]];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `zn_mean2 k N (\x0 x1. (A:(num->num)->(num->num)->real) x0 x1 *
                              A (zn_mix {j0} x0 x1) x1 * Yb x0 x1) *
              zn_mean2 k N Yb` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL]);;

let SLF_BASE = prove
 (`!k N j1 (nu:num->(num->num)->real) G0 G1 eta.
        j1 < k /\ lf_cond k N nu eta
        ==> abs(zn_slfq k N j1 nu G0 G1 {l | l < k})
            <= &2 pow CARD(lf_index k) * eta`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `nu:num->(num->num)->real`; `eta:real`;
                 `lf_index k`;
                 `\p:num#(num->bool). if FST p = j1 then --(&1) else &1`;
                 `\p:num#(num->bool). &1`] LF_PRODUCT_EXPAND) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC(prove
   (`!x x' c d e eta:real. x = x' /\ c = &0 /\ d = e
                          ==> abs(x' - c) <= d * eta ==> abs x <= e * eta`,
    SIMP_TAC[REAL_SUB_RZERO])) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[zn_slfq] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`] THEN
    REWRITE_TAC[PRODUCT_LF_INDEX] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    REWRITE_TAC[FORALL_PAIR_THM; lf_index; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `V:num->bool`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[zn_slfh; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SIMP_TAC[PRODUCT_EQ_0; FINITE_LF_INDEX] THEN
    EXISTS_TAC `(j1:num,{}:num->bool)` THEN
    ASM_REWRITE_TAC[lf_index; IN_ELIM_PAIR_THM; EMPTY_SUBSET] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[COND_RAND; REAL_ABS_NEG; REAL_ABS_NUM; COND_ID] THEN
    SIMP_TAC[PRODUCT_CONST; FINITE_LF_INDEX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SLF_INDUCT = prove
 (`!k N j1 (nu:num->(num->num)->real) G0 G1 eta.
        1 <= N /\ j1 < k /\ lf_cond k N nu eta /\
        (!j. j < k ==> zn_depon ({l | l < k} DELETE j) (nu j) /\
                       zn_depon ({l | l < k} DELETE j) (G0 j) /\
                       zn_depon ({l | l < k} DELETE j) (G1 j)) /\
        (!j x. j < k /\ ~(j = j1) /\ x IN zn_tup k N
               ==> &0 <= G0 j x /\ G0 j x <= &1 + nu j x /\
                   &0 <= G1 j x /\ G1 j x <= &1 + nu j x)
        ==> !n d. d SUBSET {l | l < k} /\ j1 IN d /\
                  CARD({l | l < k} DIFF d) = n
                  ==> abs(zn_slfq k N j1 nu G0 G1 d) pow (2 EXP n) <=
                      (&2 pow CARD(lf_index k) * (&1 + eta)) pow (2 EXP n) *
                      eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = &2 pow CARD(lf_index k) * (&1 + eta)` THEN
  SUBGOAL_THEN `&0 <= eta` ASSUME_TAC THENL
   [ASM_MESON_TAC[LF_COND_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow CARD(lf_index k) <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    REWRITE_TAC[REAL_ARITH `a <= a * (&1 + e) <=> &0 <= a * e`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow CARD(lf_index k)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `d = {l:num | l < k}` SUBST_ALL_TAC THENL
     [MP_TAC(ISPEC `{l:num | l < k} DIFF d` CARD_EQ_0) THEN
      ASM_SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG_LT] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXP; REAL_POW_1] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow CARD(lf_index k) * eta` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SLF_BASE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?j0. j0 IN {l:num | l < k} DIFF d` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s:num->bool = {}) ==> ?x. x IN s`) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `CARD({l:num | l < k} DIFF d) = SUC n` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(j0:num) INSERT d`) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `{l:num | l < k} DIFF (j0 INSERT d) =
                  ({l | l < k} DIFF d) DELETE j0` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DIFF; FINITE_NUMSEG_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `j0:num`;
                 `nu:num->(num->num)->real`;
                 `G0:num->(num->num)->real`; `G1:num->(num->num)->real`;
                 `d:num->bool`; `eta:real`] SLF_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF; IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[EXP; GSYM REAL_POW_POW; REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `(abs(zn_slfq k N j1 nu G0 G1 (j0 INSERT d)) * B) pow (2 EXP n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `zn_slfq k N j1 nu G0 G1 (j0 INSERT d) * B` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((B:real) pow (2 EXP n) * eta) * B pow (2 EXP n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE];
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]);;

let zn_avg = new_definition
 `zn_avg N j (P:(num->num)->real) x =
  fmean {r | r < N} (\r. P(zn_upd x j r))`;;

let ZN_UPD_AT = prove
 (`!x j r. zn_upd x j r j = r`,
  REWRITE_TAC[zn_upd]);;

let ZN_MIX_EMPTY = prove
 (`!x0 x1. zn_mix {} x0 x1 = x0`,
  REWRITE_TAC[zn_mix; NOT_IN_EMPTY; ETA_AX]);;

let POWERSET_SING = prove
 (`!a:num. {V | V SUBSET {a}} = {{}, {a}}`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT;
   NOT_IN_EMPTY] THEN
  GEN_TAC THEN REWRITE_TAC[SUBSET; IN_SING; EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let ZN_AVG_UPD = prove
 (`!N j (P:(num->num)->real) x r. zn_avg N j P (zn_upd x j r) =
                                  zn_avg N j P x`,
  REWRITE_TAC[zn_avg; ZN_UPD_UPD]);;

let FMEAN_ZN_AVG = prove
 (`!k N j (F1:(num->num)->real) P.
        j < k /\ 1 <= N /\ (!x r. F1(zn_upd x j r) = F1 x)
        ==> fmean (zn_tup k N) (\x. F1 x * zn_avg N j P x) =
            fmean (zn_tup k N) (\x. F1 x * P x)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ZN_TUP_FMEAN_COORD o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[zn_avg; FMEAN_LMUL]);;

let ZN_MEAN2_AVG = prove
 (`!k N j (F1:(num->num)->real) P Q.
        j < k /\ 1 <= N /\ (!x r. F1(zn_upd x j r) = F1 x)
        ==> zn_mean2 k N (\x0 x1. F1 x0 * P x0 * Q(zn_mix {j} x0 x1)) =
            fmean (zn_tup k N) (\x. F1 x * zn_avg N j P x * zn_avg N j Q x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_mean2; ZN_MIX_SING] THEN
  SUBGOAL_THEN
   `!x0. fmean (zn_tup k N)
           (\x1. F1 x0 * P x0 * (Q:(num->num)->real)(zn_upd x0 j (x1 j))) =
         F1 x0 * P x0 * zn_avg N j Q x0`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC; FMEAN_LMUL] THEN AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ZN_TUP_FMEAN_COORD o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ZN_UPD_AT; GSYM zn_avg] THEN
    MATCH_MP_TAC FMEAN_CONST THEN
    ASM_SIMP_TAC[FINITE_ZN_TUP; ZN_TUP_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (F1:(num->num)->real) x * P x * zn_avg N j Q x =
        (F1 x * zn_avg N j Q x) * P x`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (F1:(num->num)->real) x * zn_avg N j P x * zn_avg N j Q x =
        (F1 x * zn_avg N j Q x) * zn_avg N j P x`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FMEAN_ZN_AVG THEN
  ASM_REWRITE_TAC[ZN_AVG_UPD]);;

let ZN_SLFQ_SING = prove
 (`!k N j1 (nu:num->(num->num)->real) G0 G1.
        j1 < k
        ==> zn_slfq k N j1 nu G0 G1 {j1} =
            zn_mean2 k N (\x0 x1. (nu j1 x0 - &1) *
                            product ({l | l < k} DELETE j1) (\j. G0 j x0) *
                            product ({l | l < k} DELETE j1)
                              (\j. G1 j (zn_mix {j1} x0 x1)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_slfq] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`] THEN
  SUBGOAL_THEN `FINITE {l:num | l < k} /\ j1 IN {l:num | l < k}`
  (fun th -> REWRITE_TAC[GSYM(MATCH_MP PRODUCT_DELETE th)]) THENL
   [ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `{a:num} DELETE a = {}`; SUBSET_EMPTY; SING_GSPEC;
              PRODUCT_SING; ZN_MIX_EMPTY] THEN
  REWRITE_TAC[zn_slfh] THEN
  SIMP_TAC[GSYM PRODUCT_MUL; FINITE_DELETE; FINITE_NUMSEG_LT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[SET_RULE `~(j:num = a) ==> {a} DELETE j = {a}`] THEN
  REWRITE_TAC[POWERSET_SING] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING;
           NOT_EMPTY_INSERT] THEN
  ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; ZN_MIX_EMPTY; REAL_MUL_RID]);;

let STRONG_LINEAR_FORMS = prove
 (`!k N j1 (nu:num->(num->num)->real) G0 G1 eta.
        1 <= N /\ j1 < k /\ lf_cond k N nu eta /\
        (!j. j < k ==> zn_depon ({l | l < k} DELETE j) (nu j) /\
                       zn_depon ({l | l < k} DELETE j) (G0 j) /\
                       zn_depon ({l | l < k} DELETE j) (G1 j)) /\
        (!j x. j < k /\ ~(j = j1) /\ x IN zn_tup k N
               ==> &0 <= G0 j x /\ G0 j x <= &1 + nu j x /\
                   &0 <= G1 j x /\ G1 j x <= &1 + nu j x)
        ==> abs(fmean (zn_tup k N)
                  (\x. (nu j1 x - &1) *
                       zn_avg N j1 (\y. product ({l | l < k} DELETE j1)
                                               (\j. G0 j y)) x *
                       zn_avg N j1 (\y. product ({l | l < k} DELETE j1)
                                               (\j. G1 j y)) x))
            pow (2 EXP (k - 1)) <=
            (&2 pow CARD(lf_index k) * (&1 + eta)) pow (2 EXP (k - 1)) * eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`;
                 `\x. (nu:num->(num->num)->real) j1 x - &1`;
                 `\y. product ({l | l < k} DELETE j1)
                        (\j. (G0:num->(num->num)->real) j y)`;
                 `\y. product ({l | l < k} DELETE j1)
                        (\j. (G1:num->(num->num)->real) j y)`]
                          ZN_MEAN2_AVG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC ZN_DEPON_UPD THEN
    EXISTS_TAC `{l:num | l < k} DELETE j1` THEN
    ASM_SIMP_TAC[IN_DELETE];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM ZN_SLFQ_SING] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `nu:num->(num->num)->real`;
                 `G0:num->(num->num)->real`; `G1:num->(num->num)->real`;
                 `eta:real`] SLF_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`k - 1`; `{j1:num}`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_SING; SING_SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC[SET_RULE `s DIFF {a:num} = s DELETE a`] THEN
  ASM_SIMP_TAC[CARD_DELETE; FINITE_NUMSEG_LT; IN_ELIM_THM; CARD_NUMSEG_LT]);;

(* ------------------------------------------------------------------------- *)
(* Densification.                                                            *)
(* ------------------------------------------------------------------------- *)

let ZN_HDISC_POS = prove
 (`!k N j (g:(num->num)->real) h eps. zn_hdisc k N j g h eps ==> &0 <= eps`,
  REWRITE_TAC[zn_hdisc] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i:num x:num->num. &0`) THEN
  REWRITE_TAC[zn_depon; REAL_LE_REFL; REAL_POS] THEN REAL_ARITH_TAC);;

let ZN_HDISC_MONO = prove
 (`!k N j (g:(num->num)->real) h e e'.
        zn_hdisc k N j g h e /\ e <= e' ==> zn_hdisc k N j g h e'`,
  REWRITE_TAC[zn_hdisc] THEN MESON_TAC[REAL_LE_TRANS]);;

let ZN_HDISC_REFL = prove
 (`!k N j (g:(num->num)->real) eps. &0 <= eps ==> zn_hdisc k N j g g eps`,
  SIMP_TAC[zn_hdisc; REAL_SUB_REFL; REAL_MUL_LZERO; fmean; SUM_0; real_div;
           REAL_ABS_NUM]);;

let LF_COND_MONO = prove
 (`!k N (nu:num->(num->num)->real) e e'.
        lf_cond k N nu e /\ e <= e' ==> lf_cond k N nu e'`,
  REWRITE_TAC[lf_cond] THEN MESON_TAC[REAL_LE_TRANS]);;

let LF_COND_ONE = prove
 (`!k N (nu:num->(num->num)->real) eta j1.
        lf_cond k N nu eta
        ==> lf_cond k N (\j. if j = j1 then (\x. &1) else nu j) eta`,
  REWRITE_TAC[lf_cond] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    SPEC `{p:num#(num->bool) | p IN S /\ ~(FST p = j1)}`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_RESTRICT_SET] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a = b ==> abs(a - &1) <= e ==> abs(b - &1) <= e`) THEN
  AP_TERM_TAC THEN ABS_TAC THEN ABS_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `p:num#(num->bool)` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FMEAN_WEIGHTED_CS = prove
 (`!(X:A->bool) a y.
        FINITE X /\ (!x. x IN X ==> &0 <= y x)
        ==> fmean X (\x. a x * y x) pow 2 <=
            fmean X (\x. a x pow 2 * y x) * fmean X y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean; real_div; REAL_POW_MUL] THEN
  MP_TAC(ISPECL [`X:A->bool`; `a:A->real`;
   `y:A->real`] SUM_WEIGHTED_CS_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_RING `((a:real) * c) * (b * c) = (a * b) * c pow 2`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let FMEAN_ABS_SQRT = prove
 (`!(X:A->bool) f.
        FINITE X /\ ~(X = {})
        ==> fmean X (\x. abs(f x)) <= sqrt(fmean X (\x. f x pow 2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  MP_TAC(ISPECL [`X:A->bool`; `\x:A. abs(f x)`; `\x:A. &1`]
         FMEAN_WEIGHTED_CS) THEN
  ASM_SIMP_TAC[REAL_MUL_RID; REAL_POS; FMEAN_CONST; REAL_POW2_ABS]);;

let ZN_HCOUNT_SPLIT = prove
 (`!k N j1 (G:num->(num->num)->real).
        j1 < k /\ 1 <= N /\ (!x r. G j1 (zn_upd x j1 r) = G j1 x)
        ==> zn_hcount k N G =
            fmean (zn_tup k N)
              (\x. G j1 x *
                   zn_avg N j1 (\y. product ({l | l < k} DELETE j1)
                                          (\j. G j y)) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_hcount] THEN
  SUBGOAL_THEN `FINITE {l:num | l < k} /\ j1 IN {l:num | l < k}`
  (fun th -> REWRITE_TAC[GSYM(MATCH_MP PRODUCT_DELETE th)]) THENL
   [ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`;
                 `(G:num->(num->num)->real) j1`;
                 `\y. product ({l | l < k} DELETE j1)
                        (\j. (G:num->(num->num)->real) j y)`]
                          FMEAN_ZN_AVG) THEN
  ASM_REWRITE_TAC[]);;

let zn_hsys = new_definition
 `zn_hsys k N Sp (nu:num->(num->num)->real) g h eps eta <=>
    1 <= N /\ Sp SUBSET {j | j < k} /\ lf_cond k N nu eta /\
    (!j. j < k
         ==> zn_depon ({l | l < k} DELETE j) (nu j) /\
             zn_depon ({l | l < k} DELETE j) (g j) /\
             zn_depon ({l | l < k} DELETE j) (h j) /\
             zn_hdisc k N j (g j) (h j) eps /\
             !x. x IN zn_tup k N
                 ==> &0 <= g j x /\ g j x <= nu j x /\
                     &0 <= h j x /\ h j x <= &1) /\
    (!j x. j < k /\ ~(j IN Sp) /\ x IN zn_tup k N ==> nu j x = &1)`;;

let zn_dens = new_definition
 `zn_dens k N j1 (G:num->(num->num)->real) =
    zn_avg N j1 (\y. product ({l | l < k} DELETE j1) (\j. G j y))`;;

let ZN_DEPON_MONO = prove
 (`!e e' (g:(num->num)->real). e SUBSET e' /\ zn_depon e g ==> zn_depon e' g`,
  REWRITE_TAC[zn_depon; SUBSET] THEN MESON_TAC[]);;

let ZN_DEPON_COMPOSE = prove
 (`!e (g:(num->num)->real) f. zn_depon e g ==> zn_depon e (\x. f(g x))`,
  REWRITE_TAC[zn_depon] THEN MESON_TAC[]);;

let ZN_DEPON_CONST = prove
 (`!e c. zn_depon e (\x:num->num. c)`,
  REWRITE_TAC[zn_depon]);;

let ZN_DEPON_PRODUCT = prove
 (`!e s (G:num->(num->num)->real).
        (!j. j IN s ==> zn_depon e (G j))
        ==> zn_depon e (\y. product s (\j. G j y))`,
  REWRITE_TAC[zn_depon] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN ASM_MESON_TAC[]);;

let ZN_DEPON_AVG = prove
 (`!k N j (P:(num->num)->real).
        zn_depon {l | l < k} P
        ==> zn_depon ({l | l < k} DELETE j) (zn_avg N j P)`,
  REWRITE_TAC[zn_depon; zn_avg] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[zn_upd] THEN ASM_MESON_TAC[IN_DELETE]);;

let ZN_AVG_MONO = prove
 (`!k N j (P:(num->num)->real) Q x.
        j < k /\ 1 <= N /\ x IN zn_tup k N /\
        (!y. y IN zn_tup k N ==> P y <= Q y)
        ==> zn_avg N j P x <= zn_avg N j Q x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_avg] THEN
  MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[ZN_UPD_IN_TUP]);;

let ZN_AVG_CONST = prove
 (`!N j c x. 1 <= N ==> zn_avg N j (\y. c) x = c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_avg] THEN
  MATCH_MP_TAC FMEAN_CONST THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `0` THEN ASM_ARITH_TAC);;

let ZN_AVG_BOUNDS = prove
 (`!k N j (P:(num->num)->real) a b x.
        j < k /\ 1 <= N /\ x IN zn_tup k N /\
        (!y. y IN zn_tup k N ==> a <= P y /\ P y <= b)
        ==> a <= zn_avg N j P x /\ zn_avg N j P x <= b`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `N:num`; `j:num`; `\y:num->num. (a:real)`;
                   `P:(num->num)->real`; `x:num->num`] ZN_AVG_MONO);
    MP_TAC(ISPECL [`k:num`; `N:num`; `j:num`; `P:(num->num)->real`;
                   `\y:num->num. (b:real)`; `x:num->num`] ZN_AVG_MONO)] THEN
  ASM_SIMP_TAC[ZN_AVG_CONST]);;

let ZN_DENS_UPD = prove
 (`!k N j1 (G:num->(num->num)->real) x r.
        zn_dens k N j1 G (zn_upd x j1 r) = zn_dens k N j1 G x`,
  REWRITE_TAC[zn_dens; ZN_AVG_UPD]);;

let ZN_DEPON_DENS = prove
 (`!k N j1 (G:num->(num->num)->real).
        (!j. j < k /\ ~(j = j1) ==> zn_depon ({l | l < k} DELETE j) (G j))
        ==> zn_depon ({l | l < k} DELETE j1) (zn_dens k N j1 G)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_dens; ETA_AX] THEN
  MATCH_MP_TAC ZN_DEPON_AVG THEN MATCH_MP_TAC ZN_DEPON_PRODUCT THEN
  REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ZN_DEPON_MONO THEN
  EXISTS_TAC `{l:num | l < k} DELETE j` THEN
  ASM_SIMP_TAC[DELETE_SUBSET]);;

let ZN_DENS_MONO = prove
 (`!k N j1 (G:num->(num->num)->real) H x.
        j1 < k /\ 1 <= N /\ x IN zn_tup k N /\
        (!j y. j < k /\ ~(j = j1) /\ y IN zn_tup k N
               ==> &0 <= G j y /\ G j y <= H j y)
        ==> &0 <= zn_dens k N j1 G x /\
            zn_dens k N j1 G x <= zn_dens k N j1 H x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[zn_dens] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `\y:num->num. &0`;
                   `\y. product ({l | l < k} DELETE j1)
                          (\j. (G:num->(num->num)->real) j y)`;
                   `x:num->num`] ZN_AVG_MONO) THEN
    ASM_SIMP_TAC[ZN_AVG_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_POS_LE;
    MATCH_MP_TAC ZN_AVG_MONO THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_LE] THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; IN_DELETE; IN_ELIM_THM]);;

let FMEAN_ZN_DENS = prove
 (`!k N j1 (F1:(num->num)->real) (G:num->(num->num)->real).
        j1 < k /\ 1 <= N /\ (!x r. F1(zn_upd x j1 r) = F1 x)
        ==> fmean (zn_tup k N) (\x. F1 x * zn_dens k N j1 G x) =
            fmean (zn_tup k N)
              (\x. F1 x * product ({l | l < k} DELETE j1) (\j. G j x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_dens] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `F1:(num->num)->real`;
                 `\y. product ({l | l < k} DELETE j1)
                        (\j. (G:num->(num->num)->real) j y)`]
                          FMEAN_ZN_AVG) THEN
  ASM_REWRITE_TAC[]);;

let ZN_HCOUNT_DENS = prove
 (`!k N j1 (G:num->(num->num)->real).
        j1 < k /\ 1 <= N /\ (!x r. G j1 (zn_upd x j1 r) = G j1 x)
        ==> zn_hcount k N G =
            fmean (zn_tup k N) (\x. G j1 x * zn_dens k N j1 G x)`,
  REWRITE_TAC[zn_dens] THEN MATCH_ACCEPT_TAC ZN_HCOUNT_SPLIT);;

let PRODUCT_IMAGE_PAIR = prove
 (`!s (W:num->bool) (f:num#(num->bool)->real).
        product (IMAGE (\j. (j,W)) s) f = product s (\j. f (j,W))`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]);;

let DISJOINT_IMAGE_PAIR = prove
 (`!s (a:B) b. ~(a = b)
               ==> DISJOINT (IMAGE (\j:A. (j,a)) s) (IMAGE (\j. (j,b)) s)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
  MESON_TAC[PAIR_EQ]);;

let LF_COND_ZN_DENS = prove
 (`!k N j1 (nu:num->(num->num)->real) eta.
        1 <= N /\ j1 < k /\ lf_cond k N nu eta
        ==> abs(fmean (zn_tup k N) (zn_dens k N j1 nu) - &1) <= eta /\
            abs(fmean (zn_tup k N)
                  (\x. zn_dens k N j1 nu x * zn_dens k N j1 nu x) -
                  &1) <= eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (\j. (j,{}:num->bool)) ({l | l < k} DELETE j1) SUBSET lf_index k /\
    IMAGE (\j. (j,{j1:num})) ({l | l < k} DELETE j1) SUBSET lf_index k`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; lf_index; IN_ELIM_PAIR_THM;
                IN_DELETE; IN_ELIM_THM] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `\x:num->num. &1`;
                   `nu:num->(num->num)->real`] FMEAN_ZN_DENS) THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `{}:num->bool`;
                   `\x. product ({l | l < k} DELETE j1)
                          (\j. (nu:num->(num->num)->real) j x)`]
                            ZN_MIX_MEAN2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o
      SPEC `IMAGE (\j. (j,{}:num->bool)) ({l:num | l < k} DELETE j1)` o
      REWRITE_RULE[lf_cond]) THEN
    ASM_REWRITE_TAC[PRODUCT_IMAGE_PAIR; FST; SND];
    ALL_TAC] THEN
  REWRITE_TAC[zn_dens] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `\x:num->num. &1`;
                 `\y. product ({l | l < k} DELETE j1)
                        (\j. (nu:num->(num->num)->real) j y)`;
                 `\y. product ({l | l < k} DELETE j1)
                        (\j. (nu:num->(num->num)->real) j y)`]
                          ZN_MEAN2_AVG) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o
    SPEC `IMAGE (\j. (j,{}:num->bool)) ({l:num | l < k} DELETE j1) UNION
          IMAGE (\j. (j,{j1:num})) ({l | l < k} DELETE j1)` o
    REWRITE_RULE[lf_cond]) THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a = b ==> abs(a - &1) <= e ==> abs(b - &1) <= e`) THEN
  AP_TERM_TAC THEN ABS_TAC THEN ABS_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_DELETE; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC DISJOINT_IMAGE_PAIR THEN REWRITE_TAC[NOT_EMPTY_INSERT];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PRODUCT_IMAGE_PAIR; FST; SND; ZN_MIX_EMPTY]);;

let TRUNC_POINT = prove
 (`!a b c. &0 <= a /\ a <= c /\ &0 <= b /\ b <= &1
           ==> abs((a - b) * (a - min a (&1))) <= (c - &1) pow 2 +
             abs(c - &1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a <= &1` THENL
   [ASM_SIMP_TAC[REAL_ARITH `a <= &1 ==> min a (&1) = a`; REAL_SUB_REFL;
                 REAL_MUL_RZERO; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2; REAL_ABS_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(a <= &1) ==> min a (&1) = &1`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * (c - &1)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= (a - b) * (a - &1)`
    (fun th -> REWRITE_TAC[MATCH_MP (REAL_ARITH `&0 <= x ==> abs x = x`) th])
    THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_RING `(c:real) * (c - &1) = (c - &1) pow 2 +
      (c - &1)`] THEN
    REAL_ARITH_TAC]);;

let FMEAN_SUB1_SQUARE = prove
 (`!(X:A->bool) f.
        FINITE X /\ ~(X = {})
        ==> fmean X (\x. (f x - &1) pow 2) =
            fmean X (\x. f x * f x) - &2 * fmean X f + &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:A. (f x - &1) pow 2 = (f x * f x - &2 * f x) + &1`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[FMEAN_ADD; FMEAN_SUB; FMEAN_LMUL; FMEAN_CONST; ETA_AX]);;

let NUP_L2 = prove
 (`!k N j1 (nu:num->(num->num)->real) eta.
        1 <= N /\ j1 < k /\ lf_cond k N nu eta
        ==> fmean (zn_tup k N) (\x. (zn_dens k N j1 nu x - &1) pow 2)
              <= &3 * eta`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `nu:num->(num->num)->real`;
                 `eta:real`] LF_COND_ZN_DENS) THEN
  ASM_SIMP_TAC[FMEAN_SUB1_SQUARE; FINITE_ZN_TUP; ZN_TUP_NONEMPTY] THEN
  REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC);;

let NUP_L1 = prove
 (`!k N j1 (nu:num->(num->num)->real) eta.
        1 <= N /\ j1 < k /\ lf_cond k N nu eta
        ==> fmean (zn_tup k N) (\x. abs(zn_dens k N j1 nu x - &1))
            <= sqrt(&3 * eta)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `sqrt(fmean (zn_tup k N) (\x. (zn_dens k N j1 nu x - &1) pow 2))` THEN
  ASM_SIMP_TAC[FMEAN_ABS_SQRT; FINITE_ZN_TUP; ZN_TUP_NONEMPTY] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC NUP_L2 THEN
  ASM_REWRITE_TAC[]);;

let LF_COND_SING_MEAN = prove
 (`!k N j1 (nu:num->(num->num)->real) eta.
        1 <= N /\ j1 < k /\ lf_cond k N nu eta
        ==> abs(fmean (zn_tup k N) (nu j1) - &1) <= eta`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{(j1:num,{}:num->bool)}` o
                REWRITE_RULE[lf_cond]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SING_SUBSET; lf_index; IN_ELIM_PAIR_THM; EMPTY_SUBSET] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_SING; ZN_MIX_MEAN2; ETA_AX]);;

let SLF_ZN_DENS = prove
 (`!k N j1 (nu:num->(num->num)->real) G0 G1 eta delta.
        1 <= N /\ j1 < k /\ lf_cond k N nu eta /\
        (!j. j < k ==> zn_depon ({l | l < k} DELETE j) (nu j) /\
                       zn_depon ({l | l < k} DELETE j) (G0 j) /\
                       zn_depon ({l | l < k} DELETE j) (G1 j)) /\
        (!j x. j < k /\ ~(j = j1) /\ x IN zn_tup k N
               ==> &0 <= G0 j x /\ G0 j x <= &1 + nu j x /\
                   &0 <= G1 j x /\ G1 j x <= &1 + nu j x) /\
        &0 <= delta /\
        (&2 pow CARD(lf_index k) * (&1 + eta)) pow (2 EXP (k - 1)) * eta <=
        delta pow (2 EXP (k - 1))
        ==> abs(fmean (zn_tup k N)
                  (\x. (nu j1 x - &1) * zn_dens k N j1 G0 x *
                       zn_dens k N j1 G1 x))
            <= delta`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN
  EXISTS_TAC `2 EXP (k - 1)` THEN ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 pow CARD(lf_index k) * (&1 + eta)) pow (2 EXP (k - 1))
    * eta` THEN
  ASM_REWRITE_TAC[zn_dens] THEN MATCH_MP_TAC STRONG_LINEAR_FORMS THEN
  ASM_REWRITE_TAC[]);;

let SLF_SQUARE = prove
 (`!k N Sp (nu:num->(num->num)->real) g h eps eta j1 delta.
        zn_hsys k N Sp nu g h eps eta /\ j1 IN Sp /\ &0 <= delta /\
        (&2 pow CARD(lf_index k) * (&1 + eta)) pow (2 EXP (k - 1)) * eta <=
        delta pow (2 EXP (k - 1))
        ==> abs(fmean (zn_tup k N)
                  (\x. (nu j1 x - &1) *
                       (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2))
            <= &4 * delta`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zn_hsys] THEN STRIP_TAC THEN
  SUBGOAL_THEN `j1:num < k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j x. j < k /\ x IN zn_tup k N
          ==> (&0 <= (g:num->(num->num)->real) j x /\
               g j x <= &1 + nu j x) /\
              (&0 <= (h:num->(num->num)->real) j x /\ h j x <= &1 + nu j x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= g /\ g <= n /\ &0 <= h /\ h <= &1
      ==> (&0 <= g /\ g <= &1 + n) /\ (&0 <= h /\ h <= &1 + n)`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!G0 G1. (G0 = g \/ G0 = h) /\ (G1 = g \/ G1 = h)
            ==> abs(fmean (zn_tup k N)
                      (\x. (nu j1 x - &1) * zn_dens k N j1 G0 x *
                           zn_dens k N j1 (G1:num->(num->num)->real) x))
                <= delta`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SLF_ZN_DENS THEN
    EXISTS_TAC `eta:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (nu j1 x - &1) * (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2 =
        ((nu j1 x - &1) * zn_dens k N j1 g x * zn_dens k N j1 g x -
         &2 * ((nu j1 x - &1) * zn_dens k N j1 g x * zn_dens k N j1 h x)) +
        (nu j1 x - &1) * zn_dens k N j1 h x *
        zn_dens k N j1 (h:num->(num->num)->real) x`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SIMP_TAC[FMEAN_ADD; FMEAN_SUB; FMEAN_LMUL; FINITE_ZN_TUP] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs a <= d /\ abs b <= d /\ abs c <= d
    ==> abs((a - &2 * b) + c) <= &4 * d`) THEN
  ASM_SIMP_TAC[]);;

let ZN_DENS_EQ = prove
 (`!k N j1 (G:num->(num->num)->real) H.
        (!j. j < k /\ ~(j = j1) ==> G j = H j)
        ==> zn_dens k N j1 G = zn_dens k N j1 H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_dens] THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[IN_DELETE; IN_ELIM_THM]);;

let IH_APPLY = prove
 (`!k N Sp (nu:num->(num->num)->real) g h eps eta j1 c (A:(num->num)->real).
        zn_hsys k N Sp nu g h eps eta /\ j1 IN Sp /\
        (!nu' g' h'. zn_hsys k N (Sp DELETE j1) nu' g' h' eps eta
                     ==> abs(zn_hcount k N g' - zn_hcount k N h') <= c) /\
        zn_depon ({l | l < k} DELETE j1) A /\
        (!x. x IN zn_tup k N ==> &0 <= A x /\ A x <= &1)
        ==> abs(fmean (zn_tup k N)
                  (\x. (zn_dens k N j1 g x - zn_dens k N j1 h x) * A x)) <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [zn_hsys]) THEN
  SUBGOAL_THEN `j1:num < k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eps` ASSUME_TAC THENL
   [MATCH_MP_TAC ZN_HDISC_POS THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `N:num`; `j1:num`;
                          `(g:num->(num->num)->real) j1`;
                          `(h:num->(num->num)->real) j1`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x r. (A:(num->num)->real) (zn_upd x j1 r) = A x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC ZN_DEPON_UPD THEN
    EXISTS_TAC `{l:num | l < k} DELETE j1` THEN ASM_REWRITE_TAC[IN_DELETE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\j. if j = j1 then (\x:num->num. &1) else (nu:num->(num->num)->real) j`;
    `\j:num. if j = j1 then (A:(num->num)->real) else g j`;
    `\j:num. if j = j1 then (A:(num->num)->real) else h j`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[zn_hsys] THEN ASM_SIMP_TAC[LF_COND_ONE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j:num = j1` THEN
      ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[ZN_DEPON_CONST; REAL_LE_REFL; ZN_HDISC_REFL];
        ASM_SIMP_TAC[]];
      REPEAT GEN_TAC THEN REWRITE_TAC[COND_RATOR; IN_DELETE] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> abs a <= c ==> abs b <= c`) THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`;
                 `\j:num. if j = j1 then (A:(num->num)->real) else g j`]
                ZN_HCOUNT_DENS) THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`;
                 `\j:num. if j = j1 then (A:(num->num)->real) else h j`]
                ZN_HCOUNT_DENS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `zn_dens k N j1 (\j:num. if j = j1 then (A:(num->num)->real) else g j) =
    zn_dens k N j1 g /\
    zn_dens k N j1 (\j:num. if j = j1 then (A:(num->num)->real) else h j) =
    zn_dens k N j1 h`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC ZN_DENS_EQ THEN SIMP_TAC[]; ALL_TAC] THEN
  SIMP_TAC[GSYM FMEAN_SUB; FINITE_ZN_TUP] THEN AP_TERM_TAC THEN ABS_TAC THEN
  REAL_ARITH_TAC);;

let ZN_DENS_ONE = prove
 (`!k N j1 x. 1 <= N ==> zn_dens k N j1 (\j:num x:num->num. &1) x = &1`,
  SIMP_TAC[zn_dens; PRODUCT_ONE; ZN_AVG_CONST]);;

let ZN_DENS_L2 = prove
 (`!k N Sp (nu:num->(num->num)->real) g h eps eta j1 c.
        zn_hsys k N Sp nu g h eps eta /\ j1 IN Sp /\
        (!nu' g' h'. zn_hsys k N (Sp DELETE j1) nu' g' h' eps eta
                     ==> abs(zn_hcount k N g' - zn_hcount k N h') <= c)
        ==> fmean (zn_tup k N)
              (\x. (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2)
            <= &3 * eta + sqrt(&3 * eta) + &2 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [zn_hsys]) THEN
  SUBGOAL_THEN `j1:num < k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN zn_tup k N
        ==> &0 <= zn_dens k N j1 g x /\
            zn_dens k N j1 g x <= zn_dens k N j1 nu x /\
            &0 <= zn_dens k N j1 h x /\ zn_dens k N j1 h x <= &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `g:num->(num->num)->real`;
                   `nu:num->(num->num)->real`; `x:num->num`] ZN_DENS_MONO) THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `h:num->(num->num)->real`;
                   `\j:num x:num->num. &1`; `x:num->num`] ZN_DENS_MONO) THEN
    ASM_SIMP_TAC[ZN_DENS_ONE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2 =
        (zn_dens k N j1 g x - zn_dens k N j1 h x) *
        (zn_dens k N j1 g x - min (zn_dens k N j1 g x) (&1)) +
        ((zn_dens k N j1 g x - zn_dens k N j1 h x) *
         min (zn_dens k N j1 g x) (&1) -
         (zn_dens k N j1 g x - zn_dens k N j1 h x) *
         zn_dens k N j1 (h:num->(num->num)->real) x)`
  (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SIMP_TAC[FMEAN_ADD; FMEAN_SUB; FINITE_ZN_TUP] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= p + q /\ abs b <= c /\ abs b' <= c
    ==> a + (b - b') <= p + q + &2 * c`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `fmean (zn_tup k N)
                  (\x. (zn_dens k N j1 nu x - &1) pow 2 +
                       abs(zn_dens k N j1 nu x - &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs a <= b ==> a <= b`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `fmean (zn_tup k N)
        (\x. abs((zn_dens k N j1 g x - zn_dens k N j1 h x) *
                 (zn_dens k N j1 g x - min (zn_dens k N j1 g x) (&1))))` THEN
      SIMP_TAC[FMEAN_ABS_LE; FINITE_ZN_TUP] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC TRUNC_POINT THEN ASM_SIMP_TAC[];
      SIMP_TAC[FMEAN_ADD; FINITE_ZN_TUP] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC NUP_L2; MATCH_MP_TAC NUP_L1] THEN
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`k:num`; `N:num`; `Sp:num->bool`;
                   `nu:num->(num->num)->real`; `g:num->(num->num)->real`;
                   `h:num->(num->num)->real`; `eps:real`; `eta:real`;
                   `j1:num`; `c:real`;
                   `\x. min (zn_dens k N j1 g x) (&1)`] IH_APPLY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`{l:num | l < k} DELETE j1`;
                     `zn_dens k N j1 (g:num->(num->num)->real)`;
                     `\y:real. min y (&1)`] ZN_DEPON_COMPOSE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC ZN_DEPON_DENS THEN ASM_SIMP_TAC[];
      GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:num->num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    MP_TAC(ISPECL [`k:num`; `N:num`; `Sp:num->bool`;
                   `nu:num->(num->num)->real`; `g:num->(num->num)->real`;
                   `h:num->(num->num)->real`; `eps:real`; `eta:real`;
                   `j1:num`; `c:real`;
                   `zn_dens k N j1 (h:num->(num->num)->real)`] IH_APPLY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC ZN_DEPON_DENS THEN ASM_SIMP_TAC[]]);;

let COUNTING_STEP = prove
 (`!k N Sp (nu:num->(num->num)->real) g h eps eta j1 c delta.
        zn_hsys k N Sp nu g h eps eta /\ j1 IN Sp /\
        (!nu' g' h'. zn_hsys k N (Sp DELETE j1) nu' g' h' eps eta
                     ==> abs(zn_hcount k N g' - zn_hcount k N h') <= c) /\
        &0 <= delta /\
        (&2 pow CARD(lf_index k) * (&1 + eta)) pow (2 EXP (k - 1)) * eta <=
        delta pow (2 EXP (k - 1))
        ==> abs(zn_hcount k N g - zn_hcount k N h) <=
            eps + sqrt((&3 * eta + sqrt(&3 * eta) + &2 * c + &4 * delta) *
                       (&1 + eta))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [zn_hsys]) THEN
  SUBGOAL_THEN `j1:num < k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x r. (g:num->(num->num)->real) j1 (zn_upd x j1 r) = g j1 x /\
          (h:num->(num->num)->real) j1 (zn_upd x j1 r) = h j1 x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC ZN_DEPON_UPD THEN
    EXISTS_TAC `{l:num | l < k} DELETE j1` THEN ASM_SIMP_TAC[IN_DELETE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `g:num->(num->num)->real`]
                ZN_HCOUNT_DENS) THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `h:num->(num->num)->real`]
                ZN_HCOUNT_DENS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `fmean (zn_tup k N) (\x. g j1 x * zn_dens k N j1 g x) -
    fmean (zn_tup k N) (\x. h j1 x * zn_dens k N j1 h x) =
    fmean (zn_tup k N)
      (\x. (zn_dens k N j1 g x - zn_dens k N j1 h x) * g j1 x) +
    fmean (zn_tup k N)
      (\x. (g j1 x - h j1 x) * zn_dens k N j1 (h:num->(num->num)->real) x)`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM FMEAN_SUB; GSYM FMEAN_ADD; FINITE_ZN_TUP] THEN
    AP_TERM_TAC THEN ABS_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs a <= s /\ abs b <= e ==> abs(a + b) <= e + s`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`;
                   `\x. (g:num->(num->num)->real) j1 x - h j1 x`;
                   `h:num->(num->num)->real`] FMEAN_ZN_DENS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC TELESCOPE_STEP THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `fmean (zn_tup k N)
      (\x. (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2 * g j1 x) *
    fmean (zn_tup k N) ((g:num->(num->num)->real) j1)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`zn_tup k N`;
                   `\x. zn_dens k N j1 g x - zn_dens k N j1 h x`;
                   `(g:num->(num->num)->real) j1`] FMEAN_WEIGHTED_CS) THEN
    ASM_SIMP_TAC[FINITE_ZN_TUP];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_POS THEN
    ASM_SIMP_TAC[FINITE_ZN_TUP; REAL_LE_MUL; REAL_LE_POW_2];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `fmean (zn_tup k N)
        (\x. (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2 * nu j1 x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_LE THEN
      ASM_SIMP_TAC[FINITE_ZN_TUP; REAL_LE_LMUL; REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `fmean (zn_tup k N)
        (\x. (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2 * nu j1 x) =
      fmean (zn_tup k N)
        (\x. (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2) +
      fmean (zn_tup k N)
        (\x. (nu j1 x - &1) *
             (zn_dens k N j1 g x - zn_dens k N j1 h x) pow 2)`
    SUBST1_TAC THENL
     [SIMP_TAC[GSYM FMEAN_ADD; FINITE_ZN_TUP] THEN AP_TERM_TAC THEN
      ABS_TAC THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `Sp:num->bool`;
                   `nu:num->(num->num)->real`; `g:num->(num->num)->real`;
                   `h:num->(num->num)->real`; `eps:real`; `eta:real`;
                   `j1:num`; `c:real`] ZN_DENS_L2) THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `Sp:num->bool`;
                   `nu:num->(num->num)->real`; `g:num->(num->num)->real`;
                   `h:num->(num->num)->real`; `eps:real`; `eta:real`;
                   `j1:num`; `delta:real`] SLF_SQUARE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC FMEAN_POS THEN ASM_SIMP_TAC[FINITE_ZN_TUP];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `fmean (zn_tup k N) ((nu:num->(num->num)->real) j1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_LE THEN ASM_SIMP_TAC[FINITE_ZN_TUP]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `j1:num`; `nu:num->(num->num)->real`;
                   `eta:real`] LF_COND_SING_MEAN) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The counting lemma.                                                       *)
(* ------------------------------------------------------------------------- *)

let ZN_HSYS_MONO = prove
 (`!k N Sp (nu:num->(num->num)->real) g h e1 n1 zn_mean2 n2.
        zn_hsys k N Sp nu g h e1 n1 /\ e1 <= zn_mean2 /\ n1 <= n2
        ==> zn_hsys k N Sp nu g h zn_mean2 n2`,
  REWRITE_TAC[zn_hsys] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[ZN_HDISC_MONO; LF_COND_MONO]);;

let SLF_PARAM = prove
 (`!L m delta eta.
        &0 < delta /\ &0 <= eta /\ eta <= &1 /\
        eta <= (delta / &2 pow (L + 1)) pow m
        ==> (&2 pow L * (&1 + eta)) pow m * eta <= delta pow m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 pow (L + 1)) pow m * eta` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 pow (L + 1)) pow m * (delta / &2 pow (L + 1)) pow m` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN
    REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC]);;

let COUNT_PARAM = prove
 (`!ga eps eta.
        &0 < ga /\ ga <= &1 /\ &0 <= eps /\ eps <= ga / &2 /\
        &0 <= eta /\ eta <= &1 /\ &3 * eta <= ga pow 4 / &1024
        ==> eps + sqrt((&3 * eta + sqrt(&3 * eta) + &2 * (ga pow 2 / &64) +
                        &4 * (ga pow 2 / &128)) * (&1 + eta)) <= ga`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&3 * eta) <= ga pow 2 / &32` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_POW_DIV; GSYM REAL_POW_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ga pow 4 <= ga pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO_INV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&3 * eta)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= ga / &2 /\ eps <= ga / &2 ==> eps + x <= ga`) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(ga pow 2 / &8) * &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LE_POW_2; REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_DIV] THEN REAL_ARITH_TAC]);;

let GT_COUNTING_LEMMA = prove
 (`!k s gam.
        &0 < gam
        ==> ?eps eta.
              &0 < eps /\ &0 < eta /\
              !N Sp (nu:num->(num->num)->real) g h.
                zn_hsys k N Sp nu g h eps eta /\ CARD Sp = s
                ==> abs(zn_hcount k N g - zn_hcount k N h) <= gam`,
  GEN_TAC THEN INDUCT_TAC THENL
   [X_GEN_TAC `gam:real` THEN DISCH_TAC THEN
    EXISTS_TAC `gam / (&k + &1)` THEN EXISTS_TAC `&1` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &k + &1`; REAL_LT_01] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[zn_hsys] THEN STRIP_TAC THEN
    SUBGOAL_THEN `Sp:num->bool = {}` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0; FINITE_SUBSET; FINITE_NUMSEG_LT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!j x. j < k /\ x IN zn_tup k N ==> (nu:num->(num->num)->real) j x = &1`
    ASSUME_TAC THENL [ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!j x. j < k /\ x IN zn_tup k N ==> (g:num->(num->num)->real) j x <= &1`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k * (gam / (&k + &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DENSE_COUNT THEN ASM_SIMP_TAC[];
      MP_TAC(SPEC `k:num` REAL_POS) THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ &k * x + x = gam ==> &k * x <= gam`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_FIELD
         `&0 < x + &1 ==> x * (gam / (x + &1)) + gam / (x + &1) = gam`) THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `gam:real` THEN DISCH_TAC THEN
  ABBREV_TAC `ga = min gam (&1)` THEN
  SUBGOAL_THEN `&0 < ga /\ ga <= &1 /\ ga <= gam` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ga" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ga pow 2 / &64`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `n1:real`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `dl = ga pow 2 / &128` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ep = min e1 (ga / &2)` THEN
  ABBREV_TAC
   `et = min n1 (min (&1) (min (ga pow 4 / &3072)
           ((dl / &2 pow (CARD(lf_index k) + 1)) pow (2 EXP (k - 1)))))` THEN
  SUBGOAL_THEN
    `&0 < (dl / &2 pow (CARD(lf_index k) + 1)) pow (2 EXP (k - 1)) /\
                &0 < ga pow 4 / &3072`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < ep /\ ep <= e1 /\ ep <= ga / &2 /\
    &0 < et /\ et <= n1 /\ et <= &1 /\ et <= ga pow 4 / &3072 /\
    et <= (dl / &2 pow (CARD(lf_index k) + 1)) pow (2 EXP (k - 1))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ep"; "et"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ep:real`; `et:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `Sp:num->bool`; `nu:num->(num->num)->real`;
                       `g:num->(num->num)->real`;
                        `h:num->(num->num)->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(Sp:num->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [zn_hsys]) THEN
    MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?j1:num. j1 IN Sp` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s:num->bool = {}) ==> ?x. x IN s`) THEN
    DISCH_TAC THEN UNDISCH_TAC `CARD(Sp:num->bool) = SUC s` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `Sp:num->bool`;
                 `nu:num->(num->num)->real`; `g:num->(num->num)->real`;
                 `h:num->(num->num)->real`; `ep:real`; `et:real`; `j1:num`;
                 `ga pow 2 / &64`; `dl:real`] COUNTING_STEP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`nu':num->(num->num)->real`;
                           `g':num->(num->num)->real`;
                           `h':num->(num->num)->real`] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
       [`N:num`; `Sp DELETE (j1:num)`; `nu':num->(num->num)->real`;
        `g':num->(num->num)->real`; `h':num->(num->num)->real`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC ZN_HSYS_MONO THEN
        MAP_EVERY EXISTS_TAC [`ep:real`; `et:real`] THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[CARD_DELETE] THEN ARITH_TAC];
      MATCH_MP_TAC SLF_PARAM THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= ga /\ ga <= gam ==> a <= b ==> a <= gam`) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "dl" THEN MATCH_MP_TAC COUNT_PARAM THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;
