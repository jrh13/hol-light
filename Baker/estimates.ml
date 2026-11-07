(* ========================================================================= *)
(* Explicit logarithmic estimates for the bound functions of                 *)
(* Baker/parametric_core.ml.                                                 *)
(*                                                                           *)
(* Purpose: Baker, Transcendental Number Theory, Ch. 3, made explicit. M     *)
(* bounds n, nproduct V d, Lam, log(inv lmin) and the height sum             *)
(* sum(1..n) log((d r + 1) H r^3); h bounds M, log k, log G, log Bb, log Gn  *)
(* and sum V e r log((d r + 1) H r^3). The bound functions of                *)
(* Baker/parametric_core.ml are compared with exponentials of baker_lu,      *)
(* baker_lw and baker_l7, explicit polynomials in M, the degree product D,   *)
(* L, k, h, N, R, X7, lmax and log((R + h) / h), lk >= log k, so that the    *)
(* numeric layer Baker/param.ml chooses the parameters by elementary         *)
(* comparisons.                                                              *)
(*                                                                           *)
(* Main results:                                                             *)
(*  - BAKER_NMAX_LOG: log(baker_nmax h R) = h (19 + log((R + h) / h));       *)
(*  - BAKER_PBOUND_LOG_LE: log(baker_pbound ...) <= 43 h k + (2 M + 10) L h; *)
(*  - BAKER_UB_LOG_LE: log(baker_ub ...) <= baker_lu M L k h N;              *)
(*  - BAKER_ERR_LE_UB: baker_err <= exp(1) N L d0 baker_ub if N L d0 <= 1;   *)
(*  - BAKER_LIOU5_EXP_LOWER: the Liouville bound of Lemma 5 divided by       *)
(*    (baker_nmax h R Gn)^k, times lmin^k, is >= exp(--baker_lw ...);        *)
(*  - BAKER_LIOU7_EXP_LOWER: baker_liou7 ... >= exp(--baker_l7 ...);         *)
(*  - the generic LOG_LE_SELF (also used by later files).                    *)
(*                                                                           *)
(* Uses: Baker/parametric_core.ml (the bound functions), Baker/bounds.ml     *)
(* (CARD_BAKER_INDEX_EXP_BOUND, PRODUCT_GE_1), Baker/aux_arith.ml            *)
(* (CARD_BAKER_INDEX), Baker/auxiliary.ml (baker_index), Baker/lemmas.ml     *)
(* (REAL_LE_1_MUL, LOG_MUL4, LOG_2_LE_1, LOG_SUC_SUB_LE_INV).                *)
(* ========================================================================= *)

needs "Baker/parametric_core.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The explicit exponents.                                                   *)
(* ------------------------------------------------------------------------- *)

let baker_lu = new_definition
 `baker_lu M L k h N =
    &51 * &h * &k + (&3 * M + &15) * &L * &h + (M + &4) * &L * &N`;;

let baker_lw = new_definition
 `baker_lw M D L k h R =
    (&D + &1) * &k * &h * (&19 + log((&R + &h) / &h)) +
    (&50 * &D + &2) * &h * &k + &D * (&3 * M + &12) * &L * &h +
    &D * (M + &9) * &L * &R`;;

let baker_l7 = new_definition
 `baker_l7 M D n L k h X7 lmax lk =
    &D * &k pow n *
    ((&n + &1) * &h + (&3 * M + &12) * &L * &h + &43 * &h * &k +
     &6 * &h * &L * lk + &6 * &L * &X7 +
     &L * &lmax * (&n * (lk + &1) + M))`;;

(* ------------------------------------------------------------------------- *)
(* Elementary facts about log, products and nproduct.                        *)
(* ------------------------------------------------------------------------- *)

let LOG_LE_SELF = prove
 (`!x. &0 < x ==> log x <= x`,
  SIMP_TAC[LOG_LT_X; REAL_LT_IMP_LE]);;

let LOG_NUM_SUC_LE = prove
 (`!k. 1 <= k ==> log(&k + &1) <= &1 + log(&k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&k` LOG_SUC_SUB_LE_INV) THEN MP_TAC(SPEC `&k` REAL_INV_LE_1) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT;
               ARITH_RULE `1 <= k ==> 0 < k`] THEN
  REAL_ARITH_TAC);;

let BAKER_LOG_MUL3 = prove
 (`!a b c. &0 < a /\ &0 < b /\ &0 < c
           ==> log(a * b * c) = log a + log b + log c`,
  SIMP_TAC[LOG_MUL; REAL_LT_MUL]);;

let BAKER_LOG_POW4 = prove
 (`!a b c w x y z t.
        &0 < a /\ &0 < b /\ &0 < c /\ &0 < w
        ==> log(a pow x * b pow y * c pow z * w pow t) =
            &x * log a + &y * log b + &z * log c + &t * log w`,
  SIMP_TAC[LOG_MUL4; LOG_POW; REAL_POW_LT]);;

let BAKER_POW4_GE_1 = prove
 (`!a b c w x y z t.
        &1 <= a /\ &1 <= b /\ &1 <= c /\ &1 <= w
        ==> &1 <= a pow x * b pow y * c pow z * w pow t`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
  MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The common multiple bound baker_nmax.                                     *)
(* ------------------------------------------------------------------------- *)

let BAKER_NMAX_LOG = prove
 (`!h R. 1 <= h
         ==> &1 <= baker_nmax h R /\
             log(baker_nmax h R) = &h * (&19 + log((&R + &h) / &h))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &h` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&R + &h) / &h` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp(&19)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&19` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[baker_nmax] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN MATCH_MP_TAC REAL_LE_1_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(&19) * (&R + &h) / &h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP;
               REAL_ARITH `&1 <= x ==> &0 < x`]);;

(* ------------------------------------------------------------------------- *)
(* Estimates shared by the bounds: CARD(baker_index h L n), the factors      *)
(* 2^(...) (k + 1)^k (2 L G)^k and the height products and sums.             *)
(* ------------------------------------------------------------------------- *)

let BAKER_HNL_LE = prove
 (`!h L n M. 1 <= h /\ 1 <= L /\ &n <= M
             ==> &h + &(n + 1) * &L <= (M + &2) * &L * &h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &L` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&L - &1) * &h /\ &0 <= (M - &n) * &L /\
    &0 <= (M * &L) * (&h - &1) /\ &0 <= &L * (&h - &1)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

let BAKER_LOG_CARD_LE = prove
 (`!h L n M.
        1 <= h /\ 1 <= L /\ &n <= M
        ==> &1 <= &(CARD(baker_index h L n)) /\
            log(&(CARD(baker_index h L n))) <= (M + &2) * &L * &h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &(CARD(baker_index h L n))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; CARD_BAKER_INDEX] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  TRANS_TAC REAL_LE_TRANS `&h + &(n + 1) * &L` THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `log(exp(&h) * exp(&(n + 1) * &L))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[CARD_BAKER_INDEX_EXP_BOUND] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_EXP_ADD; LOG_EXP; REAL_LE_REFL]];
    MATCH_MP_TAC BAKER_HNL_LE THEN ASM_REWRITE_TAC[]]);;

let BAKER_LOG_X_BOUND = prove
 (`!h L k G R.
        1 <= h /\ h <= R /\ 1 <= L /\ L <= k /\ &1 <= G /\
        log G <= &h /\ log(&k) <= &h
        ==> &((L + 2) * ((R + 1) + h)) * log(&2) + &k * log(&k + &1) +
            &k * log(&2 * &L * G) <= &9 * &L * &R + &5 * &h * &k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &h <= &R /\ &1 <= &L /\ &L <= &k /\ &1 <= &k`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&k + &1) <= &1 + &h` ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` LOG_NUM_SUC_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * &L * G) <= &1 + &2 * &h` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(&2 * &L * G) = log(&2) + log(&L) + log G`
    SUBST1_TAC THENL
     [MATCH_MP_TAC BAKER_LOG_MUL3 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `log(&L) <= log(&k)` MP_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC LOG_2_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&((L + 2) * ((R + 1) + h)) <= &9 * &L * &R` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN
     `&0 <= (&2 * &L - &2) * (&R + &1 + &h) /\
      &0 <= (&3 * &L) * (&2 * &R - &1 - &h)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&((L + 2) * ((R + 1) + h)) * log(&2) <=
    &((L + 2) * ((R + 1) + h)) * &1 /\
    &k * log(&k + &1) <= &k * (&1 + &h) /\
    &k * log(&2 * &L * G) <= &k * (&1 + &2 * &h)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_POS; LOG_2_LE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &k * (&h - &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BAKER_LOG_2H_LE = prove
 (`!d x. 1 <= d /\ &1 <= x
         ==> &0 < &2 * x /\ &0 <= log(&2 * x) /\
             log(&2 * x) <= log(&(d + 1) * x pow 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`1`; `3`; `x:real`] REAL_POW_MONO) THEN
    ASM_REWRITE_TAC[REAL_POW_1; ARITH]]);;

let BAKER_SUM_IF_SPLIT = prove
 (`!V n c k (e:num->num) (w:num->real).
        FINITE V /\ (1..n) SUBSET V
        ==> sum V (\r. &((if r IN 1..n then c else 0) + k * e r) * w r) =
            &c * sum(1..n) w + &k * sum V (\r. &(e r) * w r)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              REAL_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[SUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum(1..n) (\r. &(if r IN 1..n then c else 0) * (w:num->real) r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[]]);;

let BAKER_SUM_IF_LE = prove
 (`!V n c k (e:num->num) (w:num->real) M h.
        FINITE V /\ (1..n) SUBSET V /\ sum(1..n) w <= M /\
        sum V (\r. &(e r) * w r) <= &h
        ==> sum V (\r. &((if r IN 1..n then c else 0) + k * e r) * w r) <=
            &c * M + &k * &h`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BAKER_SUM_IF_SPLIT] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]);;

let BAKER_LOG_PI_LE = prove
 (`!V n (d:num->num) (H:num->real) (e:num->num) c k M h.
        FINITE V /\ (1..n) SUBSET V /\
        (!r. r IN V ==> 1 <= d r /\ &1 <= H r) /\
        sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= M /\
        sum V (\r. &(e r) * log(&(d r + 1) * H r pow 3)) <= &h
        ==> &1 <= product V (\r. (&2 * H r) pow
                                 ((if r IN 1..n then c else 0) + k * e r)) /\
            log(product V (\r. (&2 * H r) pow
                               ((if r IN 1..n then c else 0) + k * e r)))
            <= &c * M + &k * &h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. r IN V
        ==> &0 < &2 * (H:num->real) r /\ &1 <= &2 * H r /\
            log(&2 * H r) <= log(&((d:num->num) r + 1) * H r pow 3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `1 <= (d:num->num) r /\ &1 <= (H:num->real) r`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`(d:num->num) r`; `(H:num->real) r`] BAKER_LOG_2H_LE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_GE_1 THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\r. (&2 * (H:num->real) r) pow
         ((if r IN 1..n then c else 0) + k * (e:num->num) r)`;
    `V:num->bool`] LOG_PRODUCT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum V (\r. &((if r IN 1..n then c else 0) + k * (e:num->num) r) *
               log(&((d:num->num) r + 1) * (H:num->real) r pow 3))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LOG_POW] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POS];
    MP_TAC(ISPECL [`V:num->bool`; `n:num`; `c:num`; `k:num`; `e:num->num`;
                   `\r. log(&((d:num->num) r + 1) * (H:num->real) r pow 3)`;
                   `M:real`; `h:num`] BAKER_SUM_IF_LE) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[]]);;

let BAKER_LOG_KD_LE = prove
 (`!k d x lk.
        1 <= k /\ &1 <= x /\ log(&k) <= lk
        ==> log(&(k * d + 1) * x pow 3) <=
            (lk + &1) + log(&(d + 1) * x pow 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(d + 1) * x pow 3 /\ &0 < &(k * d + 1) * x pow 3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `log((&k + &1) * &(d + 1) * x pow 3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &k + &1`] THEN
    MP_TAC(SPEC `k:num` LOG_NUM_SUC_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Siegel height bound baker_pbound.                                     *)
(* ------------------------------------------------------------------------- *)

let BAKER_PBOUND_LOG_LE = prove
 (`!n h L k V G (H:num->real) (e:num->num) (d:num->num) M.
        1 <= n /\ 1 <= h /\ 1 <= L /\ L <= k /\ FINITE V /\
        (1..n) SUBSET V /\ (!r. r IN V ==> 1 <= d r /\ &1 <= H r) /\
        &1 <= G /\ &n <= M /\
        sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= M /\
        log G <= &h /\ log(&k) <= &h /\
        sum V (\r. &(e r) * log(&(d r + 1) * H r pow 3)) <= &h
        ==> &1 <= baker_pbound n h L k V G H e /\
            log(baker_pbound n h L k V G H e) <=
            &43 * &h * &k + (&2 * M + &10) * &L * &h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[baker_pbound] THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &L /\ &L <= &k /\ &1 <= &k`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &2 * &L * G` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= y ==> &1 <= &2 * y`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `L:num`; `k:num`; `G:real`; `h:num`]
         BAKER_LOG_X_BOUND) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  ABBREV_TAC `C = &(CARD(baker_index h L n))` THEN
  ABBREV_TAC
   `X = exp(&36 * &h) pow k * &2 pow ((L + 2) * ((h + 1) + h)) *
        (&k + &1) pow k * (&2 * &L * G) pow k` THEN
  ABBREV_TAC
   `Q = product V (\r. (&2 * (H:num->real) r) pow
                       ((if r IN 1..n then L * h else 0) + k * e r))` THEN
  SUBGOAL_THEN `&1 <= C /\ log C <= (M + &2) * &L * &h` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC BAKER_LOG_CARD_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= Q /\ log Q <= &L * &h * M + &k * &h`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    MP_TAC(SPECL [`V:num->bool`; `n:num`; `d:num->num`; `H:num->real`;
                  `e:num->num`; `L * h`; `k:num`; `M:real`; `h:num`]
           BAKER_LOG_PI_LE) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= X /\
    log X = &k * (&36 * &h) + &((L + 2) * ((h + 1) + h)) * log(&2) +
            &k * log(&k + &1) + &k * log(&2 * &L * G)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= exp(&36 * &h)` ASSUME_TAC THENL
     [MP_TAC(SPEC `&36 * &h` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "X" THEN CONJ_TAC THENL
     [MATCH_MP_TAC BAKER_POW4_GE_1 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`exp(&36 * &h)`; `&2`; `&k + &1`; `&2 * &L * G`;
                   `k:num`; `(L + 2) * ((h + 1) + h)`; `k:num`; `k:num`]
           BAKER_LOG_POW4) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LOG_EXP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `max (&1) (X * Q) = X * Q` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= y ==> max (&1) y = y`) THEN
    ASM_SIMP_TAC[REAL_LE_1_MUL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_SIMP_TAC[REAL_LE_1_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(C * X * Q) = log C + log X + log Q` SUBST1_TAC THENL
   [MATCH_MP_TAC BAKER_LOG_MUL3 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&L * &h <= &k * &h` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bounds baker_ub and baker_err for the auxiliary function.             *)
(* ------------------------------------------------------------------------- *)

let BAKER_UB_LOG_LE = prove
 (`!n h L k P Bb Lam N M.
        1 <= n /\ 1 <= h /\ 1 <= L /\ L <= k /\ &1 <= P /\ &1 <= Bb /\
        &1 <= Lam /\ Lam <= M /\ &n <= M /\ M <= &h /\
        log(&k) <= &h /\ log Bb <= &h /\
        log P <= &43 * &h * &k + (&2 * M + &10) * &L * &h
        ==> log(baker_ub n h L k P Bb Lam N) <= baker_lu M L k h N`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_ub; baker_lu] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP;
               REAL_ARITH `&1 <= x ==> &0 < x`] THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &L /\ &1 <= &k /\ &L <= &k`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * &k * Bb * Lam) <= &1 + &3 * &h` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `log(&2 * &k * Bb * Lam) = log(&2) + log(&k) + log Bb + log Lam`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LOG_MUL4 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC LOG_2_LE_1 THEN
    MP_TAC(SPEC `Lam:real` LOG_LE_SELF) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(2 * k) * log(&2 * &k * Bb * Lam) <= &(2 * k) * (&1 + &3 * &h)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&(2 * k) * (&1 + &3 * &h) <= &8 * &h * &k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&0 <= &k * (&h - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `L:num`; `n:num`; `M:real`] BAKER_HNL_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&(L + 2) * &(N + h) <= &3 * &L * &N + &3 * &L * &h`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&0 <= (&2 * &L - &2) * (&N + &h)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N * &L * (Lam + &1) <= &N * &L * (M + &1)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BAKER_ERR_LE_UB = prove
 (`!n h L k P Bb Lam d0 N.
        &0 <= P /\ &0 <= d0 /\ &N * &L * d0 <= &1
        ==> baker_err n h L k P Bb Lam d0 N <=
            exp(&1) * (&N * &L * d0) * baker_ub n h L k P Bb Lam N`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_err; baker_ub] THEN
  SUBGOAL_THEN
   `exp(&h + &(n + 1) * &L + &(L + 2) * &(N + h) +
        &(2 * k) * log(&2 * &k * Bb * Lam) + &N * &L * (Lam + &1)) =
    exp(&h + &(n + 1) * &L + &(L + 2) * &(N + h) +
        &(2 * k) * log(&2 * &k * Bb * Lam) + &N * &L * Lam) * exp(&N * &L)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `E = exp(&h + &(n + 1) * &L + &(L + 2) * &(N + h) +
            &(2 * k) * log(&2 * &k * Bb * Lam) + &N * &L * Lam)` THEN
  SUBGOAL_THEN `&0 <= P * E * (&N * &L * d0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&N * &L * d0) <= exp(&1) * exp(&N * &L)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
    MP_TAC(SPECL [`&N`; `&L`] REAL_LE_MUL) THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`P * E * (&N * &L * d0)`; `exp(&N * &L * d0)`;
                `exp(&1) * exp(&N * &L)`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* The Liouville bound of Lemma 5 (divided by the common multiple and the    *)
(* denominator power, times lmin^k as in baker_vb).                          *)
(* ------------------------------------------------------------------------- *)

let BAKER_EXP_RATIO_LOWER = prove
 (`!D Y lmin k nm Gn W.
        &0 < lmin /\ &0 < nm /\ &0 < Gn /\
        D * Y + &k * log(inv lmin) + &k * log nm + &k * log Gn <= W
        ==> exp(--W) <= lmin pow k * exp(--(D * Y)) / (nm pow k * Gn pow k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `lmin:real` LOG_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SUBGOAL_THEN
   `lmin pow k * exp(--(D * Y)) / (nm pow k * Gn pow k) =
    exp(&k * log lmin + --(D * Y) - (&k * log nm + &k * log Gn))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_SUB; REAL_EXP_ADD; REAL_EXP_N] THEN
    ASM_SIMP_TAC[EXP_LOG];
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC]);;

let BAKER_LIOU5_LOG_LE = prove
 (`!n h L k V G (H:num->real) (e:num->num) (d:num->num) P R M.
        1 <= n /\ 1 <= h /\ h <= R /\ 1 <= L /\ L <= k /\ FINITE V /\
        (1..n) SUBSET V /\ (!r. r IN V ==> 1 <= d r /\ &1 <= H r) /\
        &1 <= G /\ &1 <= P /\ &n <= M /\ &(nproduct V d) <= M /\
        sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= M /\
        M <= &h /\ log G <= &h /\ log(&k) <= &h /\
        sum V (\r. &(e r) * log(&(d r + 1) * H r pow 3)) <= &h /\
        log P <= &43 * &h * &k + (&2 * M + &10) * &L * &h
        ==> log(&(nproduct V d)) +
            log(&(CARD(baker_index h L n)) * P *
                (baker_nmax h R pow k * &2 pow ((L + 2) * ((R + 1) + h)) *
                 (&k + &1) pow k * (&2 * &L * G) pow k)) +
            sum V (\r. &((if r IN 1..n then L * R else 0) + k * e r) *
                       log(&(d r + 1) * H r pow 3))
            <= &k * log(baker_nmax h R) + &50 * &h * &k +
               (&3 * M + &12) * &L * &h + (M + &9) * &L * &R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &h <= &R /\ &1 <= &L /\ &L <= &k /\ &1 <= &k`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= baker_nmax h R` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BAKER_NMAX_LOG]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &2 * &L * G` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= y ==> &1 <= &2 * y`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `L:num`; `n:num`; `M:real`] BAKER_LOG_CARD_LE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:num`; `L:num`; `k:num`; `G:real`; `R:num`]
         BAKER_LOG_X_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:num->bool`; `n:num`; `L * R`; `k:num`; `e:num->num`;
                 `\r. log(&((d:num->num) r + 1) * (H:num->real) r pow 3)`;
                 `M:real`; `h:num`] BAKER_SUM_IF_LE) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_MUL]) THEN
  SUBGOAL_THEN `log(&(nproduct V (d:num->num))) <= &h` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&(nproduct V (d:num->num))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC LOG_LE_SELF THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> 0 < n`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= baker_nmax h R pow k * &2 pow ((L + 2) * ((R + 1) + h)) *
          (&k + &1) pow k * (&2 * &L * G) pow k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_POW4_GE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `log(baker_nmax h R pow k * &2 pow ((L + 2) * ((R + 1) + h)) *
        (&k + &1) pow k * (&2 * &L * G) pow k) =
    &k * log(baker_nmax h R) + &((L + 2) * ((R + 1) + h)) * log(&2) +
    &k * log(&k + &1) + &k * log(&2 * &L * G)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_LOG_POW4 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&(CARD(baker_index h L n)) * P *
        (baker_nmax h R pow k * &2 pow ((L + 2) * ((R + 1) + h)) *
         (&k + &1) pow k * (&2 * &L * G) pow k)) =
    log(&(CARD(baker_index h L n))) + log P +
    log(baker_nmax h R pow k * &2 pow ((L + 2) * ((R + 1) + h)) *
        (&k + &1) pow k * (&2 * &L * G) pow k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC BAKER_LOG_MUL3 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &h * (&k - &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BAKER_LIOU5_EXP_LOWER = prove
 (`!n h L k V G (H:num->real) (e:num->num) (d:num->num) P Gn lmin R M.
        1 <= n /\ 1 <= h /\ h <= R /\ 1 <= L /\ L <= k /\ FINITE V /\
        (1..n) SUBSET V /\ (!r. r IN V ==> 1 <= d r /\ &1 <= H r) /\
        &1 <= G /\ &1 <= P /\ &1 <= Gn /\ &0 < lmin /\ lmin <= &1 /\
        &n <= M /\ &(nproduct V d) <= M /\
        sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= M /\
        log(inv lmin) <= M /\ M <= &h /\
        log G <= &h /\ log(&k) <= &h /\ log Gn <= &h /\
        sum V (\r. &(e r) * log(&(d r + 1) * H r pow 3)) <= &h /\
        log P <= &43 * &h * &k + (&2 * M + &10) * &L * &h
        ==> exp(--(baker_lw M (nproduct V d) L k h R)) <=
            lmin pow k * baker_liou5 n h L k V G H e d P R /
            (baker_nmax h R pow k * Gn pow k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[baker_liou5] THEN
  MP_TAC(SPECL [`h:num`; `R:num`] BAKER_NMAX_LOG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC BAKER_EXP_RATIO_LOWER THEN
  SUBGOAL_THEN `&0 < baker_nmax h R /\ &0 < Gn` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `k:num`; `V:num->bool`;
                `G:real`; `H:num->real`; `e:num->num`; `d:num->num`;
                `P:real`; `R:num`; `M:real`] BAKER_LIOU5_LOG_LE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o
             CONJ (SPEC `nproduct V (d:num->num)` REAL_POS)) THEN
  SUBGOAL_THEN `&k * log(inv lmin) <= &k * &h /\ &k * log Gn <= &k * &h`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[baker_lw] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Liouville bound of Lemma 7.                                           *)
(* ------------------------------------------------------------------------- *)

let BAKER_LIOU7_LOG_LE = prove
 (`!n h L k (d:num->num) (H:num->real) P X7 lmax lk V M.
        1 <= n /\ 1 <= h /\ h <= X7 /\ 1 <= L /\ L <= k /\ FINITE V /\
        (1..n) SUBSET V /\ (!r. r IN V ==> 1 <= d r /\ &1 <= H r) /\
        &1 <= P /\ &n <= M /\ &(nproduct V d) <= M /\
        sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= M /\
        M <= &h /\ log(&k) <= &h /\ log(&k) <= lk /\
        log P <= &43 * &h * &k + (&2 * M + &10) * &L * &h
        ==> log(&(nproduct(1..n) (\r. k * d r))) +
            log(&(CARD(baker_index h L n)) *
                (P * &k pow (2 * h * (L + 2)) * &2 pow ((L + 2) * (X7 + h)))) +
            sum(1..n) (\r. &(L * lmax) * log(&(k * d r + 1) * H r pow 3))
            <= (&n + &1) * &h + (&3 * M + &12) * &L * &h + &43 * &h * &k +
               &6 * &h * &L * lk + &6 * &L * &X7 +
               &L * &lmax * (&n * (lk + &1) + M)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &h <= &X7 /\ &1 <= &L /\ &L <= &k /\ &1 <= &k`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&k) /\ &0 <= lk` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&k` LOG_POS) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nproduct(1..n) (\r. k * (d:num->num) r) = k EXP n * nproduct(1..n) d`
  SUBST1_TAC THENL
   [SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG; NPRODUCT_CONST_NUMSEG; ADD_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `1 <= nproduct(1..n) (d:num->num) /\
    nproduct(1..n) (d:num->num) <= nproduct V d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
      MATCH_MP_TAC NPRODUCT_POS_LT THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(r:num) IN V` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> 0 < n`];
      MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&(k EXP n * nproduct(1..n) d)) <= (&n + &1) * &h`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    SUBGOAL_THEN
     `&0 < &k pow n /\ &1 <= &(nproduct(1..n) (d:num->num))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    SUBGOAL_THEN `&n * log(&k) <= &n * &h` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    MP_TAC(SPEC `&(nproduct(1..n) (d:num->num))` LOG_LE_SELF) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&(nproduct(1..n) (d:num->num)) <= &(nproduct V d)`
    MP_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `L:num`; `n:num`; `M:real`] BAKER_LOG_CARD_LE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `log(&(CARD(baker_index h L n)) *
        (P * &k pow (2 * h * (L + 2)) * &2 pow ((L + 2) * (X7 + h)))) =
    log(&(CARD(baker_index h L n))) + log P +
    &(2 * h * (L + 2)) * log(&k) + &((L + 2) * (X7 + h)) * log(&2)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `&0 < &k pow (2 * h * (L + 2)) /\ &0 < &2 pow ((L + 2) * (X7 + h))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL4; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    ASM_SIMP_TAC[LOG_POW; REAL_ARITH `&1 <= x ==> &0 < x`;
                 REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(2 * h * (L + 2)) * log(&k) <= &6 * &h * &L * lk`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&(2 * h * (L + 2)) * lk` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&0 <= &h * (&L - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&((L + 2) * (X7 + h)) * log(&2) <= &6 * &L * &X7`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&((L + 2) * (X7 + h)) * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; LOG_2_LE_1];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN
     `&0 <= (&2 * &L - &2) * (&X7 + &h) /\ &0 <= (&3 * &L) * (&X7 - &h)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\r. &(L * lmax) * log(&(k * d r + 1) * H r pow 3)) <=
    &L * &lmax * (&n * (lk + &1) + M)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]) THEN
    TRANS_TAC REAL_LE_TRANS
     `sum(1..n) (\r. (lk + &1) +
                     log(&((d:num->num) r + 1) * (H:num->real) r pow 3))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC BAKER_LOG_KD_LE THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(r:num) IN V` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_NUMSEG]; ASM_SIMP_TAC[]];
      REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG; ADD_SUB] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BAKER_LIOU7_EXP_LOWER = prove
 (`!n h L k (d:num->num) (H:num->real) P X7 lmax lk V M.
        1 <= n /\ 1 <= h /\ h <= X7 /\ 1 <= L /\ L <= k /\ FINITE V /\
        (1..n) SUBSET V /\ (!r. r IN V ==> 1 <= d r /\ &1 <= H r) /\
        &1 <= P /\ &n <= M /\ &(nproduct V d) <= M /\
        sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= M /\
        M <= &h /\ log(&k) <= &h /\ log(&k) <= lk /\
        log P <= &43 * &h * &k + (&2 * M + &10) * &L * &h
        ==> exp(--(baker_l7 M (nproduct V d) n L k h X7 lmax lk)) <=
            baker_liou7 n h L k d H P X7 lmax`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[baker_l7; baker_liou7; REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `k:num`; `d:num->num`;
                `H:num->real`; `P:real`; `X7:num`; `lmax:num`; `lk:real`;
                `V:num->bool`; `M:real`] BAKER_LIOU7_LOG_LE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `B = (&n + &1) * &h + (&3 * M + &12) * &L * &h + &43 * &h * &k +
        &6 * &h * &L * lk + &6 * &L * &X7 +
        &L * &lmax * (&n * (lk + &1) + M)` THEN
  ABBREV_TAC
   `Y = log(&(nproduct(1..n) (\r. k * d r))) +
        log(&(CARD(baker_index h L n)) *
            (P * &k pow (2 * h * (L + 2)) * &2 pow ((L + 2) * (X7 + h)))) +
        sum(1..n) (\r. &(L * lmax) * log(&(k * d r + 1) * H r pow 3))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lk` ASSUME_TAC THENL
   [MP_TAC(SPEC `&k` LOG_POS) THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SUBGOAL_THEN `&0 <= M` MP_TAC THENL
     [MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    REPEAT((MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) ORELSE
           (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(nproduct(1..n) (\r. k * (d:num->num) r)) <= &(nproduct V d) * &k pow n`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG; NPRODUCT_CONST_NUMSEG; ADD_SUB] THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&(nproduct(1..n) (\r. k * (d:num->num) r)) * B` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[]]);;
