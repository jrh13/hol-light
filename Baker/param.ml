(* ========================================================================= *)
(* The numeric layer of the Baker method: explicit parameters.               *)
(*                                                                           *)
(* Purpose: Baker, Transcendental Number Theory, Ch. 3, made explicit:       *)
(* parameters for BAKER_CORE_PARAMETRIC (Baker/parametric_core.ml) and the   *)
(* verification of all its numeric hypotheses. With D = nproduct V d,        *)
(* a = 8 D + 8, c = a + 2, a base q (natural, huge) and h (natural, of the   *)
(* size of log of the heights):                                              *)
(*   k = q^(c (n+1)), L = 2 D q^(c n), R_K = h q^K, S_K = k DIV 2^K,         *)
(*   rho_K = 4 q^a R_(K+1), J = c (2 n^2 + 2 n) + 2, X7 = h (L+2)^(n+1),     *)
(*   rhoX = 4 q^a R_J, eps = exp(-(q^e1 h)) with e1 = c (n+1) + J + 4.       *)
(* The extrapolation steps (BAKER_STEP_NUM) and Lemma 7 (BAKER_LEMMA7_NUM)   *)
(* are the two delicate comparisons of powers of q; all other conditions     *)
(* follow from crude bounds by U = h q^(c (n+1) + J + 3) <= q^e1 h / 16      *)
(* (BAKER_UNITS).                                                            *)
(*                                                                           *)
(* Main results: BAKER_CORE_NUMERIC: if the data are as in                   *)
(* BAKER_CORE_PARAMETRIC, M bounds n, D, Lam, the heights of the alphas and  *)
(* log(1/lmin), q is large in terms of M, n, D, and h bounds M, log k,       *)
(* log G, log Bb, log Gn and the heights of the extra variables, then        *)
(* |beta0 + sum beta r lg r - lg n| > exp(-(q^(e1+1) h)). The parameters     *)
(* baker_kpar, baker_Lpar, baker_J, baker_c and baker_e1 are also used by    *)
(* Baker/numeric_dmax.ml and Baker/explicit.ml.                              *)
(*                                                                           *)
(* Uses: Baker/parametric_core.ml (BAKER_CORE_PARAMETRIC and the bound       *)
(* functions), Baker/estimates.ml (the logarithmic estimates, baker_lu,      *)
(* baker_lw, baker_l7), Baker/bounds.ml (REAL_LE_EXP_SELF), Baker/lemmas.ml  *)
(* (REAL_TWO_POW_LE_EXP, REAL_LE_1_MUL), Baker/intpoly.ml (intpoly).         *)
(* ========================================================================= *)

needs "Baker/estimates.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The parameters: a = baker_a D, c = baker_c D, k = baker_kpar n D q,       *)
(* L = baker_Lpar n D q and J = baker_J n D.                                 *)
(* ------------------------------------------------------------------------- *)

let baker_a = new_definition `baker_a D = 8 * D + 8`;;
let baker_c = new_definition `baker_c D = 8 * D + 10`;;
let baker_kpar = new_definition
 `baker_kpar n D q = q EXP (baker_c D * (n + 1))`;;
let baker_Lpar = new_definition
 `baker_Lpar n D q = 2 * D * q EXP (baker_c D * n)`;;
let baker_J = new_definition
 `baker_J n D = baker_c D * (2 * n * n + 2 * n) + 2`;;

(* ------------------------------------------------------------------------- *)
(* Elementary facts about the parameters and powers of q.                    *)
(* ------------------------------------------------------------------------- *)

let BAKER_C_EQ = prove
 (`!D. baker_c D = baker_a D + 2`,
  REWRITE_TAC[baker_a; baker_c] THEN ARITH_TAC);;

let REAL_POW_COUNT_LE = prove
 (`!K. &(K + 2) * &2 pow K <= &2 * &4 pow K`,
  INDUCT_TAC THENL
   [REWRITE_TAC[real_pow; ADD_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[real_pow; ARITH_RULE `SUC K + 2 = (K + 2) + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    MP_TAC(SPECL [`&2`; `K:num`] REAL_POW_LE) THEN
    MP_TAC(SPECL [`&K`; `&2 pow K`] REAL_LE_MUL) THEN
    REWRITE_TAC[REAL_POS] THEN
    MP_TAC(SPECL [`&2`; `K:num`] REAL_POW_LE) THEN
    REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC]);;

let REAL_DIV_SUC_LE = prove
 (`!k m. ~(m = 0) ==> &k / &m <= &(k DIV m + 1)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1; REAL_OF_NUM_MUL;
               REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`k:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

let LOG_POW_ADD1_LE = prove
 (`!q K. 1 <= q ==> log(&q pow (K + 1) + &1) <= &1 + &(K + 1) * log(&q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &q pow (K + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `log(&2 * &q pow (K + 1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
  MP_TAC(SPEC `&1` LOG_LE) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let BAKER_KPAR_REAL = prove
 (`!n D q. &(baker_kpar n D q) =
           &q pow (baker_c D * n) * &q pow (baker_a D) * &q pow 2`,
  REWRITE_TAC[baker_kpar; GSYM REAL_OF_NUM_POW; GSYM REAL_POW_ADD;
              BAKER_C_EQ] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

let BAKER_LPAR_REAL = prove
 (`!n D q. &(baker_Lpar n D q) = &2 * &D * &q pow (baker_c D * n)`,
  REWRITE_TAC[baker_Lpar; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW]);;

(* ------------------------------------------------------------------------- *)
(* The extrapolation step (Lemma 6): the exponents baker_lu and baker_lw     *)
(* at step K are small against R_K (S_(K+1) + 1) a log q.                    *)
(* ------------------------------------------------------------------------- *)

let BAKER_STEP_NUM = prove
 (`!M D n q h K.
     1 <= n /\ 1 <= D /\ &D <= M /\ 1 <= h /\ 4 <= q /\ &112 <= log(&q) /\
     &2176 * M pow 3 * &2 pow K <= &q
     ==> baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h
                  (4 * q EXP baker_a D * (h * q EXP (K + 1)) + 1) +
         baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h
                  (h * q EXP (K + 1)) + &3
         <= &(h * q EXP K) * &(baker_kpar n D q DIV 2 EXP (K + 1) + 1) *
            &(baker_a D) * log(&q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[baker_lu; baker_lw] THEN
  ABBREV_TAC `a = baker_a D` THEN
  ABBREV_TAC `lam = baker_c D * n` THEN
  ABBREV_TAC `k = baker_kpar n D q` THEN
  ABBREV_TAC `L = baker_Lpar n D q` THEN
  SUBGOAL_THEN `&k = &q pow lam * &q pow a * &q pow 2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["k"; "lam"; "a"] THEN REWRITE_TAC[BAKER_KPAR_REAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&L = &2 * &D * &q pow lam` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "lam"] THEN REWRITE_TAC[BAKER_LPAR_REAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&a = &8 * (&D + &1)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[baker_a; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R = h * q EXP (K + 1)` THEN
  ABBREV_TAC `N = 4 * q EXP a * R + 1` THEN
  SUBGOAL_THEN `&R = &h * &q pow (K + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N = &4 * &q pow a * &h * &q pow (K + 1) + &1` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW;
                GSYM REAL_OF_NUM_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q /\ &1 <= &q /\ &2 <= &q /\ &4 <= &q`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &D /\ &1 <= M` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    TRANS_TAC REAL_LE_TRANS `&D` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &q pow a /\ &1 <= &q pow K /\ &1 <= &q pow lam /\
                &1 <= &q pow (K + 1) /\ &0 <= log(&q)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE_1; LOG_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LE_1];
    ALL_TAC] THEN
  ABBREV_TAC `Z = &h * &q pow K * (&k / &2 pow (K + 1)) * &a * log(&q)` THEN
  SUBGOAL_THEN
   `Z <= &(h * q EXP K) * &(k DIV 2 EXP (K + 1) + 1) * &a * log(&q)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW;
                GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_DIV_SUC_LE THEN
      REWRITE_TAC[EXP_EQ_0] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&D + &1) * &k * &h * (&19 + log((&R + &h) / &h)) <= Z / &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(&R + &h) / &h = &q pow (K + 1) + &1` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(&h = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MP_TAC(SPECL [`q:num`; `K:num`] LOG_POW_ADD1_LE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `(&D + &1) * &k * &h * (&(K + 2) * log(&q))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `Z / &2 = (&D + &1) * &k * &h * (((&2 * &q pow K) / &2 pow K) * log(&q))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Z" THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `&a = &8 * (&D + &1)`)) THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
      SUBGOAL_THEN `~(&2 pow K = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ];
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
    TRANS_TAC REAL_LE_TRANS `&2 * &4 pow K` THEN
    REWRITE_TAC[REAL_POW_COUNT_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&51 * &h * &k + (&50 * &D + &2) * &h * &k + &3 <= Z / &8`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `Z / &8 = ((&D + &1) * &h * &k) * (log(&q) * (&q pow K / &2 pow (K + 1)))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Z" THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `&a = &8 * (&D + &1)`)) THEN
      SUBGOAL_THEN `~(&2 pow (K + 1) = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ];
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&56 <= log(&q) * (&q pow K / &2 pow (K + 1))` ASSUME_TAC THENL
     [SUBGOAL_THEN `&1 / &2 <= &q pow K / &2 pow (K + 1)` ASSUME_TAC THENL
       [SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
        REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 / &2 * (x * &2) <= y`) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`&112`; `log(&q)`; `&1 / &2`;
                    `&q pow K / &2 pow (K + 1)`] REAL_LE_MUL2) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &h * &k /\ &0 <= &D * &h * &k` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[];
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`(&D + &1) * &h * &k`; `&56`;
                  `log(&q) * (&q pow K / &2 pow (K + 1))`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&3 * M + &15) * &L * &h + (M + &4) * &L * &N +
    &D * (&3 * M + &12) * &L * &h + &D * (M + &9) * &L * &R <= Z / &8`
  ASSUME_TAC THENL
   [ABBREV_TAC `U = &h * &q pow a * &q pow (K + 1)` THEN
    SUBGOAL_THEN `&1 <= &q pow a * &q pow (K + 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&h <= U /\ &R <= U /\ &N <= &5 * U /\ &1 <= U`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`&h`; `&1`; `&q pow a * &q pow (K + 1)`] REAL_LE_LMUL) THEN
      MP_TAC(SPECL [`&h * &q pow (K + 1)`; `&1`; `&q pow a`] REAL_LE_LMUL) THEN
      SUBGOAL_THEN `&0 <= &h * &q pow (K + 1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "U" THEN ASM_REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &2 * &D * &q pow lam` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&2 * &D * &q pow lam) * &h <= (&2 * &D * &q pow lam) * U /\
      (&2 * &D * &q pow lam) * &R <= (&2 * &D * &q pow lam) * U /\
      (&2 * &D * &q pow lam) * &N <= (&2 * &D * &q pow lam) * (&5 * U)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `Y = (&2 * &D * &q pow lam) * U` THEN
    SUBGOAL_THEN `&0 <= Y` ASSUME_TAC THENL
     [EXPAND_TAC "Y" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&L * &h <= Y /\ &L * &N <= &5 * Y /\ &L * &R <= Y`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o check ((=)
        `&L = &2 * &D * &q pow lam` o concl)) THEN
      EXPAND_TAC "Y" THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(&8 * M + &35 + &D * (&4 * M + &21)) * Y` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(&3 * M + &15) * (&L * &h) <= (&3 * M + &15) * Y`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(M + &4) * (&L * &N) <= (M + &4) * (&5 * Y)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(&D * (&3 * M + &12)) * (&L * &h) <= (&D * (&3 * M + &12)) * Y`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&D * (M + &9)) * (&L * &R) <= (&D * (M + &9)) * Y`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      REPLICATE_TAC 4 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(&68 * M pow 2) * Y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      SUBGOAL_THEN `&D * M <= M * M /\ M <= M * M /\ &1 <= M * M`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `&1 * M <= M * M ==> M <= M * M`) THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `Z / &8 = (&h * &q pow lam * &q pow a * &q pow K) *
               (((&D + &1) * &q pow 2 * log(&q)) / &2 pow (K + 1)) /\
      (&68 * M pow 2) * Y = (&h * &q pow lam * &q pow a * &q pow K) *
                            (&136 * M pow 2 * &D * &q)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [EXPAND_TAC "Z" THEN EXPAND_TAC "Y" THEN EXPAND_TAC "U" THEN
      FIRST_ASSUM(SUBST1_TAC o check ((=)
        `&k = &q pow lam * &q pow a * &q pow 2` o concl)) THEN
      FIRST_ASSUM(SUBST1_TAC o check ((=) `&a = &8 * (&D + &1)` o concl)) THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
      SUBGOAL_THEN `~(&2 pow K = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ];
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_2] THEN
    SUBGOAL_THEN `&0 <= M pow 2 * &2 pow K` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[REAL_POW_LE; REAL_LE_POW_2; REAL_POS];
      ALL_TAC] THEN
    MP_TAC(SPECL [`M pow 2 * &2 pow K`; `&D`; `M:real`] REAL_LE_LMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&272 * (M pow 2 * &2 pow K) * &D <= &q` ASSUME_TAC THENL
     [UNDISCH_TAC `&2176 * M pow 3 * &2 pow K <= &q` THEN
      REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow] THEN
      SUBGOAL_THEN `&0 <= M * M pow 2 * &2 pow K` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`&272 * (M pow 2 * &2 pow K) * &D`; `&q`; `&q`]
                 REAL_LE_RMUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&1 <= (&D + &1) * log(&q)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&1`; `(&D + &1) * log(&q)`; `&q * &q`] REAL_LE_RMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Z` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV) THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPLICATE_TAC 5 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemma 7: the exponent baker_l7 of the Liouville bound against the         *)
(* extrapolation exponent at the last step J.                                *)
(* ------------------------------------------------------------------------- *)

let BAKER_L7_BOUND = prove
 (`!M D n L k h X7 lmax lk.
     1 <= n /\ 1 <= D /\ &D <= M /\ &n <= M /\ 1 <= h /\ 1 <= L /\
     1 <= k /\ &k <= &L pow (n + 2) /\ &1 <= lk /\
     &X7 <= &h * &3 pow (n + 1) * &L pow (n + 1) /\
     &lmax <= &h * &3 pow (n + 1) * &L pow (n + 1)
     ==> baker_l7 M D n L k h X7 lmax lk + &6 * &h * &L * lk + &2
         <= (&8 * M + &75) * &D * &k pow n * &3 pow (n + 1) * &h *
            &L pow (n + 2) * lk`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[baker_l7] THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &L /\ &1 <= &k /\ &1 <= &D /\ &1 <= M`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    TRANS_TAC REAL_LE_TRANS `&D` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &3 pow (n + 1) /\ &1 <= &L pow (n + 1) /\
                &1 <= &L pow (n + 2) /\ &1 <= &k pow n`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `G = &h * &L pow (n + 2) * lk * &3 pow (n + 1)` THEN
  SUBGOAL_THEN `&L <= &L pow (n + 2)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= lk * &3 pow (n + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &h * &L pow (n + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&h * &L pow (n + 2) <= G` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&h * &L pow (n + 2)`; `&1`; `lk * &3 pow (n + 1)`]
                 REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; EXPAND_TAC "G" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&h <= G /\ &L * &h <= G /\ &h * &k <= G /\ &0 <= G`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&h * &1 <= &h * &L pow (n + 2) /\
                  &h * &L <= &h * &L pow (n + 2) /\
                  &h * &k <= &h * &L pow (n + 2)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&h * &L * lk <= G` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &h * lk /\ &0 <= &h * &L pow (n + 2) * lk`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`&h * &L pow (n + 2) * lk`; `&1`; `&3 pow (n + 1)`]
                 REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`&h * lk`; `&L`; `&L pow (n + 2)`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    EXPAND_TAC "G" THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&L * &X7 <= G /\ &L * &lmax <= G` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&h * &3 pow (n + 1) * &L pow (n + 2) <= G` ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN
      MP_TAC(SPECL [`&h * &3 pow (n + 1) * &L pow (n + 2)`; `&1`; `lk:real`]
                   REAL_LE_LMUL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN
         CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&L * (&h * &3 pow (n + 1) * &L pow (n + 1)) =
                  &h * &3 pow (n + 1) * &L pow (n + 2)` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1)`; real_pow] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&L * (&h * &3 pow (n + 1) * &L pow (n + 1))` THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
       ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `&L * &lmax * (&n * (lk + &1) + M) <= (&3 * M) * G`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&n * (lk + &1) + M <= &3 * M * lk` ASSUME_TAC THENL
     [SUBGOAL_THEN `&n * lk <= M * lk /\ &n <= M * lk /\ M <= M * lk`
      MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(REAL_ARITH `M * &1 <= M * lk ==> M <= M * lk`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `M * &1 <= M * lk ==> M <= M * lk`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &n * (lk + &1) + M /\ &0 <= &L *
      &lmax` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`&L * &lmax`; `&h * &3 pow (n + 1) * &L pow (n + 2)`;
                  `&n * (lk + &1) + M`; `&3 * M * lk`] REAL_LE_MUL2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&L * (&h * &3 pow (n + 1) * &L pow (n + 1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1)`; real_pow] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "G" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = (&n + &1) * &h + (&3 * M + &12) * &L * &h + &43 * &h * &k +
                  &6 * &h * &L * lk + &6 * &L * &X7 +
                  &L * &lmax * (&n * (lk + &1) + M)` THEN
  SUBGOAL_THEN `B <= (&8 * M + &67) * G` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SUBGOAL_THEN `(&n + &1) * &h <= (&2 * M) * G /\
                  (&3 * M + &12) * (&L * &h) <= (&3 * M + &12) * G`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ASSUME `&h * &k <= G`) THEN MP_TAC(ASSUME `&h * &L * lk <= G`) THEN
    MP_TAC(ASSUME `&L * &X7 <= G`) THEN
    MP_TAC(ASSUME `&L * &lmax * (&n * (lk + &1) + M) <= (&3 * M) * G`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &D * &k pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&D * &k pow n) * ((&8 * M + &67) * G) + &8 * G` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `a <= b /\ x + &2 <= &8 * g ==> a + x + &2 <= b + &8 * g`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ASSUME `&h * &L * lk <= G`) THEN MP_TAC(ASSUME `&h <= G`) THEN
      MP_TAC(ASSUME `&1 <= &h`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 * G <= (&D * &k pow n) * (&8 * G)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * x <= y * x ==> x <= y * x`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "G" THEN POP_ASSUM MP_TAC THEN EXPAND_TAC "G" THEN
  REAL_ARITH_TAC);;

let BAKER_J_EXP = prove
 (`!n D. baker_J n D + baker_c D * (n + 1) =
         (baker_c D * (n + 1)) * n + (baker_c D * n) * (n + 2) + (baker_c D +
           2)`,
  REWRITE_TAC[baker_J] THEN CONV_TAC NUM_RING);;

let BAKER_POW6_LE = prove
 (`!M D n. 1 <= D /\ &D <= M
           ==> &D * &3 pow (n + 1) * &2 pow (n + 2) * &D pow (n + 2) <=
               (&6 * M) pow (n + 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &D /\ &1 <= M` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    TRANS_TAC REAL_LE_TRANS `&D` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&6 * M) pow (n + 3) =
                (&6 * M) * &3 pow (n + 2) * &2 pow (n + 2) * M pow (n + 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n + 3 = SUC(n + 2)`; real_pow] THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_ARITH `&6 = &3 * &2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 pow (n + 1) <= &3 pow (n + 2) /\ &D pow (n + 2) <=
    M pow (n + 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
       ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_POS]; ASM_REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[REAL_POW_LE; REAL_POS]; ASM_REWRITE_TAC[];
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  ASM_REWRITE_TAC[]);;

let BAKER_KL_LE = prove
 (`!n D q. 1 <= n /\ 1 <= D /\ 1 <= q
           ==> &(baker_kpar n D q) <= &(baker_Lpar n D q) pow (n + 2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BAKER_LPAR_REAL; baker_kpar; GSYM REAL_OF_NUM_POW] THEN
  TRANS_TAC REAL_LE_TRANS `(&q pow (baker_c D * n)) pow (n + 2)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_POW] THEN
    REWRITE_TAC[REAL_POW_POW] THEN MATCH_MP_TAC REAL_POW_MONO THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN
    REWRITE_TAC[LE_REFL] THEN
    MP_TAC(SPEC `n:num` LE_SQUARE_REFL) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * x <= y ==> x <= y`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

let BAKER_X7_LE = prove
 (`!h L n. 1 <= L
           ==> &(h * (L + 2) EXP (n + 1)) <= &h * &3 pow (n + 1) * &L pow (n +
             1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW;
              GSYM REAL_OF_NUM_ADD] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

let BAKER_LMAX_LE = prove
 (`!h L n. 1 <= L
           ==> &(h * (L + 2) * (L + 1) EXP n) <=
               &h * &3 pow (n + 1) * &L pow (n + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW;
              GSYM REAL_OF_NUM_ADD] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
  DISCH_TAC THEN
  REWRITE_TAC[ADD1; REAL_POW_ADD; REAL_POW_1] THEN
  TRANS_TAC REAL_LE_TRANS `(&3 * &L) * (&3 * &L) pow n` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]);;

let BAKER_LW_POS = prove
 (`!M D L k h R. &0 <= M /\ 1 <= h ==> &0 <= baker_lw M D L k h R`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_lw] THEN
  SUBGOAL_THEN `&0 <= log((&R + &h) / &h)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN
    SUBGOAL_THEN `&0 < &h` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_REAL_ARITH_TAC);;

let BAKER_L7_POWER_NUM = prove
 (`!M D n q h.
     1 <= n /\ 1 <= D /\ &D <= M /\ 1 <= h /\ 4 <= q /\ &1 <= log(&q) /\
     &(baker_c D * (n + 1)) * (&8 * M + &75) * (&6 * M) pow (n + 3) *
     &2 pow (baker_J n D + 1) <= &q
     ==> (&8 * M + &75) * &D * &(baker_kpar n D q) pow n * &3 pow (n + 1) *
         &h * &(baker_Lpar n D q) pow (n + 2) *
         (&(baker_c D * (n + 1)) * log(&q))
         <= (&(h * q EXP baker_J n D) *
             &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) *
             &(baker_a D) * log(&q)) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&q pow (baker_J n D) * &q pow (baker_c D * (n + 1)) =
    &q pow ((baker_c D * (n + 1)) * n) * &q pow ((baker_c D * n) * (n + 2)) *
    &q pow (baker_c D + 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD; BAKER_J_EXP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&(baker_kpar n D q) <=
    &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) * &2 pow (baker_J n D)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`baker_kpar n D q`; `2 EXP baker_J n D`] REAL_DIV_SUC_LE) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ; GSYM REAL_OF_NUM_POW] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(h * q EXP baker_J n D) = &h * &q pow (baker_J n D)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW]; ALL_TAC] THEN
  REWRITE_TAC[BAKER_LPAR_REAL] THEN
  SUBGOAL_THEN `&(baker_kpar n D q) = &q pow (baker_c D * (n + 1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[baker_kpar; REAL_OF_NUM_POW]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `(&q pow (baker_c D * (n + 1))) pow n =
    &q pow ((baker_c D * (n + 1)) * n) /\
    (&2 * &D * &q pow (baker_c D * n)) pow (n + 2) =
    &2 pow (n + 2) * &D pow (n + 2) * &q pow ((baker_c D * n) * (n + 2))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[REAL_POW_POW; REAL_POW_MUL]; ALL_TAC] THEN
  MP_TAC(SPECL [`M:real`; `D:num`; `n:num`] BAKER_POW6_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&q <= &q pow (baker_c D + 2) * &(baker_a D)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&q pow (baker_c D + 2)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &1 * x <= y * x ==> x <= x * y`) THEN
      CONJ_TAC THENL [SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      REWRITE_TAC[REAL_OF_NUM_LE; baker_a] THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `A = &q pow ((baker_c D * (n + 1)) * n)` THEN
  ABBREV_TAC `B = &q pow ((baker_c D * n) * (n + 2))` THEN
  ABBREV_TAC `C = &q pow (baker_c D + 2)` THEN
  ABBREV_TAC `P = &q pow (baker_J n D)` THEN
  ABBREV_TAC `Kq = &q pow (baker_c D * (n + 1))` THEN
  ABBREV_TAC `Tj = &2 pow (baker_J n D)` THEN
  ABBREV_TAC `s = &(baker_kpar n D q DIV 2 EXP baker_J n D + 1)` THEN
  ABBREV_TAC `kr = &(baker_c D * (n + 1))` THEN
  ABBREV_TAC `ar = &(baker_a D)` THEN
  ABBREV_TAC `lq = log(&q)` THEN
  ABBREV_TAC `W = &D * &3 pow (n + 1) * &2 pow (n + 2) * &D pow (n + 2)` THEN
  ABBREV_TAC `V = (&6 * M) pow (n + 3)` THEN
  SUBGOAL_THEN `&0 < Tj` ASSUME_TAC THENL
   [EXPAND_TAC "Tj" THEN SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A /\ &0 <= B` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= kr /\ &1 <= ar` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kr"; "ar"] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; baker_c; baker_a] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s /\ &1 <= &h` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow (baker_J n D + 1) = &2 * Tj` ASSUME_TAC THENL
   [EXPAND_TAC "Tj" THEN REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&8 * M + &75) * kr * W * (&2 * Tj) <= C * ar` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&q` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `kr * (&8 * M + &75) * V * &2 pow (baker_J n D + 1)` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check ((=)
      `&2 pow (baker_J n D + 1) = &2 * Tj` o concl)) THEN
    SUBGOAL_THEN `&0 <= (&8 * M + &75) * kr * (&2 * Tj)` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`(&8 * M + &75) * kr * (&2 * Tj)`; `W:real`; `V:real`]
                 REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&8 * M + &75) * &D * A * &3 pow (n + 1) * &h *
    (&2 pow (n + 2) * &D pow (n + 2) * B) * (kr * lq) =
    ((&8 * M + &75) * kr * W) * (&h * lq * A * B)`
  SUBST1_TAC THENL [EXPAND_TAC "W" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &h * lq * A * B` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&8 * M + &75) * kr * W <= (C * ar) / (&2 *
    Tj)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < t ==> &0 < &2 * t`] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((C * ar) / (&2 * Tj)) * (&h * lq * A * B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((C * ar) / (&2 * Tj)) * (&h * lq * A * B) =
                (&h * ar * lq * (A * B * C)) / (&2 * Tj)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < Tj` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check ((=) `(P:real) * Kq = A * B *
    C` o concl)) THEN
  SUBGOAL_THEN `(Kq:real) <= s * Tj` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check ((=) `&(baker_kpar n D q) =
     Kq` o concl)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&h * ar * lq * (P * (s * Tj))) / (&2 * Tj)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * Tj /\ &0 <= P` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "P" THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_LE_DIV2_EQ th]) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  UNDISCH_TAC `&0 < Tj` THEN CONV_TAC REAL_FIELD);;

let BAKER_LEMMA7_NUM = prove
 (`!M D n q h.
     1 <= n /\ 1 <= D /\ &D <= M /\ &n <= M /\ 1 <= h /\ 4 <= q /\
     &112 <= log(&q) /\
     &2176 * M pow 3 * &2 pow (baker_J n D) <= &q /\
     &(baker_c D * (n + 1)) * (&8 * M + &75) * (&6 * M) pow (n + 3) *
     &2 pow (baker_J n D + 1) <= &q
     ==> baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h
                  (4 * q EXP baker_a D * (h * q EXP baker_J n D) + 1) + &1 +
         (baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h
                   (h * (baker_Lpar n D q + 2) EXP (n + 1))
                   (h * (baker_Lpar n D q + 2) * (baker_Lpar n D q + 1) EXP n)
                   (&(baker_c D * (n + 1)) * log(&q)) +
          &6 * &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) * log(&q)) +
          &2)
         <= &(h * q EXP baker_J n D) *
            &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) *
            &(baker_a D) * log(&q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= baker_J n D` ASSUME_TAC THENL
   [REWRITE_TAC[baker_J] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= M` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&D` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`M:real`; `D:num`; `n:num`; `q:num`; `h:num`;
                `baker_J n D - 1`] BAKER_STEP_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&2176 * M pow 3 * &2 pow (baker_J n D)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `baker_J n D - 1 + 1 = baker_J n D` SUBST1_TAC THENL
   [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `1 <= baker_Lpar n D q /\ 1 <= baker_kpar n D q`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[baker_Lpar; baker_kpar; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                MULT_EQ_0; EXP_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`M:real`; `D:num`; `n:num`; `baker_Lpar n D q`;
                `baker_kpar n D q`; `h:num`;
                `h * (baker_Lpar n D q + 2) EXP (n + 1)`;
                `h * (baker_Lpar n D q + 2) * (baker_Lpar n D q + 1) EXP n`;
                `&(baker_c D * (n + 1)) * log(&q)`] BAKER_L7_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[BAKER_X7_LE; BAKER_LMAX_LE; BAKER_KL_LE;
                 ARITH_RULE `4 <= q ==> 1 <= q`] THEN
    MATCH_MP_TAC REAL_LE_1_MUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; baker_c; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                MULT_EQ_0] THEN ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`M:real`; `D:num`; `n:num`; `q:num`; `h:num`]
               BAKER_L7_POWER_NUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`M:real`; `D:num`; `baker_Lpar n D q`; `baker_kpar n D q`;
                `h:num`; `h * q EXP baker_J n D`] BAKER_LW_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&(h * q EXP baker_J n D) = &q * &(h * q EXP (baker_J n D - 1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `q EXP baker_J n D = q * q EXP (baker_J n D - 1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL] THEN AP_TERM_TAC THEN
      REWRITE_TAC[MULT_AC]];
    ALL_TAC] THEN
  ABBREV_TAC `X = &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) *
                  &(baker_a D) * log(&q)` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Y = &(h * q EXP (baker_J n D - 1))` THEN
  SUBGOAL_THEN `&0 <= Y * X /\ &4 * (Y * X) <= &q * (Y * X)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= Y` ASSUME_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=)
    `&(h * q EXP baker_J n D) = &q * Y` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let c = concl th in is_binary "real_le" c &&
      not (is_var (rand c)) &&
      (can (find_term (fun t -> try fst(dest_const t) = "baker_lu"
                       with Failure _ -> false)) c ||
       can (find_term (fun t -> try fst(dest_const t) = "baker_l7"
                       with Failure _ -> false)) c ||
       can (find_term (fun t -> try fst(dest_const t) = "baker_lw"
                       with Failure _ -> false)) c ||
       c = `&4 * (Y * X) <= &q * (Y * X)` ||
       can (find_term ((=) `&8 * M + &75`)) c)))) THEN
  MP_TAC(ASSUME `&0 <= Y * X`) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Exponential bounds for the error terms of the extrapolation.              *)
(* ------------------------------------------------------------------------- *)

let EXP_BOUND_MUL = prove
 (`!x y a b. &0 <= x /\ x <= exp a /\ &0 <= y /\ y <= exp b
             ==> x * y <= exp(a + b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let EXP_BOUND_POW = prove
 (`!x a m. &0 <= x /\ x <= exp a ==> x pow m <= exp(&m * a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_N] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]);;

let EXP_BOUND_MUL5 = prove
 (`!x1 x2 x3 x4 x5 a1 a2 a3 a4 a5.
     &0 <= x1 /\ x1 <= exp a1 /\ &0 <= x2 /\ x2 <= exp a2 /\
     &0 <= x3 /\ x3 <= exp a3 /\ &0 <= x4 /\ x4 <= exp a4 /\
     &0 <= x5 /\ x5 <= exp a5
     ==> x1 * x2 * x3 * x4 * x5 <= exp(a1 + a2 + a3 + a4 + a5)`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC EXP_BOUND_MUL THEN ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL
          [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN
            ASM_REWRITE_TAC[]); ALL_TAC]) THEN
  ASM_REWRITE_TAC[]);;

let REAL_TWO_LE_EXP_1 = prove
 (`&2 <= exp(&1)`,
  MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

let REAL_NUM_MUL_16_POW_LE_EXP = prove
 (`!y. &y * &16 pow y <= exp(&y + &4 * &y)`,
  GEN_TAC THEN MATCH_MP_TAC EXP_BOUND_MUL THEN
  REWRITE_TAC[REAL_POS; REAL_LE_EXP_SELF] THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MP_TAC(SPEC `4 * y` REAL_TWO_POW_LE_EXP) THEN
  REWRITE_TAC[GSYM REAL_POW_POW; GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let BAKER_TERM2_EXP_LE = prove
 (`!x y s n. &2 * &x * &2 pow s * exp(&n) * (&y * &16 pow y) pow (s + 1) <=
             exp(&1 + &x + &s + &n + &5 * &y * (&s + &1))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&5 * &y * (&s + &1) = &(s + 1) * (&y + &4 * &y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EXP_BOUND_MUL5 THEN
  REWRITE_TAC[REAL_POS; REAL_TWO_LE_EXP_1; REAL_LE_EXP_SELF;
              REAL_TWO_POW_LE_EXP; REAL_EXP_POS_LE; REAL_LE_REFL] THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_MUL] THEN
  MATCH_MP_TAC EXP_BOUND_POW THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS;
           REAL_NUM_MUL_16_POW_LE_EXP]);;

let BAKER_TERM12_EXP_LE = prove
 (`!k x s n. &2 * &k * &x * (&2 * &k) pow s * exp(&n) *
             (&x * &16 pow x) pow (s + 1) <=
             exp(&1 + &k + &x + &s * (&1 + &k) + &n + &5 * &x * (&s + &1))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `&1 + &k + &x + &s * (&1 + &k) + &n + &5 * &x * (&s + &1) =
    (&1 + &k) + &x + &s * (&1 + &k) + &n + &(s + 1) * (&x + &4 * &x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * &k * &x * (&2 * &k) pow s * exp(&n) * (&x * &16 pow x) pow (s + 1) =
    (&2 * &k) * &x * (&2 * &k) pow s * exp(&n) * (&x * &16 pow x) pow (s + 1)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &k <= exp(&1 + &k)` ASSUME_TAC THENL
   [MATCH_MP_TAC EXP_BOUND_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_TWO_LE_EXP_1; REAL_LE_EXP_SELF];
    ALL_TAC] THEN
  MATCH_MP_TAC EXP_BOUND_MUL5 THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_EXP_SELF; REAL_EXP_POS_LE;
                  REAL_LE_REFL] THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_MUL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXP_BOUND_POW THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
    MATCH_MP_TAC EXP_BOUND_POW THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS;
             REAL_NUM_MUL_16_POW_LE_EXP]]);;

(* ------------------------------------------------------------------------- *)
(* The simple conditions: positivity, the Siegel condition,                  *)
(* L Lam < 2 pi k, X7 <= R_J, S_(K+1) <= S_K / 2 and the crude               *)
(* bound for the extrapolation exponents.                                    *)
(* ------------------------------------------------------------------------- *)

let BAKER_PAR_POS = prove
 (`!n D q. 1 <= D /\ 1 <= q
           ==> 1 <= baker_Lpar n D q /\ 1 <= baker_kpar n D q`,
  REWRITE_TAC[baker_Lpar; baker_kpar; ARITH_RULE `1 <= x <=> ~(x = 0)`;
              MULT_EQ_0; EXP_EQ_0] THEN ARITH_TAC);;

let BAKER_C_POS = prove
 (`!D. 1 <= baker_c D`,
  REWRITE_TAC[baker_c] THEN ARITH_TAC);;

let BAKER_L_LE_K = prove
 (`!n D q. 1 <= q /\ 2 * D <= q ==> baker_Lpar n D q <= baker_kpar n D q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_Lpar; baker_kpar] THEN
  SUBGOAL_THEN `baker_c D * (n + 1) = baker_c D + baker_c D * n`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; MULT_ASSOC] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
  TRANS_TAC LE_TRANS `q:num` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
  REWRITE_TAC[LE_EXP] THEN
  MP_TAC(SPEC `D:num` BAKER_C_POS) THEN ASM_ARITH_TAC);;

let BAKER_SIEGEL_NUM = prove
 (`!n D q. 1 <= n /\ 1 <= D /\ 1 <= q
           ==> 2 * D * (baker_kpar n D q + 1) EXP n <=
               (baker_Lpar n D q + 1) * (baker_Lpar n D q + 1) EXP n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `D:num`; `q:num`] BAKER_PAR_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TRANS_TAC LE_TRANS `2 * D * (2 * baker_kpar n D q) EXP n` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS `baker_Lpar n D q * baker_Lpar n D q EXP n` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
     [ARITH_TAC; MATCH_MP_TAC EXP_MONO_LE_IMP THEN ARITH_TAC]] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW; BAKER_LPAR_REAL] THEN
  REWRITE_TAC[baker_kpar; GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN
  SUBGOAL_THEN
   `&q pow ((baker_c D * (n + 1)) * n) =
    &q pow (baker_c D * n) * &q pow ((baker_c D * n) * n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN CONV_TAC NUM_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &D pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &2 * &D * &2 pow n * &q pow (baker_c D * n) *
          &q pow ((baker_c D * n) * n)`
  ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&2 * &D * &2 pow n * &q pow (baker_c D * n) *
                 &q pow ((baker_c D * n) * n)`; `&1`; `&D pow n`]
               REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let BAKER_LLAM_LT = prove
 (`!n D q Lam. 1 <= q /\ &0 <= Lam /\ &2 * &D * Lam <= &q
               ==> &(baker_Lpar n D q) * Lam < &2 * pi * &(baker_kpar n D q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BAKER_LPAR_REAL; baker_kpar] THEN
  SUBGOAL_THEN `&1 <= &q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `baker_c D * (n + 1) = baker_c D + baker_c D * n`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_POW_ADD] THEN
  SUBGOAL_THEN `&q <= &q pow baker_c D` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; BAKER_C_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &q pow (baker_c D * n)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC PI_APPROX_32 THEN
  MP_TAC(SPECL [`&q pow (baker_c D * n)`; `&2 * &D * Lam`;
                `&q pow baker_c D`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&q pow (baker_c D * n) * &q pow baker_c D`; `&1`; `pi`]
               REAL_LE_LMUL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q pow (baker_c D * n) * &q pow baker_c D` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let BAKER_X7_LE_R = prove
 (`!n D q h. 1 <= n /\ 1 <= D /\ 6 * D <= q
             ==> h * (baker_Lpar n D q + 2) EXP (n + 1) <= h *
               q EXP baker_J n D`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
  TRANS_TAC LE_TRANS `(q EXP (baker_c D * n + 1)) EXP (n + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EXP_MONO_LE_IMP THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN
    REWRITE_TAC[baker_Lpar] THEN
    SUBGOAL_THEN `1 <= q EXP (baker_c D * n)` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`q EXP (baker_c D * n)`, `x:num`) THEN GEN_TAC THEN
    DISCH_TAC THEN
    TRANS_TAC LE_TRANS `6 * D * x` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `1 <= D * x` MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= y ==> 1 <= y`) THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
        ARITH_TAC];
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXP_EXP] THEN
    REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISJ2_TAC THEN REWRITE_TAC[baker_J] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
    MP_TAC(SPEC `n:num` LE_SQUARE_REFL) THEN
    MP_TAC(SPEC `D:num` BAKER_C_POS) THEN
    SPEC_TAC(`baker_c D`, `c:num`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `n <= c * n` MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `1 * n <= x ==> n <= x`) THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    ARITH_TAC]);;

let BAKER_S_HALF = prove
 (`!k K. 2 * (k DIV 2 EXP (K + 1)) <= k DIV 2 EXP K`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXP_ADD; EXP_1; GSYM DIV_DIV] THEN
  MP_TAC(SPECL [`k DIV 2 EXP K`; `2`] DIV_MUL_LE) THEN ARITH_TAC);;

let BAKER_ZBOUND = prove
 (`!D n q h K m.
     1 <= D /\ 8 * D + 8 <= q /\ K <= baker_J n D
     ==> &(h * q EXP K) * &(baker_kpar n D q DIV 2 EXP m + 1) *
         &(baker_a D) * log(&q)
         <= &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &q /\ &2 <= &q /\ &0 < &q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow K <= &q pow (baker_J n D)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&(baker_kpar n D q DIV 2 EXP m + 1) <= &2 * &q pow (baker_c D * (n + 1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM baker_kpar; REAL_OF_NUM_POW] THEN
    SUBGOAL_THEN `1 <= baker_kpar n D q` MP_TAC THENL
     [MP_TAC(SPECL [`n:num`; `D:num`; `q:num`] BAKER_PAR_POS) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MP_TAC(SPECL [`baker_kpar n D q`; `2 EXP m`] DIV_LE) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(baker_a D) <= &q /\ log(&q) <= &q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_LE_SELF; baker_a; REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&h * &q pow (baker_J n D)) * (&2 * &q pow (baker_c D * (n + 1))) *
    &q * &q` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_POS]; ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `3 = SUC(SUC(SUC 0))`; real_pow] THEN
  SUBGOAL_THEN
   `&0 <= &h * &q pow (baker_J n D) * &q pow (baker_c D * (n + 1)) * &q * &q`
  ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`&h * &q pow (baker_J n D) * &q pow (baker_c D * (n + 1)) * &q * &q`;
    `&2`; `&q`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The exponent e1 of eps, the unit U = h q^(c (n+1) + J + 3) and small      *)
(* facts about exp and powers.                                               *)
(* ------------------------------------------------------------------------- *)

let baker_e1 = new_definition
 `baker_e1 n D = baker_c D * (n + 1) + baker_J n D + 4`;;

let REAL_EXP_3_GE_16 = prove
 (`&16 <= exp(&3)`,
  MP_TAC E_APPROX_32 THEN
  REWRITE_TAC[REAL_ARITH `abs(x - a) <= e <=> a - e <= x /\ x <= a + e`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBST1_TAC(REAL_ARITH `&3 = &3 * &1`) THEN REWRITE_TAC[REAL_EXP_N] THEN
  TRANS_TAC REAL_LE_TRANS `(&13 / &5) pow 3` THEN
  CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

let REAL_EXP_2_GT_3 = prove
 (`&3 < exp(&2)`,
  MP_TAC REAL_TWO_LE_EXP_1 THEN
  SUBST1_TAC(REAL_ARITH `&2 = &2 * &1`) THEN REWRITE_TAC[REAL_EXP_N] THEN
  DISCH_TAC THEN TRANS_TAC REAL_LTE_TRANS `&2 pow 2` THEN
  CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

let BAKER_INV_POW_EXP = prove
 (`!q a m. 1 <= q ==> inv(&q pow a) pow m = exp(--(&m * &a * log(&q)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EXP_NEG; REAL_EXP_N; EXP_LOG; REAL_POW_INV]);;

let BAKER_KPOW_LE = prove
 (`!k h L. 1 <= k /\ 1 <= L
           ==> &k pow (2 * h * (L + 2)) <= exp(&6 * &h * &L * log(&k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &k /\ &0 <= log(&k)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM(MATCH_MP EXP_LOG
    (ASSUME `&0 < &k`))] THEN
  REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_LE] o
    check (fun th -> concl th = `1 <= L`)) THEN
  MP_TAC(SPEC `h:num` REAL_POS) THEN
  SPEC_TAC(`&h`, `x:real`) THEN SPEC_TAC(`&L`, `y:real`) THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x * (&4 * y - &4) ==> &2 * x * (y + &2) <= (&6 * x) * y`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let BAKER_KAP_LE_J = prove
 (`!n D. 1 <= n ==> baker_c D * (n + 1) <= baker_J n D`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_J] THEN
  MATCH_MP_TAC(ARITH_RULE `x <= y ==> x <= y + 2`) THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
  MP_TAC(SPEC `n:num` LE_SQUARE_REFL) THEN ASM_ARITH_TAC);;

let BAKER_UNITS = prove
 (`!n D q h.
     1 <= n /\ 16 <= q /\ 1 <= h
     ==> &1 <= &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3) /\
         &16 * (&h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)) <=
         &q pow baker_e1 n D * &h /\
         (!K. K <= baker_J n D
              ==> &(h * q EXP K) <=
                  &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)) /\
         &(baker_kpar n D q) <=
         &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3) /\
         &5 * &(h * q EXP baker_J n D) * (&(baker_kpar n D q) + &1) <=
         &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3) /\
         &2 * &(h * q EXP baker_J n D) * &(baker_kpar n D q) <=
         &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3) /\
         &(baker_kpar n D q) * (&1 + &(baker_kpar n D q)) <=
         &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[baker_kpar; baker_e1; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MP_TAC(SPECL [`n:num`; `D:num`] BAKER_KAP_LE_J) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`baker_J n D`, `J:num`) THEN
  SPEC_TAC(`baker_c D * (n + 1)`, `kap:num`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&16 <= &q /\ &1 <= &q /\ &1 <= &h` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A = &q pow kap` THEN ABBREV_TAC `B = &q pow J` THEN
  SUBGOAL_THEN `&1 <= A /\ &1 <= B /\ A <= B` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_POW_MONO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow (kap + J + 4) = &q pow (kap + J + 3) * &q`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `kap + J + 4 = SUC(kap + J + 3)`; real_pow] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow (kap + J + 3) = A * B * &q pow 3` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4096 <= &q pow 3` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&16 pow 3` THEN
    CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C = &q pow 3` THEN
  SUBGOAL_THEN `&1 <= A * B /\ &1 <= &h * A * B /\ A * A <= A * B /\
                &0 <= &h * A * B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4096 * (&h * A * B) <= (&h * A * B) * C` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(x:real) * a <= x * b ==> a * x <= x * b`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `A * &1 <= A * B /\ &1 * (A * B) <= &h * (A * B) /\
                (&h * B) * &1 <= (&h * B) * A /\ &1 * A <= (&h * B) * A`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 * (&h * A * B * C) <= (&h * A * B * C) *
    &q` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(x:real) * a <= x * b ==> a * x <= x * b`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&q pow K <= B` ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&h * &q pow K <= &h * B` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The numeric core: all numeric hypotheses of BAKER_CORE_PARAMETRIC         *)
(* hold for the explicit parameters.                                         *)
(* ------------------------------------------------------------------------- *)

let BAKER_CORE_NUMERIC = prove
 (`!n lg theta V (g:num->(num->complex)->complex) e G a d H beta
    Bb Lam d0 lmin Gn M q h.
    1 <= n /\ &1 <= G /\ FINITE V /\ (1..n) SUBSET V /\
    (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
    (!j. j <= n ==> intpoly V e G (g j)) /\
    ~(g n theta = Cx(&0)) /\ norm(g n theta) <= Gn /\ &1 <= Gn /\
    (!j. j < n ==> beta j * g n theta = --(g j theta)) /\
    (!r. r IN V
         ==> 1 <= d r /\ &1 <= H r /\
             (!j. integer(a r j) /\ abs(a r j) <= H r) /\
             ~(a r (d r) = &0) /\
             vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
    (!b. (!r. r IN 1..n
              ==> integer(b r) /\
                  abs(b r) <= &(baker_Lpar n (nproduct V d) q)) /\
         vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
         ==> !r. r IN 1..n ==> b r = &0) /\
    &1 <= Bb /\ (!j. j < n ==> norm(beta j) <= Bb) /\
    &1 <= Lam /\ (!r. r IN 1..n ==> norm(lg r) <= Lam) /\
    sum(1..n) (\r. norm(lg r)) <= Lam /\
    &0 < lmin /\ lmin <= &1 /\ (!r. r IN 1..n ==> lmin <= norm(lg r)) /\
    &n <= M /\ &(nproduct V d) <= M /\ Lam <= M /\
    sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= M /\
    log(inv lmin) <= M /\
    &112 <= log(&q) /\
    &2176 * M pow 3 * &2 pow (baker_J n (nproduct V d)) <= &q /\
    &(baker_c (nproduct V d) * (n + 1)) * (&8 * M + &75) *
    (&6 * M) pow (n + 3) * &2 pow (baker_J n (nproduct V d) + 1) <= &q /\
    1 <= h /\ M <= &h /\
    log(&(baker_kpar n (nproduct V d) q)) <= &h /\
    log G <= &h /\ log Bb <= &h /\ log Gn <= &h /\
    sum V (\r. &(e r) * log(&(d r + 1) * H r pow 3)) <= &h /\
    norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n) <= d0 /\
    d0 <= exp(--(&q pow (baker_e1 n (nproduct V d) + 1) * &h))
    ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = nproduct V (d:num->num)` THEN
  SUBGOAL_THEN
   `1 <= D`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[ARITH_RULE `1 <= x <=> 0 < x`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= x ==> 0 < x`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= M /\ &0 <= M`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= x /\ &0 <= x`) THEN
    TRANS_TAC REAL_LE_TRANS `&D` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `16 <= q /\ 8 * D + 8 <= q /\ 6 * D <= q /\ 2 * D <= q /\ 1 <= q /\ 4 <= q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&16 * &D + &16 <= &q` MP_TAC THENL
     [SUBGOAL_THEN `M <= M pow 3 /\ M pow 3 <= M pow 3 * &2 pow baker_J n D`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow] THEN
          MATCH_MP_TAC(REAL_ARITH `M * &1 <= M * y ==> M <= M * y`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE_1];
          MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * y ==> x <= x * y`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          SIMP_TAC[REAL_POW_LE; ASSUME `&0 <= M`] THEN
          MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * &D * Lam <= &q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&D * Lam <= M * M /\ M * M <= M pow 3 /\
                  M pow 3 <= M pow 3 * &2 pow baker_J n D /\ &0 <= M * M`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow; REAL_POW_2] THEN
        MATCH_MP_TAC(REAL_ARITH `&1 * x <= M * x ==> x <= M * x`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL];
        MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * y ==> x <= x * y`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        SIMP_TAC[REAL_POW_LE; ASSUME `&0 <= M`] THEN
        MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_SQUARE]];
      ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `1 <= baker_Lpar n D q /\ 1 <= baker_kpar n D q /\ baker_Lpar n D q <=
     baker_kpar n D q`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BAKER_PAR_POS; BAKER_L_LE_K]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= d0 /\ d0 <= &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((beta:num->complex) 0 +
                       vsum(1..n-1) (\r. beta r * (lg:num->complex) r) -
                       lg n)` THEN
      ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp(--(&q pow (baker_e1 n D + 1) * &h))` THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE; REAL_NEG_LE0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
        SIMP_TAC[REAL_POW_LE; REAL_POS]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `2 * D * (baker_kpar n D q + 1) EXP n <= (baker_Lpar n D q + 1) *
     (baker_Lpar n D q + 1) EXP n`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_SIEGEL_NUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= baker_pbound n h (baker_Lpar n D q) (baker_kpar n D q) V G H e /\
     log(baker_pbound n h (baker_Lpar n D q) (baker_kpar n D q) V G H e) <=
     &43 * &h * &(baker_kpar n D q) + (&2 * M + &10) * &(baker_Lpar n D q) *
     &h`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_PBOUND_LOG_LE THEN ASM_REWRITE_TAC[] THEN
     EXISTS_TAC `d:num->num` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!N. baker_ub n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
     (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam (N) <=
     exp(baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (N))`
  STRIP_ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`n:num`; `h:num`; `baker_Lpar n D q`; `baker_kpar n D q`;
      `baker_pbound n h (baker_Lpar n D q) (baker_kpar n D q) V G H e`;
      `Bb:real`;
                   `Lam:real`; `N:num`; `M:real`] BAKER_UB_LOG_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <
      baker_ub n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
      (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam (N)` ASSUME_TAC
      THENL
     [REWRITE_TAC[baker_ub] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `exp(log(baker_ub n h (baker_Lpar n D q)
      (baker_kpar n D q) (baker_pbound n h (baker_Lpar n D q) (baker_kpar n D
      q) V G H e) Bb Lam (N)))` THEN CONJ_TAC THENL
     [POP_ASSUM(fun th -> REWRITE_TAC[MATCH_MP EXP_LOG th; REAL_LE_REFL]);
      ASM_REWRITE_TAC[REAL_EXP_MONO_LE]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `h * (baker_Lpar n D q + 2) * (baker_Lpar n D q + 1) EXP n <=
     baker_kpar n D q * (h * (baker_Lpar n D q + 2) EXP (n + 1)) /\ h *
     (baker_Lpar n D q + 2) EXP (n + 1) <= h * q EXP baker_J n D /\ 4 * (h *
     q EXP baker_J n D) <= 4 * q EXP baker_a D * (h * q EXP baker_J n D)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [TRANS_TAC LE_TRANS `h * (baker_Lpar n D q + 2) EXP (n + 1)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM ADD1; EXP; LE_MULT_LCANCEL] THEN
        DISJ2_TAC THEN DISJ2_TAC THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
          ARITH_TAC;
        MATCH_MP_TAC(ARITH_RULE `1 * x <= k * x ==> x <= k * x`) THEN
        REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC BAKER_X7_LE_R THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `1 <= q EXP baker_a D` MP_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
        UNDISCH_TAC `16 <= q` THEN ARITH_TAC;
        ALL_TAC] THEN
      SPEC_TAC(`q EXP baker_a D`, `y:num`) THEN
      SPEC_TAC(`h * q EXP baker_J n D`, `x:num`) THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `4 * 1 * x <= 4 * y * x ==> 4 * x <= 4 * y *
        x`) THEN
      REWRITE_TAC[LE_MULT_LCANCEL; LE_MULT_RCANCEL] THEN
        ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3) /\ &16 * (&h *
     &q pow (baker_c D * (n + 1) + baker_J n D + 3)) <= &q pow baker_e1 n D *
     &h /\ (!K. K <= baker_J n D ==> &(h * q EXP K) <= &h * &q pow (baker_c D *
     (n + 1) + baker_J n D + 3)) /\ &(baker_kpar n D q) <= &h *
     &q pow (baker_c D * (n + 1) + baker_J n D + 3) /\ &5 * &(h *
     q EXP baker_J n D) * (&(baker_kpar n D q) + &1) <= &h *
     &q pow (baker_c D * (n + 1) + baker_J n D + 3) /\ &2 * &(h *
     q EXP baker_J n D) * &(baker_kpar n D q) <= &h * &q pow (baker_c D * (n +
     1) + baker_J n D + 3) /\ &(baker_kpar n D q) * (&1 +
     &(baker_kpar n D q)) <= &h * &q pow (baker_c D * (n + 1) + baker_J n D +
     3)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_UNITS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. K < baker_J n D ==>
     baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (4 * q EXP baker_a D *
     (h * q EXP (K + 1)) + 1) +
     baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h * q EXP (K + 1)) +
     &3 <= &(h * q EXP K) * &(baker_kpar n D q DIV 2 EXP (K + 1) + 1) *
     &(baker_a D) * log(&q)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC BAKER_STEP_NUM THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&2176 * M pow 3 * &2 pow baker_J n D` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `K < baker_J n D` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (4 * q EXP baker_a D *
     (h * q EXP baker_J n D) + 1) + &1 +
     (baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
     (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
     (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) * log(&q)) + &6 *
     &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) * log(&q)) + &2) <=
     &(h * q EXP baker_J n D) * &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) *
     &(baker_a D) * log(&q)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_LEMMA7_NUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!K. K < baker_J n D ==> &(h * q EXP K) * &(baker_kpar n D q DIV 2 EXP (K +
     1) + 1) * &(baker_a D) * log(&q) <= &h * &q pow (baker_c D * (n + 1) +
     baker_J n D + 3)) /\ &(h * q EXP baker_J n D) *
     &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) * &(baker_a D) * log(&q) <=
     &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC; ALL_TAC] THEN
    MATCH_MP_TAC BAKER_ZBOUND THEN ASM_REWRITE_TAC[LE_REFL] THEN
    UNDISCH_TAC `K < baker_J n D` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!N. &0 <= baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (N)) /\
     (!R. &0 <= baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (R)) /\
     &0 <= baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
     (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
     (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) * log(&q))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= log(&q)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[baker_lu] THEN
      REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
             CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_POW_LE];
      GEN_TAC THEN MATCH_MP_TAC BAKER_LW_POS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[baker_l7] THEN
      REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
             CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_POW_LE]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&(baker_kpar n D q)) = &(baker_c D * (n + 1)) * log(&q)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[baker_kpar; GSYM REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC LOG_POW THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `16 <= q` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &q pow baker_e1 n D * &h /\ &16 * (&q pow baker_e1 n D * &h) <=
     &q pow (baker_e1 n D + 1) * &h /\ &0 <= &6 * &h * &(baker_Lpar n D q) *
     (&(baker_c D * (n + 1)) * log(&q)) /\
    1 <= h * q EXP baker_J n D`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
      SUBGOAL_THEN `&q pow (baker_e1 n D + 1) * &h = &q *
        (&q pow baker_e1 n D * &h)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
      UNDISCH_TAC `1 <= h` THEN UNDISCH_TAC `16 <= q` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!N. N <= h * q EXP baker_J n D + 1 ==>
     baker_err n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
     (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam d0 (N) <=
     exp(--(&q pow baker_e1 n D * &h))`
  STRIP_ASSUME_TAC THENL
   [X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (N) <=
      &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS
       `baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (4 *
         q EXP baker_a D * (h * q EXP baker_J n D) + 1)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[baker_lu; REAL_LE_LADD] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
          REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `N <= h * q EXP baker_J n D + 1` THEN
        UNDISCH_TAC `4 * (h * q EXP baker_J n D) <=
                     4 * q EXP baker_a D * (h * q EXP baker_J n D)` THEN
        ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&N * &(baker_Lpar n D q) <= &h * &q pow (baker_c D * (n +
      1) + baker_J n D + 3)` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&2 * &(h * q EXP baker_J n D) *
       &(baker_kpar n D q)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MP_TAC(SPECL [`&N`; `&2 * &(h *
        q EXP baker_J n D)`; `&(baker_Lpar n D q)`; `&(baker_kpar n D q)`]
        REAL_LE_MUL2) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_POS; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `N <= h * q EXP baker_J n D + 1` THEN
          UNDISCH_TAC `1 <= h * q EXP baker_J n D` THEN ARITH_TAC;
          ASM_REWRITE_TAC[]];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&N * &(baker_Lpar n D q) <= exp(&q pow (baker_e1 n D + 1) *
      &h)` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&q pow (baker_e1 n D + 1) * &h` THEN
       REWRITE_TAC[REAL_LE_EXP_SELF] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&N * &(baker_Lpar n D q) * d0 <= &1` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `exp(&q pow (baker_e1 n D + 1) * &h) *
       exp(--(&q pow (baker_e1 n D + 1) * &h))` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
        REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0;
                    REAL_LE_REFL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`n:num`; `h:num`; `baker_Lpar n D q`; `baker_kpar n D q`;
      `baker_pbound n h (baker_Lpar n D q) (baker_kpar n D q) V G H e`;
      `Bb:real`; `Lam:real`;
                   `d0:real`; `N:num`] BAKER_ERR_LE_UB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <=
      baker_ub n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
      (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam (N) /\
      baker_ub n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
      (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam (N) <= exp(&h *
      &q pow (baker_c D * (n + 1) + baker_J n D + 3))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[baker_ub] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
        TRANS_TAC REAL_LE_TRANS `exp(baker_lu M (baker_Lpar n D q) (baker_kpar
          n D q) h (N))` THEN
        ASM_REWRITE_TAC[REAL_EXP_MONO_LE]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&1) * (exp(&h * &q pow (baker_c D * (n + 1) + baker_J n D +
      3)) * exp(--(&q pow (baker_e1 n D + 1) * &h))) * exp(&h *
      &q pow (baker_c D * (n + 1) + baker_J n D + 3))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp(&1) * (&N * &(baker_Lpar n D q) * d0) *
        baker_ub n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
        (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam (N)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
          TRANS_TAC REAL_LE_TRANS `&h * &q pow (baker_c D * (n + 1) +
            baker_J n D + 3)` THEN ASM_REWRITE_TAC[REAL_LE_EXP_SELF]]];
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `baker_err n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
     (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam d0 (h + 1) <=
     exp(--(&q pow baker_e1 n D * &h))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `h * 1 <= h * x ==> h + 1 <= h * x + 1`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
    UNDISCH_TAC `16 <= q` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. K < baker_J n D ==>
     baker_err n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
     (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam d0 (h * q EXP (K +
     1) + 1) <= exp(--(&q pow baker_e1 n D * &h))`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LE_ADD_RCANCEL; LE_MULT_LCANCEL; LE_EXP] THEN
    COND_CASES_TAC THEN UNDISCH_TAC `K < baker_J n D` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. K < baker_J n D ==> h * q EXP K <= h * q EXP (K + 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP] THEN COND_CASES_TAC THENL
     [UNDISCH_TAC `16 <= q` THEN UNDISCH_TAC `q = 0` THEN ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. K < baker_J n D ==> 2 * baker_kpar n D q DIV 2 EXP (K + 1) <=
     baker_kpar n D q DIV 2 EXP K`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BAKER_S_HALF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. K < baker_J n D ==> 4 * (h * q EXP (K + 1)) <= 4 * q EXP baker_a D *
     (h * q EXP (K + 1))`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `1 <= q EXP baker_a D` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
      UNDISCH_TAC `16 <= q` THEN ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`q EXP baker_a D`, `y:num`) THEN
    SPEC_TAC(`h * q EXP (K + 1)`, `x:num`) THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `4 * 1 * x <= 4 * y * x ==> 4 * x <= 4 * y *
      x`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; LE_MULT_RCANCEL] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!K. K < baker_J n D ==>
    baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h * q EXP (K + 1)) <=
    &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(h * q EXP K) *
      &(baker_kpar n D q DIV 2 EXP (K + 1) + 1) * &(baker_a D) * log(&q)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!u w z:real. &0 <= u /\ u + w + &3 <= z ==> w <= z`) THEN
    EXISTS_TAC `baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (4 *
      q EXP baker_a D * (h * q EXP (K + 1)) + 1)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. K < baker_J n D ==>
     exp(--(baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h *
     q EXP (K + 1)))) / &2 <=
     baker_vb n h (baker_Lpar n D q) (baker_kpar n D q) V G H e d (baker_pbound
     n h (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam d0 lmin Gn (h *
     q EXP (K + 1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[baker_vb] THEN
    MP_TAC(ISPECL [`n:num`; `h:num`; `baker_Lpar n D q`; `baker_kpar n D q`;
      `V:num->bool`; `G:real`;
                   `H:num->real`; `e:num->num`; `d:num->num`; `baker_pbound n h
                     (baker_Lpar n D q) (baker_kpar n D q) V G H e`;
                   `Gn:real`; `lmin:real`; `h * q EXP (K + 1)`; `M:real`]
                  BAKER_LIOU5_EXP_LOWER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `h * 1 <= h * x ==> h <= h * x`) THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
        REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
        UNDISCH_TAC `16 <= q` THEN ARITH_TAC;
        ASM_SIMP_TAC[]];
      DISCH_TAC] THEN
    SUBGOAL_THEN `baker_err n h (baker_Lpar n D q) (baker_kpar n D q)
      (baker_pbound n h (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam
      d0 (h * q EXP (K + 1) + 1) <=
      exp(--(baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h *
      q EXP (K + 1)))) / &2`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--(&q pow baker_e1 n D *
       &h))` THEN
      CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp(--(baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h
        (h * q EXP (K + 1)) + &1))` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
        SUBGOAL_THEN `baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h *
          q EXP (K + 1)) <= &h * &q pow (baker_c D * (n + 1) + baker_J n D +
          3)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(h * q EXP K) *
           &(baker_kpar n D q DIV 2 EXP (K + 1) + 1) * &(baker_a D) *
           log(&q)` THEN
          CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
          MATCH_MP_TAC(REAL_ARITH
           `!u w z:real. &0 <= u /\ u + w + &3 <= z ==> w <= z`) THEN
          EXISTS_TAC `baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (4 *
            q EXP baker_a D * (h * q EXP (K + 1)) + 1)` THEN ASM_SIMP_TAC[];
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_NEG_ADD; REAL_EXP_ADD] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= x /\ x * y <= x * inv(&2) ==> x * y <= x / &2`) THEN
        CONJ_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_TWO_LE_EXP_1] THEN REAL_ARITH_TAC];
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. K < baker_J n D ==> &0 <
     baker_vb n h (baker_Lpar n D q) (baker_kpar n D q) V G H e d (baker_pbound
     n h (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam d0 lmin Gn (h *
     q EXP (K + 1))`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `exp(--(baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h
      * q EXP (K + 1)))) / &2` THEN
    ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_LT_DIV; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. K < baker_J n D ==> &2 *
     baker_ub n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
     (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam (4 *
     q EXP baker_a D * (h * q EXP (K + 1)) + 1) * (&4 * &(h * q EXP (K + 1)) /
     &(4 * q EXP baker_a D * (h * q EXP (K + 1)))) pow ((h * q EXP K) *
     (baker_kpar n D q DIV 2 EXP (K + 1) + 1)) + exp(--(&q pow baker_e1 n D *
     &h)) * &2 * &(h * q EXP K) * &2 pow (baker_kpar n D q DIV 2 EXP (K + 1)) *
     exp(&n) * (&(h * q EXP (K + 1)) * &16 pow (h * q EXP (K +
     1))) pow (baker_kpar n D q DIV 2 EXP (K + 1) + 1) <=
     baker_vb n h (baker_Lpar n D q) (baker_kpar n D q) V G H e d (baker_pbound
     n h (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam d0 lmin Gn (h *
     q EXP (K + 1)) / &2`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `K:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "baker_vb"
                      with Failure _ -> false)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "baker_lw"
                      with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a b w v:real. a <= w / &8 /\ b <= w / &8 /\ w / &2 <= v
                     ==> a + b <= v / &2`) THEN
    EXISTS_TAC `exp(--(baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h
      * q EXP (K + 1))))` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&4 * &(h * q EXP (K + 1)) / &(4 * q EXP baker_a D * (h *
       q EXP (K + 1))) = inv(&q pow baker_a D)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        SUBGOAL_THEN `~(&h = &0) /\ ~(&q pow (K + 1) = &0) /\
                      ~(&q pow baker_a D = &0)` MP_TAC THENL
         [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ] THEN
          UNDISCH_TAC `1 <= h` THEN UNDISCH_TAC `16 <= q` THEN ARITH_TAC;
          CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      REWRITE_TAC[MATCH_MP BAKER_INV_POW_EXP (ASSUME `1 <= q`)] THEN
      SUBGOAL_THEN `&((h * q EXP K) * (baker_kpar n D q DIV 2 EXP (K + 1) +
        1)) * &(baker_a D) * log(&q) = &(h * q EXP K) *
        &(baker_kpar n D q DIV 2 EXP (K + 1) + 1) * &(baker_a D) * log(&q)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 *
        exp(baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (4 *
        q EXP baker_a D * (h * q EXP (K + 1)) + 1)) * exp(--(&(h * q EXP K) *
        &(baker_kpar n D q DIV 2 EXP (K + 1) + 1) * &(baker_a D) *
        log(&q)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 *
        exp(--(baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h *
        q EXP (K + 1))) + --(&3))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
         REWRITE_TAC[REAL_POS; REAL_EXP_MONO_LE] THEN
        FIRST_ASSUM(MP_TAC o SPEC `K:num` o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "baker_lu"
                          with Failure _ -> false)) (concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "baker_lw"
                          with Failure _ -> false)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
        REWRITE_TAC[REAL_EXP_ADD] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= x /\ x * y <= x * inv(&16) ==> &2 * x * y <= x / &8`) THEN
        CONJ_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_EXP_3_GE_16] THEN REAL_ARITH_TAC];
      MP_TAC(SPECL [`h * q EXP K`; `h * q EXP (K +
        1)`; `baker_kpar n D q DIV 2 EXP (K +
        1)`; `n:num`] BAKER_TERM2_EXP_LE) THEN
      DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp(--(&q pow baker_e1 n D * &h)) * exp(&1 + &(h * q EXP K) +
        &(baker_kpar n D q DIV 2 EXP (K + 1)) + &n +
                  &5 * &(h * q EXP (K + 1)) *
                    (&(baker_kpar n D q DIV 2 EXP (K + 1)) + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp(--(baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h
        (h * q EXP (K + 1))) + --(&3))` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        SUBGOAL_THEN `baker_lw M D (baker_Lpar n D q) (baker_kpar n D q) h (h *
          q EXP (K + 1)) <= &h * &q pow (baker_c D * (n + 1) + baker_J n D +
          3)` ASSUME_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `&(h * q EXP K) <= &h * &q pow (baker_c D * (n + 1) +
          baker_J n D + 3) /\ &(h * q EXP (K + 1)) <= &(h *
          q EXP baker_J n D) /\
                      &(baker_kpar n D q DIV 2 EXP (K + 1)) <=
                        &(baker_kpar n D q) /\ &h <= &h * &q pow (baker_c D *
                        (n + 1) + baker_J n D + 3)`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
              is_forall(concl th) && free_in `K:num` (concl th) = false &&
              can (find_term ((=) `baker_c D * (n + 1) + baker_J n D + 3`))
                  (concl th))) THEN
            UNDISCH_TAC `K < baker_J n D` THEN ARITH_TAC;
            REWRITE_TAC[REAL_OF_NUM_LE; LE_MULT_LCANCEL; LE_EXP] THEN
            COND_CASES_TAC THEN UNDISCH_TAC `K < baker_J n D` THEN
            ARITH_TAC;
            REWRITE_TAC[REAL_OF_NUM_LE; DIV_LE];
            MATCH_MP_TAC(REAL_ARITH `&h * &1 <= &h * x ==> &h <= &h * x`) THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
            MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
            ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN `&5 * &(h * q EXP (K + 1)) *
          (&(baker_kpar n D q DIV 2 EXP (K + 1)) + &1) <= &h *
          &q pow (baker_c D * (n + 1) + baker_J n D + 3)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&5 * &(h * q EXP baker_J n D) * (&(baker_kpar n D q) +
            &1)` THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_ADD] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= x /\ x * y <= x * inv(&16) ==> x * y <= x / &8`) THEN
        CONJ_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_EXP_3_GE_16] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(baker_kpar n D q) pow (2 * h * (baker_Lpar n D q + 2)) * (&2 *
     baker_ub n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
     (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam (4 *
     q EXP baker_a D * (h * q EXP baker_J n D) + 1) * (&4 * &(h *
     q EXP baker_J n D) / &(4 * q EXP baker_a D * (h *
     q EXP baker_J n D))) pow ((h * q EXP baker_J n D) *
     (baker_kpar n D q DIV 2 EXP baker_J n D + 1)) +
     exp(--(&q pow baker_e1 n D * &h)) * &2 * &(baker_kpar n D q) * &(h *
     q EXP baker_J n D) * (&2 *
     &(baker_kpar n D q)) pow (baker_kpar n D q DIV 2 EXP baker_J n D) *
     exp(&n) * (&(h * q EXP baker_J n D) * &16 pow (h *
     q EXP baker_J n D)) pow (baker_kpar n D q DIV 2 EXP baker_J n D + 1) +
     baker_err n h (baker_Lpar n D q) (baker_kpar n D q) (baker_pbound n h
     (baker_Lpar n D q) (baker_kpar n D q) V G H e) Bb Lam d0 (h *
     (baker_Lpar n D q + 2) EXP (n + 1) + 1)) <
     baker_liou7 n h (baker_Lpar n D q) (baker_kpar n D q) d H (baker_pbound n
     h (baker_Lpar n D q) (baker_kpar n D q) V G H e) (h * (baker_Lpar n D q +
     2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) * (baker_Lpar n D q +
     1) EXP n)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `h:num`; `baker_Lpar n D q`; `baker_kpar n D q`;
     `d:num->num`; `H:num->real`;
                   `baker_pbound n h (baker_Lpar n D q) (baker_kpar n D q) V G
                     H e`; `h * (baker_Lpar n D q + 2) EXP (n + 1)`; `h *
                     (baker_Lpar n D q + 2) * (baker_Lpar n D q +
                     1) EXP n`; `&(baker_c D * (n + 1)) *
                     log(&q)`; `V:num->bool`; `M:real`]
                  BAKER_LIOU7_EXP_LOWER) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `h * 1 <= h * x ==> h <= h * x`) THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
        REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN ARITH_TAC;
        ASM_SIMP_TAC[]];
      DISCH_TAC] THEN
    SUBGOAL_THEN `baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
      (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
      (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) * log(&q)) + &6 *
      &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) * log(&q)) + &2 <=
      &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(h * q EXP baker_J n D) *
       &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) * &(baker_a D) *
       log(&q)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!u w z:real. &0 <= u /\ u + &1 + w <= z ==> w <= z`) THEN
      EXISTS_TAC `baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (4 *
        q EXP baker_a D * (h * q EXP baker_J n D) + 1)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `exp(&6 * &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) *
      log(&q))) * (&3 *
      exp(--(baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
      (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
      (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) * log(&q)) + &6 *
      &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) * log(&q)) +
      &2)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(baker_kpar n D q) pow (2 * h * (baker_Lpar n D q + 2)) *
        (&3 *
        exp(--(baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
        (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
        (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) * log(&q)) + &6 *
        &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) * log(&q)) +
        &2)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH
         `a <= e /\ b <= e /\ c <= e ==> a + b + c <= &3 * e`) THEN
        REPEAT CONJ_TAC THENL
         [SUBGOAL_THEN `&4 * &(h * q EXP baker_J n D) / &(4 * q EXP baker_a D *
           (h * q EXP baker_J n D)) = inv(&q pow baker_a D)`
          SUBST1_TAC THENL
           [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
            SUBGOAL_THEN `~(&h = &0) /\ ~(&q pow baker_J n D = &0) /\
                          ~(&q pow baker_a D = &0)` MP_TAC THENL
             [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ] THEN
              UNDISCH_TAC `1 <= h` THEN UNDISCH_TAC `16 <= q` THEN ARITH_TAC;
              CONV_TAC REAL_FIELD];
            ALL_TAC] THEN
          REWRITE_TAC[MATCH_MP BAKER_INV_POW_EXP (ASSUME `1 <= q`)] THEN
          SUBGOAL_THEN `&((h * q EXP baker_J n D) *
            (baker_kpar n D q DIV 2 EXP baker_J n D + 1)) * &(baker_a D) *
            log(&q) = &(h * q EXP baker_J n D) *
            &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) * &(baker_a D) *
            log(&q)`
          SUBST1_TAC THENL
           [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2 *
            exp(baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h (4 *
            q EXP baker_a D * (h * q EXP baker_J n D) + 1)) * exp(--(&(h *
            q EXP baker_J n D) * &(baker_kpar n D q DIV 2 EXP baker_J n D +
            1) * &(baker_a D) * log(&q)))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
            MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2 *
            exp(--(baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
            (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
            (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) * log(&q)) +
            &6 * &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) *
            log(&q)) + &2) + --(&1))` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN
             REWRITE_TAC[REAL_POS; REAL_EXP_MONO_LE] THEN
            MP_TAC(ASSUME `baker_lu M (baker_Lpar n D q) (baker_kpar n D q) h
              (4 * q EXP baker_a D * (h * q EXP baker_J n D) + 1) + &1 +
              (baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
              (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
              (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) *
              log(&q)) + &6 * &h * &(baker_Lpar n D q) * (&(baker_c D * (n +
              1)) * log(&q)) + &2) <= &(h * q EXP baker_J n D) *
              &(baker_kpar n D q DIV 2 EXP baker_J n D + 1) * &(baker_a D) *
              log(&q)`) THEN
            REAL_ARITH_TAC;
            REWRITE_TAC[REAL_EXP_ADD] THEN
            MATCH_MP_TAC(REAL_ARITH
             `&0 <= x /\ x * y <= x * inv(&2) ==> &2 * x * y <= x`) THEN
            CONJ_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
            REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
            REWRITE_TAC[REAL_TWO_LE_EXP_1] THEN REAL_ARITH_TAC];
          MP_TAC(SPECL [`baker_kpar n D q`; `h *
            q EXP baker_J n D`; `baker_kpar n D q DIV 2 EXP baker_J n D`;
            `n:num`] BAKER_TERM12_EXP_LE) THEN
          DISCH_TAC THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `exp(--(&q pow baker_e1 n D * &h)) * exp(&1 +
            &(baker_kpar n D q) + &(h * q EXP baker_J n D) +
            &(baker_kpar n D q DIV 2 EXP baker_J n D) * (&1 +
            &(baker_kpar n D q)) +
                      &n + &5 * &(h * q EXP baker_J n D) *
                        (&(baker_kpar n D q DIV 2 EXP baker_J n D) + &1))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
            ALL_TAC] THEN
          REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
          SUBGOAL_THEN `&(baker_kpar n D q DIV 2 EXP baker_J n D) <=
            &(baker_kpar n D q) /\ &(h * q EXP baker_J n D) <= &h *
            &q pow (baker_c D * (n + 1) + baker_J n D + 3) /\ &h <= &h *
            &q pow (baker_c D * (n + 1) + baker_J n D + 3)`
          STRIP_ASSUME_TAC THENL
           [REPEAT CONJ_TAC THENL
             [REWRITE_TAC[REAL_OF_NUM_LE; DIV_LE];
              FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
                is_forall(concl th) &&
                can (find_term ((=) `K <= baker_J n D`)) (concl th))) THEN
              REWRITE_TAC[LE_REFL];
              MATCH_MP_TAC(REAL_ARITH `&h * &1 <= &h * x ==> &h <= &h * x`) THEN
              MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
              MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
              ASM_REWRITE_TAC[]];
            ALL_TAC] THEN
          SUBGOAL_THEN `&(baker_kpar n D q DIV 2 EXP baker_J n D) * (&1 +
            &(baker_kpar n D q)) <= &h * &q pow (baker_c D * (n + 1) +
            baker_J n D + 3) /\
                        &5 * &(h * q EXP baker_J n D) *
                          (&(baker_kpar n D q DIV 2 EXP baker_J n D) + &1) <=
                          &h * &q pow (baker_c D * (n + 1) + baker_J n D + 3)`
          STRIP_ASSUME_TAC THENL
           [CONJ_TAC THENL
             [MATCH_MP_TAC REAL_LE_TRANS THEN
              EXISTS_TAC `&(baker_kpar n D q) * (&1 +
                &(baker_kpar n D q))` THEN ASM_REWRITE_TAC[] THEN
              MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
              REAL_ARITH_TAC;
              MATCH_MP_TAC REAL_LE_TRANS THEN
              EXISTS_TAC `&5 * &(h * q EXP baker_J n D) *
                (&(baker_kpar n D q) + &1)` THEN ASM_REWRITE_TAC[] THEN
              MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
              MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
              ASM_REAL_ARITH_TAC];
            ALL_TAC] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC `exp(--(&q pow baker_e1 n D * &h))` THEN CONJ_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_ADD_RCANCEL];
            REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC]];
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [MP_TAC(SPECL [`baker_kpar n D q`; `h:num`; `baker_Lpar n D q`]
           BAKER_KPOW_LE) THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
          REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `exp(--(baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q)
        h (h * (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q +
        2) * (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) *
        log(&q))))` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `exp(&6 * &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) *
         log(&q))) * (&3 *
         exp(--(baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
         (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
         (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) * log(&q)) +
         &6 * &h * &(baker_Lpar n D q) * (&(baker_c D * (n + 1)) * log(&q)) +
         &2))) = &3 *
         (exp(--(baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D q) h (h *
         (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q + 2) *
         (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) * log(&q)))) *
         exp(--(&2)))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x * y = z ==> x * (&3 * y) = &3 * z`) THEN
        REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `exp(--(&2)) < inv(&3)` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
        REWRITE_TAC[REAL_EXP_2_GT_3] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`exp(--(baker_l7 M D n (baker_Lpar n D q) (baker_kpar n D
        q) h (h * (baker_Lpar n D q + 2) EXP (n + 1)) (h * (baker_Lpar n D q +
        2) * (baker_Lpar n D q + 1) EXP n) (&(baker_c D * (n + 1)) *
        log(&q))))`; `exp(--(&2))`; `inv(&3)`] REAL_LT_LMUL) THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(baker_Lpar n D q) * Lam < &2 * pi * &(baker_kpar n D q)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_LLAM_LT THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`n:num`; `lg:num->complex`; `theta:num->complex`; `V:num->bool`;
    `g:num->(num->complex)->complex`; `e:num->num`; `G:real`;
    `a:num->num->real`; `d:num->num`; `H:num->real`; `beta:num->complex`;
    `h:num`; `baker_Lpar n D q`; `baker_kpar n D q`; `\K. h *
      q EXP K`; `\K. baker_kpar n D q DIV 2 EXP K`;
    `\K. 4 * q EXP baker_a D * (h * q EXP (K + 1))`; `baker_J n D`; `h *
      (baker_Lpar n D q + 2) EXP (n + 1)`; `4 * q EXP baker_a D * (h *
      q EXP baker_J n D)`; `exp(--(&q pow baker_e1 n D * &h))`;
    `Bb:real`; `Lam:real`; `d0:real`; `lmin:real`; `Gn:real`]
   BAKER_CORE_PARAMETRIC) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES; DIV_1]);;
