(* ========================================================================= *)
(* The Green-Tao theorem in its general form: every set of primes of         *)
(* positive relative upper density contains arbitrarily long arithmetic      *)
(* progressions, with the lower bound of Green and Tao for their number.     *)
(*   GREEN_TAO_DENSE_COUNT: for k >= 2 and delta > 0 there are c > 0 and     *)
(*   X0 such that for every set A of primes and every X >= X0 with           *)
(*   |A INTER [0, X]| >= delta pi(X), at least c X^2 / log(X)^k pairs        *)
(*   (a, d) have d > 0, a + (k - 1) d <= X and every a + j d (j < k) in A.   *)
(*   GREEN_TAO_DENSE, GREEN_TAO_DENSE_INFINITE: if |A INTER [0, X]| >=       *)
(*   delta pi(X) for arbitrarily large X, then A contains k-term             *)
(*   progressions for every k, indeed infinitely many.                       *)
(*   GREEN_TAO_COUNT is the case A = the primes, delta = 1, and GREEN_TAO:   *)
(*   !k. ?a d. 0 < d /\ !j. j < k ==> prime(a + j * d).                      *)
(* So the primes need no equidistribution in residue classes, only the       *)
(* prime number theorem in the form pi(X) >= X / (2 log X) (PI_LOWER).       *)
(*                                                                           *)
(* * gtfun A W b R N c0: the W-tricked function on Z_N for the residue b,    *)
(*   equal to c0 (phi W / W) log(W y + b) when y < N / 2 and W y + b is in   *)
(*   A and > R, and 0 otherwise.  GTFUN_LE_NU: gtfun <= gtnu W b             *)
(*   (GT_MAJORANT) for a set A of primes, b <= W, c0 = 1 / (80 m) and        *)
(*   N <= R^(40 m).                                                          *)
(* * GT_AP_LOWER: with m = |lf_index k|, R large and N a prime in            *)
(*   (R^(20 m), R^(40 m)], GT_LINEAR_FORMS gives lf_hyp for gtnu W b and     *)
(*   RELATIVE_SZEMEREDI turns E gtfun >= delta into AP_k(gtfun) >= c > 0,    *)
(*   uniformly in A, b, R and N.                                             *)
(* * GT_DENSE_MEAN: for A INTER [0, X] the mean is >= c0 delta / (2560 m)    *)
(*   when b is the residue given by RESIDUE_PIGEONHOLE (one of the phi(W)    *)
(*   classes coprime to W holds a 1 / phi(W) share of the primes of A in     *)
(*   (R, X]): the primes <= R are few (LOG_ROOT_BOUND) and the others have   *)
(*   log p > log R >= log X / (80 m).                                        *)
(* * GT_PAIRS_COUNT: since gtfun <= log R, AP_COUNT_NONTRIVIAL gives         *)
(*   c N^2 / (2 log^k R) pairs (a, d) mod N, d /= 0, with all values         *)
(*   positive, and PROGRESSIONS_FROM_PAIRS turns them, at most two to one,   *)
(*   into progressions W n_j + b in A INTER [0, X].  N is a prime in         *)
(*   (2 y + 2, 4 y + 4] for y = X DIV W (PRIME_DOUBLE_INTERVAL, from         *)
(*   BERTRAND) and R the largest number with R^(20 m) < N (ROOT_CHOICE).     *)
(* AP_COUNT_NONTRIVIAL and PROGRESSIONS_FROM_PAIRS are those of              *)
(* Library/szemeredi.ml.                                                     *)
(* ========================================================================= *)

needs "Sieve/gt_majorant.ml";;
needs "Sieve/gt_transfer.ml";;
needs "Sieve/goldbach_shnirelman.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The W-tricked function on Z_N for a residue b, majorized by gtnu.         *)
(* ------------------------------------------------------------------------- *)

let CARD_LF_INDEX_GE = prove
 (`!k. k <= CARD(lf_index k)`,
  GEN_TAC THEN
  SUBGOAL_THEN `k = CARD(IMAGE (\j. (j,{}:num->bool)) {j | j < k})`
  (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [SIMP_TAC[CARD_IMAGE_INJ; FINITE_NUMSEG_LT; PAIR_EQ; CARD_NUMSEG_LT];
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_LF_INDEX] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; lf_index; IN_ELIM_PAIR_THM;
                IN_ELIM_THM; NOT_IN_EMPTY]]);;

let GTW_GE_2 = prove
 (`!w. 2 <= w ==> 2 <= gtW w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 divides gtW w` MP_TAC THENL
   [REWRITE_TAC[gtW] THEN
    MP_TAC(SPECL [`2`; `{p:num | prime p /\ p <= w}`]
      PRIME_DIVIDES_NPRODUCT_PRIMES) THEN
    ASM_SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM; PRIME_2];
    ALL_TAC] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  MP_TAC(SPEC `w:num` GTW_POS) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `q = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

let gtfun = new_definition
 `gtfun (A:num->bool) W b R N c0 y =
    if y < N DIV 2 /\ A(W * y + b) /\ R < W * y + b
    then c0 * (&(phi W) / &W * log(&(W * y + b))) else &0`;;

let PHI_RATIO = prove
 (`!W. 1 <= W ==> &0 <= &(phi W) / &W /\ &(phi W) / &W <= &1`,
  REPEAT STRIP_TAC THEN SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `1 <= W ==> 0 < W`] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE; PHI_LIMIT]);;

let GTFUN_POS = prove
 (`!A W b R N c0 y. 1 <= W /\ &0 <= c0 ==> &0 <= gtfun A W b R N c0 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gtfun] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_LE_REFL] THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[PHI_RATIO] THEN MATCH_MP_TAC LOG_POS THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC);;

let GTFUN_POS_IMP = prove
 (`!A W b R N c0 y.
        &0 < gtfun A W b R N c0 y
        ==> y < N DIV 2 /\ A(W * y + b) /\ R < W * y + b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gtfun] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LT_REFL]);;

let GTFUN_LOG = prove
 (`!m W b R N y.
        1 <= m /\ 1 <= W /\ 1 <= b /\ b <= W /\ W <= R /\
        N <= R EXP (40 * m) /\ y < N
        ==> inv(&(80 * m)) * log(&(W * y + b)) <= log(&R)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= R` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `W * y + b <= R EXP (80 * m)` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(R:num) * R EXP (40 * m)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(W:num) * N` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(W:num) * (y + 1)` THEN
        CONJ_TAC THENL [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN ASM_ARITH_TAC;
                        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC];
        MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM(CONJUNCT2 EXP); LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&(W * y + b)) <= &(80 * m) * log(&R)` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH_RULE `1 <= R ==> 0 < R`;
                 LOG_MONO_LE; REAL_POW_LT;
                 ARITH_RULE `1 <= b ==> 0 < W * y + b`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(80 * m)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`&(80 * m)`,`a:real`) THEN
  SPEC_TAC(`log(&(W * y + b))`,`L:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let GTFUN_LE_LOGR = prove
 (`!m A W b R N y.
        1 <= m /\ 1 <= W /\ 1 <= b /\ b <= W /\ W <= R /\
        N <= R EXP (40 * m) /\ y < N
        ==> gtfun A W b R N (inv(&(80 * m))) y <= log(&R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gtfun] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&(80 * m)) * log(&(W * y + b))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[PHI_RATIO] THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC GTFUN_LOG THEN EXISTS_TAC `N:num` THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC]);;

let GTFUN_LE_NU = prove
 (`!w A b R N m y.
        2 <= w /\ 1 <= m /\ 1 <= b /\ b <= gtW w /\ gtW w <= R /\
        N <= R EXP (40 * m) /\ y < N /\ (!p. A p ==> prime p)
        ==> gtfun A (gtW w) b R N (inv(&(80 * m))) y <=
            gtnu (gtW w) b (gtD w R) (gtP w R) (&y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= R` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:num` GTW_POS) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[gtfun] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `prime(gtW w * y + b)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GT_MAJORANT THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&R)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC GTFUN_LOG THEN EXISTS_TAC `N:num` THEN
      ASM_REWRITE_TAC[GTW_POS];
      ASM_SIMP_TAC[LOG_MONO_LE; REAL_OF_NUM_LT;
                   ARITH_RULE `1 <= R ==> 0 < R`;
                   REAL_ARITH `&1 <= x ==> &0 < x + &1`; REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC GTNU_POS THEN REWRITE_TAC[GTP_FINITE] THEN
    ASM_SIMP_TAC[GTD_FAMILY] THEN ASM_MESON_TAC[GTP_PRIME]]);;

(* ------------------------------------------------------------------------- *)
(* Progression averages of the W-tricked function.                           *)
(* ------------------------------------------------------------------------- *)

let GT_AP_LOWER = prove
 (`!k delta.
        2 <= k /\ &0 < delta
        ==> ?W R0 c.
              2 <= W /\ W + 4 <= R0 /\ &0 < c /\
              !A b R N.
                (!p. A p ==> prime p) /\ 1 <= b /\ b <= W /\ R0 <= R /\
                prime N /\ R EXP (20 * CARD(lf_index k)) < N /\
                N <= R EXP (40 * CARD(lf_index k)) /\
                delta <= fmean {y | y < N}
                           (gtfun A W b R N (inv(&(80 * CARD(lf_index k)))))
                ==> c <= fmean {a | a < N}
                           (\a. fmean {d | d < N}
                                  (\d. product {j | j < k}
                                         (\j. gtfun A W b R N
                                                (inv(&(80 * CARD(lf_index k))))
                                                ((a + j * d) MOD N))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = CARD(lf_index k)` THEN
  SUBGOAL_THEN `k <= m /\ 1 <= m` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` CARD_LF_INDEX_GE) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c0 = inv(&(80 * m))` THEN
  SUBGOAL_THEN `&0 <= c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `delta:real`] RELATIVE_SZEMEREDI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `csz:real` (X_CHOOSE_THEN `eta:real`
   (X_CHOOSE_THEN `N1:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rel")))))) THEN
  MP_TAC(SPECL [`m:num`; `2 * k`; `k:num`; `eta:real`] GT_LINEAR_FORMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:num` (X_CHOOSE_TAC `R1:num`)) THEN
  ABBREV_TAC `w = MAX w0 2` THEN
  SUBGOAL_THEN `w0 <= w /\ 2 <= w` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `W = gtW w` THEN
  SUBGOAL_THEN `2 <= W /\ 1 <= W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_SIMP_TAC[GTW_GE_2; GTW_POS]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W:num`; `R1 + W + N1 + k + 4`; `csz:real`] THEN
  REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC[]; ARITH_TAC; ASM_REWRITE_TAC[];
                         ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`A:num->bool`; `b:num`; `R:num`; `N:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `4 <= R /\ 1 <= R /\ R1 <= R /\ W <= R /\ N1 <= R /\ k <= R`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `R <= R EXP (20 * m)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
    ASM_SIMP_TAC[LE_EXP; ARITH_RULE `4 <= R ==> ~(R = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `1 <= N /\ k <= N /\ N1 <= N /\ R EXP (10 * m) * R EXP (10 * m) <= N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `10 * m + 10 * m = 20 * m`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. &(num_of_int(z rem &N)) = z rem &N` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    MATCH_MP_TAC INT_REM_POS THEN REWRITE_TAC[INT_OF_NUM_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lf_hyp N (\y. gtnu W b (gtD w R) (gtP w R) (&y)) (2 * k) m k eta`
  ASSUME_TAC THENL
   [REWRITE_TAC[lf_hyp] THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`w:num`; `b:num`; `R:num`; `R EXP (10 * m)`; `N:num`; `Js:num->bool`;
      `c:num->num->int`]) THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  REMOVE_THEN "rel" MATCH_MP_TAC THEN
  EXISTS_TAC `\y. gtnu W b (gtD w R) (gtP w R) (&y)` THEN
  ASM_REWRITE_TAC[ETA_AX] THEN X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC GTFUN_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`w:num`; `A:num->bool`; `b:num`; `R:num`; `N:num`; `m:num`;
                `y:num`] GTFUN_LE_NU) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The mean of the W-tricked function of a dense set of primes.              *)
(* ------------------------------------------------------------------------- *)

let GTFUN_SUM_LOWER = prove
 (`!A W b R N c0.
        1 <= W /\ 1 <= R /\ &0 <= c0 /\
        (!y. A(W * y + b) ==> 2 * y + 2 <= N)
        ==> c0 * &(phi W) / &W * log(&R) *
            &(CARD {y | A(W * y + b) /\ R < W * y + b}) <=
            sum {y | y < N} (gtfun A W b R N c0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Yb = {y | (A:num->bool)(W * y + b) /\ R < W * y + b}` THEN
  SUBGOAL_THEN `Yb SUBSET {y:num | y < N}` ASSUME_TAC THENL
   [EXPAND_TAC "Yb" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(Yb:num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{y:num | y < N}` THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Yb (gtfun A W b R N c0)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC GTFUN_POS THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Yb (\y:num. c0 * &(phi W) / &W * log(&R))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[SUM_CONST] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:num` THEN EXPAND_TAC "Yb" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[gtfun] THEN
  SUBGOAL_THEN `y < N DIV 2` (fun th -> ASM_REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[GSYM LE_SUC_LT; LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[PHI_RATIO] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC);;

let RESIDUE_PIGEONHOLE = prove
 (`!W S. 2 <= W /\ FINITE S /\ (!p. p IN S ==> coprime(p,W))
         ==> ?b. 1 <= b /\ b < W /\
                 &(CARD S) <= &(phi W) * &(CARD {y | W * y + b IN S})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = {r | coprime(r,W) /\ r < W}` THEN
  SUBGOAL_THEN `FINITE(B:num->bool) /\ CARD B = phi W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[PHI_ALT; PHI_FINITE_LEMMA]; ALL_TAC] THEN
  SUBGOAL_THEN `~(B:num->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `1` THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM; COPRIME_1] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < phi W` ASSUME_TAC THENL
   [UNDISCH_TAC `CARD(B:num->bool) = phi W` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[CARD_EQ_0; ARITH_RULE `0 < n <=> ~(n = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum B (\r. &(CARD {p | p IN S /\ p MOD W = r})) = &(CARD(S:num->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\p:num. p MOD W`; `\p:num. &1:real`; `S:num->bool`;
                   `B:num->bool`] SUM_GROUP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[DIVISION; ARITH_RULE `2 <= W ==> ~(W = 0)`] THEN
      REWRITE_TAC[COPRIME_LMOD] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum S (\p:num. &1)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID]] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC CARD_EQ_SUM THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `S:num->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:num->bool`;
                 `\r. &(CARD {p | p IN S /\ p MOD W = r})`;
                 `&(CARD(S:num->bool)) / &(phi W)`] FMEAN_EXISTS_GE) THEN
  ASM_REWRITE_TAC[fmean; REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:num` THEN
  UNDISCH_TAC `(r:num) IN B` THEN EXPAND_TAC "B" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= r` ASSUME_TAC THENL
   [ASM_CASES_TAC `r = 0` THENL
     [UNDISCH_TAC `coprime(r,W)` THEN ASM_REWRITE_TAC[COPRIME_0] THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE {y | W * y + r IN (S:num->bool)}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:num. W * y + r`; `S:num->bool`] FINITE_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_LCANCEL] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= W ==> ~(W = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {p | p IN S /\ p MOD W = r} <= CARD {y | W * y + r IN S}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD(IMAGE (\y. W * y + r) {y | W * y + r IN (S:num->bool)})` THEN
    ASM_SIMP_TAC[CARD_IMAGE_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `p:num` THEN
    STRIP_TAC THEN EXISTS_TAC `p DIV W` THEN
    MP_TAC(SPECL [`p:num`; `W:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(phi W) * &(CARD {p | p IN S /\ p MOD W = r})` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_OF_NUM_LT];
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE]]);;

let LOG_SQUARE_SMALL = prove
 (`!e. &0 < e ==> ?X1. !X. X1 <= X ==> log(&X) pow 2 <= e * &X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(&16 / e) pow 2 + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `X1:num`) THEN EXISTS_TAC `X1:num` THEN
  X_GEN_TAC `X:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&16 / e) pow 2 + &1 <= &X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&X1` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&16 / e) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &X /\ &16 / e <= sqrt(&X)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`2`; `&X`] LOG_POW_LE_SQRT) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 * sqrt(&X)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&X = sqrt(&X) * sqrt(&X)`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&16 / e <= sqrt(&X)` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS]]);;

let LOG_ROOT_BOUND = prove
 (`!d R X. &0 < d /\ 1 <= X /\ (R + 1) * (R + 1) <= 32 * X /\
           log(&X) pow 2 <= d pow 2 / &512 * &X
           ==> &4 * (&R + &1) * log(&X) <= d * &X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log(&X)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `(&R + &1) pow 2 <= &32 * &X` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_OF_NUM_ADD; REAL_OF_NUM_MUL;
                REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&16 * (&32 * &X) * log(&X) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&X * (&512 * (d pow 2 / &512 * &X))` THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `&16 * (&32 * &X) * log(&X) pow 2 = &X * (&512 * log(&X) pow 2)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

let GT_DENSE_ARITH = prove
 (`!c0 d w lr lx x n m phw yn sn an r.
        &0 < c0 /\ &0 < d /\ &0 < w /\ &0 < lx /\ &0 < m /\ &0 <= lr /\
        &0 <= x /\ &0 <= n /\ lx <= &80 * m * lr /\ w * n <= &8 * x /\
        &4 * (r + &1) * lx <= d * x /\ d * (x / (&2 * lx)) <= an /\
        an - (r + &1) <= sn /\ sn <= phw * yn
        ==> (c0 * d / (&2560 * m)) * n <= c0 * phw / w * lr * yn`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = (d * x) / (&4 * lx)` THEN
  SUBGOAL_THEN `&0 <= t /\ t <= phw * yn` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `d * (x / (&2 * lx)) = &2 * t /\ r + &1 <= t`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < lx` THEN CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ;
                     REAL_ARITH `&0 < lx ==> &0 < &4 * lx`] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 * phw / w * lr * yn = (c0 * lr / w) * (phw * yn:real)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < w` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c0 * lr / w) * t:real` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]] THEN
  EXPAND_TAC "t" THEN
  SUBGOAL_THEN
   `(c0 * lr / w) * ((d * x) / (&4 * lx)) - (c0 * d / (&2560 * m)) * n =
    ((c0 * d) / (&2560 * m * w * lx)) * (&640 * m * lr * x - n * w * lx)`
  MP_TAC THENL
   [UNDISCH_TAC `&0 < w` THEN UNDISCH_TAC `&0 < lx` THEN
    UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= z ==> a - b = z ==> b <= a`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&8 * x) * (&80 * m * lr)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `n * w * lx = (w * n) * lx:real` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let GT_DENSE_MEAN = prove
 (`!A W b R N X m delta.
        2 <= W /\ 1 <= m /\ 2 <= R /\ 2 <= X /\ &0 < delta /\
        2 * (X DIV W) + 2 <= N /\ W * N <= 8 * X /\ X <= N * N /\
        N <= R EXP (40 * m) /\
        &4 * (&R + &1) * log(&X) <= delta * &X /\
        delta * (&X / (&2 * log(&X))) <= &(CARD {p | p IN A /\ p <= X}) /\
        &(CARD {p | p IN A /\ p <= X /\ R < p}) <=
        &(phi W) *
        &(CARD {y | W * y + b IN {p | p IN A /\ p <= X /\ R < p}})
        ==> inv(&(80 * m)) * delta / (&2560 * &m) <=
            fmean {y | y < N}
              (gtfun (\p. p IN A /\ p <= X) W b R N (inv(&(80 * m))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c0 = inv(&(80 * m))` THEN
  SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = {p:num | p IN A /\ p <= X /\ R < p}` THEN
  ABBREV_TAC `Yb = {y | W * y + b IN (S:num->bool)}` THEN
  MP_TAC(ISPECL [`\p:num. p IN A /\ p <= X`; `W:num`; `b:num`; `R:num`;
                 `N:num`; `c0:real`] GTFUN_SUM_LOWER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y <= X DIV W` MP_TAC THENL
     [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `2 <= W ==> ~(W = 0)`] THEN
      ASM_ARITH_TAC;
      UNDISCH_TAC `2 * X DIV W + 2 <= N` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{y:num | (\p:num. p IN A /\ p <= X) (W * y + b) /\ R < W * y + b} =
    Yb`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Yb"; "S"] THEN
    REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | p <= X}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LE] THEN EXPAND_TAC "S" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {p:num | p IN A /\ p <= X} <= CARD(S:num->bool) + (R + 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD((S:num->bool) UNION {p:num | p <= R})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC[FINITE_UNION; FINITE_NUMSEG_LE] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      MESON_TAC[NOT_LT];
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD(S:num->bool) + CARD {p:num | p <= R}` THEN
      ASM_SIMP_TAC[CARD_UNION_LE; FINITE_NUMSEG_LE] THEN
      REWRITE_TAC[CARD_NUMSEG_LE; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&X) <= &80 * &m * log(&R)` ASSUME_TAC THENL
   [SUBGOAL_THEN `X <= R EXP (80 * m)` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N * N:num` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `80 * m = 40 * m + 40 * m`; EXP_ADD] THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&R pow (80 * m))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[LOG_POW; REAL_OF_NUM_LT; ARITH_RULE `2 <= R ==> 0 < R`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[fmean; CARD_NUMSEG_LT] THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c0 * &(phi W) / &W * log(&R) * &(CARD(Yb:num->bool))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GT_DENSE_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`log(&X)`; `&X`; `&(CARD(S:num->bool))`;
    `&(CARD {p:num | p IN A /\ p <= X})`; `&R`] THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE];
    REWRITE_TAC[REAL_ARITH `a - b <= c <=> a <= c + b:real`; REAL_OF_NUM_ADD;
                REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* From progressions mod N to progressions in A.                             *)
(* ------------------------------------------------------------------------- *)

let GT_PAIRS_COUNT = prove
 (`!k N W b X R c (f:num->real) (Q:num->bool).
        2 <= k /\ 1 <= W /\ 2 <= R /\ R <= X /\ X < W * N /\
        R EXP (k + 1) < N /\ &0 < c /\ &2 <= c * &R /\
        (!z. z < N ==> &0 <= f z /\ f z <= log(&R)) /\
        (!z. &0 < f z ==> 2 * z < N /\ Q(W * z + b) /\ W * z + b <= X) /\
        c <= fmean {a | a < N}
               (\a. fmean {d | d < N}
                      (\d. product {j | j < k} (\j. f((a + j * d) MOD N))))
        ==> c / &4 / &W pow 2 * &X pow 2 / log(&X) pow k <=
            &(CARD {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                            !j. j < k ==> Q(a + j * d)})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `f:num->real`; `log(&R)`]
    AP_COUNT_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `W:num`; `b:num`; `X:num`;
                `\z. &0 < (f:num->real) z`; `Q:num->bool`]
    PROGRESSIONS_FROM_PAIRS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_MUL] o
             GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
  ABBREV_TAC
   `ap = fmean {a | a < N}
           (\a. fmean {d | d < N}
                  (\d. product {j | j < k}
                         (\j. (f:num->real)((a + j * d) MOD N))))` THEN
  ABBREV_TAC
   `sp = &(CARD {(a,d) | a < N /\ 0 < d /\ d < N /\
                         !j. j < k ==> &0 < (f:num->real)((a + j * d) MOD N)})`
  THEN
  ABBREV_TAC
   `tc = &(CARD {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                         !j. j < k ==> (Q:num->bool)(a + j * d)})` THEN
  ABBREV_TAC `B = log(&R)` THEN
  SUBGOAL_THEN `&0 <= B /\ B <= &R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_LE_REFL THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * B pow k <= c * &N` ASSUME_TAC THENL
   [SUBGOAL_THEN `&R pow k * &R < &N` ASSUME_TAC THENL
     [MP_TAC(ASSUME `R EXP (k + 1) < N`) THEN
      REWRITE_TAC[EXP_ADD; EXP_1] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_LE;
                  GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `B pow k <= &R pow k` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c * &R) * &R pow k` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &R pow k` THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]];
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * &N pow 2 <= &4 * tc * B pow k` ASSUME_TAC THENL
   [SUBGOAL_THEN `c * &N pow 2 <= &N pow 2 * ap` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&N * (&2 * B pow k) <= &N * (c * &N)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `sp * B pow k <= (&2 * tc) * B pow k` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&X)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `B <= log(&X)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= tc` ASSUME_TAC THENL
   [EXPAND_TAC "tc" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `tc * B pow k <= tc * log(&X) pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&X pow 2 <= &W pow 2 * &N pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_POS; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = log(&X) pow k` THEN
  SUBGOAL_THEN `&0 < L /\ &0 < &W pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c / &4 / &W pow 2 * &X pow 2 / L = (c * &X pow 2) / (&4 * &W pow 2 * L)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < L` THEN UNDISCH_TAC `&0 < &W pow 2` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * &W pow 2 * L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * (&W pow 2 * &N pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&W pow 2 * (&4 * tc * B pow k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!w c n x:real. w * (c * n) <= w * x ==> c * (w * n) <= w * x`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `tc * (&4 * &W pow 2 * L) = &W pow 2 * (&4 * (tc * L))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC]);;

let ROOT_CHOICE = prove
 (`!e N R0. 1 <= e /\ 2 <= R0 /\ R0 EXP e < N
            ==> ?R. R0 <= R /\ R EXP e < N /\ N <= R EXP (2 * e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\r. r EXP e < N` num_MAX) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `R0:num` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `N:num` THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `r EXP e` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
      ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `R:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= R` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `R0:num` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `N <= (R + 1) EXP e` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `R + 1`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(R + 1) EXP e` THEN
  ASM_REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 * R` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP_2; LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

let PRIME_DOUBLE_INTERVAL = prove
 (`?y0. !y. y0 <= y ==> ?p. prime p /\ y < p /\ p <= 2 * y`,
  EXISTS_TAC `1` THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC BERTRAND THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Green-Tao theorem for dense subsets of the primes.                    *)
(* ------------------------------------------------------------------------- *)

let GREEN_TAO_DENSE_COUNT = prove
 (`!k delta.
        2 <= k /\ &0 < delta
        ==> ?c X0. &0 < c /\
                   !A X. A SUBSET {p | prime p} /\ X0 <= X /\
                         delta * &(CARD {p | prime p /\ p <= X}) <=
                         &(CARD {p | p IN A /\ p <= X})
                         ==> c * &X pow 2 / log(&X) pow k <=
                             &(CARD {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                                             !j. j < k ==> a + j * d IN A})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`k:num`;
    `inv(&(80 * CARD(lf_index k))) * delta / (&2560 * &(CARD(lf_index k)))`]
   GT_AP_LOWER) THEN
  ABBREV_TAC `m = CARD(lf_index k)` THEN
  ABBREV_TAC `c0 = inv(&(80 * m))` THEN
  SUBGOAL_THEN `k <= m /\ 1 <= m` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` CARD_LF_INDEX_GE) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num` (X_CHOOSE_THEN `R0:num`
   (X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "core"))))))) THEN
  X_CHOOSE_TAC `R2:num` (SPEC `&2 / c` REAL_ARCH_SIMPLE) THEN
  ABBREV_TAC `R3 = R0 + R2:num` THEN
  X_CHOOSE_THEN `y0:num` (LABEL_TAC "bertrand") PRIME_DOUBLE_INTERVAL THEN
  X_CHOOSE_THEN `N0:num` (LABEL_TAC "pnt") PI_LOWER THEN
  MP_TAC(SPEC `delta pow 2 / &512` LOG_SQUARE_SMALL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "lsq"))] THEN
  EXISTS_TAC `c / &4 / &W pow 2` THEN
  EXISTS_TAC `W * (y0 + R3 EXP (20 * m) + 3) + N0 + N1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`A:num->bool`; `X:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `y0 + R3 EXP (20 * m) + 3 <= X DIV W /\ W * X DIV W <= X /\
    X < W * (X DIV W + 1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`X:num`; `W:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `2 <= W ==> ~(W = 0)`] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y = X DIV W` THEN
  REMOVE_THEN "bertrand" (MP_TAC o SPEC `2 * y + 2`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `2 <= R3 /\ R0 <= R3 /\ R2 <= R3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R3" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`20 * m`; `N:num`; `R3:num`] ROOT_CHOICE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * 20 * m = 40 * m`] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `4 <= R /\ 2 <= R /\ W <= R /\ R0 <= R /\ R2 <= R /\ 1 <= W`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `R EXP (k + 1) <= R EXP (20 * m) /\ R * R <= R EXP (20 * m)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[GSYM EXP_2]] THEN
    ASM_SIMP_TAC[LE_EXP; ARITH_RULE `4 <= R ==> ~(R = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * R <= R * R` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  SUBGOAL_THEN `2 * y <= W * y /\ W <= W * y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `W = W * 1`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `W * N <= W * (4 * y + 4) /\ W * (y + 1) <= W * N /\ W * N <= N * N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL; LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `W * (4 * y + 4) = 4 * (W * y) + 4 * W`
  ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(R + 1) * (R + 1) <= 4 * (R * R)` ASSUME_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `W * N <= 8 * X /\ X < W * N /\ X <= N * N /\ R <= X /\ 2 <= X /\
    (R + 1) * (R + 1) <= 32 * X`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (&R + &1) * log(&X) <= delta * &X` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_ROOT_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; REMOVE_THEN "lsq" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `delta * (&X / (&2 * log(&X))) <= &(CARD {p:num | p IN A /\ p <= X})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `delta * &(CARD {p | prime p /\ p <= X})` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REMOVE_THEN "pnt" MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:num`; `{p:num | p IN A /\ p <= X /\ R < p}`]
    RESIDUE_PIGEONHOLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | p <= X}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LE] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `prime p` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`A:num->bool`; `W:num`; `b:num`; `R:num`; `N:num`; `X:num`;
                `m:num`; `delta:real`] GT_DENSE_MEAN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REMOVE_THEN "core" (MP_TAC o SPECL
   [`\p:num. p IN A /\ p <= X`; `b:num`; `R:num`; `N:num`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `R EXP (k + 1) < N /\ &2 <= c * &R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * &R2` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ];
        MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `W:num`; `b:num`; `X:num`; `R:num`;
                 `c:real`; `gtfun (\p:num. p IN A /\ p <= X) W b R N c0`;
                 `\x:num. x IN A`] GT_PAIRS_COUNT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC GTFUN_POS THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      EXPAND_TAC "c0" THEN MATCH_MP_TAC GTFUN_LE_LOGR THEN ASM_ARITH_TAC];
    X_GEN_TAC `z:num` THEN DISCH_THEN(MP_TAC o MATCH_MP GTFUN_POS_IMP) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `z < N DIV 2` THEN ARITH_TAC]);;

let GREEN_TAO_DENSE = prove
 (`!A k. A SUBSET {p | prime p} /\
         (?delta. &0 < delta /\
                  !X0. ?X. X0 <= X /\
                           delta * &(CARD {p | prime p /\ p <= X}) <=
                           &(CARD {p | p IN A /\ p <= X}))
         ==> ?a d. 0 < d /\ !j. j < k ==> a + j * d IN A`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 <= k` THENL
   [MP_TAC(SPECL [`k:num`; `delta:real`] GREEN_TAO_DENSE_COUNT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `X0:num`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `X0 + 3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `X:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`A:num->bool`; `X:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC
     `Z = {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                   !j. j < k ==> a + j * d IN (A:num->bool)}` THEN
    ASM_CASES_TAC `Z:num#num->bool = {}` THENL
     [ASM_REWRITE_TAC[CARD_CLAUSES] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LT THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC];
      DISCH_THEN(K ALL_TAC) THEN UNDISCH_TAC `~(Z:num#num->bool = {})` THEN
      EXPAND_TAC "Z" THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; EXISTS_PAIR_THM;
        IN_ELIM_PAIR_THM] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:num. a IN A` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
    DISCH_THEN(X_CHOOSE_THEN `X:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `1 <= CARD {p | prime p /\ p <= X}` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
      SIMP_TAC[CARD_EQ_0; FINITE_ATMOST] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `2` THEN ASM_REWRITE_TAC[PRIME_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `~({p:num | p IN A /\ p <= X} = {})` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
       `delta * &(CARD {p | prime p /\ p <= X}) <=
        &(CARD {p:num | p IN A /\ p <= X})` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES; REAL_NOT_LE] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `1`] THEN REWRITE_TAC[ARITH_RULE `0 < 1`] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let GREEN_TAO_DENSE_INFINITE = prove
 (`!A k. A SUBSET {p | prime p} /\
         (?delta. &0 < delta /\
                  !X0. ?X. X0 <= X /\
                           delta * &(CARD {p | prime p /\ p <= X}) <=
                           &(CARD {p | p IN A /\ p <= X}))
         ==> INFINITE {(a,d) | 0 < d /\ !j. j < k ==> a + j * d IN A}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC
   `{(a,d) | 0 < d /\ !j. j < MAX k 2 ==> a + j * d IN (A:num->bool)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MESON_TAC[ARITH_RULE `j < k ==> j < MAX k 2`]] THEN
  ABBREV_TAC `n = MAX k 2` THEN
  SUBGOAL_THEN `2 <= n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `delta:real`] GREEN_TAO_DENSE_COUNT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `X0:num`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC
   `Z = {(a,d) | 0 < d /\ !j. j < n ==> a + j * d IN (A:num->bool)}` THEN
  REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  MP_TAC(SPEC `((&(CARD(Z:num#num->bool)) + &1) * (&2 * &n) pow n) / c`
    REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `X0 + M + 3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `X:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`A:num->bool`; `X:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {(a,d) | 0 < d /\ a + (n - 1) * d <= X /\
                  !j. j < n ==> a + j * d IN (A:num->bool)} <=
    CARD(Z:num#num->bool)`
  (MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Z" THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `z < x ==> s <= z ==> x <= s ==> F`) THEN
  SUBGOAL_THEN `&0 < log(&X)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&X) pow n /\ &0 < (&2 * &n) pow n`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LT THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&X) pow n <= (&2 * &n) pow n * &X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * &n) pow n * sqrt(&X)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POW_LE_SQRT THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POS; REAL_POW_2] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `X = 1 * X`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&(CARD(Z:num#num->bool)) + &1) * (&2 * &n) pow n <= c * &X`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * &M` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ];
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `(&(CARD(Z:num#num->bool)) + &1) * log(&X) pow n` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(&(CARD(Z:num#num->bool)) + &1) * ((&2 * &n) pow n * &X)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `CARD(Z:num#num->bool)` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c * &X) * &X` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_POS];
    REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The Green-Tao theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let GREEN_TAO_COUNT = prove
 (`!k. 2 <= k
       ==> ?c X0. &0 < c /\
                  !X. X0 <= X
                      ==> c * &X pow 2 / log(&X) pow k <=
                          &(CARD {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                                          !j. j < k ==> prime(a + j * d)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `&1`] GREEN_TAO_DENSE_COUNT) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `X0:num`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `X0:num`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `X:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{p:num | prime p}`; `X:num`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; IN_ELIM_THM; REAL_MUL_LID; REAL_LE_REFL]);;

let GREEN_TAO = prove
 (`!k. ?a d. 0 < d /\ !j. j < k ==> prime(a + j * d)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`{p:num | prime p}`; `k:num`] GREEN_TAO_DENSE) THEN
  REWRITE_TAC[SUBSET_REFL; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `&1` THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; REAL_LE_REFL] THEN
  MESON_TAC[LE_REFL]);;
