(* ========================================================================= *)
(* The limit formula at s = 1: the Poisson kernel up to an exponentially     *)
(* small error, and the mean of the Ramanujan sums.                          *)
(*                                                                           *)
(* Purpose: the tools of the limit formula for a general positive definite   *)
(* form (Baker/qform_limit.ml). CLASSNO_LIMIT_KERNEL_BOUND: the Poisson      *)
(* kernel G(t,c) = (pi/c) sinh(2 pi c) / (cosh(2 pi c) - cos(2 pi t))        *)
(* satisfies abs(G - pi/c) <= (pi/c) 2 q (1 + q) / (1 - q)^2, q = exp(-2 pi  *)
(* c). CLASSNO_LIMIT_MEAN_ZERO: for k = p q the sum over y <= k N of c(y) /  *)
(* y, c(y) = 1 - p [p divides y] - q [q divides y] + k [k divides y] (the    *)
(* Ramanujan sum c_k(y) for distinct primes p, q), tends to 0 (harmonic sums *)
(* and EULER_MASCHERONI). Geometric bounds for the errors of the slices      *)
(* (CLASSNO_LIMIT_GEOM_TERM, CLASSNO_LIMIT_GP_BOUND); arithmetic helpers     *)
(* (CLASSNO_LIMIT_C0, CLASSNO_LIMIT_SUM_BLOCKS,                              *)
(* CLASSNO_LIMIT_SUM_MOD_PERMUTE, CLASSNO_LIMIT_PRIMES). The bound for the   *)
(* slices of the principal form (CLASSNO_SLICE_BOUND, the                    *)
(* estimate of the terms A_r of the limit formula in Baker, Transcendental   *)
(* Number Theory, Ch. 5, sec. 3, together with A_0 = 0 for k not a prime     *)
(* power) is a corollary of QFORM_SLICE_BOUND (Baker/qform_limit.ml).        *)
(*                                                                           *)
(* Main results: CLASSNO_LIMIT_KERNEL_BOUND, CLASSNO_LIMIT_MEAN_ZERO; helper *)
(* names CLASSNO_LIMIT_*.                                                    *)
(*                                                                           *)
(* Uses: Baker/classno_series.ml (CLASSNO_SERIES_REALLIM_SUBSEQ,             *)
(* CLASSNO_SERIES_C0), Baker/laurent_corner.ml (LAURENT_CORNER_DIV_LE);      *)
(* Multivariate/gamma.ml (EULER_MASCHERONI).                                 *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files, 100/dirichlet.ml before *)
(* Multivariate/gamma.ml), so that the file also loads alone.                *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Multivariate/gamma.ml";;
needs "Baker/laurent_corner.ml";;
needs "Baker/classno_series.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The Poisson kernel is pi/c up to an exponentially small error.            *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LIMIT_KERNEL_RATIO = prove
 (`!q w. &0 < q /\ q < &1 /\ abs w <= &1
         ==> abs((inv q - q) / (inv q + q - &2 * w) - &1)
             <= (&2 * q * (&1 + q)) / (&1 - q) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(inv q + q - &2 * w) * q = &1 + q pow 2 - &2 * w * q`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - q) pow 2 <= (inv q + q - &2 * w) * q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `w * q <= &1 * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - q) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv q + q - &2 * w` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&0`; `inv q + q - &2 * w`; `q:real`] REAL_LT_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(inv q - q) / (inv q + q - &2 * w) - &1 =
    (&2 * q * (w - q)) / ((inv q + q - &2 * w) * q)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < q`; `&0 < inv q + q - &2 * w`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  MATCH_MP_TAC LAURENT_CORNER_DIV_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < q ==> abs q = q`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let CLASSNO_LIMIT_KERNEL_BOUND = prove
 (`!t c. &0 < c
         ==> abs(pi / c * (exp(&2 * pi * c) - exp(--(&2 * pi * c))) /
                          (exp(&2 * pi * c) + exp(--(&2 * pi * c)) -
                           &2 * cos(&2 * pi * t)) - pi / c)
             <= pi / c *
                (&2 * exp(--(&2 * pi * c)) * (&1 + exp(--(&2 * pi * c)))) /
                (&1 - exp(--(&2 * pi * c))) pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = exp(--(&2 * pi * c))` THEN
  SUBGOAL_THEN `exp(&2 * pi * c) = inv q` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q /\ q < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_NEG_LT0] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[PI_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < pi / c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a * x - a:real = a * (x - &1)`] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CLASSNO_LIMIT_KERNEL_RATIO THEN ASM_REWRITE_TAC[COS_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic helpers: c0 = (d + 1) / 4, grouping by the residues modulo k,  *)
(* permutations of the residues, the primes 3, 7 and 11.                     *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LIMIT_C0 = prove
 (`!d. d MOD 4 = 3 ==> 4 * ((d + 1) DIV 4) = d + 1 /\ 3 <= d`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLASSNO_SERIES_C0] THEN
  MP_TAC(SPECL [`d:num`; `4`] MOD_LE) THEN ASM_ARITH_TAC);;

let CLASSNO_LIMIT_LE_MULT = prove
 (`!k n. 1 <= k ==> n <= k * n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `k:num`; `n:num`] LE_MULT_RCANCEL) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES]);;

(* Grouping the n < k (N + 1) by their residues m modulo k.                  *)

let CLASSNO_LIMIT_SUM_BLOCKS = prove
 (`!f k N. 1 <= k
           ==> sum(0..k * N + (k - 1)) f =
               sum(0..k - 1) (\m. sum(0..N) (\j. f(k * j + m)))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUM_SING_NUMSEG; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * SUC N + (k - 1) = (k * N + (k - 1)) + k` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP (ISPECL [`f:num->real`; `0`; `k * N + (k - 1)`; `k:num`]
                SUM_ADD_SPLIT) (ARITH_RULE `0 <= (k * N + (k - 1)) + 1`)] THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; SUM_ADD_NUMSEG] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(k * N + (k - 1)) + 1 = 0 + k * SUC N /\
                (k * N + (k - 1)) + k = (k - 1) + k * SUC N`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET] THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN ARITH_TAC);;

(* x -> a x + b permutes the residues modulo k when coprime(a,k).            *)

let CLASSNO_LIMIT_SUM_MOD_PERMUTE = prove
 (`!g k a b. 1 <= k /\ coprime(a,k)
             ==> sum(0..k - 1) (\m. g((a * m + b) MOD k)) = sum(0..k - 1) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN 0..k - 1 /\ y IN 0..k - 1 /\
                      (a * x + b) MOD k = (a * y + b) MOD k ==> x = y`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `k:num` THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    UNDISCH_TAC `(a * x + b) MOD k = (a * y + b) MOD k` THEN
    REWRITE_TAC[GSYM CONG] THEN UNDISCH_TAC `coprime(a:num,k)` THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m. (a * m + b) MOD k`; `g:num->real`; `0..k - 1`]
    SUM_IMAGE) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < k ==> x <= k - 1`) THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[FINITE_NUMSEG]]);;

let CLASSNO_LIMIT_PRIMES = prove
 (`prime 3 /\ prime 7 /\ prime 11`,
  REPEAT CONJ_TAC THEN CONV_TAC PRIME_CONV);;

(* ------------------------------------------------------------------------- *)
(* The mean of c_k(y)/y vanishes along the partial sums up to k N.           *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LIMIT_HARMONIC_MULTIPLES = prove
 (`!a M. 1 <= a
         ==> sum(1..a * M) (\y. (&a * (if a divides y then &1 else &0)) / &y) =
             sum(1..M) (\j. inv(&j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y. (&a * (if a divides y then &1 else &0)) / &y =
                    if a divides y then &a / &y else &0`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{y | y IN 1..a * M /\ a divides y} = IMAGE (\j. a * j) (1..M)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `y:num` THEN EQ_TAC THENL
     [REWRITE_TAC[divides] THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
       (X_CHOOSE_THEN `j:num` SUBST1_TAC)) THEN
      STRIP_TAC THEN EXISTS_TAC `j:num` THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `~(j = 0) ==> 1 <= j`) THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `1 <= a * 0` THEN REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
        UNDISCH_TAC `a * j <= a * M` THEN REWRITE_TAC[LE_MULT_LCANCEL] THEN
        ASM_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
        ASM_ARITH_TAC;
        ASM_REWRITE_TAC[LE_MULT_LCANCEL];
        NUMBER_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN 1..M /\ y IN 1..M /\ a * x = a * y ==> x = y`
  ASSUME_TAC THENL
   [REWRITE_TAC[EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\j. a * j`; `\y. &a / &y`; `1..M`] SUM_IMAGE) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `~(&a:real = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* H(r N) - log(r N) -> Euler gamma, hence H(pq N) - H(q N) - H(p N) + H(N)  *)
(* -> log(pq) - log q - log p = 0.                                           *)

let CLASSNO_LIMIT_HARMONIC_SUBSEQ = prove
 (`!r. 1 <= r
       ==> ((\N. sum(1..r * N) (\j. inv(&j)) - log(&(r * N))) --->
            euler_mascheroni) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. sum(1..n) (\j. inv(&j)) - log(&n)`;
                 `euler_mascheroni`; `\N. r * N`]
    CLASSNO_SERIES_REALLIM_SUBSEQ) THEN
  REWRITE_TAC[EULER_MASCHERONI] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CLASSNO_LIMIT_LE_MULT]);;

let CLASSNO_LIMIT_HARMONIC_LIMIT = prove
 (`!k p q. k = p * q /\ 1 <= p /\ 1 <= q
           ==> ((\N. sum(1..k * N) (\j. inv(&j)) -
                     sum(1..q * N) (\j. inv(&j)) -
                     sum(1..p * N) (\j. inv(&j)) +
                     sum(1..N) (\j. inv(&j))) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\N. ((sum(1..k * N) (\j. inv(&j)) - log(&(k * N))) -
         (sum(1..q * N) (\j. inv(&j)) - log(&(q * N))) -
         (sum(1..p * N) (\j. inv(&j)) - log(&(p * N)))) +
        (sum(1..1 * N) (\j. inv(&j)) - log(&(1 * N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    SUBGOAL_THEN `&0 < &p /\ &0 < &q /\ &0 < &N` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 = (euler_mascheroni - euler_mascheroni - euler_mascheroni) +
         euler_mascheroni`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT((MATCH_MP_TAC REALLIM_ADD ORELSE MATCH_MP_TAC REALLIM_SUB) THEN
         CONJ_TAC) THEN
  MATCH_MP_TAC CLASSNO_LIMIT_HARMONIC_SUBSEQ THEN ASM_REWRITE_TAC[LE_REFL]);;

let CLASSNO_LIMIT_MEAN_ZERO = prove
 (`!k p q. k = p * q /\ 1 <= p /\ 1 <= q
           ==> ((\N. sum(1..k * N)
                      (\y. (&1 - &p * (if p divides y then &1 else &0) -
                            &q * (if q divides y then &1 else &0) +
                            &k * (if k divides y then &1 else &0)) / &y))
                ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a - b - c + e) / y = a / y - b / y - c / y + e / y`;
              SUM_ADD_NUMSEG; SUM_SUB_NUMSEG] THEN
  SUBGOAL_THEN
   `!N. sum(1..k * N) (\y. (&p * (if p divides y then &1 else &0)) / &y) =
        sum(1..q * N) (\j. inv(&j)) /\
        sum(1..k * N) (\y. (&q * (if q divides y then &1 else &0)) / &y) =
        sum(1..p * N) (\j. inv(&j)) /\
        sum(1..k * N) (\y. (&k * (if k divides y then &1 else &0)) / &y) =
        sum(1..N) (\j. inv(&j)) /\
        sum(1..k * N) (\y. &1 / &y) = sum(1..k * N) (\j. inv(&j))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `k * N = p * (q * N)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[MULT_ASSOC];
        ASM_SIMP_TAC[CLASSNO_LIMIT_HARMONIC_MULTIPLES]];
      SUBGOAL_THEN `k * N = q * (p * N)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[MULT_AC];
        ASM_SIMP_TAC[CLASSNO_LIMIT_HARMONIC_MULTIPLES]];
      ASM_SIMP_TAC[CLASSNO_LIMIT_HARMONIC_MULTIPLES];
      REWRITE_TAC[real_div; REAL_MUL_LID]];
    ALL_TAC] THEN
  MATCH_MP_TAC CLASSNO_LIMIT_HARMONIC_LIMIT THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Geometric bounds for the errors of the slices.                            *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LIMIT_GEOM_TERM = prove
 (`!eta x y. &0 < eta /\ eta < &1 /\ &0 <= x /\ x <= eta /\ &1 <= y
             ==> (x * (&1 + x)) / (&1 - x) pow 2 / y <=
                 (&1 + eta) / (&1 - eta) pow 2 * x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(x * (&1 + x)) / (&1 - x) pow 2 / y =
    (x * (&1 + x)) / ((&1 - x) pow 2 * y) /\
    (&1 + eta) / (&1 - eta) pow 2 * x = (x * (&1 + eta)) / (&1 - eta) pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LAURENT_CORNER_DIV_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - x) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]]);;
let CLASSNO_LIMIT_GP_BOUND = prove
 (`!eta n. &0 <= eta /\ eta < &1
           ==> sum(1..n) (\y. eta pow y) <= eta / (&1 - eta)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUM_GP] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_SUB_LT; REAL_POW_1] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]);;
