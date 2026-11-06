(* ========================================================================= *)
(* Goldbach's problem for almost all even numbers (Chudakov, van der         *)
(* Corput, Estermann, 1937-38): the exceptional set is O(N / log^A N).       *)
(*   GOLDBACH_ALMOST_ALL:                                                    *)
(*     !A. ?N0. !N. N0 <= N                                                  *)
(*                  ==> &(CARD {n | n <= N /\ EVEN n /\                      *)
(*                                  ~(?p q. prime p /\ prime q /\            *)
(*                                          p + q = n)})                     *)
(*                      <= &N / log(&N) pow A                                *)
(*   GOLDBACH_ALMOST_ALL_DENSITY: the proportion of the n <= N that are      *)
(*   even but not a sum of two primes tends to 0.                            *)
(*   GOLDBACH_VARIANCE, the variance of the binary problem: for every A      *)
(*   and all large N there is Q with log^A N <= sqrt Q, Q <= log^(4A+14) N   *)
(*   and                                                                     *)
(*     sum_{n <= 2N} (goldbach_rep2 N n - goldbach_pair2 N n sing2_series n  *)
(*     Q)^2                                                                  *)
(*       <= N^3 / log^A N                                                    *)
(*   (also the main step for 3-term progressions of primes,                  *)
(*   van_der_corput.ml).                                                     *)
(*                                                                           *)
(* Method: the discrete circle method of vinogradov.ml in mean square over   *)
(* n (the variance of the binary problem) instead of at a single n.          *)
(* * goldbach_rep2 N n = sum over m1 + m2 = n of w(m1) w(m2), w(m) = [prime  *)
(*   m] log m, and goldbach_pair2 N n = #{m1 + m2 = n, m1, m2 <= N} = n - 1  *)
(*   (GOLDBACH_PAIR2_EQ).  With M = 2 N + 1, BINARY_CIRCLE and               *)
(*   CIRCLE_GOLDBACH_REP2:                                                   *)
(*     sum_{k < M} primexp N (k/M)^2 e(-n k/M) = M goldbach_rep2 N n,        *)
(*   and DFT_PARSEVAL is Parseval for the discrete Fourier transform.        *)
(* * Binary singular series: sing2_series n Q = sum_{q <= Q} (mu(q) /        *)
(*   phi(q))^2 ramanujan_sum q n.  Its Euler product over the primes p <= Q  *)
(*   is at least 1 for even n (SING2_PRODUCT_LOWER), and the tail is small   *)
(*   on average over n (SING2_TAIL_L1:                                       *)
(*     sum_{n <= N} |sing2_series n Q - product| <= e^16 N / sqrt Q,         *)
(*   from sum_{n <= N} |ramanujan_sum q n| <= N tau(q) and Rankin's trick).  *)
(* * goldbach_major2 N M Q k = sum_{q <= Q} sum_a (mu(q)/phi(q))^2 unitexp N *)
(*   (k/M - a/q)^2 has transform M goldbach_pair2 N n sing2_series n Q       *)
(*   (CIRCLE_GOLDBACH_MAJOR2), so Parseval gives VARIANCE_IDENTITY:          *)
(*     sum_{n < M} (goldbach_rep2 N n - goldbach_pair2 N n sing2_series n    *)
(*     Q)^2                                                                  *)
(*       = sum_{k < M} |primexp N (k/M)^2 - goldbach_major2 N M Q k|^2 / M.  *)
(* * VARIANCE_BOUND: goldbach_major2 = goldbach_inarc2 + goldbach_outarc2,   *)
(*   the term of the major arc containing k plus the rest.  Off its arc      *)
(*   |unitexp| <= 2 Kw (ARC_UNITEXP_BOUND), which bounds sum_k               *)
(*   |goldbach_outarc2|^2 (GOLDBACH_OUTARC2_SQUARE).  On the major arcs |F^2 *)
(*   - Phi^2|^2 <= 2 E^2 (|F|^2 + |Phi|^2) with E the error of ARC_APPROX    *)
(*   (Siegel-Walfisz); on the minor arcs |F|^4 <= B^2 |F|^2 with B from      *)
(*   MINOR_POINT_BOUND; then Parseval for primexp.                           *)
(* * GOLDBACH_FIXED: an even n <= N that is not a sum of two primes has      *)
(*   goldbach_rep2 N n = 0, so either n < h, or |sing2_series n Q - product| *)
(*   >= 1/2, or (goldbach_rep2 N n - goldbach_pair2 N n sing2_series n Q)^2  *)
(*   >= (h/4)^2; the last two sets are counted by Markov's inequality        *)
(*   (MARKOV_CARD).                                                          *)
(* * GOLDBACH_VARIANCE: with L = log N, Y = L^A, R about Y^2 L^7, Q = R^2,   *)
(*   Kw = N DIV Q and the Siegel-Walfisz constant for the exponents          *)
(*   10 A + 35 and 4 A + 14 (THETA_AP_UNIFORM), the bound of                 *)
(*   VARIANCE_BOUND is at most N^3 / (64 Y^3 L^2) for all large N            *)
(*   (GV1_BOUND, GV2_BOUND, GV3_BOUND).                                      *)
(* * GOLDBACH_ALMOST_ALL: GOLDBACH_FIXED with h = N/(Y L) and the Q of       *)
(*   GOLDBACH_VARIANCE for the exponent 3 A + 9; every term is at most       *)
(*   N/(4 Y) (G_SMALL, G_SING, G_VAR).                                       *)
(* ========================================================================= *)

needs "Sieve/vinogradov.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The binary circle identity; Parseval for the discrete transform.          *)
(* ------------------------------------------------------------------------- *)

let EXPI_PAIR = prove
 (`!a b p q n x.
     ((Cx a * expi(p * x)) * (Cx b * expi(q * x))) * expi(--(n * x)) =
     Cx(a * b) * expi(((p + q) - n) * x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `((p + q) - n) * x:real =
                          p * x + (q * x + --(n * x))`] THEN
  REWRITE_TAC[EXPI_ADD; CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let SQUARE_EXPAND = prove
 (`!(w:num->real) N n x.
     vsum(1..N) (\m. Cx(w m) * expi(&m * x)) pow 2 * expi(--(&n * x)) =
     vsum(1..N) (\m1. vsum(1..N) (\m2.
       Cx(w m1 * w m2) * expi(((&m1 + &m2) - &n) * x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPLEX_POW_2] THEN
  SIMP_TAC[VSUM_MUL_VSUM; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[EXPI_PAIR]);;

let VSUM_SWAP2 = prove
 (`!(G:num->num->num->complex) N M.
     vsum {k | k < M} (\k. vsum(1..N) (\m1. vsum(1..N) (\m2. G m1 m2 k))) =
     vsum(1..N) (\m1. vsum(1..N) (\m2. vsum {k | k < M} (\k. G m1 m2 k)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(GEN `f:num->num->complex`
   (MP (ISPECL [`f:num->num->complex`; `{k:num | k < M}`; `1..N`] VSUM_SWAP)
       (CONJ (SPEC `M:num` FINITE_NUMSEG_LT)
             (SPECL [`1`; `N:num`] FINITE_NUMSEG)))) THEN
  DISCH_THEN(fun sw ->
    GEN_REWRITE_TAC LAND_CONV [sw] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m1:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [sw] THEN REWRITE_TAC[]));;

let BINARY_CIRCLE = prove
 (`!(w:num->real) N M n t.
     2 * N < M /\ n < M
     ==> vsum {k | k < M}
           (\k. vsum(1..N) (\m. Cx(w m) * expi(&m * (&k / &M + t))) pow 2 *
                expi(--(&n * (&k / &M + t)))) =
         Cx(&M * sum(1..N) (\m1. sum(1..N) (\m2.
                   if m1 + m2 = n then w m1 * w m2 else &0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SQUARE_EXPAND; VSUM_SWAP2] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m1:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m2:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `s = (&m1 + &m2) - &n` THEN
  SUBGOAL_THEN `!k. expi(s * (&k / &M + t)) = expi(s * t) * expi(s * &k / &M)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM EXPI_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  MP_TAC(SPECL [`M:num`; `s:real`] VSUM_EXPI_RESIDUES_INT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      EXPAND_TAC "s" THEN SIMP_TAC[INTEGER_CLOSED];
      EXPAND_TAC "s" THEN
      SUBGOAL_THEN `&1 <= &m1 /\ &m1 <= &N /\ &1 <= &m2 /\ &m2 <= &N /\
                    &2 * &N < &M /\ &n < &M:real`
      MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL; REAL_OF_NUM_LT];
        REAL_ARITH_TAC]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `s = &0 <=> m1 + m2 = n:num` (fun th -> REWRITE_TAC[th])
  THENL
   [EXPAND_TAC "s" THEN
    REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; CX_MUL] THEN
  SUBGOAL_THEN `s = &0` SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN
    ASM_REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ];
    REWRITE_TAC[REAL_MUL_LZERO; EXPI_0] THEN CONV_TAC COMPLEX_RING]);;

let PAIR_INNER_COUNT = prove
 (`!a n N. n <= N + a
           ==> sum(1..N) (\m. if a + m = n then &1 else &0) =
               if a < n then &1 else &0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..N) (\m. if m = n - a then &1 else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC]);;

let PAIR_COUNT = prove
 (`!N n. 1 <= n /\ n <= N + 1
         ==> sum(1..N) (\m1. sum(1..N) (\m2.
               if m1 + m2 = n then &1 else &0)) = &n - &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..N) (\m1. if m1 < n then &1 else &0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m1:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC PAIR_INNER_COUNT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m:num. m < n`; `1..N`; `\m:num. &1`] SUM_RESTRICT_SET) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `{m | m IN 1..N /\ m < n} = 1..n - 1` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> (n - 1 + 1) - 1 = n - 1`] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_SUB]]);;

let NORM_VSUM_POW2_CNJ = prove
 (`!(f:A->complex) s.
        FINITE s
        ==> norm(vsum s f) pow 2 =
            Re(vsum s (\i. vsum s (\j. f i * cnj(f j))))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[RE_CX] `!a b. Cx a = b ==> a = Re b`) THEN
  REWRITE_TAC[CX_POW; COMPLEX_NORM_POW_2] THEN
  ASM_SIMP_TAC[CNJ_VSUM; VSUM_MUL_VSUM]);;

let VSUM_SWAP_LT3 = prove
 (`!(G:num->num->num->complex) M.
     vsum {n | n < M} (\n. vsum {i | i < M} (\i. vsum {j | j < M} (\j.
       G n i j))) =
     vsum {i | i < M} (\i. vsum {j | j < M} (\j. vsum {n | n < M} (\n.
       G n i j)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(GEN `f:num->num->complex`
   (MP (ISPECL [`f:num->num->complex`; `{k:num | k < M}`; `{k:num | k < M}`]
               VSUM_SWAP)
       (CONJ (SPEC `M:num` FINITE_NUMSEG_LT) (SPEC `M:num` FINITE_NUMSEG_LT))))
  THEN
  DISCH_THEN(fun sw ->
    GEN_REWRITE_TAC LAND_CONV [sw] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [sw] THEN REWRITE_TAC[]));;

let DFT_PARSEVAL = prove
 (`!(d:num->complex) M.
     ~(M = 0)
     ==> sum {n | n < M}
           (\n. norm(vsum {k | k < M} (\k. d k * expi(--(&n * &k / &M))))
                pow 2) =
         &M * sum {k | k < M} (\k. norm(d k) pow 2)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[NORM_VSUM_POW2_CNJ; FINITE_NUMSEG_LT] THEN
  SIMP_TAC[GSYM RE_VSUM; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[VSUM_SWAP_LT3] THEN
  SUBGOAL_THEN
   `!i j. i < M /\ j < M
          ==> vsum {n | n < M}
                (\n. (d i * expi(--(&n * &i / &M))) *
                     cnj(d j * expi(--(&n * &j / &M)))) =
              if j = i then Cx(&M) * d i * cnj(d i) else Cx(&0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[CNJ_MUL; CNJ_EXPI; REAL_NEG_NEG] THEN
    SUBGOAL_THEN
     `!n. (d i * expi(--(&n * &i / &M))) * cnj(d j) * expi(&n * &j / &M) =
          (d i * cnj(d j)) * expi((&j - &i) * &n / &M)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `(&j - &i) * &n / &M = --(&n * &i / &M) + &n * &j / &M`
      SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        REWRITE_TAC[EXPI_ADD] THEN CONV_TAC COMPLEX_RING];
      ALL_TAC] THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
    MP_TAC(SPECL [`M:num`; `&j - &i`] VSUM_EXPI_RESIDUES_INT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      UNDISCH_TAC `i < M:num` THEN UNDISCH_TAC `j < M:num` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `Re(vsum {i | i < M} (\i. Cx(&M) * d i * cnj(d i)))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum {j | j < M}
                  (\j. if j = i then Cx(&M) * d i * cnj(d i) else Cx(&0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_DELTA; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC[RE_VSUM; FINITE_NUMSEG_LT] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[RE_MUL_CX; GSYM COMPLEX_NORM_POW_2; GSYM CX_POW; RE_CX]);;

(* ------------------------------------------------------------------------- *)
(* The binary singular series.                                               *)
(* ------------------------------------------------------------------------- *)

let sing2_term = new_definition
 `sing2_term n q = (mobius q / &(phi q)) pow 2 * ramanujan_sum q n`;;

let sing2_series = new_definition
 `sing2_series n Q = sum(1..Q) (sing2_term n)`;;

let SING2_TERM_MULTIPLICATIVE = prove
 (`!n. real_multiplicative (sing2_term n)`,
  GEN_TAC THEN
  SUBGOAL_THEN `sing2_term n =
                (\q. (mobius q pow 2 * inv(&(phi q)) pow 2) *
                     ramanujan_sum q n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sing2_term; real_div; REAL_POW_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_MULTIPLICATIVE_MUL THEN
  REWRITE_TAC[RAMANUJAN_SUM_MULTIPLICATIVE] THEN
  MATCH_MP_TAC REAL_MULTIPLICATIVE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MULTIPLICATIVE_POW THEN
    REWRITE_TAC[REAL_MULTIPLICATIVE_MOBIUS];
    MATCH_MP_TAC REAL_MULTIPLICATIVE_INV_POW THEN
    REWRITE_TAC[REAL_MULTIPLICATIVE_PHI]]);;

let SING2_TERM_PRIME = prove
 (`!n p. prime p
         ==> sing2_term n p =
             if p divides n then inv(&p - &1)
             else --inv((&p - &1) pow 2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[sing2_term; MOBIUS_PRIME; PHI_PRIME; RAMANUJAN_SUM_PRIME] THEN
  SUBGOAL_THEN `1 <= p /\ ~(&p - &1 = &0)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  COND_CASES_TAC THEN UNDISCH_TAC `~(&p - &1 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let SING2_TERM_SQUAREFREE = prove
 (`!n q. ~(sing2_term n q = &0) ==> squarefree q`,
  REWRITE_TAC[sing2_term; mobius] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_POW_ZERO; ARITH_EQ]);;

let PRODUCT_P3_LOWER = prove
 (`!Q. 1 <= Q
       ==> &1 / &2 <= product {p | prime p /\ 3 <= p /\ p <= Q}
                              (\p. &1 - inv((&p - &1) pow 2))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P3 = {p | prime p /\ 3 <= p /\ p <= Q}` THEN
  SUBGOAL_THEN
   `product P3 (\p. &1 - inv((&p - &1) pow 2)) =
    product (IMAGE (\p. p - 1) P3) (\n. &1 - inv(&n pow 2))`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_IMAGE o rand o snd) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "P3" THEN REWRITE_TAC[IN_ELIM_THM] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    EXPAND_TAC "P3" THEN REWRITE_TAC[IN_ELIM_THM; o_DEF] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `3 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product(2..Q) (\n. &1 - inv(&n pow 2))` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `Q - 1` PRODUCT_INV_SQUARE) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= Q ==> SUC(Q - 1) = Q`] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &2 * &n + &2`] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC PRODUCT_SUBSET_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "P3" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
      ARITH_TAC;
      X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&1 <= &n pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= inv(&n pow 2) /\ inv(&n pow 2) <= &1` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_INV_LE_1] THEN MATCH_MP_TAC REAL_LE_INV THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]]]);;

let SING2_PRODUCT_LOWER = prove
 (`!n Q. EVEN n
         ==> &1 <= product {p | prime p /\ p <= Q} (\p. &1 + sing2_term n p)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `Q <= 1` THENL
   [SUBGOAL_THEN `{p | prime p /\ p <= Q} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC;
      REWRITE_TAC[PRODUCT_CLAUSES; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `P3 = {p | prime p /\ 3 <= p /\ p <= Q}` THEN
  SUBGOAL_THEN
   `{p | prime p /\ p <= Q} = 2 INSERT P3 /\ ~(2 IN P3) /\ FINITE P3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P3" THEN REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:num` THEN ASM_CASES_TAC `p = 2` THEN
      ASM_REWRITE_TAC[PRIME_2] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC;
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ p <= Q}` THEN
      REWRITE_TAC[FINITE_ATMOST; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; SING2_TERM_PRIME; PRIME_2] THEN
  SUBGOAL_THEN `2 divides n` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[DIVIDES_2]; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH `&1 / &2 <= x ==> &1 <= &2 * x`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product P3 (\p. &1 - inv((&p - &1) pow 2))` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "P3" THEN MATCH_MP_TAC PRODUCT_P3_LOWER THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "P3" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[SING2_TERM_PRIME] THEN
  SUBGOAL_THEN `&2 <= &p - &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv((&p - &1) pow 2) <= &1 /\ &0 <= inv((&p - &1) pow 2) /\
                &0 <= inv(&p - &1)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

let DIVISORS_PRIME = prove
 (`!p. prime p ==> {d | d divides p} = {1,p}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `d:num` THEN EQ_TAC THENL
   [ASM_MESON_TAC[prime];
    STRIP_TAC THEN ASM_REWRITE_TAC[DIVIDES_1; DIVIDES_REFL]]);;

let TAU_MULTIPLICATIVE = prove
 (`real_multiplicative (\q. sum {d | d divides q} (\d. &1))`,
  MATCH_MP_TAC REAL_MULTIPLICATIVE_DIVISORSUM THEN
  REWRITE_TAC[real_multiplicative; REAL_MUL_LID]);;

let TAU_PRIME = prove
 (`!p. prime p ==> sum {d | d divides p} (\d. &1) = &2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DIVISORS_PRIME] THEN
  SUBGOAL_THEN `~(p = 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
               NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let RAMANUJAN_SUM_ABS_BOUND = prove
 (`!q n. 1 <= q
         ==> abs(ramanujan_sum q n) <=
             sum {d | d divides q} (\d. if d divides n then &d else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ramanujan_sum] THEN
  SUBGOAL_THEN `FINITE {d | d divides q}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `{d | d divides q /\ d divides n} = {d | d IN {d | d divides q} /\
                                            d divides n}`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_ABS_MOBIUS]);;

let RAMANUJAN_SUM_ABS_SUM = prove
 (`!q N. 1 <= q
         ==> sum(1..N) (\n. abs(ramanujan_sum q n)) <=
             &N * sum {d | d divides q} (\d. &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {d | d divides q}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\n. sum {d | d divides q}
                                 (\d. if d divides n then &d else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[RAMANUJAN_SUM_ABS_BOUND];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n d. if d divides n then &d else &0`; `1..N`;
                 `{d | d divides q}`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `0 divides q` THEN REWRITE_TAC[DIVIDES_ZERO] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i:num. d divides i`; `1..N`; `\i:num. &d`]
         SUM_RESTRICT_SET) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  MP_TAC(SPECL [`d:num`; `N:num`] CARD_MULTIPLES_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &d` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_RID]);;

let SING2_TERM_ABS_SUM = prove
 (`!q N. 1 <= q
         ==> sum(1..N) (\n. abs(sing2_term n q)) <=
             &N * sum {d | d divides q} (\d. &1) * inv(&(phi q)) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `sum(1..N) (\n. inv(&(phi q)) pow 2 * abs(ramanujan_sum q n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[sing2_term; REAL_ABS_MUL; REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM; real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_MOBIUS; REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `n * t * i = i * n * t:real`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[RAMANUJAN_SUM_ABS_SUM] THEN
  MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]);;

let SING2_RANKIN = prove
 (`!Q. product {p | prime p /\ p <= Q}
                 (\p. &1 + &2 * sqrt(&p) * inv((&p - &1) pow 2)) <= exp(&16)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product {p | prime p /\ p <= Q}
                      (\p. exp(&8 * inv(&p * sqrt(&p))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN
    REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt(&p)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv((&p - &1) pow 2) /\
                  inv((&p - &1) pow 2) <= &4 / &p pow 2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((&p / &2) pow 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_POW_DIV; REAL_INV_DIV] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 + &8 * inv(&p * sqrt(&p))` THEN
    REWRITE_TAC[REAL_EXP_LE_X; REAL_LE_LADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * sqrt(&p) * &4 / &p pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ABBREV_TAC `s = sqrt(&p)` THEN
    SUBGOAL_THEN `&p = s pow 2` SUBST1_TAC THENL
     [EXPAND_TAC "s" THEN SIMP_TAC[SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `~(s = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p. &8 * inv(&p * sqrt(&p))`; `{p | prime p /\ p <= Q}`]
         REAL_EXP_SUM) THEN
  REWRITE_TAC[FINITE_ATMOST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; SUM_LMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> &8 * x <= &16`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2..Q) (\n. inv(&n * sqrt(&n)))` THEN
  REWRITE_TAC[SUM_INV_THREE_HALVES] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[PRIME_GE_2];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS]]);;

let SING2_TAIL_POINT = prove
 (`!n Q. abs(sing2_series n Q -
             product {p | prime p /\ p <= Q} (\p. &1 + sing2_term n p)) <=
         sum {t | t SUBSET {p | prime p /\ p <= Q} /\
                  ~(nproduct t (\p. p) <= Q)}
             (\t. abs(sing2_term n (nproduct t (\p. p))))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `P = {p | prime p /\ p <= Q}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN SIMP_TAC[IN_ELIM_THM; FINITE_ATMOST];
    ALL_TAC] THEN
  REWRITE_TAC[sing2_series] THEN
  MP_TAC(ISPECL [`sing2_term n`; `Q:num`] SUM_SQUAREFREE_SUBSETS) THEN
  REWRITE_TAC[SING2_TERM_SQUAREFREE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`sing2_term n`; `P:num->bool`]
         SUM_SUBSETS_MULTIPLICATIVE) THEN
  ASM_REWRITE_TAC[SING2_TERM_MULTIPLICATIVE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`{t | t SUBSET (P:num->bool)}`;
                 `\t. nproduct t (\p:num. p) <= Q`;
                 `\t. sing2_term n (nproduct t (\p:num. p))`;
                 `\t. sing2_term n (nproduct t (\p:num. p))`] SUM_CASES) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; COND_ID; IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs b <= e ==> abs(a - (a + b)) <= e`) THEN
  MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t | t SUBSET (P:num->bool)}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

let SING2_TAIL_L1 = prove
 (`!N Q. 1 <= Q
         ==> sum(1..N) (\n. abs(sing2_series n Q -
                                product {p | prime p /\ p <= Q}
                                        (\p. &1 + sing2_term n p)))
             <= exp(&16) * &N / sqrt(&Q)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = {p | prime p /\ p <= Q}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN SIMP_TAC[IN_ELIM_THM; FINITE_ATMOST];
    ALL_TAC] THEN
  ABBREV_TAC `Tt = {t | t SUBSET P /\ ~(nproduct t (\p:num. p) <= Q)}` THEN
  SUBGOAL_THEN `FINITE(Tt:(num->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t | t SUBSET (P:num->bool)}` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FINITE_POWERSET]; ALL_TAC] THEN
    EXPAND_TAC "Tt" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN Tt ==> 1 <= nproduct t (\p:num. p) /\ Q < nproduct t (\p. p)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Tt" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t:num->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN ASM_MESON_TAC[SUBSET; PRIME_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\n. sum Tt (\t. abs(sing2_term n
                                              (nproduct t (\p. p)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MP_TAC(SPECL [`n:num`; `Q:num`] SING2_TAIL_POINT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n t. abs(sing2_term n (nproduct t (\p:num. p)))`; `1..N`;
                 `Tt:(num->bool)->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h = \q. sum {d | d divides q} (\d. &1) * sqrt(&q) *
                      inv(&(phi q)) pow 2` THEN
  SUBGOAL_THEN `!q. 1 <= q ==> &0 <= h q` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t SUBSET P ==> 1 <= nproduct t (\p:num. p)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN ASM_MESON_TAC[SUBSET; PRIME_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Tt (\t. &N / sqrt(&Q) * h(nproduct t (\p:num. p)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `1 <= nproduct t (\p:num. p) /\ Q < nproduct t (\p. p)`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `q = nproduct t (\p:num. p)` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&N * sum {d | d divides q} (\d. &1) *
                inv(&(phi q)) pow 2` THEN
    ASM_SIMP_TAC[SING2_TERM_ABS_SUM] THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&N / sqrt(&Q) * sum {d | d divides q} (\d. &1) * sqrt(&q) *
      inv(&(phi q)) pow 2 =
      (&N * sum {d | d divides q} (\d. &1) * inv(&(phi q)) pow 2) *
      (sqrt(&q) / sqrt(&Q))`
    SUBST1_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]];
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&N / sqrt(&Q) * exp(&16)` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[real_div; REAL_MUL_AC; REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET P} (\t. h(nproduct t (\p:num. p)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    CONJ_TAC THENL [EXPAND_TAC "Tt" THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->real`; `P:num->bool`] SUM_SUBSETS_MULTIPLICATIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "h" THEN
    MATCH_MP_TAC REAL_MULTIPLICATIVE_MUL THEN
    REWRITE_TAC[TAU_MULTIPLICATIVE] THEN
    MATCH_MP_TAC REAL_MULTIPLICATIVE_MUL THEN
    REWRITE_TAC[REAL_MULTIPLICATIVE_SQRT] THEN
    MATCH_MP_TAC REAL_MULTIPLICATIVE_INV_POW THEN
    REWRITE_TAC[REAL_MULTIPLICATIVE_PHI];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product P (\p. &1 + &2 * sqrt(&p) * inv((&p - &1) pow 2))` THEN
  CONJ_TAC THENL
   [ALL_TAC; EXPAND_TAC "P" THEN REWRITE_TAC[SING2_RANKIN]] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `prime p` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[TAU_PRIME; PHI_PRIME] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `2 <= p ==> 1 <= p`] THEN
  REWRITE_TAC[REAL_POW_INV]);;

(* ------------------------------------------------------------------------- *)
(* The variance identity.                                                    *)
(* ------------------------------------------------------------------------- *)

let goldbach_rep2 = new_definition
 `goldbach_rep2 N n =
  sum(1..N) (\m1. sum(1..N) (\m2.
    if m1 + m2 = n
    then (if prime m1 then log(&m1) else &0) *
         (if prime m2 then log(&m2) else &0)
    else &0))`;;

let goldbach_pair2 = new_definition
 `goldbach_pair2 N n =
  sum(1..N) (\m1. sum(1..N) (\m2. if m1 + m2 = n then &1 else &0))`;;

let goldbach_major2 = new_definition
 `goldbach_major2 N M Q k =
  vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)} (\a.
    Cx((mobius q / &(phi q)) pow 2) * unitexp N (&k / &M - &a / &q) pow 2))`;;

let GOLDBACH_REP2_ZERO = prove
 (`!N n. ~(?p q. prime p /\ prime q /\ p + q = n) ==> goldbach_rep2 N n = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[goldbach_rep2] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `m1:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `m2:num` THEN STRIP_TAC THEN
  BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m1:num`; `m2:num`]) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]);;

let GOLDBACH_PAIR2_EQ = prove
 (`!N n. 1 <= n /\ n <= N + 1 ==> goldbach_pair2 N n = &n - &1`,
  REWRITE_TAC[goldbach_pair2; PAIR_COUNT]);;

let CIRCLE_GOLDBACH_REP2 = prove
 (`!N M n. 2 * N < M /\ n < M
           ==> vsum {k | k < M}
                 (\k. primexp N (&k / &M) pow 2 *
                      expi(--(&n * &k / &M))) =
               Cx(&M * goldbach_rep2 N n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. if prime m then log(&m) else &0`; `N:num`; `M:num`;
                 `n:num`; `&0`] BINARY_CIRCLE) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; GSYM primexp; GSYM goldbach_rep2]);;

let CIRCLE_GOLDBACH_PAIR2 = prove
 (`!N M n t. 2 * N < M /\ n < M
             ==> vsum {k | k < M}
                   (\k. unitexp N (&k / &M - t) pow 2 *
                        expi(--(&n * (&k / &M - t)))) =
                 Cx(&M * goldbach_pair2 N n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m:num. &1`; `N:num`; `M:num`; `n:num`; `--t:real`]
         BINARY_CIRCLE) THEN
  ASM_REWRITE_TAC[GSYM real_sub; UNITEXP_ALT; REAL_MUL_LID;
                  GSYM goldbach_pair2]);;

let VSUM_SWAP_MAJOR = prove
 (`!(f:num->num->num->complex) M Q.
     vsum {k | k < M} (\k. vsum(1..Q) (\q.
       vsum {a | a < q /\ coprime(a,q)} (\a. f q a k))) =
     vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)} (\a.
       vsum {k | k < M} (\k. f q a k)))`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN BETA_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_COPRIME_RESIDUES]);;

let CIRCLE_GOLDBACH_MAJOR2 = prove
 (`!N M Q n. 2 * N < M /\ n < M
             ==> vsum {k | k < M}
                   (\k. goldbach_major2 N M Q k * expi(--(&n * &k / &M))) =
                 Cx(&M * goldbach_pair2 N n * sing2_series n Q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[goldbach_major2] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG; FINITE_COPRIME_RESIDUES] THEN
  REWRITE_TAC[VSUM_SWAP_MAJOR] THEN
  REWRITE_TAC[sing2_series; sing2_term; GSYM SUM_LMUL; GSYM VSUM_CX] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `!a k. (Cx((mobius q / &(phi q)) pow 2) *
           unitexp N (&k / &M - &a / &q) pow 2) * expi(--(&n * &k / &M)) =
          (Cx((mobius q / &(phi q)) pow 2) * expi(--(&n * &a / &q))) *
          (unitexp N (&k / &M - &a / &q) pow 2 *
           expi(--(&n * (&k / &M - &a / &q))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `--(&n * &k / &M) =
                  --(&n * &a / &q) + --(&n * (&k / &M - &a / &q))`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[EXPI_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[CIRCLE_GOLDBACH_PAIR2] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; VSUM_COMPLEX_LMUL; FINITE_COPRIME_RESIDUES] THEN
  ASM_SIMP_TAC[RAMANUJAN_SUM_NEG_VSUM] THEN
  REWRITE_TAC[GSYM CX_MUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let VARIANCE_IDENTITY = prove
 (`!N M Q. 2 * N < M
           ==> sum {n | n < M}
                 (\n. (goldbach_rep2 N n - goldbach_pair2 N n *
                       sing2_series n Q) pow 2) =
               sum {k | k < M}
                 (\k. norm(primexp N (&k / &M) pow 2 -
                           goldbach_major2 N M Q k) pow 2)
               / &M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(M = 0) /\ &0 < &M` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN
  MATCH_MP_TAC(REAL_RING
   `!m x y:real. ~(m = &0) /\ m * x * m = m * y ==> x * m = y`) THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
           [`\k. primexp N (&k / &M) pow 2 - goldbach_major2 N M Q k`; `M:num`]
         DFT_PARSEVAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  BETA_TAC THEN REWRITE_TAC[COMPLEX_SUB_RDISTRIB] THEN
  SIMP_TAC[VSUM_SUB; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[CIRCLE_GOLDBACH_REP2; CIRCLE_GOLDBACH_MAJOR2] THEN
  REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Major and minor arcs: the variance bound.                                 *)
(* ------------------------------------------------------------------------- *)

let goldbach_inarc2 = new_definition
 `goldbach_inarc2 N M Kw Q k =
  vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)} (\a.
    if k IN circ_arc M Kw q a
    then Cx((mobius q / &(phi q)) pow 2) * unitexp N (&k / &M - &a / &q) pow 2
    else Cx(&0)))`;;

let goldbach_outarc2 = new_definition
 `goldbach_outarc2 N M Kw Q k =
  vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)} (\a.
    if k IN circ_arc M Kw q a then Cx(&0)
    else Cx((mobius q / &(phi q)) pow 2) *
         unitexp N (&k / &M - &a / &q) pow 2))`;;

let GOLDBACH_MAJOR2_SPLIT = prove
 (`!N M Kw Q k. goldbach_major2 N M Q k = goldbach_inarc2 N M Kw Q k +
                goldbach_outarc2 N M Kw Q k`,
  REWRITE_TAC[goldbach_major2; goldbach_inarc2; goldbach_outarc2] THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_NUMSEG; FINITE_COPRIME_RESIDUES] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `q:num` THEN
  DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_ADD_RID]);;

let GOLDBACH_INARC2_DELTA = prove
 (`!N M Kw Q q0 a0 k.
     2 * Q EXP 2 < Kw /\ 1 <= q0 /\ q0 <= Q /\ a0 < q0 /\ coprime(a0,q0) /\
     k IN circ_arc M Kw q0 a0
     ==> goldbach_inarc2 N M Kw Q k =
         Cx((mobius q0 / &(phi q0)) pow 2) *
         unitexp N (&k / &M - &a0 / &q0) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[goldbach_inarc2] THEN
  SUBGOAL_THEN
   `!q a. q IN 1..Q /\ a IN {a | a < q /\ coprime(a,q)}
          ==> (k IN circ_arc M Kw q a <=> q = q0 /\ a = a0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`; `q:num`; `a:num`; `q0:num`;
                    `a0:num`; `k:num`] CIRC_ARC_DISJOINT) THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(1..Q) (\q. if q = q0
                               then Cx((mobius q0 / &(phi q0)) pow 2) *
                                    unitexp N (&k / &M - &a0 / &q0) pow 2
                               else vec 0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[VSUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {a | a < q /\ coprime(a,q)}
                (\a. if a = a0 then
                       (if q = q0
                        then Cx((mobius q0 / &(phi q0)) pow 2) *
                             unitexp N (&k / &M - &a0 / &q0) pow 2
                        else vec 0)
                     else vec 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `q:num = q0` THEN ASM_CASES_TAC `a:num = a0` THEN
    ASM_REWRITE_TAC[COMPLEX_VEC_0];
    REWRITE_TAC[VSUM_DELTA; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(a0 < q /\ coprime(a0,q:num))` THEN ASM_REWRITE_TAC[]]);;

let GOLDBACH_INARC2_MINOR = prove
 (`!N M Kw Q k. ~(k IN circ_major M Kw Q)
                ==> goldbach_inarc2 N M Kw Q k = Cx(&0)`,
  REWRITE_TAC[circ_major; UNIONS_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[goldbach_inarc2; GSYM COMPLEX_VEC_0] THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN X_GEN_TAC `q:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN X_GEN_TAC `a:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SUM_SWAP_MAJOR = prove
 (`!(f:num->num->num->real) M Q.
     sum {k | k < M} (\k. sum(1..Q) (\q.
       sum {a | a < q /\ coprime(a,q)} (\a. f q a k))) =
     sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)} (\a.
       sum {k | k < M} (\k. f q a k)))`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN BETA_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_COPRIME_RESIDUES]);;

let MOBIUS_PHI_SQUARE_SUM = prove
 (`!Q c. &0 <= c
         ==> sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                               (\a. (mobius q / &(phi q)) pow 2 * c)) <=
             c * sum(1..Q) (\q. inv(&(phi q)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES] THEN
  SUBGOAL_THEN `CARD {a | a < q /\ coprime(a,q)} = phi q` SUBST1_TAC THENL
   [REWRITE_TAC[PHI_ALT] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `2`] MOBIUS_PHI_POW_BOUND) THEN
  ASM_REWRITE_TAC[ARITH; REAL_POW2_ABS] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * ((mobius q / &(phi q)) pow 2 * &(phi q))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let GOLDBACH_OUTARC2_POINT = prove
 (`!N M Kw Q k. 1 <= Kw /\ k < M
               ==> norm(goldbach_outarc2 N M Kw Q k) <=
                   &4 * &Kw pow 2 * sum(1..Q) (\q. inv(&(phi q)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                               (\a. (mobius q / &(phi q)) pow 2 *
                                    (&4 * &Kw pow 2)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(SPECL [`Q:num`; `&4 * &Kw pow 2`] MOBIUS_PHI_SQUARE_SUM) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      REWRITE_TAC[REAL_MUL_ASSOC]]] THEN
  REWRITE_TAC[goldbach_outarc2] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN X_GEN_TAC `a:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_POW] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  SUBGOAL_THEN `&4 * &Kw pow 2 = (&2 * &Kw) pow 2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC ARC_UNITEXP_BOUND THEN ASM_REWRITE_TAC[]);;

let GOLDBACH_OUTARC2_SUM = prove
 (`!N M Kw Q. N < M
             ==> sum {k | k < M} (\k. norm(goldbach_outarc2 N M Kw Q k)) <=
                 &M * &N * sum(1..Q) (\q. inv(&(phi q)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {k | k < M} (\k. sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
      (\a. (mobius q / &(phi q)) pow 2 *
           norm(unitexp N (&k / &M - &a / &q)) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[goldbach_outarc2] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN X_GEN_TAC `a:num` THEN
    DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_POW] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS; REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SWAP_MAJOR; SUM_LMUL] THEN
  ASM_SIMP_TAC[PARSEVAL_UNITEXP] THEN
  SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `CARD {a | a < q /\ coprime(a,q)} = phi q` SUBST1_TAC THENL
   [REWRITE_TAC[PHI_ALT] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `2`] MOBIUS_PHI_POW_BOUND) THEN
  ASM_REWRITE_TAC[ARITH; REAL_POW2_ABS] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&M * &N) * ((mobius q / &(phi q)) pow 2 * &(phi q))` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&M * &N * inv(&(phi q)) = (&M * &N) * inv(&(phi q))`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]);;

let GOLDBACH_OUTARC2_SQUARE = prove
 (`!N M Kw Q. 1 <= Kw /\ N < M
             ==> sum {k | k < M}
                   (\k. norm(goldbach_outarc2 N M Kw Q k) pow 2) <=
                 (&4 * &Kw pow 2 * sum(1..Q) (\q. inv(&(phi q)))) *
                 (&M * &N * sum(1..Q) (\q. inv(&(phi q))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {k | k < M}
                (\k. (&4 * &Kw pow 2 * sum(1..Q) (\q. inv(&(phi q)))) *
                     norm(goldbach_outarc2 N M Kw Q k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC GOLDBACH_OUTARC2_POINT THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[GOLDBACH_OUTARC2_SUM] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]]);;

let SQUARE_DIFF_BOUND = prove
 (`!x y:complex e.
     norm(x - y) <= e
     ==> norm(x pow 2 - y pow 2) pow 2 <=
         &2 * e pow 2 * (norm x pow 2 + norm y pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:complex) pow 2 - y pow 2 = (x - y) * (x + y)` SUBST1_TAC
  THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `e pow 2 * (norm(x:complex) + norm(y:complex)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REWRITE_TAC[NORM_TRIANGLE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&2 * e = e * &2`] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  MP_TAC(SPEC `norm(x:complex) - norm(y:complex)` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_RING `(a - b:real) pow 2 = a pow 2 + b pow 2 - &2 * a * b`;
              REAL_RING `(a + b:real) pow 2 = a pow 2 + b pow 2 + &2 * a * b`]
  THEN REAL_ARITH_TAC);;

let GOLDBACH_INARC2_MINOR_SUM = prove
 (`!N M Kw Q B.
     N < M /\ &0 <= B /\
     (!k. k < M /\ ~(k IN circ_major M Kw Q)
          ==> norm(primexp N (&k / &M)) <= B)
     ==> sum ({k | k < M} DIFF circ_major M Kw Q)
           (\k. norm(primexp N (&k / &M) pow 2 -
                     goldbach_inarc2 N M Kw Q k) pow 2)
         <= B pow 2 * &M *
            sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum ({k | k < M} DIFF circ_major M Kw Q)
                  (\k. B pow 2 * norm(primexp N (&k / &M)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG_LT; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[GOLDBACH_INARC2_MINOR; COMPLEX_SUB_RZERO;
                 COMPLEX_NORM_POW] THEN
    REWRITE_TAC[REAL_RING `((x:real) pow 2) pow 2 = x pow 2 * x pow 2`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_SIMP_TAC[GSYM PARSEVAL_PRIMEXP] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_POW_2] THEN SET_TAC[]);;

let GOLDBACH_INARC2_MAJOR_SUM = prove
 (`!N M Kw Q E.
     2 * Q EXP 2 < Kw /\ N < M /\ &0 <= E /\
     (!q a k. 1 <= q /\ q <= Q /\ a < q /\ coprime(a,q) /\
              k IN circ_arc M Kw q a
              ==> norm(primexp N (&k / &M) -
                       Cx(mobius q / &(phi q)) *
                       unitexp N (&k / &M - &a / &q)) <= E)
     ==> sum (circ_major M Kw Q)
           (\k. norm(primexp N (&k / &M) pow 2 -
                     goldbach_inarc2 N M Kw Q k) pow 2)
         <= &2 * E pow 2 *
            (&M * sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2) +
             &M * &N * sum(1..Q) (\q. inv(&(phi q))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CIRC_MAJOR_SUM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)} (\a.
      sum (circ_arc M Kw q a) (\k.
        &2 * E pow 2 * (norm(primexp N (&k / &M)) pow 2 +
                        norm(Cx(mobius q / &(phi q)) *
                             unitexp N (&k / &M - &a / &q)) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_COPRIME_RESIDUES; IN_ELIM_THM] THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[CIRC_ARC_FINITE] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`; `q:num`; `a:num`;
                  `k:num`] GOLDBACH_INARC2_DELTA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `Cx((mobius q / &(phi q)) pow 2) * unitexp N (&k / &M - &a / &q) pow 2 =
      (Cx(mobius q / &(phi q)) * unitexp N (&k / &M - &a / &q)) pow 2`
    SUBST1_TAC THENL [REWRITE_TAC[CX_POW; COMPLEX_POW_MUL]; ALL_TAC] THEN
    MATCH_MP_TAC SQUARE_DIFF_BOUND THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG; FINITE_COPRIME_RESIDUES;
           CIRC_ARC_FINITE] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM CIRC_MAJOR_SUM] THEN
    MP_TAC(SPECL [`N:num`; `M:num`] PARSEVAL_PRIMEXP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; CIRC_MAJOR_SUBSET; REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                               (\a. (mobius q / &(phi q)) pow 2 *
                                    (&M * &N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_POW_MUL; SUM_LMUL;
                REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC(SPECL [`N:num`; `M:num`; `&a / &q`] PARSEVAL_UNITEXP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_POW_2] THEN
    REWRITE_TAC[circ_arc; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    MP_TAC(SPECL [`Q:num`; `&M * &N`] MOBIUS_PHI_SQUARE_SUM) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_MUL_ASSOC]]]);;

let NORM_SUB_SQUARE_LE = prove
 (`!a b c:complex.
     norm(a - (b + c)) pow 2 <= &2 * norm(a - b) pow 2 + &2 * norm(c) pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(norm(a - b:complex) + norm(c:complex)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    CONV_TAC NORM_ARITH;
    MP_TAC(SPEC `norm(a - b:complex) - norm(c:complex)` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_RING
                 `(x - y:real) pow 2 = x pow 2 + y pow 2 - &2 * x * y`;
                REAL_RING
                 `(x + y:real) pow 2 = x pow 2 + y pow 2 + &2 * x * y`]
    THEN REAL_ARITH_TAC]);;

let VARIANCE_BOUND = prove
 (`!N M Kw Q D B.
     1 <= N /\ 2 * N < M /\ 1 <= Kw /\ 1 <= Q /\ 2 * Q EXP 2 < Kw /\
     &0 <= D /\ &0 <= B /\
     (!q h b. 1 <= q /\ q <= Q /\ h <= N /\ b < q /\ coprime(b,q)
              ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                          (\p. log(&p)) - &h / &(phi q)) <= D) /\
     (!k. k < M /\ ~(k IN circ_major M Kw Q)
          ==> norm(primexp N (&k / &M)) <= B)
     ==> sum {n | n < M}
           (\n. (goldbach_rep2 N n - goldbach_pair2 N n *
                 sing2_series n Q) pow 2)
         <= &2 * (B pow 2 *
                  sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2) +
                  &2 * ((&Q * D + log(&Q)) * (&1 + &2 * pi * &N / &Kw)) pow 2 *
                  (sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2) +
                   &N * sum(1..Q) (\q. inv(&(phi q))))) +
            &8 * &Kw pow 2 * &N * sum(1..Q) (\q. inv(&(phi q))) pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VARIANCE_IDENTITY] THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ABBREV_TAC `W = sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)` THEN
  ABBREV_TAC `P = sum(1..Q) (\q. inv(&(phi q)))` THEN
  ABBREV_TAC `E = (&Q * D + log(&Q)) * (&1 + &2 * pi * &N / &Kw)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[PI_POS_LE; REAL_LE_DIV; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q a k. 1 <= q /\ q <= Q /\ a < q /\ coprime(a,q) /\
            k IN circ_arc M Kw q a
            ==> norm(primexp N (&k / &M) -
                     Cx(mobius q / &(phi q)) *
                     unitexp N (&k / &M - &a / &q)) <= E`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`q:num`; `a:num`; `k:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(phi q) * D + log(&q)) * (&1 + &2 * pi * &N / &Kw)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ARC_APPROX THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q:num` THEN
        ASM_REWRITE_TAC[PHI_LIMIT];
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[PI_POS_LE; REAL_LE_DIV; REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {k:num | k < M}
      (\k. &2 *
           norm(primexp N (&k / &M) pow 2 - goldbach_inarc2 N M Kw Q k) pow 2 +
           &2 * norm(goldbach_outarc2 N M Kw Q k) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`]
                  GOLDBACH_MAJOR2_SPLIT] THEN
    REWRITE_TAC[NORM_SUB_SQUARE_LE];
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT; SUM_LMUL] THEN
  SUBGOAL_THEN
   `sum {k:num | k < M}
      (\k. norm(primexp N (&k / &M) pow 2 -
                goldbach_inarc2 N M Kw Q k) pow 2) =
    sum (circ_major M Kw Q)
      (\k. norm(primexp N (&k / &M) pow 2 -
                goldbach_inarc2 N M Kw Q k) pow 2) +
    sum ({k | k < M} DIFF circ_major M Kw Q)
      (\k. norm(primexp N (&k / &M) pow 2 - goldbach_inarc2 N M Kw Q k) pow 2)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `{k:num | k < M} = circ_major M Kw Q UNION
                                    ({k | k < M} DIFF circ_major M Kw Q)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th])
    THENL
     [MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`] CIRC_MAJOR_SUBSET) THEN
      SET_TAC[];
      MATCH_MP_TAC SUM_UNION THEN
      REWRITE_TAC[CIRC_MAJOR_FINITE;
                  SET_RULE `DISJOINT (s:num->bool) (t DIFF s)`]
      THEN SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG_LT]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`; `E:real`]
         GOLDBACH_INARC2_MAJOR_SUM) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 * N < M ==> N < M`] THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`; `B:real`]
         GOLDBACH_INARC2_MINOR_SUM) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 * N < M ==> N < M`] THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`]
           GOLDBACH_OUTARC2_SQUARE) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 * N < M ==> N < M`] THEN
  SPEC_TAC(`sum (circ_major M Kw Q)
              (\k. norm(primexp N (&k / &M) pow 2 -
                        goldbach_inarc2 N M Kw Q k) pow 2)`,
           `s1:real`) THEN
  SPEC_TAC(`sum ({k | k < M} DIFF circ_major M Kw Q)
              (\k. norm(primexp N (&k / &M) pow 2 -
                        goldbach_inarc2 N M Kw Q k) pow 2)`,
           `s2:real`) THEN
  SPEC_TAC(`sum {k:num | k < M} (\k. norm(goldbach_outarc2 N M Kw Q k) pow 2)`,
           `s3:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (&2 * E pow 2 * (&M * W + &M * &N * P) + B pow 2 * &M * W) +
              &2 * ((&4 * &Kw pow 2 * P) * (&M * &N * P))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Counting the exceptions for one N.                                        *)
(* ------------------------------------------------------------------------- *)

let MARKOV_CARD = prove
 (`!(f:A->real) s t.
        FINITE s /\ (!x. x IN s ==> &0 <= f x) /\ &0 < t
        ==> &(CARD {x | x IN s /\ t <= f x}) <= sum s f / t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `FINITE {x:A | x IN s /\ t <= f x}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {x:A | x IN s /\ t <= f x} f` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {x:A | x IN s /\ t <= f x} (\x. t)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_CONST; REAL_LE_REFL];
      MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[IN_ELIM_THM]];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[]]);;

let CARD_SMALL_NUMS = prove
 (`!N h. &0 <= h ==> &(CARD {n | n <= N /\ &n < h}) <= h + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `h:real` FLOOR_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
  MP_TAC(SPEC `h:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(CARD(0..c))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[LE_0] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&n < &c + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG; ARITH_RULE `(c + 1) - 0 = c + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC]);;

let GOLDBACH_FIXED = prove
 (`!N M Q h V.
     1 <= N /\ N < M /\ 1 <= Q /\ &2 <= h /\
     sum {n | n < M}
       (\n. (goldbach_rep2 N n - goldbach_pair2 N n * sing2_series n Q) pow 2)
     <= V
     ==> &(CARD {n | n <= N /\ EVEN n /\
                     ~(?p q. prime p /\ prime q /\ p + q = n)})
         <= (h + &1) + &2 * exp(&16) * &N / sqrt(&Q) + (&4 / h) pow 2 * V`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Pr = \n. product {p | prime p /\ p <= Q}
                               (\p. &1 + sing2_term n p)` THEN
  ABBREV_TAC `S1 = {n | n <= N /\ &n < h}` THEN
  ABBREV_TAC `S2 = {n | n IN 1..N /\
                        &1 / &2 <= abs(sing2_series n Q - Pr n)}` THEN
  ABBREV_TAC `S3 = {n | n IN {n | n < M} /\
                        (h / &4) pow 2 <=
                        (goldbach_rep2 N n - goldbach_pair2 N n *
                         sing2_series n Q) pow 2}` THEN
  SUBGOAL_THEN `FINITE(S1:num->bool) /\ FINITE(S2:num->bool) /\
                FINITE(S3:num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S2"; "S3"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      ARITH_TAC;
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG];
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(S1:num->bool)) + &(CARD(S2:num->bool)) +
              &(CARD(S3:num->bool))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD((S1:num->bool) UNION S2 UNION S3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_UNION] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      MAP_EVERY EXPAND_TAC ["S1"; "S2"; "S3"] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
      ASM_CASES_TAC `&n < h` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `2 <= n /\ 1 <= n` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `2 <= n ==> 2 <= n /\ 1 <= n`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `&1 / &2 <= abs(sing2_series n Q - Pr n)` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&1 <= (Pr:num->real) n` ASSUME_TAC THENL
       [EXPAND_TAC "Pr" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC SING2_PRODUCT_LOWER THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GOLDBACH_REP2_ZERO; GOLDBACH_PAIR2_EQ;
                   ARITH_RULE `2 <= n ==> 1 <= n`;
                   ARITH_RULE `n <= N ==> n <= N + 1`] THEN
      SUBGOAL_THEN `&1 / &2 <= sing2_series n Q` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_LZERO; REAL_POW_NEG; ARITH] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&n - &1) * &1 / &2` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD(S1:num->bool) + CARD((S2:num->bool) UNION S3)` THEN
      ASM_SIMP_TAC[CARD_UNION_LE; FINITE_UNION; LE_ADD_LCANCEL]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= a' /\ b <= b' /\ c <= c' ==> a + b + c <= a' + b' + c'`) THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "S1" THEN MATCH_MP_TAC CARD_SMALL_NUMS THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\n. abs(sing2_series n Q - Pr n)`; `1..N`; `&1 / &2`]
           MARKOV_CARD) THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_ABS_POS] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 / &2`] THEN
    EXPAND_TAC "Pr" THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`N:num`; `Q:num`] SING2_TAIL_L1) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL
             [`\n:num. (goldbach_rep2 N n - goldbach_pair2 N n *
                        sing2_series n Q) pow 2`;
                   `{n:num | n < M}`; `(h / &4) pow 2`] MARKOV_CARD) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_POW_2] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    SUBGOAL_THEN `(&4 / h) pow 2 * V = V / (h / &4) pow 2` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(h = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (h / &4) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ]]]);;

(* ------------------------------------------------------------------------- *)
(* Inequalities for the parameters.                                          *)
(* ------------------------------------------------------------------------- *)

let GV_R_FACTS = prove
 (`!L Y r. &10 pow 6 <= L /\ &1 <= Y /\ &1 <= r /\
           Y pow 2 * L pow 7 <= &2 * r
           ==> &1 <= L /\ &0 < r /\ Y pow 4 * L pow 14 <= &4 * r pow 2 /\
               &1000000000000 * Y pow 3 * L pow 12 <= Y pow 4 * L pow 14`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(Y:real) pow 4 * L pow 14 = (Y pow 2 * L pow 7) pow 2 /\
                  &4 * (r:real) pow 2 = (&2 * r) pow 2`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Y:real) pow 4 * L pow 14 = (Y * L pow 2) * (Y pow 3 * L pow 12)`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&10 pow 6) pow 2` THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

let GV1_BOUND = prove
 (`!n L Y r W.
     &10 pow 6 <= L /\ &1 <= Y /\ &1 <= r /\ Y pow 2 * L pow 7 <= &2 * r /\
     &0 <= W /\ W <= n * L pow 2 /\ &0 <= n
     ==> &2 * ((&16000 * L pow 4 * (n / r)) pow 2 * W) *
         (&256 * Y pow 3 * L pow 2) <= n pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:real`; `Y:real`; `r:real`] GV_R_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = (n:real) / r` THEN
  SUBGOAL_THEN `n = (x:real) * r /\ &0 <= x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `(n:real) = x * r`))
  THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * ((&16000 * L pow 4 * x) pow 2 * (x * r) * L pow 2) *
              (&256 * Y pow 3 * L pow 2)` THEN
  CONJ_TAC THENL
   [REPEAT(FIRST [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC;
                  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC;
                  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC]) THEN
    REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC;
                  MATCH_MP_TAC REAL_POW_LE]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * ((&16000 * L pow 4 * x) pow 2 * (x * r) * L pow 2) *
    (&256 * Y pow 3 * L pow 2) =
    (x pow 3 * r) * (&131072000000 * Y pow 3 * L pow 12) /\
    (x * r) pow 3 = (x pow 3 * r) * r pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Y pow 3 * L pow 12` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let GV3_BOUND = prove
 (`!n L Y r k P.
     &10 pow 6 <= L /\ &1 <= Y /\ &1 <= r /\ Y pow 2 * L pow 7 <= &2 * r /\
     &0 < k /\ k * r pow 2 <= n /\ &0 <= P /\ P <= &8 * L
     ==> &8 * k pow 2 * n * P pow 2 * (&256 * Y pow 3 * L pow 2) <= n pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:real`; `Y:real`; `r:real`] GV_R_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= n /\ &0 < r pow 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(k:real) * r pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&131072 * Y pow 3 * L pow 4 <= r pow 4` ASSUME_TAC THENL
   [SUBGOAL_THEN `(r:real) pow 2 <= r pow 4 /\ (L:real) pow 4 <= L pow 12 /\
                  &0 <= (Y:real) pow 3`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_MONO) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
      TRY ARITH_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Y:real) pow 3 * L pow 4 <= Y pow 3 * L pow 12` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Y pow 3 * L pow 4` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&8 * k pow 2 * n * (&8 * L) pow 2 *
              (&256 * Y pow 3 * L pow 2)` THEN
  CONJ_TAC THENL
   [REPEAT(FIRST [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC;
                  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC;
                  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC]) THEN
    REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC;
                  MATCH_MP_TAC REAL_POW_LE]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&8 * k pow 2 * n * (&8 * L) pow 2 * (&256 * Y pow 3 * L pow 2) =
    ((k * r pow 2) pow 2 * (n * (&131072 * Y pow 3 * L pow 4))) / r pow 4`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~((r:real) = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(n:real) pow 3 * r pow 4 = n pow 2 * (n * r pow 4)`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let GV2_BOUND = prove
 (`!n L Y r k P W c.
     &10 pow 6 * (&1 + c) <= L /\ &0 <= c /\ &1 <= Y /\ &1 <= r /\
     r <= Y pow 2 * L pow 7 /\ &10 pow 7 * Y pow 20 * L pow 70 <= n /\
     &0 < k /\ n <= &2 * r pow 2 * k /\ &0 <= P /\ P <= &8 * L /\
     &0 <= W /\ W <= n * L pow 2 /\ &0 <= log(r pow 2) /\ log(r pow 2) <= L
     ==> &4 * ((r pow 2 * (c * n / (Y pow 10 * L pow 35)) + log(r pow 2)) *
               (&1 + &2 * pi * n / k)) pow 2 * (W + n * P) *
         (&256 * Y pow 3 * L pow 2) <= &2 * n pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&10 pow 6 <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow 6 * (&1 + c)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L /\ &0 < L` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (Y:real) pow 4 * L pow 14 /\ &0 < Y pow 6 * L pow 21 /\
                &0 < Y pow 10 * L pow 35 /\ &0 <= Y pow 3 * L pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL) THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
    CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&10 pow 7 * (Y:real) pow 20 * L pow 70` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real) pow 2 <= Y pow 4 * L pow 14` ASSUME_TAC THENL
   [SUBGOAL_THEN `(Y:real) pow 4 * L pow 14 = (Y pow 2 * L pow 7) pow 2`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = (c:real) * n / (Y pow 6 * L pow 21)` THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= r pow 2 * (c * n / (Y pow 10 * L pow 35)) + log(r pow 2) /\
    r pow 2 * (c * n / (Y pow 10 * L pow 35)) + log(r pow 2) <= u + L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= c * n / (Y pow 10 * L pow 35)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `((Y:real) pow 4 * L pow 14) * (c * n / (Y pow 10 * L pow 35))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "u" THEN
      SUBGOAL_THEN `~((Y:real) = &0) /\ ~((L:real) = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= n / k /\ n / k <= &2 * (Y pow 4 * L pow 14)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * r pow 2 * k` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&2 * r * k = (&2 * r) * k`;
                  REAL_ARITH `(&2 * y) * k = (&2 * y) * k`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&2 * a * k = (&2 * a) * k`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + &2 * pi * n / k /\
                &1 + &2 * pi * n / k <= &17 * (Y pow 4 * L pow 14)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= pi /\ pi <= &4 /\ &1 <= (Y:real) pow 4 * L pow 14`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[PI_POS_LE] THEN CONJ_TAC THENL
       [MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= pi * n / k /\
                  pi * n / k <= &4 * (&2 * (Y pow 4 * L pow 14))`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= W + n * P /\ W + n * P <= &9 * n * L pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `n * P <= n * (&8 * L pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&8 * L` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * ((u + L) * (&17 * (Y pow 4 * L pow 14))) pow 2 *
              (&9 * n * L pow 2) * (&256 * Y pow 3 * L pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&5326848 * (u pow 2 * Y pow 11 * L pow 32 * n) +
              &5326848 * (n * Y pow 11 * L pow 34)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `&4 * ((u + L) * (&17 * (Y pow 4 * L pow 14))) pow 2 *
      (&9 * n * L pow 2) * (&256 * Y pow 3 * L pow 2) =
      &2663424 * ((u + L) pow 2 * (Y pow 11 * L pow 32 * n))`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2663424 * ((&2 * u pow 2 + &2 * L pow 2) *
                            (Y pow 11 * L pow 32 * n))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC `u - L:real` REAL_LE_POW_2) THEN
        REWRITE_TAC[REAL_RING
                     `(u - L:real) pow 2 = u pow 2 + L pow 2 - &2 * u * L`;
                    REAL_RING
                     `(u + L:real) pow 2 = u pow 2 + L pow 2 + &2 * u * L`]
        THEN REAL_ARITH_TAC;
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= n3 /\ b <= n3 ==> a + b <= &2 * n3`) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(u:real) pow 2 * Y pow 11 * L pow 32 * n =
                  (c pow 2 / (Y * L pow 10)) * n pow 3`
    SUBST1_TAC THENL
     [EXPAND_TAC "u" THEN
      SUBGOAL_THEN `~((Y:real) = &0) /\ ~((L:real) = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `&0 < (Y:real) * L pow 10` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&10 pow 6 * (&1 + c)) pow 2` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        SUBGOAL_THEN `c pow 2 <= (&1 + c) pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 10` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n:real) pow 3 = n * n pow 2` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(c:real) * (n * x) = n * (c * x)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&10 pow 7 * Y pow 20 * L pow 70) pow 2` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `(&10 pow 7 * Y pow 20 * L pow 70) pow 2 =
                &10 pow 14 * (Y pow 11 * L pow 34) * (Y pow 29 * L pow 106)`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (Y:real) pow 11 * L pow 34 /\
                &1 <= (Y:real) pow 29 * L pow 106`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&1 = &1 * &1`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `m = (Y:real) pow 11 * L pow 34` THEN
  ABBREV_TAC `y = (Y:real) pow 29 * L pow 106` THEN
  SUBGOAL_THEN `m <= m * (y:real)` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

let G_SMALL = prove
 (`!n L Y. &10 pow 6 <= L /\ &1 <= Y /\ &8 * Y * L <= n
           ==> n / (Y * L) + &1 <= n / (&4 * Y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Y /\ &0 < L /\ &0 < &4 * Y * L` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
    TRY CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n / (Y * L) + &1 = (&4 * n + &4 * Y * L) / (&4 * Y * L) /\
                n / (&4 * Y) = (n * L) / (&4 * Y * L)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < Y` THEN UNDISCH_TAC `&0 < L` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  SUBGOAL_THEN `(&8 * Y * L) * (L - &4) <= n * (L - &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (Y * L) <= (&8 * (L - &4)) * (Y * L)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let G_SING = prove
 (`!n L Y r. &10 pow 6 <= L /\ &1 <= Y /\ &1 <= r /\
             Y pow 2 * L pow 7 <= &2 * r /\ &0 <= n
             ==> &2 * exp(&16) * n / r <= n / (&4 * Y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r /\ &0 < Y /\ &0 < &4 * Y * r` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
    TRY CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 * exp(&16) * Y <= r` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(&16) <= &100000000` ASSUME_TAC THENL
     [SUBGOAL_THEN `exp(&16) = exp(&1) pow 16` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 pow 16` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN `Y <= (Y:real) pow 2 /\ &10 pow 42 <= L pow 7`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&10 pow 6) pow 7` THEN
        CONJ_TAC THENL
         [CONV_TAC REAL_RAT_REDUCE_CONV;
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `Y * &10 pow 42 <= (Y:real) pow 2 * L pow 7` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(&16) * Y <= &100000000 * Y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * exp(&16) * n / r = (n * (&8 * exp(&16) * Y)) /
                                         (&4 * Y * r) /\
                n / (&4 * Y) = (n * r) / (&4 * Y * r)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < Y` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[]);;

let G_VAR = prove
 (`!n L Y V. &1 <= L /\ &1 <= Y /\ &0 < n /\
             V * (&256 * Y pow 3 * L pow 2) <= &4 * n pow 3
             ==> (&4 / (n / (Y * L))) pow 2 * V <= n / (&4 * Y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Y /\ &0 < L /\ &0 < Y pow 3 * L pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
    TRY CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&4 / (n / (Y * L))) pow 2 * V =
                (V * (&256 * Y pow 3 * L pow 2)) / (&16 * n pow 2 * Y)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < Y`; `&0 < L`; `&0 < n`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &16 * n pow 2 * Y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `n / (&4 * Y) * (&16 * n pow 2 * Y) = &4 * n pow 3`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < Y` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The variance of the binary problem; Goldbach for almost all even n.       *)
(* ------------------------------------------------------------------------- *)

let REAL_POW_LINEAR_EXP = prove
 (`!x:real A a b. x pow (a * A + b) = (x pow A) pow a * x pow b`,
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_POW] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MULT_SYM]);;

let GOLDBACH_VARIANCE = prove
 (`!A. ?N0. !N. N0 <= N
           ==> ?Q. 1 <= Q /\ log(&N) pow A <= sqrt(&Q) /\
                   &Q <= log(&N) pow (4 * A + 14) /\
                   sum {n | n < 2 * N + 1}
                       (\n. (goldbach_rep2 N n - goldbach_pair2 N n *
                             sing2_series n Q) pow 2)
                   <= &N pow 3 / log(&N) pow A`,
  GEN_TAC THEN
  MP_TAC(SPECL [`10 * A + 35`; `4 * A + 14`] THETA_AP_UNIFORM) THEN
  DISCH_THEN(X_CHOOSE_TAC `Ct:real`) THEN
  MP_TAC(SPECL [`20 * A + 70`; `&10 pow 7`; `&1`] POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_TAC `L1:real`) THEN
  MP_TAC(SPEC `exp(max L1 (&10 pow 6 * (&1 + abs Ct)))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N1 + 6` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&6 <= &N /\ &0 < &N /\ &N1 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = log(&N)` THEN
  SUBGOAL_THEN `L1 <= L /\ &10 pow 6 * (&1 + abs Ct) <= L`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `max a b <= x ==> a <= x /\ b <= x`) THEN
    EXPAND_TAC "L" THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&10 pow 6 <= L /\ &1 <= L /\ &0 < L` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&10 pow 6 <= L` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&10 pow 6 * (&1 + abs Ct)` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `Ct:real` REAL_ABS_POS) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Y = (L:real) pow A` THEN
  SUBGOAL_THEN `&1 <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&10 pow 7 * Y pow 20 * L pow 70 <= &N` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `L:real`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "L" THEN ASM_SIMP_TAC[EXP_LOG] THEN
    ASM_REWRITE_TAC[REAL_POW_LINEAR_EXP];
    ALL_TAC] THEN
  MP_TAC(SPEC `(Y:real) pow 2 * L pow 7` NUM_FLOOR_HALF) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&1 = &1 * &1`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Q = R EXP 2` THEN
  SUBGOAL_THEN `&Q = &R pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[REAL_OF_NUM_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &Q /\ &Q <= Y pow 4 * L pow 14` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      SUBGOAL_THEN `(Y:real) pow 4 * L pow 14 = (Y pow 2 * L pow 7) pow 2`
      SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q EXP 5 <= N /\ (2 * Q EXP 2 + 1) * Q <= N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&0 <= (Y:real) pow 4 * L pow 14 /\ &1 <= Y pow 4 * L pow 14`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&1 = &1 * &1`] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&Q pow 5 <= ((Y:real) pow 4 * L pow 14) pow 5 /\
                  &Q pow 3 <= (Y pow 4 * L pow 14) pow 5`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `((Y:real) pow 4 * L pow 14) pow 3` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `((Y:real) pow 4 * L pow 14) pow 5 = Y pow 20 * L pow 70`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN
     `(Y:real) pow 20 * L pow 70 <= &10 pow 7 * Y pow 20 * L pow 70`
    ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&Q <= &Q pow 3 /\
                  (&2 * &Q pow 2 + &1) * &Q = &2 * &Q pow 3 + &Q`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        CONV_TAC REAL_RING];
      ALL_TAC] THEN
    MP_TAC(SPEC `(Y:real) pow 20 * L pow 70` REAL_LE_REFL) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `Q:num`] DIV_PARAMETER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Kw = N DIV Q` THEN STRIP_TAC THEN
  SUBGOAL_THEN `Q <= N /\ 3 <= N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Kw * Q:num` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `Q = 1 * Q`] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &R /\ sqrt(&N * &N / &Q) = &N / &R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&N * &N / &R pow 2 = (&N / &R) pow 2` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(&R = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `2 * N + 1`; `Kw:num`; `Q:num`;
                `abs Ct * &N / (Y pow 10 * L pow 35)`;
                `&16000 * L pow 4 * (&N / &R)`] VARIANCE_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]];
      MAP_EVERY X_GEN_TAC [`q:num`; `h:num`; `b:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Ct * &N / log(&N) pow (10 * A + 35)` THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN
        REWRITE_TAC[REAL_POW_LINEAR_EXP] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Q` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ASM_REWRITE_TAC[REAL_POW_LINEAR_EXP] THEN
        REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_INV THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check
        (fun th -> concl th = `sqrt(&N * &N / &Q) = &N / &R`)) THEN
      EXPAND_TAC "L" THEN MATCH_MP_TAC MINOR_POINT_BOUND THEN
      EXISTS_TAC `Kw:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `W = sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)` THEN
  ABBREV_TAC `P = sum(1..Q) (\q. inv(&(phi q)))` THEN
  SUBGOAL_THEN `&0 <= W /\ W <= &N * L pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN EXPAND_TAC "L" THEN MATCH_MP_TAC SUM_W_SQUARE THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&R pow 2) /\ log(&R pow 2) <= L`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "L" THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check
        (fun th -> concl th = `&Q = &R pow 2`)) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P /\ P <= &8 * L` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS];
      MP_TAC(SPEC `Q:num` SUM_INV_PHI_LE) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &R /\ &0 < &Kw /\ &Kw * &R pow 2 <= &N /\
                &N <= &2 * &R pow 2 * &Kw /\ &0 <= &N`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> concl th = `&Q = &R pow 2`)) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[REAL_POS] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&N`; `L:real`; `Y:real`; `&R`; `W:real`] GV1_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&N`; `L:real`; `Y:real`; `&R`; `&Kw`; `P:real`; `W:real`;
                `abs Ct`] GV2_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&N`; `L:real`; `Y:real`; `&R`; `&Kw`; `P:real`]
         GV3_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `V = &2 * ((&16000 * L pow 4 * &N / &R) pow 2 * W +
              &2 * ((&R pow 2 * abs Ct * &N / (Y pow 10 * L pow 35) +
                     log(&R pow 2)) * (&1 + &2 * pi * &N / &Kw)) pow 2 *
              (W + &N * P)) +
        &8 * &Kw pow 2 * &N * P pow 2` THEN
  SUBGOAL_THEN `(V:real) * (&256 * Y pow 3 * L pow 2) <= &4 * &N pow 3`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    UNDISCH_TAC `&2 * ((&16000 * L pow 4 * &N / &R) pow 2 * W) *
                 (&256 * Y pow 3 * L pow 2) <= &N pow 3` THEN
    UNDISCH_TAC `&4 * ((&R pow 2 * abs Ct * &N / (Y pow 10 * L pow 35) +
                        log(&R pow 2)) * (&1 + &2 * pi * &N / &Kw)) pow 2 *
                 (W + &N * P) * (&256 * Y pow 3 * L pow 2) <=
                 &2 * &N pow 3` THEN
    UNDISCH_TAC `&8 * &Kw pow 2 * &N * P pow 2 *
                 (&256 * Y pow 3 * L pow 2) <= &N pow 3` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `Q:num` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[POW_2_SQRT; REAL_POS] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `Y <= (Y:real) pow 2 /\ &2 <= L pow 7` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L:real` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `Y * &2 <= (Y:real) pow 2 * L pow 7` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_LINEAR_EXP] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < Y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(V:real) * Y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum {n | n < 2 * N + 1}
                    (\n. (goldbach_rep2 N n - goldbach_pair2 N n *
                          sing2_series n Q) pow 2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `Y <= (Y:real) pow 3 /\ &1 <= L pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `Y * &1 <= (Y:real) pow 3 * L pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(V:real) * (&4 * Y) <= V * (&256 * Y pow 3 * L pow 2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let GOLDBACH_ALMOST_ALL = prove
 (`!A. ?N0. !N. N0 <= N
           ==> &(CARD {n | n <= N /\ EVEN n /\
                           ~(?p q. prime p /\ prime q /\ p + q = n)})
               <= &N / log(&N) pow A`,
  GEN_TAC THEN
  MP_TAC(SPEC `3 * A + 9` GOLDBACH_VARIANCE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  MP_TAC(SPECL [`A + 1`; `&8`; `&1`] POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_TAC `L1:real`) THEN
  MP_TAC(SPEC `exp(max L1 (&10 pow 6))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N0 + N1 + 6` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&6 <= &N /\ &0 < &N /\ &N1 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = log(&N)` THEN
  SUBGOAL_THEN `L1 <= L /\ &10 pow 6 <= L` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `max a b <= x ==> a <= x /\ b <= x`) THEN
    EXPAND_TAC "L" THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L /\ &0 < L` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Y = (L:real) pow A` THEN
  SUBGOAL_THEN `&1 <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 * Y * L <= &N` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `L:real`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "L" THEN ASM_SIMP_TAC[EXP_LOG] THEN
    ASM_REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sqrt(&Q) /\ Y pow 2 * L pow 7 <= &2 * sqrt(&Q)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= L pow (2 * A + 7) /\
                  L pow (2 * A + 7) <= L pow (3 * A + 9) /\
                  Y pow 2 * L pow 7 = L pow (2 * A + 7)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        REWRITE_TAC[REAL_POW_LINEAR_EXP] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `2 * N + 1`; `Q:num`; `&N / (Y * L)`;
                `&N pow 3 / L pow (3 * A + 9)`] GOLDBACH_FIXED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN
    SUBGOAL_THEN `&0 < Y * L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&N`; `L:real`; `Y:real`] G_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&N`; `L:real`; `Y:real`; `sqrt(&Q)`] G_SING) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&N`; `L:real`; `Y:real`; `&N pow 3 / L pow (3 * A + 9)`]
         G_VAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `L pow (3 * A + 9) = (Y pow 3 * L pow 2) * L pow 7 /\
                  &0 < Y pow 3 * L pow 2 /\ &64 <= L pow 7`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_LINEAR_EXP] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
        CONV_TAC NUM_REDUCE_CONV;
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2) pow 7` THEN
        CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < L pow 7` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&N pow 3 / ((Y pow 3 * L pow 2) * L pow 7) *
      (&256 * Y pow 3 * L pow 2) = (&256 * &N pow 3) / L pow 7`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < Y pow 3 * L pow 2`; `&0 < L pow 7`] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= &N pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&N pow 3 * &64 <= &N pow 3 * L pow 7` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `&N / Y = &4 * (&N / (&4 * Y))` SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= Y` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N / (&4 * Y)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(&4 / (&N / (Y * L))) pow 2 * &N pow 3 / L pow (3 * A + 9)
               <= &N / (&4 * Y)` THEN
  UNDISCH_TAC `&2 * exp(&16) * &N / sqrt(&Q) <= &N / (&4 * Y)` THEN
  UNDISCH_TAC `&N / (Y * L) + &1 <= &N / (&4 * Y)` THEN
  SPEC_TAC(`&(CARD {n | n <= N /\ EVEN n /\
                        ~(?p q. prime p /\ prime q /\ p + q = n)})`, `cd:real`)
  THEN REAL_ARITH_TAC);;

let GOLDBACH_ALMOST_ALL_DENSITY = prove
 (`((\N. &(CARD {n | n <= N /\ EVEN n /\
                     ~(?p q. prime p /\ prime q /\ p + q = n)}) / &N)
    ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `1` GOLDBACH_ALMOST_ALL) THEN REWRITE_TAC[REAL_POW_1] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  MP_TAC(SPEC `exp(&2 / e)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N0 + N1 + 2` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `CARD {n | n <= N /\ EVEN n /\
                         ~(?p q. prime p /\ prime q /\ p + q = n)}`
         REAL_POS) THEN
  SPEC_TAC(`&(CARD {n | n <= N /\ EVEN n /\
                        ~(?p q. prime p /\ prime q /\ p + q = n)})`,
           `cd:real`) THEN
  X_GEN_TAC `cd:real` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&1 < &N /\ &0 < &N /\ &N1 < &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 < log(&N) * e /\ &0 < log(&N)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_POS_LT; GSYM REAL_LT_LDIV_EQ] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[EXP_LOG] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(cd / &N) = cd / &N` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N / log(&N)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `&N * &2 < &N * (log(&N) * e)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
