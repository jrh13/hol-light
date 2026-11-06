(* ========================================================================= *)
(* Three-term arithmetic progressions of primes (van der Corput 1939).       *)
(*   VAN_DER_CORPUT_COUNT:                                                   *)
(*     ?c N0. &0 < c /\                                                      *)
(*            !N. N0 <= N                                                    *)
(*                ==> c * &N pow 2 / log(&N) pow 3 <=                        *)
(*                    &(CARD {(a,d) | 0 < d /\ prime a /\ prime(a + d) /\    *)
(*                                    prime(a + 2 * d) /\ a + 2 * d <= N})   *)
(*   VAN_DER_CORPUT:                                                         *)
(*     !m. ?a d. m <= a /\ 0 < d /\ prime a /\ prime(a + d) /\               *)
(*               prime(a + 2 * d)                                            *)
(*   AP3W_LOWER: the weighted count ap3w N, the sum of log p1 log p2 log p3  *)
(*   over the primes p1, p2, p3 <= N with p1 + p3 = 2 p2, is at least        *)
(*   N^2 / 40 for all large N.                                               *)
(*                                                                           *)
(* Method: the case k = 3 of the Green-Tao theorem by the circle method, in  *)
(* the form of the variance of the binary Goldbach problem                   *)
(* (GOLDBACH_VARIANCE, goldbach_almost.ml):                                  *)
(*   ap3w N = sum_{m <= N} w(m) goldbach_rep2 N (2 m),   w(m) = [prime m]    *)
(*   log m.                                                                  *)
(* * For the primes m in (N/4, N/2]: goldbach_pair2 N (2 m) = 2 m - 1 >= N/2 *)
(*   - 1, and sing2_series (2 m) Q = sing2_series 2 Q once m > Q, since the  *)
(*   Ramanujan sums c_q(2 m) and c_q(2) agree for q < m                      *)
(*   (SING2_SERIES_DOUBLE_PRIME); sing2_series 2 Q >= 1/2 once               *)
(*   sqrt Q >= 4 e^16 (SING2_TAIL_L1 and SING2_PRODUCT_LOWER at n = 2).      *)
(* * Cauchy-Schwarz against GOLDBACH_VARIANCE with A = 4 bounds the error    *)
(*   sum_m w(m) (goldbach_rep2 N (2 m) - goldbach_pair2 N (2 m) sing2_series *)
(*   (2 m) Q) by sqrt(N log^2 N * N^3 / log^4 N) = N^2 / log N               *)
(*   (AP3_SUBSET_ERROR).                                                     *)
(* * The prime number theorem gives sum_{N/4 < p <= N/2} log p >= N/8        *)
(*   (THETA_HALF_QUARTER), so ap3w N >= (1/2) (N/2 - 1) (N/8) - N^2 / log N  *)
(*   >= N^2 / 40 (AP3W_LOWER).                                               *)
(* * Counting: every solution (m1, m, 2 m - m1) has weight at most           *)
(*   log^3 N (AP3W_UPPER); those with m1 /= m come from the progressions     *)
(*   (a, d), each in two ways (AP3_PAIRS_CARD), so there are at least        *)
(*   N^2 / (160 log^3 N) progressions with a + 2 d <= N.                     *)
(* ========================================================================= *)

needs "Sieve/goldbach_almost.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Weights; the binary singular series at 2 p.                               *)
(* ------------------------------------------------------------------------- *)

let ap3w = new_definition
 `ap3w N = sum(1..N) (\m. (if prime m then log(&m) else &0) *
                          goldbach_rep2 N (2 * m))`;;

let PRIME_WEIGHT_POS = prove
 (`!m. &0 <= (if prime m then log(&m) else &0)`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC);;

let PRIME_WEIGHT_LE = prove
 (`!m N. 1 <= N /\ m <= N ==> (if prime m then log(&m) else &0) <= log(&N)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]]);;

let GOLDBACH_REP2_POS = prove
 (`!N n. &0 <= goldbach_rep2 N n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[goldbach_rep2] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PRIME_WEIGHT_POS]);;

let RAMANUJAN_SUM_DOUBLE_PRIME = prove
 (`!p q. prime p /\ 1 <= q /\ q < p
         ==> ramanujan_sum q (2 * p) = ramanujan_sum q 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ramanujan_sum] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN
  ASM_CASES_TAC `d divides q` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC COPRIME_DIVPROD THEN
    EXISTS_TAC `p:num` THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`d:num`; `q:num`] DIVIDES_LE) THEN
    MP_TAC(SPECL [`p:num`; `d:num`] DIVIDES_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `d = 0` THENL
     [UNDISCH_TAC `d divides q` THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL; MULT_SYM]]);;

let SING2_SERIES_DOUBLE_PRIME = prove
 (`!p Q. prime p /\ Q < p ==> sing2_series (2 * p) Q = sing2_series 2 Q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sing2_series] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  REWRITE_TAC[sing2_term] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RAMANUJAN_SUM_DOUBLE_PRIME THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let SING2_SERIES_TWO_LOWER = prove
 (`!Q. 1 <= Q /\ &4 * exp(&16) <= sqrt(&Q)
       ==> &1 / &2 <= sing2_series 2 Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `Q:num`] SING2_TAIL_L1) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY; ARITH_EQ] THEN
  MP_TAC(SPECL [`2`; `Q:num`] SING2_PRODUCT_LOWER) THEN
  REWRITE_TAC[ARITH] THEN
  SUBGOAL_THEN `&0 < sqrt(&Q)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&16` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&16) * &2 / sqrt(&Q) <= &1 / &2` MP_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `P1 = product {p | prime p /\ p <= Q} (\p. &1 + sing2_term 1 p)` THEN
  ABBREV_TAC
   `P2 = product {p | prime p /\ p <= Q} (\p. &1 + sing2_term 2 p)` THEN
  REAL_ARITH_TAC);;

let EXP_16_BOUND = prove
 (`&4 * exp(&16) <= &10 pow 12`,
  SUBGOAL_THEN `exp(&16) = exp(&1) pow 16` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * &3 pow 16` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_POS_LE; EXP_1_LE_3]];
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* The weighted count from the variance of the binary problem.               *)
(* ------------------------------------------------------------------------- *)

let AP3_SUBSET_ERROR = prove
 (`!N Q s. s SUBSET 1..N
           ==> abs(sum s (\m. (if prime m then log(&m) else &0) *
                              (goldbach_rep2 N (2 * m) -
                               goldbach_pair2 N (2 * m) *
                               sing2_series (2 * m) Q)))
               <= sqrt(sum(1..N)
                           (\m. (if prime m then log(&m) else &0) pow 2) *
                       sum {n | n < 2 * N + 1}
                           (\n. (goldbach_rep2 N n - goldbach_pair2 N n *
                                 sing2_series n Q)
                                pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW2_ABS] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SIEVE_SUM_CAUCHY_SCHWARZ o
      lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_LE_POW_2];
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m:num. 2 * m`;
                 `\n. (goldbach_rep2 N n - goldbach_pair2 N n *
                       sing2_series n Q) pow 2`;
                 `s:num->bool`] SUM_IMAGE) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_POW_2] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `m IN 1..N` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let DIV_2_4_FACTS = prove
 (`!N. N <= 2 * (N DIV 2) + 1 /\ 4 * (N DIV 4) <= N /\
       N < 4 * (N DIV 4) + 4 /\ N DIV 4 <= N DIV 2 /\ 2 * (N DIV 2) <= N`,
  GEN_TAC THEN
  MP_TAC(SPECL [`N:num`; `2`] DIVISION) THEN
  MP_TAC(SPECL [`N:num`; `4`] DIVISION) THEN
  ARITH_TAC);;

let THETA_HALF_QUARTER = prove
 (`?N0. !N. N0 <= N
           ==> &N / &8 <= sum {m | N DIV 4 < m /\ m <= N DIV 2}
                              (\m. if prime m then log(&m) else &0)`,
  MP_TAC(SPEC `1` PNT_THETA_UNIFORM) THEN REWRITE_TAC[REAL_POW_1] THEN
  DISCH_THEN(X_CHOOSE_TAC `Cb:real`) THEN
  MP_TAC(SPEC `exp(&32 * (&1 + abs Cb))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N1 + 16` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `N:num` DIV_2_4_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `sum {m | N DIV 4 < m /\ m <= N DIV 2}
        (\m. if prime m then log(&m) else &0) =
    sum {p | prime p /\ p <= N DIV 2} (\p. log(&p)) -
    sum {p | prime p /\ p <= N DIV 4} (\p. log(&p))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\p:num. log(&p)`; `&(N DIV 4)`; `&(N DIV 2)`]
           SUM_PRIMES_INTERVAL) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 <= &N /\ &N1 <= &N /\ &2 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&N`; `N DIV 2`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&N`; `N DIV 4`]) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `N DIV 4 <= N /\ N DIV 2 <= N` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = log(&N)` THEN
  SUBGOAL_THEN `&32 * (&1 + abs Cb) <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&16 <= x ==> &0 < x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [MP_TAC(SPEC `Cb:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Cb * &N / L <= &N / &32` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &N / L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + abs Cb) * &N / L` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L / &32) * &N / L` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < L` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N <= &2 * &(N DIV 2) + &1 /\ &4 * &(N DIV 4) <= &N`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD];
    ALL_TAC] THEN
  ABBREV_TAC `T2 = sum {p | prime p /\ p <= N DIV 2} (\p. log(&p))` THEN
  ABBREV_TAC `T4 = sum {p | prime p /\ p <= N DIV 4} (\p. log(&p))` THEN
  ASM_REAL_ARITH_TAC);;

let AP3W_LOWER = prove
 (`?N0. !N. N0 <= N ==> &N pow 2 / &40 <= ap3w N`,
  MP_TAC(SPEC `4` GOLDBACH_VARIANCE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "var")) THEN
  X_CHOOSE_THEN `N2:num` (LABEL_TAC "theta") THETA_HALF_QUARTER THEN
  MP_TAC(SPECL [`30`; `&8`; `&1`] POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real` (LABEL_TAC "poly")) THEN
  MP_TAC(SPEC `exp(max L1 (&1000))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  EXISTS_TAC `N1 + N2 + N3 + 100` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  REMOVE_THEN "var" (MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:num` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "theta" (MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `N:num` DIV_2_4_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&100 <= &N /\ &N3 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = log(&N)` THEN
  SUBGOAL_THEN `L1 <= L /\ &1000 <= L` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `max a b <= x ==> a <= x /\ b <= x`) THEN
    EXPAND_TAC "L" THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&100 <= x ==> &0 < x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 * L pow 30 <= &N` ASSUME_TAC THENL
   [REMOVE_THEN "poly" (MP_TAC o SPEC `L:real`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "L" THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&100 <= x ==> &0 < x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q <= N DIV 4` ASSUME_TAC THENL
   [SUBGOAL_THEN `&8 * &Q <= &N` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&8 * (L:real) pow 30` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&Q <= L pow (4 * 4 + 14)` THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= sing2_series 2 Q` ASSUME_TAC THENL
   [MATCH_MP_TAC SING2_SERIES_TWO_LOWER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 4` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1000:real) pow 4` THEN
    CONJ_TAC THENL
     [MP_TAC EXP_16_BOUND THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `s = {m | N DIV 4 < m /\ m <= N DIV 2}` THEN
  SUBGOAL_THEN `s SUBSET 1..N` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum s (\m. (if prime m then log(&m) else &0) *
               goldbach_rep2 N (2 * m))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[ap3w] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[PRIME_WEIGHT_POS; GOLDBACH_REP2_POS]] THEN
  SUBGOAL_THEN
   `sum s (\m. (if prime m then log(&m) else &0) * goldbach_rep2 N (2 * m)) =
    sing2_series 2 Q *
    sum s (\m. (if prime m then log(&m) else &0) * (&2 * &m - &1)) +
    sum s (\m. (if prime m then log(&m) else &0) *
               (goldbach_rep2 N (2 * m) - goldbach_pair2 N (2 * m) *
                sing2_series (2 * m) Q))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN ASM_SIMP_TAC[GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `prime m` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN `goldbach_pair2 N (2 * m) = &2 * &m - &1 /\
                  sing2_series (2 * m) Q = sing2_series 2 Q`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`N:num`; `2 * m`] GOLDBACH_PAIR2_EQ) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL];
        MATCH_MP_TAC SING2_SERIES_DOUBLE_PRIME THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `A = sum s (\m. (if prime m then log(&m) else &0) * (&2 * &m - &1))` THEN
  ABBREV_TAC
   `B = sum s (\m. (if prime m then log(&m) else &0) *
                   (goldbach_rep2 N (2 * m) - goldbach_pair2 N (2 * m) *
                                     sing2_series (2 * m) Q))` THEN
  ABBREV_TAC `Tw = sum s (\m. if prime m then log(&m) else &0)` THEN
  SUBGOAL_THEN `(&N / &2 - &1) * Tw <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN EXPAND_TAC "Tw" THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[PRIME_WEIGHT_POS] THEN
    SUBGOAL_THEN `&N < &4 * &m` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs B <= &N pow 2 / &1000` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) AP3_SUBSET_ERROR o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MP_TAC(SPEC `N:num` SUM_W_SQUARE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN STRIP_TAC THEN
    ABBREV_TAC
     `W = sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)` THEN
    ABBREV_TAC
     `V = sum {n | n < 2 * N + 1}
              (\n. (goldbach_rep2 N n - goldbach_pair2 N n * sing2_series n Q)
                     pow 2)` THEN
    SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
     [EXPAND_TAC "V" THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < L pow 4 /\ &0 < L` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `W * V <= (&N pow 2 / L) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&N * (L:real) pow 2) * (&N pow 3 / L pow 4)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < L` THEN
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N pow 2 / (L:real)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC SUM_POS_LE THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PRIME_WEIGHT_POS] THEN
    SUBGOAL_THEN `&1 <= &m` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `A / &2 <= sing2_series 2 Q * A` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&N / &2 - &1) * (&N / &8) <= (&N / &2 - &1) * Tw`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&100 * &N <= &N pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* From the weighted count to progressions.                                  *)
(* ------------------------------------------------------------------------- *)

let GOLDBACH_REP2_DELTA = prove
 (`!N n. goldbach_rep2 N n =
         sum(1..N) (\m1. if m1 < n /\ n - m1 <= N
                         then (if prime m1 then log(&m1) else &0) *
                              (if prime(n - m1) then log(&(n - m1)) else &0)
                         else &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[goldbach_rep2] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m1:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `!m2. m2 IN 1..N ==> (m1 + m2 = n <=> m1 < n /\ m2 = n - m1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..N) (\m2. if m2 = n - m1
                              then (if m1 < n
                                    then (if prime m1 then log(&m1) else &0) *
                                         (if prime(n - m1)
                                          then log(&(n - m1)) else &0)
                                    else &0)
                              else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m2:num` THEN DISCH_TAC THEN
    BETA_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `m2:num`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `(m2:num) = n - m1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN
  ASM_CASES_TAC `(m1:num) < n` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(n:num) - m1 <= N` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PRIME_WEIGHT_TRIPLE_LE = prove
 (`!N a b c. 1 <= N /\ a <= N /\ b <= N /\ c <= N
             ==> (if prime a then log(&a) else &0) *
                 (if prime b then log(&b) else &0) *
                 (if prime c then log(&c) else &0)
                 <= if prime a /\ prime b /\ prime c then log(&N) pow 3
                    else &0`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `prime a /\ prime b /\ prime c` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `log(&N) pow 3 = log(&N) * log(&N) * log(&N)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`a:num`; `N:num`] PRIME_WEIGHT_LE) THEN
    MP_TAC(SPECL [`b:num`; `N:num`] PRIME_WEIGHT_LE) THEN
    MP_TAC(SPECL [`c:num`; `N:num`] PRIME_WEIGHT_LE) THEN
    MP_TAC(SPEC `a:num` PRIME_WEIGHT_POS) THEN
    MP_TAC(SPEC `b:num` PRIME_WEIGHT_POS) THEN
    MP_TAC(SPEC `c:num` PRIME_WEIGHT_POS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `prime a` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
    ASM_CASES_TAC `prime b` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL] THEN
    ASM_CASES_TAC `prime c` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL] THEN
    ASM_MESON_TAC[]]);;

let AP3W_UPPER = prove
 (`!N. 1 <= N
       ==> ap3w N <=
           log(&N) pow 3 *
           &(CARD {(m,m1) | m IN 1..N /\ m1 IN 1..N /\ m1 < 2 * m /\
                            2 * m - m1 <= N /\ prime m /\ prime m1 /\
                            prime(2 * m - m1)})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = {(m,m1) | m IN 1..N /\ m1 IN 1..N /\ m1 < 2 * m /\
                            2 * m - m1 <= N /\ prime m /\ prime m1 /\
                            prime(2 * m - m1)}` THEN
  SUBGOAL_THEN `t SUBSET {m,m1 | m IN 1..N /\ m1 IN 1..N}` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {m,m1 | m IN 1..N /\ m1 IN 1..N}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT THEN REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(t:num#num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_EQ_SUM; GSYM SUM_LMUL; REAL_MUL_RID] THEN
  MP_TAC(ISPECL [`\x:num#num. if x IN t then log(&N) pow 3 else &0`;
                 `t:num#num->bool`;
                 `{m,m1 | m IN 1..N /\ m1 IN 1..N}`] SUM_SUPERSET) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sum t (\x:num#num. if x IN t then log(&N) pow 3 else &0) =
                sum t (\x. log(&N) pow 3)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ap3w; GOLDBACH_REP2_DELTA] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `m1:num`] THEN REWRITE_TAC[IN_NUMSEG] THEN
  STRIP_TAC THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `m1 < 2 * m /\ 2 * m - m1 <= N` THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`N:num`; `m:num`; `m1:num`; `2 * m - m1`]
           PRIME_WEIGHT_TRIPLE_LE) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE]]);;

let FINITE_AP3 = prove
 (`!N. FINITE {(a,d) | 0 < d /\ prime a /\ prime(a + d) /\
                       prime(a + 2 * d) /\ a + 2 * d <= N}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{a,d | a IN 0..N /\ d IN 0..N}` THEN
  SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
  ARITH_TAC);;

let AP3_PAIRS_CARD = prove
 (`!N. CARD {(m,m1) | m IN 1..N /\ m1 IN 1..N /\ m1 < 2 * m /\
                      2 * m - m1 <= N /\ prime m /\ prime m1 /\
                      prime(2 * m - m1)}
       <= N + 2 * CARD {(a,d) | 0 < d /\ prime a /\ prime(a + d) /\
                                prime(a + 2 * d) /\ a + 2 * d <= N}`,
  GEN_TAC THEN
  ABBREV_TAC `s = {(a,d) | 0 < d /\ prime a /\ prime(a + d) /\
                           prime(a + 2 * d) /\ a + 2 * d <= N}` THEN
  SUBGOAL_THEN `FINITE(s:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[FINITE_AP3]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\p:num. (p,p)) (1..N) UNION
                   (IMAGE (\(a,d). (a + d,a)) s UNION
                    IMAGE (\(a,d). (a + d,a + 2 * d)) s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_UNION;
                IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ; IN_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `m1:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m1:num = m` THENL
     [DISJ1_TAC THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN ASM_CASES_TAC `(m1:num) < m` THENL
     [DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`m1:num`; `(m:num) - m1`] THEN
      EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      SUBGOAL_THEN `(m1:num) + m - m1 = m /\ m1 + 2 * (m - m1) = 2 * m - m1`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`2 * (m:num) - m1`; `(m1:num) - m`] THEN
      EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      SUBGOAL_THEN `(2 * (m:num) - m1) + m1 - m = m /\
                    (2 * m - m1) + 2 * (m1 - m) = m1`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\p:num. (p,p)) (1..N)) +
              (CARD(IMAGE (\(a,d). (a + d,a)) s) +
               CARD(IMAGE (\(a,d). (a + d,a + 2 * d)) s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(IMAGE (\p:num. (p,p)) (1..N)) +
                CARD(IMAGE (\(a,d). (a + d,a)) s UNION
                     IMAGE (\(a,d). (a + d,a + 2 * d)) s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_UNION_LE THEN
      ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUMSEG];
      REWRITE_TAC[LE_ADD_LCANCEL] THEN MATCH_MP_TAC CARD_UNION_LE THEN
      ASM_SIMP_TAC[FINITE_IMAGE]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= n /\ b <= s /\ c <= s
                           ==> a + (b + c) <= n + 2 * s`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..N)` THEN
    SIMP_TAC[CARD_IMAGE_LE; FINITE_NUMSEG; CARD_NUMSEG_1; LE_REFL];
    ASM_SIMP_TAC[CARD_IMAGE_LE];
    ASM_SIMP_TAC[CARD_IMAGE_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Three-term progressions of primes.                                        *)
(* ------------------------------------------------------------------------- *)

let VAN_DER_CORPUT_COUNT = prove
 (`?c N0. &0 < c /\
          !N. N0 <= N
              ==> c * &N pow 2 / log(&N) pow 3 <=
                  &(CARD {(a,d) | 0 < d /\ prime a /\ prime(a + d) /\
                                  prime(a + 2 * d) /\ a + 2 * d <= N})`,
  X_CHOOSE_THEN `N1:num` (LABEL_TAC "low") AP3W_LOWER THEN
  MP_TAC(SPECL [`3`; `&80`; `&1`] POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real` (LABEL_TAC "poly")) THEN
  MP_TAC(SPEC `exp(max L1 (&1))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `&1 / &160` THEN EXISTS_TAC `N1 + N2 + 3` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  ABBREV_TAC `c0 = CARD {(a,d) | 0 < d /\ prime a /\ prime(a + d) /\
                                 prime(a + 2 * d) /\ a + 2 * d <= N}` THEN
  ABBREV_TAC `d0 = CARD {(m,m1) | m IN 1..N /\ m1 IN 1..N /\ m1 < 2 * m /\
                                  2 * m - m1 <= N /\ prime m /\ prime m1 /\
                                  prime(2 * m - m1)}` THEN
  REMOVE_THEN "low" (MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `N:num` AP3W_UPPER) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPEC `N:num` AP3_PAIRS_CARD) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&3 <= &N /\ &N2 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = log(&N)` THEN
  SUBGOAL_THEN `L1 <= L /\ &1 <= L` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `max a b <= x ==> a <= x /\ b <= x`) THEN
    EXPAND_TAC "L" THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&3 <= x ==> &0 < x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&80 * L pow 3 <= &N` ASSUME_TAC THENL
   [REMOVE_THEN "poly" (MP_TAC o SPEC `L:real`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "L" THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&3 <= x ==> &0 < x`];
    ALL_TAC] THEN
  ABBREV_TAC `C = &c0` THEN ABBREV_TAC `D = &d0` THEN
  SUBGOAL_THEN `&0 < L pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L pow 3 * D <= L pow 3 * (&N + &2 * C)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(&80 * L pow 3) * &N <= &N * &N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&N pow 2 / L pow 3 <= &160 * C` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let VAN_DER_CORPUT = prove
 (`!m. ?a d. m <= a /\ 0 < d /\ prime a /\ prime(a + d) /\
             prime(a + 2 * d)`,
  GEN_TAC THEN
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)
    VAN_DER_CORPUT_COUNT THEN
  MP_TAC(SPECL [`3`; `&4 * (&m + &1) / c`; `&1`] POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real` (LABEL_TAC "poly")) THEN
  MP_TAC(SPEC `exp(max L1 (&1))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  ABBREV_TAC `N = N0 + N2 + 3` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&m * (&N + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {a,d | a IN {x:num | x < m} /\ d IN 0..N})` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG;
                  IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:num`; `d:num`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `d:num`]) THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[CARD_PRODUCT; FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[CARD_NUMSEG_LT; CARD_NUMSEG; GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[ARITH_RULE `(N + 1) - 0 = N + 1`; GSYM REAL_OF_NUM_ADD;
                  REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= &N /\ &N2 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN EXPAND_TAC "N" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `L1 <= log(&N) /\ &1 <= log(&N)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `max a b <= x ==> a <= x /\ b <= x`) THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&3 <= x ==> &0 < x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "poly" (MP_TAC o SPEC `log(&N)`) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&3 <= x ==> &0 < x`] THEN
  ABBREV_TAC `L = log(&N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < L pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (&m + &1) * L pow 3 <= c * &N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * ((&4 * (&m + &1) / c) * L pow 3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < c` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (&m + &1) * &N <= c * &N pow 2 / L pow 3`
  MP_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `(&4 * (&m + &1) * L pow 3) * &N <= (c * &N) * &N`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&m * &1 <= &m * &N` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &m` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
