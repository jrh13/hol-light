(* ========================================================================= *)
(* Vinogradov's three primes theorem (1937):                                 *)
(*   VINOGRADOV:                                                             *)
(*     ?N0. !N. ODD N /\ N0 <= N                                             *)
(*              ==> ?p1 p2 p3. prime p1 /\ prime p2 /\ prime p3 /\           *)
(*                             p1 + p2 + p3 = N                              *)
(*                                                                           *)
(* Method (Nathanson ch. 8, with a discrete circle method).                  *)
(* * vinogradov_rep3 N = sum over m1 + m2 + m3 = N of w(m1) w(m2) w(m3),     *)
(*   w(m) = [prime m] log m; VINOGRADOV_REP3_POS: vinogradov_rep3 N > 0      *)
(*   gives the three primes.  With primexp N x = sum_{m <= N} w(m) e(m x)    *)
(*   and M = 3 N + 1, CIRCLE_PRIMEXP:                                        *)
(*     sum_{k < M} primexp N (k/M)^3 e(-N k/M) = M vinogradov_rep3 N.        *)
(* * Major arcs circ_arc M K q a = {k < M | ndist(k/M - a/q) <= 1/K}, q <=   *)
(*   Q, a < q, (a,q) = 1, disjoint for 2 Q^2 < K (FAREY_SEPARATION,          *)
(*   CIRC_ARC_DISJOINT).  On them primexp N (k/M) is mu(q)/phi(q) unitexp    *)
(*   N (k/M - a/q) up to an error controlled by theta in the progressions    *)
(*   mod q (ARC_APPROX, MAJOR_ARC_APPROX: residue classes, Ramanujan sums,   *)
(*   partial summation), and MAJOR_TOTAL evaluates the major arc sum as      *)
(*   M (N - 1)(N - 2)/2 sing_series N Q up to explicit errors                *)
(*   (CIRCLE_UNITEXP, ARC_MAIN_TERM, CUBE_DIFF_BOUND, Parseval).             *)
(* * Singular series: sing_series N Q = sum_{q <= Q} (mu(q)/phi(q))^3        *)
(*   ramanujan_sum q N; SING_SERIES_LOWER: for odd N,                        *)
(*     1 - exp(8) / sqrt Q <= sing_series N Q,                               *)
(*   from the Euler product over the primes p <= Q (>= 1 for odd N:          *)
(*   SING_PRODUCT_LOWER) and Rankin's trick with sqrt d for the q > Q        *)
(*   (SING_PRODUCT_RANKIN, SING_SERIES_TAIL).                                *)
(* * Minor arcs: Dirichlet's approximation with denominator K gives Q < q    *)
(*   <= K (MINOR_DIRICHLET); VINOGRADOV_LAMBDA_BOUND with U = V = Q^2 and    *)
(*   the prime power correction give MINOR_POINT_BOUND:                      *)
(*     |primexp N (k/M)| <= 16000 log^4 N sqrt(N^2/Q).                       *)
(* * VINOGRADOV_FIXED: |vinogradov_rep3 N - (N - 1)(N - 2)/2 sing_series N   *)
(*   Q| is at most an explicit sum of the three errors.  With Q =            *)
(*   floor(log^8 N)^2, K = N DIV Q and the Siegel-Walfisz constant for A =   *)
(*   40, B = 16, the errors are below N^2/250 and the main term at least     *)
(*   N^2/8 for all large N (E1_BOUND, E2_BOUND, E3_BOUND).                   *)
(* ========================================================================= *)

needs "Sieve/vinogradov_minor.ml";;
needs "Sieve/sw_theta.ml";;
needs "Sieve/pairs_sieve.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Primes on a major arc.                                                    *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_COPRIME = prove
 (`!q a. 1 <= q /\ coprime(a,q)
         ==> vsum {b | b < q /\ coprime(b,q)} (\b. expi(&a * &b / &q)) =
             Cx(mobius q)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RAMANUJAN_FORMULA] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `{d | d divides q /\ d divides a} = {1}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `d:num` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN UNDISCH_TAC `coprime(a,q)` THEN
      REWRITE_TAC[coprime] THEN ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIVIDES_1]];
    REWRITE_TAC[SUM_SING; DIV_1; REAL_MUL_LID]]);;

let EXPI_MOD = prove
 (`!q a m. ~(q = 0) ==> expi(&m * &a / &q) = expi(&a * &(m MOD q) / &q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `m:num`; `m MOD q`; `a:num`] EXPI_CONG) THEN
  ASM_REWRITE_TAC[CONG_RMOD; CONG_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
  REAL_ARITH_TAC);;

let RESIDUE_DECOMP = prove
 (`!q a h.
     1 <= q
     ==> vsum(1..h) (\m. Cx(if prime m then log(&m) else &0) *
                         expi(&m * &a / &q)) =
         vsum {b | b < q}
           (\b. expi(&a * &b / &q) *
                Cx(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                       (\p. log(&p))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum(1..h) (\m. vsum {b | b < q}
       (\b. if b = m MOD q
            then Cx(if prime m then log(&m) else &0) * expi(&a * &b / &q)
            else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `vsum {b | b < q}
       (\b. if b = m MOD q
            then Cx(if prime m then log(&m) else &0) *
                 expi(&a * &(m MOD q) / &q)
            else vec 0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VSUM_DELTA; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[MOD_LT_EQ] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC EXPI_MOD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(GEN `f:num->num->complex`
   (MP (ISPECL [`f:num->num->complex`; `1..h`; `{b:num | b < q}`] VSUM_SWAP)
       (CONJ (SPECL [`1`; `h:num`] FINITE_NUMSEG)
             (SPEC `q:num` FINITE_NUMSEG_LT)))) THEN
  DISCH_THEN(fun sw -> GEN_REWRITE_TAC LAND_CONV [sw]) THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `b:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(if (b:num) = c then (x:complex) else y) = (if c = b then x else y)`]
  THEN REWRITE_TAC[GSYM VSUM_RESTRICT_SET] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  SIMP_TAC[VSUM_CX; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  GEN_REWRITE_TAC RAND_CONV [COMPLEX_MUL_SYM] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG; CONG] THEN
  ASM_SIMP_TAC[MOD_LT] THEN X_GEN_TAC `p:num` THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC);;

let THETA_NONCOPRIME_RESIDUES = prove
 (`!q h. 1 <= q
         ==> sum {b | b < q /\ ~coprime(b,q)}
               (\b. sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                        (\p. log(&p))) <= log(&q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s = {p | prime p /\ p <= h /\ ~coprime(p,q)}` THEN
  SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..h` THEN REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM;
                                      IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p. p MOD q`; `\p. log(&p)`; `s:num->bool`;
                 `{b | b < q /\ ~coprime(b,q)}`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[COPRIME_LMOD; MOD_LT_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c <= d ==> a = c ==> b <= d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `b:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONG] THEN ASM_SIMP_TAC[MOD_LT] THEN
    X_GEN_TAC `p:num` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM COPRIME_LMOD] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ p divides q} (\p. log(&p))` THEN
  ASM_SIMP_TAC[LOG_SUM_PRIME_DIVISORS] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d | d divides q}` THEN
    ASM_SIMP_TAC[FINITE_DIVISORS] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[PRIME_COPRIME_EQ];
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC]);;

let PARTIAL_SUM_MAJOR = prove
 (`!q a h D.
     1 <= q /\ coprime(a,q) /\
     (!b. b < q /\ coprime(b,q)
          ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                      (\p. log(&p)) - &h / &(phi q)) <= D)
     ==> norm(vsum(1..h) (\m. Cx(if prime m then log(&m) else &0) *
                              expi(&m * &a / &q)) -
              Cx(&h * mobius q / &(phi q))) <= &(phi q) * D + log(&q)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RESIDUE_DECOMP] THEN
  MP_TAC(ISPECL
   [`{b:num | b < q}`; `\b. coprime(b,q)`;
    `\b. expi(&a * &b / &q) *
         Cx(sum {p | prime p /\ p <= h /\ (p == b) (mod q)} (\p. log(&p)))`;
    `\b. expi(&a * &b / &q) *
         Cx(sum {p | prime p /\ p <= h /\ (p == b) (mod q)} (\p. log(&p)))`]
   VSUM_CASES) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; COND_ID; ETA_AX; IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < &(phi q):real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&h * mobius q / &(phi q)) =
    vsum {b | b < q /\ coprime(b,q)}
      (\b. expi(&a * &b / &q) * Cx(&h / &(phi q)))`
  SUBST1_TAC THENL
   [SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_RESTRICT; FINITE_NUMSEG_LT;
             SET_RULE `{b:num | b < q /\ coprime(b,q)} =
                       {b | b IN {b | b < q} /\ coprime(b,q)}`] THEN
    REWRITE_TAC[GSYM(SET_RULE `{b:num | b < q /\ coprime(b,q)} =
                       {b | b IN {b | b < q} /\ coprime(b,q)}`)] THEN
    ASM_SIMP_TAC[RAMANUJAN_COPRIME; GSYM CX_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a - c:complex) <= x /\ norm(b:complex) <= y
    ==> norm((a + b) - c) <= x + y`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[GSYM VSUM_SUB; FINITE_RESTRICT; FINITE_NUMSEG_LT;
             SET_RULE `{b:num | b < q /\ coprime(b,q)} =
                       {b | b IN {b | b < q} /\ coprime(b,q)}`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {b | b IN {b | b < q} /\ coprime(b,q)} (\b. D)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB; COMPLEX_NORM_MUL; NORM_EXPI;
                  REAL_MUL_LID; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[PHI_ALT; REAL_OF_NUM_EQ] THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {b | b < q /\ ~coprime(b,q)}
               (\b. sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                        (\p. log(&p)))` THEN
  ASM_SIMP_TAC[THETA_NONCOPRIME_RESIDUES] THEN
  REWRITE_TAC[SET_RULE `{b:num | b < q /\ ~coprime(b,q)} =
                        {b | b IN {b | b < q} /\ ~coprime(b,q)}`] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_LID; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x <= x`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_POS THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC);;

let MAJOR_ARC_APPROX = prove
 (`!N q a beta D.
     1 <= q /\ coprime(a,q) /\
     (!h b. h <= N /\ b < q /\ coprime(b,q)
            ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                        (\p. log(&p)) - &h / &(phi q)) <= D)
     ==> norm(vsum(1..N) (\m. Cx(if prime m then log(&m) else &0) *
                              expi(&m * (&a / &q + beta))) -
              Cx(mobius q / &(phi q)) * vsum(1..N) (\m. expi(&m * beta)))
         <= (&(phi q) * D + log(&q)) * (&1 + &2 * pi * &N * abs beta)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `1 MOD q`]) THEN
    ASM_REWRITE_TAC[LE_0; MOD_LT_EQ; COPRIME_LMOD; COPRIME_1] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Mb = &(phi q) * D + log(&q)` THEN
  SUBGOAL_THEN `&0 <= Mb` ASSUME_TAC THENL
   [EXPAND_TAC "Mb" THEN MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..N) (\m. Cx(if prime m then log(&m) else &0) *
                    expi(&m * (&a / &q + beta))) -
    Cx(mobius q / &(phi q)) * vsum(1..N) (\m. expi(&m * beta)) =
    vsum(1..N) (\m. (Cx(if prime m then log(&m) else &0) *
                     expi(&m * &a / &q) - Cx(mobius q / &(phi q))) *
                    expi(&m * beta))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; EXPI_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\m. Cx(if prime m then log(&m) else &0) * expi(&m * &a / &q) -
         Cx(mobius q / &(phi q))`;
    `\m. expi(&m * beta)`; `N:num`; `Mb:real`] ABEL_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    SIMP_TAC[VSUM_SUB; FINITE_NUMSEG; VSUM_CONST_NUMSEG; ADD_SUB] THEN
    REWRITE_TAC[COMPLEX_CMUL; GSYM CX_MUL] THEN EXPAND_TAC "Mb" THEN
    MATCH_MP_TAC PARTIAL_SUM_MAJOR THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_EXPI] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N-1) (\h. &2 * pi * abs beta)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; REAL_MUL_LID;
                EXPI_ADD] THEN
    REWRITE_TAC[COMPLEX_RING `a * b - a:complex = a * (b - Cx(&1))`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_LID] THEN
    REWRITE_TAC[NORM_EXPI_SUB_1_UPPER];
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&N * (&2 * pi * abs beta)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The singular series.                                                      *)
(* ------------------------------------------------------------------------- *)

let sing_term = new_definition
 `sing_term N q = (mobius q / &(phi q)) pow 3 * ramanujan_sum q N`;;

let sing_series = new_definition
 `sing_series N Q = sum(1..Q) (sing_term N)`;;

let REAL_MULTIPLICATIVE_POW = prove
 (`!f k. real_multiplicative f ==> real_multiplicative (\n. f n pow k)`,
  SIMP_TAC[real_multiplicative; REAL_POW_MUL; REAL_POW_ONE]);;

let REAL_MULTIPLICATIVE_SQRT = prove
 (`real_multiplicative (\n. sqrt(&n))`,
  REWRITE_TAC[real_multiplicative; SQRT_1; GSYM REAL_OF_NUM_MUL; SQRT_MUL]);;

let SING_TERM_MULTIPLICATIVE = prove
 (`!N. real_multiplicative (sing_term N)`,
  GEN_TAC THEN
  SUBGOAL_THEN `sing_term N =
                (\q. (mobius q pow 3 * inv(&(phi q)) pow 3) *
                     ramanujan_sum q N)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sing_term; real_div; REAL_POW_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_MULTIPLICATIVE_MUL THEN
  REWRITE_TAC[RAMANUJAN_SUM_MULTIPLICATIVE] THEN
  MATCH_MP_TAC REAL_MULTIPLICATIVE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MULTIPLICATIVE_POW THEN
    REWRITE_TAC[REAL_MULTIPLICATIVE_MOBIUS];
    MATCH_MP_TAC REAL_MULTIPLICATIVE_INV_POW THEN
    REWRITE_TAC[REAL_MULTIPLICATIVE_PHI]]);;

let SING_TERM_PRIME = prove
 (`!N p. prime p
         ==> sing_term N p =
             if p divides N then --inv((&p - &1) pow 2)
             else inv((&p - &1) pow 3)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[sing_term; MOBIUS_PRIME; PHI_PRIME; RAMANUJAN_SUM_PRIME] THEN
  SUBGOAL_THEN `1 <= p /\ ~(&p - &1 = &0)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  COND_CASES_TAC THEN UNDISCH_TAC `~(&p - &1 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let SING_TERM_SQUAREFREE = prove
 (`!N q. ~(sing_term N q = &0) ==> squarefree q`,
  REWRITE_TAC[sing_term; mobius] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_POW_ZERO; ARITH_EQ]);;

let REAL_MULTIPLICATIVE_NPRODUCT = prove
 (`!f t. real_multiplicative f /\ FINITE t /\ (!p. p IN t ==> prime p)
         ==> f(nproduct t (\p. p)) = product t f`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NPRODUCT_CLAUSES; PRODUCT_CLAUSES] THEN
    ASM_MESON_TAC[real_multiplicative];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `t:num->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES; PRODUCT_CLAUSES] THEN
  SUBGOAL_THEN `coprime(p,nproduct t (\q. q))` ASSUME_TAC THENL
   [MATCH_MP_TAC COPRIME_PRIME_NPRODUCT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [real_multiplicative])
    THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let SUM_SUBSETS_MULTIPLICATIVE = prove
 (`!f s. real_multiplicative f /\ FINITE s /\ (!p. p IN s ==> prime p)
         ==> sum {t | t SUBSET s} (\t. f(nproduct t (\p. p))) =
             product s (\p. &1 + f p)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PRODUCT_ADD_EXPAND] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MULTIPLICATIVE_NPRODUCT THEN
  ASM_MESON_TAC[FINITE_SUBSET; SUBSET]);;

let SUM_SQUAREFREE_SUBSETS = prove
 (`!f Q. (!q. ~(f q = &0) ==> squarefree q)
         ==> sum(1..Q) f =
             sum {t | t SUBSET {p | prime p /\ p <= Q} /\
                      nproduct t (\p. p) <= Q}
                 (\t. f(nproduct t (\p. p)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = {p | prime p /\ p <= Q}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN SIMP_TAC[IN_ELIM_THM; FINITE_ATMOST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:num->bool. nproduct t (\p. p)`; `f:num->real`;
                 `{t | t SUBSET P /\ nproduct t (\p:num. p) <= Q}`]
         SUM_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC NPRODUCT_PRIMES_INJ THEN
    ASM_MESON_TAC[FINITE_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `t:num->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN ASM_MESON_TAC[SUBSET; PRIME_IMP_NZ];
    ALL_TAC] THEN
  X_GEN_TAC `q:num` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_NUMSEG; NOT_EXISTS_THM] THEN
  ASM_CASES_TAC `f(q:num) = &0` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `squarefree q` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{p | prime p /\ p divides q}`) THEN
  ASM_SIMP_TAC[SQUAREFREE_EXPAND] THEN
  EXPAND_TAC "P" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  UNDISCH_TAC `1 <= q` THEN UNDISCH_TAC `q <= Q:num` THEN ARITH_TAC);;

let PRODUCT_SUBSET_LE = prove
 (`!f:A->real s t.
        FINITE t /\ s SUBSET t /\ (!x. x IN t ==> &0 <= f x /\ f x <= &1)
        ==> product t f <= product s f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t:A->bool = s UNION (t DIFF s)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:A->bool) /\ FINITE(t DIFF s:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_UNION; SET_RULE `DISJOINT (s:A->bool) (t DIFF s)`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a * b <= a * &1 ==> a * b <= a`) THEN
  SUBGOAL_THEN `&0 <= product s (f:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_LE_1 THEN
  ASM_MESON_TAC[IN_DIFF]);;

let PRODUCT_INV_SQUARE = prove
 (`!m. product(2..SUC m) (\n. &1 - inv(&n pow 2)) =
       (&m + &2) / (&2 * &m + &2)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH]
     THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG] THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 <= SUC(SUC m)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  SUBGOAL_THEN `&0 <= &m` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let SING_PRODUCT_LOWER = prove
 (`!N Q. ODD N
         ==> &1 <= product {p | prime p /\ p <= Q} (\p. &1 + sing_term N p)`,
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
  ASM_SIMP_TAC[PRODUCT_CLAUSES; SING_TERM_PRIME; PRIME_2] THEN
  SUBGOAL_THEN `~(2 divides N)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[DIVIDES_2; GSYM NOT_ODD]; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH `&1 / &2 <= x ==> &1 <= &2 * x`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product P3 (\p. &1 - inv((&p - &1) pow 2))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "P3" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[SING_TERM_PRIME] THEN
    SUBGOAL_THEN `&2 <= &p - &1` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv((&p - &1) pow 2) <= &1 /\ &0 <= inv((&p - &1) pow 2) /\
                  &0 <= inv((&p - &1) pow 3)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC];
      COND_CASES_TAC THEN REAL_ARITH_TAC]] THEN
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
    ASM_SIMP_TAC[ARITH_RULE `~(Q <= 1) ==> SUC(Q - 1) = Q`] THEN
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

let RPOW_NEG_THREE_HALVES = prove
 (`!n. 1 <= n ==> &n rpow (--(&1 / &2 + &1)) = inv(&n * sqrt(&n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_NEG; RPOW_ADD; RPOW_SQRT; REAL_LT_IMP_LE; RPOW_POW;
               REAL_POW_1] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let SUM_INV_THREE_HALVES = prove
 (`!Q. sum(2..Q) (\n. inv(&n * sqrt(&n))) <= &2`,
  GEN_TAC THEN
  MP_TAC(SPECL [`1`; `Q:num`; `&1 / &2`] SUM_RPOW_TAIL) THEN
  ANTS_TAC THENL [REWRITE_TAC[LE_REFL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RPOW_ONE; ARITH_RULE `1 + 1 = 2`] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c = &2 ==> a <= c ==> b <= &2`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RPOW_NEG_THREE_HALVES THEN ASM_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SING_TERM_ABS_PRIME = prove
 (`!N p. prime p ==> abs(sing_term N p) <= &4 / &p pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SING_TERM_PRIME] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv((&p - &1) pow 2) <= &4 / &p pow 2 /\
                inv((&p - &1) pow 3) <= inv((&p - &1) pow 2) /\
                &0 <= inv((&p - &1) pow 3)` MP_TAC THENL
   [ALL_TAC; COND_CASES_TAC THEN REAL_ARITH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((&p / &2) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_POW_DIV; REAL_INV_DIV] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ARITH_TAC]];
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC]);;

let SING_PRODUCT_RANKIN = prove
 (`!N Q. product {p | prime p /\ p <= Q}
                 (\p. &1 + abs(sing_term N p) * sqrt(&p)) <= exp(&8)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product {p | prime p /\ p <= Q}
                      (\p. exp(&4 * inv(&p * sqrt(&p))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN
    REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < sqrt(&p)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 + &4 * inv(&p * sqrt(&p))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&4 / &p pow 2 * sqrt(&p)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[SING_TERM_ABS_PRIME; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        ABBREV_TAC `s = sqrt(&p)` THEN
        SUBGOAL_THEN `&p = s pow 2` SUBST1_TAC THENL
         [EXPAND_TAC "s" THEN SIMP_TAC[SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
        SUBGOAL_THEN `~(s = &0)` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
      REWRITE_TAC[REAL_EXP_LE_X]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p. &4 * inv(&p * sqrt(&p))`; `{p | prime p /\ p <= Q}`]
         REAL_EXP_SUM) THEN
  REWRITE_TAC[FINITE_ATMOST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; SUM_LMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> &4 * x <= &8`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2..Q) (\n. inv(&n * sqrt(&n)))` THEN
  REWRITE_TAC[SUM_INV_THREE_HALVES] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[PRIME_GE_2];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS]]);;

let SING_SERIES_TAIL = prove
 (`!N Q. 1 <= Q
         ==> abs(sing_series N Q -
                 product {p | prime p /\ p <= Q} (\p. &1 + sing_term N p))
             <= exp(&8) / sqrt(&Q)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = {p | prime p /\ p <= Q}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN SIMP_TAC[IN_ELIM_THM; FINITE_ATMOST];
    ALL_TAC] THEN
  REWRITE_TAC[sing_series] THEN
  MP_TAC(ISPECL [`sing_term N`; `Q:num`] SUM_SQUAREFREE_SUBSETS) THEN
  REWRITE_TAC[SING_TERM_SQUAREFREE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`sing_term N`; `P:num->bool`] SUM_SUBSETS_MULTIPLICATIVE) THEN
  ASM_REWRITE_TAC[SING_TERM_MULTIPLICATIVE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`{t | t SUBSET (P:num->bool)}`;
                 `\t. nproduct t (\p:num. p) <= Q`;
                 `\t. sing_term N (nproduct t (\p:num. p))`;
                 `\t. sing_term N (nproduct t (\p:num. p))`] SUM_CASES) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; COND_ID; IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs b <= e ==> abs(a - (a + b)) <= e`) THEN
  SUBGOAL_THEN `&0 < sqrt(&Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {t | t SUBSET P /\ ~(nproduct t (\p:num. p) <= Q)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET
     THEN EXISTS_TAC `{t | t SUBSET (P:num->bool)}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET P /\ ~(nproduct t (\p:num. p) <= Q)}
                  (\t. abs(sing_term N (nproduct t (\p. p))) *
                       sqrt(&(nproduct t (\p. p)))) / sqrt(&Q)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_ABS_LE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `t:num->bool` THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM real_div; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET P}
                  (\t. abs(sing_term N (nproduct t (\p. p))) *
                       sqrt(&(nproduct t (\p. p))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. abs(sing_term N n) * sqrt(&n)`; `P:num->bool`]
         SUM_SUBSETS_MULTIPLICATIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_MULTIPLICATIVE_MUL THEN
    REWRITE_TAC[REAL_MULTIPLICATIVE_SQRT] THEN
    MATCH_MP_TAC REAL_MULTIPLICATIVE_ABS THEN
    REWRITE_TAC[ETA_AX; SING_TERM_MULTIPLICATIVE];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o BETA_RULE) THEN EXPAND_TAC "P" THEN
  REWRITE_TAC[SING_PRODUCT_RANKIN]);;

let SING_SERIES_LOWER = prove
 (`!N Q. ODD N /\ 1 <= Q ==> &1 - exp(&8) / sqrt(&Q) <= sing_series N Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `Q:num`] SING_SERIES_TAIL) THEN
  MP_TAC(SPECL [`N:num`; `Q:num`] SING_PRODUCT_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`product {p | prime p /\ p <= Q} (\p. &1 + sing_term N p)`,
           `x:real`) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The circle identity for vinogradov_rep3; counting m1 + m2 + m3 = N.       *)
(* ------------------------------------------------------------------------- *)

let primexp = new_definition
 `primexp N x =
  vsum(1..N) (\m. Cx(if prime m then log(&m) else &0) * expi(&m * x))`;;

let unitexp = new_definition
 `unitexp N x = vsum(1..N) (\m. expi(&m * x))`;;

let vinogradov_rep3 = new_definition
 `vinogradov_rep3 N =
  sum(1..N) (\m1. sum(1..N) (\m2. sum(1..N) (\m3.
    if m1 + m2 + m3 = N
    then (if prime m1 then log(&m1) else &0) *
         (if prime m2 then log(&m2) else &0) *
         (if prime m3 then log(&m3) else &0)
    else &0)))`;;

let PRIMEXP_INTEGER_ADD = prove
 (`!N x n. integer n ==> primexp N (x + n) = primexp N x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[primexp] THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  ASM_SIMP_TAC[EXPI_INTEGER_ADD; INTEGER_CLOSED]);;

let UNITEXP_INTEGER_ADD = prove
 (`!N x n. integer n ==> unitexp N (x + n) = unitexp N x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[unitexp] THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  ASM_SIMP_TAC[EXPI_INTEGER_ADD; INTEGER_CLOSED]);;

let VINOGRADOV_REP3_POS = prove
 (`!N. &0 < vinogradov_rep3 N
       ==> ?p1 p2 p3. prime p1 /\ prime p2 /\ prime p3 /\ p1 + p2 + p3 = N`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[vinogradov_rep3] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `m1:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `m2:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `m3:num` THEN STRIP_TAC THEN
  BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m1:num`; `m2:num`; `m3:num`]) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]);;

let INNER_COUNT = prove
 (`!a N. sum(1..N) (\m. if a + m = N then &1 else &0) =
         if a < N then &1 else &0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..N) (\m. if m = N - a then &1 else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC]);;

let MIDDLE_COUNT = prove
 (`!a N. sum(1..N) (\m. if a + m < N then &1 else &0) = &((N - 1) - a)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\m:num. a + m < N`; `1..N`;
    `\m:num. &1`] SUM_RESTRICT_SET) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `{m | m IN 1..N /\ a + m < N} = 1..(N - 1) - a`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; REAL_MUL_RID] THEN AP_TERM_TAC THEN
    ARITH_TAC]);;

let SUM_PRED_NUM = prove
 (`!n. sum(0..n) (\i. &(i - 1)) = &n * (&n - &1) / &2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`; GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

let TRIPLE_COUNT = prove
 (`!N. 1 <= N
       ==> sum(1..N) (\m1. sum(1..N) (\m2. sum(1..N) (\m3.
             if m1 + m2 + m3 = N then &1 else &0))) =
           (&N - &1) * (&N - &2) / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ADD_ASSOC; INNER_COUNT] THEN
  REWRITE_TAC[MIDDLE_COUNT] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(0..N - 1) (\i. &(i - 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_PRED_NUM] THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REAL_ARITH_TAC]);;

let CIRCLE_PRIMEXP = prove
 (`!N M. 3 * N < M
         ==> vsum {k | k < M}
               (\k. primexp N (&k / &M) pow 3 * expi(--(&N * (&k / &M)))) =
             Cx(&M * vinogradov_rep3 N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. if prime m then log(&m) else &0`; `N:num`; `M:num`;
                 `&0`] GENERAL_CIRCLE) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; GSYM primexp; GSYM vinogradov_rep3]);;

let UNITEXP_ALT = prove
 (`!N x. vsum(1..N) (\m. Cx(&1) * expi(&m * x)) = unitexp N x`,
  REWRITE_TAC[unitexp; COMPLEX_MUL_LID]);;

let CIRCLE_UNITEXP = prove
 (`!N M t. 1 <= N /\ 3 * N < M
           ==> vsum {k | k < M}
                 (\k. unitexp N (&k / &M - t) pow 3 *
                      expi(--(&N * (&k / &M - t)))) =
               Cx(&M * (&N - &1) * (&N - &2) / &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m:num. &1`; `N:num`; `M:num`;
    `--t:real`] GENERAL_CIRCLE) THEN
  ASM_REWRITE_TAC[GSYM real_sub; UNITEXP_ALT; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[TRIPLE_COUNT]);;

let PARSEVAL_UNITEXP = prove
 (`!N M t. N < M
           ==> sum {k | k < M} (\k. norm(unitexp N (&k / &M - t)) pow 2) =
               &M * &N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m:num. &1`; `N:num`; `M:num`;
    `--t:real`] PARSEVAL_EXPSUM) THEN
  ASM_REWRITE_TAC[GSYM real_sub; UNITEXP_ALT] THEN
  REWRITE_TAC[REAL_POW_ONE; SUM_CONST_NUMSEG; REAL_MUL_RID] THEN
  REWRITE_TAC[ARITH_RULE `(N + 1) - 1 = N`]);;

let PARSEVAL_PRIMEXP = prove
 (`!N M. N < M
         ==> sum {k | k < M} (\k. norm(primexp N (&k / &M)) pow 2) =
             &M * sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m. if prime m then log(&m) else &0`; `N:num`; `M:num`;
                 `&0`] PARSEVAL_EXPSUM) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; GSYM primexp]);;

(* ------------------------------------------------------------------------- *)
(* Major arcs and their disjointness.                                        *)
(* ------------------------------------------------------------------------- *)

let circ_arc = new_definition
 `circ_arc M Kw q a = {k | k < M /\ ndist(&k / &M - &a / &q) <= inv(&Kw)}`;;

let circ_major = new_definition
 `circ_major M Kw Q =
  UNIONS (IMAGE (\q. UNIONS (IMAGE (\a. circ_arc M Kw q a)
                                   {a | a < q /\ coprime(a,q)}))
                (1..Q))`;;

let NDIST_ADD_LE = prove
 (`!x y. ndist(x + y) <= ndist x + ndist y`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `x:real` NDIST_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `y:real` NDIST_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`x + y:real`; `n + m:real`] NDIST_LE_ABS) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC);;

let NDIST_SUB_LE = prove
 (`!x y z. ndist(x - z) <= ndist(x - y) + ndist(y - z)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `x - z = (x - y) + (y - z:real)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; REWRITE_TAC[NDIST_ADD_LE]]);;

let NDIST_RATIONAL_LOWER = prove
 (`!j n. integer j /\ 1 <= n /\ ~integer(j / &n) ==> inv(&n) <= ndist(j / &n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `j / &n` NDIST_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `j / &n - m = (j - m * &n) / &n` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN DISCH_TAC THEN
  UNDISCH_TAC `~integer(j / &n)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `j / &n = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  UNDISCH_TAC `j - m * &n = &0` THEN UNDISCH_TAC `&0 < &n` THEN
  CONV_TAC REAL_FIELD);;

let COPRIME_FRACTION_EQ = prove
 (`!a q a' q'. coprime(a,q) /\ coprime(a',q') /\ ~(q = 0) /\
               a * q' = a' * q
               ==> q = q' /\ a = a'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `q:num = q'` SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`a:num`; `q:num`; `a':num`; `q':num`] (NUMBER_RULE
       `!a q a' q'. coprime(a,q) /\ a * q' = a' * q ==> q divides q'`));
      MP_TAC(SPECL [`a:num`; `q:num`; `a':num`; `q':num`] (NUMBER_RULE
       `!a q a' q'. coprime(a',q') /\ a * q' = a' * q ==> q' divides q`))] THEN
     ASM_REWRITE_TAC[];
    ASM_MESON_TAC[EQ_MULT_RCANCEL]]);;

let FAREY_SEPARATION = prove
 (`!q a q' a'. 1 <= q /\ 1 <= q' /\ a < q /\ a' < q' /\
               coprime(a,q) /\ coprime(a',q') /\ ~(q = q' /\ a = a')
               ==> inv(&q * &q') <= ndist(&a / &q - &a' / &q')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &q /\ &0 < &q'` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&a / &q - &a' / &q' = (&a * &q' - &a' * &q) / (&q * &q')`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &q` THEN UNDISCH_TAC `&0 < &q'` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL] THEN MATCH_MP_TAC NDIST_RATIONAL_LOWER THEN
  SIMP_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= n ==> 1 <= n`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&a * &q' - &a' * &q) / (&q * &q') = &a / &q - &a' / &q'`
  SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < &q` THEN UNDISCH_TAC `&0 < &q'` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `&a / &q - &a' / &q' = &0` THENL
   [ALL_TAC;
    MP_TAC(SPEC `&a / &q - &a' / &q'` REAL_ABS_INTEGER_LEMMA) THEN
    ASM_REWRITE_TAC[REAL_NOT_LE] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x < &1 /\ &0 <= y /\ y < &1 ==> abs(x - y) < &1`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_LDIV_EQ; REAL_MUL_LID;
                 REAL_OF_NUM_LT]] THEN
  SUBGOAL_THEN `a * q' = a' * q:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `&a / &q - &a' / &q' = &0` THEN
    UNDISCH_TAC `&0 < &q` THEN UNDISCH_TAC `&0 < &q'` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  UNDISCH_TAC `~(q:num = q' /\ a:num = a')` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC COPRIME_FRACTION_EQ THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let CIRC_ARC_DISJOINT = prove
 (`!M Kw Q q a q' a' k.
        2 * Q EXP 2 < Kw /\ 1 <= q /\ q <= Q /\ 1 <= q' /\ q' <= Q /\
        a < q /\ a' < q' /\ coprime(a,q) /\ coprime(a',q') /\
        k IN circ_arc M Kw q a /\ k IN circ_arc M Kw q' a'
        ==> q = q' /\ a = a'`,
  REWRITE_TAC[circ_arc; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `q:num = q' /\ a:num = a'` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`q:num`; `a:num`; `q':num`; `a':num`] FAREY_SEPARATION) THEN
  ASM_REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 * inv(&Kw)` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`&a / &q`; `&k / &M`; `&a' / &q'`] NDIST_SUB_LE) THEN
    MP_TAC(SPEC `&k / &M - &a / &q` NDIST_NEG) THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * inv(&Kw) = inv(&Kw / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_DIV; real_div]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &2`] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `2 * Q EXP 2` THEN
  ASM_REWRITE_TAC[EXP_2] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `x * 2 = 2 * x`] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]);;

let VSUM_DISJOINT_FAMILY = prove
 (`!f:B->complex t:A->B->bool s.
        FINITE s /\ (!i. i IN s ==> FINITE(t i)) /\
        (!i j x. i IN s /\ j IN s /\ x IN t i /\ x IN t j ==> i = j)
        ==> vsum (UNIONS (IMAGE t s)) f = vsum s (\i. vsum (t i) f)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_UNIONS_NONZERO o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE_NONZERO o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN
    STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ_0 THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let SUM_DISJOINT_FAMILY = prove
 (`!f:B->real t:A->B->bool s.
        FINITE s /\ (!i. i IN s ==> FINITE(t i)) /\
        (!i j x. i IN s /\ j IN s /\ x IN t i /\ x IN t j ==> i = j)
        ==> sum (UNIONS (IMAGE t s)) f = sum s (\i. sum (t i) f)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNIONS_NONZERO o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN
    STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let CIRC_ARC_FINITE = prove
 (`!M Kw q a. FINITE(circ_arc M Kw q a)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{k:num | k < M}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[circ_arc; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let FINITE_COPRIME_RESIDUES = prove
 (`!q. FINITE {a | a < q /\ coprime(a,q)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET
    THEN EXISTS_TAC `{a:num | a < q}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let CIRC_MAJOR_VSUM = prove
 (`!f:num->complex M Kw Q. 2 * Q EXP 2 < Kw
             ==> vsum (circ_major M Kw Q) f =
                 vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
                                      (\a. vsum (circ_arc M Kw q a) f))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[circ_major] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_DISJOINT_FAMILY o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[FINITE_UNIONS] THEN
      SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; CIRC_ARC_FINITE;
               FINITE_COPRIME_RESIDUES];
      REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[CIRC_ARC_DISJOINT]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC VSUM_DISJOINT_FAMILY THEN
  REWRITE_TAC[CIRC_ARC_FINITE; FINITE_COPRIME_RESIDUES; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[CIRC_ARC_DISJOINT]);;

let CIRC_MAJOR_SUM = prove
 (`!f M Kw Q. 2 * Q EXP 2 < Kw
             ==> sum (circ_major M Kw Q) f =
                 sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                                    (\a. sum (circ_arc M Kw q a) f))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[circ_major] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_DISJOINT_FAMILY o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[FINITE_UNIONS] THEN
      SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; CIRC_ARC_FINITE;
               FINITE_COPRIME_RESIDUES];
      REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[CIRC_ARC_DISJOINT]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_DISJOINT_FAMILY THEN
  REWRITE_TAC[CIRC_ARC_FINITE; FINITE_COPRIME_RESIDUES; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[CIRC_ARC_DISJOINT]);;

let CIRC_MAJOR_SUBSET = prove
 (`!M Kw Q. circ_major M Kw Q SUBSET {k | k < M}`,
  REWRITE_TAC[circ_major; circ_arc; SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let CIRC_MAJOR_FINITE = prove
 (`!M Kw Q. FINITE(circ_major M Kw Q)`,
  MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG_LT; CIRC_MAJOR_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* The major arc contribution.                                               *)
(* ------------------------------------------------------------------------- *)

let ARC_UNITEXP_BOUND = prove
 (`!N M Kw q a k. 1 <= Kw /\ k < M /\ ~(k IN circ_arc M Kw q a)
                 ==> norm(unitexp N (&k / &M - &a / &q)) <= &2 * &Kw`,
  REWRITE_TAC[circ_arc; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(&Kw) <= ndist(&k / &M - &a / &q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_NOT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Kw` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * emin (&N) (&k / &M - &a / &q)` THEN
  REWRITE_TAC[unitexp; VSUM_EXPI_GEOM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC EMIN_LE_INV THEN ASM_SIMP_TAC[REAL_LT_INV]);;

let ARC_MAIN_TERM = prove
 (`!N M Kw q a. 1 <= N /\ 3 * N < M /\ 1 <= Kw
               ==> norm(vsum (circ_arc M Kw q a)
                          (\k. unitexp N (&k / &M - &a / &q) pow 3 *
                               expi(--(&N * (&k / &M - &a / &q)))) -
                        Cx(&M * (&N - &1) * (&N - &2) / &2))
                   <= &2 * &Kw * &M * &N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `&a / &q`] CIRCLE_UNITEXP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `circ_arc M Kw q a SUBSET {k | k < M}` ASSUME_TAC THENL
   [REWRITE_TAC[circ_arc; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN
  ASM_SIMP_TAC[GSYM VSUM_DIFF; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum ({k | k < M} DIFF circ_arc M Kw q a)
                  (\k. &2 * &Kw * norm(unitexp N (&k / &M - &a / &q)) pow 2)`
                    THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG_LT; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_RID;
                COMPLEX_NORM_POW] THEN
    REWRITE_TAC[REAL_RING `(x:real) pow 3 = x * x pow 2`; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC ARC_UNITEXP_BOUND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {k | k < M}
                  (\k. &2 * &Kw * norm(unitexp N (&k / &M - &a / &q)) pow 2)`
                    THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL
      THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    REWRITE_TAC[SUM_LMUL] THEN
    ASM_SIMP_TAC[PARSEVAL_UNITEXP; ARITH_RULE `3 * N < M ==> N < M`] THEN
    REAL_ARITH_TAC]);;

let RAMANUJAN_SUM_NEG_VSUM = prove
 (`!q n. 1 <= q
         ==> vsum {a | a < q /\ coprime(a,q)} (\a. expi(--(&n * (&a / &q)))) =
             Cx(ramanujan_sum q n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `n:num`] RAMANUJAN_FORMULA) THEN
  ASM_REWRITE_TAC[GSYM ramanujan_sum] THEN
  DISCH_THEN(MP_TAC o AP_TERM `cnj`) THEN
  SIMP_TAC[CNJ_VSUM; FINITE_COPRIME_RESIDUES; CNJ_EXPI; CNJ_CX] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC VSUM_EQ THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

let MOBIUS_PHI_POW_BOUND = prove
 (`!q k. 1 <= q /\ 2 <= k
         ==> abs(mobius q / &(phi q)) pow k * &(phi q) <= inv(&(phi q))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &(phi q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_LE; PHI_LOWERBOUND_1_STRONG]; ALL_TAC] THEN
  ABBREV_TAC `f = &(phi q)` THEN
  SUBGOAL_THEN `abs(mobius q / f) <= inv f /\ &0 <= abs(mobius q / f)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 <= f ==> abs f = f`; real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_MOBIUS] THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv f /\ inv f <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INV_LE_1] THEN MATCH_MP_TAC REAL_LE_INV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(f:real) pow k * f` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(f:real) pow 2 * f` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `~(f = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

let MAJOR_MAIN_Q = prove
 (`!N M Kw q. 1 <= N /\ 3 * N < M /\ 1 <= Kw /\ 1 <= q
             ==> norm(vsum {a | a < q /\ coprime(a,q)}
                        (\a. vsum (circ_arc M Kw q a)
                               (\k. (Cx(mobius q / &(phi q)) *
                                     unitexp N (&k / &M - &a / &q)) pow 3 *
                                    expi(--(&N * &k / &M)))) -
                      Cx((&M * (&N - &1) * (&N - &2) / &2) * sing_term N q))
                 <= &2 * &Kw * &M * &N * inv(&(phi q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `3`] MOBIUS_PHI_POW_BOUND) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[sing_term] THEN
  ABBREV_TAC `c = mobius q / &(phi q)` THEN
  ABBREV_TAC `Tm = &M * (&N - &1) * (&N - &2) / &2` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a k. (Cx c * unitexp N (&k / &M - &a / &q)) pow 3 *
          expi(--(&N * &k / &M)) =
          (Cx(c pow 3) * expi(--(&N * &a / &q))) *
          (unitexp N (&k / &M - &a / &q) pow 3 *
           expi(--(&N * (&k / &M - &a / &q))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `--(&N * &k / &M) =
                  --(&N * &a / &q) + --(&N * (&k / &M - &a / &q))`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[EXPI_ADD; COMPLEX_POW_MUL; CX_POW] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; CIRC_ARC_FINITE] THEN
  SUBGOAL_THEN
   `Cx(Tm * c pow 3 * ramanujan_sum q N) =
    vsum {a | a < q /\ coprime(a,q)}
         (\a. (Cx(c pow 3) * expi(--(&N * &a / &q))) * Cx Tm)`
  SUBST1_TAC THENL
   [SIMP_TAC[VSUM_COMPLEX_RMUL; VSUM_COMPLEX_LMUL;
     FINITE_COPRIME_RESIDUES] THEN
    ASM_SIMP_TAC[RAMANUJAN_SUM_NEG_VSUM; GSYM CX_MUL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_COPRIME_RESIDUES] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {a | a < q /\ coprime(a,q)}
                  (\a. abs c pow 3 * (&2 * &Kw * &M * &N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_EXPI; REAL_MUL_RID;
                REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    EXPAND_TAC "Tm" THEN MATCH_MP_TAC ARC_MAIN_TERM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES] THEN
  SUBGOAL_THEN `CARD {a | a < q /\ coprime(a,q)} = phi q` SUBST1_TAC THENL
   [REWRITE_TAC[PHI_ALT] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * &Kw * &M * &N) * (abs c pow 3 * &(phi q))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &Kw * &M * &N * inv(&(phi q)) =
                (&2 * &Kw * &M * &N) * inv(&(phi q))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN REWRITE_TAC[REAL_POS]);;

let MAJOR_MAIN = prove
 (`!N M Kw Q. 1 <= N /\ 3 * N < M /\ 1 <= Kw
             ==> norm(vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
                        (\a. vsum (circ_arc M Kw q a)
                               (\k. (Cx(mobius q / &(phi q)) *
                                     unitexp N (&k / &M - &a / &q)) pow 3 *
                                    expi(--(&N * &k / &M))))) -
                      Cx((&M * (&N - &1) * (&N - &2) / &2) *
                         sing_series N Q))
                 <= &2 * &Kw * &M * &N * sum(1..Q) (\q. inv(&(phi q)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sing_series; GSYM SUM_LMUL; GSYM VSUM_CX] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC MAJOR_MAIN_Q THEN ASM_REWRITE_TAC[]);;

let CUBE_DIFF_BOUND = prove
 (`!x y:complex. norm(x pow 3 - y pow 3) <=
                 norm(x - y) * &2 * (norm x pow 2 + norm y pow 2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(x:complex) pow 3 - y pow 3 = (x - y) * (x pow 2 + x * y + y pow 2)`
  SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((x:complex) pow 2) + norm(x * y) + norm((y:complex) pow 2)`
  THEN
  REWRITE_TAC[NORM_ARITH
   `norm(a + b + c:complex) <= norm a + norm b + norm c`] THEN
  REWRITE_TAC[COMPLEX_NORM_POW; COMPLEX_NORM_MUL] THEN
  MP_TAC(SPEC `norm(x:complex) - norm(y:complex)` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `norm(x:complex)` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `norm(y:complex)` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_RING `(a - b:real) pow 2 = a pow 2 + b pow 2 - &2 * a * b`]
    THEN
  REAL_ARITH_TAC);;

let TRIPLE_NORM_LE = prove
 (`!(s:num->bool) (A:num->num->bool) (t:num->num->num->bool)
    (f:num->num->num->complex) g.
        FINITE s /\ (!q. FINITE(A q)) /\ (!q a. FINITE(t q a))
        ==> norm(vsum s (\q. vsum (A q) (\a. vsum (t q a) (f q a))) -
                 vsum s (\q. vsum (A q) (\a. vsum (t q a) (g q a)))) <=
            sum s (\q. sum (A q) (\a. sum (t q a)
                                         (\k. norm(f q a k - g q a k))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM VSUM_SUB] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN ASM_SIMP_TAC[REAL_LE_REFL]);;

let MAJOR_APPROX = prove
 (`!N M Kw Q E.
     2 * Q EXP 2 < Kw /\ N < M /\ &0 <= E /\
     (!q a k. 1 <= q /\ q <= Q /\ a < q /\ coprime(a,q) /\
              k IN circ_arc M Kw q a
              ==> norm(primexp N (&k / &M) -
                       Cx(mobius q / &(phi q)) *
                       unitexp N (&k / &M - &a / &q)) <= E)
     ==> norm(vsum (circ_major M Kw Q)
                (\k. primexp N (&k / &M) pow 3 * expi(--(&N * &k / &M))) -
              vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
                (\a. vsum (circ_arc M Kw q a)
                       (\k. (Cx(mobius q / &(phi q)) *
                             unitexp N (&k / &M - &a / &q)) pow 3 *
                            expi(--(&N * &k / &M))))))
         <= &2 * E *
            (&M * sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2) +
             &M * &N * sum(1..Q) (\q. inv(&(phi q))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CIRC_MAJOR_VSUM] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) TRIPLE_NORM_LE o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_COPRIME_RESIDUES; CIRC_ARC_FINITE] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)} (\a.
      sum (circ_arc M Kw q a) (\k.
        &2 * E * (norm(primexp N (&k / &M)) pow 2 +
                  norm(Cx(mobius q / &(phi q)) *
                       unitexp N (&k / &M - &a / &q)) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_COPRIME_RESIDUES; IN_ELIM_THM] THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[CIRC_ARC_FINITE] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB] THEN
    GEN_REWRITE_TAC LAND_CONV [COMPLEX_NORM_MUL] THEN
    REWRITE_TAC[NORM_EXPI; REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(primexp N (&k / &M) -
                     Cx(mobius q / &(phi q)) *
                     unitexp N (&k / &M - &a / &q)) * &2 *
                (norm(primexp N (&k / &M)) pow 2 +
                 norm(Cx(mobius q / &(phi q)) *
                      unitexp N (&k / &M - &a / &q)) pow 2)` THEN
    REWRITE_TAC[CUBE_DIFF_BOUND] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * &2 * b = (a * &2) * b`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * a * b = (a * &2) * b`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG; FINITE_COPRIME_RESIDUES;
           CIRC_ARC_FINITE] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM CIRC_MAJOR_SUM] THEN
    MP_TAC(SPECL [`N:num`; `M:num`] PARSEVAL_PRIMEXP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; CIRC_MAJOR_SUBSET; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {a | a < q /\ coprime(a,q)}
                  (\a. abs(mobius q / &(phi q)) pow 2 * (&M * &N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_POW_MUL; SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC(SPECL [`N:num`; `M:num`; `&a / &q`] PARSEVAL_UNITEXP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; REAL_LE_POW_2] THEN
    REWRITE_TAC[circ_arc; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES] THEN
  SUBGOAL_THEN `CARD {a | a < q /\ coprime(a,q)} = phi q` SUBST1_TAC THENL
   [REWRITE_TAC[PHI_ALT] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `2`] MOBIUS_PHI_POW_BOUND) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&M * &N) * (abs(mobius q / &(phi q)) pow 2 * &(phi q))` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&M * &N * inv(&(phi q)) = (&M * &N) * inv(&(phi q))`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]);;

let ARC_APPROX = prove
 (`!N M Kw q a k D.
     1 <= q /\ coprime(a,q) /\ 1 <= Kw /\ &0 <= D /\
     (!h b. h <= N /\ b < q /\ coprime(b,q)
            ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                        (\p. log(&p)) - &h / &(phi q)) <= D) /\
     k IN circ_arc M Kw q a
     ==> norm(primexp N (&k / &M) -
              Cx(mobius q / &(phi q)) * unitexp N (&k / &M - &a / &q))
         <= (&(phi q) * D + log(&q)) * (&1 + &2 * pi * &N / &Kw)`,
  REWRITE_TAC[circ_arc; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&k / &M - &a / &q` NDIST_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `beta = &k / &M - &a / &q - n` THEN
  SUBGOAL_THEN `abs beta <= inv(&Kw)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `unitexp N (&k / &M - &a / &q) = unitexp N beta`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&k / &M - &a / &q = beta + n` SUBST1_TAC THENL
     [EXPAND_TAC "beta" THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[UNITEXP_INTEGER_ADD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `primexp N (&k / &M) = primexp N (&a / &q + beta)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&k / &M = (&a / &q + beta) + n` SUBST1_TAC THENL
     [EXPAND_TAC "beta" THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[PRIMEXP_INTEGER_ADD]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&(phi q) * D + log(&q)) * (&1 + &2 * pi * &N * abs beta)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[primexp; unitexp] THEN MATCH_MP_TAC MAJOR_ARC_APPROX THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_LADD; real_div] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
          [SIMP_TAC[REAL_POS; PI_POS_LE]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[]);;

let MAJOR_TOTAL = prove
 (`!N M Kw Q D.
     1 <= N /\ 3 * N < M /\ 1 <= Kw /\ 1 <= Q /\ 2 * Q EXP 2 < Kw /\ &0 <= D /\
     (!q h b. 1 <= q /\ q <= Q /\ h <= N /\ b < q /\ coprime(b,q)
              ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                          (\p. log(&p)) - &h / &(phi q)) <= D)
     ==> norm(vsum (circ_major M Kw Q)
                (\k. primexp N (&k / &M) pow 3 * expi(--(&N * &k / &M))) -
              Cx((&M * (&N - &1) * (&N - &2) / &2) * sing_series N Q))
         <= &2 * &Kw * &M * &N * sum(1..Q) (\q. inv(&(phi q))) +
            &2 * ((&Q * D + log(&Q)) * (&1 + &2 * pi * &N / &Kw)) *
            (&M * sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2) +
             &M * &N * sum(1..Q) (\q. inv(&(phi q))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &1 + &2 * pi * &N / &Kw` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[PI_POS_LE; REAL_LE_DIV; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`] MAJOR_MAIN) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`;
                `(&Q * D + log(&Q)) * (&1 + &2 * pi * &N / &Kw)`]
         MAJOR_APPROX) THEN
  ASM_SIMP_TAC[ARITH_RULE `3 * N < M ==> N < M`] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `a:num`; `k:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(phi q) * D + log(&q)) * (&1 + &2 * pi * &N / &Kw)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ARC_APPROX THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q:num` THEN
      ASM_REWRITE_TAC[PHI_LIMIT];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    MATCH_ACCEPT_TAC(NORM_ARITH
     `!a b c:complex e1 e2. norm(a - b) <= e1 ==> norm(b - c) <= e2
                            ==> norm(a - c) <= e2 + e1`)]);;

(* ------------------------------------------------------------------------- *)
(* Minor arcs; the estimate for one large N.                                 *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT_PRIME = prove
 (`!p. prime p ==> mangoldt p = log(&p)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`p:num`; `1`] MANGOLDT_PRIMEPOW) THEN
  ASM_REWRITE_TAC[EXP_1; LE_REFL]);;

let PRIMEXP_MANGOLDT = prove
 (`!N x. 1 <= N
         ==> norm(primexp N x) <=
             norm(vsum(1..N) (\n. Cx(mangoldt n) * expi(&n * x))) +
             sqrt(&N) * log(&N) pow 2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a - b:complex) <= e ==> norm a <= norm b + e`) THEN
  REWRITE_TAC[primexp] THEN SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; GSYM CX_SUB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..N) (\m. mangoldt m - (if prime m then log(&m) else &0))` THEN
  ASM_SIMP_TAC[PRIME_POWER_SUM_BOUND] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_EXPI; REAL_MUL_RID] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MANGOLDT_PRIME] THENL
   [REAL_ARITH_TAC;
    MP_TAC(SPEC `m:num` MANGOLDT_POS_LE) THEN REAL_ARITH_TAC]);;

let MINOR_DIRICHLET = prove
 (`!M Kw Q k. 1 <= Kw /\ k < M /\ ~(k IN circ_major M Kw Q)
             ==> ?a q. Q < q /\ q <= Kw /\ coprime(a,q) /\
                       abs(&k / &M - &a / &q) <= inv(&q pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&k / &M`; `Kw:num`] DIRICHLET_APPROX) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `q:num`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `q:num`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &q /\ &0 < &Kw` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(&k / &M - &a / &q) < inv(&Kw) * inv(&q)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&k / &M - &a / &q = (&q * &k / &M - &a) * inv(&q)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&Kw) <= inv(&q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(k IN circ_major M Kw Q)` THEN
    REWRITE_TAC[circ_major; UNIONS_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `a MOD q` THEN
    SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; COPRIME_LMOD; circ_arc; IN_ELIM_THM] THEN
    SUBGOAL_THEN `&k / &M - &(a MOD q) / &q =
                  (&k / &M - &a / &q) + &(a DIV q)` SUBST1_TAC THENL
     [MP_TAC(SPECL [`a:num`; `q:num`] DIVISION) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `real_of_num` o CONJUNCT1) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
      UNDISCH_TAC `&0 < &q` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SIMP_TAC[NDIST_INTEGER_ADD; INTEGER_CLOSED] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(&k / &M - &a / &q)` THEN REWRITE_TAC[NDIST_LE] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&Kw) * inv(&q)` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_INV] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&Kw) * inv(&q)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_INV]]);;

let VLB_SIMPLE = prove
 (`!n Qr qr X Lb l0 l1 l2 l3 l4.
     &1 <= Lb /\ &0 <= l0 /\ l0 <= Lb /\ &0 <= l1 /\ l1 <= Lb /\
     &0 <= l2 /\ l2 <= Lb /\ &0 <= l3 /\ l3 <= Lb /\ &0 <= l4 /\ l4 <= Lb /\
     &0 <= Qr /\ &0 < qr /\ &1 <= X /\ X <= n /\ n / qr <= X /\
     n / Qr pow 2 <= X /\ qr <= X /\ Qr pow 2 <= X /\
     Qr pow 2 * Qr pow 2 <= X
     ==> &18 * Qr pow 2 +
         &1 * (&4 * l0) *
         (&14 * n / qr * (&1 + l1) + &8 * (Qr pow 2 + qr) * (&1 + l2)) +
         l0 * &2 *
         (&14 * n / qr * (&1 + l1) +
          &8 * (Qr pow 2 * Qr pow 2 + qr) * (&1 + l2)) +
         (&2 * l0 + &1) *
         sqrt(&504 * n * l3 * (&1 + l4) pow 3 * (&1 + l2) *
              (n / qr + n / Qr pow 2 + n / Qr pow 2 + qr)) +
         sqrt n * l0 pow 2
         <= &1000 * Lb pow 4 * sqrt(n * X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= n / qr /\ &0 <= n / Qr pow 2 /\ &0 <= Qr pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `X <= sqrt(n * X) /\ sqrt n <= sqrt(n * X)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LE THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S = sqrt(n * X)` THEN
  SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= Lb pow 2 /\ Lb pow 2 <= Lb pow 4 /\ &1 <= Lb pow 4`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN
    TRY(MATCH_MP_TAC REAL_POW_MONO) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= &18 * X /\ b <= &240 * (Lb pow 2 * X) /\
    c <= &120 * (Lb pow 2 * X) /\ d <= &540 * p /\
    e <= p /\ X <= p /\ Lb pow 2 * X <= p /\ &0 <= p
    ==> a + b + c + d + e <= &1000 * p`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * (&4 * Lb) *
                (&14 * X * (&2 * Lb) + &8 * (&2 * X) * (&2 * Lb))` THEN
    CONJ_TAC THENL
     [REPEAT(FIRST [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC;
                   MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC]) THEN
     REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_POW_LE]) THEN
     ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Lb * &2 *
                (&14 * X * (&2 * Lb) + &8 * (&2 * X) * (&2 * Lb))` THEN
    CONJ_TAC THENL
     [REPEAT(FIRST [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC;
                   MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC]) THEN
     REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_POW_LE]) THEN
     ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&3 * Lb) * (&180 * Lb pow 3 * S)` THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN
      REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC;
                    MATCH_MP_TAC REAL_POW_LE]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &180 * Lb pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt((&180 * Lb pow 3) pow 2 * (n * X))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      GEN_REWRITE_TAC LAND_CONV [SQRT_MUL] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_REFL; REAL_MUL_ASSOC]] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&504 * n * Lb * (&2 * Lb) pow 3 * (&2 * Lb) * (&4 * X)` THEN
    CONJ_TAC THENL [REPEAT(FIRST [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC;
                   MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC]) THEN
     REPEAT(FIRST [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC;
                   MATCH_MP_TAC REAL_POW_LE]) THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&504 * n * Lb * (&2 * Lb) pow 3 * (&2 * Lb) * (&4 * X) =
      (&32256 * Lb pow 5) * (n * X) /\
      (&180 * Lb pow 3) pow 2 * (n * X) = (&32400 * Lb pow 6) * (n * X)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Lb:real) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `S:real` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let MINOR_POINT_BOUND = prove
 (`!N M Kw Q k.
     3 <= N /\ 1 <= Q /\ 1 <= Kw /\ Kw * Q <= N /\ Q EXP 5 <= N /\
     k < M /\ ~(k IN circ_major M Kw Q)
     ==> norm(primexp N (&k / &M)) <=
         &16000 * log(&N) pow 4 * sqrt(&N * &N / &Q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`; `k:num`] MINOR_DIRICHLET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `q:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&1 <= &Q /\ &Q < &q /\ &q <= &Kw /\ &Kw * &Q <= &N /\
                &Q pow 5 <= &N /\ &3 <= &N`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_MUL;
                    REAL_OF_NUM_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN `Kw <= N:num` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Kw * Q:num` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `Kw = Kw * 1`] THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Q /\ &0 < &q /\ &0 < &N /\ &q <= &N /\ &Q <= &N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&Q pow 2 * &Q pow 2 * &Q <= &N /\ &Q pow 2 * &Q <= &N`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&Q pow 2 * &Q pow 2 * &Q = &Q pow 5 /\
                  &Q pow 2 * &Q = &Q pow 3`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&Q pow 5` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &Q pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `&k / &M`] PRIMEXP_MANGOLDT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&Q pow 2`; `&Q pow 2`; `N:num`; `&k / &M`; `a:num`;
                `q:num`] VINOGRADOV_LAMBDA_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Q pow 2 * &Q pow 2 * &Q` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&N`; `&Q`; `&q`; `&N / &Q`; `&2 * log(&N)`; `log(&N)`;
                `log(&N + &1)`; `log(&q)`; `log(&2 * &N)`; `log(&Q pow 2)`]
         VLB_SIMPLE) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `&16000 * log(&N) pow 4 * sqrt(&N * &N / &Q) =
                  &1000 * (&2 * log(&N)) pow 4 * sqrt(&N * &N / &Q)`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_ACCEPT_TAC(REAL_ARITH
     `!a b s t1 t2 t3 t4 w.
        t1 + t2 + t3 + t4 + s <= w ==> b <= t1 + t2 + t3 + t4 ==>
        a <= b + s ==> a <= w`)] THEN
  SUBGOAL_THEN `&1 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&3)` THEN
    CONJ_TAC THENL
     [MP_TAC LOG_3_LOWER THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N + &1 <= &N pow 2 /\ &2 * &N <= &N pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `&3 * &N <= &N * &N` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&N pow 2) = &2 * log(&N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_POW] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&Q pow 2) = &2 * log(&Q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_POW] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&Q) /\ log(&Q) <= log(&N) /\
                &0 <= log(&q) /\ log(&q) <= log(&N) /\
                &0 <= log(&N + &1) /\ log(&N + &1) <= log(&N pow 2) /\
                &0 <= log(&2 * &N) /\ log(&2 * &N) <= log(&N pow 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&Kw * &Q` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]]);;

let MINOR_SUM = prove
 (`!N M Kw Q B.
     N < M /\ &0 <= B /\
     (!k. k < M /\ ~(k IN circ_major M Kw Q)
          ==> norm(primexp N (&k / &M)) <= B)
     ==> norm(vsum ({k | k < M} DIFF circ_major M Kw Q)
                (\k. primexp N (&k / &M) pow 3 * expi(--(&N * &k / &M))))
         <= B * &M *
            sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum ({k | k < M} DIFF circ_major M Kw Q)
                  (\k. B * norm(primexp N (&k / &M)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG_LT; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_RID;
                COMPLEX_NORM_POW] THEN
    REWRITE_TAC[REAL_RING `(x:real) pow 3 = x * x pow 2`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {k | k < M} (\k. B * norm(primexp N (&k / &M)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    REWRITE_TAC[SUM_LMUL] THEN ASM_SIMP_TAC[PARSEVAL_PRIMEXP] THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

let VINOGRADOV_FIXED = prove
 (`!N M Kw Q D B.
     1 <= N /\ 3 * N < M /\ 1 <= Kw /\ 1 <= Q /\ 2 * Q EXP 2 < Kw /\
     &0 <= D /\ &0 <= B /\
     (!q h b. 1 <= q /\ q <= Q /\ h <= N /\ b < q /\ coprime(b,q)
              ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                          (\p. log(&p)) - &h / &(phi q)) <= D) /\
     (!k. k < M /\ ~(k IN circ_major M Kw Q)
          ==> norm(primexp N (&k / &M)) <= B)
     ==> abs(vinogradov_rep3 N - ((&N - &1) * (&N - &2) / &2) *
             sing_series N Q)
         <= &2 * &Kw * &N * sum(1..Q) (\q. inv(&(phi q))) +
            &2 * ((&Q * D + log(&Q)) * (&1 + &2 * pi * &N / &Kw)) *
            (sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2) +
             &N * sum(1..Q) (\q. inv(&(phi q)))) +
            B * sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `M:num`] CIRCLE_PRIMEXP) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{k | k < M} = circ_major M Kw Q UNION
                              ({k | k < M} DIFF circ_major M Kw Q)`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`] CIRC_MAJOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_UNION; CIRC_MAJOR_FINITE; FINITE_DIFF; FINITE_NUMSEG_LT;
           SET_RULE `DISJOINT (s:num->bool) (t DIFF s)`] THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`;
    `D:real`] MAJOR_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`; `B:real`] MINOR_SUM) THEN
  ASM_SIMP_TAC[ARITH_RULE `3 * N < M ==> N < M`] THEN
  ABBREV_TAC `vmaj = vsum (circ_major M Kw Q)
                 (\k. primexp N (&k / &M) pow 3 * expi(--(&N * &k / &M)))` THEN
  ABBREV_TAC `vmin = vsum ({k | k < M} DIFF circ_major M Kw Q)
                 (\k. primexp N (&k / &M) pow 3 * expi(--(&N * &k / &M)))` THEN
  ABBREV_TAC `P = sum(1..Q) (\q. inv(&(phi q)))` THEN
  ABBREV_TAC `W = sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)` THEN
  ABBREV_TAC `E = (&Q * D + log(&Q)) * (&1 + &2 * pi * &N / &Kw)` THEN
  ABBREV_TAC `S = sing_series N Q` THEN
  ABBREV_TAC `R = vinogradov_rep3 N` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `abs(&M * R - (&M * (&N - &1) * (&N - &2) / &2) * S) <=
    (&2 * &Kw * &M * &N * P + &2 * E * (&M * W + &M * &N * P)) +
    B * &M * W`
  MP_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_CX; CX_SUB] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(NORM_ARITH
     `!x y c:complex e1 e2. norm(x - c) <= e1 /\ norm(y) <= e2
                            ==> norm((x + y) - c) <= e1 + e2`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&M * R - (&M * (&N - &1) * (&N - &2) / &2) * S =
    &M * (R - ((&N - &1) * (&N - &2) / &2) * S) /\
    (&2 * &Kw * &M * &N * P + &2 * E * (&M * W + &M * &N * P)) + B * &M * W =
    &M * (&2 * &Kw * &N * P + &2 * E * (W + &N * P) + B * W)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Choosing the parameters; Vinogradov's theorem.                            *)
(* ------------------------------------------------------------------------- *)

let NUM_FLOOR_HALF = prove
 (`!x. &1 <= x ==> ?n. 1 <= n /\ &n <= x /\ x <= &2 * &n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &n` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= &n` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ASM_REAL_ARITH_TAC]);;

let SUM_W_SQUARE = prove
 (`!N. 1 <= N
       ==> &0 <= sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2) /\
           sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2) <=
           &N * log(&N) pow 2`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1..N`; `\m. (if prime m then log(&m) else &0) pow 2`;
                 `log(&N) pow 2`] SUM_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; IN_NUMSEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_LE_POW_2]]);;

let DIV_PARAMETER_FACTS = prove
 (`!N Q. 1 <= Q /\ (2 * Q EXP 2 + 1) * Q <= N
         ==> 1 <= N DIV Q /\ 2 * Q EXP 2 < N DIV Q /\
             (N DIV Q) * Q <= N /\ N <= 2 * Q * N DIV Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(Q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 * Q EXP 2 < N DIV Q` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a < b <=> a + 1 <= b`] THEN
    ASM_SIMP_TAC[LE_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[DIV_MUL_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `Q:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = N DIV Q` THEN ABBREV_TAC `r = N MOD Q` THEN STRIP_TAC THEN
  SUBGOAL_THEN `Q <= d * Q:num` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `Q = 1 * Q`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * Q * d = 2 * (d * Q)` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  UNDISCH_TAC `N = d * Q + r:num` THEN UNDISCH_TAC `r < Q:num` THEN
  SPEC_TAC(`d * Q:num`,`x:num`) THEN ARITH_TAC);;

let TRIPLE_LOWER = prove
 (`!N. 6 <= N ==> &N pow 2 / &4 <= (&N - &1) * (&N - &2) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &N * (&N - &6)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_SUB_LE; REAL_OF_NUM_LE];
    REAL_ARITH_TAC]);;

let EXP_8_LE = prove
 (`exp(&8) <= &6561`,
  SUBGOAL_THEN `exp(&8) = exp(&1) pow 8` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 pow 8` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SING_SERIES_HALF = prove
 (`!N R. ODD N /\ 13122 <= R ==> &1 / &2 <= sing_series N (R EXP 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `R EXP 2`] SING_SERIES_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXP_2] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= R * R ==> 1 <= R * R`) THEN
    MATCH_MP_TAC(ARITH_RULE `1 * 1 <= R * R ==> 1 <= R * R`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
  SIMP_TAC[POW_2_SQRT; REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 / &2 ==> &1 - x <= s ==> &1 / &2 <= s`) THEN
  SUBGOAL_THEN `&13122 <= &R` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&13122 <= x ==> &0 < x`] THEN
  MP_TAC EXP_8_LE THEN ASM_REAL_ARITH_TAC);;

let E1_BOUND = prove
 (`!n L r k P.
     &10 pow 6 <= L /\ &0 < k /\ k * r pow 2 <= n /\ L pow 8 <= &2 * r /\
     &0 <= r /\ &0 <= P /\ P <= &8 * L /\ &0 <= n
     ==> &1000 * (&2 * k * n * P) <= n pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&16000 * L <= r pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&64000 * L <= L pow 16 /\ L pow 16 <= &4 * r pow 2`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 2` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
        SUBGOAL_THEN `(L:real) pow 16 = (L pow 8) pow 2 /\
                      &4 * (r:real) pow 2 = (&2 * r) pow 2`
        (CONJUNCTS_THEN SUBST1_TAC) THENL
         [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(n:real) * (k * (&16000 * L))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1000 * (&2 * k * (n:real) * (&8 * L))` THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(k:real) * r pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let E3_BOUND = prove
 (`!n L r W.
     &10 pow 6 <= L /\ &1 <= r /\ L pow 8 <= &2 * r /\ &0 <= W /\
     W <= n * L pow 2 /\ &0 <= n
     ==> &1000 * (&16000 * L pow 4 * (n / r) * W) <= n pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&16000000 * L pow 6 <= r` ASSUME_TAC THENL
   [SUBGOAL_THEN `&32000000 * L pow 6 <= L pow 8` MP_TAC THENL
     [SUBGOAL_THEN `(L:real) pow 8 = L pow 2 * L pow 6` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&10 pow 6 * (&10:real) pow 6` THEN CONJ_TAC THENL
         [CONV_TAC REAL_RAT_REDUCE_CONV;
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= n / r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&16000000 * (L:real) pow 6) * (n / r * n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1000 * (&16000 * (L:real) pow 4 * (n / r) * (n * L pow 2))`
      THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(r:real) * (n / r * n)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(r = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]]);;

let E2_BOUND = prove
 (`!n L r k P W c.
     &10 pow 6 * (&1 + c) <= L /\ &0 <= c /\ &10 pow 7 * L pow 80 <= n /\
     &1 <= r /\ r <= L pow 8 /\ &0 < k /\ n <= &2 * r pow 2 * k /\
     &0 <= P /\ P <= &8 * L /\ &0 <= W /\ W <= n * L pow 2 /\
     &0 <= log(r pow 2) /\ log(r pow 2) <= L
     ==> &1000 * (&2 * ((r pow 2 * (c * n / L pow 40) + log(r pow 2)) *
                        (&1 + &2 * pi * n / k)) * (W + n * P))
         <= &2 * n pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&10 pow 6 <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow 6 * (&1 + c)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L /\ &0 < L` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&10 pow 7 * (L:real) pow 80` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real) pow 2 <= L pow 16` ASSUME_TAC THENL
   [SUBGOAL_THEN `(L:real) pow 16 = (L pow 8) pow 2` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * n / L pow 40` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `r pow 2 * (c * n / L pow 40) + log(r pow 2) <= c * n / L pow 24 + L`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(L:real) pow 16 * (c * n / L pow 40)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(L = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= n / k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &2 * pi * n / k <= &17 * L pow 16` ASSUME_TAC THENL
   [SUBGOAL_THEN `n / k <= &2 * r pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN `pi <= &4 /\ &1 <= (L:real) pow 16` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * pi * n / k <= &2 * &4 * (&2 * L pow 16)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[PI_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `W + n * P <= &9 * n * L pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `n * P <= n * (&8 * L pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&8 * L` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1000 * (&2 * ((c * n / L pow 24 + L) * (&17 * L pow 16)) *
                       (&9 * n * L pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[REAL_POS] THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[PI_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_REWRITE_TAC[REAL_POS] THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[PI_POS_LE];
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&1000 * (&2 * ((c * n / L pow 24 + L) * (&17 * L pow 16)) *
             (&9 * n * L pow 2)) =
    (&306000 * c / L pow 6) * n pow 2 + (&306000 * L pow 19) * n`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(L = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= x /\ b <= x ==> a + b <= &2 * x`) THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; ASSUME `&0 < L`] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L:real` THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `&10 pow 6 * (&1 + c) <= L`) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&10 pow 7 * (L:real) pow 80` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]]);;

let VINOGRADOV = prove
 (`?N0. !N. ODD N /\ N0 <= N
            ==> ?p1 p2 p3. prime p1 /\ prime p2 /\ prime p3 /\
                           p1 + p2 + p3 = N`,
  MP_TAC(SPECL [`40`; `16`] THETA_AP_UNIFORM) THEN
  DISCH_THEN(X_CHOOSE_TAC `Ct:real`) THEN
  MP_TAC(SPECL [`80`; `&10 pow 7`; `&1`] POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_TAC `L1:real`) THEN
  MP_TAC(SPEC `exp(max L1 (&10 pow 6 * (&1 + abs Ct)))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N1 + 6` THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC VINOGRADOV_REP3_POS THEN
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
      MP_TAC(SPEC `Ct:real` REAL_ABS_POS)
        THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&10 pow 7 * L pow 80 <= &N` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `L:real`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "L" THEN ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  MP_TAC(SPEC `(L:real) pow 8` NUM_FLOOR_HALF) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LE_1
    THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Q = R EXP 2` THEN
  SUBGOAL_THEN `&1 <= &Q /\ &Q <= L pow 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      SUBGOAL_THEN `(L:real) pow 16 = (L pow 8) pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q EXP 5 <= N /\ (2 * Q EXP 2 + 1) * Q <= N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&Q pow 5 <= L pow 80 /\ &Q pow 3 <= L pow 80`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `(L:real) pow 80 = (L pow 16) pow 5` SUBST1_TAC THENL
         [CONV_TAC REAL_RING; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 48` THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `(L:real) pow 48 = (L pow 16) pow 3` SUBST1_TAC THENL
           [CONV_TAC REAL_RING; ALL_TAC] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(L:real) pow 80 <= &10 pow 7 * L pow 80` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&Q <= &Q pow 3 /\
                  (&2 * &Q pow 2 + &1) * &Q = &2 * &Q pow 3 + &Q`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        CONV_TAC REAL_RING];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `Q:num`] DIV_PARAMETER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Kw = N DIV Q` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `3 * N + 1`; `Kw:num`; `Q:num`;
                `abs Ct * &N / L pow 40`;
                `&16000 * L pow 4 * sqrt(&N * &N / &Q)`] VINOGRADOV_FIXED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
        REWRITE_TAC[REAL_POS]];
      MAP_EVERY X_GEN_TAC [`q:num`; `h:num`; `b:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Ct * &N / log(&N) pow 40` THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Q` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ASM_REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN EXPAND_TAC "L" THEN
      MATCH_MP_TAC MINOR_POINT_BOUND THEN EXISTS_TAC `Kw:num` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q <= N:num` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Kw * Q:num` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `Q = 1 * Q`] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL];
    ALL_TAC] THEN
  ABBREV_TAC `P = sum(1..Q) (\q. inv(&(phi q)))` THEN
  ABBREV_TAC `W = sum(1..N) (\m. (if prime m then log(&m) else &0) pow 2)` THEN
  SUBGOAL_THEN `&0 <= log(&Q) /\ log(&Q) <= L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "L" THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LE]
         THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P /\ P <= &8 * L` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS];
      MP_TAC(SPEC `Q:num` SUM_INV_PHI_LE) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= W /\ W <= &N * L pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN EXPAND_TAC "L" THEN MATCH_MP_TAC SUM_W_SQUARE THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&R pow 2 = &Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[REAL_OF_NUM_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&N * &N / &Q) = &N / &R` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&N * &N / &R pow 2 = (&N / &R) pow 2` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(&R = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N pow 2 / &8 <=
                ((&N - &1) * (&N - &2) / &2) * sing_series N Q`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&N pow 2 / &8 = (&N pow 2 / &4) * (&1 / &2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
      MATCH_MP_TAC TRIPLE_LOWER THEN ASM_ARITH_TAC;
      REAL_ARITH_TAC;
      EXPAND_TAC "Q" THEN MATCH_MP_TAC SING_SERIES_HALF THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN `L <= L pow 8` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MP_TAC(ASSUME `&10 pow 6 <= L`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Kw /\ &Kw * &Q <= &N /\ &N <= &2 * &Q * &Kw`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&N`; `L:real`; `&R`; `&Kw`; `P:real`] E1_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`&N`; `L:real`; `&R`; `W:real`] E3_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE]; DISCH_TAC] THEN
  MP_TAC(SPECL [`&N`; `L:real`; `&R`; `&Kw`; `P:real`; `W:real`; `abs Ct`]
         E2_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &N pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
