(* ========================================================================= *)
(* Vinogradov's estimate for exponential sums over primes (Nathanson,        *)
(* Theorem 8.5, through Vaughan's identity):                                 *)
(*   VINOGRADOV_LAMBDA_BOUND: for 1 <= q, (aa,q) = 1, |alpha - aa/q| <=      *)
(*   1/q^2, 1 <= U, 1 <= V and U V <= N,                                     *)
(*     |sum_{n <= N} Lambda(n) e(n alpha)| <=                                *)
(*       18 U + 4 log N (14 N/q (1 + log(N + 1)) + 8 (V + q) (1 + log q))    *)
(*       + 2 log N (14 N/q (1 + log(N + 1)) + 8 (U V + q) (1 + log q))       *)
(*       + (2 log N + 1) sqrt(504 N log(2 N) (1 + log V)^3 (1 + log q)       *)
(*                            (N/q + N/U + N/V + q)).                        *)
(* (With U = V = Q^2 and Q < q <= N/Q this is O(N log^4 N / sqrt Q).)        *)
(*                                                                           *)
(* * DIRICHLET_CONV_VSUM_GEN, VAUGHAN_VSUM_GEN: Dirichlet convolutions and   *)
(*   Vaughan's identity (vaughan.ml) summed against an arbitrary c(m n).     *)
(* * Type I sums (VAUGHAN_S0_BOUND, TYPE_I_GENERIC, VAUGHAN_EXP_S1_BOUND,    *)
(*   VAUGHAN_EXP_S2_BOUND) by EMIN_SUM_DIV, the log weights by Abel          *)
(*   summation.                                                              *)
(* * Type II sums (VAUGHAN_EXP_S3_BOUND) by Cauchy-Schwarz on dyadic blocks  *)
(*   (DYADIC_VSUM, TYPE2_BLOCK_FINAL): expanding the square gives the        *)
(*   bilinear form of TYPE2_PAIR_BOUND, bounded by EMIN_SUM_CONST.           *)
(* ========================================================================= *)

needs "Sieve/expsum.ml";;
needs "Sieve/vaughan.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Vaughan's identity against an arbitrary c(m n).                           *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CONV_VSUM_GEN = prove
 (`!f g (c:num->complex) N.
     vsum(1..N) (\n. Cx(dirichlet_conv f g n) * c n) =
     vsum(1..N) (\d. Cx(f d) * vsum(1..N DIV d) (\k. Cx(g k) * c(d * k)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(1..N) (\n. vsum {d | d divides n}
     (\d. Cx(f d) * (Cx(g(n DIV d)) * c(d * n DIV d))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[dirichlet_conv; LE_1; ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
    REWRITE_TAC[GSYM VSUM_CX] THEN
    ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_DIVISORS; LE_1;
                 ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `d * n DIV d = n` SUBST1_TAC THENL
     [ASM_MESON_TAC[DIVIDES_DIV_MULT; MULT_SYM];
      REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING];
    REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT; LE_1;
                 ARITH_RULE `1 <= n ==> ~(n = 0)`]]);;

let VAUGHAN_VSUM_GEN = prove
 (`!U V (c:num->complex) N.
     vsum(1..N) (\n. Cx(mangoldt n) * c n) =
     vsum(1..N) (\n. Cx(vaughan_F U n) * c n) +
     vsum(1..N) (\d. Cx(vaughan_G V d) *
                     vsum(1..N DIV d) (\h. Cx(log(&h)) * c(d * h))) -
     vsum(1..N) (\s. Cx(dirichlet_conv (vaughan_G V) (vaughan_F U) s) *
                     vsum(1..N DIV s) (\t. c(s * t))) +
     vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) *
                     vsum(1..N DIV m) (\k. Cx(vaughan_e V k) * c(m * k)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum(1..N) (\n. Cx(vaughan_F U n) * c n +
                    Cx(dirichlet_conv (vaughan_G V) (\h. log(&h)) n) * c n -
                    Cx(dirichlet_conv
                         (dirichlet_conv (vaughan_G V) (vaughan_F U))
                           (\t. &1) n) *
                    c n +
                    Cx(dirichlet_conv (\m. mangoldt m - vaughan_F U m)
                             (vaughan_e V) n) *
                    c n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MP_TAC(SPECL [`U:real`; `V:real`;
     `n:num`] VAUGHAN_IDENTITY) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[CX_ADD; CX_SUB] THEN CONV_TAC COMPLEX_RING;
    SIMP_TAC[VSUM_ADD; VSUM_SUB; FINITE_NUMSEG] THEN
    REWRITE_TAC[DIRICHLET_CONV_VSUM_GEN] THEN
    REWRITE_TAC[COMPLEX_MUL_LID; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Type I sums.                                                              *)
(* ------------------------------------------------------------------------- *)

let VAUGHAN_S0_BOUND = prove
 (`!U N (c:num->complex).
     &0 <= U /\ (!n. norm(c n) <= &1)
     ==> norm(vsum(1..N) (\n. Cx(vaughan_F U n) * c n)) <= &18 * U`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `U:real` FLOOR_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MP_TAC(SPEC `U:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..M) (\d. mangoldt d)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..N) (\n. vaughan_F U n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN
      REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= vaughan_F U n` ASSUME_TAC THENL
       [REWRITE_TAC[vaughan_F] THEN COND_CASES_TAC THEN
        REWRITE_TAC[MANGOLDT_POS_LE; REAL_LE_REFL];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[vaughan_F] THEN
      REWRITE_TAC[GSYM SUM_RESTRICT_SET; ETA_AX] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; MANGOLDT_POS_LE; SUBSET; IN_ELIM_THM;
                  IN_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&n < &M + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC]];
    MP_TAC(SPEC `M:num` PSI_BOUND) THEN ASM_REAL_ARITH_TAC]);;

let TYPE_I_GENERIC = prove
 (`!(w:num->real) (z:num->complex) N D W Kw alpha a q.
     1 <= q /\ coprime(a,q) /\ abs(alpha - &a / &q) <= inv(&q pow 2) /\
     &1 <= D /\ D <= &N /\ &0 <= W /\ &0 <= Kw /\
     (!d. 1 <= d /\ d <= N ==> abs(w d) <= W) /\
     (!d. 1 <= d /\ d <= N /\ D < &d ==> w d = &0) /\
     (!d. 1 <= d /\ d <= N ==> norm(z d) <= Kw * emin (&N / &d) (&d * alpha))
     ==> norm(vsum(1..N) (\d. Cx(w d) * z d)) <=
         W * Kw * (&14 * &N / &q * (&1 + log(&N + &1)) +
                  &8 * (D + &q) * (&1 + log(&q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `D:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MP_TAC(SPEC `D:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `M <= N:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!d. &d <= D <=> d <= M` ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `&d < &M + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..M) (\d. W * Kw * emin (&N / &d) (&d * alpha))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..N) (\d. if d <= M
                               then W * Kw * emin (&N / &d) (&d * alpha)
                               else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; COMPLEX_NORM_MUL;
                  COMPLEX_NORM_CX] THEN
      X_GEN_TAC `d:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `abs((w:num->real) d) <= W /\
        norm((z:num->complex) d) <= Kw * emin (&N / &d) (&d * alpha)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `W * norm((z:num->complex) d)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
          REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(w:num->real) d = &0` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[REAL_NOT_LE];
          REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LZERO; REAL_LE_REFL]]];
      REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&14 * &N / &q * (&1 + log(&M + &1)) +
              &8 * (&M + &q) * (&1 + log(&q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EMIN_SUM_DIV THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' ==> a + b <= a' + b'`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
    THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
    THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]]]);;

let NUM_DIV_LE_REAL = prove
 (`!N d. 1 <= d ==> &(N DIV d) <= &N / &d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &d:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`N:num`; `d:num`] DIVISION) THEN ASM_ARITH_TAC);;

let VAUGHAN_EXP_S1_BOUND = prove
 (`!V N alpha a q.
     1 <= q /\ coprime(a,q) /\ abs(alpha - &a / &q) <= inv(&q pow 2) /\
     &1 <= V /\ V <= &N
     ==> norm(vsum(1..N) (\d. Cx(vaughan_G V d) *
                              vsum(1..N DIV d)
                                (\h. Cx(log(&h)) * expi(&(d * h) * alpha))))
         <= &1 * (&4 * log(&N)) *
            (&14 * &N / &q * (&1 + log(&N + &1)) +
             &8 * (V + &q) * (&1 + log(&q)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  MATCH_MP_TAC TYPE_I_GENERIC THEN
  MAP_EVERY EXISTS_TAC [`alpha:real`; `a:num`] THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[vaughan_G] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_ABS_MOBIUS; REAL_ABS_NUM; REAL_POS];
    REPEAT STRIP_TAC THEN REWRITE_TAC[vaughan_G] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!h. &(d * h) * alpha = &h * (&d * alpha)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * log(&(N DIV d)) * emin (&(N DIV d)) (&d * alpha)` THEN
  REWRITE_TAC[LOG_EXPSUM_BOUND] THEN
  SUBGOAL_THEN `1 <= N DIV d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[DIV_LE]];
    MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC EMIN_MONO THEN MATCH_MP_TAC NUM_DIV_LE_REAL THEN
    ASM_REWRITE_TAC[]]);;

let VAUGHAN_EXP_S2_BOUND = prove
 (`!U V N alpha a q.
     1 <= q /\ coprime(a,q) /\ abs(alpha - &a / &q) <= inv(&q pow 2) /\
     &1 <= U * V /\ U * V <= &N
     ==> norm(vsum(1..N)
                (\s. Cx(dirichlet_conv (vaughan_G V) (vaughan_F U) s) *
                              vsum(1..N DIV s) (\t. expi(&(s * t) * alpha))))
         <= log(&N) * &2 *
            (&14 * &N / &q * (&1 + log(&N + &1)) +
             &8 * (U * V + &q) * (&1 + log(&q)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  MATCH_MP_TAC TYPE_I_GENERIC THEN
  MAP_EVERY EXISTS_TAC [`alpha:real`; `a:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VAUGHAN_C_BOUND THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC VAUGHAN_C_ZERO THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. &(s * t) * alpha = &t * (&s * alpha)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * emin (&(N DIV s)) (&s * alpha)` THEN
  REWRITE_TAC[VSUM_EXPI_GEOM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EMIN_MONO THEN MATCH_MP_TAC NUM_DIV_LE_REAL THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Type II sums on blocks.                                                   *)
(* ------------------------------------------------------------------------- *)

let VSUM_NUMSEG_INDICATOR = prove
 (`!(c:num->real) (f:num->complex) n Kw.
     n <= Kw
     ==> vsum(1..n) (\k. Cx(c k) * f k) =
         vsum(1..Kw) (\k. Cx(if k <= n then c k else &0) * f k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC);;

let TYPE2_PAIR_BOUND = prove
 (`!(b:num->real) N M i j alpha.
     1 <= i /\ 1 <= j
     ==> abs(sum(M+1..2*M)
               (\m. (if i <= N DIV m then b i else &0) *
                    (if j <= N DIV m then b j else &0) *
                    Re(expi(&(m * i) * alpha - &(m * j) * alpha)))) <=
         abs(b i) * abs(b j) * &2 * emin (&M) ((&i - &j) * alpha)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = MIN (2 * M) (MIN (N DIV i) (N DIV j))` THEN
  SUBGOAL_THEN
   `sum(M+1..2*M)
      (\m. (if i <= N DIV m then b i else &0) *
           (if j <= N DIV m then b j else &0) *
           Re(expi(&(m * i) * alpha - &(m * j) * alpha))) =
    b i * b j * Re(vsum(M+1..L) (\m. expi(&m * ((&i - &j) * alpha))))`
  SUBST1_TAC THENL
   [SIMP_TAC[RE_VSUM; FINITE_NUMSEG; GSYM SUM_LMUL] THEN
    SUBGOAL_THEN `!m. &(m * i) * alpha - &(m * j) * alpha =
                      &m * ((&i - &j) * alpha)` (fun th -> REWRITE_TAC[th])
    THENL [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(M+1..2*M) (\m. if m <= L
                         then b i * b j * Re(expi(&m * ((&i - &j) * alpha)))
                         else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(i <= N DIV m /\ j <= N DIV m) <=> m <= L` MP_TAC THENL
       [EXPAND_TAC "L" THEN
        REWRITE_TAC[ARITH_RULE `m <= MIN a b <=> m <= a /\ m <= b`] THEN
        SUBGOAL_THEN `~(m = 0) /\ ~(i = 0) /\ ~(j = 0)` STRIP_ASSUME_TAC
        THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[LE_RDIV_EQ] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY ASM_CASES_TAC [`i <= N DIV m`; `j <= N DIV m`] THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
      SUBGOAL_THEN `{m | m IN M+1..2*M /\ m <= L} = M+1..L` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN EXPAND_TAC "L" THEN
        ARITH_TAC;
        REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vsum(M+1..L) (\m. expi(&m * ((&i - &j) * alpha))))` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * emin (&(L - M)) ((&i - &j) * alpha)` THEN
  REWRITE_TAC[VSUM_EXPI_INTERVAL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EMIN_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  EXPAND_TAC "L" THEN ARITH_TAC);;

let TYPE2_SQUARE_BOUND = prove
 (`!(b:num->real) N M Kw alpha.
     1 <= M /\ N DIV (M + 1) <= Kw
     ==> sum(M+1..2*M)
           (\m. norm(vsum(1..N DIV m)
                       (\k. Cx(b k) * expi(&(m * k) * alpha))) pow 2)
         <= sum(1..Kw) (\i. sum(1..Kw) (\j. abs(b i) * abs(b j) *
                                         &2 * emin (&M) ((&i - &j) * alpha)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(M+1..2*M) (\m. sum(1..Kw) (\i. sum(1..Kw) (\j.
                 (if i <= N DIV m then b i else &0) *
                 (if j <= N DIV m then b j else &0) *
                 Re(expi(&(m * i) * alpha - &(m * j) * alpha)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `N DIV m <= Kw` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N DIV (M + 1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIV_MONO2 THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[VSUM_NUMSEG_INDICATOR] THEN
    REWRITE_TAC[NORM_VSUM_EXPI_POW2];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
  MATCH_MP_TAC TYPE2_PAIR_BOUND THEN ASM_REWRITE_TAC[]);;

let TYPE2_BLOCK_BOUND = prove
 (`!(a:num->real) (b:num->real) N M Kw alpha aa q.
     1 <= M /\ N DIV (M + 1) <= Kw /\
     1 <= q /\ coprime(aa,q) /\ abs(alpha - &aa / &q) <= inv(&q pow 2)
     ==> norm(vsum(M+1..2*M) (\m. Cx(a m) *
                vsum(1..N DIV m) (\k. Cx(b k) * expi(&(m * k) * alpha))))
         pow 2
         <= sum(M+1..2*M) (\m. a m pow 2) *
            sum(1..Kw) (\k. b k pow 2) *
            &2 * (&Kw / &q + &1) * (&7 * &M + &4 * &q * (&1 + log(&q)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(M+1..2*M) (\m. (a:num->real) m pow 2) *
    sum(M+1..2*M) (\m. norm(vsum(1..N DIV m)
                     (\k. Cx(b k) * expi(&(m * k) * alpha))) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NORM_VSUM_CAUCHY_SCHWARZ THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `B = &2 * (&Kw / &q + &1) * (&7 * &M + &4 * &q * (&1 + log(&q)))`
  THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Kw) (\i. sum(1..Kw) (\j. abs((b:num->real) i) * abs(b j) *
                                         &2 * emin (&M) ((&i - &j) * alpha)))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC TYPE2_SQUARE_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`b:num->real`;
                 `\i j. &2 * emin (&M) ((&i - &j) * alpha)`; `Kw:num`]
    SUM_SYM_BILINEAR_LE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM EMIN_NEG] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  EXPAND_TAC "B" THEN REWRITE_TAC[SUM_LMUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Kw) (\j. emin (&M) (--(&i * alpha) + &j * alpha))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM EMIN_NEG] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC EMIN_SUM_CONST THEN EXISTS_TAC `aa:num` THEN
    ASM_REWRITE_TAC[REAL_POS]]);;

let SUM_A_SQUARE = prove
 (`!U M. 1 <= M
         ==> sum(M+1..2*M) (\m. (mangoldt m - vaughan_F U m) pow 2) <=
             &36 * &M * log(&2 * &M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log(&2 * &M)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..2*M) (\m. mangoldt m * log(&2 * &M))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(M+1..2*M) (\m. mangoldt m * log(&2 * &M))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= mangoldt m - vaughan_F U m /\
                    mangoldt m - vaughan_F U m <= mangoldt m`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[vaughan_F] THEN COND_CASES_TAC THEN
        MP_TAC(SPEC `m:num` MANGOLDT_POS_LE) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `mangoldt m <= log(&2 * &M)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&m)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MANGOLDT_LE_LOG THEN ASM_ARITH_TAC;
          MATCH_MP_TAC LOG_MONO_LE_IMP THEN
          REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
          ASM_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[MANGOLDT_POS_LE]];
    REWRITE_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&36 * &M) * log(&2 * &M)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `2 * M` PSI_BOUND) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; ETA_AX] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]]]);;

let SUM_B_SQUARE = prove
 (`!V Kw. &1 <= V
         ==> sum(1..Kw) (\k. vaughan_e V k pow 2) <= &Kw * (&1 + log V) pow 3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Kw) (\k. &(tau_le V k) pow 2)` THEN
  ASM_SIMP_TAC[SUM_TAU_LE_SQUARE_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS; VAUGHAN_E_BOUND; REAL_ABS_NUM]);;

let EXISTS_LOG2 = prove
 (`!N. 1 <= N ==> ?J. 2 EXP J <= N /\ N < 2 EXP (J + 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\n. N < 2 EXP n` num_WOP) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
  CONJ_TAC THENL [MESON_TAC[LT_POW2_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `N < 2 EXP n` THEN ASM_REWRITE_TAC[EXP] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `n - 1` THEN
  SUBGOAL_THEN `n - 1 + 1 = n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ARITH_TAC]);;

let LOG2_BOUND = prove
 (`!J N. 1 <= N /\ 2 EXP J <= N ==> &J <= &2 * log(&N)`,
  REPEAT STRIP_TAC THEN MP_TAC LOG_2_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&J * log(&2) <= log(&N)` MP_TAC THENL
   [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_RULE `0 < n <=> ~(n = 0)`; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &J` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&J * (&1 / &2) <= &J * log(&2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let LE_MULT_EXP2 = prove
 (`!M0 J. M0 <= M0 * 2 EXP J`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `M0 = M0 * 1`] THEN
  REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0;
              ARITH]);;

let DYADIC_VSUM = prove
 (`!(f:num->complex) M0 J.
     vsum(M0+1..M0 * 2 EXP (J + 1)) f =
     vsum(0..J) (\j. vsum(M0 * 2 EXP j + 1..2 * (M0 * 2 EXP j)) f)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_SING_NUMSEG; ADD_CLAUSES; EXP; EXP_1; MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `M0 * 2 = 2 * M0`];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `M0 * 2 EXP (SUC J + 1) =
                M0 * 2 EXP (J + 1) + M0 * 2 EXP (J + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[ADD1; EXP_ADD] THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[VSUM_ADD_SPLIT; LE_MULT_EXP2; LE_ADD_RCANCEL] THEN
  REWRITE_TAC[ADD1] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let TYPE2_BLOCK_FINAL = prove
 (`!U V N M alpha aa q.
     1 <= q /\ coprime(aa,q) /\ abs(alpha - &aa / &q) <= inv(&q pow 2) /\
     &1 <= U /\ &1 <= V /\ 1 <= N /\ 1 <= M /\ U <= &M + &1
     ==> norm(vsum(M+1..2*M) (\m. Cx(mangoldt m - vaughan_F U m) *
                vsum(1..N DIV m)
                  (\k. Cx(vaughan_e V k) * expi(&(m * k) * alpha))))
         <= sqrt(&504 * &N * log(&2 * &N) * (&1 + log V) pow 3 *
                 (&1 + log(&q)) * (&N / &q + &N / U + &N / V + &q))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Kw = N DIV (M + 1)` THEN
  ABBREV_TAC `L = &1 + log(&q)` THEN
  SUBGOAL_THEN `&0 < &q:real /\ &0 < &N:real /\ &1 <= L /\ &0 <= log V /\
                &0 <= log(&2 * &N)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC;
      EXPAND_TAC "L" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE]
      THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `X = &504 * &N * log(&2 * &N) * (&1 + log V) pow 3 * L *
                  (&N / &q + &N / U + &N / V + &q)` THEN
  SUBGOAL_THEN `&0 <= &N / &q + &N / U + &N / V + &q` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c /\ &0 <= d ==> &0 <= a + b + c + d`) THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&Kw <= V` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
    ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
    REWRITE_TAC[NORM_EQ_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN `vsum(1..N DIV m)
                   (\k. Cx(vaughan_e V k) * expi(&(m * k) * alpha)) = vec 0`
    (fun th -> REWRITE_TAC[th; COMPLEX_MUL_RZERO; COMPLEX_VEC_0]) THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN `vaughan_e V k = &0`
     (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
    MATCH_MP_TAC VAUGHAN_E_SMALL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Kw:real` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N DIV m` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kw" THEN MATCH_MP_TAC DIV_MONO2 THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  MP_TAC(ISPECL [`\m. mangoldt m - vaughan_F U m`; `vaughan_e V`;
                 `N:num`; `M:num`; `Kw:num`; `alpha:real`; `aa:num`; `q:num`]
    TYPE2_BLOCK_BOUND) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  MP_TAC(SPECL [`U:real`; `M:num`] SUM_A_SQUARE) THEN
  MP_TAC(SPECL [`V:real`; `Kw:num`] SUM_B_SQUARE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `As = sum(M+1..2*M) (\m. (mangoldt m - vaughan_F U m) pow 2)` THEN
  ABBREV_TAC `Bs = sum(1..Kw) (\k. vaughan_e V k pow 2)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= As /\ &0 <= Bs` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["As"; "Bs"] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Kw /\ &M * &Kw <= &N /\ (&M + &1) * &Kw <= &N`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(M + 1) * Kw <= N` MP_TAC THENL
     [EXPAND_TAC "Kw" THEN MP_TAC(SPECL [`N:num`; `M + 1`] DIVISION) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&1 <= &Kw:real` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `V:real` THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(&M + &1) * &Kw <= &N` THEN UNDISCH_TAC `&1 <= &Kw:real` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&M <= &N / V /\ &Kw <= &N / U /\ &M <= &N` STRIP_ASSUME_TAC
  THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M * &Kw` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&M + &1) * &Kw` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M * &Kw` THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * &M) <= log(&2 * &N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `&M <= &N` THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&Kw / &q + &1) * (&7 * &M + &4 * &q * L) <=
    &7 * L * (&N / &q + &N / U + &N / V + &q)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(&Kw / &q + &1) * (&7 * &M + &4 * &q * L) =
                  &7 * (&M * &Kw) / &q + &7 * &M + &4 * &Kw * L + &4 * &q * L`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &q:real` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(&M * &Kw) / &q <= &N / &q * L /\ &M <= &N / V * L /\
                  &Kw * L <= &N / U * L /\ &0 <= &q * L`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N / &q` THEN
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N / V` THEN
        ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &N / &q * L /\ &0 <= &N / U * L /\
                  &0 <= &N / V * L /\ &q <= &q * L`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
          TRY(MATCH_MP_TAC REAL_LE_DIV) THEN ASM_REAL_ARITH_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `As * Bs * &2 * (&Kw / &q + &1) * (&7 * &M + &4 * &q * L)` THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = (&Kw / &q + &1) * (&7 * &M + &4 * &q * L)` THEN
  ABBREV_TAC `S = &N / &q + &N / U + &N / V + &q` THEN
  ABBREV_TAC `W3 = (&1 + log V) pow 3` THEN
  SUBGOAL_THEN `&0 <= W3 /\ &0 <= P /\ &0 <= log(&2 * &M)` STRIP_ASSUME_TAC
  THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "W3" THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= a /\ &0 <= b ==> &0 <= &7 * a + &4 * b`) THEN
        REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE]
      THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&36 * &M * log(&2 * &M)) * (&Kw * W3) * &2 * P` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= W3 * P /\ W3 * P <= W3 * (&7 * L * S)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&2 * &M) * W3 * P <= log(&2 * &N) * W3 * (&7 * L * S)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&2 * &M) * W3 * P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&M * &Kw) * log(&2 * &M) * W3 * P <=
    &N * log(&2 * &N) * W3 * (&7 * L * S)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  EXPAND_TAC "X" THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Vinogradov's estimate.                                                    *)
(* ------------------------------------------------------------------------- *)

let TYPE2_X_POS = prove
 (`!U V N q. 1 <= q /\ &1 <= U /\ &1 <= V /\ 1 <= N
             ==> &0 <= &504 * &N * log(&2 * &N) * (&1 + log V) pow 3 *
                       (&1 + log(&q)) * (&N / &q + &N / U + &N / V + &q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log V /\ &0 <= log(&q) /\ &0 <= log(&2 * &N)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N / &q + &N / U + &N / V + &q` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c /\ &0 <= d ==> &0 <= a + b + c + d`) THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC);;

let VAUGHAN_EXP_S3_BOUND = prove
 (`!U V N alpha aa q.
     1 <= q /\ coprime(aa,q) /\ abs(alpha - &aa / &q) <= inv(&q pow 2) /\
     &1 <= U /\ &1 <= V /\ 1 <= N
     ==> norm(vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) *
                              vsum(1..N DIV m)
                               (\k. Cx(vaughan_e V k) *
                                    expi(&(m * k) * alpha))))
         <= (&2 * log(&N) + &1) *
            sqrt(&504 * &N * log(&2 * &N) * (&1 + log V) pow 3 *
                 (&1 + log(&q)) * (&N / &q + &N / U + &N / V + &q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`U:real`; `V:real`; `N:num`; `q:num`] TYPE2_X_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `R = sqrt(&504 * &N * log(&2 * &N) * (&1 + log V) pow 3 *
                       (&1 + log(&q)) * (&N / &q + &N / U + &N / V + &q))` THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `U:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `M0:num`)] THEN
  MP_TAC(SPEC `U:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= M0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &M0 + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&M0 = &0)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `U < &M0 + &1` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `N:num` EXISTS_LOG2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \m. Cx(mangoldt m - vaughan_F U m) *
                      vsum(1..N DIV m)
                       (\k. Cx(vaughan_e V k) * expi(&(m * k) * alpha))` THEN
  SUBGOAL_THEN `vsum(1..N) g = vsum(M0+1..M0 * 2 EXP (J + 1)) (g:num->complex)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `vsum(M0+1..N) (g:num->complex)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_SUPERSET THEN
      REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[vaughan_F] THEN
      SUBGOAL_THEN `&m <= U` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M0:real` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        REWRITE_TAC[REAL_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
      REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `N <= M0 * 2 EXP (J + 1)` MP_TAC THENL
         [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP (J + 1)` THEN
          CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
          REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
          ARITH_TAC];
        ALL_TAC] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN EXPAND_TAC "g" THEN
      SUBGOAL_THEN `N DIV m = 0` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC;
        REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH; COMPLEX_VEC_0;
                    COMPLEX_MUL_RZERO]]];
    ALL_TAC] THEN
  REWRITE_TAC[DYADIC_VSUM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..J) (\j. R)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    EXPAND_TAC "g" THEN EXPAND_TAC "R" THEN
    MATCH_MP_TAC TYPE2_BLOCK_FINAL THEN EXISTS_TAC `aa:num` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `M0:num` THEN
      ASM_REWRITE_TAC[LE_MULT_EXP2];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M0 + &1` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE; LE_MULT_EXP2]];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_LE_RADD] THEN
    MATCH_MP_TAC LOG2_BOUND THEN ASM_REWRITE_TAC[]]);;

let VINOGRADOV_LAMBDA_BOUND = prove
 (`!U V N alpha aa q.
     1 <= q /\ coprime(aa,q) /\ abs(alpha - &aa / &q) <= inv(&q pow 2) /\
     &1 <= U /\ &1 <= V /\ U * V <= &N
     ==> norm(vsum(1..N) (\n. Cx(mangoldt n) * expi(&n * alpha))) <=
         &18 * U +
         &1 * (&4 * log(&N)) *
         (&14 * &N / &q * (&1 + log(&N + &1)) +
          &8 * (V + &q) * (&1 + log(&q))) +
         log(&N) * &2 *
         (&14 * &N / &q * (&1 + log(&N + &1)) +
          &8 * (U * V + &q) * (&1 + log(&q))) +
         (&2 * log(&N) + &1) *
         sqrt(&504 * &N * log(&2 * &N) * (&1 + log V) pow 3 *
              (&1 + log(&q)) * (&N / &q + &N / U + &N / V + &q))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= U * V /\ V <= &N /\ 1 <= N` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `V <= U * V` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`U:real`; `V:real`] VAUGHAN_VSUM_GEN] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:complex) <= x /\ norm(b:complex) <= y /\ norm(c:complex) <= z /\
    norm(d:complex) <= w ==> norm(a + b - c + d) <= x + y + z + w`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC VAUGHAN_S0_BOUND THEN
    REWRITE_TAC[NORM_EXPI; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC VAUGHAN_EXP_S1_BOUND THEN EXISTS_TAC `aa:num` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC VAUGHAN_EXP_S2_BOUND THEN EXISTS_TAC `aa:num` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC VAUGHAN_EXP_S3_BOUND THEN EXISTS_TAC `aa:num` THEN
    ASM_REWRITE_TAC[]]);;
