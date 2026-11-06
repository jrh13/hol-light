(* ========================================================================= *)
(* Waring's problem: the Hardy-Littlewood bound G(k) <= 2^k + 1 (in Hua's    *)
(* form, Nathanson Theorem 5.7) and Hilbert's theorem as a corollary.        *)
(*   WARING_HARDY_LITTLEWOOD:                                                *)
(*     !k s. 2 <= k /\ 2 EXP k + 1 <= s                                      *)
(*           ==> ?N0. !N. N0 <= N                                            *)
(*                 ==> ?x. (!i. 1 <= i /\ i <= s ==> 1 <= x i) /\            *)
(*                         nsum(1..s) (\i. x i EXP k) = N                    *)
(*   WARING_COUNT_LOWER: the number of ordered representations of N as a     *)
(*   sum of s positive k-th powers is at least c N^(s/k - 1):                *)
(*     ?c N0. &0 < c /\                                                      *)
(*            !N. N0 <= N                                                    *)
(*                ==> c * &N rpow (&s / &k - &1) <=                          *)
(*                    &(CARD {x | (!i. 1 <= i /\ i <= s ==> 1 <= x i) /\     *)
(*                                (!i. ~(1 <= i /\ i <= s) ==> x i = 0) /\   *)
(*                                nsum(1..s) (\i. x i EXP k) = N})           *)
(*   HILBERT_WARING (Hilbert 1909):                                          *)
(*     !k. 1 <= k ==> ?g. !n. ?x. n = nsum(1..g) (\i. x i EXP k)             *)
(*   with g = 2^k + 1 + N0 (the n < N0 are sums of n ones).                  *)
(* Method.  Let P^k <= N < (P + 1)^k, M = s N + 1, Q^10 <= P < (Q + 1)^10    *)
(* and Kw = N DIV Q.  WARING_KEXP_CIRCLE writes M r(N), r(N) = waring_conv   *)
(* (waring_kpow k) N s N, as the sum of waring_kexp k P (j/M)^s e(-N j/M)    *)
(* over j < M.  On the major arcs (q <= Q) this is M J(N) waring_sing k s N  *)
(* Q up to explicit errors (waring_major.ml), with J(N) >= (1/k) 2^(-s(s+1)) *)
(* N^(s/k-1) and Re waring_sing >= c0 (WARING_SING_LOWER).  On the minor     *)
(* arcs Dirichlet's theorem and Weyl's inequality bound |waring_kexp k       *)
(* P|^(2^(k-1)), and Hua's lemma bounds the mean value of |waring_kexp k     *)
(* P|^(2^k) (WARING_MINOR_GEN, WARING_MINOR_POINT); WARING_CIRCLE_LOWER is   *)
(* the resulting explicit inequality and WARING_CIRCLE_SIMPLE its normalized *)
(* form.  With the divisor bound for the exponent 1/(40 k (k-1)(2^(k-1)+1))  *)
(* the minor arc term, raised to the power 2^(k-1), is at most C Q^(-1/4)    *)
(* (E3_SMALL), the other errors are at most C/Q, and WARING_FIXED gives      *)
(* r(N) >= c P^(s-k) for all large N.  WARING_CONV_KPOW_CARD identifies r(N) *)
(* with the number of representations.                                       *)
(* ========================================================================= *)

needs "Sieve/waring_singular.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Minor arcs and the circle-method inequality.                              *)
(* ------------------------------------------------------------------------- *)

let WARING_MINOR_GEN = prove
 (`!k P M Kw Q s W.
     2 <= k /\ 1 <= P /\ 2 EXP k + 1 <= s /\ 2 EXP (k - 1) * P EXP k < M /\
     &0 <= W /\
     (!j. j < M /\ ~(j IN circ_major M Kw Q)
          ==> norm(waring_kexp k P (&j / &M)) pow (2 EXP (k - 1)) <= W)
     ==> sum {j | j < M /\ ~(j IN circ_major M Kw Q)}
             (\j. norm(waring_kexp k P (&j / &M)) pow s)
         <= &P pow (s - 2 EXP k - 1) * root (2 EXP (k - 1)) W *
            &M * waring_hua k P k`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Kq = 2 EXP (k - 1)` THEN
  SUBGOAL_THEN `~(Kq = 0) /\ 2 EXP k = 2 * Kq` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kq" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < M /\ ~(j IN circ_major M Kw Q)
        ==> norm(waring_kexp k P (&j / &M)) <= root Kq W`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ROOT_MONO_LE) THEN
    DISCH_THEN(MP_TAC o SPEC `Kq:num`) THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
    MATCH_MP_TAC REAL_ROOT_POW THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= root Kq W` ASSUME_TAC THENL
   [MATCH_MP_TAC ROOT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {j | j < M /\ ~(j IN circ_major M Kw Q)}
        (\j. &P pow (s - 2 EXP k - 1) * root Kq W *
             norm(waring_kexp k P (&j / &M)) pow (2 * Kq))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < M:num}` THEN
      SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `norm(waring_kexp k P (&j / &M)) pow s =
      norm(waring_kexp k P (&j / &M)) pow (s - 2 EXP k - 1) *
      norm(waring_kexp k P (&j / &M)) *
      norm(waring_kexp k P (&j / &M)) pow (2 * Kq)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 real_pow); GSYM REAL_POW_ADD] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE; REAL_LE_MUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[NORM_POS_LE; WARING_KEXP_TRIVIAL];
      MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC]) THEN
  MP_TAC(SPECL [`k:num`; `P:num`; `Kq:num`; `M:num`; `0`]
           WARING_KEXP_CORR) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; REAL_MUL_RZERO; EXPI_0; RE_CX;
                  REAL_MUL_LID] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `sum {t | t < M} (\t. norm(waring_kexp k P (&t / &M)) pow (2 * Kq))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[FINITE_NUMSEG_LT; REAL_POW_LE; NORM_POS_LE] THEN SET_TAC[];
    ASM_REWRITE_TAC[waring_hua; REAL_POW_2; REAL_LE_REFL]]);;

let WARING_MINOR_POINT = prove
 (`!k P M Kw Q B j.
     2 <= k /\ 1 <= P /\ 1 <= Q /\ Q < Kw /\ &0 <= B /\
     (!m. 1 <= m /\ m <= P EXP (k - 1) ==> &(CARD {d | d divides m}) <= B) /\
     j < M /\ ~(j IN circ_major M Kw Q)
     ==> norm(waring_kexp k P (&j / &M)) pow (2 EXP (k - 1)) <=
         (&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k *
         (&(k - 1) * &P pow (k - 1) +
          B pow (k - 1) *
          (&7 * &P * &(FACT k * P EXP (k - 1)) / &Q +
           &4 * &(FACT k * P EXP (k - 1)) * (&1 + log(&Kw)) +
           &7 * &P + &4 * &Kw * (&1 + log(&Kw))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`; `j:num`] MINOR_DIRICHLET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `q:num`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k *
    (&(k - 1) * &P pow (k - 1) +
     B pow (k - 1) * (&(FACT k * P EXP (k - 1)) / &q + &1) *
     (&7 * &P + &4 * &q * (&1 + log(&q))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WEYL_EXPLICIT THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &Q /\ &Q <= &q /\ &q <= &Kw` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_MUL]; ALL_TAC]) THEN
  REWRITE_TAC[REAL_LE_LADD] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  ABBREV_TAC `A = &(FACT k * P EXP (k - 1))` THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&q) /\ log(&q) <= log(&Kw)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A / &q + &1) * (&7 * &P + &4 * &q * (&1 + log(&q))) =
                &7 * &P * A / &q + &4 * A * (&1 + log(&q)) +
                &7 * &P + &4 * &q * (&1 + log(&q))` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < &q` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= a' /\ b <= b' /\ d <= d' ==> a + b + c + d <= a' + b' + c + d'`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let RE_CHAIN_LOWER = prove
 (`!a x y m:complex.
     Re y - norm(a - x) - norm(x - y) - norm m <= Re a + Re m`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `a - x:complex` COMPLEX_NORM_GE_RE_IM) THEN
  MP_TAC(SPEC `x - y:complex` COMPLEX_NORM_GE_RE_IM) THEN
  MP_TAC(SPEC `m:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN REAL_ARITH_TAC);;

let WARING_CIRCLE_LOWER = prove
 (`!k S N P Q Kw M B c0 CT Ch.
     2 <= k /\ 2 EXP k + 1 <= S /\ 1 <= P /\
     P EXP k <= N /\ N < (P + 1) EXP k /\ S * N < M /\
     1 <= Q /\ 2 * Q EXP 2 < Kw /\ Kw <= M /\ 2 EXP S <= N /\
     &0 <= c0 /\ c0 <= Re(waring_sing k S N Q) /\ &1 <= B /\
     sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                        (\a. norm(Cx(inv(&q)) * waring_csum k q a) pow
                               S)) <= CT /\
     waring_hua k P k <= Ch * B pow (k - 1) * &P pow (2 EXP k - k) /\
     (!m. 1 <= m /\ m <= P EXP (k - 1) ==> &(CARD {d | d divides m}) <= B)
     ==> &M * c0 * (inv(&k) * inv(&2) pow (S * (S + 1)) *
                    root k (&N) pow S / &N) -
         &Q * &Q * (&3 * (&2 * &M / &Kw + &1)) *
         (&S * (&P + &1) pow (S - 1) *
          (&2 * &Q * (&1 + &2 * pi * &N / &Kw))) -
         (&4 pow (2 * k) * root k (&N) pow (S - 2 * k) *
          (&18 * &M * &Kw)) * CT -
         &P pow (S - 2 EXP k - 1) *
         root (2 EXP (k - 1))
          ((&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k *
           (&(k - 1) * &P pow (k - 1) +
            B pow (k - 1) *
            (&7 * &P * &(FACT k * P EXP (k - 1)) / &Q +
             &4 * &(FACT k * P EXP (k - 1)) * (&1 + log(&Kw)) +
             &7 * &P + &4 * &Kw * (&1 + log(&Kw))))) *
         &M * (Ch * B pow (k - 1) * &P pow (2 EXP k - k))
         <= &M * waring_conv (waring_kpow k) N S N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 * k <= S /\ 1 <= k /\ 1 <= S /\ N < M:num`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` DOUBLE_LE_POW2) THEN
    SUBGOAL_THEN `N <= S * N:num` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `N = 1 * N`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S:num`; `P:num`; `N:num`; `M:num`; `&0`]
    WARING_KEXP_CIRCLE) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN REWRITE_TAC[RE_CX] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC
    `F0 = \j. waring_kexp k P (&j / &M) pow S * expi(--(&N * &j / &M))` THEN
  SUBGOAL_THEN
   `vsum {j | j < M} (F0:num->complex) =
    vsum (circ_major M Kw Q) F0 +
    vsum {j | j < M /\ ~(j IN circ_major M Kw Q)} F0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(COMPLEX_RING `c = a - b ==> a = b + c:complex`) THEN
    SUBGOAL_THEN `{j | j < M /\ ~(j IN circ_major M Kw Q)} =
                  {j | j < M} DIFF circ_major M Kw Q` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC VSUM_DIFF THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; CIRC_MAJOR_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[RE_ADD] THEN
  ABBREV_TAC `Wm = (&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k *
           (&(k - 1) * &P pow (k - 1) +
            B pow (k - 1) *
            (&7 * &P * &(FACT k * P EXP (k - 1)) / &Q +
             &4 * &(FACT k * P EXP (k - 1)) * (&1 + log(&Kw)) +
             &7 * &P + &4 * &Kw * (&1 + log(&Kw))))` THEN
  SUBGOAL_THEN `&0 <= Wm` ASSUME_TAC THENL
   [EXPAND_TAC "Wm" THEN
    SUBGOAL_THEN `&0 <= log(&Kw)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_MUL] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= B ==> &0 <= B`] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_LE_MUL;
                 REAL_ARITH `&0 <= x ==> &0 <= &1 + x`];
    ALL_TAC] THEN
  ALL_TAC THEN
  SUBGOAL_THEN `Q < Kw:num /\ &0 <= B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(SPEC `Q:num` LE_SQUARE_REFL) THEN REWRITE_TAC[EXP_2] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vsum {j | j < M /\ ~(j IN circ_major M Kw Q)} (F0:num->complex)) <=
    &P pow (S - 2 EXP k - 1) * root (2 EXP (k - 1)) Wm * &M *
    (Ch * B pow (k - 1) * &P pow (2 EXP k - k))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {j | j < M /\ ~(j IN circ_major M Kw Q)}
                    (\j. norm(waring_kexp k P (&j / &M)) pow S)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < M:num}` THEN
        SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
        EXPAND_TAC "F0" THEN
        REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; NORM_EXPI;
                    REAL_MUL_RID; REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&P pow (S - 2 EXP k - 1) * root (2 EXP (k - 1)) Wm *
                &M * waring_hua k P k` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WARING_MINOR_GEN THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `S * N:num` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_MULT2 THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC `2 EXP k` THEN CONJ_TAC THENL
         [MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC;
          ASM_ARITH_TAC];
        REPEAT STRIP_TAC THEN EXPAND_TAC "Wm" THEN
        MATCH_MP_TAC WARING_MINOR_POINT THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; ROOT_POS_LE]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `X = vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
         (\a. vsum (circ_arc M Kw q a)
           (\j. (Cx(inv(&q)) * waring_csum k q a *
                 waring_vsm k N (&j / &M - &a / &q)) pow S *
                expi(--(&N * &j / &M)))))` THEN
  MP_TAC(SPECL [`k:num`; `P:num`; `N:num`; `M:num`; `Kw:num`; `Q:num`;
                `S:num`] WARING_MAJOR_APPROX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `M:num`; `Kw:num`; `Q:num`; `S:num`]
    WARING_MAJOR_MAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ALL_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `S:num`; `N:num`] JCONV_LOWER) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  ABBREV_TAC `J = waring_conv (waring_klam k) N S N` THEN
  ABBREV_TAC `Jl = inv(&k) * inv(&2) pow (S * (S + 1)) *
                   root k (&N) pow S / &N` THEN
  SUBGOAL_THEN `&0 <= Jl` ASSUME_TAC THENL
   [EXPAND_TAC "Jl" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_POW_LE; REAL_LE_DIV;
             ROOT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&M * c0 * Jl <= Re(Cx(&M * J) * waring_sing k S N Q)`
  ASSUME_TAC THENL
   [REWRITE_TAC[RE_MUL_CX] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&M * c0) * J` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
        GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `(m * c) * j = (m * j) * c:real`]
          THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vsum (circ_major M Kw Q) (F0:num->complex)`; `X:complex`;
                 `Cx(&M * J) * waring_sing k S N Q`;
                 `vsum {j | j < M /\ ~(j IN circ_major M Kw Q)}
                       (F0:num->complex)`] RE_CHAIN_LOWER) THEN
  SUBGOAL_THEN
   `(&4 pow (2 * k) * root k (&N) pow (S - 2 * k) * (&18 * &M * &Kw)) *
    sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                       (\a. norm(Cx(inv(&q)) * waring_csum k q a) pow S)) <=
    (&4 pow (2 * k) * root k (&N) pow (S - 2 * k) * (&18 * &M * &Kw)) * CT`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS; ROOT_POS_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `&M * c0 * Jl <= Re(Cx(&M * J) * waring_sing k S N Q)` THEN
  UNDISCH_TAC
   `norm(vsum {j | j < M /\ ~(j IN circ_major M Kw Q)} (F0:num->complex)) <=
    &P pow (S - 2 EXP k - 1) * root (2 EXP (k - 1)) Wm * &M *
    (Ch * B pow (k - 1) * &P pow (2 EXP k - k))` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `X:complex`)) (concl th) &&
    can (find_term ((=) `waring_sing k S N Q`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `X:complex`)) (concl th) &&
    can (find_term ((=) `vsum (circ_major M Kw Q) (F0:num->complex)`))
        (concl th))) THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!t y n1 e1 n2 x2 e2 n3 e3 ra rm:real.
      n1 <= e1 ==> n2 <= x2 ==> n3 <= e3 ==> t <= y ==> x2 <= e2 ==>
      y - n1 - n2 - n3 <= ra + rm ==> t - e1 - e2 - e3 <= ra + rm`));;

(* ------------------------------------------------------------------------- *)
(* The error terms.                                                          *)
(* ------------------------------------------------------------------------- *)

let ROOT_BOUNDS_P = prove
 (`!k N P. 1 <= k /\ P EXP k <= N /\ N < (P + 1) EXP k
           ==> &P <= root k (&N) /\ root k (&N) <= &P + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!x y. a = root k x /\ root k x <= root k (&N) /\
                           root k (&N) <= root k y /\ root k y = b
                           ==> a <= root k (&N) /\ root k (&N) <= b`) THEN
  EXISTS_TAC `&P pow k` THEN EXISTS_TAC `(&P + &1) pow k` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_ROOT_POW THEN
    ASM_REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE];
    MATCH_MP_TAC ROOT_MONO_LE THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_ROOT_POW THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let N_LE_POW_P = prove
 (`!k N P. 1 <= P /\ N < (P + 1) EXP k ==> &N <= &2 pow k * &P pow k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&P + &1) pow k` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN
    SUBGOAL_THEN `&1 <= &P` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC]]);;

let BOUND_MAIN_TERM = prove
 (`!k S N P. 1 <= k /\ k <= S /\ 1 <= P /\ P EXP k <= N /\ N < (P + 1) EXP k
             ==> &P pow (S - k) * inv(&2 pow k) <= root k (&N) pow S / &N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`] ROOT_BOUNDS_P) THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`] N_LE_POW_P) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `P EXP k` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; EXP_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&P pow (S - k) * inv(&2 pow k)) * (&2 pow k * &P pow k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&P pow (S - k) * inv(&2 pow k)) * (&2 pow k * &P pow k) =
                &P pow S` SUBST1_TAC THENL
   [SUBGOAL_THEN `&P pow S = &P pow (S - k) * &P pow k` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(&2 pow k = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS]]);;

let BOUND_E1 = prove
 (`!k S N P Q Kw.
     2 <= k /\ 2 EXP k + 1 <= S /\ 1 <= P /\ P EXP k <= N /\
     N < (P + 1) EXP k /\ 1 <= Q /\ 1 <= Kw /\ N <= 2 * Q * Kw
     ==> &Q * &Q * (&3 * (&2 * &(S * N + 1) / &Kw + &1)) *
         (&S * (&P + &1) pow (S - 1) *
          (&2 * &Q * (&1 + &2 * pi * &N / &Kw))) <=
         &(S * N + 1) * &P pow (S - k) *
         (&510 * &(S + 1) * &2 pow (S - 1) * &Q pow 5 / &P)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Kw /\ &1 <= &Q /\ &1 <= &P /\ &1 <= &N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `1 <= P EXP k` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N <= &2 * &Q * &Kw` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&3 * (&2 * &(S * N + 1) / &Kw + &1) <= &15 * &(S + 1) * &Q`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH
     `&0 < k ==> (&3 * (&2 * x / k + &1) <= y <=> &6 * x / k <= y - &3)`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH
     `&6 * x / k = (&6 * x) / k`] THEN
    SUBGOAL_THEN `&S * &N <= &2 * (&S * &Q * &Kw) /\ &Kw <= &Q * &Kw /\
                  &1 <= &S * &Q * &Kw /\ &1 <= &Q * &Kw` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_ARITH `&2 * (s * q * k) = s * (&2 * q * k)`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
        REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
        REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
        ASM_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &2 * pi * &N / &Kw <= &17 * &Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&N / &Kw <= &2 * &Q` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC PI_BOUNDS_CRUDE THEN
    SUBGOAL_THEN `&0 <= &N / &Kw` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    SPEC_TAC(`&N / &Kw`,`x:real`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `pi * x <= &4 * (&2 * &Q)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&P + &1) pow (S - 1) <= &2 pow (S - 1) * &P pow (S - 1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3 * (&2 * &(S * N + 1) / &Kw + &1) /\
                &0 <= &1 + &2 * pi * &N / &Kw`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &3 * (&2 * x + &1)`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + &2 * x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[PI_POS_LE; REAL_LE_DIV;
        REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&Q * &Q * (&15 * &(S + 1) * &Q) *
              (&S * (&2 pow (S - 1) * &P pow (S - 1)) *
               (&2 * &Q * (&17 * &Q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_ARITH `&0 <= &P + &1`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&S * &P pow k <= &(S * N + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= b + 1:num`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&P pow (S - 1) * &P = &P pow (S - k) * &P pow k`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_POW_1] THEN
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`2 <= k`; `2 EXP k + 1 <= S`] THEN
    MP_TAC(SPEC `k:num` LT_POW2_REFL) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(S * N + 1) * &P pow (S - k) *
                (&510 * &(S + 1) * &2 pow (S - 1) * &Q pow 5 / &P) =
                (&(S * N + 1) * &P pow (S - k) *
                 (&510 * &(S + 1) * &2 pow (S - 1) * &Q pow 5)) / &P`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&S * &P pow k) * &P pow (S - k) *
    (&510 * &(S + 1) * &2 pow (S - 1) * &Q pow 5)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC(REAL_RING
     `!q s t a b c d p:real. a * p = b * c
        ==> (q * q * (&15 * t * q) * s * (d * a) * &2 * q * &17 * q) * p =
            (s * c) * b * (&510 * t * d * q pow 5)`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE]]);;

let BOUND_E2 = prove
 (`!k S N P Q Kw M CT.
     2 <= k /\ 2 EXP k + 1 <= S /\ 1 <= P /\ P EXP k <= N /\
     N < (P + 1) EXP k /\ 1 <= Q /\ Q * Kw <= N /\ &0 <= CT
     ==> (&4 pow (2 * k) * root k (&N) pow (S - 2 * k) *
          (&18 * &M * &Kw)) * CT <=
         &M * &P pow (S - k) *
         (&4 pow (2 * k) * &2 pow (S - k) * &18 * CT / &Q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`] ROOT_BOUNDS_P) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&1 <= &P /\ &1 <= &Q` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `2 * k <= S` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 * k <= 2 EXP k` MP_TAC THENL
     [SPEC_TAC(`k:num`,`n:num`) THEN INDUCT_TAC THEN
      REWRITE_TAC[EXP; ARITH] THEN
      MP_TAC(SPEC `n:num` LT_POW2_REFL) THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&Kw <= (&2 pow k * &P pow k) / &Q` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    TRANS_TAC REAL_LE_TRANS `&N` THEN
    ASM_SIMP_TAC[N_LE_POW_P] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `root k (&N) pow (S - 2 * k) <=
                &2 pow (S - 2 * k) * &P pow (S - 2 * k)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&4 pow (2 * k) * (&2 pow (S - 2 * k) * &P pow (S - 2 * k)) *
     &18 * &M * ((&2 pow k * &P pow k) / &Q)) * CT` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow (S - k) = &2 pow (S - 2 * k) * &2 pow k /\
                &P pow (S - k) = &P pow (S - 2 * k) * &P pow k`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[real_div; REAL_MUL_AC; REAL_LE_REFL]]);;

let BRACKET_GENERIC = prove
 (`!c kk Fk A L X P1 p w t.
     &0 <= c /\ c <= kk /\ &1 <= A /\ &1 <= L /\ &0 <= P1 /\ P1 <= X /\
     p <= X /\ w <= t * X /\ &0 <= Fk
     ==> c * P1 + A * (&7 * Fk * X + &4 * (Fk * P1) * L + &7 * p +
                       &4 * w * L)
         <= (kk + &11 * Fk + &7 + &4 * t) * (A * L * X)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (kk - c) * (A * L * X) /\
                &0 <= c * ((A * L - &1) * X) /\ &0 <= c * (X - P1) /\
                &0 <= Fk * A * X * (L - &1) /\ &0 <= Fk * A * L * (X - P1) /\
                &0 <= A * (L - &1) * X /\ &0 <= A * (X - p) /\
                &0 <= A * L * (t * X - w)`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 <= X /\ &0 <= A /\ &0 <= L /\ &1 <= A * L`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let BOUND_W = prove
 (`!k N P Q Kw B.
     2 <= k /\ 1 <= P /\ 1 <= Q /\ Q <= P /\ 1 <= Kw /\ Q * Kw <= N /\
     N < (P + 1) EXP k /\ &1 <= B
     ==> (&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k *
         (&(k - 1) * &P pow (k - 1) +
          B pow (k - 1) *
          (&7 * &P * &(FACT k * P EXP (k - 1)) / &Q +
           &4 * &(FACT k * P EXP (k - 1)) * (&1 + log(&Kw)) +
           &7 * &P + &4 * &Kw * (&1 + log(&Kw)))) <=
         (&2 * &P) pow (2 EXP (k - 1)) *
         (B pow (k - 1) * (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
          (&1 + log(&Kw)) / &Q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &P /\ &1 <= &Q /\ &Q <= &P /\ &1 <= &Kw`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&Kw <= &2 pow k * &P pow k / &Q` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x:real`] THEN
    TRANS_TAC REAL_LE_TRANS `&N` THEN
    ASM_SIMP_TAC[N_LE_POW_P] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&P pow k = &P * &P pow (k - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &P pow (k - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&P pow (k - 1) <= &P pow k / &Q /\ &P <= &P pow k / &Q`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `&P` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&7 * &P * &(FACT k * P EXP (k - 1)) / &Q =
                &7 * &(FACT k) * &P pow k / &Q /\
                &(FACT k * P EXP (k - 1)) = &(FACT k) * &P pow (k - 1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div; REAL_MUL_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k *
              ((&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
               (B pow (k - 1) * (&1 + log(&Kw)) * (&P pow k / &Q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC BRACKET_GENERIC THEN ASM_REWRITE_TAC[REAL_POS] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(&2 * &P) pow (2 EXP (k - 1)) =
                  (&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k * &P pow k`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
      MP_TAC(SPEC `k - 1` LT_POW2_REFL) THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div; REAL_MUL_AC]]]);;

let BOUND_E3 = prove
 (`!k S P M B Ch W Y.
     2 <= k /\ 2 EXP k + 1 <= S /\ 1 <= P /\ &0 <= Ch /\ &1 <= B /\
     &0 <= Y /\ W <= (&2 * &P) pow (2 EXP (k - 1)) * Y
     ==> &P pow (S - 2 EXP k - 1) * root (2 EXP (k - 1)) W * &M *
         (Ch * B pow (k - 1) * &P pow (2 EXP k - k)) <=
         &M * &P pow (S - k) *
         (&2 * Ch * B pow (k - 1) * root (2 EXP (k - 1)) Y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `root (2 EXP (k - 1)) W <= &2 * &P * root (2 EXP (k - 1)) Y`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `root (2 EXP (k - 1)) ((&2 * &P) pow (2 EXP (k - 1)) * Y)` THEN
    ASM_SIMP_TAC[ROOT_MONO_LE; REAL_ROOT_MUL] THEN
    SUBGOAL_THEN `root (2 EXP (k - 1)) ((&2 * &P) pow (2 EXP (k - 1))) =
                  &2 * &P`
     (fun th -> REWRITE_TAC[th; REAL_MUL_ASSOC; REAL_LE_REFL]) THEN
    MATCH_MP_TAC REAL_ROOT_POW THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&P pow (S - k) =
                &P pow (S - 2 EXP k - 1) * &P * &P pow (2 EXP k - k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow); GSYM REAL_POW_ADD] THEN
    AP_TERM_TAC THEN MP_TAC(SPEC `k:num` LT_POW2_REFL) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &P pow (S - 2 EXP k - 1) /\
                &0 <= &P pow (2 EXP k - k) /\ &0 <= B pow (k - 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `&P pow (S - 2 EXP k - 1) * (&2 * &P * root (2 EXP (k - 1)) Y) * &M *
    (Ch * B pow (k - 1) * &P pow (2 EXP k - k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_MUL_AC]]);;

let CIRCLE_CHAIN = prove
 (`!m w x a b1 b2 b3 main f1 f2 f3:real.
     &0 < m
     ==> m * (x * a) <= main
     ==> f3 <= m * (x * b3)
     ==> f2 <= m * (x * b2)
     ==> f1 <= m * (x * b1)
     ==> main - f1 - f2 - f3 <= m * w
     ==> x * (a - b1 - b2 - b3) <= w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(m:real) * (x * (a - b1 - b2 - b3)) <= m * w` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

let WARING_CIRCLE_SIMPLE = prove
 (`!k S N P Q Kw B c0 CT Ch.
     2 <= k /\ 2 EXP k + 1 <= S /\ 1 <= P /\
     P EXP k <= N /\ N < (P + 1) EXP k /\
     1 <= Q /\ Q <= P /\ 2 * Q EXP 2 < Kw /\ Q * Kw <= N /\
     N <= 2 * Q * Kw /\ 2 EXP S <= N /\
     &0 <= c0 /\ c0 <= Re(waring_sing k S N Q) /\ &1 <= B /\ &0 <= CT /\
     &0 <= Ch /\
     sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                        (\a. norm(Cx(inv(&q)) * waring_csum k q a) pow
                               S)) <= CT /\
     waring_hua k P k <= Ch * B pow (k - 1) * &P pow (2 EXP k - k) /\
     (!m. 1 <= m /\ m <= P EXP (k - 1) ==> &(CARD {d | d divides m}) <= B)
     ==> &P pow (S - k) *
         (c0 * inv(&k) * inv(&2) pow (S * (S + 1)) * inv(&2 pow k) -
          &510 * &(S + 1) * &2 pow (S - 1) * &Q pow 5 / &P -
          &4 pow (2 * k) * &2 pow (S - k) * &18 * CT / &Q -
          &2 * Ch * B pow (k - 1) *
          root (2 EXP (k - 1))
           (B pow (k - 1) * (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
            (&1 + log(&Kw)) / &Q))
         <= waring_conv (waring_kpow k) N S N`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= Kw /\ k <= S:num` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` LT_POW2_REFL) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`; `Q:num`; `Kw:num`; `B:real`]
               BOUND_W) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S:num`; `N:num`; `P:num`; `Q:num`; `Kw:num`;
                `S * N + 1`; `B:real`; `c0:real`; `CT:real`; `Ch:real`]
               WARING_CIRCLE_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE
     `1 * Kw <= Q * Kw /\ Q * Kw <= N /\ 1 * N <= S * N
      ==> S * N < S * N + 1 /\ Kw <= S * N + 1:num`) THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S:num`; `N:num`; `P:num`; `Q:num`; `Kw:num`]
               BOUND_E1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S:num`; `N:num`; `P:num`; `Q:num`; `Kw:num`;
                `S * N + 1`; `CT:real`] BOUND_E2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL
   [`k:num`; `S:num`; `P:num`; `S * N + 1`; `B:real`; `Ch:real`;
    `(&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k *
     (&(k - 1) * &P pow (k - 1) +
      B pow (k - 1) *
      (&7 * &P * &(FACT k * P EXP (k - 1)) / &Q +
       &4 * &(FACT k * P EXP (k - 1)) * (&1 + log(&Kw)) +
       &7 * &P + &4 * &Kw * (&1 + log(&Kw))))`;
    `B pow (k - 1) * (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
     (&1 + log(&Kw)) / &Q`] BOUND_E3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ &0 <= b /\ &0 <= c
        ==> &0 <= a + &11 * b + &7 + &4 * c`) THEN
      SIMP_TAC[REAL_POS; REAL_POW_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S:num`; `N:num`; `P:num`] BOUND_MAIN_TERM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&(S * N + 1) *
    (&P pow (S - k) *
     (c0 * inv(&k) * inv(&2) pow (S * (S + 1)) * inv(&2 pow k))) <=
    &(S * N + 1) * c0 * (inv(&k) * inv(&2) pow (S * (S + 1)) *
                         root k (&N) pow S / &N)`
  MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `&(S * N + 1) * c0 * inv(&k) * inv(&2) pow (S * (S + 1)) *
      (&P pow (S - k) * inv(&2 pow k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_MUL_AC];
      REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
        [ASM_SIMP_TAC[REAL_POS; REAL_LE_INV_EQ; REAL_POW_LE]; ALL_TAC]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ARITH_RULE `0 < S * N + 1`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  MATCH_ACCEPT_TAC CIRCLE_CHAIN);;

(* ------------------------------------------------------------------------- *)
(* The parameters.                                                           *)
(* ------------------------------------------------------------------------- *)

let NUM_KTH_ROOT = prove
 (`!k n. 1 <= k ==> ?m. m EXP k <= n /\ n < (m + 1) EXP k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\m. n < (m + 1) EXP k` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `(n + 1) EXP 1` THEN CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[EXP_ZERO] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `m - 1`) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> m - 1 < m /\ m - 1 + 1 = m`;
                   NOT_LT]]]);;

let CT_BOUND = prove
 (`!k S. 2 <= k /\ 2 EXP k + 1 <= S
         ==> ?CT. &0 <= CT /\
                  !Q. sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                          (\a. norm(Cx(inv(&q)) * waring_csum k q a)
                                 pow S)) <= CT`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `S:num`] WARING_CSUM_ABS_DECAY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CA:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CA * (&1 + &(2 EXP k))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `Q:num` THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..Q) (\q. CA * &q rpow (--(inv(&(2 EXP k)) + &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `inv(&(2 EXP k)) + &1 = &1 + inv(&(2 EXP k))`]
      THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `Q = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `~(Q = 0) ==> 1 <= Q`] THEN
  REWRITE_TAC[RPOW_ONE] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
  MP_TAC(SPECL [`1`; `Q:num`; `inv(&(2 EXP k))`] SUM_RPOW_TAIL) THEN
  REWRITE_TAC[RPOW_ONE; REAL_LT_INV_EQ; REAL_OF_NUM_LT; EXP_LT_0; ARITH] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_INV_INV]);;

let E1_SMALL = prove
 (`!K1 P Q. &0 <= K1 /\ 1 <= Q /\ Q EXP 10 <= P
            ==> K1 * &Q pow 5 / &P <= K1 / &Q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &Q /\ &Q pow 10 <= &P` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&Q pow 10` THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&1 <= x ==> &0 < x`];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
  TRANS_TAC REAL_LE_TRANS `&Q pow 5 * inv(&Q pow 10)` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&1 <= x ==> &0 < x`];
    SUBGOAL_THEN `&Q pow 5 * inv(&Q pow 10) = inv(&Q pow 5)` SUBST1_TAC THENL
     [MP_TAC(ASSUME `&1 <= &Q`) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let B_POW_BOUND = prove
 (`!k a Ce P Q.
     1 <= k /\ ~(a = 0) /\ 1 <= P /\ 1 <= Q /\ P < (Q + 1) EXP 10 /\
     &0 <= Ce
     ==> (Ce * &(P EXP k) rpow inv(&(40 * k * a))) pow a <=
         Ce pow a * (&2 * &Q rpow inv(&4))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  SUBGOAL_THEN `&0 < &(P EXP k) /\ &1 <= &Q /\ &0 < &P` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[EXP_LT_0; ARITH_RULE `0 < P <=> 1 <= P`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_POW_MUL] THEN
  SUBGOAL_THEN `&a * inv(&(40 * k * a)) = inv(&40) * inv(&k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&a = &0) /\ ~(&k = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM RPOW_POW] THEN
  ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `&k * inv(&40) * inv(&k) = inv(&40)` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&P <= (&2 * &Q) pow 10` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `(Q + 1) EXP 10` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `((&2 * &Q) pow 10) rpow inv(&40)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM RPOW_POW] THEN
  SIMP_TAC[RPOW_RPOW; REAL_LE_MUL; REAL_POS] THEN
  REWRITE_TAC[REAL_ARITH `&10 * inv(&40) = inv(&4)`; RPOW_MUL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[RPOW_POS_LE; REAL_POS] THEN
  TRANS_TAC REAL_LE_TRANS `&2 rpow &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_MONO_LE THEN REAL_ARITH_TAC;
    REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]]);;

let LOG_KW_BOUND = prove
 (`!k N P Q Kw.
     1 <= k /\ 1 <= Kw /\ Kw <= N /\ N < (P + 1) EXP k /\
     P < (Q + 1) EXP 10 /\ 1 <= Q
     ==> &1 + log(&Kw) <= (&1 + &50 * &k) * &Q rpow inv(&4)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &Q rpow inv(&4)` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_LE_1 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&Q) <= &4 * &Q rpow inv(&4)` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(&Q) = &4 * log(&Q rpow inv(&4))` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < Q <=> 1 <= Q`];
        ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_RPOW] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= r - &1 ==> &4 * x <= &4 * r`) THEN
    MP_TAC(SPEC `&Q rpow inv(&4) - &1` LOG_LE) THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; REAL_ARITH `&1 + (x - &1) = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&Kw <= (&2 * &Q) pow (10 * k)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    TRANS_TAC LE_TRANS `N:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `(P + 1) EXP k` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
    TRANS_TAC LE_TRANS `(Q + 1) EXP 10` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&Kw) <= &10 * &k * (log(&2) + log(&Q))` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `log((&2 * &Q) pow (10 * k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < Q <=> 1 <= Q`];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * &Q` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_POW] THEN
    SUBGOAL_THEN `log(&2 * &Q) = log(&2) + log(&Q)` SUBST1_TAC THENL
     [MATCH_MP_TAC LOG_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` LOG_LE) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&k * (log(&2) + log(&Q)) <= &k * (&1 + &4 * &Q rpow inv(&4)) /\
                &k <= &k * &Q rpow inv(&4)`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ASM_REAL_ARITH_TAC]);;

let E3_ROOT_BOUND = prove
 (`!k Ch B KW L Q eps.
     2 <= k /\ &0 <= Ch /\ &1 <= B /\ &0 <= KW /\ &0 <= L /\ 1 <= Q /\
     &0 <= eps /\
     (&2 * Ch) pow (2 EXP (k - 1)) * KW *
     B pow ((k - 1) * (2 EXP (k - 1) + 1)) * L / &Q <=
     eps pow (2 EXP (k - 1))
     ==> &2 * Ch * B pow (k - 1) *
         root (2 EXP (k - 1)) (B pow (k - 1) * KW * L / &Q) <= eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(2 EXP (k - 1) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * Ch * B pow (k - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * Ch * B pow (k - 1) *
    root (2 EXP (k - 1)) (B pow (k - 1) * KW * L / &Q) =
    root (2 EXP (k - 1))
     ((&2 * Ch * B pow (k - 1)) pow (2 EXP (k - 1)) *
      (B pow (k - 1) * KW * L / &Q))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ROOT_MUL] THEN ASM_SIMP_TAC[REAL_ROOT_POW] THEN
    REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ROOT_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= b ==> x = a ==> x <= b`)) THEN
  REWRITE_TAC[REAL_POW_MUL; LEFT_ADD_DISTRIB; MULT_CLAUSES; REAL_POW_ADD;
              GSYM REAL_POW_POW] THEN
  REWRITE_TAC[real_div; REAL_POW_1; REAL_MUL_AC]);;

let RPOW_QUARTER = prove
 (`!Q. 1 <= Q
       ==> &Q rpow inv(&4) * &Q rpow inv(&4) / &Q <= &Q rpow (--inv(&4))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < Q <=> 1 <= Q`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &Q rpow inv(&4) /\
                &Q = (&Q rpow inv(&4)) pow 4 /\
                &Q rpow (--inv(&4)) = inv(&Q rpow inv(&4))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_SIMP_TAC[RPOW_POW_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[RPOW_POW; REAL_POW_1];
      REWRITE_TAC[RPOW_NEG]];
    ALL_TAC] THEN
  SPEC_TAC(`&Q rpow (--inv(&4))`,`s:real`) THEN
  SPEC_TAC(`&Q rpow inv(&4)`,`r:real`) THEN
  SPEC_TAC(`&Q`,`q:real`) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r * r / r pow 4 = inv r * inv(r:real)` SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= r:real` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_INV_LE_1;
               REAL_ARITH `&1 <= r ==> &0 <= r`]);;

let MONO_PRODUCT4 = prove
 (`!x kw ba bb l lb q.
     &0 <= x /\ &0 <= kw /\ &0 <= ba /\ ba <= bb /\ &0 <= l /\ l <= lb /\
     &0 < q
     ==> x * kw * ba * l / q <= x * kw * bb * lb / q`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_DIV; REAL_LT_IMP_LE]);;

let SCALE_BELOW_ONE = prove
 (`!z x. &0 <= z /\ &0 <= x ==> z * x / (z + &1) <= x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [REAL_ARITH `!z x y:real. z * x / y = (z * x) / y`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= z ==> &0 < z + &1`] THEN
  ASM_REAL_ARITH_TAC);;

let E3_SMALL = prove
 (`!k N P Q Kw Ce Ch eps.
     2 <= k /\ 1 <= P /\ 1 <= Q /\ P < (Q + 1) EXP 10 /\ 1 <= Kw /\
     Kw <= N /\ N < (P + 1) EXP k /\ &1 <= Ce /\ &0 <= Ch /\ &0 < eps /\
     &Q rpow (--inv(&4)) <=
     eps pow (2 EXP (k - 1)) /
     ((&2 * Ch) pow (2 EXP (k - 1)) *
      (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
      (Ce pow ((k - 1) * (2 EXP (k - 1) + 1)) * &2) *
      (&1 + &50 * &k) + &1)
     ==> &2 * Ch *
         (Ce * &(P EXP k) rpow
               inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1))))) pow (k - 1) *
         root (2 EXP (k - 1))
          ((Ce * &(P EXP k) rpow
                 inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1))))) pow (k - 1)
                   *
           (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
           (&1 + log(&Kw)) / &Q) <= eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &1 + log(&Kw) /\ &1 <= &Q /\
                &0 <= &k + &11 * &(FACT k) + &7 + &4 * &2 pow k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ &0 <= b /\ &0 <= c
        ==> &0 <= a + &11 * b + &7 + &4 * c`) THEN
      SIMP_TAC[REAL_POS; REAL_POW_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC E3_ROOT_BOUND THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC RPOW_LE_1 THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_OF_NUM_LE] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ALL_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `(k - 1) * (2 EXP (k - 1) + 1)`; `Ce:real`;
                `P:num`; `Q:num`] B_POW_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MULT_EQ_0; ADD_EQ_0; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`; `Q:num`; `Kw:num`]
               LOG_KW_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&2 * Ch) pow (2 EXP (k - 1)) *
          (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
          (Ce pow ((k - 1) * (2 EXP (k - 1) + 1)) * &2) *
          (&1 + &50 * &k)`
  ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&2 * Ch) pow (2 EXP (k - 1)) *
    (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
    (Ce pow ((k - 1) * (2 EXP (k - 1) + 1)) * (&2 * &Q rpow inv(&4))) *
    ((&1 + &50 * &k) * &Q rpow inv(&4)) / &Q` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MONO_PRODUCT4 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[REAL_POS];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `((&2 * Ch) pow (2 EXP (k - 1)) *
     (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
     (Ce pow ((k - 1) * (2 EXP (k - 1) + 1)) * &2) *
     (&1 + &50 * &k)) *
    (&Q rpow inv(&4) * &Q rpow inv(&4) / &Q)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div; REAL_MUL_AC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `((&2 * Ch) pow (2 EXP (k - 1)) *
     (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
     (Ce pow ((k - 1) * (2 EXP (k - 1) + 1)) * &2) *
     (&1 + &50 * &k)) *
    (eps pow (2 EXP (k - 1)) /
     ((&2 * Ch) pow (2 EXP (k - 1)) *
      (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
      (Ce pow ((k - 1) * (2 EXP (k - 1) + 1)) * &2) *
      (&1 + &50 * &k) + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&Q rpow (--inv(&4))` THEN
    ASM_SIMP_TAC[RPOW_QUARTER];
    MATCH_MP_TAC SCALE_BELOW_ONE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;

let PARAM_FACTS = prove
 (`!k N P Q. 2 <= k /\ 2 <= Q /\ Q EXP 10 <= P /\ P EXP k <= N
             ==> 1 <= P /\ Q <= P /\ 2 * Q EXP 2 < N DIV Q /\
                 Q * (N DIV Q) <= N /\ N <= 2 * Q * (N DIV Q) /\
                 1 <= N DIV Q /\ N DIV Q <= N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `Q <= Q EXP 10` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Q EXP 20 <= N` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `P EXP k` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC LE_TRANS `P EXP 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `20 = 10 * 2`; GSYM EXP_EXP] THEN
      MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q EXP 19 <= N DIV Q` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `2 <= Q ==> ~(Q = 0)`] THEN
    ASM_REWRITE_TAC[GSYM(CONJUNCT2 EXP); ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * Q EXP 2 < Q EXP 19` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP 17 <= Q EXP 17 /\ 1 <= Q EXP 2` MP_TAC THENL
     [REWRITE_TAC[EXP_MONO_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                  EXP_EQ_0] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `19 = 2 + 17`; EXP_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC(SPECL [`Q EXP 2`; `3`; `Q EXP 17`] LE_MULT_LCANCEL) THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= N DIV Q` ASSUME_TAC THENL
   [MP_TAC(ASSUME `Q EXP 19 <= N DIV Q`) THEN
    MP_TAC(ASSUME `2 * Q EXP 2 < Q EXP 19`) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DIV_MUL_LE; DIV_LE] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC;
    MP_TAC(SPECL [`N:num`; `Q:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`1`; `N DIV Q`; `Q:num`] LE_MULT_RCANCEL) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let Q_LARGE = prove
 (`!k N P Q m. 1 <= k /\ m EXP (10 * k) <= N /\ N < (P + 1) EXP k /\
               P < (Q + 1) EXP 10
               ==> m <= Q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(P + 1) EXP k <= m EXP (10 * k)` MP_TAC THENL
   [REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
    TRANS_TAC LE_TRANS `(Q + 1) EXP 10` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC];
    ASM_ARITH_TAC]);;

let SMALL_OVER_Q = prove
 (`!K1 K2 eps Q1 Q.
     &0 <= K1 /\ &0 <= K2 /\ &0 < eps /\ (K1 + K2) / eps <= &Q1 /\
     Q1 <= Q /\ 1 <= Q
     ==> K1 / &Q <= eps /\ K2 / &Q <= eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `K1 + K2 <= eps * &Q` MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `eps * &Q1` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ];
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE]];
    SUBGOAL_THEN `&0 < &Q` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let FINAL_COMBINE = prove
 (`!x w a e1 e2 e3:real.
     x * (a - e1 - e2 - e3) <= w
     ==> !eps. &0 <= x /\ a / &4 = eps /\
               e1 <= eps /\ e2 <= eps /\ e3 <= eps
               ==> eps * x <= w`,
  REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `x * (a - e1 - e2 - e3:real)`
    THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorems.                                                             *)
(* ------------------------------------------------------------------------- *)

let WARING_FIXED = prove
 (`!k S. 2 <= k /\ 2 EXP k + 1 <= S
         ==> ?c N0. &0 < c /\
                    !N P. N0 <= N /\ P EXP k <= N /\ N < (P + 1) EXP k
                          ==> c * &P pow (S - k) <=
                              waring_conv (waring_kpow k) N S N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `S:num`] WARING_SING_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real`
   (X_CHOOSE_THEN `Q0:num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`k:num`; `k:num`] WARING_HUA_BOUND) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `Ch:real`)] THEN
  MP_TAC(SPECL [`k:num`; `S:num`] CT_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CT:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1))))`
              DIVISOR_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; MULT_EQ_0; ADD_EQ_0;
                EXP_EQ_0; ARITH_EQ] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `Ce:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `&0 < (c0 * inv(&k) * inv(&2) pow (S * (S + 1)) * inv(&2 pow k)) / &4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `eps = (c0 * inv(&k) * inv(&2) pow (S * (S + 1)) * inv(&2 pow k)) / &4` THEN
  ALL_TAC THEN
  MP_TAC(SPEC `(&510 * &(S + 1) * &2 pow (S - 1) +
                &4 pow (2 * k) * &2 pow (S - k) * &18 * CT) / eps`
              REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `Q1:num`) THEN
  SUBGOAL_THEN `&0 <= (&2 * abs Ch) pow (2 EXP (k - 1)) *
                (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
                (Ce pow ((k - 1) * (2 EXP (k - 1) + 1)) * &2) *
                (&1 + &50 * &k)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_POS] THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + &11 * b + &7 + &4 * c`) THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`inv(&4)`;
                `eps pow (2 EXP (k - 1)) /
                 ((&2 * abs Ch) pow (2 EXP (k - 1)) *
                  (&k + &11 * &(FACT k) + &7 + &4 * &2 pow k) *
                  (Ce pow ((k - 1) * (2 EXP (k - 1) + 1)) * &2) *
                  (&1 + &50 * &k) + &1)`] RPOW_NEG_SMALL) THEN
  ANTS_TAC THENL
   [CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `Q3:num` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `eps:real` THEN
  EXISTS_TAC `(Q0 + Q1 + Q3 + 2) EXP (10 * k) + 2 EXP S` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `P:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`10`; `P:num`] NUM_KTH_ROOT) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`; `Q:num`; `Q0 + Q1 + Q3 + 2`]
               Q_LARGE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`; `Q:num`] PARAM_FACTS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `&1 <= Ce * &(P EXP k) rpow
               inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1)))) /\
    (!m. 1 <= m /\ m <= P EXP k
         ==> &(CARD {d | d divides m}) <=
             Ce * &(P EXP k) rpow
                  inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1)))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC RPOW_LE_1 THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_OF_NUM_LE] THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      TRANS_TAC REAL_LE_TRANS
       `Ce * &m rpow inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1))))` THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RPOW_LE2 THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE; REAL_LE_INV_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `waring_hua k P k <=
    abs Ch *
    (Ce * &(P EXP k) rpow
          inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1))))) pow (k - 1) *
    &P pow (2 EXP k - k)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`P:num`; `Ce * &(P EXP k) rpow
                     inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1))))`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S:num`; `N:num`; `P:num`; `Q:num`; `N DIV Q`;
                `Ce * &(P EXP k) rpow
                      inv(&(40 * k * ((k - 1) * (2 EXP (k - 1) + 1))))`;
                `c0:real`; `CT:real`; `abs Ch`] WARING_CIRCLE_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN TRANS_TAC LE_TRANS `P EXP (k - 1)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&510 * &(S + 1) * &2 pow (S - 1) * &Q pow 5 / &P <= eps /\
                &4 pow (2 * k) * &2 pow (S - k) * &18 * CT / &Q <= eps`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`&510 * &(S + 1) * &2 pow (S - 1)`;
                  `&4 pow (2 * k) * &2 pow (S - k) * &18 * CT`;
                  `eps:real`; `Q1:num`; `Q:num`] SMALL_OVER_Q) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        SIMP_TAC[REAL_POS; REAL_POW_LE];
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POS; REAL_POW_LE];
        ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `(&510 * &(S + 1) * &2 pow (S - 1)) / &Q` THEN
      ASM_REWRITE_TAC[] THEN
      TRANS_TAC REAL_LE_TRANS
       `(&510 * &(S + 1) * &2 pow (S - 1)) * &Q pow 5 / &P` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL];
        MATCH_MP_TAC E1_SMALL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          SIMP_TAC[REAL_POS; REAL_POW_LE];
          ASM_ARITH_TAC]];
      UNDISCH_TAC
       `(&4 pow (2 * k) * &2 pow (S - k) * &18 * CT) / &Q <= eps` THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`; `Q:num`; `N DIV Q`; `Ce:real`;
                `abs Ch`; `eps:real`] E3_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    DISCH_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINAL_COMBINE) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]);;

let WARING_HARDY_LITTLEWOOD = prove
 (`!k s. 2 <= k /\ 2 EXP k + 1 <= s
         ==> ?N0. !N. N0 <= N
                      ==> ?x. (!i. 1 <= i /\ i <= s ==> 1 <= x i) /\
                              nsum(1..s) (\i. x i EXP k) = N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `s:num`] WARING_FIXED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `N0 + 1` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC WARING_CONV_KPOW_EXISTS THEN EXISTS_TAC `N:num` THEN
  MP_TAC(SPECL [`k:num`; `N:num`] NUM_KTH_ROOT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `c * &P pow (s - k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    REWRITE_TAC[ARITH_RULE `0 < P <=> ~(P = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `N < (P + 1) EXP k` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; EXP_ONE] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let NSUM_PAD_ZEROS = prove
 (`!f k m g. 1 <= k /\ m <= g
             ==> nsum(1..g) (\i. (if i <= m then f i else 0) EXP k) =
                 nsum(1..m) (\i. f i EXP k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `g = m + (g - m):num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[NSUM_ADD_SPLIT; ARITH_RULE `1 <= m + 1`] THEN
  MATCH_MP_TAC(ARITH_RULE `a = c /\ b = 0 ==> a + b = c:num`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN SIMP_TAC[];
    MATCH_MP_TAC NSUM_EQ_0_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `m + 1 <= i ==> ~(i <= m)`; EXP_ZERO] THEN
    ASM_ARITH_TAC]);;

let HILBERT_WARING = prove
 (`!k. 1 <= k ==> ?g. !n. ?x. n = nsum(1..g) (\i. x i EXP k)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 1` THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN EXISTS_TAC `\i:num. n:num` THEN
    ASM_REWRITE_TAC[NSUM_SING_NUMSEG; EXP_1];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `2 EXP k + 1`] WARING_HARDY_LITTLEWOOD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  EXISTS_TAC `(2 EXP k + 1) + N0` THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `N0 <= n:num` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\i. if i <= 2 EXP k + 1 then (x:num->num) i else 0` THEN
    ASM_SIMP_TAC[NSUM_PAD_ZEROS; ARITH_RULE `a <= a + b:num`];
    EXISTS_TAC `\i. if i <= n:num then 1 else 0` THEN
    ASM_SIMP_TAC[NSUM_PAD_ZEROS; ARITH_RULE
     `~(N0 <= n) ==> n <= (a + 1) + N0:num`] THEN
    REWRITE_TAC[EXP_ONE; NSUM_CONST_NUMSEG] THEN ARITH_TAC]);;

let WARING_LOWER_BOUND = prove
 (`!k s. 2 <= k /\ 2 EXP k + 1 <= s
         ==> ?c N0. &0 < c /\
                    !N. N0 <= N
                        ==> c * &N rpow (&s / &k - &1) <=
                            waring_conv (waring_kpow k) N s N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `s:num`] WARING_FIXED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `k <= s:num` ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` LT_POW2_REFL) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `c / &2 pow (s - k)` THEN EXISTS_TAC `N0 + 1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT;
                                               ARITH];
    ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`] NUM_KTH_ROOT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `1 <= P` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= P <=> ~(P = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `N < (P + 1) EXP k` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; EXP_ONE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `P:num`] ROOT_BOUNDS_P) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&N rpow (&s / &k - &1) = root k (&N) pow (s - k)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < &N /\ ~(k = 0)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ROOT_RPOW; REAL_LT_IMP_LE; RPOW_POW_MUL] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    UNDISCH_TAC `~(k = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `c * &P pow (s - k)` THEN CONJ_TAC THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 pow (s - k)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  MP_TAC(ASSUME `1 <= P`) THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Counting the representations.                                             *)
(* ------------------------------------------------------------------------- *)

let waring_rep = new_definition
 `waring_rep k s n =
    {x:num->num | (!i. 1 <= i /\ i <= s ==> 1 <= x i) /\
                  (!i. ~(1 <= i /\ i <= s) ==> x i = 0) /\
                  nsum(1..s) (\i. x i EXP k) = n}`;;

let WARING_REP_FINITE = prove
 (`!k s n. 1 <= k ==> FINITE(waring_rep k s n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:num->num | (!i. i IN 1..s ==> x i IN 0..n) /\
                            (!i. ~(i IN 1..s) ==> x i = 0)}` THEN
  SIMP_TAC[FINITE_FUNSPACE; FINITE_NUMSEG] THEN
  REWRITE_TAC[waring_rep; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  TRANS_TAC LE_TRANS `(x:num->num) i EXP k` THEN CONJ_TAC THENL
   [ASM_CASES_TAC `(x:num->num) i = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
    ASM_REWRITE_TAC[LE_EXP];
    MP_TAC(ISPECL [`\i. (x:num->num) i EXP k`; `n:num`; `1..s`]
                  NSUM_POS_BOUND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; LE_REFL; IN_NUMSEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let WARING_REP_0 = prove
 (`!k n. waring_rep k 0 n = if n = 0 then {\i. 0} else {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_rep; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num->num` THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH;
              ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; FUN_EQ_THM] THEN
  ASM_MESON_TAC[]);;

let WARING_REP_FIBRE = prove
 (`!k s n y. 1 <= k /\ 1 <= y /\ y EXP k <= n
             ==> {x | x IN waring_rep k (SUC s) n /\ x(SUC s) = y} =
                 IMAGE (\z i. if i = SUC s then y else z i)
                       (waring_rep k s (n - y EXP k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; waring_rep] THEN
  X_GEN_TAC `x:num->num` THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `\i. if i = SUC s then 0 else (x:num->num) i`
     THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `i <= s ==> ~(i = SUC s)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `nsum(1..s) (\i. (if i = SUC s then 0 else (x:num->num) i)
                                    EXP k) =
                    nsum(1..s) (\i. x i EXP k)` SUBST1_TAC THENL
       [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN
        SIMP_TAC[ARITH_RULE `i <= s ==> ~(i = SUC s)`];
        UNDISCH_TAC
         `nsum(1..s) (\i. (x:num->num) i EXP k) + x(SUC s) EXP k = n` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC]];
    DISCH_THEN(X_CHOOSE_THEN `z:num->num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `~(1 <= i /\ i <= SUC s) ==> ~(i = SUC s)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `nsum(1..s) (\i. (if i = SUC s then y else (z:num->num) i)
                                    EXP k) =
                    nsum(1..s) (\i. z i EXP k)` SUBST1_TAC THENL
       [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN
        SIMP_TAC[ARITH_RULE `i <= s ==> ~(i = SUC s)`];
        ASM_ARITH_TAC]]]);;

let WARING_REP_RECURSION = prove
 (`!k s n. 1 <= k
           ==> CARD(waring_rep k (SUC s) n) =
               nsum {y | 1 <= y /\ y EXP k <= n}
                    (\y. CARD(waring_rep k s (n - y EXP k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:num->num. x(SUC s)`; `\x:num->num. 1`;
                 `waring_rep k (SUC s) n`; `{y | 1 <= y /\ y EXP k <= n}`]
                NSUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WARING_REP_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; waring_rep; IN_ELIM_THM] THEN
    X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      UNDISCH_TAC `nsum(1..SUC s) (\i. (x:num->num) i EXP k) = n` THEN
      REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN
      ARITH_TAC];
    DISCH_TAC] THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM; WARING_REP_FINITE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `y:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[WARING_REP_FIBRE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z1:num->num`; `z2:num->num`] THEN
    REWRITE_TAC[waring_rep; IN_ELIM_THM; FUN_EQ_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = SUC s` THENL
     [ASM_SIMP_TAC[ARITH_RULE `~(1 <= SUC s /\ SUC s <= s)`];
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let WARING_CONV_KPOW_SUC = prove
 (`!k L s n. 1 <= k /\ n <= L
             ==> waring_conv (waring_kpow k) L (SUC s) n =
                 sum {y | 1 <= y /\ y EXP k <= n}
                     (\y. waring_conv (waring_kpow k) L s (n - y EXP k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_conv] THEN
  TRANS_TAC EQ_TRANS
   `sum (IMAGE (\y. y EXP k) {y | 1 <= y /\ y EXP k <= n})
        (\m. if m <= n then waring_kpow k m *
             waring_conv (waring_kpow k) L s (n - m) else &0)`
          THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[waring_kpow] THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; EXP_MONO_EQ] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `y:num` THEN
  REWRITE_TAC[IN_ELIM_THM; o_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[waring_kpow] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[REAL_MUL_LID]; ASM_MESON_TAC[]]);;

let FINITE_KPOW_SET = prove
 (`!k n. 1 <= k ==> FINITE {y | 1 <= y /\ y EXP k <= n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `0..n` THEN REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:num` THEN STRIP_TAC THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
  TRANS_TAC LE_TRANS `y EXP k` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
  REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC);;

let WARING_CONV_KPOW_CARD = prove
 (`!k L s n. 1 <= k /\ n <= L
             ==> waring_conv (waring_kpow k) L s n =
                 &(CARD(waring_rep k s n))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[waring_conv; WARING_REP_0] THEN
    COND_CASES_TAC THEN
    SIMP_TAC[CARD_SING; CARD_CLAUSES; ARITH];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[WARING_CONV_KPOW_SUC; WARING_REP_RECURSION] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_SUM; FINITE_KPOW_SET] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `y:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let WARING_COUNT_LOWER = prove
 (`!k s. 2 <= k /\ 2 EXP k + 1 <= s
         ==> ?c N0. &0 < c /\
                    !N. N0 <= N
                        ==> c * &N rpow (&s / &k - &1) <=
                            &(CARD {x | (!i. 1 <= i /\ i <= s ==> 1 <= x i) /\
                                        (!i. ~(1 <= i /\ i <= s) ==> x i = 0)
                                          /\
                                        nsum(1..s) (\i. x i EXP k) = N})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `s:num`] WARING_LOWER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM waring_rep] THEN
  SUBGOAL_THEN `&(CARD(waring_rep k s N)) = waring_conv (waring_kpow k) N s N`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC WARING_CONV_KPOW_CARD THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[]]);;
