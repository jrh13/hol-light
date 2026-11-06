(* ========================================================================= *)
(* Waring's problem I: the circle identity, Weyl's inequality and Hua's      *)
(* lemma for k-th powers (Nathanson, Additive Number Theory: The Classical   *)
(* Bases, ch. 4-5).                                                          *)
(* * waring_conv w L s n is the sum over m_1 + ... + m_s = n, 1 <= m_i <= L, *)
(*   of w(m_1) ... w(m_s) (recursion on s).  With waring_kpow k m = 1 if m   *)
(*   is a positive k-th power and 0 otherwise, waring_conv (waring_kpow k) L *)
(*   s n counts the ordered representations of n <= L as a sum of s positive *)
(*   k-th powers (WARING_CONV_KPOW_CARD in waring.ml);                       *)
(*   WARING_CONV_KPOW_EXISTS turns waring_conv (waring_kpow k) L s n > 0     *)
(*   into a representation.                                                  *)
(* * With waring_kexp k P x = sum_{n <= P} e(x n^k), P^k <= N < (P + 1)^k    *)
(*   and s N < M, WARING_KEXP_CIRCLE (discrete orthogonality):               *)
(*     sum_{j < M} waring_kexp k P (j/M + t)^s e(-N (j/M + t))               *)
(*       = M waring_conv (waring_kpow k) N s N.                              *)
(* * Weyl differencing on lists l of shifts: waring_diff k [] n = n^k and    *)
(*   waring_diff k (CONS e l) n = waring_diff k l (n + e) - waring_diff k l  *)
(*   n; k - 1 shifts leave k! (product of the shifts) n + const              *)
(*   (WARING_DIFF_LINEAR).  Iterating Cauchy-Schwarz (WEYL_ITER) gives       *)
(*   WEYL_EXPLICIT: if (a,q) = 1, |x - a/q| <= 1/q^2 and tau(m) <= B for 1   *)
(*   <= m <= P^(k-1), then                                                   *)
(*     |waring_kexp k P x|^(2^(k-1))                                         *)
(*       <= (2P)^(2^(k-1)-k) 2^k ((k-1) P^(k-1) +                            *)
(*          B^(k-1) (k! P^(k-1)/q + 1) (7 P + 4 q (1 + log q))).             *)
(* * Hua's lemma: waring_hua k P j, the number of solutions of x_1^k + ... + *)
(*   x_r^k = y_1^k + ... + y_r^k with r = 2^(j-1) and 1 <= x_i, y_i <= P     *)
(*   (the mean value of |waring_kexp k P|^(2^j)), satisfies                  *)
(*   WARING_HUA_BOUND:                                                       *)
(*     waring_hua k P j <= Ch B^(j-1) P^(2^j - j)     (1 <= j <= k)          *)
(*   when tau(m) <= B for 1 <= m <= P^k, by induction on j                   *)
(*   (WARING_HUA_STEP), counting the solutions of the differenced equations  *)
(*   with the divisor bound.                                                 *)
(* ========================================================================= *)

needs "Sieve/nt.ml";;
needs "Sieve/expsum.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Representations as sums of k-th powers and the circle identity.           *)
(* ------------------------------------------------------------------------- *)

let waring_conv = define
 `(waring_conv (w:num->real) L 0 n = if n = 0 then &1 else &0) /\
  (waring_conv w L (SUC s) n =
     sum(1..L) (\m. if m <= n then w m * waring_conv w L s (n - m) else &0))`;;

let WARING_CONV_SUPPORT = prove
 (`!w L s n. s * L < n ==> waring_conv w L s n = &0`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[waring_conv] THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN MESON_TAC[LT_REFL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `waring_conv w L s (n - m) = &0`
     (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `SUC s * L < n` THEN UNDISCH_TAC `m <= L:num` THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC]);;

let WARING_CONV_POS = prove
 (`!w L s n. (!m. &0 <= w m) ==> &0 <= waring_conv w L s n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[waring_conv] THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[]]);;

let WARING_CONV_GEN = prove
 (`!(w:num->real) L s x.
     vsum(1..L) (\m. Cx(w m) * expi(&m * x)) pow s =
     vsum(0..s * L) (\n. Cx(waring_conv w L s n) * expi(&n * x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[complex_pow; MULT_CLAUSES; VSUM_SING_NUMSEG; waring_conv] THEN
    REWRITE_TAC[REAL_MUL_LZERO; EXPI_0; COMPLEX_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[complex_pow; waring_conv] THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG; GSYM VSUM_COMPLEX_RMUL;
           GSYM VSUM_COMPLEX_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o rand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `vsum (0..SUC s * L)
      (\n. Cx (if m <= n then w m * waring_conv w L s (n - m) else &0) *
           expi (&n * x)) =
    vsum (m..SUC s * L)
      (\n. Cx (if m <= n then w m * waring_conv w L s (n - m) else &0) *
           expi (&n * x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL
     [ARITH_TAC;
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(m <= n:num)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `m..SUC s * L = (0 + m)..((SUC s * L - m) + m)` SUBST1_TAC
  THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
    REWRITE_TAC[VSUM_OFFSET; LE_ADDR; ADD_SUB]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(0..s * L)
                (\i. Cx(w m * waring_conv w L s i) * expi(&(i + m) * x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `waring_conv w L s i = &0` SUBST1_TAC THENL
       [MATCH_MP_TAC WARING_CONV_SUPPORT THEN ASM_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]];
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[CX_MUL; GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; EXPI_ADD] THEN
    CONV_TAC COMPLEX_RING]);;

let WARING_CONV_CIRCLE = prove
 (`!(w:num->real) L s M n t.
     s * L < M /\ n < M
     ==> vsum {j | j < M}
           (\j. vsum(1..L) (\m. Cx(w m) * expi(&m * (&j / &M + t))) pow s *
                expi(--(&n * (&j / &M + t)))) =
         Cx(&M * waring_conv w L s n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WARING_CONV_GEN] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!i. i IN 0..s * L
        ==> vsum {j | j < M}
              (\j. (Cx(waring_conv w L s i) * expi(&i * (&j / &M + t))) *
                   expi(--(&n * (&j / &M + t)))) =
            if i = n then Cx(&M * waring_conv w L s n) else Cx(&0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ABBREV_TAC `r = &i - &n:real` THEN
    SUBGOAL_THEN
     `!j. (Cx(waring_conv w L s i) * expi(&i * (&j / &M + t))) *
          expi(--(&n * (&j / &M + t))) =
          (Cx(waring_conv w L s i) * expi(r * t)) * expi(r * &j / &M)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM EXPI_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "r" THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
    MP_TAC(SPECL [`M:num`; `r:real`] VSUM_EXPI_RESIDUES_INT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        EXPAND_TAC "r" THEN SIMP_TAC[INTEGER_CLOSED];
        EXPAND_TAC "r" THEN
        SUBGOAL_THEN `i < M /\ n < M:num` MP_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `r = &0 <=> i = n:num` (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
    SUBGOAL_THEN `r = &0` SUBST1_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_MUL_LZERO; EXPI_0; CX_MUL] THEN CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `vsum(0..s * L)
      (\i. if i = n then Cx(&M * waring_conv w L s n) else Cx(&0))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_DELTA; IN_NUMSEG; LE_0] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `waring_conv w L s n = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC WARING_CONV_SUPPORT THEN ASM_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_VEC_0]]);;

let waring_kpow = new_definition
 `waring_kpow k m = if ?y. 1 <= y /\ m = y EXP k then &1 else &0`;;

let waring_kexp = new_definition
 `waring_kexp k P x = vsum(1..P) (\n. expi(x * &(n EXP k)))`;;

let WARING_KPOW_POS = prove
 (`!k m. &0 <= waring_kpow k m`,
  REWRITE_TAC[waring_kpow] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REAL_ARITH_TAC);;

let WARING_KEXP_WEIGHTS = prove
 (`!k P N x. 1 <= k /\ P EXP k <= N /\ N < (P + 1) EXP k
             ==> waring_kexp k P x =
                 vsum(1..N) (\m. Cx(waring_kpow k m) * expi(&m * x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_kexp] THEN
  SUBGOAL_THEN
   `vsum(1..N) (\m. Cx(waring_kpow k m) * expi(&m * x)) =
    vsum {m | m IN 1..N /\ ?y. 1 <= y /\ m = y EXP k} (\m. expi(&m * x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[VSUM_RESTRICT_SET] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[waring_kpow] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{m | m IN 1..N /\ ?y. 1 <= y /\ m = y EXP k} =
    IMAGE (\n. n EXP k) (1..P)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(P + 1) EXP k <= y EXP k` MP_TAC THENL
       [REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `P EXP k` THEN
        ASM_REWRITE_TAC[EXP_MONO_LE];
        EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    ASM_MESON_TAC[EXP_MONO_EQ; ARITH_RULE `1 <= k ==> ~(k = 0)`];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[o_THM; REAL_MUL_SYM]);;

let WARING_CONV_KPOW_EXISTS = prove
 (`!k L s n. &0 < waring_conv (waring_kpow k) L s n
             ==> ?x. (!i. 1 <= i /\ i <= s ==> 1 <= x i) /\
                     nsum(1..s) (\i. x i EXP k) = n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[waring_conv] THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN
    DISCH_TAC THEN EXISTS_TAC `\i:num. 1` THEN
    ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH] THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?m. 1 <= m /\ m <= L /\ m <= n /\ &0 < waring_kpow k m /\
                    &0 < waring_conv (waring_kpow k) L s (n - m)`
                    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    UNDISCH_TAC
     `&0 < sum (1..L) (\m. if m <= n
                           then waring_kpow k m *
                           waring_conv (waring_kpow k) L s (n - m)
                           else &0)` THEN
    MATCH_MP_TAC(REAL_ARITH `s <= &0 ==> &0 < s ==> F`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..L) (\m:num. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0; REAL_LE_REFL]] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN
      `waring_kpow k m = &0 \/ waring_conv (waring_kpow k) L s (n - m) = &0`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`waring_kpow k`; `L:num`; `s:num`; `n - m:num`]
               WARING_CONV_POS) THEN
      REWRITE_TAC[WARING_KPOW_POS] THEN
      MP_TAC(SPECL [`k:num`; `m:num`] WARING_KPOW_POS) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL];
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - m:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `&0 < waring_kpow k m` THEN REWRITE_TAC[waring_kpow] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i. if i = SUC s then y else (x:num->num) i` THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum(1..s) (\i. (if i = SUC s then y else (x:num->num) i) EXP k) =
                nsum(1..s) (\i. x i EXP k)` SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let WARING_KEXP_CIRCLE = prove
 (`!k s P N M t.
     1 <= k /\ P EXP k <= N /\ N < (P + 1) EXP k /\ s * N < M /\ N < M
     ==> vsum {j | j < M}
           (\j. waring_kexp k P (&j / &M + t) pow s *
                expi(--(&N * (&j / &M + t)))) =
         Cx(&M * waring_conv (waring_kpow k) N s N)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WARING_KEXP_WEIGHTS] THEN
  MATCH_MP_TAC WARING_CONV_CIRCLE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Weyl differencing.                                                        *)
(* ------------------------------------------------------------------------- *)

let waring_diff = define
 `(waring_diff k [] n = n EXP k) /\
  (waring_diff k (CONS e l) n = waring_diff k l (n + e) - waring_diff k l n)`;;

let BINOM_SHIFT_SPLIT = prove
 (`!i m e n. i <= SUC m
             ==> (n + e) EXP i =
                 n EXP i +
                 nsum(0..SUC m)
                   (\l. if l < i then binom(i,l) * n EXP l * e EXP (i - l)
                        else 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BINOMIAL_THEOREM] THEN
  SUBGOAL_THEN `0..SUC m = (0..i) UNION (i+1..SUC m)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[NSUM_UNION; FINITE_NUMSEG; DISJOINT_NUMSEG;
           ARITH_RULE `i < i + 1`] THEN
  SUBGOAL_THEN
   `nsum (i + 1..SUC m)
      (\l. if l < i then binom (i,l) * n EXP l * e EXP (i - l) else 0) = 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ADD_CLAUSES]] THEN
  TRANS_TAC EQ_TRANS
   `nsum(0..i) (\l. (if l < i then binom (i,l) * n EXP l * e EXP (i - l)
                     else 0) + (if l = i then n EXP i else 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `l:num = i` THEN
    ASM_REWRITE_TAC[LT_REFL; BINOM_REFL; SUB_REFL; EXP; MULT_CLAUSES;
                    ADD_CLAUSES] THEN
    SUBGOAL_THEN `l < i:num` (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[NSUM_ADD_NUMSEG; NSUM_DELTA; IN_NUMSEG; LE_0; LE_REFL] THEN
    ARITH_TAC]);;

let WDIFF_POLY_SHIFT = prove
 (`!b m e n.
     nsum(0..SUC m) (\i. b i * (n + e) EXP i) =
     nsum(0..SUC m) (\i. b i * n EXP i) +
     e * nsum(0..m) (\l. nsum(l+1..SUC m)
                           (\i. b i * binom(i,l) * e EXP (i - 1 - l)) *
                         n EXP l)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `nsum(0..SUC m) (\i. b i * (n + e) EXP i) =
    nsum(0..SUC m) (\i. b i * n EXP i) +
    nsum(0..SUC m) (\i. nsum(0..SUC m) (\l. b i *
       (if l < i then binom(i,l) * n EXP l * e EXP (i - l) else 0)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM NSUM_ADD_NUMSEG; NSUM_LMUL] THEN
    MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC BINOM_SHIFT_SPLIT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EQ_ADD_LCANCEL]] THEN
  GEN_REWRITE_TAC LAND_CONV [NSUM_SWAP_NUMSEG] THEN
  GEN_REWRITE_TAC LAND_CONV [NSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[LE_0] THEN
  SUBGOAL_THEN
   `nsum (0..SUC m) (\i. b i *
      (if SUC m < i then binom (i,SUC m) * n EXP SUC m * e EXP (i - SUC m)
       else 0)) = 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[ADD_CLAUSES; GSYM NSUM_LMUL]] THEN
  MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `0..SUC m = (0..l) UNION (l+1..SUC m)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[NSUM_UNION; FINITE_NUMSEG; DISJOINT_NUMSEG;
           ARITH_RULE `l < l + 1`] THEN
  SUBGOAL_THEN
   `nsum (0..l)
     (\i. b i * (if l < i then binom (i,l) * n EXP l * e EXP (i - l)
                 else 0)) = 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[ADD_CLAUSES]] THEN
  REWRITE_TAC[GSYM NSUM_LMUL; GSYM NSUM_RMUL] THEN
  MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `l < i:num` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i - l = SUC(i - 1 - l)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EXP] THEN ARITH_TAC]);;

let WARING_DIFF_POLY = prove
 (`!k l. LENGTH l <= k
         ==> ?b. (!n. waring_diff k l n =
                      ITLIST ( * ) l 1 *
                      nsum(0..k - LENGTH l) (\i. b i * n EXP i)) /\
                 FACT(k - LENGTH l) * b(k - LENGTH l) = FACT k`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ITLIST; waring_diff] THENL
   [DISCH_TAC THEN EXISTS_TAC `\i:num. if i = k then 1 else 0` THEN
    REWRITE_TAC[SUB_0; MULT_CLAUSES] THEN
    REWRITE_TAC[COND_RATOR; COND_RAND; MULT_CLAUSES] THEN
    GEN_TAC THEN
    TRANS_TAC EQ_TRANS `nsum(0..k) (\i. if i = k then n EXP k else 0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NSUM_DELTA; IN_NUMSEG; LE_0; LE_REFL];
      MATCH_MP_TAC NSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = k - SUC(LENGTH(t:num list))` THEN
  SUBGOAL_THEN `k - LENGTH(t:num list) = SUC m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `k - LENGTH(t:num list) = SUC m`]) THEN
  EXISTS_TAC
   `\l. nsum(l+1..SUC m) (\i. b i * binom(i,l) * h EXP (i - 1 - l))` THEN
  ASM_REWRITE_TAC[WDIFF_POLY_SHIFT] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_SUB2] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `m + 1 = SUC m`; NSUM_SING_NUMSEG] THEN
  REWRITE_TAC[BINOM_PENULT; ARITH_RULE `SUC m - 1 - m = 0`; EXP] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[FACT] THEN ARITH_TAC);;

let WARING_DIFF_MONO = prove
 (`!k l m n. LENGTH l <= k /\ m <= n
             ==> waring_diff k l m <= waring_diff k l n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC o
    MATCH_MP WARING_DIFF_POLY) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
  MATCH_MP_TAC NSUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
  MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]);;

let WARING_DIFF_ZERO = prove
 (`!k l n. MEM 0 l ==> waring_diff k l n = 0`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; waring_diff] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[ADD_CLAUSES; SUB_REFL];
    ASM_SIMP_TAC[SUB_REFL]]);;

let WARING_DIFF_BOUND = prove
 (`!k l n. LENGTH l <= k ==> waring_diff k l n <= (n + ITLIST (+) l 0) EXP k`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[waring_diff; ITLIST; ADD_CLAUSES; LE_REFL; LENGTH] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `waring_diff k t (n + h)` THEN
  REWRITE_TAC[ARITH_RULE `a - b <= a:num`] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `((n + h) + ITLIST (+) t 0) EXP k` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM ADD_ASSOC; LE_REFL]]);;

let ITLIST_MUL_EQ_0 = prove
 (`!l. ITLIST ( * ) l 1 = 0 <=> MEM 0 l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MEM; MULT_EQ_0; ARITH] THEN
  MESON_TAC[]);;

let WARING_DIFF_DIVIDES = prove
 (`!k l n. LENGTH l <= k ==> ITLIST ( * ) l 1 divides waring_diff k l n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC o
    MATCH_MP WARING_DIFF_POLY) THEN
  ASM_REWRITE_TAC[] THEN NUMBER_TAC);;

let WARING_DIFF_LINEAR = prove
 (`!k l. 1 <= k /\ LENGTH l = k - 1
         ==> ?b0. !n. waring_diff k l n = ITLIST ( * ) l 1 *
                      (FACT k * n + b0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `l:num list`] WARING_DIFF_POLY) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k - LENGTH(l:num list) = 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0; ARITH; NSUM_SING_NUMSEG] THEN
  SIMP_TAC[NSUM_TRIV_NUMSEG; ARITH; ADD_CLAUSES] THEN
  REWRITE_TAC[EXP; EXP_1; MULT_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(b:num->num) 0` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `FACT 1 * (b:num->num) 1 = FACT k` THEN
  REWRITE_TAC[ARITH_RULE `FACT 1 = 1`; MULT_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;

let WARING_DIFF_STRICT = prove
 (`!k l m n. LENGTH l < k /\ ~MEM 0 l /\ m < n
             ==> waring_diff k l m < waring_diff k l n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `l:num list`] WARING_DIFF_POLY) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL; ITLIST_MUL_EQ_0] THEN
  ABBREV_TAC `d = k - LENGTH(l:num list)` THEN
  SUBGOAL_THEN `d = SUC(d - 1)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `e = d - 1` THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0] THEN
  MATCH_MP_TAC LET_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
    REWRITE_TAC[LT_MULT_LCANCEL] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `FACT(SUC e) * (b:num->num)(SUC e) = FACT k` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES] THEN MESON_TAC[FACT_NZ];
      ASM_REWRITE_TAC[EXP_MONO_LT; NOT_SUC]]]);;

(* ------------------------------------------------------------------------- *)
(* Iterated Cauchy-Schwarz over lists of shifts.                             *)
(* ------------------------------------------------------------------------- *)

let NORM_ADD_POW2 = prove
 (`!a b:complex. norm(a + b) pow 2 =
                 norm a pow 2 + norm b pow 2 + &2 * Re(a * cnj b)`,
  REWRITE_TAC[COMPLEX_SQNORM; RE_ADD; IM_ADD; complex_mul; cnj; RE; IM] THEN
  REAL_ARITH_TAC);;

let SUM_REFLECT_1 = prove
 (`!(h:num->real) L. sum(1..L) h = sum(1..L) (\e. h(SUC L - e))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `L = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  SUBGOAL_THEN `1..L = (0 + 1)..((L - 1) + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let WEYL_STEP = prove
 (`!f P L. L <= P
           ==> norm(vsum(1..L) (\n. expi(f n))) pow 2 =
               sum {e | e < P}
                 (\e. (if e = 0 then &1 else &2) *
                      Re(vsum(1..L - e) (\n. expi(f(n + e) - f n))))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `0 - e = 0`; VSUM_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[NORM_0; COMPLEX_VEC_0; RE_CX; REAL_MUL_RZERO; SUM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC L`] THEN
  REWRITE_TAC[NORM_ADD_POW2; NORM_EXPI] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!e. vsum(1..SUC L - e) (\n. expi(f(n + e) - f n)) =
        vsum(1..L - e) (\n. expi(f(n + e) - f n)) +
        (if e <= L then expi(f(SUC L) - f(SUC L - e)) else Cx(&0))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `e:num` THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN `SUC L - e = SUC(L - e)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `SUC L - e = 0 /\ L - e = 0` (CONJUNCTS_THEN SUBST1_TAC)
      THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_ADD_RID]];
    ALL_TAC] THEN
  REWRITE_TAC[RE_ADD; REAL_ADD_LDISTRIB] THEN
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[REAL_ARITH `a + b + c = a + d <=> b + c = d:real`] THEN
  SUBGOAL_THEN
   `sum {e | e < P}
     (\e. (if e = 0 then &1 else &2) *
          Re (if e <= L then expi (f (SUC L) - f (SUC L - e)) else Cx (&0))) =
    sum(0..L) (\e. (if e = 0 then &1 else &2) *
                   Re(expi (f (SUC L) - f (SUC L - e))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {e | e IN {e | e < P} /\ e <= L}
                  (\e. (if e = 0 then &1 else &2) *
                       Re(expi (f (SUC L) - f (SUC L - e))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `e:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `e <= L:num` THEN ASM_REWRITE_TAC[RE_CX; REAL_MUL_RZERO];
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[SUB_0; REAL_SUB_REFL; EXPI_0; RE_CX; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_ARITH `&1 + x = &1 + y <=> x = y:real`] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG; RE_VSUM] THEN
  REWRITE_TAC[CNJ_EXPI; GSYM EXPI_ADD; GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT_1] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(e = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; AP_TERM_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM RE_CNJ] THEN REWRITE_TAC[CNJ_EXPI] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let LISTS_SUC = prove
 (`!(D:A->bool) j.
     {l | LENGTH l = SUC j /\ ALL (\x. x IN D) l} =
     IMAGE (\p. CONS (FST p) (SND p))
           (D CROSS {l | LENGTH l = j /\ ALL (\x. x IN D) l})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_CROSS; EXISTS_PAIR_THM] THEN
  X_GEN_TAC `l:A list` THEN REWRITE_TAC[LENGTH_EQ_CONS] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `h:A` (X_CHOOSE_THEN `t:A list`
      STRIP_ASSUME_TAC)) MP_TAC) THEN
    ASM_REWRITE_TAC[ALL] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`h:A`; `t:A list`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`h:A`; `t:A list`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[ALL; CONS_11] THEN
    MAP_EVERY EXISTS_TAC [`h:A`; `t:A list`] THEN ASM_REWRITE_TAC[]]);;

let LISTS_HAS_SIZE = prove
 (`!(D:A->bool) j. FINITE D
                  ==> {l | LENGTH l = j /\ ALL (\x. x IN D) l} HAS_SIZE
                      (CARD D EXP j)`,
  GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `{l:A list | LENGTH l = 0 /\ ALL (\x. x IN D) l} = {[]}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; LENGTH_EQ_NIL] THEN
      MESON_TAC[ALL];
      REWRITE_TAC[EXP; HAS_SIZE; FINITE_SING; CARD_SING]];
    ALL_TAC] THEN
  REWRITE_TAC[LISTS_SUC; EXP] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; CONS_11; PAIR_EQ] THEN MESON_TAC[];
    MATCH_MP_TAC HAS_SIZE_CROSS THEN ASM_SIMP_TAC[HAS_SIZE]]);;

let SUM_LISTS_SUC = prove
 (`!(D:A->bool) j f.
     FINITE D
     ==> sum {l | LENGTH l = SUC j /\ ALL (\x. x IN D) l} f =
         sum D (\x. sum {l | LENGTH l = j /\ ALL (\x. x IN D) l}
                        (\l. f(CONS x l)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {l:A list | LENGTH l = j /\ ALL (\x. x IN D) l}`
  ASSUME_TAC THENL [ASM_MESON_TAC[LISTS_HAS_SIZE; HAS_SIZE]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT] THEN REWRITE_TAC[LISTS_SUC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; CONS_11; PAIR_EQ] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[CROSS] THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM]);;

let waring_tup = new_definition
 `waring_tup j P =
  {l:num list | LENGTH l = j /\ ALL (\x. x IN {e | e < P}) l}`;;

let waring_wt = define
 `(waring_wt [] = &1) /\
  (waring_wt (CONS e l) = (if e = 0 then &1 else &2) * waring_wt l)`;;

let waring_ssum = new_definition
 `waring_ssum k P x l =
  vsum(1..P - ITLIST (+) l 0) (\n. expi(x * &(waring_diff k l n)))`;;

let WARING_WT_POS = prove
 (`!l. &0 <= waring_wt l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[waring_wt; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

let WARING_WT_LE = prove
 (`!l. waring_wt l <= &2 pow LENGTH l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[waring_wt; LENGTH; real_pow; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[WARING_WT_POS] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

let FINITE_WARING_TUP = prove
 (`!j P. FINITE(waring_tup j P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_tup] THEN
  MP_TAC(ISPECL [`{e:num | e < P}`; `j:num`] LISTS_HAS_SIZE) THEN
  SIMP_TAC[FINITE_NUMSEG_LT; HAS_SIZE]);;

let SUM_WARING_TUP_SUC = prove
 (`!j P f. sum (waring_tup (SUC j) P) f =
           sum {e | e < P} (\e. sum (waring_tup j P) (\l. f(CONS e l)))`,
  REWRITE_TAC[waring_tup] THEN SIMP_TAC[SUM_LISTS_SUC; FINITE_NUMSEG_LT]);;

let WARING_TUP_0 = prove
 (`!P. waring_tup 0 P = {[]}`,
  REWRITE_TAC[waring_tup; EXTENSION; IN_ELIM_THM; IN_SING; LENGTH_EQ_NIL] THEN
  MESON_TAC[ALL]);;

let SUM_WARING_WT_LE = prove
 (`!j P. sum (waring_tup j P) waring_wt <= (&2 * &P) pow j`,
  INDUCT_TAC THEN
  REWRITE_TAC[WARING_TUP_0; SUM_SING; waring_wt; real_pow; REAL_LE_REFL] THEN
  GEN_TAC THEN REWRITE_TAC[SUM_WARING_TUP_SUC; waring_wt; SUM_LMUL] THEN
  REWRITE_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUM_POS_LE; FINITE_WARING_TUP; WARING_WT_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {e:num | e < P} (\e. &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    REAL_ARITH_TAC]);;

let WARING_SSUM_STEP = prove
 (`!k P x l. LENGTH l <= k
             ==> norm(waring_ssum k P x l) pow 2 =
                 sum {e | e < P} (\e. (if e = 0 then &1 else &2) *
                                      Re(waring_ssum k P x (CONS e l)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_ssum] THEN
  MP_TAC(ISPECL [`\n. x * &(waring_diff k l n)`; `P:num`; `P - ITLIST (+) l 0`]
         WEYL_STEP) THEN
  REWRITE_TAC[ARITH_RULE `P - a <= P:num`] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ITLIST; waring_diff;
              ARITH_RULE `(P - a) - e = P - (e + a):num`] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`k:num`; `l:num list`; `i:num`; `i + e:num`]
           WARING_DIFF_MONO) THEN
  ASM_REWRITE_TAC[LE_ADD] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC);;

let WARING_KEXP_SSUM = prove
 (`!k P x. waring_kexp k P x = waring_ssum k P x []`,
  REWRITE_TAC[waring_kexp; waring_ssum; waring_diff; ITLIST; SUB_0]);;

let WEYL_ITER = prove
 (`!k P x j. 1 <= P /\ 1 <= j /\ j <= k
             ==> norm(waring_kexp k P x) pow (2 EXP j) <=
                 (&2 * &P) pow (2 EXP j - j - 1) *
                 sum (waring_tup j P)
                   (\l. waring_wt l * Re(waring_ssum k P x l))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
  ASM_CASES_TAC `j = 0` THENL
   [ASM_REWRITE_TAC[ARITH; WARING_KEXP_SSUM] THEN
    MP_TAC(SPECL [`k:num`; `P:num`; `x:real`; `[]:num list`]
             WARING_SSUM_STEP) THEN
    REWRITE_TAC[LENGTH; LE_0] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[num_CONV `1`; SUM_WARING_TUP_SUC; WARING_TUP_0; SUM_SING;
                waring_wt] THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; real_pow; REAL_MUL_LID; REAL_MUL_RID;
                REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `A = norm(waring_kexp k P x) pow (2 EXP j)` THEN
  ABBREV_TAC
    `B = sum (waring_tup j P) (\l. waring_wt l * Re(waring_ssum k P x l))` THEN
  ABBREV_TAC
    `V = sum (waring_tup j P)
       (\l. waring_wt l * norm(waring_ssum k P x l))` THEN
  SUBGOAL_THEN `norm(waring_kexp k P x) pow (2 EXP SUC j) = A pow 2`
  SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[EXP; REAL_POW_POW] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A /\ &0 < (&2 * &P) pow (2 EXP j - j - 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LT THEN
    UNDISCH_TAC `1 <= P` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `B <= V:real` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B"; "V"] THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_WARING_TUP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[WARING_WT_POS] THEN
    MP_TAC(SPEC `waring_ssum k P x x'` COMPLEX_NORM_GE_RE_IM) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (waring_tup j P) (\l. waring_wt l * norm(waring_ssum k P x l) pow 2) =
    sum (waring_tup (SUC j) P) (\l. waring_wt l * Re (waring_ssum k P x l))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUM_WARING_TUP_SUC; waring_wt] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
    REWRITE_TAC[FINITE_WARING_TUP; FINITE_NUMSEG_LT] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `l:num list` THEN REWRITE_TAC[waring_tup; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `P:num`; `x:real`; `l:num list`]
             WARING_SSUM_STEP) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `V pow 2 <= (&2 * &P) pow j *
               sum (waring_tup (SUC j) P)
                 (\l. waring_wt l * Re (waring_ssum k P x l))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (waring_tup j P) waring_wt *
                sum (waring_tup j P)
                  (\l. waring_wt l * norm(waring_ssum k P x l) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_WEIGHTED_CS THEN
      REWRITE_TAC[FINITE_WARING_TUP; WARING_WT_POS];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[SUM_WARING_WT_LE] THEN
      MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_WARING_TUP] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[WARING_WT_POS; REAL_LE_POW_2]];
    ALL_TAC] THEN
  ABBREV_TAC `Cc = (&2 * &P) pow (2 EXP j - j - 1)` THEN
  ABBREV_TAC
    `W' = sum (waring_tup (SUC j) P)
       (\l. waring_wt l * Re (waring_ssum k P x l))` THEN
  SUBGOAL_THEN `(&2 * &P) pow (2 EXP SUC j - SUC j - 1) =
                (Cc:real) pow 2 * (&2 * &P) pow j`
  SUBST1_TAC THENL
   [EXPAND_TAC "Cc" THEN REWRITE_TAC[REAL_POW_POW; GSYM REAL_POW_ADD] THEN
    AP_TERM_TAC THEN MP_TAC(SPEC `j:num` LT_POW2_REFL) THEN
    REWRITE_TAC[EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((Cc:real) * V) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Cc:real) * B` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[REAL_RING `((c:real) * v) pow 2 = c pow 2 * v pow 2`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

(* ------------------------------------------------------------------------- *)
(* Weyl's inequality.                                                        *)
(* ------------------------------------------------------------------------- *)

let WARING_SSUM_LINEAR_BOUND = prove
 (`!k P x l. 2 <= k /\ LENGTH l = k - 1
             ==> norm(waring_ssum k P x l) <=
                 &2 * emin (&P) (&(FACT k * ITLIST ( * ) l 1) * x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `l:num list`] WARING_DIFF_LINEAR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `b0:num`) THEN
  ASM_REWRITE_TAC[waring_ssum] THEN
  ABBREV_TAC `y = &(FACT k * ITLIST ( * ) l 1) * x` THEN
  SUBGOAL_THEN
   `!n. expi(x * &(ITLIST ( * ) l 1 * (FACT k * n + b0))) =
        expi(x * &(ITLIST ( * ) l 1 * b0)) * expi(&n * y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM EXPI_ADD] THEN AP_TERM_TAC THEN
    EXPAND_TAC "y" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG; COMPLEX_NORM_MUL; NORM_EXPI] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * emin (&(P - ITLIST (+) l 0)) y` THEN
  REWRITE_TAC[VSUM_EXPI_GEOM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC EMIN_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC);;

let CARD_WARING_TUP = prove
 (`!j P. CARD(waring_tup j P) = P EXP j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_tup] THEN
  MP_TAC(ISPECL [`{e:num | e < P}`; `j:num`] LISTS_HAS_SIZE) THEN
  SIMP_TAC[FINITE_NUMSEG_LT; HAS_SIZE; CARD_NUMSEG_LT]);;

let COUNT_MEM0 = prove
 (`!j P. sum (waring_tup j P) (\l. if MEM 0 l then &1 else &0) <=
         &j * &P pow (j - 1)`,
  INDUCT_TAC THEN
  REWRITE_TAC[WARING_TUP_0; SUM_SING; MEM; REAL_MUL_LZERO; REAL_LE_REFL] THEN
  GEN_TAC THEN REWRITE_TAC[SUM_WARING_TUP_SUC; MEM; SUC_SUB1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {e:num | e < P}
                (\e. (if e = 0 then &P pow j else &0) +
                     &j * &P pow (j - 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    X_GEN_TAC `e:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `e = 0` THEN ASM_REWRITE_TAC[] THENL
     [SIMP_TAC[SUM_CONST; FINITE_WARING_TUP; CARD_WARING_TUP;
               REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC(REAL_ARITH
       `&0 <= b ==> a <= a + b`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
      ASM_REWRITE_TAC[REAL_ADD_LID]];
    SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT; SUM_CONST; CARD_NUMSEG_LT] THEN
    REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN
    ASM_CASES_TAC `P = 0` THENL
     [ASM_REWRITE_TAC[LT_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LE_1; GSYM REAL_OF_NUM_SUC] THEN
    ASM_CASES_TAC `j = 0` THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO] THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&P pow j = &P * &P pow (j - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let ITLIST_MUL_LE_POW = prove
 (`!l P. ALL (\x. x <= P) l ==> ITLIST ( * ) l 1 <= P EXP LENGTH l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; ITLIST; LENGTH; EXP; LE_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[]);;

let SUM_PROD_FIBRES = prove
 (`!j P B G.
     &0 <= B /\ (!m. &0 <= G m) /\
     (!m. 1 <= m /\ m <= P EXP j ==> &(CARD {d | d divides m}) <= B)
     ==> sum {l | l IN waring_tup j P /\ ~MEM 0 l} (\l. G(ITLIST ( * ) l 1)) <=
         B pow j * sum(1..P EXP j) G`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {l | l IN waring_tup j P /\ ~MEM 0 l}` THEN
  SUBGOAL_THEN `FINITE(S:num list->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_WARING_TUP]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\l. ITLIST ( * ) l 1) S SUBSET 1..P EXP j`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; waring_tup;
                IN_NUMSEG] THEN
    X_GEN_TAC `l:num list` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; ITLIST_MUL_EQ_0];
      UNDISCH_TAC `LENGTH(l:num list) = j` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC ITLIST_MUL_LE_POW THEN
      UNDISCH_TAC `ALL (\x. x < P) (l:num list)` THEN
      MATCH_MP_TAC MONO_ALL THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\l. ITLIST ( * ) l 1`; `\l. (G:num->real)(ITLIST ( * ) l 1)`;
                 `S:num list->bool`] SUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (\l. ITLIST ( * ) l 1) S) (\m. B pow j * G m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `sum {x | x IN S /\ ITLIST ( * ) x 1 = m} (\l. G (ITLIST ( * ) l 1)) =
      sum {x | x IN S /\ ITLIST ( * ) x 1 = m} (\l. (G:num->real) m)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= m /\ m <= P EXP j` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (\l. ITLIST ( * ) l 1) S SUBSET 1..P EXP j` THEN
      REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {d | d divides m}) pow j` THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    MP_TAC(ISPECL [`{d | d divides m}`; `j:num`] LISTS_HAS_SIZE) THEN
    ASM_SIMP_TAC[FINITE_DIVISORS; LE_1; HAS_SIZE] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    MP_TAC(ISPECL [`{d | d divides m}`; `j:num`] LISTS_HAS_SIZE) THEN
    ASM_SIMP_TAC[FINITE_DIVISORS; LE_1; HAS_SIZE] THEN DISCH_TAC THEN
    EXPAND_TAC "S" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; waring_tup; GSYM ALL_MEM] THEN
    MESON_TAC[ITLIST_MUL_DIVIDES];
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG]]);;

let EMIN_SUM_SCALE = prove
 (`!V x c U. 1 <= c /\ &0 <= V
             ==> sum(1..U) (\m. emin V (&(c * m) * x)) <=
                 sum(1..c * U) (\m. emin V (&m * x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\m:num. c * m`; `\m:num. emin V (&m * x)`; `1..U`]
         SUM_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; EMIN_POS] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[LE_MULT_LCANCEL]]);;

let WEYL_EXPLICIT = prove
 (`!k P x a q B.
     2 <= k /\ 1 <= P /\ 1 <= q /\ coprime(a,q) /\
     abs(x - &a / &q) <= inv(&q pow 2) /\ &0 <= B /\
     (!m. 1 <= m /\ m <= P EXP (k - 1) ==> &(CARD {d | d divides m}) <= B)
     ==> norm(waring_kexp k P x) pow (2 EXP (k - 1)) <=
         (&2 * &P) pow (2 EXP (k - 1) - k) * &2 pow k *
         (&(k - 1) * &P pow (k - 1) +
          B pow (k - 1) * (&(FACT k * P EXP (k - 1)) / &q + &1) *
          (&7 * &P + &4 * &q * (&1 + log(&q))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `P:num`; `x:real`; `k - 1`] WEYL_ITER) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (k - 1) - (k - 1) - 1 = 2 EXP (k - 1) - k` SUBST1_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (waring_tup (k - 1) P)
                (\l. &2 pow k *
                     emin (&P) (&(FACT k * ITLIST ( * ) l 1) * x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_WARING_TUP] THEN
    X_GEN_TAC `l:num list` THEN REWRITE_TAC[waring_tup; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `P:num`; `x:real`; `l:num list`]
           WARING_SSUM_LINEAR_BOUND) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `l:num list` WARING_WT_LE) THEN
    MP_TAC(SPEC `l:num list` WARING_WT_POS) THEN
    MP_TAC(SPEC `waring_ssum k P x l` COMPLEX_NORM_GE_RE_IM) THEN
    MP_TAC(SPECL [`&P`; `&(FACT k * ITLIST ( * ) l 1) * x`] EMIN_POS) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN
    SUBGOAL_THEN `&2 pow k = &2 pow (k - 1) * &2` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `E = emin (&P) (&(FACT k * ITLIST ( * ) l 1) * x)` THEN
    ABBREV_TAC `S = waring_ssum k P x l` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `waring_wt l * &2 * E` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (waring_tup (k - 1) P)
      (\l. emin (&P) (&(FACT k * ITLIST ( * ) l 1) * x)) =
    sum (waring_tup (k - 1) P)
      (\l. if MEM 0 l then &P
           else emin (&P) (&(FACT k * ITLIST ( * ) l 1) * x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `ITLIST ( * ) l 1 = 0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[ITLIST_MUL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; emin; INTEGER_CLOSED];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CASES; FINITE_WARING_TUP] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&P * sum (waring_tup (k - 1) P) (\l. if MEM 0 l then &1 else &0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&P * &(k - 1) * &P pow (k - 1 - 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; COUNT_MEM0];
      SUBGOAL_THEN `&P pow (k - 1) = &P * &P pow (k - 1 - 1)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
        ASM_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k - 1`; `P:num`; `B:real`;
                 `\m. emin (&P) (&(FACT k * m) * x)`] SUM_PROD_FIBRES) THEN
  ASM_SIMP_TAC[EMIN_POS; REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..FACT k * P EXP (k - 1)) (\m. emin (&P) (&m * x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EMIN_SUM_SCALE THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; FACT_NZ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `a:num`; `q:num`; `&P`; `FACT k * P EXP (k - 1)`;
                `&0`] EMIN_SUM_CONST) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* Hua's lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let SUM_CORR_EXPI = prove
 (`!(c:num->real) L M D.
     L + D < M /\ (!u. L < u ==> c u = &0)
     ==> sum {t | t < M}
           (\t. Re(expi(&t / &M * &D)) *
                norm(vsum(0..L) (\u. Cx(c u) * expi(&u * (&t / &M))))
                pow 2) =
         &M * sum(0..L) (\u. c u * c(u + D))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. Re(expi(&t / &M * &D)) *
        norm(vsum(0..L) (\u. Cx(c u) * expi(&u * (&t / &M)))) pow 2 =
        Re(vsum(0..L) (\u. vsum(0..L) (\v.
             Cx(c u * c v) * expi((&D + &u - &v) * &t / &M))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    ABBREV_TAC `z = vsum(0..L) (\u. Cx(c u) * expi(&u * (&t / &M)))` THEN
    SUBGOAL_THEN `Cx(norm(z:complex) pow 2) = z * cnj z` MP_TAC THENL
     [REWRITE_TAC[CX_POW; COMPLEX_NORM_POW_2]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM RE_MUL_CX; th]) THEN
    EXPAND_TAC "z" THEN
    SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG; CNJ_MUL; CNJ_CX; CNJ_EXPI] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL;
             FINITE_NUMSEG] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    X_GEN_TAC `u:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
    REWRITE_TAC[CX_MUL] THEN
    SUBGOAL_THEN `(&D + &u - &v) * &t / &M =
                  &t / &M * &D + &u * (&t / &M) + --(&v * (&t / &M))`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXPI_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SIMP_TAC[GSYM RE_VSUM; FINITE_NUMSEG_LT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o rand o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!u. u IN 0..L
        ==> vsum {t | t < M} (\t. vsum (0..L)
              (\v. Cx (c u * c v) * expi ((&D + &u - &v) * &t / &M))) =
            Cx(&M * c u * c(u + D))`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
    TRANS_TAC EQ_TRANS
     `vsum(0..L) (\v. if v = u + D then Cx(&M * c u * c(u + D)) else Cx(&0))`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `v:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(SPECL [`M:num`; `&D + &u - &v:real`] VSUM_EXPI_RESIDUES_INT) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC;
          SIMP_TAC[INTEGER_CLOSED];
          SUBGOAL_THEN `u <= L:num /\ v <= L /\ L + D < M` MP_TAC THENL
           [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT;
                      GSYM REAL_OF_NUM_ADD] THEN
          REAL_ARITH_TAC];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `&D + &u - &v = &0 <=> v = u + D` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&D + &u - &v = &0 <=> &v = &u + &D`] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ];
        ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; CX_MUL] THEN
      CONV_TAC COMPLEX_RING;
      REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_DELTA; IN_NUMSEG; LE_0] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(c:num->real)(u + D) = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_VEC_0]]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `Re(vsum(0..L) (\u. Cx(&M * c u * c(u + D))))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[];
    SIMP_TAC[VSUM_CX; FINITE_NUMSEG; RE_CX; SUM_LMUL; REAL_MUL_ASSOC]]);;

let CORR_SUM_LE = prove
 (`!(c:num->real) L X.
     (!u. &0 <= c u) /\ (!u. L < u ==> c u = &0)
     ==> sum(1..X) (\m. sum(0..L) (\u. c u * c(u + m))) <= sum(0..L) c pow 2`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_POW_2; GSYM SUM_RMUL; SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\m:num. u + m`; `c:num->real`; `1..X`] SUM_IMAGE) THEN
  ANTS_TAC THENL [SIMP_TAC[EQ_ADD_LCANCEL]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (\m. u + m) (1..X) INTER (0..L)) c` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[INTER_SUBSET] THEN REWRITE_TAC[IN_INTER; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `w:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[NOT_LE];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; INTER_SUBSET]]);;

let WARING_DIFF_INJ = prove
 (`!k l a b. LENGTH l < k /\ ~MEM 0 l /\ waring_diff k l a = waring_diff k l b
             ==> a = b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `~(a < b) /\ ~(b < a) ==> a = b:num`) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`k:num`; `l:num list`; `a:num`; `b:num`] WARING_DIFF_STRICT);
    MP_TAC(SPECL [`k:num`; `l:num list`; `b:num`; `a:num`]
             WARING_DIFF_STRICT)] THEN
  ASM_REWRITE_TAC[LT_REFL]);;

let HUA_FIBRE_SUM = prove
 (`!k P B j G.
     j < k /\ &0 <= B /\ (!m. &0 <= G m) /\
     (!m. 1 <= m /\ m <= P EXP k ==> &(CARD {d | d divides m}) <= B)
     ==> sum {l | l IN waring_tup j P /\ ~MEM 0 l}
           (\l. sum(1..P - ITLIST (+) l 0) (\n. G(waring_diff k l n))) <=
         B pow j * sum(1..P EXP k) G`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {l | l IN waring_tup j P /\ ~MEM 0 l}
      (\l. sum(1..P EXP k)
             (\m. if ALL (\e. e divides m) l then G m else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN SIMP_TAC[FINITE_RESTRICT; FINITE_WARING_TUP] THEN
    X_GEN_TAC `l:num list` THEN REWRITE_TAC[IN_ELIM_THM; waring_tup] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`waring_diff k l`; `G:num->real`; `1..P - ITLIST (+) l 0`]
           SUM_IMAGE) THEN
    SUBGOAL_THEN `LENGTH(l:num list) < k` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_NUMSEG] THEN ASM_MESON_TAC[WARING_DIFF_INJ]; ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG; IN_DIFF; IN_ELIM_THM] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`k:num`; `l:num list`; `0`; `n:num`]
               WARING_DIFF_STRICT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ARITH_TAC];
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `(n + ITLIST (+) l 0) EXP k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC WARING_DIFF_BOUND THEN ASM_ARITH_TAC;
        REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC];
      REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `ITLIST ( * ) l 1` THEN
      ASM_SIMP_TAC[ITLIST_MUL_DIVIDES] THEN
      MATCH_MP_TAC WARING_DIFF_DIVIDES THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  SIMP_TAC[FINITE_RESTRICT; FINITE_WARING_TUP; FINITE_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(if p then G else &0) = (if p then &1 else &0) * G:real`] THEN
  REWRITE_TAC[SUM_RMUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_WARING_TUP; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {d | d divides m}) pow j` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  MP_TAC(ISPECL [`{d | d divides m}`; `j:num`] LISTS_HAS_SIZE) THEN
  ASM_SIMP_TAC[FINITE_DIVISORS; LE_1; HAS_SIZE] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  MP_TAC(ISPECL [`{d | d divides m}`; `j:num`] LISTS_HAS_SIZE) THEN
  ASM_SIMP_TAC[FINITE_DIVISORS; LE_1; HAS_SIZE] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; waring_tup] THEN
  X_GEN_TAC `l:num list` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let WARING_KEXP_POW_SUM = prove
 (`!k P m x.
     1 <= k
     ==> waring_kexp k P x pow m =
         vsum(0..m * P EXP k)
           (\u. Cx(waring_conv (waring_kpow k) (P EXP k) m u) * expi(&u * x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `P:num`; `P EXP k`; `x:real`]
           WARING_KEXP_WEIGHTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC EXP_MONO_LT_IMP THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WARING_CONV_GEN; ETA_AX]]);;

let WARING_CONV_TOTAL = prove
 (`!w L s. sum(0..s * L) (waring_conv w L s) = sum(1..L) w pow s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`w:num->real`; `L:num`; `s:num`; `&0`] WARING_CONV_GEN) THEN
  REWRITE_TAC[REAL_MUL_RZERO; EXPI_0; COMPLEX_MUL_RID] THEN
  SIMP_TAC[VSUM_CX; FINITE_NUMSEG; GSYM CX_POW; CX_INJ] THEN
  REWRITE_TAC[ETA_AX]);;

let WARING_KPOW_TOTAL = prove
 (`!k P. 1 <= k ==> sum(1..P EXP k) (waring_kpow k) = &P`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `P:num`; `P EXP k`; `&0`] WARING_KEXP_WEIGHTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC EXP_MONO_LT_IMP THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[waring_kexp; REAL_MUL_RZERO; REAL_MUL_LZERO; EXPI_0;
              COMPLEX_MUL_RID] THEN
  SIMP_TAC[VSUM_CX; FINITE_NUMSEG; VSUM_CONST_NUMSEG; CX_INJ] THEN
  REWRITE_TAC[ADD_SUB; COMPLEX_CMUL; COMPLEX_MUL_RID; CX_INJ; ETA_AX] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let WARING_CONV_1 = prove
 (`!w L u. waring_conv w L 1 u = if 1 <= u /\ u <= L then w u else &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_CONV `1`; waring_conv] THEN
  REWRITE_TAC[GSYM(num_CONV `1`)] THEN
  TRANS_TAC EQ_TRANS `sum(1..L) (\m. if m = u then w u else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `m:num = u` THEN
    ASM_REWRITE_TAC[LE_REFL; SUB_REFL; REAL_MUL_RID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(u - m = 0)` (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO])
    THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG]]);;

let WARING_KEXP_CORR = prove
 (`!k P m M D.
     1 <= k /\ m * P EXP k + D < M
     ==> sum {t | t < M}
           (\t. Re(expi(&t / &M * &D)) *
                norm(waring_kexp k P (&t / &M)) pow (2 * m)) =
         &M * sum(0..m * P EXP k)
                (\u. waring_conv (waring_kpow k) (P EXP k) m u *
                     waring_conv (waring_kpow k) (P EXP k) m (u + D))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z:complex. norm z pow (2 * m) = norm(z pow m) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[COMPLEX_NORM_POW; REAL_POW_POW] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WARING_KEXP_POW_SUM] THEN MATCH_MP_TAC SUM_CORR_EXPI THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WARING_CONV_SUPPORT THEN ASM_REWRITE_TAC[]);;

let waring_hua = new_definition
 `waring_hua k P j =
  sum(0..2 EXP (j - 1) * P EXP k)
     (\u. waring_conv (waring_kpow k) (P EXP k) (2 EXP (j - 1)) u pow 2)`;;

let WARING_HUA_1 = prove
 (`!k P. 1 <= k ==> waring_hua k P 1 = &P`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[waring_hua; SUB_REFL; EXP; MULT_CLAUSES] THEN
  REWRITE_TAC[WARING_CONV_1] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `sum(0..P EXP k) (\u. if 1 <= u then waring_kpow k u else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH] THEN
    REWRITE_TAC[waring_kpow] THEN COND_CASES_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN `{u | u IN 0..P EXP k /\ 1 <= u} = 1..P EXP k` SUBST1_TAC
    THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      ASM_SIMP_TAC[ETA_AX; WARING_KPOW_TOTAL]]]);;

let WARING_HUA_STEP = prove
 (`!k P B j.
     2 <= k /\ 1 <= P /\ 1 <= j /\ j < k /\ &0 <= B /\
     (!m. 1 <= m /\ m <= P EXP k ==> &(CARD {d | d divides m}) <= B)
     ==> waring_hua k P (j + 1) <=
         (&2 * &P) pow (2 EXP j - j - 1) * &2 pow j *
         (&j * &P pow j * waring_hua k P j + B pow j * &P pow (2 EXP j))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = 2 EXP (j - 1)` THEN
  SUBGOAL_THEN `2 EXP j = 2 * m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `c = waring_conv (waring_kpow k) (P EXP k) m` THEN
  ABBREV_TAC `M = 4 * m * P EXP k + 1` THEN
  ABBREV_TAC
   `Hc = \D. sum(0..m * P EXP k) (\u. (c:num->real) u * c(u + D))` THEN
  SUBGOAL_THEN `!D. D <= P EXP k
                    ==> sum {t | t < M}
                          (\t. Re(expi(&t / &M * &D)) *
                               norm(waring_kexp k P (&t / &M)) pow (2 EXP j)) =
                        &M * (Hc:num->real) D`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Hc" THEN
    REWRITE_TAC[ASSUME `2 EXP j = 2 * m`] THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC WARING_KEXP_CORR THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "M" THEN
    SUBGOAL_THEN `P EXP k <= m * P EXP k` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&M * waring_hua k P (j + 1) =
    sum {t | t < M} (\t. norm(waring_kexp k P (&t / &M)) pow (2 EXP j) *
                         norm(waring_kexp k P (&t / &M)) pow (2 EXP j))`
  ASSUME_TAC THENL
   [REWRITE_TAC[waring_hua; ADD_SUB] THEN
    MP_TAC(SPECL [`k:num`; `P:num`; `2 EXP j`; `M:num`; `0`]
             WARING_KEXP_CORR) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "M" THEN REWRITE_TAC[ASSUME `2 EXP j = 2 * m`] THEN
      REWRITE_TAC[GSYM MULT_ASSOC] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO; EXPI_0; RE_CX; REAL_MUL_LID; ADD_CLAUSES] THEN
    REWRITE_TAC[REAL_POW_2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Cj = (&2 * &P) pow (2 EXP j - j - 1)` THEN
  SUBGOAL_THEN
   `&M * waring_hua k P (j + 1) <=
    &M * (Cj * sum (waring_tup j P)
           (\l. waring_wt l * sum(1..P - ITLIST (+) l 0)
                         (\n. (Hc:num->real)(waring_diff k l n))))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check
     (fun th -> lhs(concl th) = `&M * waring_hua k P (j + 1)`)) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {t | t < M}
      (\t. norm (waring_kexp k P (&t / &M)) pow (2 EXP j) *
           (Cj * sum (waring_tup j P)
                   (\l. waring_wt l * Re(waring_ssum k P (&t / &M) l))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN EXPAND_TAC "Cj" THEN
    MATCH_MP_TAC WEYL_ITER THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
    SUBGOAL_THEN
   `!l. l IN waring_tup j P
        ==> sum {t | t < M}
              (\t. Re(waring_ssum k P (&t / &M) l) *
                   norm(waring_kexp k P (&t / &M)) pow (2 EXP j)) =
            &M * sum(1..P - ITLIST (+) l 0)
              (\n. (Hc:num->real)(waring_diff k l n))`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num list` THEN REWRITE_TAC[waring_tup; IN_ELIM_THM] THEN
    STRIP_TAC THEN REWRITE_TAC[waring_ssum] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG; GSYM SUM_RMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(n + ITLIST (+) l 0) EXP k` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WARING_DIFF_BOUND THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  TRANS_TAC EQ_TRANS
   `Cj * sum (waring_tup j P)
           (\l. waring_wt l * sum {t | t < M}
                  (\t. Re(waring_ssum k P (&t / &M) l) *
                       norm(waring_kexp k P (&t / &M)) pow (2 EXP j)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
    REWRITE_TAC[FINITE_WARING_TUP; FINITE_NUMSEG_LT] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
    SUBGOAL_THEN
   `!l. l IN waring_tup j P
        ==> waring_wt l * sum {t | t < M}
                 (\t. Re(waring_ssum k P (&t / &M) l) *
                      norm(waring_kexp k P (&t / &M)) pow (2 EXP j)) =
            &M * waring_wt l * sum(1..P - ITLIST (+) l 0)
                           (\n. (Hc:num->real)(waring_diff k l n))`
  (fun th -> SIMP_TAC[th; SUM_EQ]) THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) &&
         type_of(fst(dest_forall(concl th))) = `:num list`
      then MP_TAC(SPEC `l:num list` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM SUM_LMUL] THEN REWRITE_TAC[REAL_MUL_AC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!D. &0 <= (Hc:num->real) D` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Hc" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN EXPAND_TAC "c" THEN
    SIMP_TAC[WARING_CONV_POS; WARING_KPOW_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Hc:num->real) 0 = waring_hua k P j` ASSUME_TAC THENL
   [EXPAND_TAC "Hc" THEN REWRITE_TAC[waring_hua; ADD_CLAUSES; REAL_POW_2] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(0..m * P EXP k) c = &P pow m` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[WARING_CONV_TOTAL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC WARING_KPOW_TOTAL THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (waring_tup j P)
      (\l. waring_wt l * sum(1..P - ITLIST (+) l 0)
                     (\n. (Hc:num->real)(waring_diff k l n)))
    <= &2 pow j *
    (&j * &P pow j * waring_hua k P j + B pow j * &P pow (2 EXP j))`
  ASSUME_TAC THENL
   [ABBREV_TAC `X = \l. sum(1..P - ITLIST (+) l 0)
                          (\n. (Hc:num->real)(waring_diff k l n))` THEN
    SUBGOAL_THEN `!l. &0 <= (X:num list->real) l` ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "X" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `sum (waring_tup j P) (\l. &2 pow j * (X:num list->real) l)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_WARING_TUP] THEN
      X_GEN_TAC `l:num list` THEN REWRITE_TAC[waring_tup; IN_ELIM_THM] THEN
      STRIP_TAC THEN EXPAND_TAC "X" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check
          (fun th -> concl th = `LENGTH(l:num list) = j`)) THEN
        REWRITE_TAC[WARING_WT_LE];
        MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `sum (waring_tup j P) (X:num list->real) =
      sum {l | l IN waring_tup j P /\ MEM 0 l} X +
      sum {l | l IN waring_tup j P /\ ~MEM 0 l} X`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`waring_tup j P`; `\l:num list. MEM 0 l`;
                     `X:num list->real`; `X:num list->real`] SUM_CASES) THEN
      REWRITE_TAC[FINITE_WARING_TUP; COND_ID; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
        `sum {l | l IN waring_tup j P /\ MEM 0 l}
           (\l. &P * waring_hua k P j)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN
        SIMP_TAC[FINITE_RESTRICT; FINITE_WARING_TUP] THEN
        X_GEN_TAC `l:num list` THEN REWRITE_TAC[IN_ELIM_THM] THEN
        STRIP_TAC THEN EXPAND_TAC "X" THEN ASM_SIMP_TAC[WARING_DIFF_ZERO] THEN
        SIMP_TAC[SUM_CONST_NUMSEG] THEN REWRITE_TAC[ADD_SUB] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check
          (fun th -> concl th = `(Hc:num->real) 0 = waring_hua k P j`)) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[SUM_RESTRICT_SET] THEN
      ONCE_REWRITE_TAC[REAL_ARITH
       `(if p then a else &0) = a * (if p then &1 else &0):real`] THEN
      REWRITE_TAC[SUM_LMUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&P * waring_hua k P j) * &j * &P pow (j - 1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[COUNT_MEM0] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check
          (fun th -> concl th = `(Hc:num->real) 0 = waring_hua k P j`)) THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `&P pow j = &P * &P pow (j - 1)` SUBST1_TAC THENL
         [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
          ASM_ARITH_TAC;
          REAL_ARITH_TAC]];
      EXPAND_TAC "X" THEN
      MP_TAC(ISPECL [`k:num`; `P:num`; `B:real`; `j:num`; `Hc:num->real`]
             HUA_FIBRE_SUM) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
      MP_TAC(ISPECL [`c:num->real`; `m * P EXP k`; `P EXP k`] CORR_SUM_LE) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "c" THEN SIMP_TAC[WARING_CONV_POS; WARING_KPOW_POS] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC WARING_CONV_SUPPORT THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "Hc" THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_POW_POW] THEN MATCH_MP_TAC(REAL_ARITH
       `a = b ==> x <= a ==> x <= b`) THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &M /\ &0 <= Cj` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN EXPAND_TAC "Cj" THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < a + 1`] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cj * sum (waring_tup j P)
      (\l. waring_wt l * sum(1..P - ITLIST (+) l 0)
                     (\n. (Hc:num->real)(waring_diff k l n)))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check
      (fun th -> is_comb(concl th) && is_comb(rator(concl th)) &&
                 fst(dest_const(rator(rator(concl th)))) = "real_le" &&
                 lhand(concl th) = `&M * waring_hua k P (j + 1)`)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let WARING_HUA_POS = prove
 (`!k P j. &0 <= waring_hua k P j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_hua] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2]);;

let WARING_HUA_BOUND = prove
 (`!k j. 2 <= k /\ 1 <= j /\ j <= k
         ==> ?Ch. !P B. 1 <= P /\ &1 <= B /\
                        (!m. 1 <= m /\ m <= P EXP k
                             ==> &(CARD {d | d divides m}) <= B)
                        ==> waring_hua k P j <= Ch * B pow (j - 1) *
                                         &P pow (2 EXP j - j)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
  ASM_CASES_TAC `j = 0` THENL
   [ASM_REWRITE_TAC[ARITH] THEN EXISTS_TAC `&1` THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `2 <= k ==> 1 <= k`;
                                         WARING_HUA_1] THEN
    REWRITE_TAC[real_pow; REAL_POW_1; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Ch:real`) THEN
  EXISTS_TAC `&2 pow (2 EXP j - 1) * (&j * Ch + &1)` THEN
  MAP_EVERY X_GEN_TAC [`P:num`; `B:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `P:num`; `B:real`; `j:num`] WARING_HUA_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(ASM_ARITH_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`P:num`; `B:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `e = 2 EXP j` THEN
  SUBGOAL_THEN `j + 1 <= e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MP_TAC(SPEC `j:num` LT_POW2_REFL) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (j + 1) = 2 * e` SUBST1_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &P` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Ch` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `waring_hua k P j / (B pow (j - 1) * &P pow (e - j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[WARING_HUA_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < B pow (j - 1) * &P pow (e - j)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_POW_LT THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&P pow j * waring_hua k P j <= Ch * B pow j * &P pow e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&P pow j * Ch * B pow (j - 1) * &P pow (e - j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&P pow e = &P pow j * &P pow (e - j)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `B pow (j - 1) <= B pow j` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= &P pow j /\ &0 <= &P pow (e - j) /\ &0 <= B pow (j - 1)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC
     [`a = (&P:real) pow j`; `b = (&P:real) pow (e - j)`;
      `c = (B:real) pow (j - 1)`; `d = (B:real) pow j`] THEN
    STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= Ch * a * b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(Ch * a * b) * c <= (Ch * a * b) * d
      ==> (a:real) * Ch * c * b <= Ch * d * a * b`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB; REAL_POW_MUL] THEN
  SUBGOAL_THEN `&2 pow (e - 1) = &2 pow (e - j - 1) * &2 pow j /\
                &P pow (2 * e - (j + 1)) = &P pow (e - j - 1) * &P pow e`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 pow (e - j - 1) * &P pow (e - j - 1) * &2 pow j`
  ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 pow (e - j - 1) * &P pow (e - j - 1) * &2 pow j) *
              (&j * Ch * B pow j * &P pow e + B pow j * &P pow e)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(a * b) * c * d = (a * b * c) * d:real`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + z <= y + z:real`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]);;
