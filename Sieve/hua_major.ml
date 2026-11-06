(* ========================================================================= *)
(* Hua's theorem II: set-up, fourth moment and major arcs.                   *)
(* * hua_psqw m = log p for m = p^2 with p prime, and hua_psqexp N x =       *)
(*   sum_{m <= N} hua_psqw(m) e(m x).  HUA_CIRCLE: with 5 N < M,             *)
(*     sum_{j < M} hua_psqexp N (j/M)^5 e(-N j/M) = M waring_conv hua_psqw N *)
(*     5 N,                                                                  *)
(*   the weighted number of representations of N as a sum of five prime      *)
(*   squares, and HUA_EXISTS: if it is positive such a representation        *)
(*   exists.  HUA_PSQEXP_LAMBDA compares hua_psqexp with the sum of          *)
(*   hua_minor.ml.                                                           *)
(* * HUA_FOURTH_MOMENT: for P^2 <= N < (P + 1)^2 and 2 N < M,                *)
(*     sum_{t < M} |hua_psqexp N (t/M)|^4                                    *)
(*       <= M log^4 P (P^2 + 2 P^2 (1 + log P^2)^3),                         *)
(*   from the solutions of x1^2 - x3^2 = x4^2 - x2^2 and the divisor fibres. *)
(* * Major arcs: hua_pcsum q a = sum_{r < q, (r,q) = 1} e(a r^2/q).  On      *)
(*   circ_arc M Kw q a, hua_psqexp N (j/M) is (hua_pcsum q a / phi q) times  *)
(*   waring_vsm 2 N (j/M - a/q) up to (phi(q) D + log q + 2)(1 + 2 pi N/Kw), *)
(*   D the uniform error of theta in the progressions mod q                  *)
(*   (RESIDUE_DECOMP_SQ, PARTIAL_SUM_MAJOR_SQ, MAJOR_ARC_APPROX_SQ,          *)
(*   ARC_APPROX_SQ).  HUA_MAJOR_APPROX and HUA_MAJOR_MAIN                    *)
(*   (WARING_VSM_ARC_MAIN) evaluate the major arc sum as M waring_conv       *)
(*   (waring_klam 2) N 5 N hua_sing N Q up to explicit errors, hua_sing N Q  *)
(*   = sum_{q <= Q} hua_term N q.                                            *)
(* ========================================================================= *)

needs "Sieve/hua_minor.ml";;
needs "Sieve/waring_major.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Prime squares and the circle method.                                      *)
(* ------------------------------------------------------------------------- *)

let WARING_CONV_POS_EXISTS = prove
 (`!(w:num->real) L.
     (!m. &0 <= w m)
     ==> !s n. &0 < waring_conv w L s n
               ==> ?x. (!i. 1 <= i /\ i <= s ==> &0 < w(x i)) /\
                       nsum(1..s) x = n`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC[waring_conv] THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN
    DISCH_TAC THEN EXISTS_TAC `\i:num. 1` THEN
    ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH] THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?m. 1 <= m /\ m <= L /\ m <= n /\ &0 < (w:num->real) m /\
                    &0 < waring_conv w L s (n - m)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    UNDISCH_TAC
     `&0 < sum (1..L) (\m. if m <= n
                           then (w:num->real) m * waring_conv w L s (n - m)
                           else &0)` THEN
    MATCH_MP_TAC(REAL_ARITH `s <= &0 ==> &0 < s ==> F`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..L) (\m:num. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0; REAL_LE_REFL]] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `(w:num->real) m = &0 \/ waring_conv w L s (n - m) = &0`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`w:num->real`; `L:num`; `s:num`;
      `n - m:num`] WARING_CONV_POS) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `m:num` (ASSUME `!m:num. &0 <= (w:num->real) m`)) THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL];
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - m:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i. if i = SUC s then m else (x:num->num) i` THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum(1..s) (\i. if i = SUC s then m else (x:num->num) i) =
    nsum(1..s) x` SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let hua_psqw = new_definition
 `hua_psqw m = sum {p | prime p /\ p EXP 2 = m} (\p. log(&p))`;;

let HUA_PSQW_POS = prove
 (`!m. &0 <= hua_psqw m`,
  GEN_TAC THEN REWRITE_TAC[hua_psqw] THEN MATCH_MP_TAC SUM_POS_LE THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_POS THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC);;

let HUA_PSQW_POS_EXISTS = prove
 (`!m. &0 < hua_psqw m ==> ?p. prime p /\ p EXP 2 = m`,
  GEN_TAC THEN REWRITE_TAC[hua_psqw] THEN
  ASM_CASES_TAC `{p | prime p /\ p EXP 2 = m} = {}` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES; REAL_LT_REFL];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MESON_TAC[]]);;

let hua_psqexp = new_definition
 `hua_psqexp N x = vsum(1..N) (\m. Cx(hua_psqw m) * expi(&m * x))`;;

let HUA_PSQEXP_PRIMES = prove
 (`!N P x. P EXP 2 <= N /\ N < (P + 1) EXP 2
           ==> hua_psqexp N x =
               vsum(1..P) (\n. Cx(if prime n then log(&n) else &0) *
                               expi(&(n EXP 2) * x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. n EXP 2`;
                 `\n. Cx(if prime n then log(&n) else &0) *
                      expi(&(n EXP 2) * x)`;
                 `1..P`; `1..N`] VSUM_GROUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      TRANS_TAC LE_TRANS `P EXP 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[hua_psqexp] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[hua_psqw] THEN
  SUBGOAL_THEN
   `{p | prime p /\ p EXP 2 = m} =
    {n | n IN 1..P /\ n EXP 2 = m /\ prime n}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `N < (P + 1) EXP 2` THEN REWRITE_TAC[NOT_LT] THEN
    TRANS_TAC LE_TRANS `m:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RESTRICT_SET; VSUM_RESTRICT_SET] THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN ASM_CASES_TAC `n EXP 2 = m` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `prime n` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]);;

let HUA_PSQEXP_LAMBDA = prove
 (`!N P x. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2
           ==> norm(hua_psqexp N x -
                    vsum(1..P) (\n. Cx(mangoldt n) * expi(&(n EXP 2) * x)))
               <= sqrt(&P) * log(&P) pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HUA_PSQEXP_PRIMES] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG; GSYM COMPLEX_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM CX_SUB] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..P) (\n. mangoldt n - (if prime n then log(&n) else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_EXPI;
     REAL_MUL_RID] THEN
    COND_CASES_TAC THENL
     [ASM_SIMP_TAC[MANGOLDT_PRIME] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_ABS_NEG] THEN
      MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN REAL_ARITH_TAC];
    MATCH_MP_TAC PRIME_POWER_SUM_BOUND THEN ASM_REWRITE_TAC[]]);;

let HUA_CIRCLE = prove
 (`!N M. 5 * N < M
         ==> vsum {j | j < M}
               (\j. hua_psqexp N (&j / &M) pow 5 * expi(--(&N * &j / &M))) =
             Cx(&M * waring_conv hua_psqw N 5 N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hua_psqw`; `N:num`; `5`; `M:num`; `N:num`; `&0`]
    WARING_CONV_CIRCLE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID; hua_psqexp] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

let HUA_EXISTS = prove
 (`!N. &0 < waring_conv hua_psqw N 5 N
       ==> ?p1 p2 p3 p4 p5. prime p1 /\ prime p2 /\ prime p3 /\
                            prime p4 /\ prime p5 /\
                            p1 EXP 2 + p2 EXP 2 + p3 EXP 2 + p4 EXP 2 +
                            p5 EXP 2 = N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hua_psqw`; `N:num`] WARING_CONV_POS_EXISTS) THEN
  REWRITE_TAC[HUA_PSQW_POS] THEN DISCH_THEN(MP_TAC o SPECL [`5`; `N:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 5 ==> ?p. prime p /\ p EXP 2 = x i`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HUA_PSQW_POS_EXISTS THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:num->num`) THEN
  MAP_EVERY EXISTS_TAC [`p 1:num`; `p 2:num`; `p 3:num`; `p 4:num`;
                        `p 5:num`] THEN
  UNDISCH_TAC `nsum(1..5) x = N` THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; ARITH; NSUM_TRIV_NUMSEG; ADD_CLAUSES] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th) THEN
    MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th)) THEN
  REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The fourth moment.                                                        *)
(* ------------------------------------------------------------------------- *)

let KPOW2_SHIFT_COUNT = prove
 (`!D L. 1 <= D
         ==> sum(0..L) (\u. waring_kpow 2 u * waring_kpow 2 (u + D)) <=
             &(CARD {d | d divides D})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(0..L) (\u. waring_kpow 2 u * waring_kpow 2 (u + D)) =
    &(CARD {u | u IN 0..L /\ (?k. 1 <= k /\ u = k EXP 2) /\
                (?l. 1 <= l /\ u + D = l EXP 2)})`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `sum {u | u IN 0..L /\ (?k. 1 <= k /\ u = k EXP 2) /\
               (?l. 1 <= l /\ u + D = l EXP 2)} (\u. &1)` THEN
    CONJ_TAC THENL
     [ALL_TAC; SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG;
                        REAL_MUL_RID]] THEN
    REWRITE_TAC[SUM_RESTRICT_SET] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
    REWRITE_TAC[waring_kpow] THEN
    REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO;
                                             REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ABBREV_TAC `S = {u | u IN 0..L /\ (?k. 1 <= k /\ u = k EXP 2) /\
                       (?l. 1 <= l /\ u + D = l EXP 2)}` THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN S ==> ?k l. 1 <= k /\ u = k EXP 2 /\ u + D = l EXP 2 /\ k < l`
  MP_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `l:num`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `l EXP 2 <= k EXP 2` MP_TAC THENL
     [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:num->num` (X_CHOOSE_TAC `ll:num->num`)) THEN
  TRANS_TAC LE_TRANS `CARD(IMAGE (\u. (ll:num->num) u - kk u) S)` THEN
    CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:num`; `v:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `u:num` th) THEN
                            MP_TAC(SPEC `v:num` th)) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `k1 = (kk:num->num) u` THEN
      ABBREV_TAC `l1 = (ll:num->num) u` THEN
    ABBREV_TAC `k2 = (kk:num->num) v` THEN
      ABBREV_TAC `l2 = (ll:num->num) v` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(l1 - k1) * (l1 + k1) = (l2 - k2) * (l2 + k2):num`
    MP_TAC THENL
     [ASM_SIMP_TAC[GSYM SQ_DIFF_FACTOR; LT_IMP_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[EQ_MULT_LCANCEL] THEN
    SUBGOAL_THEN `~(l2 - k2 = 0:num)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `k1 = k2:num` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `D = ((ll:num->num) u - kk u) * (ll u + kk u)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM SQ_DIFF_FACTOR; LT_IMP_LE] THEN ASM_ARITH_TAC;
      NUMBER_TAC];
    MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC]);;

let RE_EXPI_NEG = prove
 (`!x. Re(expi(--x)) = Re(expi x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM CNJ_EXPI; RE_CNJ]);;

let HUA_PSQEXP_ZERO_BASED = prove
 (`!N x. hua_psqexp N x =
         vsum(0..N)
           (\u. Cx(if u <= N then hua_psqw u else &0) * expi(&u * x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hua_psqexp] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
  SUBGOAL_THEN `hua_psqw 0 = &0` SUBST1_TAC THENL
   [REWRITE_TAC[hua_psqw] THEN MATCH_MP_TAC SUM_EQ_0 THEN
    REWRITE_TAC[IN_ELIM_THM; EXP_EQ_0; ARITH_EQ] THEN
    MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  REWRITE_TAC[LE_0; COMPLEX_MUL_LZERO; COMPLEX_ADD_LID; ADD_CLAUSES] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN SIMP_TAC[]);;

let hua_corr = new_definition
 `hua_corr N D = sum(0..N) (\u. (if u <= N then hua_psqw u else &0) *
                             (if u + D <= N then hua_psqw(u + D) else &0))`;;

let HUA_FOURTH_IDENTITY = prove
 (`!N P M. P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ 2 * N < M
           ==> sum {t | t < M} (\t. norm(hua_psqexp N (&t / &M)) pow 4) =
               &M * sum(1..P) (\k. sum(1..P) (\l.
                 (if prime k then log(&k) else &0) *
                 (if prime l then log(&l) else &0) *
                 hua_corr N ((k EXP 2 - l EXP 2) + (l EXP 2 - k EXP 2))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `cw = \u. if u <= N then hua_psqw u else &0` THEN
  ABBREV_TAC `cp = \n. if prime n then log(&n) else &0` THEN
  SUBGOAL_THEN
   `!t. norm(hua_psqexp N (&t / &M)) pow 4 =
        norm(vsum(1..P) (\n. Cx(cp n) * expi(&(n EXP 2) * (&t / &M)))) pow 2 *
        norm(vsum(0..N) (\u. Cx(cw u) * expi(&u * (&t / &M)))) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "cp" THEN EXPAND_TAC "cw" THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM HUA_PSQEXP_ZERO_BASED] THEN
    ASM_SIMP_TAC[GSYM HUA_PSQEXP_PRIMES] THEN
    REWRITE_TAC[ARITH_RULE `4 = 2 + 2`; REAL_POW_ADD];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_VSUM_EXPI_POW2] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(a * b * c) * d:real = (a * b) * c * d`] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN `(cp:num->real) k = (if prime k then log(&k) else &0) /\
                (cp:num->real) l = (if prime l then log(&l) else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "cp" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a * b) * c = m * a * b * h <=> a * b * c = a * b *
      (m * h):real`] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ABBREV_TAC `D = (k EXP 2 - l EXP 2) + (l EXP 2 - k EXP 2)` THEN
  SUBGOAL_THEN `D <= N:num` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    SUBGOAL_THEN `k EXP 2 <= N /\ l EXP 2 <= N` MP_TAC THENL
     [CONJ_TAC THEN TRANS_TAC LE_TRANS `P EXP 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. Re(expi(&(k EXP 2) * &t / &M - &(l EXP 2) * &t / &M)) =
        Re(expi(&t / &M * &D))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "D" THEN
    DISJ_CASES_TAC(ARITH_RULE `l <= k \/ k < l:num`) THENL
     [SUBGOAL_THEN `l EXP 2 <= k EXP 2` ASSUME_TAC THENL
       [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `l EXP 2 - k EXP 2 = 0` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ADD_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `k EXP 2 <= l EXP 2` ASSUME_TAC THENL
       [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `k EXP 2 - l EXP 2 = 0` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ADD_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM RE_EXPI_NEG] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cw:num->real`; `N:num`; `M:num`; `D:num`] SUM_CORR_EXPI) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "cw" THEN SIMP_TAC[GSYM NOT_LT];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[hua_corr] THEN
  EXPAND_TAC "cw" THEN REWRITE_TAC[]);;

let HUA_PSQW_LE_WARING_KPOW = prove
 (`!N P u. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ u <= N
           ==> hua_psqw u <= log(&P) * waring_kpow 2 u`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?p. prime p /\ p EXP 2 = u` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `waring_kpow 2 u = &1` SUBST1_TAC THENL
     [REWRITE_TAC[waring_kpow] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID; hua_psqw] THEN
    SUBGOAL_THEN `{q | prime q /\ q EXP 2 = u} = {p}` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
           X_GEN_TAC `q:num` THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
          REWRITE_TAC[EXP_MONO_EQ; ARITH_EQ] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
    REWRITE_TAC[SUM_SING] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN CONJ_TAC THENL
         [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
        UNDISCH_TAC `N < (P + 1) EXP 2` THEN REWRITE_TAC[NOT_LT] THEN
        TRANS_TAC LE_TRANS `u:num` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
        ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hua_psqw u = &0` SUBST1_TAC THENL
   [REWRITE_TAC[hua_psqw] THEN MATCH_MP_TAC SUM_EQ_0 THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[WARING_KPOW_POS] THEN
  MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let CW_LE_WARING_KPOW = prove
 (`!N P u. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2
           ==> &0 <= (if u <= N then hua_psqw u else &0) /\
               (if u <= N then hua_psqw u else &0) <= log(&P) *
               waring_kpow 2 u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[HUA_PSQW_POS; REAL_LE_REFL] THENL
   [MATCH_MP_TAC HUA_PSQW_LE_WARING_KPOW THEN EXISTS_TAC `N:num` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[WARING_KPOW_POS] THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]]);;

let HUA_CORR_POS = prove
 (`!N D. &0 <= hua_corr N D`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hua_corr] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  CONJ_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; HUA_PSQW_POS]);;

let HUA_CORR_WARING_KPOW = prove
 (`!N P D. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2
           ==> hua_corr N D <=
               log(&P) pow 2 *
               sum(0..N) (\u. waring_kpow 2 u * waring_kpow 2 (u + D))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hua_corr; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH `(l * l) * a * b = (l * a) * (l *
      b):real`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_MESON_TAC[CW_LE_WARING_KPOW]);;

let HUA_CORR_0 = prove
 (`!N P. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2
         ==> hua_corr N 0 <= log(&P) pow 2 * &P`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `log(&P) pow 2 *
    sum(0..N) (\u. waring_kpow 2 u * waring_kpow 2 (u + 0))` THEN
  ASM_SIMP_TAC[HUA_CORR_WARING_KPOW] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2; ADD_CLAUSES] THEN
  SUBGOAL_THEN `!u. waring_kpow 2 u * waring_kpow 2 u = waring_kpow 2 u`
  (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[waring_kpow] THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`2`; `P:num`] WARING_KPOW_TOTAL) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  SUBGOAL_THEN `waring_kpow 2 0 = &0` SUBST1_TAC THENL
   [REWRITE_TAC[waring_kpow] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `0 = y EXP 2` THEN DISCH_THEN(MP_TAC o SYM) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LID; ADD_CLAUSES; ETA_AX] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `u:num` THEN STRIP_TAC THEN REWRITE_TAC[waring_kpow] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `y <= P:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `N < (P + 1) EXP 2` THEN REWRITE_TAC[NOT_LT] THEN
    TRANS_TAC LE_TRANS `u:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~(1 <= u /\ u <= P EXP 2)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]);;

let HUA_CORR_D = prove
 (`!N P D. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ 1 <= D
           ==> hua_corr N D <= log(&P) pow 2 * &(CARD {d | d divides D})`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `log(&P) pow 2 *
    sum(0..N) (\u. waring_kpow 2 u * waring_kpow 2 (u + D))` THEN
  ASM_SIMP_TAC[HUA_CORR_WARING_KPOW] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_POW_2; KPOW2_SHIFT_COUNT]);;

let SUM_SQDIFF_SPLIT = prove
 (`!(f:num->real) Kq.
     sum(1..Kq) (\k. sum(1..Kq) (\l.
       f((k EXP 2 - l EXP 2) + (l EXP 2 - k EXP 2)))) =
     &Kq * f 0 +
     &2 * sum(1..Kq) (\k. sum(1..Kq) (\l.
            if l < k then f(k EXP 2 - l EXP 2) else &0))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!k l. f((k EXP 2 - l EXP 2) + (l EXP 2 - k EXP 2)) =
          (if l = k then (f:num->real) 0 else &0) +
          (if l < k then f(k EXP 2 - l EXP 2) else &0) +
          (if k < l then f(l EXP 2 - k EXP 2) else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    ASM_CASES_TAC `l:num = k` THENL
     [ASM_REWRITE_TAC[LT_REFL; SUB_REFL; ADD_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `l < k \/ k < l:num` DISJ_CASES_TAC THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `l EXP 2 <= k EXP 2` ASSUME_TAC THENL
       [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `l < k ==> ~(k < l:num)`] THEN
      SUBGOAL_THEN `l EXP 2 - k EXP 2 = 0` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[ADD_CLAUSES] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `k EXP 2 <= l EXP 2` ASSUME_TAC THENL
       [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `k < l ==> ~(l < k:num)`] THEN
      SUBGOAL_THEN `k EXP 2 - l EXP 2 = 0` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[ADD_CLAUSES] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN
   `sum(1..Kq) (\k. sum(1..Kq) (\l. if l = k then (f:num->real) 0 else &0)) =
    &Kq * f 0`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN
    TRANS_TAC EQ_TRANS `sum(1..Kq) (\k. (f:num->real) 0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. b = c ==> a + c + b = a + &2 * c`) THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let HUA_FOURTH_MOMENT = prove
 (`!N P M. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ 2 * N < M
           ==> sum {t | t < M} (\t. norm(hua_psqexp N (&t / &M)) pow 4) <=
               &M * log(&P) pow 4 *
               (&P pow 2 + &2 * &P pow 2 * (&1 + log(&(P EXP 2))) pow 3)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HUA_FOURTH_IDENTITY] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN
  ABBREV_TAC `L = log(&P)` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n <= P ==> &0 <= (if prime n then log(&n) else &0) /\
                   (if prime n then log(&n) else &0) <= L`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      EXPAND_TAC "L" THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `L pow 2 * sum(1..P) (\k. sum(1..P) (\l.
      hua_corr N ((k EXP 2 - l EXP 2) + (l EXP 2 - k EXP 2))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[HUA_CORR_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hua_corr N`; `P:num`] SUM_SQDIFF_SPLIT) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`P:num`; `hua_corr N`] SQDIFF_FIBRE) THEN
  REWRITE_TAC[HUA_CORR_POS] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(1..P EXP 2) (\r. &(CARD {d | d divides r}) * hua_corr N r) <=
    L pow 2 * (&(P EXP 2) * (&1 + log(&(P EXP 2))) pow 3)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sum(1..P EXP 2) (\r. L pow 2 * &(CARD {d | d divides r}) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      TRANS_TAC REAL_LE_TRANS
       `&(CARD {d | d divides r}) * (L pow 2 * &(CARD {d | d divides r}))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        EXPAND_TAC "L" THEN MATCH_MP_TAC HUA_CORR_D THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        REWRITE_TAC[REAL_MUL_AC]];
      REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC TAU_SQUARE_SUM THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `hua_corr N 0 <= L pow 2 * &P` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC HUA_CORR_0 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Sd = sum(1..P) (\k. sum(1..P) (\l.
            if l < k then hua_corr N (k EXP 2 - l EXP 2) else &0))` THEN
  ABBREV_TAC
    `St = sum(1..P EXP 2) (\r. &(CARD {d | d divides r}) * hua_corr N r)`
  THEN
  SUBGOAL_THEN `&P * hua_corr N 0 <= &P * (L pow 2 * &P)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `L pow 2 * (&P * hua_corr N 0 + &2 * Sd) <=
    L pow 2 * (&P * (L pow 2 * &P) +
               &2 * (L pow 2 * (&(P EXP 2) * (&1 + log(&(P EXP 2))) pow 3)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Major arcs.                                                               *)
(* ------------------------------------------------------------------------- *)

let hua_pcsum = new_definition
 `hua_pcsum q a = vsum {r | r < q /\ coprime(r,q)} (\r. expi(&a * &(r EXP 2) /
     &q))`;;

let CARD_COPRIME_RESIDUES = prove
 (`!q. CARD {a | a < q /\ coprime(a,q)} = phi q`,
  GEN_TAC THEN REWRITE_TAC[PHI_ALT] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

let HUA_PCSUM_TRIVIAL = prove
 (`!q a. norm(hua_pcsum q a) <= &(phi q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hua_pcsum] THEN
  TRANS_TAC REAL_LE_TRANS `sum {r | r < q /\ coprime(r,q)} (\r. &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_COPRIME_RESIDUES; NORM_EXPI; REAL_LE_REFL];
    SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES; CARD_COPRIME_RESIDUES] THEN
    REAL_ARITH_TAC]);;

let RESIDUE_DECOMP_SQ = prove
 (`!q a h.
     1 <= q
     ==> vsum(1..h) (\m. Cx(if prime m then log(&m) else &0) *
                         expi(&(m EXP 2) * &a / &q)) =
         vsum {b | b < q}
           (\b. expi(&a * &(b EXP 2) / &q) *
                Cx(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                       (\p. log(&p))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!m. expi(&(m EXP 2) * &a / &q) =
                    expi(&a * &((m MOD q) EXP 2) / &q)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`q:num`; `m EXP 2`; `(m MOD q) EXP 2`; `a:num`]
      EXPI_CONG) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CONG_EXP THEN REWRITE_TAC[CONG_RMOD; CONG_REFL];
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum(1..h) (\m. vsum {b | b < q}
       (\b. if b = m MOD q
            then Cx(if prime m then log(&m) else &0) *
                 expi(&a * &(b EXP 2) / &q)
            else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `vsum {b | b < q}
       (\b. if b = m MOD q
            then Cx(if prime m then log(&m) else &0) *
                 expi(&a * &((m MOD q) EXP 2) / &q)
            else vec 0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VSUM_DELTA; IN_ELIM_THM] THEN ASM_REWRITE_TAC[MOD_LT_EQ];
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

let PARTIAL_SUM_MAJOR_SQ = prove
 (`!q a h D.
     1 <= q /\
     (!b. b < q /\ coprime(b,q)
          ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                      (\p. log(&p)) - &h / &(phi q)) <= D)
     ==> norm(vsum(1..h) (\m. Cx(if prime m then log(&m) else &0) *
                              expi(&(m EXP 2) * &a / &q)) -
              Cx(&h / &(phi q)) * hua_pcsum q a) <= &(phi q) * D + log(&q)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RESIDUE_DECOMP_SQ] THEN
  MP_TAC(ISPECL
   [`{b:num | b < q}`; `\b. coprime(b,q)`;
    `\b. expi(&a * &(b EXP 2) / &q) *
         Cx(sum {p | prime p /\ p <= h /\ (p == b) (mod q)} (\p. log(&p)))`;
    `\b. expi(&a * &(b EXP 2) / &q) *
         Cx(sum {p | prime p /\ p <= h /\ (p == b) (mod q)} (\p. log(&p)))`]
   VSUM_CASES) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; COND_ID; ETA_AX; IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `Cx(&h / &(phi q)) * hua_pcsum q a =
    vsum {b | b < q /\ coprime(b,q)}
      (\b. expi(&a * &(b EXP 2) / &q) * Cx(&h / &(phi q)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[hua_pcsum] THEN
    GEN_REWRITE_TAC LAND_CONV [COMPLEX_MUL_SYM] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_COPRIME_RESIDUES];
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

let SUM_ODD_LE_SQUARE = prove
 (`!P. sum(1..P-1) (\h. &2 * &h + &1) <= &P pow 2`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH; SUM_CLAUSES_NUMSEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1] THEN ASM_CASES_TAC `P = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `P = SUC(P - 1)` (fun th -> GEN_REWRITE_TAC
    (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  SUBGOAL_THEN `SUC(P - 1) = P` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `sum(1..P-1) (\h. &2 * &h + &1) <= &P pow 2` THEN
  ABBREV_TAC `s = sum(1..P-1) (\h. &2 * &h + &1)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let MAJOR_ARC_APPROX_SQ = prove
 (`!P q a beta D.
     1 <= q /\
     (!h b. h <= P /\ b < q /\ coprime(b,q)
            ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                        (\p. log(&p)) - &h / &(phi q)) <= D)
     ==> norm(vsum(1..P) (\m. Cx(if prime m then log(&m) else &0) *
                              expi(&(m EXP 2) * (&a / &q + beta))) -
              Cx(inv(&(phi q))) * hua_pcsum q a * waring_kexp 2 P beta)
         <= (&(phi q) * D + log(&q)) * (&1 + &2 * pi * &P pow 2 * abs beta)`,
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
   `vsum(1..P) (\m. Cx(if prime m then log(&m) else &0) *
                    expi(&(m EXP 2) * (&a / &q + beta))) -
    Cx(inv(&(phi q))) * hua_pcsum q a * waring_kexp 2 P beta =
    vsum(1..P) (\m. (Cx(if prime m then log(&m) else &0) *
                     expi(&(m EXP 2) * &a / &q) -
                     Cx(inv(&(phi q))) * hua_pcsum q a) *
                    expi(&(m EXP 2) * beta))`
  SUBST1_TAC THENL
   [REWRITE_TAC[waring_kexp] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; EXPI_ADD] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `beta * &(x EXP 2) = &(x EXP 2) * beta`] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\m. Cx(if prime m then log(&m) else &0) * expi(&(m EXP 2) * &a / &q) -
         Cx(inv(&(phi q))) * hua_pcsum q a`;
    `\m. expi(&(m EXP 2) * beta)`; `P:num`; `Mb:real`] ABEL_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    SIMP_TAC[VSUM_SUB; FINITE_NUMSEG; VSUM_CONST_NUMSEG; ADD_SUB] THEN
    REWRITE_TAC[COMPLEX_CMUL] THEN
    SUBGOAL_THEN `Cx(&h) * Cx(inv(&(phi q))) * hua_pcsum q a =
                  Cx(&h / &(phi q)) * hua_pcsum q a` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; CX_MUL; COMPLEX_MUL_ASSOC]; ALL_TAC] THEN
    EXPAND_TAC "Mb" THEN MATCH_MP_TAC PARTIAL_SUM_MAJOR_SQ THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_EXPI] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..P-1) (\h. &2 * pi * abs beta * (&2 * &h + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&((h + 1) EXP 2) * beta =
                  &(h EXP 2) * beta + (&2 * &h + &1) * beta`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_ADD] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[EXPI_ADD] THEN
    REWRITE_TAC[COMPLEX_RING `a * b - a:complex = a * (b - Cx(&1))`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_LID] THEN
    TRANS_TAC REAL_LE_TRANS `&2 * pi * abs((&2 * &h + &1) * beta)` THEN
    REWRITE_TAC[NORM_EXPI_SUB_1_UPPER] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(&2 * &h + &1) = &2 * &h + &1` SUBST1_TAC THENL
     [REAL_ARITH_TAC; REAL_ARITH_TAC];
    REWRITE_TAC[SUM_LMUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `&2 * pi * &P pow 2 * b = &2 * pi * b * &P pow 2`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS; SUM_ODD_LE_SQUARE]]);;

let HUA_PSQEXP_INTEGER_ADD = prove
 (`!N x n. integer n ==> hua_psqexp N (x + n) = hua_psqexp N x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hua_psqexp] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC EXPI_INTEGER_ADD THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let HUA_PSQEXP_TRIVIAL = prove
 (`!N P x. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2
           ==> norm(hua_psqexp N x) <= &P * log(&P)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HUA_PSQEXP_PRIMES] THEN
  TRANS_TAC REAL_LE_TRANS `sum(1..P) (\n. log(&P))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; COMPLEX_NORM_CX;
     REAL_MUL_RID] THEN
    SUBGOAL_THEN `&0 <= log(&n) /\ log(&n) <= log(&P)` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
      COND_CASES_TAC THEN REAL_ARITH_TAC];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]);;

let WARING_CSUM_1 = prove
 (`!a. waring_csum 2 1 a = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[waring_csum] THEN
  SUBGOAL_THEN `{r | r < 1} = {0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN ARITH_TAC;
    REWRITE_TAC[VSUM_SING; ARITH; REAL_MUL_RZERO; real_div; REAL_MUL_LZERO;
                EXPI_0]]);;

let HUA_PCSUM_NORMALIZED = prove
 (`!q a. 1 <= q ==> norm(Cx(inv(&(phi q))) * hua_pcsum q a) <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(phi q)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV;
              REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID;
               HUA_PCSUM_TRIVIAL]);;

let ARC_APPROX_SQ = prove
 (`!N P M Kw q a j D.
     P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ 1 <= q /\ 1 <= Kw /\
     (!h b. h <= P /\ b < q /\ coprime(b,q)
            ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                        (\p. log(&p)) - &h / &(phi q)) <= D) /\
     j IN circ_arc M Kw q a
     ==> norm(hua_psqexp N (&j / &M) -
              Cx(inv(&(phi q))) * hua_pcsum q a *
              waring_vsm 2 N (&j / &M - &a / &q))
         <= (&(phi q) * D + log(&q) + &2) * (&1 + &2 * pi * &N / &Kw)`,
  REWRITE_TAC[circ_arc; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `1 MOD q`]) THEN
    ASM_REWRITE_TAC[LE_0; MOD_LT_EQ; COPRIME_LMOD; COPRIME_1] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&j / &M - &a / &q` NDIST_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `b = &j / &M - &a / &q - n` THEN
  SUBGOAL_THEN `abs b <= inv(&Kw)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `waring_vsm 2 N (&j / &M - &a / &q) = waring_vsm 2 N b`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&j / &M - &a / &q = b + n` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[WARING_VSM_INTEGER_ADD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hua_psqexp N (&j / &M) = hua_psqexp N (&a / &q + b)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&j / &M = (&a / &q + b) + n` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[HUA_PSQEXP_INTEGER_ADD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * pi * &N * abs b /\
                &2 * pi * &N * abs b <= &2 * pi * &N / &Kw`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS; REAL_ABS_POS; PI_POS_LE];
      REWRITE_TAC[real_div] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
              [SIMP_TAC[REAL_POS; PI_POS_LE]; ALL_TAC]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(hua_psqexp N (&a / &q + b) -
         Cx(inv(&(phi q))) * hua_pcsum q a * waring_kexp 2 P b) +
    norm(Cx(inv(&(phi q))) * hua_pcsum q a *
         (waring_kexp 2 P b - waring_vsm 2 N b))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `x - z = (x - y) + w ==> norm(x - z:complex) <= norm(x - y) + norm w`)
    THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(x + z + &2) * y = (x + z) * y + &2 * y`] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[HUA_PSQEXP_PRIMES] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `(&(phi q) * D + log(&q)) * (&1 + &2 * pi * &P pow 2 * abs b)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MAJOR_ARC_APPROX_SQ THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * pi * &N * abs b` THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
            [SIMP_TAC[REAL_POS; PI_POS_LE]; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC HUA_PCSUM_NORMALIZED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (&1 + &2 * pi * &N * abs b)` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`2`; `P:num`; `N:num`; `1`; `0`; `b:real`]
      WARING_KEXP_MAJOR_APPROX) THEN
    ASM_REWRITE_TAC[WARING_CSUM_1; REAL_DIV_1; REAL_ADD_LID; REAL_INV_1;
                    COMPLEX_MUL_LID; ARITH; REAL_MUL_LID] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_LID];
    ASM_REAL_ARITH_TAC]);;

let HUA_MAJOR_APPROX = prove
 (`!N P M Kw Q D.
     1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ 1 <= Q /\ 2 <= Kw /\
     2 * Q EXP 2 < Kw /\ &0 <= D /\
     (!q h b. 1 <= q /\ q <= Q /\ h <= P /\ b < q /\ coprime(b,q)
              ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                          (\p. log(&p)) - &h / &(phi q)) <= D)
     ==> norm(vsum (circ_major M Kw Q)
                (\j. hua_psqexp N (&j / &M) pow 5 * expi(--(&N * &j / &M))) -
              vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
                (\a. vsum (circ_arc M Kw q a)
                  (\j. (Cx(inv(&(phi q))) * hua_pcsum q a *
                        waring_vsm 2 N (&j / &M - &a / &q)) pow 5 *
                       expi(--(&N * &j / &M))))))
         <= &Q * &Q * (&3 * (&2 * &M / &Kw + &1)) *
            (&5 * (&P * log(&P) + &P + &1) pow 4 *
             ((&Q * D + log(&Q) + &2) * (&1 + &2 * pi * &N / &Kw)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CIRC_MAJOR_VSUM] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) TRIPLE_NORM_LE o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_COPRIME_RESIDUES; CIRC_ARC_FINITE] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&0 <= log(&P) /\ &0 <= log(&Q)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  ABBREV_TAC `B = &P * log(&P) + &P + &1` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= x + y + &1`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + &2 * pi * &N / &Kw` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POS; PI_POS_LE; REAL_LE_DIV];
    ALL_TAC] THEN
  ABBREV_TAC `X = &5 * B pow 4 *
                  ((&Q * D + log(&Q) + &2) * (&1 + &2 * pi * &N / &Kw))` THEN
  ABBREV_TAC `Y = &3 * (&2 * &M / &Kw + &1)` THEN
  SUBGOAL_THEN `&0 <= X /\ &0 <= Y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LE_ADD; REAL_LE_DIV;
                 REAL_LE_MUL; PI_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Q) (\q. &Q * Y * X)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {a | a < q /\ coprime(a,q)} (\a. Y * X)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {a | a < q:num}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      SET_TAC[];
      ASM_REWRITE_TAC[CARD_NUMSEG_LT]]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
  X_GEN_TAC `a:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (circ_arc M Kw q a) (\j. X)` THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[SUM_CONST; CIRC_ARC_FINITE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Y" THEN MATCH_MP_TAC CARD_ARC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[CIRC_ARC_FINITE] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; COMPLEX_NORM_MUL; NORM_EXPI;
              REAL_MUL_RID] THEN
  EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&5 * B pow (5 - 1) *
    norm(hua_psqexp N (&j / &M) -
         Cx(inv(&(phi q))) * hua_pcsum q a *
         waring_vsm 2 N (&j / &M - &a / &q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPLEX_POW_DIFF_LE THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`N:num`; `P:num`; `&j / &M`] HUA_PSQEXP_TRIVIAL) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * (&P + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN
        MATCH_MP_TAC HUA_PCSUM_NORMALIZED THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `root 2 (&N)` THEN
      REWRITE_TAC[WARING_VSM_TRIVIAL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `root 2 ((&P + &1) pow 2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC ROOT_MONO_LE THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_ROOT_POW THEN
        REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC];
      EXPAND_TAC "B" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 * (y + &1) <= x + y + &1`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `5 - 1 = 4`] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
          [ASM_SIMP_TAC[REAL_POS; REAL_POW_LE]; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&(phi q) * D + log(&q) + &2) * (&1 + &2 * pi * &N / &Kw)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ARC_APPROX_SQ THEN EXISTS_TAC `P:num` THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= d ==> a + b + &2 <= c + d + &2`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[PHI_LIMIT];
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

let hua_term = new_definition
 `hua_term N q =
  vsum {a | a < q /\ coprime(a,q)}
       (\a. (Cx(inv(&(phi q))) * hua_pcsum q a) pow 5 *
            expi(--(&N * &a / &q)))`;;

let hua_sing = new_definition
 `hua_sing N Q = vsum(1..Q) (\q. hua_term N q)`;;

let HUA_MAJOR_MAIN = prove
 (`!N M Kw Q.
     1 <= Kw /\ Kw <= M /\ 5 * N < M
     ==> norm(vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
                (\a. vsum (circ_arc M Kw q a)
                  (\j. (Cx(inv(&(phi q))) * hua_pcsum q a *
                        waring_vsm 2 N (&j / &M - &a / &q)) pow 5 *
                       expi(--(&N * &j / &M))))) -
              Cx(&M * waring_conv (waring_klam 2) N 5 N) * hua_sing N Q)
         <= (&4 pow 4 * root 2 (&N) * (&18 * &M * &Kw)) *
            sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                             (\a. norm(Cx(inv(&(phi q))) * hua_pcsum q a)
                                  pow 5))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ta = &4 pow 4 * root 2 (&N) * (&18 * &M * &Kw)` THEN
  ABBREV_TAC `Jm = Cx(&M * waring_conv (waring_klam 2) N 5 N)` THEN
  SUBGOAL_THEN
   `!q a. vsum (circ_arc M Kw q a)
            (\j. (Cx(inv(&(phi q))) * hua_pcsum q a *
                  waring_vsm 2 N (&j / &M - &a / &q)) pow 5 *
                 expi(--(&N * &j / &M))) =
          ((Cx(inv(&(phi q))) * hua_pcsum q a) pow 5 *
           expi(--(&N * &a / &q))) *
          vsum (circ_arc M Kw q a)
            (\j. waring_vsm 2 N (&j / &M - &a / &q) pow 5 *
                 expi(--(&N * (&j / &M - &a / &q))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; CIRC_ARC_FINITE] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `--(&N * &j / &M) =
                  --(&N * &a / &q) + --(&N * (&j / &M - &a / &q))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXPI_ADD; COMPLEX_POW_MUL] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[hua_sing; hua_term] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG; FINITE_COPRIME_RESIDUES] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG; FINITE_COPRIME_RESIDUES] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[COMPLEX_RING
   `(c * e) * v - j * c * e:complex = (c * e) * (v - j)`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_RID; COMPLEX_NORM_POW] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_POW_LE; NORM_POS_LE; REAL_LE_MUL] THEN
  MAP_EVERY EXPAND_TAC ["Ta"; "Jm"] THEN
  MP_TAC(SPECL [`2`; `N:num`; `M:num`; `Kw:num`; `5`; `q:num`; `a:num`]
    WARING_VSM_ARC_MAIN) THEN
  ASM_REWRITE_TAC[ARITH; REAL_POW_1]);;
