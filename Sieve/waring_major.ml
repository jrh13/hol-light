(* ========================================================================= *)
(* Waring's problem II: the major arcs.                                      *)
(* * DIVISOR_BOUND: for every e > 0 there is C with tau(n) <= C n^e          *)
(*   (TAU_LOCAL_BOUND for the prime powers, multiplicativity of tau).        *)
(* * The smooth model: waring_klam k m = m^(1/k) - (m - 1)^(1/k) and         *)
(*   waring_vsm k N x = sum_{m <= N} waring_klam k m e(m x); |waring_vsm k N *)
(*   x| <= N^(1/k) and <= 4 (1/ndist x)^(1/k) (WARING_VSM_TRIVIAL,           *)
(*   WARING_VSM_DECAY), and the singular integral is bounded below           *)
(*   elementarily, JCONV_LOWER: for 2^s <= n <= L, waring_conv (waring_klam  *)
(*   k) L s n >= (1/k) 2^(-s(s+1)) n^(s/k) / n.                              *)
(* * Complete sums waring_csum k q a = sum_{r < q} e(a r^k / q).  On the     *)
(*   major arc circ_arc M Kw q a (vinogradov.ml), waring_kexp k P (j/M)      *)
(*   differs from (waring_csum k q a / q) waring_vsm k N (j/M - a/q) by at   *)
(*   most 2 q (1 + 2 pi N / Kw) (WARING_KEXP_ARC_APPROX, by Abel summation   *)
(*   over the residue classes mod q).  WARING_MAJOR_APPROX bounds the total  *)
(*   error over the major arcs, and WARING_MAJOR_MAIN evaluates the main     *)
(*   term as M waring_conv (waring_klam k) N s N waring_sing k s N Q up to   *)
(*   the contribution of waring_vsm off its arc (WARING_VSM_OFF_ARC), where  *)
(*   waring_sing k s N Q = sum_{q <= Q} waring_term k s N q and              *)
(*     waring_term k s N q = sum_{a < q, (a,q) = 1} (waring_csum k q a /     *)
(*     q)^s e(-N a/q).                                                       *)
(* * WARING_CSUM_DECAY: |waring_csum k q a| <= C q^(1 - 1/2^(k-1) + d) for   *)
(*   (a,q) = 1 and every d > 0 (Weyl's inequality with P = q), hence         *)
(*   WARING_CSUM_ABS_DECAY: for s >= 2^k + 1,                                *)
(*     sum_{a < q, (a,q) = 1} |waring_csum k q a / q|^s <= C q^(-1 - 1/2^k). *)
(* ========================================================================= *)

needs "Sieve/vinogradov.ml";;
needs "Sieve/waring_weyl.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The divisor bound.                                                        *)
(* ------------------------------------------------------------------------- *)

let TAU_PRIMEPOW = prove
 (`!p a. prime p ==> CARD {d | d divides p EXP a} = a + 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{d | d divides p EXP a} = IMAGE (\i. p EXP i) (0..a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0] THEN
    ASM_SIMP_TAC[DIVIDES_PRIMEPOW] THEN MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; EQ_EXP] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC]);;

let TAU_MUL_COPRIME = prove
 (`!m n. 1 <= m /\ 1 <= n /\ coprime(m,n)
         ==> CARD {d | d divides m * n} =
             CARD {d | d divides m} * CARD {d | d divides n}`,
  REPEAT STRIP_TAC THEN
  MP_TAC MULTIPLICATIVE_TAU THEN REWRITE_TAC[multiplicative] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[tau; MULT_EQ_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`]);;

let TAU_LOCAL_BOUND = prove
 (`!e Pe p a.
     &0 < e /\ prime p /\ (Pe < p ==> &2 <= &p rpow e)
     ==> &(a + 1) <=
         (if p <= Pe then &1 + inv(e * log(&2)) else &1) *
         (&p rpow e) pow a`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `&0 < e * log(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 + e * log(&2) <= &p rpow e` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 rpow e` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[rpow; REAL_ARITH `&0 < &2`; REAL_EXP_LE_X];
        MATCH_MP_TAC RPOW_LE2 THEN REPEAT CONJ_TAC THEN
        TRY(ASM_REAL_ARITH_TAC) THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `L = e * log(&2)` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv L) * (&1 + &a * L)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_ADD_LDISTRIB; REAL_MUL_LID] THEN
      SUBGOAL_THEN `inv L * &a * L = &a` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      MP_TAC(SPEC `L:real` REAL_LE_INV) THEN
      MP_TAC(SPECL [`&a`; `L:real`] REAL_LE_MUL) THEN
      REWRITE_TAC[REAL_POS] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + L) pow a` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LBOUND THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow a` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      MP_TAC(SPEC `a:num` LT_POW2_REFL) THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let RPOW_NUM_POW = prove
 (`!x a e. &0 < x ==> (x pow a) rpow e = (x rpow e) pow a`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[real_pow; RPOW_ONE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RPOW_MUL]);;

let DIVISOR_BOUND_INDUCT = prove
 (`!e Pe n.
     &0 < e /\ (!p. prime p /\ Pe < p ==> &2 <= &p rpow e) /\ 1 <= n
     ==> &(CARD {d | d divides n}) <=
         (&1 + inv(e * log(&2))) pow
           (CARD {p | prime p /\ p <= Pe /\ p divides n}) * &n rpow e`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[DIVIDES_ONE; RPOW_ONE; REAL_MUL_RID] THEN
    SUBGOAL_THEN `{d | d = 1} = {1} /\
                  {p | prime p /\ p <= Pe /\ p = 1} = {}`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; NOT_IN_EMPTY] THEN
      MESON_TAC[PRIME_1];
      REWRITE_TAC[CARD_SING; CARD_CLAUSES; real_pow; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `a = index p n` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= m <=> ~(m = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `p EXP a * m = n` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= a` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `coprime(p,m:num)` THEN
    UNDISCH_TAC `p EXP a * m = n` THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `m < n:num` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = 1 * m:num`] THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `p:num` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check
    (fun th -> is_forall(concl th) &&
               fst(dest_var(fst(dest_forall(concl th)))) = "m")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
    (fun th -> concl th = `p EXP a * m = n`)) THEN
  SUBGOAL_THEN
   `CARD {d | d divides p EXP a * m} = (a + 1) * CARD {d | d divides m}`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `CARD {d | d divides p EXP a} * CARD {d | d divides m}` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[TAU_PRIMEPOW]] THEN
    MATCH_MP_TAC TAU_MUL_COPRIME THEN ASM_SIMP_TAC[COPRIME_LEXP] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(p EXP a * m) rpow e = (&p rpow e) pow a * &m rpow e`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; RPOW_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RPOW_NUM_POW THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {q | prime q /\ q <= Pe /\ q divides m}` ASSUME_TAC
  THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..Pe` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p IN {q | prime q /\ q <= Pe /\ q divides m})` ASSUME_TAC
  THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{q | prime q /\ q <= Pe /\ q divides p EXP a * m} =
    if p <= Pe then p INSERT {q | prime q /\ q <= Pe /\ q divides m}
    else {q | prime q /\ q <= Pe /\ q divides m}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `q:num` THEN
    COND_CASES_TAC THEN REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
    ASM_CASES_TAC `prime q` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ; PRIME_DIVEXP_EQ;
                 ARITH_RULE `1 <= a ==> ~(a = 0)`; DIVIDES_PRIME_PRIME] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `Pe:num`; `p:num`; `a:num`] TAU_LOCAL_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C1 = &1 + inv(e * log(&2))` THEN
  ABBREV_TAC `c = CARD {q | prime q /\ q <= Pe /\ q divides m}` THEN
  SUBGOAL_THEN `&1 <= C1` ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `C1 pow CARD (if p <= Pe
                 then p INSERT {q | prime q /\ q <= Pe /\ q divides m}
                 else {q | prime q /\ q <= Pe /\ q divides m}) =
    (if p <= Pe then C1 else &1) * C1 pow c`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES; real_pow; REAL_MUL_LID];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&0 <= &p rpow e /\ &0 <= &m rpow e` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((if p <= Pe then C1 else &1) * (&p rpow e) pow a) *
              (C1 pow c * &m rpow e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]);;

let DIVISOR_BOUND = prove
 (`!e. &0 < e
       ==> ?Cw. &1 <= Cw /\
               !n. 1 <= n ==> &(CARD {d | d divides n}) <= Cw * &n rpow e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&2 rpow inv e` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `Pe:num`) THEN
  ABBREV_TAC `C1 = &1 + inv(e * log(&2))` THEN
  SUBGOAL_THEN `&1 <= C1` ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(C1:real) pow (Pe + 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`e:real`; `Pe:num`; `n:num`] DIVISOR_BOUND_INDUCT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 rpow inv e) rpow e` THEN
    CONJ_TAC THENL
     [SIMP_TAC[RPOW_RPOW; REAL_ARITH `&0 <= &2`] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      MP_TAC(SPECL [`&2`; `1`] RPOW_POW) THEN REWRITE_TAC[REAL_POW_1] THEN
      SIMP_TAC[REAL_LE_REFL];
      MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Pe:real` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(0..Pe)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC];
    MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The smooth model and the singular integral.                               *)
(* ------------------------------------------------------------------------- *)

let POW_DIFF_BOUNDS = prove
 (`!k u w. 1 <= k /\ &0 <= w /\ w <= u
           ==> &k * w pow (k - 1) * (u - w) <= u pow k - w pow k /\
               u pow k - w pow k <= &k * u pow (k - 1) * (u - w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_SUB_POW] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&k * a * (u - w) = (u - w) * (&k * a)`] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..k - 1) (\i. w pow (k - 1))` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_CONST_NUMSEG] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> (k - 1 + 1) - 0 = k`; REAL_LE_REFL];
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(w:real) pow (k - 1) = w pow i * w pow (k - 1 - i)`
        SUBST1_TAC
      THENL
       [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_POW_LE2) THEN TRY(MATCH_MP_TAC REAL_POW_LE) THEN
        ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..k - 1) (\i. u pow (k - 1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(u:real) pow (k - 1) = u pow i * u pow (k - 1 - i)`
        SUBST1_TAC
      THENL
       [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_POW_LE2) THEN TRY(MATCH_MP_TAC REAL_POW_LE) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SUM_CONST_NUMSEG] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> (k - 1 + 1) - 0 = k`;
        REAL_LE_REFL]]]);;

let waring_klam = new_definition
 `waring_klam k m = root k (&m) - root k (&m - &1)`;;

let WARING_KLAM_SUM = prove
 (`!k t. sum(1..t) (waring_klam k) = root k (&t)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ROOT_0; ARITH_RULE `1 <= SUC t`; ARITH]
    THEN
  REWRITE_TAC[waring_klam; GSYM REAL_OF_NUM_SUC;
              REAL_ARITH `(x + &1) - &1 = x`] THEN
  REAL_ARITH_TAC);;

let WARING_KLAM_POS = prove
 (`!k m. &0 <= waring_klam k m`,
  REWRITE_TAC[waring_klam; REAL_SUB_LE] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC ROOT_MONO_LE THEN REAL_ARITH_TAC);;

let WARING_KLAM_BOUNDS = prove
 (`!k m. 1 <= k /\ 1 <= m
         ==> inv(&k * root k (&m) pow (k - 1)) <= waring_klam k m /\
             (2 <= m ==> waring_klam k m <=
              inv(&k * root k (&m - &1) pow (k - 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u = root k (&m)` THEN ABBREV_TAC `w = root k (&m - &1)` THEN
  SUBGOAL_THEN `&0 <= (w:real) /\ w <= u /\ &0 < u /\ u pow k - w pow k = &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "w"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ROOT_POS_LE THEN
      UNDISCH_TAC `1 <= m` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC ROOT_MONO_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC ROOT_POS_LT THEN
      UNDISCH_TAC `1 <= m` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &m /\ &0 <= &m - &1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `1 <= m` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_POW_ROOT] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `u:real`; `w:real`] POW_DIFF_BOUNDS) THEN
  ASM_REWRITE_TAC[waring_klam] THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &k * u pow (k - 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < w` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN MATCH_MP_TAC ROOT_POS_LT THEN
      UNDISCH_TAC `2 <= m` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &k * w pow (k - 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let WARING_KLAM_DECREASING = prove
 (`!k m. 1 <= k /\ 1 <= m ==> waring_klam k (m + 1) <= waring_klam k m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&k * root k (&m) pow (k - 1))` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`k:num`; `m + 1`] WARING_KLAM_BOUNDS) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`]];
    MP_TAC(SPECL [`k:num`; `m:num`] WARING_KLAM_BOUNDS) THEN ASM_SIMP_TAC[]]);;

let WARING_KLAM_LOWER = prove
 (`!k m N. 1 <= k /\ 1 <= m /\ m <= N
           ==> inv(&k * root k (&N) pow (k - 1)) <= waring_klam k m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&k * root k (&m) pow (k - 1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC ROOT_POS_LT THEN
        UNDISCH_TAC `1 <= m` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC ROOT_POS_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC ROOT_MONO_LE THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]]];
    MP_TAC(SPECL [`k:num`; `m:num`] WARING_KLAM_BOUNDS) THEN ASM_SIMP_TAC[]]);;

let waring_vsm = new_definition
 `waring_vsm k N x = vsum(1..N) (\m. Cx(waring_klam k m) * expi(&m * x))`;;

let WARING_VSM_TRIVIAL = prove
 (`!k N x. norm(waring_vsm k N x) <= root k (&N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_vsm] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (waring_klam k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; COMPLEX_NORM_CX; REAL_MUL_RID]
      THEN
    SIMP_TAC[WARING_KLAM_POS; REAL_ARITH `&0 <= x ==> abs x <= x`];
    REWRITE_TAC[WARING_KLAM_SUM; REAL_LE_REFL]]);;

let VSM_TAIL = prove
 (`!k N x m0. 1 <= k /\ 1 <= m0 /\ ~integer x
              ==> norm(vsum(m0+1..N)
                         (\m. Cx(waring_klam k m) * expi(&m * x))) <=
                  &2 * inv(ndist x) * waring_klam k (m0 + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < ndist x` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` NDIST_BOUNDS) THEN
    MP_TAC(SPEC `x:real` NDIST_EQ_0) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * inv(ndist x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `N <= m0:num` THENL
   [ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; ARITH_RULE `N <= m0 ==> N < m0 + 1`] THEN
    REWRITE_TAC[NORM_0; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[WARING_KLAM_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `m0 + 1..N = (1 + m0)..((N - m0) + m0)` SUBST1_TAC THENL
   [BINOP_TAC THEN ASM_ARITH_TAC; REWRITE_TAC[VSUM_OFFSET]] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MP_TAC(ISPECL [`\h. expi(&(h + m0) * x)`; `\h. Cx(waring_klam k (h + m0))`;
                 `N - m0:num`; `&2 * inv(ndist x)`] ABEL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m0:num`; `\m. expi(&m * x)`; `1`; `h:num`] VSUM_OFFSET)
      THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * emin (&((m0 + h) - m0)) x` THEN
    REWRITE_TAC[VSUM_EXPI_INTERVAL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EMIN_LE_INV THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC(MESON[]
   `a + s = c:real ==> x <= m * (a + s) ==> x <= m * c`) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_SUB] THEN
  SUBGOAL_THEN `N - m0 + m0 = N:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC]
    THEN
  SUBGOAL_THEN
   `!h. abs(waring_klam k ((h + 1) + m0) - waring_klam k (h + m0)) =
        waring_klam k (h + m0) - waring_klam k ((h + 1) + m0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `b <= a ==> abs(b - a) = a - b`) THEN
    REWRITE_TAC[ARITH_RULE `(h + 1) + m0 = (h + m0) + 1`] THEN
    MATCH_MP_TAC WARING_KLAM_DECREASING THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(INST [`\h. waring_klam k (h + m0)`,`f:num->real`]
         (SPECL [`1`; `N - m0 - 1`] SUM_DIFFS)) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[WARING_KLAM_POS; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `(N - m0 - 1 + 1) + m0 = N:num` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `1 + m0 = m0 + 1`] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `N = m0 + 1:num` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REAL_ARITH_TAC]]);;

let ROOT_DOUBLE_LE = prove
 (`!k z. 1 <= k /\ &0 <= z ==> root k (&2 * z) <= &2 * root k z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= root k z` ASSUME_TAC THENL
   [MATCH_MP_TAC ROOT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `root k ((&2 * root k z) pow k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ROOT_MONO_LE THEN REWRITE_TAC[REAL_POW_MUL] THEN
    ASM_SIMP_TAC[REAL_POW_ROOT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&2 * z = &2 pow 1 * z`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_ROOT_POW THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let WARING_VSM_DECAY = prove
 (`!k N x. 1 <= k /\ ~integer x
           ==> norm(waring_vsm k N x) <= &4 * root k (inv(ndist x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < ndist x /\ ndist x <= &1 / &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` NDIST_BOUNDS) THEN
    MP_TAC(SPEC `x:real` NDIST_EQ_0) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = ndist x` THEN
  SUBGOAL_THEN `&2 <= inv d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `y = root k (inv d)` THEN
  SUBGOAL_THEN `~(k = 0) /\ &0 < y /\ y pow k = inv d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC ROOT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_ROOT THEN DISJ2_TAC THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPEC `inv(d:real)` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN
  MP_TAC(SPEC `inv(d:real)` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `m0 = n0 + 1` THEN
  SUBGOAL_THEN `inv d < &m0 /\ &m0 <= &2 * inv d /\ 1 <= m0` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "m0" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `root k (&m0) <= &2 * y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `root k (&2 * inv d)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ROOT_MONO_LE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "y" THEN MATCH_MP_TAC ROOT_DOUBLE_LE THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `N <= m0:num` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `root k (&N)` THEN
    REWRITE_TAC[WARING_VSM_TRIVIAL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `root k (&m0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ROOT_MONO_LE THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[waring_vsm] THEN
  SUBGOAL_THEN `1..N = 1..(m0 + (N - m0))` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= m0 + 1`] THEN
  SUBGOAL_THEN `m0 + (N - m0) = N:num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:complex) <= &2 * y /\ norm(b) <= &2 * y ==> norm(a + b) <= &4 * y`)
  THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`k:num`; `m0:num`; `x:real`] WARING_VSM_TRIVIAL) THEN
    REWRITE_TAC[waring_vsm] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `x:real`; `m0:num`] VSM_TAIL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MP_TAC(SPECL [`k:num`; `m0 + 1`] WARING_KLAM_BOUNDS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]
    THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `y <= root k (&m0)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC ROOT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * inv d * inv(y pow (k - 1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
     THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&k * root k (&m0) pow (k - 1))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `root k (&m0) pow (k - 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check
    (fun th -> concl th = `(y:real) pow k = inv d`)) THEN
  SUBGOAL_THEN `(y:real) pow k = y * y pow (k - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `&0 < (y:real) pow (k - 1)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let WARING_KLAM_LOWER_ROOT = prove
 (`!k n. 1 <= k /\ 1 <= n ==> inv(&k) * root k (&n) / &n <= waring_klam k n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `n:num`; `n:num`] WARING_KLAM_LOWER) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
  SUBGOAL_THEN `~(k = 0) /\ &0 < root k (&n) /\ root k (&n) pow k = &n`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC ROOT_POS_LT THEN
      UNDISCH_TAC `1 <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_ROOT THEN DISJ2_TAC THEN
      REWRITE_TAC[REAL_POS] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `r = root k (&n)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check
    (fun th -> concl th = `(r:real) pow k = &n`)) THEN
  SUBGOAL_THEN `(r:real) pow k = r * r pow (k - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (r:real) pow (k - 1) /\ &0 < &k` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN UNDISCH_TAC `1 <= k` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD]);;

let JCONV_LOWER = prove
 (`!k L s n. 1 <= k /\ 1 <= s /\ 2 EXP s <= n /\ n <= L
             ==> inv(&k) * inv(&2) pow (s * (s + 1)) * root k (&n) pow s / &n
                 <= waring_conv (waring_klam k) L s n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0) /\ 1 <= n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP SUC s` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `s = 0` THENL
   [ASM_REWRITE_TAC[ARITH; REAL_POW_1; GSYM(num_CONV `1`); WARING_CONV_1] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&k) * root k (&n) / &n`
      THEN
    ASM_SIMP_TAC[WARING_KLAM_LOWER_ROOT] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV];
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC ROOT_POS_LE THEN REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  REWRITE_TAC[waring_conv] THEN ABBREV_TAC `h = n DIV 2` THEN
  SUBGOAL_THEN `2 * h <= n /\ n <= 2 * h + 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4 <= n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP SUC s` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `4 = 2 EXP 2` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= h /\ h <= L /\ n <= 4 * h` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = root k (&n)` THEN
  SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC ROOT_POS_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `X = inv(&k) * inv(&2) pow (s * (s + 1)) * (r / &2) pow s / &n`
    THEN
  SUBGOAL_THEN
    `!m. 1 <= m /\ m <= h ==> X <= waring_conv (waring_klam k) L s (n - m)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - m:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `h:num` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP SUC s DIV 2` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[EXP] THEN SIMP_TAC[DIV_MULT; ARITH_EQ; LE_REFL];
          EXPAND_TAC "h" THEN MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[]];
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN EXPAND_TAC "X"
      THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `&0 <= inv (&k) * inv (&2) pow (s * (s + 1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN MATCH_MP_TAC REAL_LE_INV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `r <= &2 * y ==> r * inv(&2) <= y`) THEN
    EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `root k (&2 * &(n - m))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ROOT_MONO_LE THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC ROOT_DOUBLE_LE THEN ASM_REWRITE_TAC[REAL_POS]];
    MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `sum(1..h)
       (\m. waring_klam k m * waring_conv (waring_klam k) L s (n - m))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..h) (\m. if m <= n
                               then waring_klam k m *
                               waring_conv (waring_klam k) L s (n - m)
                               else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[WARING_KLAM_POS; WARING_CONV_POS]]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..h) (\m. waring_klam k m * X)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[WARING_KLAM_POS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[SUM_RMUL; ETA_AX; WARING_KLAM_SUM] THEN
  SUBGOAL_THEN `r <= &4 * root k (&h)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `root k (&2 * &2 * &h)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ROOT_MONO_LE THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * root k (&2 * &h)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ROOT_DOUBLE_LE THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `&4 * x = &2 * &2 * x`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
          THEN
        MATCH_MP_TAC ROOT_DOUBLE_LE THEN ASM_REWRITE_TAC[REAL_POS]]];
    ALL_TAC] THEN
  EXPAND_TAC "X" THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(r / &4) * inv(&k) * inv(&2) pow (s * (s + 1)) *
              (r / &2) pow s / &n` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
      TRY(CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_LE_INV) THEN
      ASM_REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN
   `r / &4 * inv (&k) * inv (&2) pow (s * (s + 1)) * (r / &2) pow s / &n =
    (inv(&k) * r pow SUC s / &n) * inv(&2) pow (s * (s + 1) + s + 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_POW_ADD; REAL_POW_MUL; real_pow] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV
   [REAL_ARITH `a * b * c / d = (a * c / d) * b:real`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN TRY(MATCH_MP_TAC REAL_LE_INV) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO_INV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[ADD1] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Complete sums and the major arcs.                                         *)
(* ------------------------------------------------------------------------- *)

let waring_csum = new_definition
 `waring_csum k q a = vsum {r | r < q} (\r. expi(&a * &(r EXP k) / &q))`;;

let WARING_KEXP_SPLIT = prove
 (`!k P q a b.
     1 <= q
     ==> waring_kexp k P (&a / &q + b) =
         vsum {r | r < q}
           (\r. expi(&a * &(r EXP k) / &q) *
                vsum {x | x IN 1..P /\ x MOD q = r}
                     (\x. expi(b * &(x EXP k))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_kexp] THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `vsum(1..P) (\x. expi(&a * &((x MOD q) EXP k) / &q) *
                    expi(b * &(x EXP k)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&a / &q + b) * &(x EXP k) =
                  &a * &(x EXP k) / &q + b * &(x EXP k)`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXPI_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&a * &x / &q = &x * &a / &q`] THEN
  MATCH_MP_TAC EXPI_CONG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_EXP THEN
  MP_TAC(SPECL [`x:num`; `q:num`] CONG_MOD) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[CONG_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. x MOD q`;
                 `\x. expi(&a * &((x MOD q) EXP k) / &q) *
                      expi(b * &(x EXP k))`; `1..P`] VSUM_IMAGE_GEN) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum {r | r < q}
      (\y. vsum {x | x IN 1..P /\ x MOD q = y}
             (\x. expi(&a * &((x MOD q) EXP k) / &q) * expi(b * &(x EXP k))))`
  THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[MOD_LT_EQ] THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN
  UNDISCH_TAC `~(r IN IMAGE (\x. x MOD q) (1..P))` THEN
  REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_ELIM_THM]]);;

let AP_COUNT_ROOT = prove
 (`!k P N q r t.
     1 <= k /\ N < (P + 1) EXP k /\ 1 <= q /\ r < q /\ t <= N
     ==> abs(&(CARD {x | x IN 1..P /\ x MOD q = r /\ x EXP k <= t}) -
             root k (&t) / &q) <= &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0) /\ ~(q = 0)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `root k (&t)` FLOOR_POS) THEN
  ANTS_TAC THENL [MATCH_MP_TAC ROOT_POS_LE THEN REWRITE_TAC[REAL_POS];
                  ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `X0:num`) THEN
  MP_TAC(SPEC `root k (&t)` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x EXP k <= t <=> x <= X0` ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `&x <= root k (&t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `root k (&x pow k)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC REAL_ROOT_POW THEN ASM_REWRITE_TAC[REAL_POS];
          ASM_SIMP_TAC[ROOT_MONO_LE_EQ]];
        DISCH_THEN(MP_TAC o MATCH_MP FLOOR_MONO) THEN
        ASM_REWRITE_TAC[FLOOR_NUM]];
      DISCH_TAC THEN
      SUBGOAL_THEN `&x pow k <= root k (&t) pow k` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_POW_ROOT; REAL_POS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `X0 <= P:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P + 1) EXP k <= t` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN 1..P /\ x MOD q = r /\ x EXP k <= t} =
    {x | x IN 1..X0 /\ (x == r) (mod q) /\ 1 divides x}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG; CONG; DIVIDES_1] THEN
    ASM_SIMP_TAC[MOD_LT] THEN X_GEN_TAC `x:num` THEN
    ASM_CASES_TAC `x MOD q = r` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`X0:num`; `q:num`; `r:num`; `1`] AP_MULTIPLES_COUNT) THEN
  ASM_REWRITE_TAC[LE_REFL; COPRIME_1; REAL_MUL_RID] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!b. abs(a - b) <= &1 /\ abs(b - c) <= &1 ==> abs(a - c) <= &2`) THEN
  EXISTS_TAC `&X0 / &q` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL;
              REAL_ABS_INV; REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `&1 <= &q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= q ==> &0 < q`] THEN
  ASM_REAL_ARITH_TAC);;

let KPOW_SET_VSUM = prove
 (`!k P N S b.
     1 <= k /\ P EXP k <= N /\ S SUBSET 1..P
     ==> vsum S (\x. expi(b * &(x EXP k))) =
         vsum(1..N) (\m. Cx(if ?x. x IN S /\ m = x EXP k then &1 else &0) *
                         expi(&m * b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum(1..N) (\m. Cx(if ?x. x IN S /\ m = x EXP k then &1 else &0) *
                    expi(&m * b)) =
    vsum {m | m IN 1..N /\ ?x. x IN S /\ m = x EXP k} (\m. expi(&m * b))`
  SUBST1_TAC THENL
   [REWRITE_TAC[VSUM_RESTRICT_SET] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{m | m IN 1..N /\ ?x. x IN S /\ m = x EXP k} = IMAGE (\x. x EXP k) S`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `m:num` THEN EQ_TAC THENL
     [MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      SUBGOAL_THEN `y IN 1..P` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `P EXP k` THEN
        ASM_REWRITE_TAC[EXP_MONO_LE]]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`u:num`; `v:num`] THEN STRIP_TAC THEN
    ASM_MESON_TAC[EXP_MONO_EQ; ARITH_RULE `1 <= k ==> ~(k = 0)`];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[o_THM; REAL_MUL_SYM]);;

let KPOW_SET_PARTIAL = prove
 (`!k S h.
     1 <= k /\ FINITE S /\ (!x. x IN S ==> 1 <= x)
     ==> sum(1..h) (\m. if ?x. x IN S /\ m = x EXP k then &1 else &0) =
         &(CARD {x | x IN S /\ x EXP k <= h})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG; REAL_MUL_RID] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `{m | m IN 1..h /\ ?x. x IN S /\ m = x EXP k} =
    IMAGE (\x. x EXP k) {x | x IN S /\ x EXP k <= h}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN EQ_TAC THENL
     [MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      SUBGOAL_THEN `1 <= y` MP_TAC THENL [ASM_MESON_TAC[]; ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[EXP_MONO_EQ; ARITH_RULE `1 <= k ==> ~(k = 0)`]);;

let FIBRE_APPROX = prove
 (`!k P N q r b.
     1 <= k /\ P EXP k <= N /\ N < (P + 1) EXP k /\ 1 <= q /\ r < q
     ==> norm(vsum {x | x IN 1..P /\ x MOD q = r}
                   (\x. expi(b * &(x EXP k))) -
              Cx(inv(&q)) * waring_vsm k N b)
         <= &2 * (&1 + &2 * pi * &N * abs b)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {x | x IN 1..P /\ x MOD q = r}` THEN
  SUBGOAL_THEN `S SUBSET 1..P /\ FINITE S /\ (!x. x IN S ==> 1 <= x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `P:num`; `N:num`; `S:num->bool`; `b:real`]
    KPOW_SET_VSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[waring_vsm] THEN
  ABBREV_TAC `c = \m. if ?x. x IN S /\ m = x EXP k then &1 else &0` THEN
  SUBGOAL_THEN
   `!m. (if ?x. x IN S /\ m = x EXP k then &1 else &0) = (c:num->real) m`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..N) (\m. Cx(c m) * expi(&m * b)) -
    Cx(inv(&q)) * vsum(1..N) (\m. Cx(waring_klam k m) * expi(&m * b)) =
    vsum(1..N) (\m. Cx(c m - waring_klam k m / &q) * expi(&m * b))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[CX_SUB; CX_DIV; real_div; CX_MUL; CX_INV] THEN
    REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\m. Cx(c m - waring_klam k m / &q)`;
    `\m. expi(&m * b)`; `N:num`; `&2`] ABEL_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    REWRITE_TAC[VSUM_CX; COMPLEX_NORM_CX] THEN
    SIMP_TAC[SUM_SUB_NUMSEG; real_div; SUM_RMUL] THEN
    REWRITE_TAC[ETA_AX; WARING_KLAM_SUM] THEN EXPAND_TAC "c" THEN
    ASM_SIMP_TAC[KPOW_SET_PARTIAL] THEN REWRITE_TAC[GSYM real_div] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC AP_COUNT_ROOT THEN EXISTS_TAC `N:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; NORM_EXPI] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N-1) (\h. &2 * pi * abs b)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; REAL_MUL_LID;
                EXPI_ADD] THEN
    REWRITE_TAC[COMPLEX_RING `a * b - a:complex = a * (b - Cx(&1))`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_LID] THEN
    REWRITE_TAC[NORM_EXPI_SUB_1_UPPER];
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&N * (&2 * pi * abs b)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

let WARING_KEXP_MAJOR_APPROX = prove
 (`!k P N q a b.
     1 <= k /\ P EXP k <= N /\ N < (P + 1) EXP k /\ 1 <= q
     ==> norm(waring_kexp k P (&a / &q + b) - Cx(inv(&q)) * waring_csum k q a *
              waring_vsm k N b)
         <= &2 * &q * (&1 + &2 * pi * &N * abs b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WARING_KEXP_SPLIT; waring_csum] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; GSYM VSUM_COMPLEX_LMUL;
           FINITE_NUMSEG_LT] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {r | r < q:num} (\r. &2 * (&1 + &2 * pi * &N * abs b))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_RING
     `e * f - i * (e * v):complex = e * (f - i * v)`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_LID] THEN
    MATCH_MP_TAC FIBRE_APPROX THEN ASM_REWRITE_TAC[];
    SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    REAL_ARITH_TAC]);;

let WARING_KEXP_INTEGER_ADD = prove
 (`!k P x n. integer n ==> waring_kexp k P (x + n) = waring_kexp k P x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_kexp] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC EXPI_INTEGER_ADD THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let WARING_VSM_INTEGER_ADD = prove
 (`!k N x n. integer n ==> waring_vsm k N (x + n) = waring_vsm k N x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_vsm] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC EXPI_INTEGER_ADD THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let WARING_KEXP_TRIVIAL = prove
 (`!k P x. norm(waring_kexp k P x) <= &P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_kexp] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..P) (\n. &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_NUMSEG; NORM_EXPI; REAL_LE_REFL];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_LE_REFL]]);;

let WARING_CSUM_TRIVIAL = prove
 (`!k q a. norm(waring_csum k q a) <= &q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_csum] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {r | r < q:num} (\r. &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; NORM_EXPI; REAL_LE_REFL];
    SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; REAL_MUL_RID;
             REAL_LE_REFL]]);;

let COMPLEX_POW_DIFF_LE = prove
 (`!s z w B. norm z <= B /\ norm w <= B
             ==> norm(z pow s - w pow s) <= &s * B pow (s - 1) * norm(z - w)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[complex_pow; COMPLEX_SUB_REFL; COMPLEX_NORM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[complex_pow; SUC_SUB1] THEN
  SUBGOAL_THEN
   `(z:complex) * z pow s - w * w pow s =
    z * (z pow s - w pow s) + (z - w) * w pow s`
  SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * (&s * B pow (s - 1) * norm(z - w:complex)) +
              norm(z - w) * B pow s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(a:complex) <= x /\ norm(b:complex) <= y ==> norm(a + b) <= x + y`)
    THEN REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s = 0` THEN
  ASM_REWRITE_TAC[ARITH; real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(B:real) pow s = B * B pow (s - 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `s = SUC(s - 1)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[real_pow]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let WARING_KEXP_ARC_APPROX = prove
 (`!k P N M Kw q a j.
     1 <= k /\ P EXP k <= N /\ N < (P + 1) EXP k /\ 1 <= q /\ 1 <= Kw /\
     j IN circ_arc M Kw q a
     ==> norm(waring_kexp k P (&j / &M) -
              Cx(inv(&q)) * waring_csum k q a *
              waring_vsm k N (&j / &M - &a / &q))
         <= &2 * &q * (&1 + &2 * pi * &N / &Kw)`,
  REWRITE_TAC[circ_arc; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&j / &M - &a / &q` NDIST_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `b = &j / &M - &a / &q - n` THEN
  SUBGOAL_THEN `abs b <= inv(&Kw)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `waring_vsm k N (&j / &M - &a / &q) = waring_vsm k N b`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&j / &M - &a / &q = b + n` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[WARING_VSM_INTEGER_ADD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `waring_kexp k P (&j / &M) = waring_kexp k P (&a / &q + b)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&j / &M = (&a / &q + b) + n` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[WARING_KEXP_INTEGER_ADD]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * &q * (&1 + &2 * pi * &N * abs b)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WARING_KEXP_MAJOR_APPROX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
          [REWRITE_TAC[REAL_POS]; ALL_TAC]) THEN
  REWRITE_TAC[REAL_LE_LADD; real_div] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
          [SIMP_TAC[REAL_POS; PI_POS_LE]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[]);;

let CARD_NEAR_REAL = prove
 (`!M c w. &0 <= w
           ==> &(CARD {j | j < M /\ abs(&j - c) <= w}) <= &2 * w + &1`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `{j | j < M /\ abs(&j - c) <= w} = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]) THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `&2 * w` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(SPEC `&2 * w` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(CARD(j0..j0+n))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[NOT_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&j < &j0 + &n + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG; ARITH_RULE `((j0 + n) + 1) - j0 = n + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC]);;

let CARD_ARC = prove
 (`!M Kw q a. 2 <= Kw /\ 1 <= q /\ a < q
              ==> &(CARD(circ_arc M Kw q a)) <= &3 * (&2 * &M / &Kw + &1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `S = \t. {j | j < M /\ abs(&j - &M * (&a / &q + t)) <= &M / &Kw}` THEN
  SUBGOAL_THEN
   `!t. FINITE((S:real->num->bool) t) /\
        &(CARD(S t)) <= &2 * &M / &Kw + &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "S" THEN BETA_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < M:num}` THEN
      SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
      MATCH_MP_TAC CARD_NEAR_REAL THEN
      SIMP_TAC[REAL_LE_DIV; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `circ_arc M Kw q a SUBSET (S(-- &1) UNION S(&0) UNION S(&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[circ_arc; SUBSET; IN_ELIM_THM; IN_UNION] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `&j / &M - &a / &q` NDIST_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < &M /\ &0 < &q /\ &2 <= &Kw` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!t. abs(&j - &M * (&a / &q + t)) <= &M / &Kw <=>
          abs(&j / &M - &a / &q - t) <= inv(&Kw)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `&j - &M * (&a / &q + t) = &M * (&j / &M - &a / &q - t)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &M` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`] THEN
      ASM_SIMP_TAC[real_div; REAL_LE_LMUL_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &j / &M /\ &j / &M < &1 /\
                  &0 <= &a / &q /\ &a / &q < &1 /\ inv(&Kw) <= inv(&2)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_LDIV_EQ; REAL_MUL_LID;
                   REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `n = -- &1 \/ n = &0 \/ n = &1` MP_TAC THENL
     [MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN
      MP_TAC(SPEC `n - &1` REAL_ABS_INTEGER_LEMMA) THEN
      MP_TAC(SPEC `n + &1` REAL_ABS_INTEGER_LEMMA) THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD((S:real->num->bool)(-- &1))) + &(CARD(S(&0))) +
              &(CARD(S(&1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD((S:real->num->bool)(-- &1) UNION S(&0) UNION S(&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[FINITE_UNION]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD((S:real->num->bool)(-- &1)) + CARD(S(&0) UNION S(&1))` THEN
    ASM_SIMP_TAC[CARD_UNION_LE; FINITE_UNION; LE_ADD_LCANCEL];
    FIRST_ASSUM(MP_TAC o SPEC `-- &1`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `&0`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `&1`) THEN
    REAL_ARITH_TAC]);;

let WARING_MAJOR_APPROX = prove
 (`!k P N M Kw Q s.
     1 <= k /\ P EXP k <= N /\ N < (P + 1) EXP k /\ 2 <= Kw /\
     2 * Q EXP 2 < Kw
     ==> norm(vsum (circ_major M Kw Q)
                (\j. waring_kexp k P (&j / &M) pow s *
                     expi(--(&N * &j / &M))) -
              vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
                (\a. vsum (circ_arc M Kw q a)
                  (\j. (Cx(inv(&q)) * waring_csum k q a *
                        waring_vsm k N (&j / &M - &a / &q)) pow s *
                       expi(--(&N * &j / &M))))))
         <= &Q * &Q * (&3 * (&2 * &M / &Kw + &1)) *
            (&s * (&P + &1) pow (s - 1) *
             (&2 * &Q * (&1 + &2 * pi * &N / &Kw)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CIRC_MAJOR_VSUM] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) TRIPLE_NORM_LE o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_COPRIME_RESIDUES; CIRC_ARC_FINITE] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  ABBREV_TAC `X = &s * (&P + &1) pow (s - 1) *
                  (&2 * &Q * (&1 + &2 * pi * &N / &Kw))` THEN
  ABBREV_TAC `Y = &3 * (&2 * &M / &Kw + &1)` THEN
  SUBGOAL_THEN `&0 <= &1 + &2 * pi * &N / &Kw` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POS; PI_POS_LE; REAL_LE_DIV];
    ALL_TAC] THEN
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
   `&s * (&P + &1) pow (s - 1) *
    norm(waring_kexp k P (&j / &M) -
         Cx(inv(&q)) * waring_csum k q a *
         waring_vsm k N (&j / &M - &a / &q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPLEX_POW_DIFF_LE THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`k:num`; `P:num`; `&j / &M`] WARING_KEXP_TRIVIAL) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV;
                REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&q) * &q * root k (&N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[NORM_POS_LE; WARING_CSUM_TRIVIAL; WARING_VSM_TRIVIAL];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&q) * &q = &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID] THEN
    SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `root k ((&P + &1) pow k)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ROOT_MONO_LE THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_ROOT_POW THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
          [SIMP_TAC[REAL_POS; REAL_POW_LE;
                    REAL_ARITH `&0 <= &P + &1`]; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * &q * (&1 + &2 * pi * &N / &Kw)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC WARING_KEXP_ARC_APPROX THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let OFF_ARC_HALF = prove
 (`!M Kw (J:num->bool) f.
     1 <= Kw /\ Kw <= M /\ FINITE J /\
     (!j. j IN J ==> inv(&Kw) < f j /\ f j <= &1) /\
     (!j j'. j IN J /\ j' IN J /\ ~(j = j') ==> inv(&M) <= abs(f j - f j'))
     ==> sum J (\j. inv(f j pow 2)) <= &9 * &M * &Kw`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &Kw /\ &Kw <= &M` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Kw /\ &0 < &M /\ &0 < inv(&M) /\ inv(&M) <= inv(&Kw)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_INV) THEN
    TRY(MATCH_MP_TAC REAL_LE_INV2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `g = \y. min (&Kw pow 2) (inv(y pow 2))` THEN
  MP_TAC(ISPECL [`J:num->bool`; `f:num->real`; `g:real->real`;
                 `inv(&M)`; `M:num`] SUM_DECREASING_SEPARATED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS];
      EXPAND_TAC "g" THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> min a b <= min a c`) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      EXPAND_TAC "g" THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= min a b`) THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2; REAL_POW_LE; REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a = b /\ c <= d ==> b <= c ==> a <= d`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `b < a ==> b = min a b`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&Kw pow 2 = inv(inv(&Kw) pow 2)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_INV; REAL_INV_INV]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[REAL_LT_INV];
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_INV]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`Kw:num`; `inv(&M)`; `M:num`] SUM_MIN_INV_SQUARE) THEN
  ASM_REWRITE_TAC[real_div; REAL_INV_INV] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ c = d ==> b <= c ==> a <= d`) THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  EXPAND_TAC "g" THEN BETA_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> min a b <= min a c`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x <= &8 * x`) THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2]);;

let GRID_FRAC_SEP = prove
 (`!M c j j'. j < M /\ j' < M /\ ~(j = j')
             ==> inv(&M) <= abs(frac(&j / &M - c) - frac(&j' / &M - c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `n = floor(&j / &M - c) - floor(&j' / &M - c)` THEN
  SUBGOAL_THEN `integer n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN SIMP_TAC[INTEGER_CLOSED; FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frac(&j / &M - c) - frac(&j' / &M - c) = (&j - &j' - n * &M) / &M`
  SUBST1_TAC THENL
   [REWRITE_TAC[FRAC_FLOOR] THEN EXPAND_TAC "n" THEN
    UNDISCH_TAC `&0 < &M` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = &0` THENL
   [UNDISCH_TAC `&j - &j' - n * &M = &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_SUB_0;
                    REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&M <= abs(n * &M)` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `&j - &j' - n * &M = &0` THEN
  UNDISCH_TAC `j < M:num` THEN UNDISCH_TAC `j' < M:num` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  MP_TAC(SPEC `j:num` REAL_POS) THEN MP_TAC(SPEC `j':num` REAL_POS) THEN
  REAL_ARITH_TAC);;

let OFF_ARC_INV_SQUARE = prove
 (`!M Kw c. 1 <= Kw /\ Kw <= M
            ==> sum {j | j < M /\ inv(&Kw) < ndist(&j / &M - c)}
                    (\j. inv(ndist(&j / &M - c) pow 2))
                <= &18 * &M * &Kw`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `J = {j | j < M /\ inv(&Kw) < ndist(&j / &M - c)}` THEN
  SUBGOAL_THEN `FINITE(J:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{j | j < M:num}` THEN
    SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum J (\j. inv(ndist(&j / &M - c) pow 2)) =
    sum J (\j. if frac(&j / &M - c) <= &1 / &2
               then inv(frac(&j / &M - c) pow 2)
               else inv((&1 - frac(&j / &M - c)) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[ndist] THEN COND_CASES_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CASES] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= &9 * m * k /\ b <= &9 * m * k
                           ==> a + b <= &18 * m * k`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`M:num`; `Kw:num`;
     `{j | j IN J /\ frac(&j / &M - c) <= &1 / &2}`;
     `\j. frac(&j / &M - c)`] OFF_ARC_HALF);
    MP_TAC(ISPECL [`M:num`; `Kw:num`;
     `{j | j IN J /\ ~(frac(&j / &M - c) <= &1 / &2)}`;
     `\j. &1 - frac(&j / &M - c)`] OFF_ARC_HALF)] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM; ndist] THEN
  (CONJ_TAC THENL
    [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
     MP_TAC(SPEC `&j / &M - c` FLOOR_FRAC) THEN ASM_REAL_ARITH_TAC;
     MAP_EVERY X_GEN_TAC [`j:num`; `j':num`] THEN STRIP_TAC THEN
     MP_TAC(SPECL [`M:num`; `c:real`; `j:num`; `j':num`] GRID_FRAC_SEP) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]));;

let WARING_VSM_OFF_ARC = prove
 (`!k N M Kw s c.
     1 <= k /\ 2 * k <= s /\ 1 <= Kw /\ Kw <= M
     ==> sum {j | j < M /\ inv(&Kw) < ndist(&j / &M - c)}
             (\j. norm(waring_vsm k N (&j / &M - c)) pow s)
         <= &4 pow (2 * k) * root k (&N) pow (s - 2 * k) *
            (&18 * &M * &Kw)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `Kw:num`; `c:real`] OFF_ARC_INV_SQUARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {j | j < M /\ inv(&Kw) < ndist(&j / &M - c)}
        (\j. &4 pow (2 * k) * root k (&N) pow (s - 2 * k) *
             inv(ndist(&j / &M - c) pow 2))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_LMUL] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; ROOT_POS_LE; REAL_POS]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < M:num}` THEN
    SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `y = &j / &M - c` THEN
  SUBGOAL_THEN `&0 < ndist y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&Kw)` THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~integer y` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NDIST_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(waring_vsm k N y) pow s =
    norm(waring_vsm k N y) pow (2 * k) *
    norm(waring_vsm k N y) pow (s - 2 * k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 pow (2 * k) * root k (&N) pow (s - 2 * k) * inv(ndist y pow 2) =
    (&4 pow (2 * k) * inv(ndist y pow 2)) * root k (&N) pow (s - 2 * k)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[NORM_POS_LE; WARING_VSM_TRIVIAL]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4 * root k (inv(ndist y))) pow (2 * k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC WARING_VSM_DECAY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
  SUBGOAL_THEN `root k (inv(ndist y)) pow k = inv(ndist y)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_POW_ROOT THEN DISJ2_TAC THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_ARITH_TAC;
    REWRITE_TAC[REAL_POW_INV]]);;

let WARING_VSM_ARC_MAIN = prove
 (`!k N M Kw s q a.
     1 <= k /\ 2 * k <= s /\ 1 <= Kw /\ Kw <= M /\ s * N < M
     ==> norm(vsum (circ_arc M Kw q a)
                (\j. waring_vsm k N (&j / &M - &a / &q) pow s *
                     expi(--(&N * (&j / &M - &a / &q)))) -
              Cx(&M * waring_conv (waring_klam k) N s N))
         <= &4 pow (2 * k) * root k (&N) pow (s - 2 * k) *
            (&18 * &M * &Kw)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `N < M:num` ASSUME_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `s * N:num` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `N = 1 * N`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`waring_klam k`; `N:num`; `s:num`; `M:num`; `N:num`;
                 `--(&a / &q)`] WARING_CONV_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM real_sub; GSYM waring_vsm] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `circ_arc M Kw q a SUBSET {j | j < M}` ASSUME_TAC THENL
   [REWRITE_TAC[circ_arc; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN
  ASM_SIMP_TAC[GSYM VSUM_DIFF; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN
   `{j | j < M} DIFF circ_arc M Kw q a =
    {j | j < M /\ inv(&Kw) < ndist(&j / &M - &a / &q)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[circ_arc; EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN ASM_CASES_TAC `j < M:num` THEN
    ASM_REWRITE_TAC[REAL_NOT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {j | j < M /\ inv(&Kw) < ndist(&j / &M - &a / &q)}
                  (\j. norm(waring_vsm k N (&j / &M - &a / &q)) pow s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < M:num}` THEN
      SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
      REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; COMPLEX_NORM_POW;
                  REAL_MUL_RID; REAL_LE_REFL]];
    MATCH_MP_TAC WARING_VSM_OFF_ARC THEN ASM_REWRITE_TAC[]]);;

let waring_term = new_definition
 `waring_term k s N q =
  vsum {a | a < q /\ coprime(a,q)}
       (\a. (Cx(inv(&q)) * waring_csum k q a) pow s *
            expi(--(&N * &a / &q)))`;;

let waring_sing = new_definition
 `waring_sing k s N Q = vsum(1..Q) (\q. waring_term k s N q)`;;

let WARING_MAJOR_MAIN = prove
 (`!k N M Kw Q s.
     1 <= k /\ 2 * k <= s /\ 1 <= Kw /\ Kw <= M /\ s * N < M
     ==> norm(vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
                (\a. vsum (circ_arc M Kw q a)
                  (\j. (Cx(inv(&q)) * waring_csum k q a *
                        waring_vsm k N (&j / &M - &a / &q)) pow s *
                       expi(--(&N * &j / &M))))) -
              Cx(&M * waring_conv (waring_klam k) N s N) * waring_sing k s N Q)
         <= (&4 pow (2 * k) * root k (&N) pow (s - 2 * k) *
             (&18 * &M * &Kw)) *
            sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                             (\a. norm(Cx(inv(&q)) *
                                       waring_csum k q a) pow s))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ta = &4 pow (2 * k) * root k (&N) pow (s - 2 * k) *
                   (&18 * &M * &Kw)` THEN
  ABBREV_TAC `Jm = Cx(&M * waring_conv (waring_klam k) N s N)` THEN
  SUBGOAL_THEN
   `!q a. vsum (circ_arc M Kw q a)
            (\j. (Cx(inv(&q)) * waring_csum k q a *
                  waring_vsm k N (&j / &M - &a / &q)) pow s *
                 expi(--(&N * &j / &M))) =
          ((Cx(inv(&q)) * waring_csum k q a) pow s * expi(--(&N * &a / &q))) *
          vsum (circ_arc M Kw q a)
            (\j. waring_vsm k N (&j / &M - &a / &q) pow s *
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
  REWRITE_TAC[waring_sing; waring_term] THEN
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
  MAP_EVERY EXPAND_TAC ["Ta"; "Jm"] THEN MATCH_MP_TAC WARING_VSM_ARC_MAIN THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Decay of the complete sums.                                               *)
(* ------------------------------------------------------------------------- *)

let WARING_CSUM_KEXP = prove
 (`!k q a. 1 <= k /\ 1 <= q ==> waring_csum k q a = waring_kexp k q (&a / &q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_csum; waring_kexp] THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{r | r < q} = IMAGE (\n. n MOD q) (1..q)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `r = 0` THENL
       [EXISTS_TAC `q:num` THEN ASM_SIMP_TAC[MOD_REFL; LE_REFL];
        EXISTS_TAC `r:num` THEN ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC];
      STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT_EQ]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    UNDISCH_TAC `m MOD q = n MOD q` THEN
    SUBGOAL_THEN `(m < q \/ m = q) /\ (n < q \/ n = q:num)`
    MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT; MOD_REFL] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `&a / &q * &(n EXP k) = &a * &(n EXP k) / &q` SUBST1_TAC
  THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&a * &x / &q = &x * &a / &q`] THEN
  MATCH_MP_TAC EXPI_CONG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_EXP THEN
  MP_TAC(SPECL [`n:num`; `q:num`] CONG_MOD) THEN ASM_REWRITE_TAC[]);;

let WARING_CSUM_WEYL = prove
 (`!k q a B.
     2 <= k /\ 1 <= q /\ coprime(a,q) /\ &1 <= B /\
     (!m. 1 <= m /\ m <= q EXP (k - 1) ==> &(CARD {d | d divides m}) <= B)
     ==> norm(waring_csum k q a) pow (2 EXP (k - 1)) <=
         &2 pow (2 EXP (k - 1)) * (&k + &11 * (&(FACT k) + &1)) *
         B pow (k - 1) * &q pow (2 EXP (k - 1) - 1) * (&1 + log(&q))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WARING_CSUM_KEXP; ARITH_RULE `2 <= k ==> 1 <= k`] THEN
  MP_TAC(SPECL [`k:num`; `q:num`; `&a / &q`; `a:num`; `q:num`; `B:real`]
    WEYL_EXPLICIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LE_INV_EQ;
                    REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  ABBREV_TAC `Kq = 2 EXP (k - 1)` THEN
  SUBGOAL_THEN `k <= Kq:num` ASSUME_TAC THENL
   [EXPAND_TAC "Kq" THEN MP_TAC(SPEC `k - 1` LT_POW2_REFL) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow (Kq - 1) = &q pow (Kq - k) * &q pow (k - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = &1 + log(&q)` THEN
  ABBREV_TAC `X = &(k - 1) * &q pow (k - 1) +
                  B pow (k - 1) * (&(FACT k * q EXP (k - 1)) / &q + &1) *
                  (&7 * &q + &4 * &q * L)` THEN
  SUBGOAL_THEN `&2 pow Kq = &2 pow (Kq - k) * &2 pow k` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 pow (Kq - k) * &2 pow k * &q pow (Kq - k)) *
              ((&k + &11 * (&(FACT k) + &1)) * B pow (k - 1) *
               &q pow (k - 1) * L)` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]
    THEN
  SUBGOAL_THEN `(&2 pow (Kq - k) * &q pow (Kq - k)) * &2 pow k * X =
                (&2 pow (Kq - k) * &2 pow k * &q pow (Kq - k)) * X`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN EXPAND_TAC "X" THEN
  SUBGOAL_THEN `&1 <= &q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`)
     THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = &q pow (k - 1)` THEN
  ABBREV_TAC `Bk = (B:real) pow (k - 1)` THEN
  ABBREV_TAC `F0 = &(FACT k)` THEN
  SUBGOAL_THEN `&1 <= Bk /\ &q <= u /\ &1 <= F0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Bk"; "u"; "F0"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                  FACT_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(FACT k * q EXP (k - 1)) / &q = (F0 * u) / &q`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["F0"; "u"] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN `((F0 * u) / &q + &1) * (&7 * &q + &4 * &q * L) =
                (F0 * u + &q) * (&7 + &4 * L)` SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= &q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&(k - 1) = &k - &1` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u /\ &2 <= &k` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u <= Bk * u * L:real` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `b * u * l = (b * l) * u:real`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= F0 * u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(F0 * u + &q) * (&7 + &4 * L) <= ((F0 + &1) * u) * (&11 * L)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Bk * (F0 * u + &q) * (&7 + &4 * L) <=
                Bk * ((F0 + &1) * u) * (&11 * L)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&k - &1) * u <= (&k - &1) * (Bk * u * L)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Bk * u * L` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RPOW_POW_MUL = prove
 (`!x t n. &0 < x ==> (x rpow t) pow n = x rpow (&n * t)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM RPOW_NUM_POW; GSYM RPOW_POW; RPOW_RPOW;
               REAL_LT_IMP_LE]);;

let WARING_CSUM_DECAY = prove
 (`!k d. 2 <= k /\ &0 < d
         ==> ?Cw. &0 <= Cw /\
                 !q a. 1 <= q /\ coprime(a,q)
                       ==> norm(waring_csum k q a) <=
                           Cw * &q rpow (&1 - inv(&(2 EXP (k - 1))) + d)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Kq = 2 EXP (k - 1)` THEN
  SUBGOAL_THEN `1 <= Kq` ASSUME_TAC THENL
   [EXPAND_TAC "Kq" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`;
                                     EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `e = d * &Kq / (&k * &k)` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `e:real` DIVISOR_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `A = &2 pow Kq * (&k + &11 * (&(FACT k) + &1)) *
                  C0 pow (k - 1) * (&1 / e * exp e)` THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_ADD; REAL_LE_MUL;
                 REAL_LE_DIV; REAL_LT_IMP_LE; REAL_EXP_POS_LE;
                 REAL_ARITH `&1 <= Cw ==> &0 <= Cw`];
    ALL_TAC] THEN
  EXISTS_TAC `A rpow inv(&Kq)` THEN ASM_SIMP_TAC[RPOW_POS_LE] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `a:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &q /\ &0 < &q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = C0 * &q rpow (&(k - 1) * e)` THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC RPOW_LE_1 THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS;
                                             REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. 1 <= m /\ m <= q EXP (k - 1) ==> &(CARD {d | d divides m}) <= B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C0 * &m rpow e` THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "B" THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(q EXP (k - 1)) rpow e` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE; REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM RPOW_POW] THEN
      ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `q:num`; `a:num`; `B:real`] WARING_CSUM_WEYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&2 pow Kq * (&k + &11 * (&(FACT k) + &1)) * B pow (k - 1) *
    &q pow (Kq - 1) * (&1 + log(&q)) <=
    A * &q rpow (&Kq - &1 + d * &Kq)`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    ASM_SIMP_TAC[REAL_POW_MUL; RPOW_POW_MUL] THEN
    SUBGOAL_THEN `&q pow (Kq - 1) = &q rpow &(Kq - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[RPOW_POW]; ALL_TAC] THEN
    MP_TAC(SPECL [`q:num`; `1`; `e:real`] LOG_POW_RPOW_BOUND) THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&2 pow Kq * (&k + &11 * (&(FACT k) + &1)) *
      (C0 pow (k - 1) * &q rpow (&(k - 1) * &(k - 1) * e)) *
      &q rpow &(Kq - 1) * (&1 / e * exp e * &q rpow e)` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_ADD; REAL_LE_MUL;
                     RPOW_POS_LE; REAL_LT_IMP_LE;
                     REAL_ARITH `&1 <= Cw ==> &0 <= Cw`];
        ALL_TAC]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `A * &q rpow (&(k - 1) * &(k - 1) * e + &(Kq - 1) + e)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "A" THEN
      SIMP_TAC[RPOW_ADD; ASSUME `&0 < &q`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(k - 1) = &k - &1 /\ &(Kq - 1) = &Kq - &1`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `e * (&k * &k) = d * &Kq` ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN
      SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&k - &1) * e` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_LE; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `e * (&k * &k) = d * &Kq` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Kq = 0) /\ &0 < &Kq` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(waring_csum k q a) = (norm(waring_csum k q a) pow Kq) rpow inv(&Kq)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_ROOT_RPOW; REAL_POW_LE; NORM_POS_LE] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_ROOT_POW THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(A * &q rpow (&Kq - &1 + d * &Kq)) rpow inv(&Kq)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE; REAL_LE_INV_EQ; REAL_POS] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_MUL; RPOW_RPOW; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < &Kq` THEN CONV_TAC REAL_FIELD);;

let WARING_CSUM_ABS_DECAY = prove
 (`!k s. 2 <= k /\ 2 EXP k + 1 <= s
         ==> ?Cw. &0 <= Cw /\
                 !q. 1 <= q
                     ==> sum {a | a < q /\ coprime(a,q)}
                             (\a. norm(Cx(inv(&q)) * waring_csum k q a) pow s)
                         <= Cw * &q rpow (--(&1 + inv(&(2 EXP k))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s0 = 2 EXP k + 1` THEN
  ABBREV_TAC `Kq = 2 EXP (k - 1)` THEN
  SUBGOAL_THEN `2 EXP k = 2 * Kq /\ 1 <= Kq` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kq" THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Kq` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `inv(&(2 EXP k) * &s0)`] WARING_CSUM_DECAY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cw:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(Cw:real) pow s0` THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &q /\ &0 < &q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&s0 = &2 * &Kq + &1` ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN
    REWRITE_TAC[ASSUME `2 EXP k = 2 * Kq`; REAL_OF_NUM_ADD; REAL_OF_NUM_MUL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {a | a < q /\ coprime(a,q)}
                  (\a. Cw pow s0 * &q rpow (--(&2 + inv(&(2 * Kq)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_COPRIME_RESIDUES; IN_ELIM_THM] THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV;
                REAL_ABS_NUM] THEN
    ABBREV_TAC `x = inv(&q) * norm(waring_csum k q a)` THEN
    SUBGOAL_THEN `&0 <= x /\ x <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN
      SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_POS; NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&q) * &q` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS; WARING_CSUM_TRIVIAL];
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(x:real) pow s0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `x <= Cw * &q rpow (--inv(&Kq) + inv(&(2 * Kq) * &s0))`
    ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `inv(&q) * Cw * &q rpow (&1 - inv(&Kq) + inv(&(2 * Kq) * &s0))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]
         THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 - a + b = &1 + (--a + b)`] THEN
      ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < &q` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Cw * &q rpow (--inv(&Kq) + inv(&(2 * Kq) * &s0))) pow s0` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_MUL; RPOW_POW_MUL] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `&0 < &Kq` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&q * Cw pow s0 * &q rpow (--(&2 + inv(&(2 * Kq))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; RPOW_POS_LE; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {a | a < q:num}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      SET_TAC[];
      REWRITE_TAC[CARD_NUMSEG_LT; LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `--(&1 + u) = &1 + --(&2 + u)`] THEN
  ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;
