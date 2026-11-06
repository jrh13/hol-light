(* ========================================================================= *)
(* Waring's problem III: local solubility and the singular series.           *)
(* * waring_loc k L s c = #{(x_1,...,x_s) mod L | x_1^k + ... + x_s^k == c   *)
(*   (mod L)} (recursion on s).  WARING_LOC_FOURIER expands it in complete   *)
(*   sums, and grouping the fractions a/L by gcd(a,L) gives WARING_LOC_SING: *)
(*     sum_{d | L} waring_term k s c d = waring_loc k L s c / L^(s-1),       *)
(*   a multiplicative function of L (WDEN_MULTIPLICATIVE, by the Chinese     *)
(*   remainder theorem).                                                     *)
(* * Hensel lifting, NEWTON_LIFT: with t = index p k, a solution of          *)
(*   u^k == a (mod p^h) with p not dividing u and h >= 2 t + 1 lifts to      *)
(*   p^(h+1).  So one solution mod p^g, g = 2 t + 1, with a unit coordinate  *)
(*   gives waring_loc k (p^h) (s + 1) c >= p^((h - g) s)                     *)
(*   (WARING_LOC_PRIMEPOW_LOWER).                                            *)
(* * SOLUBLE_PRIMEPOW: for s >= 2^k + 1 every c is a sum of s - 1 k-th       *)
(*   powers mod p^(2t+1), so that a last coordinate equal to 1 makes         *)
(*   WARING_LOC_PRIMEPOW_LOWER applicable.  Cases: all ones when p^(2t+1) <= *)
(*   s - 1 (SOLUBLE_ONES); the digits 1 and 2^k for p = 2 and even k         *)
(*   (SOLUBLE_TWO); 1, -1 and 2^k for odd k (SOLUBLE_SIGNED); otherwise      *)
(*   the growth of the sets of sums of k-th powers mod p (SOLUBLE_GROWTH:    *)
(*   there are at least (p - 1)/k nonzero k-th power residues, by            *)
(*   NUM_POLY_ROOTS for x^k - 1).                                            *)
(* * WARING_SING_LOWER: for s >= 2^k + 1 there are c0 > 0 and Q0 with        *)
(*   c0 <= Re(waring_sing k s N Q) for all N and all Q >= Q0.  With          *)
(*   L = (Q!)^(2k+1), sum_{d | L} waring_term is the product over p <= Q of  *)
(*   the local factors, which are at least p^(-(2t+1)(s-1)) for the finitely *)
(*   many small p (LOCAL_FACTOR_SMALL) and at least 1 - 2 C p^(-1-d) for     *)
(*   the large ones (LOCAL_FACTOR_LARGE, from WARING_CSUM_ABS_DECAY); the    *)
(*   terms of the sum with d > Q contribute at most C Q^(-d)/d.              *)
(* ========================================================================= *)

needs "Sieve/waring_major.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Local densities.                                                          *)
(* ------------------------------------------------------------------------- *)

let waring_loc = new_recursive_definition num_RECURSION
 `(waring_loc k L 0 c = if L divides c then &1 else &0) /\
  (waring_loc k L (SUC s) c =
     sum {x | x < L} (\x. waring_loc k L s (c + (L - 1) * x EXP k)))`;;

let WARING_LOC_FOURIER = prove
 (`!k L s c. 1 <= L
             ==> Cx(&L * waring_loc k L s c) =
                 vsum {a | a < L}
                   (\a. waring_csum k L a pow s * expi(--(&c * &a / &L)))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[waring_loc; complex_pow; COMPLEX_MUL_LID] THEN
    MP_TAC(SPECL [`L:num`; `--(&c)`] VSUM_EXPI_RESIDUES) THEN
    ASM_SIMP_TAC[INTEGER_NEG; INTEGER_CLOSED;
                 ARITH_RULE `1 <= L ==> ~(L = 0)`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[INTEGER_NEG; GSYM real_div] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[INTEGER_DIV_DIVIDES; ARITH_RULE `1 <= L ==> ~(L = 0)`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[waring_loc; GSYM SUM_LMUL] THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN
   `vsum {x | x < L} (\x. expi (--(&(c + (L - 1) * x EXP k) * &a / &L))) =
    expi(--(&c * &a / &L)) * waring_csum k L a`
  SUBST1_TAC THENL
   [REWRITE_TAC[waring_csum] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM EXPI_ADD] THEN
    MATCH_MP_TAC EXPI_INTEGER_DIFF THEN
    SUBGOAL_THEN `&0 < &L` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
                 GSYM REAL_OF_NUM_SUB] THEN
    SUBGOAL_THEN
     `--((&c + (&L - &1) * &(x EXP k)) * &a / &L) -
      (--(&c * &a / &L) + &a * &(x EXP k) / &L) =
      --(&(x EXP k) * &a)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &L` THEN CONV_TAC REAL_FIELD;
      SIMP_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[complex_pow] THEN CONV_TAC COMPLEX_RING);;

let VSUM_PERIODIC = prove
 (`!(f:num->complex) d m.
     (!x. f(x + d) = f x)
     ==> vsum {r | r < d * m} f = Cx(&m) * vsum {r | r < d} f`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; LT; EMPTY_GSPEC; VSUM_CLAUSES;
                COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j x. (f:num->complex)(x + d * j) = f x` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ADD_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{r | r < d * SUC m} =
    {r | r < d * m} UNION IMAGE (\r. r + d * m) {r | r < d:num}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[MULT_CLAUSES] THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `r < d * m:num` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `r - d * m:num` THEN ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_NUMSEG_LT; FINITE_IMAGE] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE;
                NOT_IN_EMPTY] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT] THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[o_DEF; ETA_AX; GSYM REAL_OF_NUM_SUC; CX_ADD] THEN
  REWRITE_TAC[COMPLEX_ADD_RDISTRIB; COMPLEX_MUL_LID]);;

let WARING_CSUM_SCALE = prove
 (`!k d L b. 1 <= d /\ 1 <= L /\ d divides L
             ==> waring_csum k L (b * (L DIV d)) = Cx(&(L DIV d)) *
                 waring_csum k d b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides]) THEN
  SUBGOAL_THEN `~(d = 0) /\ ~(m = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `1 <= d * m` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT] THEN REWRITE_TAC[waring_csum] THEN
  SUBGOAL_THEN
   `!r. expi(&(b * m) * &(r EXP k) / &(d * m)) =
        expi(&b * &(r EXP k) / &d)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&d = &0) /\ ~(&m = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC VSUM_PERIODIC THEN X_GEN_TAC `r:num` THEN BETA_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&b * &x / &d = &x * &b / &d`] THEN
  MATCH_MP_TAC EXPI_CONG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_EXP THEN CONV_TAC NUMBER_RULE);;

let VSUM_GCD_GROUP = prove
 (`!(g:num->complex) L.
     1 <= L
     ==> vsum {a | a < L} g =
         vsum {d | d divides L}
              (\d. vsum {b | b < d /\ coprime(b,d)} (\b. g(b * (L DIV d))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\a:num. gcd(a,L)`; `g:num->complex`; `{a:num | a < L}`;
                 `{e:num | e divides L}`] VSUM_GROUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    CONV_TAC NUMBER_RULE;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`\d. L DIV d`; `\d. L DIV d`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVISOR_REFLECT]; ALL_TAC] THEN
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`L:num`; `e:num`] DIVISOR_REFLECT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = L DIV e` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `e * m =
    L:num`)) THEN
  SUBGOAL_THEN
   `{x:num | x < e * m /\ gcd(x,e * m) = e} =
    IMAGE (\b. b * e) {b:num | b < m /\ coprime(b,m)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `x:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `x DIV e` THEN
      SUBGOAL_THEN `e divides x` MP_TAC THENL
       [UNDISCH_TAC `gcd(x,e * m) = e:num` THEN CONV_TAC NUMBER_RULE;
        REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `b:num`
          SUBST_ALL_TAC)] THEN
      ASM_SIMP_TAC[DIV_MULT] THEN
      CONJ_TAC THENL [REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `e * b < e * m:num` THEN ASM_REWRITE_TAC[LT_MULT_LCANCEL];
        UNDISCH_TAC `gcd(e * b,e * m) = e:num` THEN
        REWRITE_TAC[GCD_LMUL; COPRIME_GCD] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ARITH_RULE `e = e * 1:num`]
          THEN
        ASM_REWRITE_TAC[EQ_MULT_LCANCEL]];
      DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `b * e = e * b:num` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; GCD_LMUL] THEN
      UNDISCH_TAC `coprime(b:num,m)` THEN SIMP_TAC[COPRIME_GCD; MULT_CLAUSES]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{b | b < m:num}` THEN
      SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
      ASM_SIMP_TAC[EQ_MULT_RCANCEL]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let WARING_LOC_SING = prove
 (`!k s L c. 1 <= s /\ 1 <= L
             ==> vsum {d | d divides L} (\d. waring_term k s c d) =
                 Cx(waring_loc k L s c / &L pow (s - 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&L) pow s * vsum {d | d divides L} (\d. waring_term k s c d) =
    Cx(&L * waring_loc k L s c)`
  MP_TAC THENL
   [ASM_SIMP_TAC[WARING_LOC_FOURIER] THEN
    MP_TAC(ISPECL [`\a. waring_csum k L a pow s * expi(--(&c * &a / &L))`;
                   `L:num`] VSUM_GCD_GROUP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_DIVISORS] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`L:num`; `d:num`] DIVISOR_REFLECT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[waring_term] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_COPRIME_RESIDUES] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `b:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[WARING_CSUM_SCALE; ARITH_RULE `~(d = 0) ==> 1 <= d`] THEN
    ABBREV_TAC `m = L DIV d` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `d * m = L:num`)) THEN
      SUBGOAL_THEN `~(&d = &0) /\ ~(&m = &0)` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN CONJ_TAC THEN DISCH_TAC THEN
        UNDISCH_TAC `~(d * m = 0)` THEN ASM_REWRITE_TAC[MULT_CLAUSES];
        ALL_TAC] THEN
      SUBGOAL_THEN `&c * &(b * m) / &(d * m) = &c * &b / &d` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
        UNDISCH_TAC `~(&d = &0)` THEN UNDISCH_TAC `~(&m = &0)` THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM COMPLEX_POW_MUL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      UNDISCH_TAC `~(&d = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&L pow s = &L * &L pow (s - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&L = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&L) pow s = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0; CX_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `Cx(waring_loc k L s c / &L pow (s - 1)) =
                Cx(&L * waring_loc k L s c) / Cx(&L) pow s`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; CX_INJ] THEN
    SUBGOAL_THEN `~(&L pow (s - 1) = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_EQ_0]; ALL_TAC] THEN
    UNDISCH_TAC `~(&L = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `!z v w:complex. ~(z = Cx(&0)) /\ z * v = w ==> v = w / z`) THEN
  ASM_REWRITE_TAC[]);;

let CRT_SUM2 = prove
 (`!m n (f:num->real) g.
     coprime(m,n) /\ ~(m = 0) /\ ~(n = 0)
     ==> sum {x | x < m * n} (\x. f(x MOD m) * g(x MOD n)) =
         sum {a | a < m} f * sum {b | b < n} g`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL THEN
  EXISTS_TAC `\x:num. (x MOD m,x MOD n)` THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; FORALL_PAIR_THM; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[EXISTS_UNIQUE; PAIR_EQ] THEN
    MP_TAC(SPECL [`m:num`; `n:num`; `a:num`; `b:num`]
      CHINESE_REMAINDER_USUAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x MOD (m * n:num)` THEN
    ASM_SIMP_TAC[MOD_LT_EQ; MULT_EQ_0; MOD_MOD] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(x:num == a) (mod m)` THEN UNDISCH_TAC `(x:num == b) (mod
       n)` THEN
      ASM_SIMP_TAC[CONG; MOD_LT] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MOD] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MOD];
      ALL_TAC] THEN
    X_GEN_TAC `y:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `m * n:num` THEN
    ASM_SIMP_TAC[MOD_LT_EQ; MULT_EQ_0; CONG_CHINESE_EQ] THEN
    REWRITE_TAC[CONG] THEN ASM_SIMP_TAC[MOD_MOD] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MOD] THEN
    UNDISCH_TAC `(x:num == a) (mod m)` THEN UNDISCH_TAC `(x:num == b) (mod n)`
      THEN
    ASM_SIMP_TAC[CONG; MOD_LT];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x MOD m:num`; `x MOD n:num`] THEN
    ASM_SIMP_TAC[MOD_LT_EQ]]);;

let WARING_LOC_CONG = prove
 (`!k L s c c'. (c == c') (mod L)
                ==> waring_loc k L s c = waring_loc k L s c'`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[waring_loc] THENL
   [SUBGOAL_THEN `L divides c <=> L divides c'` (fun th -> REWRITE_TAC[th])
    THEN UNDISCH_TAC `(c:num == c') (mod L)` THEN CONV_TAC NUMBER_RULE;
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(c:num == c') (mod L)` THEN CONV_TAC NUMBER_RULE]);;

let WLOC_SHIFT_CONG = prove
 (`!c x k L1 L2.
     ~(L1 = 0) /\ ~(L2 = 0)
     ==> (c + (L1 * L2 - 1) * x EXP k ==
          c + (L1 - 1) * (x MOD L1) EXP k) (mod L1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(L1 * L2 - 1) + 1 = L1 * L2 /\ (L1 - 1) + 1 = L1`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUB_ADD THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `L1:num`] CONG_MOD) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
  SPEC_TAC(`(x MOD L1) EXP k`,`Y:num`) THEN
  SPEC_TAC(`x EXP k`,`X:num`) THEN
  SPEC_TAC(`L1 * L2 - 1`,`a:num`) THEN SPEC_TAC(`L1 - 1`,`b:num`) THEN
  CONV_TAC NUMBER_RULE);;

let WARING_LOC_MUL = prove
 (`!k s L1 L2 c.
     coprime(L1,L2) /\ ~(L1 = 0) /\ ~(L2 = 0)
     ==> waring_loc k (L1 * L2) s c = waring_loc k L1 s c *
         waring_loc k L2 s c`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[waring_loc] THENL
   [SUBGOAL_THEN `L1 * L2 divides c <=> L1 divides c /\ L2 divides c`
    SUBST1_TAC THENL
     [UNDISCH_TAC `coprime(L1:num,L2)` THEN CONV_TAC NUMBER_RULE;
      MAP_EVERY ASM_CASES_TAC [`L1 divides c`; `L2 divides c`] THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!x. waring_loc k L1 s (c + (L1 * L2 - 1) * x EXP k) =
        waring_loc k L1 s (c + (L1 - 1) * (x MOD L1) EXP k) /\
        waring_loc k L2 s (c + (L1 * L2 - 1) * x EXP k) =
        waring_loc k L2 s (c + (L2 - 1) * (x MOD L2) EXP k)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC WARING_LOC_CONG THEN
    ASM_SIMP_TAC[WLOC_SHIFT_CONG] THEN
    SUBGOAL_THEN `L1 * L2 = L2 * L1:num` SUBST1_TAC THENL
     [ARITH_TAC; ASM_SIMP_TAC[WLOC_SHIFT_CONG]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L1:num`; `L2:num`;
                 `\y. waring_loc k L1 s (c + (L1 - 1) * y EXP k)`;
                 `\y. waring_loc k L2 s (c + (L2 - 1) * y EXP k)`]
                   CRT_SUM2) THEN
  ASM_REWRITE_TAC[]);;

let REAL_MULTIPLICATIVE_EXPAND = prove
 (`!f n.
       real_multiplicative f /\ ~(n = 0)
       ==> f n = product {p | prime p /\ p divides n}
                         (\p. f(p EXP index p n))`,
  REWRITE_TAC[real_multiplicative] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[MESON[PRIME_1; DIVIDES_ONE]
      `~(prime p /\ p divides 1)`] THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; PRODUCT_CLAUSES];
    MAP_EVERY UNDISCH_TAC [`~(n = 1)`; `~(n = 0)`] THEN
    REWRITE_TAC[IMP_IMP; ARITH_RULE `~(n = 0) /\ ~(n = 1) <=> 1 < n`]] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN ASM_SIMP_TAC[] THEN
    REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MESON[PRIME_DIVPROD_EQ]
     `prime p /\ p divides a * b <=>
      prime p /\ p divides a \/ prime p /\ p divides b`] THEN
    REWRITE_TAC[SET_RULE `{x:num | P x \/ Q x} = {x | P x} UNION {x | Q x}`]
      THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_UNION o rand o snd) THEN
    ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; ARITH_RULE `1 < p ==> ~(p = 0)`] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_ELIM_THM;
                  IN_INTER; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[COPRIME_PRIME_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    BINOP_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_SIMP_TAC[INDEX_MUL; ARITH_RULE `1 < p ==> ~(p = 0)`] THEN
    REWRITE_TAC[EQ_ADD_LCANCEL_0; EQ_ADD_RCANCEL_0] THEN
    REWRITE_TAC[INDEX_EQ_0] THEN ASM_MESON_TAC[COPRIME_PRIME_EQ];
    SIMP_TAC[MESON[PRIME_DIVEXP_EQ; DIVIDES_PRIME_PRIME]
     `prime p ==> (prime q /\ q divides p EXP k <=> q = p /\ ~(k = 0))`] THEN
    REWRITE_TAC[SING_GSPEC; PRODUCT_SING] THEN
    SIMP_TAC[INDEX_EXP; INDEX_REFL] THEN
    REWRITE_TAC[ARITH_RULE `p <= 1 <=> p = 0 \/ p = 1`] THEN
    ASM_MESON_TAC[PRIME_0; PRIME_1; MULT_CLAUSES]]);;

let WARING_LOC_1 = prove
 (`!k s c. waring_loc k 1 s c = &1`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[waring_loc; DIVIDES_1] THEN
  REWRITE_TAC[ARITH_RULE `x < 1 <=> x = 0`; SING_GSPEC; SUM_SING]);;

let WDEN_MULTIPLICATIVE = prove
 (`!k s c. real_multiplicative (\L. waring_loc k L s c / &L pow (s - 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MULTIPLICATIVE] THEN
  REWRITE_TAC[WARING_LOC_1; REAL_POW_ONE; REAL_DIV_1] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WARING_LOC_MUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_MUL; real_div; REAL_INV_MUL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hensel lifting; solubility by ones and by two digits.                     *)
(* ------------------------------------------------------------------------- *)

let BINOM_LINEAR = prove
 (`!u y k. ?R. (u + y) EXP k = u EXP k + k * u EXP (k - 1) * y + y EXP 2 * R`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `R:num` ASSUME_TAC) THEN
  EXISTS_TAC `u * R + k * u EXP (k - 1) + y * R` THEN
  ASM_REWRITE_TAC[EXP; SUC_SUB1] THEN
  ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; SUB_0] THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u EXP k = u * u EXP (k - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXP_2] THEN ARITH_TAC);;

let CONG_LIFT_STEP = prove
 (`!x y n p. ~(p = 0) /\ (x == y) (mod n)
             ==> ?t. (y + n * t == x) (mod (n * p))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[CONG_SUB_CASES]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[CONG_0; divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:num`) THENL
   [EXISTS_TAC `(p - 1) * d` THEN
    SUBGOAL_THEN `y + n * (p - 1) * d = x + (n * p) * d:num` SUBST1_TAC THENL
     [UNDISCH_TAC `~(p = 0)` THEN SPEC_TAC(`p:num`,`p:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
      UNDISCH_TAC `y - x = n * d:num` THEN UNDISCH_TAC `x <= y:num` THEN
      REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
      CONV_TAC NUMBER_RULE];
    EXISTS_TAC `d:num` THEN
    SUBGOAL_THEN `y + n * d = x:num` SUBST1_TAC THENL
     [UNDISCH_TAC `x - y = n * d:num` THEN UNDISCH_TAC `~(x <= y:num)` THEN
      ARITH_TAC;
      REWRITE_TAC[CONG_REFL]]]);;

let NEWTON_LIFT = prove
 (`!p k h u a.
     prime p /\ 1 <= k /\ 2 * index p k + 1 <= h /\ ~(p divides u) /\
     (u EXP k == a) (mod (p EXP h))
     ==> ?v. (v == u) (mod (p EXP (h - index p k))) /\
             (v EXP k == a) (mod (p EXP (h + 1)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t0 = index p k` THEN
  MP_TAC(SPECL [`k:num`; `p:num`] INDEX_DECOMPOSITION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> ~(k = 0)`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:num`; `u EXP k`; `p EXP h`; `p:num`] CONG_LIFT_STEP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONG_SYM; PRIME_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:num`) THEN
  MP_TAC(SPECL [`k' * u EXP (k - 1)`; `t:num`; `p:num`] CONG_SOLVE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COPRIME_LMUL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[COPRIME_SYM];
      REWRITE_TAC[COPRIME_LEXP] THEN DISJ1_TAC THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
  EXISTS_TAC `u + p EXP (h - t0) * z` THEN
  CONJ_TAC THENL [CONV_TAC NUMBER_RULE; ALL_TAC] THEN
  MP_TAC(SPECL [`u:num`; `p EXP (h - t0) * z`; `k:num`] BINOM_LINEAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num` SUBST1_TAC) THEN
  SUBGOAL_THEN `p EXP h = p EXP t0 * p EXP (h - t0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `k * u EXP (k - 1) * p EXP (h - t0) * z =
    p EXP h * ((k' * u EXP (k - 1)) * z)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `p EXP t0 * k' = k`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p EXP h * p = p EXP (h + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_ADD; EXP_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(p EXP (h - t0) * z) EXP 2 * R =
    (p EXP h * p) * (p EXP (2 * (h - t0) - (h + 1)) * z EXP 2 * R)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[MULT_EXP; GSYM EXP_MULT; MULT_ASSOC; GSYM EXP_ADD] THEN
    SUBGOAL_THEN `(h + 1) + 2 * (h - t0) - (h + 1) = (h - t0) * 2`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `p EXP h * p = p EXP (h + 1)`)] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `!U P t a p A B:num. (U + P * t == a) (mod (P * p)) /\
                        (A == t) (mod p)
                        ==> (U + P * A + (P * p) * B == a) (mod (P * p))`) THEN
  EXISTS_TAC `t:num` THEN ASM_REWRITE_TAC[]);;

let HENSEL_ITER = prove
 (`!p k u a g.
     prime p /\ 1 <= k /\ 2 * index p k + 1 <= g /\ ~(p divides u) /\
     (u EXP k == a) (mod (p EXP g))
     ==> !h. g <= h ==> ?v. ~(p divides v) /\ (v EXP k == a) (mod (p EXP h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!d. ?v. ~(p divides v) /\ (v EXP k == a) (mod (p EXP (g + d)))`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [EXISTS_TAC `u:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`p:num`; `k:num`; `g + d:num`; `v:num`; `a:num`]
      NEWTON_LIFT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `g + SUC d = (g + d) + 1`] THEN
    UNDISCH_TAC `~(p divides v:num)` THEN
    SUBGOAL_THEN `p divides p EXP ((g + d) - index p k)` MP_TAC THENL
     [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM EXP_1] THEN
      MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC;
      UNDISCH_TAC `(w == v) (mod (p EXP ((g + d) - index p k)))` THEN
      MATCH_MP_TAC(TAUT `(a ==> b ==> d ==> c) ==> a ==> b ==> ~c ==> ~d`)
      THEN CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  X_GEN_TAC `h:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h - g:num`) THEN
  ASM_SIMP_TAC[ARITH_RULE `g <= h ==> g + h - g = h:num`]);;

let WARING_LOC_POS = prove
 (`!k L s c. &0 <= waring_loc k L s c`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[waring_loc] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT]]);;

let SUM_MOD_PERIODIC = prove
 (`!(f:num->real) d m.
     ~(d = 0)
     ==> sum {x | x < d * m} (\x. f(x MOD d)) = &m * sum {y | y < d} f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. Cx((f:num->real)(x MOD d))`; `d:num`; `m:num`]
    VSUM_PERIODIC) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `x:num` THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM CONG] THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_CX; FINITE_NUMSEG_LT; GSYM CX_MUL; CX_INJ] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM; MOD_LT]);;

let SHIFT_CONG_DIV = prove
 (`!c x k L L'.
     ~(L = 0) /\ ~(L' = 0) /\ L divides L'
     ==> (c + (L' - 1) * x EXP k == c + (L - 1) * (x MOD L) EXP k) (mod L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(L' - 1) + 1 = L' /\ (L - 1) + 1 = L` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `L:num`] CONG_MOD) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
  UNDISCH_TAC `(L:num) divides L'` THEN
  SPEC_TAC(`(x MOD L) EXP k`,`Y:num`) THEN
  SPEC_TAC(`x EXP k`,`X:num`) THEN
  SPEC_TAC(`L' - 1`,`a:num`) THEN SPEC_TAC(`L - 1`,`b:num`) THEN
  CONV_TAC NUMBER_RULE);;

let WARING_LOC_REDUCE = prove
 (`!k r L L' m0.
     ~(L = 0) /\ ~(L' = 0) /\ L divides L'
     ==> sum {m | m < L'}
             (\m. if (m == m0) (mod L) then waring_loc k L' r m else &0) =
         &(L' DIV L) pow r * waring_loc k L r m0`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[waring_loc; real_pow; REAL_MUL_LID] THEN
    TRANS_TAC EQ_TRANS
     `sum {m | m < L'}
          (\m. if m = 0 then (if (L:num) divides m0 then &1 else &0) else &0)`
            THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THENL
       [REWRITE_TAC[NUMBER_RULE `(0 == m0) (mod L) <=> (L:num) divides m0`];
        SUBGOAL_THEN `~((L':num) divides m)` (fun th -> REWRITE_TAC[th]) THENL
         [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
          COND_CASES_TAC THEN REWRITE_TAC[]]];
      REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`]];
    ALL_TAC] THEN
  REWRITE_TAC[waring_loc] THEN
  SUBGOAL_THEN
   `!m. (if (m == m0) (mod L)
         then sum {x | x < L'} (\x. waring_loc k L' r (m + (L' - 1) * x EXP k))
         else &0) =
        sum {x | x < L'}
            (\x. if (m == m0) (mod L)
                 then waring_loc k L' r (m + (L' - 1) * x EXP k) else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUM_0]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum {x | x < L'}
        (\x. &(L' DIV L) pow r *
             waring_loc k L r (m0 + (L - 1) * (x MOD L) EXP k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
    ABBREV_TAC `t = (L' - 1) * x EXP k` THEN
      SUBGOAL_THEN
       `!m. (if (m == m0) (mod L) then waring_loc k L' r (m + t) else &0) =
            (\y. if (y == m0 + t) (mod L) then waring_loc k L' r y else &0)
            ((m + t) MOD L')`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN BETA_TAC THEN
        SUBGOAL_THEN `((m + t) MOD L' == m0 + t) (mod L) <=> (m == m0) (mod L)`
        SUBST1_TAC THENL
         [MP_TAC(SPECL [`m + t:num`; `L':num`] CONG_MOD) THEN
          UNDISCH_TAC `(L:num) divides L'` THEN CONV_TAC NUMBER_RULE;
          ALL_TAC] THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC WARING_LOC_CONG THEN
        MESON_TAC[CONG_MOD; CONG_SYM];
        ALL_TAC] THEN
      MP_TAC(ISPECL
               [`\y. if (y == m0 + t) (mod L) then waring_loc k L'
                       r y else &0`;
                     `L':num`; `t:num`] SUM_SHIFT_MOD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`L:num`; `L':num`; `m0 + t:num`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC WARING_LOC_CONG THEN EXPAND_TAC "t" THEN
      MATCH_MP_TAC SHIFT_CONG_DIV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_LMUL; real_pow] THEN
      MP_TAC(SPECL [`L':num`; `L:num`] DIVISOR_REFLECT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`\y. waring_loc k L r (m0 + (L - 1) * y EXP k)`; `L:num`;
                     `L' DIV L`] SUM_MOD_PERIODIC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(REAL_RING `a = b ==> c * d * a = (d * c) * b:real`) THEN
      REWRITE_TAC[]]);;

let WARING_LOC_PEEL_LOWER = prove
 (`!k L s c P.
     ~(L = 0) /\
     (!m. m < L /\ P m
          ==> ?x. x < L /\ ((c + (L - 1) * x EXP k) == m) (mod L))
     ==> sum {m | m < L} (\m. if P m then waring_loc k L s m else &0)
         <= waring_loc k L (SUC s) c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_loc] THEN
  SUBGOAL_THEN
   `!x. waring_loc k L s (c + (L - 1) * x EXP k) =
        waring_loc k L s ((c + (L - 1) * x EXP k) MOD L)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC WARING_LOC_CONG THEN
    MESON_TAC[CONG_MOD; CONG_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (c + (L - 1) * x EXP k) MOD L`;
                 `\x. waring_loc k L s ((c + (L - 1) * x EXP k) MOD L)`;
                 `{x | x < L:num}`; `{m | m < L:num}`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
                 MOD_LT_EQ];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {x | x < L /\ (c + (L - 1) * x EXP k) MOD L = m}
        (\x. waring_loc k L s m)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM]] THEN
  SUBGOAL_THEN `FINITE {x | x < L /\ (c + (L - 1) * x EXP k) MOD L = m}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x | x < L:num}` THEN
    SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; WARING_LOC_POS]] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[WARING_LOC_POS; REAL_OF_NUM_LE] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num` THEN
  SIMP_TAC[CONG] THEN ASM_SIMP_TAC[MOD_LT]);;

let WARING_LOC_PRIMEPOW_LOWER = prove
 (`!k s p g h c.
     prime p /\ 1 <= k /\ 2 * index p k + 1 <= g /\ g <= h /\
     &1 <= waring_loc k (p EXP g) s (c + (p EXP g - 1))
     ==> &(p EXP (h - g)) pow s <= waring_loc k (p EXP h) (SUC s) c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p EXP g = 0) /\ ~(p EXP h = 0) /\ p EXP g divides p EXP h`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ; DIVIDES_EXP_LE_IMP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `p EXP h`; `s:num`; `c:num`;
                 `\m. (m == c + (p EXP g - 1)) (mod (p EXP g))`]
    WARING_LOC_PEEL_LOWER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `k:num`; `1`; `c + (p EXP h - 1) * m`; `g:num`]
      HENSEL_ITER) THEN
    ASM_REWRITE_TAC[EXP_ONE; DIVIDES_ONE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
      SUBGOAL_THEN `(p EXP g - 1) + 1 = p EXP g /\ (p EXP h - 1) + 1 = p EXP h`
        MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(m == c + p EXP g - 1) (mod (p EXP g))` THEN
        UNDISCH_TAC `p EXP g divides p EXP h` THEN
        SPEC_TAC(`p EXP g - 1`,`A:num`) THEN SPEC_TAC(`p EXP h - 1`,`B:num`)
          THEN
        SPEC_TAC(`p EXP g`,`G:num`) THEN SPEC_TAC(`p EXP h`,`H:num`) THEN
        CONV_TAC NUMBER_RULE;
      DISCH_THEN(MP_TAC o SPEC `h:num`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `v MOD p EXP h` THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN
        MP_TAC(SPECL [`v:num`; `p EXP h`] CONG_MOD) THEN
        DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
        SUBGOAL_THEN `(p EXP h - 1) + 1 = p EXP h` MP_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(v EXP k == c + (p EXP h - 1) * m) (mod (p EXP h))` THEN
        SPEC_TAC(`(v MOD p EXP h) EXP k`,`Y:num`) THEN
        SPEC_TAC(`v EXP k`,`X:num`) THEN
        SPEC_TAC(`p EXP h - 1`,`B:num`) THEN SPEC_TAC(`p EXP h`,`H:num`) THEN
        CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `s:num`; `p EXP g`; `p EXP h`; `c + (p EXP g - 1)`]
      WARING_LOC_REDUCE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `p EXP h DIV p EXP g = p EXP (h - g)` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
      ASM_SIMP_TAC[ADD_CLAUSES; GSYM EXP_ADD; SUB_ADD; LT_NZ];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]);;

let WARING_LOC_REPR = prove
 (`!k L s c y.
     ~(L = 0) /\ (nsum(1..s) (\i. y i EXP k) == c) (mod L)
     ==> &1 <= waring_loc k L s c`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[waring_loc] THENL
   [SUBGOAL_THEN `(L:num) divides c` (fun th -> REWRITE_TAC[th; REAL_LE_REFL])
     THEN
    UNDISCH_TAC `(nsum(1..0) (\i. y i EXP k) == c) (mod L)` THEN
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH] THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  ABBREV_TAC `x0 = y(SUC s) MOD L` THEN
  SUBGOAL_THEN `x0 < L:num` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN ASM_SIMP_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= waring_loc k L s (c + (L - 1) * x0 EXP k)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:num->num` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(nsum(1..SUC s) (\i. y i EXP k) == c) (mod L)` THEN
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN
    MP_TAC(SPECL [`y(SUC s):num`; `L:num`] CONG_MOD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
    SUBGOAL_THEN `(L - 1) + 1 = L` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`nsum(1..s) (\i. y i EXP k)`,`S:num`) THEN
    SPEC_TAC(`x0 EXP k`,`X:num`) THEN SPEC_TAC(`y(SUC s) EXP k`,`Y:num`) THEN
    SPEC_TAC(`L - 1`,`B:num`) THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `waring_loc k L s (c + (L - 1) * x0 EXP k)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
           [`\x. waring_loc k L s (c + (L - 1) * x EXP k)`; `{x | x < L:num}`;
                 `x0:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= d ==> d = s - a ==> a <= s`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN
  SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; WARING_LOC_POS]);;

let SOLUBLE_ONES = prove
 (`!k L s c. 1 <= k /\ ~(L = 0) /\ c MOD L <= s ==> &1 <= waring_loc k L s c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WARING_LOC_REPR THEN
  EXISTS_TAC `\i. if i <= c MOD L then 1 else 0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `nsum(1..s) (\i. (if i <= c MOD L then 1 else 0) EXP k) = c MOD L`
  SUBST1_TAC THENL
   [ALL_TAC; MESON_TAC[CONG_MOD]] THEN
  SUBGOAL_THEN `!i. (if i <= c MOD L then 1 else 0) EXP k =
                    if i <= c MOD L then 1 else 0`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[EXP_ONE; EXP_ZERO] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NSUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{i | i IN 1..s /\ i <= c MOD L} = 1..(c MOD L)` SUBST1_TAC
  THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN GEN_TAC THEN
    ASM_ARITH_TAC;
    SIMP_TAC[NSUM_CONST_NUMSEG; MULT_CLAUSES; ADD_SUB]]);;

let WARING_LOC_STEP_LOWER = prove
 (`!k L s c x. x < L ==> waring_loc k L s (c + (L - 1) * x EXP k) <=
                         waring_loc k L (SUC s) c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_loc] THEN
  MP_TAC(ISPECL
           [`\x. waring_loc k L s (c + (L - 1) * x EXP k)`; `{x | x < L:num}`;
                 `x:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= d ==> d = s - a ==> a <= s`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN
  SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; WARING_LOC_POS]);;

let WARING_LOC_SHIFTS_LOWER = prove
 (`!k L s x j c. x < L ==> waring_loc k L s (c + j * (L - 1) * x EXP k) <=
                           waring_loc k L (s + j) c`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `waring_loc k L (s + j) (c + (L - 1) * x EXP k)` THEN
  ASM_SIMP_TAC[WARING_LOC_STEP_LOWER] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c + (L - 1) * x EXP k` o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let SOLUBLE_TWO = prove
 (`!k L s c w. 1 <= k /\ ~(L = 0) /\ w < L /\ L <= 2 * w EXP k /\ w EXP k <= s
               ==> &1 <= waring_loc k L s c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c MOD L <= s` THENL
   [ASM_MESON_TAC[SOLUBLE_ONES]; ALL_TAC] THEN
  ABBREV_TAC `r = c MOD L` THEN ABBREV_TAC `v = w EXP k` THEN
  SUBGOAL_THEN `r < L:num /\ v <= r /\ r - v < v /\ ~(s = 0:num)`
    STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `L:num`; `s - 1`; `c:num`; `w:num`]
    WARING_LOC_STEP_LOWER) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(s = 0) ==> SUC(s - 1) = s`] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= a ==> a <= b ==> &1 <= b`) THEN
  MATCH_MP_TAC SOLUBLE_ONES THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c + (L - 1) * v) MOD L = r - v` SUBST1_TAC THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  REWRITE_TAC[MOD_UNIQUE] THEN
  CONJ_TAC THENL [DISJ2_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(L - 1) + 1 = L:num /\ (r - v) + v = r:num` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:num`; `L:num`] CONG_MOD) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`r - v:num`,`d:num`) THEN SPEC_TAC(`L - 1`,`B:num`) THEN
  CONV_TAC NUMBER_RULE);;

let ODD_POW_PRED_CONG = prove
 (`!L k. ODD k ==> ((L - 1) EXP k == L - 1) (mod L)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[EXP; GSYM EXP_EXP] THEN
  ASM_CASES_TAC `L = 0` THENL
   [ASM_REWRITE_TAC[ARITH; EXP_ZERO; MULT_EQ_0] THEN
    COND_CASES_TAC THEN REWRITE_TAC[CONG_REFL; MULT_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `((L - 1) EXP 2 == 1) (mod L)` MP_TAC THENL
   [SUBGOAL_THEN `(L - 1) + 1 = L` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`L - 1`,`B:num`) THEN GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXP_2] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num` o MATCH_MP CONG_EXP) THEN
  REWRITE_TAC[EXP_ONE] THEN
  SPEC_TAC(`((L - 1) EXP 2) EXP m`,`Z:num`) THEN
  CONV_TAC NUMBER_RULE);;

let SOLUBLE_SIGNED = prove
 (`!k L s c w.
     1 <= k /\ ODD k /\ 2 <= L /\ w < L /\ 1 <= w EXP k /\
     (L - 1) DIV (w EXP k) + 1 + (w EXP k) DIV 2 <= s
     ==> &1 <= waring_loc k L s c`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `v = w EXP k` THEN ABBREV_TAC `r = c MOD L` THEN
  ABBREV_TAC `a = r DIV v` THEN ABBREV_TAC `b = r MOD v` THEN
  SUBGOAL_THEN `r < L /\ r = a * v + b /\ b < v /\ a <= (L - 1) DIV v`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"; "r"] THEN
    SUBGOAL_THEN `~(L = 0) /\ ~(v = 0)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[MOD_LT_EQ; ASSUME `~(L = 0)`; ASSUME `~(v = 0)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[DIVISION];
      MATCH_MP_TAC DIV_MONO THEN
      MP_TAC(SPECL [`c:num`; `L:num`] MOD_LT_EQ) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num == a * v + b) (mod L)` ASSUME_TAC THENL
   [UNDISCH_TAC `r = a * v + b:num` THEN EXPAND_TAC "r" THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[CONG_MOD; CONG_SYM];
    ALL_TAC] THEN
  ASM_CASES_TAC `b <= v DIV 2` THENL
   [MP_TAC(SPECL [`k:num`; `L:num`; `s - a:num`; `w:num`; `a:num`; `c:num`]
      WARING_LOC_SHIFTS_LOWER) THEN
    SUBGOAL_THEN `s - a + a = s:num` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= a ==> a <= b ==> &1 <= b`) THEN
    MATCH_MP_TAC SOLUBLE_ONES THEN
        ASM_REWRITE_TAC[ARITH_RULE `2 <= L ==> ~(L = 0)`] THEN
        SUBGOAL_THEN `(c + a * (L - 1) * v) MOD L = b` SUBST1_TAC THENL
         [REWRITE_TAC[MOD_UNIQUE] THEN
          CONJ_TAC THENL [DISJ2_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(L - 1) + 1 = L:num` MP_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          UNDISCH_TAC `(c:num == a * v + b) (mod L)` THEN
          SPEC_TAC(`L - 1`,`B:num`) THEN CONV_TAC NUMBER_RULE;
          ASM_ARITH_TAC];
    ABBREV_TAC `e = v - b:num` THEN
      SUBGOAL_THEN `e + b = v:num /\ (a + 1) + e <= s` STRIP_ASSUME_TAC THENL
       [MP_TAC(SPECL [`v:num`; `2`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`k:num`; `L:num`; `s - (a + 1)`; `w:num`; `a + 1`; `c:num`]
        WARING_LOC_SHIFTS_LOWER) THEN
      SUBGOAL_THEN `s - (a + 1) + a + 1 = s:num` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= a ==> a <= b ==> &1 <= b`) THEN
      MP_TAC(SPECL [`k:num`; `L:num`; `s - (a + 1) - e`; `L - 1`; `e:num`;
                    `c + (a + 1) * (L - 1) * v`] WARING_LOC_SHIFTS_LOWER) THEN
      SUBGOAL_THEN `s - (a + 1) - e + e = s - (a + 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= a ==> a <= b ==> &1 <= b`) THEN
      MATCH_MP_TAC SOLUBLE_ONES THEN
      ASM_SIMP_TAC[ARITH_RULE `2 <= L ==> ~(L = 0)`] THEN
      SUBGOAL_THEN
       `((c + (a + 1) * (L - 1) * v) + e * (L - 1) * (L - 1) EXP k) MOD L = 0`
      SUBST1_TAC THENL [ALL_TAC; ARITH_TAC] THEN
      REWRITE_TAC[MOD_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`L:num`; `k:num`] ODD_POW_PRED_CONG) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(L - 1) + 1 = L:num` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(c:num == a * v + b) (mod L)` THEN
      UNDISCH_TAC `e + b = v:num` THEN
      SPEC_TAC(`(L - 1) EXP k`,`X:num`) THEN
      SPEC_TAC(`L - 1`,`B:num`) THEN CONV_TAC NUMBER_RULE]);;

(* ------------------------------------------------------------------------- *)
(* Solubility for every prime power.                                         *)
(* ------------------------------------------------------------------------- *)

let WARING_LOC_SCALE = prove
 (`!k L s c u. coprime(u,L)
               ==> waring_loc k L s (u EXP k * c) = waring_loc k L s c`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[waring_loc] THENL
   [SUBGOAL_THEN `L divides u EXP k * c <=> L divides c`
      (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `coprime(u EXP k,L)` MP_TAC THENL
     [ASM_REWRITE_TAC[COPRIME_LEXP]; CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. waring_loc k L s (u EXP k * c + (L - 1) * x EXP k)`;
                 `L:num`; `u:num`] SUM_OVER_RESIDUES_MUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC WARING_LOC_CONG THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `u EXP k * c + (L - 1) * (u * x) EXP k =
                u EXP k * (c + (L - 1) * x EXP k)` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_EXP] THEN ARITH_TAC;
    ASM_SIMP_TAC[]]);;

let WARING_LOC_ADD_POWER = prove
 (`!k L s a x. ~(L = 0) /\ &1 <= waring_loc k L s a
               ==> &1 <= waring_loc k L (SUC s) (a + x EXP k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `waring_loc k L s (a + x EXP k + (L - 1) * (x MOD L) EXP k)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `waring_loc k L s (a + x EXP k + (L - 1) * (x MOD L) EXP k) =
                  waring_loc k L s a` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC WARING_LOC_CONG THEN
    MP_TAC(SPECL [`x:num`; `L:num`] CONG_MOD) THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
    SUBGOAL_THEN `(L - 1) + 1 = L:num` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`(x MOD L) EXP k`,`Y:num`) THEN SPEC_TAC(`x EXP k`,`X:num`) THEN
    SPEC_TAC(`L - 1`,`B:num`) THEN CONV_TAC NUMBER_RULE;
    REWRITE_TAC[ADD_ASSOC] THEN MATCH_MP_TAC WARING_LOC_STEP_LOWER THEN
    ASM_SIMP_TAC[MOD_LT_EQ]]);;

let WARING_LOC_ZERO_POS = prove
 (`!k L s. 1 <= k /\ ~(L = 0) ==> &1 <= waring_loc k L s 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SOLUBLE_ONES THEN
  ASM_SIMP_TAC[MOD_0; LE_0]);;

let WPOLY_DIFF = prove
 (`!n a x y.
        sum(0..n) (\i. a(i) * x pow i) - sum(0..n) (\i. a(i) * y pow i) =
        (x - y) *
        sum(0..n-1) (\i. sum(i+1..n) (\j. a j * y pow (j - 1 - i)) * x pow i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_LDISTRIB] THEN
  MP_TAC(ISPEC `n:num` LE_0) THEN SIMP_TAC[SUM_CLAUSES_LEFT; ADD_CLAUSES] THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_LID; real_pow] THEN
  SIMP_TAC[REAL_SUB_POW] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = b * a * c`] THEN
  REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL; SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  REPEAT(EXISTS_TAC `\(a:num,b:num). (b,a)`) THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; FORALL_PAIR_THM; REAL_MUL_AC] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let NUM_POLY_ROOTS = prove
 (`!p n a. prime p /\ ~(p divides a n)
           ==> CARD {x | x < p /\ p divides nsum(0..n) (\i. a i * x EXP i)}
               <= n`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[NSUM_SING_NUMSEG; EXP; MULT_CLAUSES; LE] THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; CARD_CLAUSES];
    ALL_TAC] THEN
  ABBREV_TAC `Z = {x | x < p /\ p divides nsum(0..SUC n) (\i. a i * x EXP i)}`
    THEN
  ASM_CASES_TAC `Z:num->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES; LE_0]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
  ABBREV_TAC `b = \j. nsum(j+1..SUC n) (\i. a i * c EXP (i - 1 - j))` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:num->num`) THEN ANTS_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[ARITH_RULE `n + 1 = SUC n`] THEN
    REWRITE_TAC[NSUM_SING_NUMSEG; SUB_REFL; ARITH_RULE `SUC n - 1 - n = 0`;
                EXP; MULT_CLAUSES] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `Z' = {x | x < p /\ p divides nsum(0..n) (\i. b i * x EXP i)}`
    THEN
  SUBGOAL_THEN `FINITE(Z':num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z'" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x | x < p:num}` THEN
    SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD((c:num) INSERT Z')` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_INSERT];
    ASM_SIMP_TAC[CARD_CLAUSES] THEN COND_CASES_TAC THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INSERT] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:num = c` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`(x:num) IN Z`; `(c:num) IN Z`] THEN
  MAP_EVERY EXPAND_TAC ["Z"; "Z'"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`SUC n`; `\i. &((a:num->num) i):real`; `&x:real`; `&c:real`]
    WPOLY_DIFF) THEN
  REWRITE_TAC[SUC_SUB1] THEN
  SUBGOAL_THEN
   `sum(0..n) (\i. sum(i+1..SUC n) (\j. &(a j) * &c pow (j - 1 - i)) *
                   &x pow i) =
    &(nsum(0..n) (\i. b i * x EXP i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG; GSYM REAL_OF_NUM_MUL;
                GSYM REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG; GSYM REAL_OF_NUM_MUL;
                GSYM REAL_OF_NUM_POW];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; GSYM REAL_OF_NUM_SUM_NUMSEG]
    THEN
  ABBREV_TAC `Fx = nsum(0..SUC n) (\i. a i * x EXP i)` THEN
  ABBREV_TAC `Fc = nsum(0..SUC n) (\i. a i * c EXP i)` THEN
  ABBREV_TAC `G = nsum(0..n) (\i. b i * x EXP i)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(p:num) divides (if c < x then x - c else c - x) * G` MP_TAC
    THENL
   [COND_CASES_TAC THENL
     [SUBGOAL_THEN `Fx = Fc + (x - c) * G:num` SUBST_ALL_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD;
                    GSYM REAL_OF_NUM_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[DIVIDES_ADD_REVR]];
      SUBGOAL_THEN `Fc = Fx + (c - x) * G:num` SUBST_ALL_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD;
                    GSYM REAL_OF_NUM_MUL] THEN
        SUBGOAL_THEN `x <= c:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]
          THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[DIVIDES_ADD_REVR]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
  MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let NUM_ROOTS_OF_UNITY_BOUND = prove
 (`!p k. prime p /\ 1 <= k
         ==> CARD {x | x < p /\ (x EXP k == 1) (mod p)} <= k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `k:num`;
                `\i. if i = k then 1 else if i = 0 then p - 1 else 0`]
    NUM_POLY_ROOTS) THEN
  ASM_REWRITE_TAC[DIVIDES_ONE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a = b ==> a <= k ==> b <= k:num`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `nsum(0..k) (\i. (if i = k then 1 else if i = 0 then p - 1 else 0) *
                    x EXP i) =
    nsum(0..k) (\i. (if i = k then x EXP k else 0) +
                    (if i = 0 then p - 1 else 0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~(k = 0)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ARITH_TAC];
      ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[NSUM_ADD_NUMSEG; NSUM_DELTA; IN_NUMSEG; LE_0; LE_REFL] THEN
  SUBGOAL_THEN `(p - 1) + 1 = p` MP_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_IMP_NZ) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`p - 1`,`B:num`) THEN GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC NUMBER_RULE);;

let POWER_RESIDUES_LOWER = prove
 (`!p k. prime p /\ 1 <= k
         ==> p - 1 <= k * CARD (IMAGE (\u. (u EXP k) MOD p) {u | 0 < u /\ u <
           p})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `U = {u | 0 < u /\ u < p}` THEN
  SUBGOAL_THEN `FINITE(U:num->bool) /\ CARD U = p - 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    SUBGOAL_THEN `{u | 0 < u /\ u < p} = 1..p-1` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG] THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `f = \u. (u EXP k) MOD p` THEN
  MP_TAC(ISPECL [`f:num->num`; `\u:num. 1`; `U:num->bool`;
                 `IMAGE (f:num->num) U`] NSUM_GROUP) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  ASM_SIMP_TAC[GSYM CARD_EQ_NSUM; FINITE_RESTRICT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum (IMAGE (f:num->num) U) (\y. k)` THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[NSUM_CONST; FINITE_IMAGE; LE_REFL] THEN ARITH_TAC] THEN
  MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `u0:num` THEN DISCH_TAC THEN
  ALL_TAC THEN
  SUBGOAL_THEN `0 < u0 /\ u0 < p` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u0:num) IN U` THEN EXPAND_TAC "U" THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`u0:num`; `1`; `p:num`] CONG_SOLVE) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[PRIME_COPRIME_LT];
    DISCH_THEN(X_CHOOSE_TAC `v0:num`)] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {x | x < p /\ (x EXP k == 1) (mod p)}` THEN
  ASM_SIMP_TAC[NUM_ROOTS_OF_UNITY_BOUND] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (\x. (x * v0) MOD p)
                     {x | x IN U /\ (f:num->num) x = f u0})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `p:num` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x * v0) MOD p = (y * v0) MOD p` THEN
    REWRITE_TAC[GSYM CONG] THEN
    UNDISCH_TAC `(u0 * v0 == 1) (mod p)` THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x | x < p:num}` THEN
    SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM]] THEN
  X_GEN_TAC `x:num` THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT_EQ] THEN
  MP_TAC(SPECL [`x * v0:num`; `p:num`] CONG_MOD) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
  UNDISCH_TAC `(u0 * v0 == 1) (mod p)` THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
  UNDISCH_TAC `x EXP k MOD p = u0 EXP k MOD p` THEN
  REWRITE_TAC[GSYM CONG; MULT_EXP; EXP_ONE] THEN
  SPEC_TAC(`((x * v0) MOD p) EXP k`,`Z:num`) THEN
  SPEC_TAC(`x EXP k`,`X:num`) THEN SPEC_TAC(`u0 EXP k`,`Y:num`) THEN
  SPEC_TAC(`v0 EXP k`,`W:num`) THEN CONV_TAC NUMBER_RULE);;

let WARING_LOC_MONO_SUC = prove
 (`!k L s c. 1 <= k /\ ~(L = 0) /\ &1 <= waring_loc k L s c
             ==> &1 <= waring_loc k L (SUC s) c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `L:num`; `s:num`; `c:num`; `0`]
           WARING_LOC_STEP_LOWER) THEN
  ASM_SIMP_TAC[EXP_ZERO; ARITH_RULE `1 <= k ==> ~(k = 0)`; MULT_CLAUSES;
               ADD_CLAUSES; ARITH_RULE `~(L = 0) ==> 0 < L`] THEN
  ASM_REAL_ARITH_TAC);;

let WARING_LOC_RESIDUE_SCALE = prove
 (`!k L s c u. coprime(u,L) /\ &1 <= waring_loc k L s c
               ==> &1 <= waring_loc k L s ((((u EXP k) MOD L) * c) MOD L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `waring_loc k L s ((((u EXP k) MOD L) * c) MOD L) =
                waring_loc k L s (u EXP k * c)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC WARING_LOC_CONG THEN
    MP_TAC(SPECL [`u EXP k`; `L:num`] CONG_MOD) THEN
    MP_TAC(SPECL [`((u EXP k) MOD L) * c`; `L:num`] CONG_MOD) THEN
    CONV_TAC NUMBER_RULE;
    ASM_SIMP_TAC[WARING_LOC_SCALE]]);;

let GROWTH_STEP = prove
 (`!p k j.
     prime p /\ 1 <= k
     ==> {c | c < p /\ &1 <= waring_loc k p j c} = {c | c < p} \/
         CARD {c | c < p /\ &1 <= waring_loc k p j c} +
         CARD (IMAGE (\u. (u EXP k) MOD p) {u | 0 < u /\ u < p}) <=
         CARD {c | c < p /\ &1 <= waring_loc k p (SUC j) c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC]
    THEN
  ABBREV_TAC `A = {c | c < p /\ &1 <= waring_loc k p j c}` THEN
  ABBREV_TAC `A' = {c | c < p /\ &1 <= waring_loc k p (SUC j) c}` THEN
  ABBREV_TAC `R = IMAGE (\u. (u EXP k) MOD p) {u | 0 < u /\ u < p}` THEN
  SUBGOAL_THEN `(A:num->bool) SUBSET A'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "A'"] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[WARING_LOC_MONO_SUC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c x. c IN A ==> (c + x EXP k) MOD p IN A'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "A'"] THEN
    SIMP_TAC[IN_ELIM_THM; MOD_LT_EQ] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `waring_loc k p (SUC j) ((c + x EXP k) MOD p) =
                  waring_loc k p (SUC j) (c + x EXP k)` SUBST1_TAC THENL
     [MATCH_MP_TAC WARING_LOC_CONG THEN REWRITE_TAC[CONG_MOD];
      MATCH_MP_TAC WARING_LOC_ADD_POWER THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 IN A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[WARING_LOC_ZERO_POS] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `A':num->bool = A` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `!m. m < p ==> (m:num) IN A` ASSUME_TAC THENL
       [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
        SUBGOAL_THEN `m + 1 < p` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `1`] o
          check (is_forall o concl)) THEN
        ASM_REWRITE_TAC[EXP_ONE; ADD1] THEN ASM_SIMP_TAC[MOD_LT];
        ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `m:num` THEN
      EQ_TAC THEN ASM_SIMP_TAC[] THEN MAP_EVERY EXPAND_TAC ["A"; "A'"] THEN
      SIMP_TAC[IN_ELIM_THM];
    DISJ2_TAC THEN
    SUBGOAL_THEN `?t:num. t IN A' /\ ~(t IN A)` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `t < p /\ &1 <= waring_loc k p (SUC j) t /\ ~(t = 0)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(t:num) IN A'` THEN EXPAND_TAC "A'" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `FINITE(A:num->bool) /\ FINITE(A':num->bool) /\
                    FINITE(R:num->bool)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["A"; "A'"; "R"] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{c | c < p:num}` THEN
          SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
          MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{c | c < p:num}` THEN
          SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
          MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `{c | c < p:num}` THEN
          SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM]];
        ALL_TAC] THEN
      ABBREV_TAC `T0 = IMAGE (\r. (t * r) MOD p) R` THEN
      SUBGOAL_THEN `CARD(T0:num->bool) = CARD(R:num->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "T0" THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`u:num`; `u':num`] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC)
         (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v':num` STRIP_ASSUME_TAC)
           ASSUME_TAC)) THEN
        SUBGOAL_THEN `u < p /\ u' < p:num` STRIP_ASSUME_TAC THENL
         [ASM_SIMP_TAC[MOD_LT_EQ]; ALL_TAC] THEN
        MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `p:num` THEN
        ASM_SIMP_TAC[MOD_LT_EQ] THEN
        MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `t:num` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC PRIME_COPRIME_LT THEN
          ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          UNDISCH_TAC `(t * u) MOD p = (t * u') MOD p` THEN
          REWRITE_TAC[GSYM CONG] THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
    SUBGOAL_THEN `!r. r IN R ==> (t * r) MOD p IN A' /\ ~((t * r) MOD p IN A)`
      ASSUME_TAC THENL
       [EXPAND_TAC "R" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `u:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `coprime(u:num,p)` ASSUME_TAC THENL
         [ASM_SIMP_TAC[PRIME_COPRIME_LT]; ALL_TAC] THEN
        CONJ_TAC THENL
         [EXPAND_TAC "A'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
          ASM_SIMP_TAC[MOD_LT_EQ] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
          MATCH_MP_TAC WARING_LOC_RESIDUE_SCALE THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(SPECL [`u:num`; `1`; `p:num`] CONG_SOLVE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:num`) THEN
        SUBGOAL_THEN `coprime(w:num,p)` ASSUME_TAC THENL
         [UNDISCH_TAC `(u * w == 1) (mod p)` THEN CONV_TAC NUMBER_RULE;
          ALL_TAC] THEN
        DISCH_TAC THEN UNDISCH_TAC `~((t:num) IN A)` THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `(t * u EXP k MOD p) MOD p IN A` THEN
        EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`k:num`; `p:num`; `j:num`; `(t * u EXP k MOD p) MOD p`;
                      `w:num`] WARING_LOC_RESIDUE_SCALE) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `a = b ==> &1 <= a ==> &1 <= b`) THEN
        MATCH_MP_TAC WARING_LOC_CONG THEN
        MP_TAC(SPECL [`w EXP k`; `p:num`] CONG_MOD) THEN
        MP_TAC(SPECL [`u EXP k`; `p:num`] CONG_MOD) THEN
        MP_TAC(SPECL [`t * u EXP k MOD p`; `p:num`] CONG_MOD) THEN
        MP_TAC(SPECL [`(w EXP k MOD p) * (t * u EXP k MOD p) MOD p`; `p:num`]
          CONG_MOD) THEN
        UNDISCH_TAC `(u * w == 1) (mod p)` THEN
        DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
        REWRITE_TAC[MULT_EXP; EXP_ONE] THEN
        SPEC_TAC(`u EXP k`,`U:num`) THEN SPEC_TAC(`w EXP k`,`W:num`) THEN
        CONV_TAC NUMBER_RULE;
        ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD((A:num->bool) UNION T0)` THEN
      SUBGOAL_THEN `FINITE(T0:num->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "T0" THEN ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`A:num->bool`; `T0:num->bool`] CARD_UNION) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
          X_GEN_TAC `y:num` THEN EXPAND_TAC "T0" THEN REWRITE_TAC[IN_IMAGE]
            THEN
          ASM_MESON_TAC[];
          ARITH_TAC];
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
        EXPAND_TAC "T0" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC[]]]);;

let GROWTH_LOWER = prove
 (`!p k j.
     prime p /\ 1 <= k
     ==> {c | c < p /\ &1 <= waring_loc k p j c} = {c | c < p} \/
         1 + j * CARD (IMAGE (\u. (u EXP k) MOD p) {u | 0 < u /\ u < p}) <=
         CARD {c | c < p /\ &1 <= waring_loc k p j c}`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
   [DISJ2_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    SUBGOAL_THEN `FINITE {c | c < p /\ &1 <= waring_loc k p 0 c}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{c | c < p:num}` THEN
      SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
      ASM_SIMP_TAC[CARD_EQ_0]] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `0` THEN
    ASM_SIMP_TAC[WARING_LOC_ZERO_POS; PRIME_IMP_NZ] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `~(p = 0) ==> 0 < p`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WARING_LOC_MONO_SUC THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
    UNDISCH_TAC `{c | c < p /\ &1 <= waring_loc k p j c} = {c | c < p}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MP_TAC(SPECL [`p:num`; `k:num`; `j:num`] GROWTH_STEP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
      SIMP_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `c:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WARING_LOC_MONO_SUC THEN
      ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
      UNDISCH_TAC `{c | c < p /\ &1 <= waring_loc k p j c} = {c | c < p}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      DISJ2_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC]]);;

let SOLUBLE_GROWTH = prove
 (`!p k s c. prime p /\ 1 <= k /\ k <= s ==> &1 <= waring_loc k p s c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. &1 <= waring_loc k p k c` ASSUME_TAC THENL
   [X_GEN_TAC `c0:num` THEN
    SUBGOAL_THEN `{c | c < p /\ &1 <= waring_loc k p k c} = {c | c < p}`
    MP_TAC THENL
     [MP_TAC(SPECL [`p:num`; `k:num`; `k:num`] GROWTH_LOWER) THEN
      MP_TAC(SPECL [`p:num`; `k:num`] POWER_RESIDUES_LOWER) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `A = {c | c < p /\ &1 <= waring_loc k p k c}` THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CARD_SUBSET_EQ THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "A" THEN SIMP_TAC[SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE `a <= p /\ p <= a ==> a = p:num`) THEN
      CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      EXPAND_TAC "A" THEN SIMP_TAC[SUBSET; IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `c0 MOD p`) THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> &1 <= a ==> &1 <= b`) THEN
    MATCH_MP_TAC WARING_LOC_CONG THEN REWRITE_TAC[CONG_MOD];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MATCH_MP_TAC WARING_LOC_MONO_SUC THEN ASM_REWRITE_TAC[]);;

let NUM_CUBE_EXPAND = prove
 (`!x. x EXP 3 = x * x * x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `3 = SUC 2`; EXP; EXP_2] THEN
  ARITH_TAC);;

let CUBE_LE_POW2_ODD = prove
 (`!k. 3 <= k ==> k EXP 3 <= 2 EXP (2 * k - 1)`,
  SUBGOAL_THEN `!m. (m + 3) EXP 3 <= 2 EXP (2 * m + 5)` ASSUME_TAC THENL
   [INDUCT_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `2 EXP (2 * SUC m + 5) = 4 * 2 EXP (2 * m + 5)`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * SUC m + 5 = SUC(SUC(2 * m + 5))`; EXP] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `4 * (m + 3) EXP 3` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NUM_CUBE_EXPAND; ADD1] THEN ARITH_TAC;
      ASM_ARITH_TAC];
    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC o
      REWRITE_RULE[LE_EXISTS]) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[ARITH_RULE `2 * (m + 3) - 1 = 2 * m + 5`] THEN
    ASM_REWRITE_TAC[]]);;

let CUBE_LE_POW2_EIGHT = prove
 (`!k. k EXP 3 <= 8 * 2 EXP k`,
  SUBGOAL_THEN `!m. (m + 4) EXP 3 <= 8 * 2 EXP (m + 4)` ASSUME_TAC THENL
   [INDUCT_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `2 EXP (SUC m + 4) = 2 * 2 EXP (m + 4)` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `SUC m + 4 = SUC(m + 4)`; EXP]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 * (m + 4) EXP 3` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NUM_CUBE_EXPAND; ADD1] THEN ARITH_TAC; ASM_ARITH_TAC];
    GEN_TAC THEN ASM_CASES_TAC `4 <= k` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
        REWRITE_RULE[LE_EXISTS]) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` MP_TAC THENL
       [ASM_ARITH_TAC;
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]]]);;

let DOUBLE_LE_POW2 = prove
 (`!t. 2 * t <= 2 EXP t`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; MULT_CLAUSES; LE_0] THEN
  ASM_CASES_TAC `t = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  MP_TAC(SPEC `t:num` LE_0) THEN
  SUBGOAL_THEN `1 <= 2 EXP t` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH];
    ASM_ARITH_TAC]);;

let SIGNED_COUNT = prove
 (`!L v s. 2 <= v /\ L <= v * (v DIV 2) /\ v <= s
           ==> (L - 1) DIV v + 1 + v DIV 2 <= s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(v = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(L - 1) DIV v < v DIV 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN
    SUBGOAL_THEN `1 <= v DIV 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(v * v DIV 2 = 0)` MP_TAC THENL
     [REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`v:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_ARITH_TAC);;

let POW2_HALF = prove
 (`!k. 1 <= k ==> 2 EXP k DIV 2 = 2 EXP (k - 1) /\
                  2 EXP k * 2 EXP (k - 1) = 2 EXP (2 * k - 1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
    SUBGOAL_THEN `k = SUC(k - 1)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EXP] THEN ARITH_TAC];
    REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let SOLUBLE_PRIMEPOW = prove
 (`!k S p c. 2 <= k /\ 2 EXP k + 1 <= S /\ prime p
             ==> &1 <= waring_loc k (p EXP (2 * index p k + 1)) (S - 1) c`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = index p k` THEN ABBREV_TAC `s = S - 1` THEN
  SUBGOAL_THEN `2 EXP k <= s /\ k <= s` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` LT_POW2_REFL) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= p:num` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `p EXP t divides k` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `p EXP t <= k` ASSUME_TAC THENL
   [MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [ASM_REWRITE_TAC[ARITH; EXP_1] THEN MATCH_MP_TAC SOLUBLE_GROWTH THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num) divides k` ASSUME_TAC THENL
   [MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `p EXP t` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVIDES_REXP THEN
    ASM_REWRITE_TAC[DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `p <= k:num` ASSUME_TAC THENL
   [MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ALL_TAC THEN
  SUBGOAL_THEN `p EXP (2 * t + 1) = p EXP t * p EXP t * p` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_ADD; EXP_1; MULT_2] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= p EXP t` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p <= p EXP (2 * t + 1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `p = 1 * 1 * p`] THEN
    REPEAT(MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]);
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k /\ 2 <= 2 EXP k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 * k` THEN
    REWRITE_TAC[DOUBLE_LE_POW2] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `ODD k` THENL
   [MATCH_MP_TAC SOLUBLE_SIGNED THEN EXISTS_TAC `2` THEN
    SUBGOAL_THEN `~(p = 2)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `ODD k` THEN
      REWRITE_TAC[GSYM NOT_EVEN; EVEN_EXISTS] THEN
      UNDISCH_TAC `2 divides k` THEN REWRITE_TAC[divides] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `3 <= p /\ 3 <= k` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `k = 2` THENL
       [UNDISCH_TAC `ODD k` THEN ASM_REWRITE_TAC[ARITH]; ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `p EXP (2 * t + 1) <= k EXP 3` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NUM_CUBE_EXPAND] THEN
      REPEAT(MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]);
      ALL_TAC] THEN
    MP_TAC(SPEC `k:num` CUBE_LE_POW2_ODD) THEN
    MP_TAC(SPEC `k:num` POW2_HALF) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
      MATCH_MP_TAC SIGNED_COUNT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 divides k` ASSUME_TAC THENL
   [ASM_MESON_TAC[EVEN_EXISTS; divides; NOT_ODD; MULT_SYM]; ALL_TAC] THEN
  ASM_CASES_TAC `p = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC SOLUBLE_TWO THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `2 <= 2 EXP t` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
      REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 * 2 * 2` THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]);
      ALL_TAC] THEN
    REWRITE_TAC[GSYM(ASSUME `2 EXP (2 * t + 1) = 2 EXP t * 2 EXP t * 2`)] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MP_TAC(SPEC `t:num` DOUBLE_LE_POW2) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SOLUBLE_ONES THEN ASM_REWRITE_TAC[EXP_EQ_0] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP t * p EXP t * p` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[MOD_LT_EQ; MULT_EQ_0; EXP_EQ_0]
     THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(2,p)` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * p EXP t <= k /\ 2 * p <= k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIVIDES_LE_IMP THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
    MATCH_MP_TAC(NUMBER_RULE
     `!a b n:num. a divides n /\ b divides n /\ coprime(a,b)
                  ==> a * b divides n`) THEN
    ASM_REWRITE_TAC[COPRIME_REXP];
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` CUBE_LE_POW2_EIGHT) THEN
  SUBGOAL_THEN `8 * (p EXP t * p EXP t * p) <= k EXP 3` MP_TAC THENL
   [REWRITE_TAC[NUM_CUBE_EXPAND] THEN
    REWRITE_TAC[ARITH_RULE `8 * (a * a * p) = (2 * a) * (2 * a) * (2 * p)`]
      THEN
    REPEAT(MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]);
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The singular series.                                                      *)
(* ------------------------------------------------------------------------- *)

let WARING_TERM_BOUND = prove
 (`!k s. 2 <= k /\ 2 EXP k + 1 <= s
         ==> ?Cw. &0 <= Cw /\
                 !N q. 1 <= q
                       ==> norm(waring_term k s N q) <=
                           Cw * &q rpow (--(&1 + inv(&(2 EXP k))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WARING_CSUM_ABS_DECAY) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Cw:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {a | a < q /\ coprime(a,q)}
                  (\a. norm(Cx(inv(&q)) * waring_csum k q a) pow s)` THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[waring_term] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; NORM_EXPI; REAL_MUL_RID;
              REAL_LE_REFL]);;

let WARING_TERM_1 = prove
 (`!k s N. waring_term k s N 1 = Cx(&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_term; waring_csum] THEN
  SUBGOAL_THEN `{a | a < 1 /\ coprime(a,1)} = {0} /\ {r | r < 1} = {0}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; COPRIME_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_SING; REAL_MUL_LZERO; real_div; REAL_MUL_RZERO;
              REAL_NEG_0; EXPI_0; REAL_INV_1; COMPLEX_MUL_LID;
              COMPLEX_POW_ONE; COMPLEX_MUL_RID]);;

let GEOM_SUM_LE = prove
 (`!x e. &0 <= x /\ x <= &1 / &2 ==> sum(1..e) (\j. x pow j) <= &2 * x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUM_GP] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_1] THEN
  SUBGOAL_THEN `&0 < &1 - x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]
    THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MP_TAC(SPECL [`x:real`; `SUC e`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x * x <= x * (&1 / &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let LOCAL_FACTOR_SUM = prove
 (`!k s c p e.
     1 <= s /\ prime p
     ==> Cx(waring_loc k (p EXP e) s c / &(p EXP e) pow (s - 1)) =
         Cx(&1) + vsum(1..e) (\j. waring_term k s c (p EXP j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ 2 <= p` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; PRIME_GE_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `s:num`; `p EXP e`; `c:num`] WARING_LOC_SING) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `{d | d divides p EXP e} = IMAGE (\j. p EXP j) (0..e)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0;
                 DIVIDES_PRIMEPOW] THEN MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[EQ_PRIMEPOW];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; EXP; WARING_TERM_1; ADD_CLAUSES]);;

let LOCAL_FACTOR_LARGE = prove
 (`!k s c p e Cw d.
     1 <= s /\ prime p /\ &0 <= Cw /\ &0 < d /\
     (!q. 1 <= q ==> norm(waring_term k s c q) <= Cw * &q rpow (--(&1 + d)))
     ==> &1 - &2 * Cw * &p rpow (--(&1 + d)) <=
         waring_loc k (p EXP e) s c / &(p EXP e) pow (s - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = &p rpow (--(&1 + d))` THEN
  SUBGOAL_THEN `&0 <= x /\ x <= &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; ASSUME `&0 < &p`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&p rpow (--(&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_MONO_LE THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[RPOW_NEG; RPOW_POW; REAL_POW_1; real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `s:num`; `c:num`; `p:num`; `e:num`]
    LOCAL_FACTOR_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
  REWRITE_TAC[RE_CX; RE_ADD] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs y <= &2 * Cw * x ==> &1 - &2 * Cw * x <= &1 +
    y`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vsum(1..e) (\j. waring_term k s c (p EXP j)))` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..e) (\j. Cw * x pow j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Cw * &(p EXP j) rpow (--(&1 + d))` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      EXPAND_TAC "x" THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_POW; RPOW_NUM_POW; REAL_LE_REFL]];
    REWRITE_TAC[SUM_LMUL] THEN
    MP_TAC(SPECL [`x:real`; `e:num`] GEOM_SUM_LE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `Cw * sum(1..e) (\j. x pow j) <= Cw * (&2 * x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]);;

let LOCAL_FACTOR_SMALL = prove
 (`!k S p c h.
     2 <= k /\ 2 EXP k + 1 <= S /\ prime p /\ 2 * index p k + 1 <= h
     ==> inv(&p pow ((2 * index p k + 1) * (S - 1))) <=
         waring_loc k (p EXP h) S c / &(p EXP h) pow (S - 1)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `g = 2 * index p k + 1` THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S - 1`; `p:num`; `g:num`; `h:num`; `c:num`]
    WARING_LOC_PRIMEPOW_LOWER) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN EXPAND_TAC "g" THEN
    MATCH_MP_TAC SOLUBLE_PRIMEPOW THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC(S - 1) = S` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &(p EXP h) pow (S - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`;
                    EXP_EQ_0];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
    `a <= b ==> c = a ==> c <= b`)) THEN
  SUBGOAL_THEN `p EXP h = p EXP (h - g) * p EXP g` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_POW_MUL;
              REAL_POW_POW] THEN
  SUBGOAL_THEN `~(&p pow (g * (S - 1)) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ] THEN ASM_REWRITE_TAC[];
    CONV_TAC REAL_FIELD]);;

let PRODUCT_ONE_MINUS = prove
 (`!(s:A->bool) x.
     FINITE s /\ (!i. i IN s ==> &0 <= x i /\ x i <= &1)
     ==> &1 - sum s x <= product s (\i. &1 - x i)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; REAL_LE_REFL; REAL_SUB_RZERO] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sum t (x:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - (x:A->real) a) * (&1 - sum t x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= u * v ==> &1 - (u + v) <= (&1 - u) * (&1 -
     v)`)
    THEN ASM_SIMP_TAC[REAL_LE_MUL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]);;

let RPOW_NEG_SMALL = prove
 (`!d e. &0 < d /\ &0 < e ==> ?N. 1 <= N /\ !n. N <= n ==> &n rpow (--d) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `inv(e) rpow (inv d)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv(e) rpow (inv d) /\ inv(e) rpow (inv d) <= &n`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT; REAL_LT_INV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv e <= &n rpow d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(inv(e) rpow (inv d)) rpow d` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE; REAL_LT_INV; REAL_MUL_LINV;
                   REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL];
      MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[RPOW_NEG] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV]);;

let FACT_POW_PRIMES = prove
 (`!Q h. 1 <= h
         ==> {p | prime p /\ p divides FACT Q EXP h} = {p | prime p /\ p <= Q}
           /\
             !p. prime p /\ p <= Q ==> h <= index p (FACT Q EXP h)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `prime p` THEN
    ASM_SIMP_TAC[PRIME_DIVEXP_EQ; DIVIDES_FACT_PRIME] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[INDEX_EXP] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `h = h * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; INDEX_EQ_0] THEN
    ASM_SIMP_TAC[DIVIDES_FACT_PRIME; FACT_NZ] THEN
    ASM_MESON_TAC[PRIME_1]]);;

let INDEX_LT_SELF = prove
 (`!p k. prime p /\ 1 <= k ==> index p k < k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP index p k` THEN REWRITE_TAC[LT_POW2_REFL] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP index p k` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_MESON_TAC[PRIME_GE_2];
    MATCH_MP_TAC DIVIDES_LE_IMP THEN
    REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; LE_REFL] THEN ASM_ARITH_TAC]);;

let WARING_SING_LOWER = prove
 (`!k S. 2 <= k /\ 2 EXP k + 1 <= S
         ==> ?c0 Q0. &0 < c0 /\
                     !N Q. Q0 <= Q ==> c0 <= Re(waring_sing k S N Q)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = inv(&(2 EXP k))` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S:num`] WARING_TERM_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cw:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d:real`; `d / (&4 * (Cw + &1))`] RPOW_NEG_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `P0:num` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `c1 = product {p | prime p /\ p <= P0}
                     (\p. inv(&p pow ((2 * index p k + 1) * (S - 1))))` THEN
  SUBGOAL_THEN `&0 < c1` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
    REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `~(p = 0) ==> 0 < p`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `c1 * d / (&4 * (Cw + &1))`] RPOW_NEG_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `Q1:num` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `c1 / &4` THEN EXISTS_TAC `P0 + Q1:num` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `Q:num`] THEN DISCH_TAC THEN
  ABBREV_TAC `L = FACT Q EXP (2 * k + 1)` THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[EXP_EQ_0; FACT_NZ]; ALL_TAC] THEN
  ABBREV_TAC `f = \n. waring_loc k n S N / &n pow (S - 1)` THEN
  SUBGOAL_THEN `real_multiplicative f` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[WDEN_MULTIPLICATIVE]; ALL_TAC] THEN
  MP_TAC(SPECL [`Q:num`; `2 * k + 1`] FACT_POW_PRIMES) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= 2 * k + 1`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `L:num`] REAL_MULTIPLICATIVE_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1 / &2 <= (f:num->real) L` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{p | prime p /\ p <= Q} =
      {p | prime p /\ p <= P0} UNION {p | prime p /\ P0 < p /\ p <= Q}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `x:num` THEN ASM_CASES_TAC `prime x` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `P0 + Q1 <= Q:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `FINITE {p | prime p /\ P0 < p /\ p <= Q}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | prime p /\ p <= Q}` THEN
      REWRITE_TAC[FINITE_ATMOST; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_UNION o rand o snd) THEN
    ASM_REWRITE_TAC[FINITE_ATMOST] THEN ANTS_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY]
      THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `c / &2 = c * &1 / &2`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXPAND_TAC "c1" THEN MATCH_MP_TAC PRODUCT_LE THEN
        REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
        X_GEN_TAC `p:num` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
          REWRITE_TAC[REAL_POS];
          ALL_TAC] THEN
        EXPAND_TAC "f" THEN BETA_TAC THEN MATCH_MP_TAC LOCAL_FACTOR_SMALL THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`p:num`; `k:num`] INDEX_LT_SELF) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o
          check (fun th -> is_forall(concl th) &&
                           can (find_term ((=) `index p L`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[ARITH_RULE `2 <= k ==> 1 <= k`] THEN ARITH_TAC;
      REAL_ARITH_TAC;
      ABBREV_TAC `B = {p | prime p /\ P0 < p /\ p <= Q}` THEN
        SUBGOAL_THEN `!p. p IN B ==> &0 <= &2 * Cw * &p rpow (--(&1 + d)) /\
                                     &2 * Cw * &p rpow (--(&1 + d)) <= &1`
        ASSUME_TAC THENL
         [EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
          X_GEN_TAC `p:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `&0 < &p /\ &1 <= &p` STRIP_ASSUME_TAC THENL
           [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
            ALL_TAC] THEN
          CONJ_TAC THENL
           [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
            ASM_SIMP_TAC[REAL_POS; RPOW_POS_LE; REAL_LT_IMP_LE];
            ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2 * Cw * d / (&4 * (Cw + &1))` THEN CONJ_TAC THENL
           [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&p rpow (--d)` THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
              FIRST_X_ASSUM(MATCH_MP_TAC o
                check (fun th -> can (find_term ((=) `d / (&4 * (Cw + &1))`))
                                 (concl th))) THEN
              ASM_ARITH_TAC];
            ALL_TAC] THEN
          SUBGOAL_THEN `d <= &1` ASSUME_TAC THENL
           [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
            REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                        EXP_EQ_0; ARITH_EQ];
            ALL_TAC] THEN
          SUBGOAL_THEN `&2 * Cw * d / (&4 * (Cw + &1)) = (Cw * d) / (&2 * (Cw +
            &1))`
          SUBST1_TAC THENL
           [UNDISCH_TAC `&0 <= Cw` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
                       REAL_ARITH `&0 <= Cw ==> &0 < &2 * (Cw + &1)`] THEN
          SUBGOAL_THEN `Cw * d <= Cw * &1` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
             ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
      SUBGOAL_THEN `FINITE(B:num->bool)` ASSUME_TAC THENL
         [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `product B (\p. &1 - &2 * Cw * &p rpow (--(&1 + d)))` THEN
        CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&1 - sum B (\p. &2 * Cw * &p rpow (--(&1 + d)))` THEN
          CONJ_TAC THENL
           [ALL_TAC;
            MATCH_MP_TAC PRODUCT_ONE_MINUS THEN ASM_SIMP_TAC[]] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= &1 / &2 ==> &1 / &2 <= &1 - x`) THEN
          REWRITE_TAC[SUM_LMUL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2 * Cw * (&P0 rpow (--d) / d)` THEN CONJ_TAC THENL
           [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
            MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC `sum(P0+1..Q) (\n. &n rpow (--(d + &1)))` THEN
            CONJ_TAC THENL
             [REWRITE_TAC[REAL_ARITH `--(&1 + d) = --(d + &1)`] THEN
              MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
              SIMP_TAC[FINITE_NUMSEG; RPOW_POS_LE; REAL_POS] THEN
              EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG]
                THEN
              ARITH_TAC;
              MATCH_MP_TAC SUM_RPOW_TAIL THEN ASM_REWRITE_TAC[]];
            ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2 * Cw * ((d / (&4 * (Cw + &1))) / d)` THEN CONJ_TAC
            THENL
           [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
            ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o
              check (fun th -> can (find_term ((=) `d / (&4 * (Cw + &1))`))
                               (concl th) && is_forall(concl th))) THEN
            ARITH_TAC;
            ALL_TAC] THEN
        SUBGOAL_THEN `&2 * Cw * ((d / (&4 * (Cw + &1))) / d) = Cw / (&2 * (Cw +
          &1))`
          SUBST1_TAC THENL
           [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 <= Cw` THEN
            CONV_TAC REAL_FIELD;
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
                         REAL_ARITH `&0 <= Cw ==> &0 < &2 * (Cw + &1)`] THEN
            ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o
            check (fun th -> can (find_term ((=) `B:num->bool`)) (concl th) &&
                             is_forall(concl th))) THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        EXPAND_TAC "f" THEN BETA_TAC THEN MATCH_MP_TAC LOCAL_FACTOR_LARGE THEN
        UNDISCH_TAC `(p:num) IN B` THEN EXPAND_TAC "B" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S:num`; `L:num`; `N:num`] WARING_LOC_SING) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `waring_loc k L S N / &L pow (S - 1) = (f:num->real) L`
  SUBST1_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `D = {m:num | m divides L /\ Q < m}` THEN
  SUBGOAL_THEN `FINITE(D:num->bool) /\ D SUBSET (Q+1..L)` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{m:num | m divides L}` THEN
      SIMP_TAC[FINITE_DIVISORS; ASSUME `~(L = 0)`] THEN
      SIMP_TAC[SUBSET; IN_ELIM_THM];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `{m:num | m divides L} = (1..Q) UNION D` SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM;
                                     IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(m = 0)` MP_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `0 divides (L:num)` THEN ASM_REWRITE_TAC[DIVIDES_ZERO];
        ARITH_TAC];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "L" THEN MATCH_MP_TAC DIVIDES_TRANS THEN
      EXISTS_TAC `FACT Q` THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIVIDES_FACT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC DIVIDES_REXP THEN REWRITE_TAC[DIVIDES_REFL] THEN
        ARITH_TAC]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_UNION o lhand o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [EXPAND_TAC "D" THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_NUMSEG;
                NOT_IN_EMPTY] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM waring_sing] THEN DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
  REWRITE_TAC[RE_ADD; RE_CX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(Re(vsum D (\d. waring_term k S N d))) <= c1 / &4`
  MP_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vsum D (\d. waring_term k S N d))` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum D (\q. Cw * &q rpow (--(&1 + d)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cw * (&Q rpow (--d) / d)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(Q+1..L) (\n. &n rpow (--(d + &1)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `--(&1 + d) = --(d + &1)`] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; RPOW_POS_LE; REAL_POS];
      MATCH_MP_TAC SUM_RPOW_TAIL THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cw * ((c1 * d / (&4 * (Cw + &1))) / d)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      check (fun th -> can (find_term ((=) `c1 * d / (&4 * (Cw + &1))`))
                       (concl th) && is_forall(concl th))) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cw * ((c1 * d / (&4 * (Cw + &1))) / d) =
                c1 / &4 * (Cw / (Cw + &1))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 <= Cw` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= Cw ==> &0 < Cw + &1`] THEN
  REAL_ARITH_TAC);;
