(* ========================================================================= *)
(* Siegel lemma, over the integers and for algebraic coefficients.           *)
(*                                                                           *)
(* Purpose: Siegel lemma (Dirichlet box principle; Baker, Transcendental     *)
(* Number Theory, Ch. 2, Lemma 1): M linear equations in N unknowns with     *)
(* integer coefficients bounded by U have a nonzero integer solution bounded *)
(* by B as soon as (N U)^M < (B + 1)^(N - M), in particular with B = N U     *)
(* when N >= 2 M. Then the reduction of (a_d theta)^e, and of an intpoly in  *)
(* roots theta r of integer polynomials, to integer combinations of the      *)
(* monomials prod_r theta r^(s r) with s r < d r, and the Siegel lemma for   *)
(* linear equations whose coefficients are such expressions (used for Baker  *)
(* Lemma 4).                                                                 *)
(*                                                                           *)
(* Main results: SIEGEL_LEMMA, SIEGEL_LEMMA_HALF (the case N >= 2 M),        *)
(*   ALGEBRAIC_SIEGEL (algebraic coefficients), POWER_REDUCTION,             *)
(*   INTPOLY_REDUCE.                                                         *)
(*                                                                           *)
(* Uses: Baker/lemmas.ml (PIGEONHOLE_CARD_LT), Baker/algebraic.ml            *)
(*   (COMPLEX_POLYFUN_MUL_LINEAR), Baker/intpoly.ml (intpoly, cartesian      *)
(*   products).                                                              *)
(* ========================================================================= *)

needs "Baker/intpoly.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Siegel lemma: M integer linear equations in N unknowns with coefficients  *)
(* bounded by U have a nonzero integer solution bounded by B as soon as      *)
(* (N U)^M < (B + 1)^(N - M).                                                *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let SIEGEL_TERM_LEMMA = prove
 (`!c x b u:real.
        abs c <= u /\ &0 <= x /\ x <= b
        ==> &0 <= c * x + max (&0) (--c) * b /\
            c * x + max (&0) (--c) * b <= u * b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 <= c` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> max (&0) (--c) = &0`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN
    TRANS_TAC REAL_LE_TRANS `c * b` THEN ASM_SIMP_TAC[REAL_LE_LMUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= c) ==> max (&0) (--c) = --c`] THEN
    REWRITE_TAC[REAL_ARITH `c * x + --c * b = --c * (b - x)`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `--c * b` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]]);;

prioritize_num();;

let SIEGEL_LEMMA = prove
 (`!(u:E->J->real) eqs unk U B.
        FINITE eqs /\ FINITE unk /\ ~(unk = {}) /\ &1 <= U /\
        (!i j. i IN eqs /\ j IN unk ==> integer(u i j) /\ abs(u i j) <= U) /\
        (&(CARD unk) * U) pow (CARD eqs) < (&B + &1) pow (CARD unk - CARD eqs)
        ==> ?x. (!j. j IN unk ==> integer(x j) /\ abs(x j) <= &B) /\
                ~(!j. j IN unk ==> x j = &0) /\
                (!i. i IN eqs ==> sum unk (\j. u i j * x j) = &0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `N = CARD(unk:J->bool)` THEN ABBREV_TAC `M =
    CARD(eqs:E->bool)` THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN
    ASM_SIMP_TAC[CARD_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N * U * &B` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `m:num` o MATCH_MP FLOOR_POS)] THEN
  ABBREV_TAC
   `V = \i:E. sum unk (\j:J. max (&0) (--((u:E->J->real) i j)))` THEN
  ABBREV_TAC
   `ev = \(x:J->num) (i:E).
       if i IN eqs then sum unk (\j:J. (u:E->J->real) i j * &(x j)) + V i * &B
       else &0` THEN
  SUBGOAL_THEN
   `{x:J->num | (!j. j IN unk ==> x j IN 0..B) /\
                (!j. ~(j IN unk) ==> x j = 0)} HAS_SIZE (B + 1) EXP N`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC[HAS_SIZE] THEN
    REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{y:E->real | (!i. i IN eqs ==> y i IN IMAGE (\n. &n) (0..m)) /\
                 (!i. ~(i IN eqs) ==> y i = &0)} HAS_SIZE (m + 1) EXP M`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC[HAS_SIZE] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_OF_NUM_EQ; CARD_NUMSEG] THEN
    ANTS_TAC THENL [MESON_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `M <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `(&N * U) pow M < (&B + &1) pow (N - M)` THEN
    ASM_SIMP_TAC[ARITH_RULE `N < M ==> N - M = 0`; real_pow; REAL_NOT_LT] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&m <= &N * U * &B /\ &N * U * &B < &m + &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&N * U * &B` FLOOR) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(m + 1) EXP M < (B + 1) EXP N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_POW;
                GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&1 <= &N * U` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE];
      ALL_TAC] THEN
    TRANS_TAC REAL_LET_TRANS `(&N * U * (&B + &1)) pow M` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_ASSOC; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&N * U * (&B + &1)) pow M = (&N * U) pow M * (&B + &1) pow M`
    SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_ASSOC; REAL_POW_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&B + &1) pow N = (&B + &1) pow (N - M) * (&B + &1) pow M`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN {x:J->num | (!j. j IN unk ==> x j IN 0..B) /\
                        (!j. ~(j IN unk) ==> x j = 0)}
        ==> ev x IN
            {y:E->real | (!i. i IN eqs ==> y i IN IMAGE (\n. &n) (0..m)) /\
                         (!i. ~(i IN eqs) ==> y i = &0)}`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:J->num` THEN REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    STRIP_TAC THEN EXPAND_TAC "ev" THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    X_GEN_TAC `i:E` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "V" THEN ASM_SIMP_TAC[GSYM SUM_RMUL; GSYM SUM_ADD] THEN
    SUBGOAL_THEN
     `!j. j IN unk
          ==> &0 <= (u:E->J->real) i j * &(x j) + max (&0) (--u i j) * &B /\
              u i j * &(x j) + max (&0) (--u i j) * &B <= U * &B`
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIEGEL_TERM_LEMMA THEN
      ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `integer(sum unk (\j. (u:E->J->real) i j * &(x j) +
                           max (&0) (--u i j) * &B))`
    MP_TAC THENL
     [MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `j:J` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC(el 1 (CONJUNCTS INTEGER_CLOSED)) THEN
      CONJ_TAC THEN MATCH_MP_TAC(el 3 (CONJUNCTS INTEGER_CLOSED)) THEN
      REWRITE_TAC[INTEGER_CLOSED] THEN
      TRY(MATCH_MP_TAC(el 7 (CONJUNCTS INTEGER_CLOSED))) THEN
      ASM_MESON_TAC[INTEGER_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= sum unk (\j. (u:E->J->real) i j * &(x j) +
                         max (&0) (--u i j) * &B) /\
      sum unk (\j. (u:E->J->real) i j * &(x j) + max (&0) (--u i j) * &B)
      <= &N * U * &B`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[];
        TRANS_TAC REAL_LE_TRANS `sum (unk:J->bool) (\j. U * &B)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[];
          ASM_SIMP_TAC[SUM_CONST] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGER_POS] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN EXISTS_TAC `k:num` THEN
    REWRITE_TAC[ARITH_RULE `k <= m <=> k < m + 1`; GSYM REAL_OF_NUM_LT;
                GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ev:(J->num)->E->real`;
    `{x:J->num | (!j. j IN unk ==> x j IN 0..B) /\
                 (!j. ~(j IN unk) ==> x j = 0)}`;
    `{y:E->real | (!i. i IN eqs ==> y i IN IMAGE (\n. &n) (0..m)) /\
                  (!i. ~(i IN eqs) ==> y i = &0)}`]
   PIGEONHOLE_CARD_LT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; LE_0; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:J->num`; `y:J->num`] THEN STRIP_TAC THEN
  EXISTS_TAC `\j:J. &(x j) - &((y:J->num) j)` THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:J` THEN DISCH_TAC THEN SIMP_TAC[INTEGER_CLOSED] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ a <= b /\ &0 <= c /\ c <= b ==> abs(a - c) <= b`) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE];
    DISCH_TAC THEN UNDISCH_TAC `~(x:J->num = y)` THEN
      REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `j:J` THEN ASM_CASES_TAC `(j:J) IN unk` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:J`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ];
      ASM_MESON_TAC[]];
    X_GEN_TAC `i:E` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `i:E`) THEN EXPAND_TAC "ev" THEN
    ASM_SIMP_TAC[REAL_SUB_LDISTRIB; SUM_SUB] THEN REAL_ARITH_TAC]);;

let SIEGEL_LEMMA_HALF = prove
 (`!(u:E->J->real) eqs unk U.
        FINITE eqs /\ FINITE unk /\ ~(unk = {}) /\ &1 <= U /\
        (!i j. i IN eqs /\ j IN unk ==> integer(u i j) /\ abs(u i j) <= U) /\
        2 * CARD eqs <= CARD unk
        ==> ?x. (!j. j IN unk ==> integer(x j) /\
                                  abs(x j) <= &(CARD unk) * U) /\
                ~(!j. j IN unk ==> x j = &0) /\
                (!i. i IN eqs ==> sum unk (\j. u i j * x j) = &0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `N = CARD(unk:J->bool)` THEN ABBREV_TAC `M =
    CARD(eqs:E->bool)` THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN
    ASM_SIMP_TAC[CARD_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &N * U` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N * U` MP_TAC THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `B:num` o MATCH_MP FLOOR_POS)] THEN
  MP_TAC(SPEC `&N * U` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:E->J->real`; `eqs:E->bool`; `unk:J->bool`; `U:real`;
                 `B:num`]
    SIEGEL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [TRANS_TAC REAL_LET_TRANS `(&N * U) pow (N - M)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(a ==> a') ==> a /\ b /\ c ==> a' /\ b /\ c`) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Reduction of powers: (a_d theta)^e is an integer combination of the       *)
(* powers theta^s, s < d, with coefficients bounded by (2h)^e.               *)
(* ------------------------------------------------------------------------- *)

let POWER_REDUCTION = prove
 (`!(a:num->real) d h theta.
        1 <= d /\ (!j. integer(a j) /\ abs(a j) <= h) /\ ~(a d = &0) /\
        vsum(0..d) (\j. Cx(a j) * theta pow j) = Cx(&0)
        ==> !e. ?K. (!s. integer(K s) /\ abs(K s) <= (&2 * h) pow e) /\
                    (Cx(a d) * theta) pow e =
                    vsum(0..d-1) (\s. Cx(K s) * theta pow s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= h` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx((a:num->real) d) * theta pow d =
    --vsum(0..d-1) (\j. Cx(a j) * theta pow j)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `vsum (0..d) (\j. Cx ((a:num->real) j) * theta pow j) =
     Cx (&0)` THEN
    SUBGOAL_THEN `0 < d /\ 0 <= d`
     (fun th -> REWRITE_TAC[MATCH_MP VSUM_CLAUSES_RIGHT th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [EXISTS_TAC `\s:num. if s = 0 then &1 else &0` THEN
    REWRITE_TAC[complex_pow; real_pow] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED] THEN
      REAL_ARITH_TAC;
      SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; complex_pow; COMPLEX_MUL_RID] THEN
      MATCH_MP_TAC(COMPLEX_RING `y = Cx(&0) ==> Cx(&1) = Cx(&1) + y`) THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
      SIMP_TAC[IN_NUMSEG; ARITH_RULE `0 + 1 <= s ==> ~(s = 0)`;
               COMPLEX_VEC_0; COMPLEX_MUL_LZERO]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `K:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `\s. (if s = 0 then &0 else (a:num->real) d * K(s - 1)) - K(d - 1) *
     a s` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED];
      REWRITE_TAC[real_pow] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs x <= h * p /\ abs y <= p * h ==> abs(x - y) <= (&2 * h) * p`) THEN
      CONJ_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NUM] THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
          TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
          ASM_SIMP_TAC[REAL_ABS_POS]];
        REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[REAL_ABS_POS]]];
    ALL_TAC] THEN
  REWRITE_TAC[complex_pow] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d - 1`; `\s. Cx((K:num->real) s)`; `Cx(&0)`; `theta:complex`]
    COMPLEX_POLYFUN_MUL_LINEAR) THEN
  REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_LZERO] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= d ==> SUC(d - 1) = d`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `(p * t) * v:complex = p * (t * v)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `0 < d /\ 0 <= d`
   (fun th -> REWRITE_TAC[MATCH_MP VSUM_CLAUSES_RIGHT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(d = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_ADD_LDISTRIB] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `p * q * w:complex = q * (p * w)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vsum (0..d - 1)
     (\s. Cx ((if s = 0 then &0 else (a:num->real) d * K (s - 1)) -
              K (d - 1) * a s) * theta pow s) =
    Cx(a d) * vsum (0..d - 1)
               (\s. (if s = 0 then Cx (&0) else Cx (K (s - 1))) * theta pow s) -
    Cx(K(d - 1)) * vsum (0..d - 1) (\j. Cx (a j) * theta pow j)`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG; GSYM VSUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[CX_SUB; CX_MUL] THEN CONV_TAC COMPLEX_RING;
    CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* An integer polynomial expression in roots theta r of integer polynomials, *)
(* multiplied by prod_r (leading coefficient)^(n r), is an integer           *)
(* combination of the monomials prod_r theta r^(s r) with s r < d r.         *)
(* ------------------------------------------------------------------------- *)

let INTPOLY_REDUCE = prove
 (`!v n b (g:(num->complex)->complex) (theta:num->complex)
    (a:num->num->real) d h.
     FINITE v /\ intpoly v n b g /\
     (!r. r IN v ==> 1 <= d r /\ (!j. integer(a r j) /\ abs(a r j) <= h r) /\
                     ~(a r (d r) = &0) /\
                     vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0))
     ==> ?K. (!s. integer(K s) /\
                  abs(K s) <= b * product v (\r. (&2 * h r) pow n r)) /\
             Cx(product v (\r. a r (d r) pow n r)) * g theta =
             vsum (cartesian_product v (\r. 0..d r - 1))
                  (\s. Cx(K s) * cproduct v (\r. theta r pow s r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[intpoly] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?R. !r e. r IN v
              ==> (!s. integer(R r e s) /\ abs(R r e s) <= (&2 * h r) pow e) /\
                  (Cx((a:num->num->real) r (d r)) * (theta:num->complex) r)
                  pow e =
                  vsum(0..d r - 1) (\s. Cx(R r e s) * theta r pow s)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `e:num`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`(a:num->num->real) r`; `(d:num->num) r`; `(h:num->real) r`;
                   `(theta:num->complex) r`] POWER_REDUCTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:num`) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `\sg:num->num. sum s (\k. (c:num->real) k *
      product v (\r. (a:num->num->real) r (d r) pow
                       (n r - (e:num->num->num) k r) *
                     (R:num->num->num->real) r (e k r) (sg r)))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `sg:num->num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC(el 3 (CONJUNCTS INTEGER_CLOSED)) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC INTEGER_PRODUCT THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC(el 3 (CONJUNCTS INTEGER_CLOSED)) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(el 4 (CONJUNCTS INTEGER_CLOSED)) THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum s (\k. abs((c:num->real) k) *
                 product v (\r. (&2 * (h:num->real) r) pow n r))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[GSYM PRODUCT_ABS] THEN MATCH_MP_TAC PRODUCT_LE THEN
      ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(&2 * (h:num->real) r) pow n r =
        (&2 * h r) pow (n r - (e:num->num->num) k r) * (&2 * h r) pow e k r`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC(GSYM SUB_ADD) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `r:num` th) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
        ASM_MESON_TAC[REAL_ARITH `abs x <= h ==> abs x <= &2 * h`];
        ASM_MESON_TAC[]];
      ASM_SIMP_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_POW_LE THEN
      SUBGOAL_THEN `&0 <= (h:num->real) x` MP_TAC THENL
       [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(cartesian_product v (\r:num. 0..(d:num->num) r - 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
  REWRITE_TAC[GSYM VSUM_CX] THEN ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[VSUM_COMPLEX_LMUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `p * q * w:complex = q * p * w`] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[CX_PRODUCT; CX_MUL; CX_POW; GSYM CPRODUCT_MUL] THEN
  MP_TAC(ISPECL [`v:num->bool`; `\r:num. 0..(d:num->num) r - 1`;
   `\x i. (Cx((a:num->num->real) x (d x)) pow
             (n x - (e:num->num->num) k x) *
           Cx((R:num->num->num->real) x (e k x) i)) *
          (theta:num->complex) x pow i`]
   VSUM_CPRODUCT_CARTESIAN_PRODUCT) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SIMP_TAC[GSYM COMPLEX_MUL_ASSOC; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `(e:num->num->num) k r`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_MUL_ASSOC; GSYM COMPLEX_POW_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(GSYM SUB_ADD) THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Siegel lemma for linear equations whose coefficients are integer          *)
(* polynomial expressions in algebraic numbers theta r.                      *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_SIEGEL = prove
 (`!v n b (g:E->J->(num->complex)->complex) eqs unk
    (theta:num->complex) (a:num->num->real) d h.
     FINITE v /\ FINITE eqs /\ FINITE unk /\ ~(unk = {}) /\
     (!r. r IN v ==> 1 <= d r /\ (!j. integer(a r j) /\ abs(a r j) <= h r) /\
                     ~(a r (d r) = &0) /\
                     vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
     (!i j. i IN eqs /\ j IN unk ==> intpoly v n b (g i j)) /\
     2 * nproduct v d * CARD eqs <= CARD unk
     ==> ?x. (!j. j IN unk
                  ==> integer(x j) /\
                      abs(x j) <= &(CARD unk) *
                                  max (&1) (b * product v (\r. (&2 *
                                    h r) pow n r))) /\
             ~(!j. j IN unk ==> x j = &0) /\
             (!i. i IN eqs ==> vsum unk (\j. Cx(x j) * g i j theta) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?K. !i j. i IN eqs /\ j IN unk
              ==> (!s. integer(K i j s) /\
                       abs(K i j s) <=
                       b * product (v:num->bool)
                             (\r. (&2 * (h:num->real) r) pow (n:num->num) r)) /\
                  Cx(product v (\r. (a:num->num->real) r (d r) pow n r)) *
                  (g:E->J->(num->complex)->complex) i j theta =
                  vsum (cartesian_product v (\r. 0..d r - 1))
                       (\s. Cx(K i j s) * cproduct v (\r. theta r pow s r))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTPOLY_REDUCE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `box = cartesian_product v (\r:num. 0..(d:num->num) r - 1)` THEN
  SUBGOAL_THEN `FINITE(box:(num->num)->bool) /\ CARD box =
    nproduct (v:num->bool) (d:num->num)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "box" THEN
    ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; CARD_CARTESIAN_PRODUCT;
                 FINITE_NUMSEG; CARD_NUMSEG] THEN
    MATCH_MP_TAC NPRODUCT_EQ THEN ASM_SIMP_TAC[ARITH_RULE
     `1 <= d ==> (d - 1 + 1) - 0 = d`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:E#(num->num) j:J. (K:E->J->(num->num)->real) (FST p) j (SND p)`;
    `(eqs:E->bool) CROSS (box:(num->num)->bool)`; `unk:J->bool`;
    `max (&1) (b * product v (\r. (&2 * (h:num->real) r) pow n r))`]
   SIEGEL_LEMMA_HALF) THEN
  ASM_SIMP_TAC[FINITE_CROSS; CARD_CROSS; FORALL_PAIR_THM; IN_CROSS] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max (&1) b`) THEN
      ASM_SIMP_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:J->real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:E` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(Cx(product v (\r. (a:num->num->real) r (d r) pow n r)) =
    Cx(&0))`
  MP_TAC THENL
   [ASM_SIMP_TAC[CX_INJ; PRODUCT_EQ_0; REAL_POW_EQ_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(COMPLEX_RING `p * s = Cx(&0) ==> ~(p = Cx(&0)) ==> s =
    Cx(&0)`) THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `p * q * w:complex = q * p * w`] THEN
  TRANS_TAC EQ_TRANS
   `vsum unk (\j:J. Cx(x j) *
       vsum box (\s. Cx((K:E->J->(num->num)->real) i j s) *
                     cproduct v (\r. (theta:num->complex) r pow s r)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  X_GEN_TAC `s:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN ASM_SIMP_TAC[VSUM_COMPLEX_RMUL] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE] THEN DISJ1_TAC THEN
  REWRITE_TAC[GSYM CX_MUL; VSUM_CX; CX_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:E`; `s:num->num`]) THEN
  ASM_REWRITE_TAC[REAL_MUL_SYM]);;
