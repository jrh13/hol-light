(* ========================================================================= *)
(* Elementary estimates for sums over primes.                                *)
(*                                                                           *)
(* MERTENS_REAL extends the library's MERTENS (sum of log p / p) to real     *)
(* arguments, and MERTENS_RECIP is Mertens' second theorem with an explicit  *)
(* error term:                                                               *)
(*                                                                           *)
(*   sum_{p <= x} 1/p = log(log x) + M + E(x),   |E(x)| <= 50 / log x.       *)
(*                                                                           *)
(* It is obtained by partial summation (ABEL_SUMMATION_ASYMPTOTIC) against   *)
(* 1/log t, which bounds the variation of the error, and CAUCHY_RATE_LIMIT,  *)
(* which produces the constant M.                                            *)
(* ========================================================================= *)

needs "Sieve/sums.ml";;
needs "Sieve/nt.ml";;
needs "Examples/mangoldt.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Finite sets of primes and integers below a real bound.                    *)
(* ------------------------------------------------------------------------- *)

let FINITE_PRIMES_LE_REAL = prove
 (`!x. FINITE {p | prime p /\ &p <= x}`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_MESON_TAC[REAL_LE_TRANS]);;

let SUM_PRIMES_INTERVAL = prove
 (`!g x y.
        x <= y
        ==> sum {n | x < &n /\ &n <= y} (\n. if prime n then g n else &0) =
            sum {p | prime p /\ &p <= y} g - sum {p | prime p /\ &p <= x} g`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; FINITE_NUM_INTERVAL] THEN
  MATCH_MP_TAC(REAL_ARITH `a + b = c ==> a = c - b:real`) THEN
  W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o lhand o snd) THEN
  SIMP_TAC[FINITE_PRIMES_LE_REAL; FINITE_RESTRICT; FINITE_NUM_INTERVAL] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `p:num` THEN REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Mertens' first theorem for real arguments.                                *)
(* ------------------------------------------------------------------------- *)

let MERTENS_REAL = prove
 (`!x. &1 <= x
       ==> abs(sum {p | prime p /\ &p <= x} (\p. log(&p) / &p) - log x)
           <= &25`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `!r. integer r ==> (r <= x <=> r <= &n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN `{p | prime p /\ &p <= x} = {p | prime p /\ p <= n}`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; INTEGER_CLOSED; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_MESON_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  MP_TAC(SPEC `n:num` MERTENS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&n <= x /\ x < &n + &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&n) <= log x /\ log x - log(&n) <= &1` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `log x - log(&n) = log(&1 + (x - &n) / &n)` SUBST1_TAC THENL
     [SUBGOAL_THEN `&1 + (x - &n) / &n = x / &n` SUBST1_TAC THENL
       [UNDISCH_TAC `&1 <= &n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(x - &n) / &n` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= n ==> &0 < n`] THEN
      ASM_REAL_ARITH_TAC];
    ABBREV_TAC `S = sum {p | prime p /\ p <= n} (\p. log(&p) / &p)` THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Mertens' second theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let MERTENS_RECIP_VARIATION = prove
 (`!x y. &2 <= x /\ x <= y
         ==> abs((sum {p | prime p /\ &p <= y} (\p. inv(&p)) - log(log y)) -
                 (sum {p | prime p /\ &p <= x} (\p. inv(&p)) - log(log x)))
             <= &50 / log x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n. if prime n then log(&n) / &n else &0`;
    `\t. inv(log t)`; `\t. --(&1 * inv t) / log t pow 2`;
    `log`; `\t:real. inv t`; `&50`; `y:real`; `x:real`]
   ABEL_SUMMATION_ASYMPTOTIC) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < t /\ &0 < log t` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\t. inv(log t)) has_real_derivative f') (atreal t)`)) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      DISJ2_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_MUL_LID; real_div; REAL_MUL_LNEG; REAL_NEG_LE0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_INV THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID; IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[SUM_PRIMES_INTERVAL] THEN
      MP_TAC(SPEC `t:real` MERTENS_REAL) THEN
      MP_TAC(SPEC `x:real` MERTENS_REAL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      ABBREV_TAC `S1 = sum {p | prime p /\ &p <= x} (\p. log(&p) / &p)` THEN
      ABBREV_TAC `S2 = sum {p | prime p /\ &p <= t} (\p. log(&p) / &p)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log x /\ log x <= log y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {n | x < &n /\ &n <= y}
        (\n. (if prime n then log(&n) / &n else &0) * inv(log(&n))) =
    sum {p | prime p /\ &p <= y} (\p. inv(&p)) -
    sum {p | prime p /\ &p <= x} (\p. inv(&p))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_PRIMES_INTERVAL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    SUBGOAL_THEN `&0 < log(&n)` MP_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[x,y]) (\t. inv t * inv(log t)) =
    log(log y) - log(log x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    MP_TAC(ISPECL [`\t. log(log t)`; `\t. inv t * inv(log t)`;
                   `x:real`; `y:real`]
           REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < t /\ &0 < log t` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\t. log(log t)) has_real_derivative f') (atreal t)`)) THEN
    ASM_SIMP_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&50 * (abs(inv(log y)) + abs(inv(log y) - inv(log x))) = &50 / log x`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < inv(log y) /\ inv(log y) <= inv(log x)` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S1 = sum {p | prime p /\ &p <= x} (\p. inv(&p))` THEN
  ABBREV_TAC `S2 = sum {p | prime p /\ &p <= y} (\p. inv(&p))` THEN
  REAL_ARITH_TAC);;

let MERTENS_RECIP = prove
 (`?M. !x. &2 <= x
           ==> abs(sum {p | prime p /\ &p <= x} (\p. inv(&p)) -
                   log(log x) - M) <= &50 / log x`,
  MP_TAC(ISPECL
   [`\x. sum {p | prime p /\ &p <= x} (\p. inv(&p)) - log(log x)`;
    `\x. &50 / log x`; `&2`] CAUCHY_RATE_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MERTENS_RECIP_VARIATION THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `exp(&100 / e) + &2` THEN
    SUBGOAL_THEN `&0 < &100 / e` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `&100 / e` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `L = log(exp(&100 / e) + &2)` THEN
    SUBGOAL_THEN `&100 / e < L` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `e * (&100 / e) < e * L` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `e * (&100 / e) = &100` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Strict upper bounds p < x, as in the sieve products P(z).                 *)
(* ------------------------------------------------------------------------- *)

let FINITE_PRIMES_LT = prove
 (`!x. FINITE {p | prime p /\ &p < x}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p | prime p /\ &p <= x}` THEN
  REWRITE_TAC[FINITE_PRIMES_LE_REAL; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let SUM_PRIMES_LT_INTERVAL = prove
 (`!g u z.
        u <= z
        ==> sum {p | prime p /\ u <= &p /\ &p < z} g =
            sum {p | prime p /\ &p < z} g - sum {p | prime p /\ &p < u} g`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a + b = c ==> a = c - b:real`) THEN
  W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o lhand o snd) THEN
  SIMP_TAC[FINITE_PRIMES_LT; FINITE_RESTRICT] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ &p < z}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                  NOT_IN_EMPTY] THEN
      X_GEN_TAC `p:num` THEN REAL_ARITH_TAC];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let SUM_PRIMES_LE_LT = prove
 (`!x. &0 < x
       ==> &0 <= sum {p | prime p /\ &p <= x} (\p. inv(&p)) -
                 sum {p | prime p /\ &p < x} (\p. inv(&p)) /\
           sum {p | prime p /\ &p <= x} (\p. inv(&p)) -
           sum {p | prime p /\ &p < x} (\p. inv(&p)) <= inv x`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum {p | prime p /\ &p <= x} (\p. inv(&p)) -
    sum {p | prime p /\ &p < x} (\p. inv(&p)) =
    sum {p | prime p /\ &p = x} (\p. inv(&p))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a = b + c ==> a - b = c:real`) THEN
    W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o rand o snd) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[FINITE_PRIMES_LT];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{p | prime p /\ &p <= x}` THEN
        REWRITE_TAC[FINITE_PRIMES_LE_REAL; SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[REAL_LE_REFL];
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                    NOT_IN_EMPTY] THEN
        X_GEN_TAC `p:num` THEN REAL_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `?n. prime n /\ &n = x` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{p | prime p /\ &p = x} = {n}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
      ASM_MESON_TAC[REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUM_SING; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
    SUBGOAL_THEN `{p | prime p /\ &p = x} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES; REAL_LE_REFL; REAL_LE_INV; REAL_LT_IMP_LE]]);;

let MERTENS_RECIP_LT = prove
 (`?M. !x. &2 <= x
           ==> abs(sum {p | prime p /\ &p < x} (\p. inv(&p)) -
                   log(log x) - M) <= &51 / log x`,
  X_CHOOSE_TAC `M:real` MERTENS_RECIP THEN EXISTS_TAC `M:real` THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `x:real` SUM_PRIMES_LE_LT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log x /\ inv x <= inv(log x)` MP_TAC THENL
   [SUBGOAL_THEN `&0 < log x` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC LOG_LT_X THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ABBREV_TAC `S1 = sum {p | prime p /\ &p <= x} (\p. inv(&p))` THEN
  ABBREV_TAC `S2 = sum {p | prime p /\ &p < x} (\p. inv(&p))` THEN
  REAL_ARITH_TAC);;

let LOG_ONE_MINUS_BOUNDS = prove
 (`!y. &0 <= y /\ y <= inv(&2)
       ==> y <= --log(&1 - y) /\ --log(&1 - y) <= y + &2 * y pow 2`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPEC `--y:real` LOG_LE_STRONG) THEN
    REWRITE_TAC[GSYM real_sub] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--log(&1 - y) = log(&1 + y / (&1 - y))` SUBST1_TAC THENL
   [SUBGOAL_THEN `&1 + y / (&1 - y) = inv(&1 - y)` SUBST1_TAC THENL
     [UNDISCH_TAC `y <= inv(&2)` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC(GSYM LOG_INV) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y / (&1 - y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - y` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ]] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= y pow 2 * (&1 - &2 * y) ==> y <= (y + &2 * y pow 2) * (&1 - y)`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Mertens' product estimate, in logarithmic form.                           *)
(* ------------------------------------------------------------------------- *)

let SUM_PRIME_SQUARES_TAIL = prove
 (`!u z. &2 <= u
         ==> sum {p | prime p /\ u <= &p /\ &p < z} (\p. inv(&p pow 2))
             <= &3 / u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `u:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `&k <= u /\ u < &k + &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[REAL_LE_FLOOR; INTEGER_CLOSED];
    ALL_TAC] THEN
  MP_TAC(SPEC `max z (&k)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum ((k - 1) + 1..N) (\n. inv(&n pow 2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[FINITE_NUMSEG; REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= k ==> k - 1 + 1 = k`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k - 1`; `N:num`] SUM_INV_SQUARE_TAIL_NUMSEG) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `2 <= k ==> 1 <= k`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s a b c:real. &0 <= b /\ a <= c ==> s <= a - b ==> s <= c`) THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `2 <= k ==> 1 <= k`] THEN
  SUBGOAL_THEN `&3 / u = inv(u / &3)` SUBST1_TAC THENL
   [UNDISCH_TAC `&2 <= u` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  UNDISCH_TAC `2 <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_REAL_ARITH_TAC);;

let MERTENS_PRODUCT_LOG = prove
 (`?C. !u z. &2 <= u /\ u <= z
             ==> abs(sum {p | prime p /\ u <= &p /\ &p < z}
                         (\p. --log(&1 - inv(&p))) -
                     (log(log z) - log(log u))) <= C / log u`,
  X_CHOOSE_TAC `M:real` MERTENS_RECIP_LT THEN EXISTS_TAC `&108` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log u /\ log u <= log z /\ log u < u`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_LT_X THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ u <= &p /\ &p < z}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | prime p /\ &p < z}` THEN
    REWRITE_TAC[FINITE_PRIMES_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN {p | prime p /\ u <= &p /\ &p < z}
        ==> &0 <= inv(&p) /\ inv(&p) <= inv(&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; ARITH] THEN
    ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {p | prime p /\ u <= &p /\ &p < z} (\p. --log(&1 - inv(&p))) =
    sum {p | prime p /\ u <= &p /\ &p < z} (\p. inv(&p)) +
    sum {p | prime p /\ u <= &p /\ &p < z}
        (\p. --log(&1 - inv(&p)) - inv(&p))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN
    REWRITE_TAC[REAL_ARITH `a + (b - a) = b:real`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum {p | prime p /\ u <= &p /\ &p < z}
             (\p. --log(&1 - inv(&p)) - inv(&p)) /\
    sum {p | prime p /\ u <= &p /\ &p < z}
        (\p. --log(&1 - inv(&p)) - inv(&p)) <= &6 / u`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `inv(&p)` LOG_ONE_MINUS_BOUNDS) THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {p | prime p /\ u <= &p /\ &p < z}
                    (\p. &2 * inv(&p pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `inv(&p)` LOG_ONE_MINUS_BOUNDS) THEN
      ASM_SIMP_TAC[REAL_POW_INV] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_LMUL] THEN
      MP_TAC(SPECL [`u:real`; `z:real`] SUM_PRIME_SQUARES_TAIL) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
      ABBREV_TAC `Q = sum {p | prime p /\ u <= &p /\ &p < z}
                          (\p. inv(&p pow 2))` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ISPEC `\p:num. inv(&p)` SUM_PRIMES_LT_INTERVAL] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `u:real` th) THEN MP_TAC(SPEC `z:real` th)) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(log z) <= inv(log u) /\ inv u <= inv(log u)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `sum {p | prime p /\ u <= &p /\ &p < z}
        (\p. --log(&1 - inv(&p)) - inv(&p)) <= &6 / u` THEN
  UNDISCH_TAC
   `&0 <= sum {p | prime p /\ u <= &p /\ &p < z}
              (\p. --log(&1 - inv(&p)) - inv(&p))` THEN
  REWRITE_TAC[real_div] THEN
  ABBREV_TAC `R = sum {p | prime p /\ u <= &p /\ &p < z}
                      (\p. --log(&1 - inv(&p)) - inv(&p))` THEN
  ABBREV_TAC `Su = sum {p | prime p /\ &p < u} (\p. inv(&p))` THEN
  ABBREV_TAC `Sz = sum {p | prime p /\ &p < z} (\p. inv(&p))` THEN
  REAL_ARITH_TAC);;
