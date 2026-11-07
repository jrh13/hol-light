(* ========================================================================= *)
(* Tools for the Schinzel-Tijdeman theorem: the logarithm of a monic         *)
(* polynomial.                                                               *)
(*                                                                           *)
(* Purpose: a monic real polynomial g of degree n satisfies, for large       *)
(* abs X, g(X) non-zero and abs(log abs g(X) - n log abs X) <=               *)
(* C / abs X (POLY_MONIC_LOG_ASYMPTOTIC), with the elementary bounds for     *)
(* logarithms near 1 and for the tail of a monic polynomial; used through    *)
(* SCHINZEL_TIJDEMAN_MULT_F_BOUND (Baker/schinzel_mult.ml) by the            *)
(* Schinzel-Tijdeman theorem (Baker/schinzel_general.ml).                    *)
(*                                                                           *)
(* Main results: POLY_MONIC_LOG_ASYMPTOTIC; helper names POLY_*.             *)
(*                                                                           *)
(* Uses: Multivariate/transcendentals.ml (LOG_DIV, LOG_INV, LOG_LE_STRONG,   *)
(* LOG_POW).                                                                 *)
(* ========================================================================= *)

needs "Multivariate/transcendentals.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Logarithms near 1.                                                        *)
(* ------------------------------------------------------------------------- *)

let POLY_LOG_ABS_LE = prove
 (`!u d. &0 < u /\ abs(u - &1) <= d /\ d <= &1 / &2
         ==> abs(log u) <= &2 * d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(u:real) - &1` LOG_LE_STRONG) THEN
  REWRITE_TAC[REAL_ARITH `&1 + ((u:real) - &1) = u`] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `inv(u:real) - &1` LOG_LE_STRONG) THEN
  REWRITE_TAC[REAL_ARITH `&1 + ((x:real) - &1) = x`] THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; LOG_INV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (d:real) * ((u:real) - &1 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    UNDISCH_TAC `abs((u:real) - &1) <= d` THEN
    UNDISCH_TAC `(d:real) <= &1 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(u:real) - &1 <= &2 * d` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(u:real) - &1 = (&1 - u) / u` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (u:real)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `&0 <= (d:real) * ((u:real) - &1 / &2)` THEN
    UNDISCH_TAC `abs((u:real) - &1) <= d` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `inv(u:real) - &1 <= &2 * d` THEN
  UNDISCH_TAC `--log(u:real) <= inv u - &1` THEN
  UNDISCH_TAC `log(u:real) <= u - &1` THEN
  UNDISCH_TAC `abs((u:real) - &1) <= d` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The real core of the asymptotic: abs g within s p of a p, a >= 2 s + 1.   *)
(* ------------------------------------------------------------------------- *)

let POLY_LOG_CORE = prove
 (`!g a p s. &1 <= a /\ &0 < p /\ &0 <= s /\ &2 * s + &1 <= a /\
             abs(abs g - a * p) <= s * p
             ==> &0 < abs g /\
                 abs(log(abs g) - log(a * p)) <= (&2 * s) / a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (a:real) * p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    UNDISCH_TAC `&1 <= (a:real)` THEN UNDISCH_TAC `&0 < (p:real)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * ((s:real) * p) <= a * p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    UNDISCH_TAC `&2 * (s:real) + &1 <= a` THEN UNDISCH_TAC `&0 < (p:real)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(g:real)` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 * ((s:real) * p) <= a * p` THEN
    UNDISCH_TAC `&0 < (a:real) * p` THEN
    UNDISCH_TAC `abs(abs(g:real) - a * p) <= s * p` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_DIV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (s:real) / a` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_LE_REFL]] THEN
  SUBGOAL_THEN `&0 < (a:real)` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 <= (a:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC POLY_LOG_ABS_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `abs(g:real) / (a * p) - &1 = (abs g - a * p) / (a * p)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (a:real) * p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIV] THEN
    SUBGOAL_THEN `abs((a:real) * p) = a * p` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (a:real) * p` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `(s:real) / a * (a * p) = s * p` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (a:real)` THEN CONV_TAC REAL_FIELD;
      FIRST_ASSUM ACCEPT_TAC];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `&2 * (s:real) + &1 <= a` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Monic polynomials: split off the leading term, bound the tail.            *)
(* ------------------------------------------------------------------------- *)

let POLY_MONIC_SPLIT = prove
 (`!n (c:num->real) x.
     1 <= n /\ c n = &1
     ==> sum(0..n) (\i. c i * x pow i) =
         x pow n + sum(0..n-1) (\i. c i * x pow i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < n /\ 0 <= n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; REAL_MUL_LID] THEN REAL_ARITH_TAC);;

let POLY_TAIL_BOUND = prove
 (`!m (c:num->real) x.
     &1 <= abs x
     ==> abs(sum(0..m) (\i. c i * x pow i)) <=
         sum(0..m) (\i. abs(c i)) * abs x pow m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..m) (\i. abs((c:num->real) i * x pow i))` THEN
  REWRITE_TAC[SUM_ABS_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Monic g: log abs g(X) = n log abs X + O(1 / abs X).                       *)
(* ------------------------------------------------------------------------- *)

let POLY_MONIC_LOG_ASYMPTOTIC = prove
 (`!n (c:num->real).
    1 <= n /\ c n = &1
    ==> ?X0 C. &1 <= X0 /\ &0 <= C /\
               !X. X0 <= abs X
                   ==> ~(sum(0..n) (\i. c i * X pow i) = &0) /\
                       abs(log(abs(sum(0..n) (\i. c i * X pow i))) -
                           &n * log(abs X)) <= C / abs X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `s = sum(0..n-1) (\i. abs((c:num->real) i))` THEN
  SUBGOAL_THEN `&0 <= (s:real)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&2 * (s:real) + &1`; `&2 * (s:real)`] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&0 <= (s:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&0 <= (s:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `X:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= abs(X:real)` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 * (s:real) + &1 <= abs(X:real)` THEN
    UNDISCH_TAC `&0 <= (s:real)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(X:real) pow (n - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `&1 <= abs(X:real)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(X:real) pow n = abs X * abs X pow (n - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `1 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `X:real`] POLY_MONIC_SPLIT) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`n - 1`; `c:num->real`; `X:real`] POLY_TAIL_BOUND) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `sum(0..n-1) (\i. abs((c:num->real) i)) = s`] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`sum(0..n) (\i. (c:num->real) i * X pow i)`; `abs(X:real)`;
                `abs(X:real) pow (n - 1)`; `s:real`] POLY_LOG_CORE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MP_TAC(SPECL [`sum(0..n) (\i. (c:num->real) i * X pow i)`;
                  `(X:real) pow n`] REAL_ABS_SUB_ABS) THEN
    REWRITE_TAC[REAL_ABS_POW] THEN
    UNDISCH_TAC `abs(X:real) pow n = abs X * abs X pow (n - 1)` THEN
    UNDISCH_TAC
     `abs(sum(0..n-1) (\i. (c:num->real) i * X pow i)) <=
      s * abs X pow (n - 1)` THEN
    UNDISCH_TAC
     `sum(0..n) (\i. (c:num->real) i * X pow i) =
      X pow n + sum(0..n-1) (\i. c i * X pow i)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(X:real) * abs X pow (n - 1) = abs X pow n` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(abs(X:real) pow n) = &n * log(abs X)` SUBST1_TAC THENL
   [MATCH_MP_TAC LOG_POW THEN UNDISCH_TAC `&1 <= abs(X:real)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < abs(sum(0..n) (\i. (c:num->real) i * X pow i))` THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;
