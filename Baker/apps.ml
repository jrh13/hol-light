(* ========================================================================= *)
(* Applications of Baker theorem: transcendence, Gelfond-Schneider, gaps     *)
(* between S-units, an irrationality measure for pi.                         *)
(*                                                                           *)
(* Purpose: the qualitative corollaries of the Baker-Feldman bound (Baker,   *)
(* Transcendental Number Theory, Ch. 2, Thms 2.1-2.4), the S-unit gap of     *)
(* Tijdeman (1973) and irrationality measures from lower bounds for linear   *)
(* forms in logarithms.                                                      *)
(*                                                                           *)
(* Main results: BAKER_LINEAR_INDEPENDENCE (Thm 2.1): if lg 1, ..., lg n     *)
(* (cexp(lg r) algebraic) are linearly independent over the rationals then   *)
(* 1, lg 1, ..., lg n are linearly independent over the algebraic numbers.   *)
(* BAKER_INHOMOGENEOUS: for arbitrary such lg r and algebraic beta j, beta 0 *)
(* + sum beta r lg r = 0 implies beta 0 = 0. Hence a nonzero combination sum *)
(* beta r lg r is transcendental (BAKER_LOG_COMBINATION_TRANSCENDENTAL, Thm  *)
(* 2.2) and so is cexp(beta 0 + sum beta r lg r) for beta 0 <> 0             *)
(* (BAKER_EXP_TRANSCENDENTAL, Thm 2.3, which includes Hermite-Lindemann);    *)
(* PI_PLUS_LOG_TRANSCENDENTAL: pi + lg is transcendental.                    *)
(* BAKER_POWER_PRODUCT_TRANSCENDENTAL (Thm 2.4): cexp(sum beta r lg r), that *)
(* is alpha_1^beta_1 ... alpha_n^beta_n, is transcendental if all lg r <> 0  *)
(* and 1, beta_1, ..., beta_n are linearly independent over the rationals.   *)
(* GELFOND_SCHNEIDER: cexp l and beta algebraic, l <> 0, beta irrational ==> *)
(* cexp(beta l) transcendental. GELFOND_SCHNEIDER_CPOW: the same for a cpow  *)
(* b with a <> 0, 1 algebraic. EXP_PI_TRANSCENDENTAL: e^pi.                  *)
(* GELFOND_SCHNEIDER_CONSTANT: 2^sqrt 2 (Hilbert seventh problem).           *)
(* REAL_DIV_POW_ANTIMONO: a / y^k <= a / x^k for a >= 0 and 0 < x <= y.      *)
(* SUNIT_GAP (Tijdeman 1973): for a finite set S of primes there are c > 0   *)
(* and C such that all S-units 3 <= x < y satisfy y - x >= c x / (log x)^C.  *)
(* Proof: BAKER_FELDMAN with the primes of S as alphas and Dx = 1 bounds log *)
(* y - log x = sum (index p y - index p x) log p from below by (4 log x)^-C  *)
(* when y < 2 x; and y - x >= x (log y - log x). SUNIT_POW_GAP: |a^m - b^n|  *)
(* >= c a^m / m^C for a, b >= 2, m >= 2 and a^m <> b^n (S = the primes       *)
(* dividing a b), and its case POW2_POW3_GAP: |2^m - 3^n| >= c 2^m / m^C for *)
(* m >= 2. IRRATIONALITY_MEASURE_LINEAR_FORM: an irrational x has a finite   *)
(* irrationality measure if w |q x - p| >= (K q)^-C (w > 0, K >= |x| + 1)    *)
(* for all integers p, q with 1 <= q, |p| <= K q and q x <> p.               *)
(* PI_IRRATIONALITY_MEASURE: |pi - p / q| >= c / q^C (BAKER_FELDMAN with lg  *)
(* 1 = ii pi, beta 0 = -ii p, beta 1 = q).                                   *)
(*                                                                           *)
(* Uses: Baker/theorem.ml (BAKER_LOWER_BOUND_INDEPENDENT, BAKER_FELDMAN,     *)
(* INTEGER_INDEPENDENT_SUBFAMILY, LINEAR_FORM_SUBFAMILY), Baker/bridge.ml    *)
(* (closure properties of algebraic_number, ALGEBRAIC_NUMBER_CX_SQRT,        *)
(* explicit integer polynomials), Baker/prelim.ml (VSUM_NUMSEG_SPLIT_LAST),  *)
(* Baker/lemmas.ml (VSUM_DEGREE_1_ROOT); 100/sqrt.ml                         *)
(* (IRRATIONAL_SQRT_2), 100/transcendence.ml                                 *)
(* (algebraic_number_neg), Multivariate/vectors.ml (VSUM_2).                 *)
(* ========================================================================= *)

needs "100/sqrt.ml";;
needs "Baker/theorem.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The qualitative theorem (Baker, Thm 2.1).                                 *)
(* ------------------------------------------------------------------------- *)

let BAKER_LINEAR_INDEPENDENCE = prove
 (`!n (lg:num->complex) (beta:num->complex).
     1 <= n /\
     (!r. r IN 1..n ==> algebraic_number(cexp(lg r))) /\
     (!b. (!r. r IN 1..n ==> integer(b r)) /\
          vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
          ==> !r. r IN 1..n ==> b r = &0) /\
     (!j. j <= n ==> algebraic_number(beta j)) /\
     beta 0 + vsum(1..n) (\r. beta r * lg r) = Cx(&0)
     ==> !j. j <= n ==> beta j = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d (a:num->num->real) (H:num->real).
      !r. r IN 1..n
          ==> 1 <= d r /\ &1 <= H r /\
              (!j. integer(a r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT_1 THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?db (ab:num->num->real) (Hb:num->real).
      !j. j <= n
          ==> 1 <= db j /\ &1 <= Hb j /\
              (!i. integer(ab j i) /\ abs(ab j i) <= Hb j) /\
              ~(ab j (db j) = &0) /\
              vsum(0..db j) (\i. Cx(ab j i) * beta j pow i) = Cx(&0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT_1 THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j <= n ==> &0 <= (Hb:num->real) j` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && free_in `ab:num->num->real` (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `lg:num->complex`; `a:num->num->real`; `d:num->num`;
                `H:num->real`; `nsum(0..n) db + 1`]
               BAKER_LOWER_BOUND_INDEPENDENT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= x + 1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:num` (MP_TAC o SPECL
   [`&2 + sum(0..n) (Hb:num->real)`; `beta:num->complex`; `db:num->num`;
    `ab:num->num->real`])) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ ~c ==> (a /\ b /\ ~p ==> c) ==> p`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &2 <= &2 + x`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && free_in `ab:num->num->real` (concl th) &&
      free_in `db:num->num` (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x <= s ==> x <= s + 1`) THEN
      MP_TAC(ISPECL [`db:num->num`; `nsum(0..n) db`; `0..n`]
                    NSUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_NUMSEG; LE_0];
      X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Hb:num->real) j` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= s ==> x <= &2 + s`) THEN
      MP_TAC(ISPECL [`Hb:num->real`; `sum(0..n) Hb`; `0..n`]
                    SUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; IN_NUMSEG; LE_0] THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_NOT_LE; REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 + x`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Arbitrary logarithms: Baker, Thms 2.2, 2.3 and 2.4.                       *)
(* ------------------------------------------------------------------------- *)

let BAKER_INHOMOGENEOUS = prove
 (`!n (lg:num->complex) (beta:num->complex).
     (!r. r IN 1..n ==> algebraic_number(cexp(lg r))) /\
     (!j. j <= n ==> algebraic_number(beta j)) /\
     beta 0 + vsum(1..n) (\r. beta r * lg r) = Cx(&0)
     ==> beta 0 = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `lg:num->complex`] INTEGER_INDEPENDENT_SUBFAMILY) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`t:num`; `sg:num->num`; `N:real`; `c:num->num->real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `t:num`; `lg:num->complex`; `sg:num->num`;
                `N:real`; `c:num->num->real`; `beta:num->complex`]
               LINEAR_FORM_SUBFAMILY) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `Cx N * beta 0 = Cx(&0)` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `t = 0` THENL
   [UNDISCH_TAC
     `Cx N * beta 0 +
      vsum(1..t) (\s. vsum(1..n) (\r. Cx((c:num->num->real) r s) * beta r) *
                      (lg:num->complex)((sg:num->num) s)) = Cx(&0)` THEN
    ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH_EQ; VSUM_CLAUSES] THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ADD_RID] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`t:num`; `\s. (lg:num->complex)((sg:num->num) s)`;
    `\j. if j = 0 then Cx N * (beta:num->complex) 0
         else vsum(1..n) (\r. Cx((c:num->num->real) r j) * beta r)`]
   BAKER_LINEAR_INDEPENDENCE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `s:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC ALGEBRAIC_NUMBER_MUL THEN
        ASM_SIMP_TAC[ALGEBRAIC_NUMBER_CX_INTEGER; LE_0];
        MATCH_MP_TAC ALGEBRAIC_NUMBER_VSUM THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `r:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC ALGEBRAIC_NUMBER_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC ALGEBRAIC_NUMBER_CX_INTEGER THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
          ASM_ARITH_TAC;
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `Cx(&0)` &&
        can (find_term ((=) `Cx N`)) (lhs(concl th)))) THEN
      AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
      X_GEN_TAC `s:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      BETA_TAC THEN
      SIMP_TAC[ASSUME `1 <= s`; ARITH_RULE `1 <= s ==> ~(s = 0)`]];
    DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0]]);;

let BAKER_LOG_COMBINATION_TRANSCENDENTAL = prove
 (`!n (lg:num->complex) (beta:num->complex).
     (!r. r IN 1..n ==> algebraic_number(cexp(lg r))) /\
     (!r. r IN 1..n ==> algebraic_number(beta r)) /\
     ~(vsum(1..n) (\r. beta r * lg r) = Cx(&0))
     ==> ~algebraic_number(vsum(1..n) (\r. beta r * lg r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL
   [`n:num`; `lg:num->complex`;
    `\j. if j = 0 then --vsum(1..n) (\r. (beta:num->complex) r * lg r)
         else beta j`] BAKER_INHOMOGENEOUS) THEN
  BETA_TAC THEN REWRITE_TAC[COMPLEX_NEG_EQ_0] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[algebraic_number_neg] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC(COMPLEX_RING `y = x ==> --x + y = Cx(&0)`) THEN
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_NUMSEG; ARITH_RULE
     `1 <= r ==> ~(r = 0)`]]);;

let BAKER_EXP_TRANSCENDENTAL = prove
 (`!n (lg:num->complex) (beta:num->complex).
     (!r. r IN 1..n ==> algebraic_number(cexp(lg r))) /\
     (!j. j <= n ==> algebraic_number(beta j)) /\ ~(beta 0 = Cx(&0))
     ==> ~algebraic_number(cexp(beta 0 + vsum(1..n) (\r. beta r * lg r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL
   [`SUC n`;
    `\r. if r = SUC n
         then beta 0 + vsum(1..n) (\r. (beta:num->complex) r * lg r)
         else (lg:num->complex) r`;
    `\j. if j = SUC n then --Cx(&1) else (beta:num->complex) j`]
   BAKER_INHOMOGENEOUS) THEN
  BETA_TAC THEN REWRITE_TAC[ARITH_RULE `~(0 = SUC n)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[algebraic_number_neg; ALGEBRAIC_NUMBER_CX_NUM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MP_TAC(ISPECL
     [`\r. (beta:num->complex) r * (lg:num->complex) r`;
      `\r. (if r = SUC n then --Cx(&1) else (beta:num->complex) r) *
           (if r = SUC n
            then beta 0 + vsum(1..n) (\r. beta r * lg r)
            else (lg:num->complex) r)`;
      `n:num`] VSUM_NUMSEG_SPLIT_LAST) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `s:num` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `~(s = SUC n)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC COMPLEX_RING]]);;

let BAKER_POWER_PRODUCT_TRANSCENDENTAL = prove
 (`!n (lg:num->complex) (beta:num->complex).
     1 <= n /\
     (!r. r IN 1..n ==> algebraic_number(cexp(lg r)) /\ ~(lg r = Cx(&0))) /\
     (!r. r IN 1..n ==> algebraic_number(beta r)) /\
     (!b. (!r. r <= n ==> integer(b r)) /\
          Cx(b 0) + vsum(1..n) (\r. Cx(b r) * beta r) = Cx(&0)
          ==> !r. r <= n ==> b r = &0)
     ==> ~algebraic_number(cexp(vsum(1..n) (\r. beta r * lg r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `L = vsum(1..n) (\r. (beta:num->complex) r * lg r)` THEN
  MP_TAC(SPECL [`n:num`; `lg:num->complex`] INTEGER_INDEPENDENT_SUBFAMILY) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`t:num`; `sg:num->num`; `N:real`; `c:num->num->real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `gam = \s. vsum(1..n) (\r. Cx((c:num->num->real) r s) *
                              (beta:num->complex) r)` THEN
  SUBGOAL_THEN
   `Cx N * L = vsum(1..t) (\s. (gam:num->complex) s * lg((sg:num->num) s))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `t:num`; `lg:num->complex`; `sg:num->num`;
                  `N:real`; `c:num->num->real`;
                  `\j. if j = 0 then Cx(&0) else (beta:num->complex) j`]
                 LINEAR_FORM_SUBFAMILY) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_LID] THEN
    MATCH_MP_TAC(MESON[]
     `(a:complex) = a' /\ (b:complex) = b' ==> a = b ==> a' = b'`) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "L" THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
      SIMP_TAC[IN_NUMSEG; ARITH_RULE `1 <= r ==> ~(r = 0)`];
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `s:num` THEN DISCH_TAC THEN
      BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "gam" THEN
      MATCH_MP_TAC VSUM_EQ THEN
      SIMP_TAC[IN_NUMSEG; ARITH_RULE `1 <= r ==> ~(r = 0)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. 1 <= s /\ s <= t ==> algebraic_number((gam:num->complex) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "gam" THEN
    MATCH_MP_TAC ALGEBRAIC_NUMBER_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_NUMBER_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALGEBRAIC_NUMBER_CX_INTEGER THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r s. r IN 1..n /\ s IN 1..t ==> (c:num->num->real) r s = &0`
  ASSUME_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Cx N`)) (concl th) &&
      can (find_term ((=) `(c:num->num->real) r s`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN
    SUBGOAL_THEN
     `vsum(1..t) (\s. Cx((c:num->num->real) 1 s) *
                      (lg:num->complex)((sg:num->num) s)) = Cx(&0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
      X_GEN_TAC `s:num` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `(c:num->num->real) 1 s = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL];
        REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]];
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `cexp`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN MESON_TAC[]]] THEN
  ASM_CASES_TAC `t = 0` THENL
   [ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH_EQ; NOT_IN_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?m (k:num->real).
      integer m /\ ~(m = &0) /\ (!s. s IN 1..t ==> integer(k s)) /\
      (!s. s IN 1..t
           ==> Cx m * (gam:num->complex) s + Cx N * Cx(k s) = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `\q. if q = 0 then N * (k:num->real) s
          else m * (c:num->num->real) q s` o check (fun th ->
      is_forall(concl th) &&
      type_of(fst(dest_forall(concl th))) = `:num->real` &&
      can (find_term ((=) `beta:num->complex`)) (concl th))) THEN
    BETA_TAC THEN REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `q:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
        MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC THEN
        TRY(FIRST_ASSUM ACCEPT_TAC) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `s IN 1..t` THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
        SUBGOAL_THEN
         `vsum(1..n) (\r. Cx(if r = 0 then N * (k:num->real) s
                             else m * (c:num->num->real) r s) *
                          (beta:num->complex) r) =
          Cx m * vsum(1..n) (\r. Cx(c r s) * beta r)`
        SUBST1_TAC THENL
         [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
          MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `u:num` THEN
          REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN BETA_TAC THEN
          SIMP_TAC[ASSUME `1 <= u`; ARITH_RULE `1 <= u ==> ~(u = 0)`;
                   CX_MUL] THEN
          CONV_TAC COMPLEX_RING;
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:num` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `Cx m`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "gam" THEN
        REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING];
      DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
      UNDISCH_TAC `r IN 1..n` THEN REWRITE_TAC[IN_NUMSEG] THEN
      STRIP_TAC THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(r = 0)` (fun th -> REWRITE_TAC[th; REAL_ENTIRE]) THENL
       [ASM_ARITH_TAC;
        UNDISCH_TAC `~(m = &0)` THEN CONV_TAC TAUT]]] THEN
  ASM_CASES_TAC
   `!b. (!s. s IN 1..SUC t ==> integer(b s)) /\
        vsum(1..SUC t)
         (\s. Cx(b s) * (if s = SUC t then L
                         else (lg:num->complex)((sg:num->num) s))) =
        Cx(&0)
        ==> !s. s IN 1..SUC t ==> b s = &0` THENL
   [MP_TAC(SPECL
     [`SUC t`;
      `\s. if s = SUC t then L else (lg:num->complex)((sg:num->num) s)`;
      `\j. if j = 0 then Cx(&0) else if j = SUC t then --Cx N
           else (gam:num->complex) j`]
     BAKER_LINEAR_INDEPENDENCE) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        X_GEN_TAC `s:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(sg:num->num) s IN 1..n` ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
          ASM_ARITH_TAC;
          ASM_SIMP_TAC[]];
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN REPEAT COND_CASES_TAC THEN
        ASM_SIMP_TAC[ALGEBRAIC_NUMBER_CX_NUM; algebraic_number_neg;
                     ALGEBRAIC_NUMBER_CX_INTEGER] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[COMPLEX_ADD_LID] THEN
        MP_TAC(ISPECL
         [`\s. (gam:num->complex) s * (lg:num->complex)((sg:num->num) s)`;
          `\s. (if s = 0 then Cx(&0) else if s = SUC t then --Cx N
                else (gam:num->complex) s) *
               (if s = SUC t then L
                else (lg:num->complex)((sg:num->num) s))`;
          `t:num`] VSUM_NUMSEG_SPLIT_LAST) THEN
        ANTS_TAC THENL
         [X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
          SUBGOAL_THEN `~(s = 0) /\ ~(s = SUC t)`
           (fun th -> REWRITE_TAC[th]) THEN
          ASM_ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
          REWRITE_TAC[NOT_SUC] THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
            is_eq(concl th) && lhs(concl th) = `Cx N * L`)) THEN
          CONV_TAC COMPLEX_RING]];
      DISCH_THEN(MP_TAC o SPEC `SUC t`) THEN
      REWRITE_TAC[LE_REFL; NOT_SUC; COMPLEX_NEG_EQ_0; CX_INJ] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL
   [`\s. Cx((b:num->real) s) * (lg:num->complex)((sg:num->num) s)`;
    `\s. Cx((b:num->real) s) *
         (if s = SUC t then L else (lg:num->complex)((sg:num->num) s))`;
    `t:num`] VSUM_NUMSEG_SPLIT_LAST) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(s = SUC t)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    BETA_TAC THEN REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC] THEN
  SUBGOAL_THEN `~((b:num->real)(SUC t) = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b:num->real` o check (fun th ->
      is_forall(concl th) &&
      type_of(fst(dest_forall(concl th))) = `:num->real` &&
      can (find_term ((=) `sg:num->num`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `s:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
        UNDISCH_TAC
         `vsum(1..t) (\s. Cx((b:num->real) s) *
                          (lg:num->complex)((sg:num->num) s)) +
          Cx(b(SUC t)) * L = Cx(&0)` THEN
        ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID]];
      DISCH_TAC THEN UNDISCH_TAC `~((b:num->real) j0 = &0)` THEN
      REWRITE_TAC[] THEN UNDISCH_TAC `j0 IN 1..SUC t` THEN
      REWRITE_TAC[IN_NUMSEG] THEN ASM_CASES_TAC `j0 = SUC t` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. 1 <= s /\ s <= SUC t ==> integer((b:num->real) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(b:num->real)(SUC t)`; `b:num->real`] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `integer((b:num->real) s)`)) (concl th) &&
      can (find_term ((=) `s <= SUC t`)) (concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `integer((b:num->real) s)`)) (concl th) &&
      can (find_term ((=) `s <= SUC t`)) (concl th))) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:num`; `\s. (lg:num->complex)((sg:num->num) s)`;
                `\j. if j = 0 then Cx(&0)
                     else Cx((b:num->real)(SUC t)) * (gam:num->complex) j +
                          Cx N * Cx(b j)`]
               BAKER_LINEAR_INDEPENDENCE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `s:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(sg:num->num) s IN 1..n` ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `(sg:num->num) s IN 1..n`)) (concl th))) THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `(sg:num->num) s` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `cexp`)) (concl th))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM] THEN
      MATCH_MP_TAC ALGEBRAIC_NUMBER_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC ALGEBRAIC_NUMBER_MUL THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC ALGEBRAIC_NUMBER_CX_INTEGER THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC ALGEBRAIC_NUMBER_CX_INTEGER THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC ALGEBRAIC_NUMBER_CX_INTEGER THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      REWRITE_TAC[COMPLEX_ADD_LID] THEN
      TRANS_TAC EQ_TRANS
       `Cx((b:num->real)(SUC t)) *
        vsum(1..t) (\s. (gam:num->complex) s *
                        (lg:num->complex)((sg:num->num) s)) +
        Cx N * vsum(1..t) (\s. Cx(b s) * lg(sg s))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_ADD; FINITE_NUMSEG] THEN
        MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `u:num` THEN
        REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN BETA_TAC THEN
        SIMP_TAC[ASSUME `1 <= u`; ARITH_RULE `1 <= u ==> ~(u = 0)`] THEN
        CONV_TAC COMPLEX_RING;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          is_eq(concl th) && lhs(concl th) = `Cx N * L`)) THEN
        UNDISCH_TAC
         `vsum(1..t) (\s. Cx((b:num->real) s) *
                          (lg:num->complex)((sg:num->num) s)) +
          Cx(b(SUC t)) * L = Cx(&0)` THEN
        CONV_TAC COMPLEX_RING]];
    DISCH_TAC THEN X_GEN_TAC `s:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(s = 0)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Gelfond-Schneider and the transcendence of e^pi.                          *)
(* ------------------------------------------------------------------------- *)

let GELFOND_SCHNEIDER = prove
 (`!l beta. algebraic_number(cexp l) /\ ~(l = Cx(&0)) /\
            algebraic_number beta /\ ~(?q. rational q /\ beta = Cx q)
            ==> ~algebraic_number(cexp(beta * l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `!b. (!r. r IN 1..2 ==> integer(b r)) /\
        vsum(1..2) (\r. Cx(b r) * (if r = 1 then l else beta * l)) = Cx(&0)
        ==> !r. r IN 1..2 ==> b r = &0` THENL
   [MP_TAC(SPECL [`2`; `\r:num. if r = 1 then l:complex else beta * l`;
                  `\j:num. if j = 0 then Cx(&0)
                           else if j = 1 then beta else --Cx(&1)`]
          BAKER_LINEAR_INDEPENDENCE) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        X_GEN_TAC `r:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        REPEAT COND_CASES_TAC THEN
        ASM_SIMP_TAC[ALGEBRAIC_NUMBER_CX_NUM; algebraic_number_neg];
        REWRITE_TAC[VSUM_2] THEN BETA_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING];
      DISCH_THEN(MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[COMPLEX_NEG_EQ_0; CX_INJ] THEN REAL_ARITH_TAC];
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:num->real` MP_TAC o
      REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    REWRITE_TAC[VSUM_2; IN_NUMSEG;
                ARITH_RULE `1 <= r /\ r <= 2 <=> r = 1 \/ r = 2`] THEN
    REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `Cx(b 1) + Cx(b 2) * beta = Cx(&0)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(l = Cx(&0))` THEN
      UNDISCH_TAC `Cx(b 1) * l + Cx(b 2) * beta * l = Cx(&0)` THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    ASM_CASES_TAC `b 2 = &0` THENL
     [UNDISCH_TAC `~(b 1 = &0) \/ ~(b 2 = &0)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Cx(b 1) + Cx(b 2) * beta = Cx(&0)` THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; CX_INJ];
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        is_neg(concl th) && is_exists(rand(concl th)))) THEN
      REWRITE_TAC[] THEN EXISTS_TAC `--(b 1) / b 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RATIONAL_DIV THEN
        ASM_SIMP_TAC[RATIONAL_NEG; RATIONAL_INTEGER];
        UNDISCH_TAC `Cx(b 1) + Cx(b 2) * beta = Cx(&0)` THEN
        UNDISCH_TAC `~(b 2 = &0)` THEN
        REWRITE_TAC[GSYM CX_INJ; CX_DIV; CX_NEG] THEN
        CONV_TAC COMPLEX_FIELD]]]);;

let GELFOND_SCHNEIDER_CPOW = prove
 (`!a b. algebraic_number a /\ ~(a = Cx(&0)) /\ ~(a = Cx(&1)) /\
         algebraic_number b /\ ~(?q. rational q /\ b = Cx q)
         ==> ~algebraic_number(a cpow b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[cpow] THEN
  MATCH_MP_TAC GELFOND_SCHNEIDER THEN ASM_SIMP_TAC[CEXP_CLOG] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(a = Cx(&1))` THEN REWRITE_TAC[] THEN
  MP_TAC(SPEC `a:complex` CEXP_CLOG) THEN ASM_REWRITE_TAC[CEXP_0] THEN
  MESON_TAC[]);;

let EXP_PI_TRANSCENDENTAL = prove
 (`~algebraic_number(cexp(Cx pi))`,
  SUBGOAL_THEN `Cx pi = --ii * ii * Cx pi` SUBST1_TAC THENL
   [MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC GELFOND_SCHNEIDER THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CEXP_II_PI] THEN MATCH_MP_TAC algebraic_number_neg THEN
    REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM];
    REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ; PI_NZ];
    MATCH_MP_TAC algebraic_number_neg THEN REWRITE_TAC[algebraic_number_ii];
    DISCH_THEN(X_CHOOSE_THEN `q:real` (MP_TAC o AP_TERM `Im` o CONJUNCT2)) THEN
    REWRITE_TAC[IM_NEG; IM_II; IM_CX] THEN REAL_ARITH_TAC]);;

let PI_PLUS_LOG_TRANSCENDENTAL = prove
 (`!z. algebraic_number(cexp z) ==> ~algebraic_number(Cx pi + z)`,
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL
   [`2`; `\r. if r = 1 then ii * Cx pi else z`;
    `\j. if j = 0 then --(Cx pi + z) else if j = 1 then --ii else Cx(&1)`]
   BAKER_INHOMOGENEOUS) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REWRITE_TAC[VSUM_2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[CEXP_II_PI] THEN MATCH_MP_TAC algebraic_number_neg THEN
      REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN REPEAT COND_CASES_TAC THEN
      ASM_SIMP_TAC[algebraic_number_neg; algebraic_number_ii;
                   ALGEBRAIC_NUMBER_CX_NUM];
      MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING];
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_NEG_EQ_0] THEN
    DISCH_TAC THEN MP_TAC EXP_PI_TRANSCENDENTAL THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `z = --Cx pi` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `Cx pi + z = Cx(&0)` THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    UNDISCH_TAC `algebraic_number(cexp(--Cx pi))` THEN
    REWRITE_TAC[CEXP_NEG] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ALGEBRAIC_NUMBER_INV) THEN
    REWRITE_TAC[COMPLEX_INV_INV]]);;

let GELFOND_SCHNEIDER_CONSTANT = prove
 (`~algebraic_number(Cx(&2) cpow Cx(sqrt(&2)))`,
  MATCH_MP_TAC GELFOND_SCHNEIDER_CPOW THEN
  REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM; ALGEBRAIC_NUMBER_CX_SQRT; CX_INJ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[IRRATIONAL_SQRT_2]);;

(* ------------------------------------------------------------------------- *)
(* Gaps between S-units (Tijdeman).                                          *)
(* ------------------------------------------------------------------------- *)

let INDEX_LOG_BOUND = prove
 (`!p n. 2 <= p /\ ~(n = 0) ==> &(index p n) <= &2 * log(&n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (index p n) <= n` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `p EXP (index p n)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[EXP_MONO_LE];
      MP_TAC(SPECL [`n:num`; `p:num`; `index p n`] PRIMEPOW_DIVIDES_INDEX) THEN
      REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(index p n) * log(&2) <= log(&n)` ASSUME_TAC THENL
   [SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) LOG_MONO_LE o snd) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; LT_NZ;
                 REAL_OF_NUM_POW; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(CONJUNCT1 LOG_2_BOUNDS) THEN
  MP_TAC(SPECL [`&(index p n)`; `&1 / &2`; `log(&2)`] REAL_LE_LMUL) THEN
  REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC);;

let LOG_SUNIT = prove
 (`!S x. FINITE S /\ (!q. q IN S ==> prime q) /\ ~(x = 0) /\
         (!q. prime q /\ q divides x ==> q IN S)
         ==> log(&x) = sum S (\q. &(index q x) * log(&q))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&x = product S (\q. &q pow index q x)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_POW; GSYM REAL_OF_NUM_NPRODUCT;
                 REAL_OF_NUM_EQ] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
      [SYM(MATCH_MP PRIME_FACTORIZATION th)]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC NPRODUCT_SUPERSET THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `index q x = 0` (fun th -> REWRITE_TAC[th; EXP]) THEN
    MATCH_MP_TAC INDEX_ZERO THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `!q. q IN S ==> &0 < &q` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_IMP_NZ; REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_PRODUCT; LOG_POW; REAL_POW_LT]]);;

let LOG_SUNIT_NUMSEG = prove
 (`!pr s z. (!i j. i IN 1..s /\ j IN 1..s /\ pr i = pr j ==> i = j) /\
            (!r. r IN 1..s ==> prime(pr r)) /\ ~(z = 0) /\
            (!q. prime q /\ q divides z ==> q IN IMAGE pr (1..s))
            ==> log(&z) = sum(1..s) (\r. &(index (pr r) z) * log(&(pr r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`IMAGE (pr:num->num) (1..s)`; `z:num`] LOG_SUNIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF]);;

let SUNIT_GAP = prove
 (`!S. FINITE S /\ (!p. p IN S ==> prime p)
       ==> ?c C. &0 < c /\
                 !x y. 3 <= x /\ x < y /\
                       (!p. prime p /\ p divides x ==> p IN S) /\
                       (!p. prime p /\ p divides y ==> p IN S)
                       ==> c * &x / log(&x) pow C <= &y - &x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `s = CARD(S:num->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `pr:num->num`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `!r. r IN 1..s ==> prime((pr:num->num) r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN 1..s ==> &0 < &((pr:num->num) r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(SPECL [`s:num`; `\r. Cx(log(&((pr:num->num) r)))`; `1`]
    BAKER_FELDMAN)) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM CX_EXP] THEN
    SUBGOAL_THEN `&0 < &((pr:num->num) r)`
     (fun th -> REWRITE_TAC[MATCH_MP EXP_LOG th; ALGEBRAIC_NUMBER_CX_NUM]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_TAC `C:num`)] THEN
  MAP_EVERY EXISTS_TAC [`inv(&4 pow C)`; `C:num`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~(x = 0) /\ ~(y = 0) /\ &0 < &x /\ &0 < &y /\ &x < &y /\ &3 <= &x`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) <= log(&x) /\ log(&x) < log(&y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP; MATCH_MP_TAC LOG_MONO_LT_IMP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(CONJUNCT1 LOG_2_BOUNDS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < log(&x)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&x * (log(&y) - log(&x)) <= &y - &x` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(&y) - log(&x) = log(&1 + (&y - &x) / &x)`
    SUBST1_TAC THENL
     [SIMP_TAC[GSYM LOG_DIV; ASSUME `&0 < &x`; ASSUME `&0 < &y`] THEN
      AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < &x` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&x * (&y - &x) / &x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL;
               ASSUME `&0 < &x`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(&4 pow C) * &x / log(&x) pow C = &x * inv((&4 * log(&x)) pow C)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &4 * log(&x)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&2 * &x <= &y` THENL
   [TRANS_TAC REAL_LE_TRANS `&x` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&y) <= &2 * log(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&2 * &x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[LOG_MUL; REAL_OF_NUM_LT; ARITH; ASSUME `&0 < &x`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `b = \j. if j = 0 then &0
            else &(index ((pr:num->num) j) y) - &(index (pr j) x)` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`&4 * log(&x)`; `\j. Cx((b:num->real) j)`; `\j:num. 1`;
    `\j i. if i = 0 then --((b:num->real) j)
           else if i = 1 then &1 else &0`]) THEN
  BETA_TAC THEN REWRITE_TAC[LE_REFL; VSUM_DEGREE_1_ROOT] THEN
  SUBGOAL_THEN
   `Cx(b 0) + vsum(1..s) (\r. Cx(b r) * Cx(log(&((pr:num->num) r)))) =
    Cx(log(&y) - log(&x))`
  SUBST1_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[COMPLEX_ADD_LID] THEN
    REWRITE_TAC[GSYM CX_MUL; VSUM_CX; CX_INJ] THEN
    TRANS_TAC EQ_TRANS
     `sum(1..s) (\r. &(index ((pr:num->num) r) y) * log(&(pr r)) -
                     &(index (pr r) x) * log(&(pr r)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      SIMP_TAC[ASSUME `1 <= i`; ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUM_SUB_NUMSEG] THEN BINOP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_SUNIT_NUMSEG THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ] THEN
  SUBGOAL_THEN `abs(log(&y) - log(&x)) = log(&y) - log(&x) /\
                ~(log(&y) - log(&x) = &0)`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `integer((b:num->real) j) /\ abs(b j) <= &4 * log(&x)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "b" THEN COND_CASES_TAC THENL
       [REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
      MP_TAC(SPECL [`(pr:num->num) j`; `y:num`] INDEX_LOG_BOUND) THEN
      MP_TAC(SPECL [`(pr:num->num) j`; `x:num`] INDEX_LOG_BOUND) THEN
      SUBGOAL_THEN `2 <= (pr:num->num) j` ASSUME_TAC THENL
       [MATCH_MP_TAC PRIME_GE_2 THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      MP_TAC(SPEC `index ((pr:num->num) j) x` REAL_POS) THEN
      MP_TAC(SPEC `index ((pr:num->num) j) y` REAL_POS) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    X_GEN_TAC `i:num` THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG; REAL_ABS_NEG; REAL_ABS_NUM;
                ASSUME `integer((b:num->real) j)`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN TRANS_TAC REAL_LE_TRANS `&x * (log(&y) - log(&x))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[REAL_POS]);;

let REAL_DIV_POW_ANTIMONO = prove
 (`!a x y k. &0 <= a /\ &0 < x /\ x <= y ==> a / y pow k <= a / x pow k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_POW_LE2; REAL_LT_IMP_LE]);;

let SUNIT_POW_GAP = prove
 (`!a b. 2 <= a /\ 2 <= b
         ==> ?c C. &0 < c /\
                   !m n. 2 <= m /\ ~(a EXP m = b EXP n)
                         ==> c * &a pow m / &m pow C <=
                             abs(&a pow m - &b pow n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `{p | prime p /\ p divides a * b}` SUNIT_GAP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..(a * b)` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC;
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < &a /\ &0 < log(&a) /\ &1 <= (log(&a) + &1) pow C`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= x + &1`) THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`min c (&1) / &2 / (log(&a) + &1) pow C`; `C:num`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!p. prime p /\ p divides a EXP m
         ==> p IN {p | prime p /\ p divides a * b}) /\
    (!p. prime p /\ p divides b EXP n
         ==> p IN {p | prime p /\ p divides a * b})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[PRIME_DIVEXP; DIVIDES_LMUL; DIVIDES_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 <= a EXP m` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `a EXP 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[EXP_2] THEN
      MP_TAC(SPECL [`2`; `a:num`; `2`; `a:num`] LE_MULT2) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= &a pow m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&a pow m) /\ log(&a pow m) <= &m * (log(&a) + &1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[LOG_POW] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D = (&m * (log(&a) + &1)) pow C` THEN
  SUBGOAL_THEN `log(&a pow m) pow C <= D /\ &1 <= D` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_POW_LE_1 THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x ==> &1 <= x`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `min c (&1) / &2 / (log(&a) + &1) pow C * &a pow m / &m pow C =
    min c (&1) / &2 * &a pow m / D`
  SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN
    REWRITE_TAC[REAL_POW_MUL; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &a pow m / D /\ &a pow m / D <= &a pow m`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POW_LE; REAL_POS;
                 REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(x = y) ==> x < y \/ y < x`)) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`a EXP m`; `b EXP n`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `y:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= y - x ==> a <= abs(x - y)`) THEN
    TRANS_TAC REAL_LE_TRANS `c * &a pow m / D` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `2 * b EXP n <= a EXP m` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= x / &2 /\ &2 * y <= x ==> a <= abs(x - y)`) THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&1 / &2 * &a pow m` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b EXP n`; `a EXP m`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `y:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  SUBGOAL_THEN `3 <= b EXP n` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LT] o
    check (fun th -> concl th = `a EXP m < 2 * b EXP n`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LT] o
    check (fun th -> concl th = `b EXP n < a EXP m`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < log(&b pow n) /\ log(&b pow n) pow C <= D`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `log(&a pow m) pow C` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= x - y ==> a <= abs(x - y)`) THEN
  TRANS_TAC REAL_LE_TRANS `c * &b pow n / D` THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `c / &2 * &a pow m / D` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT]]]);;

let POW2_POW3_GAP = prove
 (`?c C. &0 < c /\
         !m n. 2 <= m ==> c * &2 pow m / &m pow C <= abs(&2 pow m - &3 pow n)`,
  MP_TAC(SPECL [`2`; `3`] SUNIT_POW_GAP) THEN REWRITE_TAC[ARITH] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MATCH_MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_EXP; ARITH] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Irrationality measures from lower bounds for linear forms; a finite       *)
(* irrationality measure for pi.                                             *)
(* ------------------------------------------------------------------------- *)

let IRRATIONALITY_MEASURE_LINEAR_FORM = prove
 (`!x w K.
     ~rational x /\ &0 < w /\ abs x + &1 <= K /\
     (?C. !p q. integer p /\ integer q /\ &1 <= q /\ abs p <= K * q /\
                ~(q * x - p = &0)
                ==> inv((K * q) pow C) <= w * abs(q * x - p))
     ==> ?c C. &0 < c /\
               !p q. integer p /\ integer q /\ &1 <= q
                     ==> c / q pow C <= abs(x - p / q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `C:num`)))) THEN
  SUBGOAL_THEN `&1 <= K pow C * (w + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x ==> &1 <= x`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE_1; ALL_TAC] THEN
    MP_TAC(SPEC `x:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv(K pow C * (w + &1))`; `C + 1`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q /\ &1 <= q pow (C + 1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE_1] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= abs(x - p / q)` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_ARITH `a * b <= &1 * &1 ==> a * b <= &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_LE_1) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs p <= K * q` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `abs(p / q) * q` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_DIV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < q ==> abs q = q`; REAL_DIV_RMUL;
                   REAL_LT_IMP_NZ; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q * x - p = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~rational x` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `x = p / q` SUBST1_TAC THENL
     [UNDISCH_TAC `q * x - p = &0` THEN UNDISCH_TAC `&0 < q` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC RATIONAL_DIV THEN ASM_SIMP_TAC[RATIONAL_INTEGER]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real`; `q:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(x - p / q) = abs(q * x - p) / q` SUBST1_TAC THENL
   [SUBGOAL_THEN `q * x - p = q * (x - p / q)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < q ==> abs q = q`] THEN
    UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(K pow C * (w + &1)) / q pow (C + 1) =
    inv((K * q) pow C) / ((w + &1) * q)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW_ADD; REAL_POW_1; real_div;
                REAL_INV_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL;
               REAL_ARITH `&0 < w ==> &0 < w + &1`] THEN
  SUBGOAL_THEN `abs(q * x - p) / q * (w + &1) * q = (w + &1) * abs(q * x - p)`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `w * abs(q * x - p)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REAL_ARITH_TAC);;

let PI_IRRATIONALITY_MEASURE = prove
 (`?c C. &0 < c /\
         !p q. integer p /\ integer q /\ &1 <= q
               ==> c / q pow C <= abs(pi - p / q)`,
  MATCH_MP_TAC IRRATIONALITY_MEASURE_LINEAR_FORM THEN
  MAP_EVERY EXISTS_TAC [`&1`; `&5`] THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[rational] THEN STRIP_TAC THEN MP_TAC pi_is_transcendental THEN
    ASM_REWRITE_TAC[CX_DIV] THEN MATCH_MP_TAC ALGEBRAIC_NUMBER_DIV THEN
    ASM_SIMP_TAC[ALGEBRAIC_NUMBER_CX_INTEGER];
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`1`; `\r:num. ii * Cx pi`; `2`] BAKER_FELDMAN) THEN
  REWRITE_TAC[CEXP_II_PI] THEN ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC algebraic_number_neg THEN
    REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM];
    DISCH_THEN(X_CHOOSE_TAC `C:num`)] THEN
  EXISTS_TAC `2 * C` THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&5 * q) pow (2 * C) = (&25 * q pow 2) pow C` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_POW] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= q pow 2 /\ q <= q pow 2 /\ p pow 2 <= &25 * q pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `q * &1 <= x ==> q <= x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      REWRITE_TAC[REAL_ARITH `&25 * q pow 2 = (&5 * q) pow 2`] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`&25 * q pow 2`; `\j. if j = 0 then --ii * Cx p else Cx q`;
    `\j. if j = 0 then 2 else 1`;
    `\j i. if j = 0 then (if i = 0 then p pow 2 else if i = 2 then &1 else &0)
           else (if i = 0 then --q else if i = 1 then &1 else &0)`]) THEN
  BETA_TAC THEN REWRITE_TAC[VSUM_SING_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `--ii * Cx p + Cx q * ii * Cx pi = ii * Cx(q * pi - p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_SUB; CX_MUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX;
              COMPLEX_ENTIRE; II_NZ; CX_INJ; REAL_MUL_LID] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j <= 1 <=> j = 0 \/ j = 1`] THEN
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_ABS_POW; REAL_POW2_ABS;
             ASSUME `integer p`] THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
    REWRITE_TAC[ARITH; VSUM_2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REWRITE_TAC[complex_pow; COMPLEX_POW_1; CX_POW] THEN
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING;
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_ABS_NEG;
             ASSUME `integer q`] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VSUM_DEGREE_1_ROOT]]);;
