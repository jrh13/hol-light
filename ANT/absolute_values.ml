(* ========================================================================= *)
(* Absolute values on fields: equivalence, the approximation theorem of      *)
(* Artin and Whaples, and the absolute values of the fraction field of a     *)
(* Dedekind domain that are bounded on the domain. The predicates            *)
(* absolute_value k f and nonarchimedean_absolute_value k f are those of     *)
(* ANT/dedekind_absolute.ml, with their basic properties and the             *)
(* nonarchimedean criterion (NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED); f is    *)
(* nontrivial when some nonzero x has f x <> 1, and f2 is equivalent to f1   *)
(* when f2 x = f1 x rpow s for some real s > 0 (both stated directly,        *)
(* without new constants).                                                   *)
(*                                                                           *)
(* Main results, for absolute values on a field k:                           *)
(*                                                                           *)
(*   f1 nontrivial ==> (f2 = f1 rpow s for some s > 0 <=>                    *)
(*                      !x. f1 x < 1 ==> f2 x < 1)                           *)
(*      (ABSOLUTE_VALUE_EQUIVALENT; for f1, f2 nontrivial also with <= 1,    *)
(*       the unit balls, ABSOLUTE_VALUE_EQUIVALENT_LE); f rpow s is an       *)
(*      absolute value for 0 < s <= 1 (ABSOLUTE_VALUE_RPOW), a               *)
(*      nonarchimedean one for every s > 0 if f is                           *)
(*      (NONARCHIMEDEAN_ABSOLUTE_VALUE_RPOW)                                 *)
(*   Artin-Whaples: for finitely many pairwise inequivalent nontrivial f_i,  *)
(*      elements a_i and e > 0 some x has f_i(x - a_i) < e for all i         *)
(*      (ABSOLUTE_VALUE_WEAK_APPROXIMATION)                                  *)
(*   for a Dedekind domain r with fraction field k (along h), a nontrivial   *)
(*      nonarchimedean f with f(h a) <= 1 on r is c zpow --v_P for exactly   *)
(*      one nonzero prime P of r and some c > 1                              *)
(*      (DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE; P = {a | f(h a) < 1},       *)
(*       DEDEKIND_ABSOLUTE_VALUE_PRIME; P and c are determined by the        *)
(*       function, DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE)                 *)
(*                                                                           *)
(* Routes. Equivalence: with y such that f1 y > 1, the hypothesis compares   *)
(* f1 and f2 on the quotients z^n / y^m (f1 u < f1 v ==> f2 u < f2 v), so    *)
(* log f1 z / log f1 y and log f2 z / log f2 y have the same rational lower  *)
(* and upper bounds (REAL_NUM_FRACTIONS_EQ of                                *)
(* Library/floor.ml), first for f1 z > 1 and then for all z through z y^N;   *)
(* with the unit balls, f1 x < 1 = f2 x would make f2 <= 1 on all of k       *)
(* (through x^n z). Artin-Whaples: two inequivalent ones are separated, f1 z *)
(* > 1 > f2 z (ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE); by induction one finds *)
(* z with f_i z > 1 and f_j z < 1 for j <> i                                 *)
(* (ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT, with y^m w or w y^m / (1 + y^m));  *)
(* then y^m / (1 + y^m) tends to 1 for f_i and to 0 for the f_j              *)
(* (ABSOLUTE_VALUE_POW_QUOTIENT) and x is the sum of the a_i z_i^m / (1 +    *)
(* z_i^m) for m large. Dedekind domains: P is a nonzero prime, the unit ball *)
(* of c zpow --v_P (the valuation ring {x | x = 0 \/ v_P(x) >= 0},           *)
(* DEDEKIND_VALUATION_ABSOLUTE_VALUE of ANT/dedekind_absolute.ml) consists   *)
(* of the h(a) / h(b) with b NOTIN P (DEDEKIND_VALUATION_POS) and lies in    *)
(* that of f, so the two are equivalent; distinct nonzero primes are         *)
(* separated by an element of P not in Q (maximality).                       *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml, Library/floor.ml     *)
(* (REAL_NUM_FRACTIONS_EQ), ANT/dedekind.ml, ANT/dedekind_valuation.ml,      *)
(* ANT/dedekind_absolute.ml, Multivariate/transcendentals.ml (rpow, log,     *)
(* REAL_ZPOW_RPOW, RPOW_ADD_LE) and Multivariate/realanalysis.ml             *)
(* (REAL_POW_EVENTUALLY_LT).                                                 *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/floor.ml";;
needs "ANT/integral.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_valuation.ml";;
needs "ANT/dedekind_absolute.ml";;
needs "Multivariate/transcendentals.ml";;
needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Equivalence of absolute values: f2 = f1 rpow s for some s > 0; f rpow s   *)
(* is an absolute value for 0 < s <= 1.                                      *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTE_VALUE_EQUIVALENT = prove
 (`!k (f1:A->real) f2.
        field k /\ absolute_value k f1 /\ absolute_value k f2 /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f1 x = &1))
        ==> ((?s. &0 < s /\ !x. x IN ring_carrier k ==> f2 x = f1 x rpow s) <=>
             (!x. x IN ring_carrier k /\ f1 x < &1 ==> f2 x < &1))`,
  let lemma = prove
   (`!a b m n. &0 < b
               ==> (&n * a / b < &m <=> &n * a < &m * b) /\
                   (&m < &n * a / b <=> &m * b < &n * a)`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `&n * a / b = (&n * a) / b`] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ]) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nontriv")))) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `s:real` RPOW_ONE)] THEN
    MATCH_MP_TAC RPOW_LT2 THEN ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!u v:A. u IN ring_carrier k /\ v IN ring_carrier k /\
            (f1:A->real) u < f1 v
            ==> (f2:A->real) u < f2 v`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(v:A = ring_0 k)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(f1:A->real) u < f1 v` THEN
      ASM_SIMP_TAC[ABSOLUTE_VALUE_0; REAL_NOT_LT] THEN
      ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (f1:A->real) v /\ &0 < (f2:A->real) v`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ring_div k u v:A`) THEN
    ASM_SIMP_TAC[RING_DIV; ABSOLUTE_VALUE_DIV; REAL_LT_LDIV_EQ;
                 REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:A. y IN ring_carrier k /\ (&1:real) < f1 y`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `f1:A->real`] ABSOLUTE_VALUE_NONTRIVIAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 < (f1:A->real) y` THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < (f2:A->real) y` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 = (f2:A->real)(ring_1 k)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTE_VALUE_1; FIELD_NONTRIVIAL]; ALL_TAC] THEN
    USE_THEN "mono" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_1; ABSOLUTE_VALUE_1; FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log((f1:A->real) y) /\ &0 < log((f2:A->real) y)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[LOG_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `s = log((f2:A->real) y) / log((f1:A->real) y)` THEN
  SUBGOAL_THEN `&0 < (s:real)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z:A. z IN ring_carrier k /\ &1 < f1 z
          ==> log(f2 z) / log(f2 y) = log(f1 z) / log(f1 y)`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(z:A = ring_0 k)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 < (f1:A->real) z` THEN
      ASM_SIMP_TAC[ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (f1:A->real) z /\ &0 < (f2:A->real) z /\
                  &0 < (f1:A->real) y /\ &0 < (f2:A->real) y`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_NUM_FRACTIONS_EQ THEN
    ASM_SIMP_TAC[REAL_LT_DIV; LOG_POS_LT; lemma] THEN
    ASM_SIMP_TAC[GSYM LOG_POW; LOG_MONO_LT; REAL_POW_LT] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    (SUBGOAL_THEN
      `(f2:A->real) z pow n = f2(ring_pow k z n) /\
       (f2:A->real) y pow m = f2(ring_pow k y m)`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
      [ASM_SIMP_TAC[ABSOLUTE_VALUE_POW; FIELD_NONTRIVIAL]; ALL_TAC]) THEN
    USE_THEN "mono" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_POW; ABSOLUTE_VALUE_POW; FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `z:A = ring_0 k` THENL
   [ASM_SIMP_TAC[ABSOLUTE_VALUE_0; RPOW_ZERO; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (f1:A->real) z /\ &0 < (f2:A->real) z /\
                &0 < (f1:A->real) y /\ &0 < (f2:A->real) y`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[rpow] THEN
  SUBGOAL_THEN `log((f2:A->real) z) = s * log(f1 z)` (SUBST1_TAC o SYM) THENL
   [ALL_TAC; ASM_SIMP_TAC[EXP_LOG]] THEN
  MP_TAC(ISPECL [`(f1:A->real) y`; `inv((f1:A->real) z)`] REAL_ARCH_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  REMOVE_THEN "key" (MP_TAC o SPEC `ring_mul k z (ring_pow k y N):A`) THEN
  ASM_SIMP_TAC[RING_MUL; RING_POW; ABSOLUTE_VALUE_MUL; ABSOLUTE_VALUE_POW;
               FIELD_NONTRIVIAL] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`(f1:A->real) z`; `inv((f1:A->real) z)`;
                   `(f1:A->real) y pow N`] REAL_LT_LMUL) THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW] THEN
  EXPAND_TAC "s" THEN
  UNDISCH_TAC `&0 < log((f1:A->real) y)` THEN
  UNDISCH_TAC `&0 < log((f2:A->real) y)` THEN
  CONV_TAC REAL_FIELD);;

let ABSOLUTE_VALUE_EQUIVALENT_LE = prove
 (`!k (f1:A->real) f2.
        field k /\ absolute_value k f1 /\ absolute_value k f2 /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f1 x = &1)) /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f2 x = &1))
        ==> ((?s. &0 < s /\ !x. x IN ring_carrier k ==> f2 x = f1 x rpow s) <=>
             (!x. x IN ring_carrier k /\ f1 x <= &1 ==> f2 x <= &1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "nt2"))))) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC RPOW_1_LE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
    DISCH_THEN(LABEL_TAC "le")] THEN
  MP_TAC(ISPECL [`k:A ring`; `f1:A->real`; `f2:A->real`]
    ABSOLUTE_VALUE_EQUIVALENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [USE_THEN "le" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_TAC] THEN
  SUBGOAL_THEN `~(x:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(f2:A->real) x = &1` THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. z IN ring_carrier k ==> (f2:A->real) z <= &1`
  (LABEL_TAC "bd") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `z:A = ring_0 k` THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0; REAL_POS] THEN
    SUBGOAL_THEN `&0 < (f1:A->real) z` ASSUME_TAC THENL
     [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(f1:A->real) x`; `inv((f1:A->real) z)`]
      REAL_ARCH_POW_INV) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    REMOVE_THEN "le" (MP_TAC o SPEC `ring_mul k (ring_pow k x n) z:A`) THEN
    ASM_SIMP_TAC[RING_MUL; RING_POW; ABSOLUTE_VALUE_MUL; ABSOLUTE_VALUE_POW;
                 FIELD_NONTRIVIAL; REAL_POW_ONE; REAL_MUL_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`(f1:A->real) z`; `(f1:A->real) x pow n`;
                   `inv((f1:A->real) z)`] REAL_LT_LMUL) THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "nt2" (X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(f2:A->real) w <= &1 /\ inv((f2:A->real) w) <= &1 /\ &0 < f2 w`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      REMOVE_THEN "bd" (MP_TAC o SPEC `ring_inv k w:A`) THEN
      ASM_SIMP_TAC[RING_INV; ABSOLUTE_VALUE_INV];
      ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (f2:A->real) w` MP_TAC THENL
   [MP_TAC(ISPECL [`(f2:A->real) w`; `inv((f2:A->real) w)`; `(&1:real)`]
      REAL_LE_LMUL) THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LT_IMP_LE; REAL_MUL_RID];
    ASM_REAL_ARITH_TAC]);;

let ABSOLUTE_VALUE_EQUIVALENT_SYM = prove
 (`!k (f1:A->real) f2.
        absolute_value k f1 /\
        (?s. &0 < s /\ !x. x IN ring_carrier k ==> f2 x = f1 x rpow s)
        ==> ?s. &0 < s /\ !x. x IN ring_carrier k ==> f1 x = f2 x rpow s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `inv s:real` THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (f1:A->real) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[ABSOLUTE_VALUE_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_RPOW; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1]);;

let ABSOLUTE_VALUE_RPOW = prove
 (`!k (f:A->real) s.
        absolute_value k f /\ &0 < s /\ s <= &1
        ==> absolute_value k (\x. f x rpow s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[absolute_value] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RPOW_POS_LE; RPOW_EQ_0; REAL_LT_IMP_NZ; RPOW_MUL] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `((f:A->real) x + f y) rpow s` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; RING_ADD];
    MATCH_MP_TAC RPOW_ADD_LE THEN ASM_SIMP_TAC[]]);;

let NONARCHIMEDEAN_ABSOLUTE_VALUE_RPOW = prove
 (`!k (f:A->real) s.
        nonarchimedean_absolute_value k f /\ &0 < s
        ==> nonarchimedean_absolute_value k (\x. f x rpow s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONARCHIMEDEAN_ABSOLUTE_VALUE] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[RPOW_POS_LE; RPOW_EQ_0; REAL_LT_IMP_NZ; RPOW_MUL] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `max ((f:A->real) x rpow s) (f y rpow s) = (max (f x) (f y)) rpow s`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MAX_RPOW THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; RING_ADD] THEN
  ASM_SIMP_TAC[REAL_LE_MAX; RING_ADD]);;

(* ------------------------------------------------------------------------- *)
(* The approximation theorem of Artin and Whaples.                           *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTE_VALUE_POW_QUOTIENT = prove
 (`!k (f:A->real) y.
        field k /\ absolute_value k f /\ y IN ring_carrier k
        ==> (f y < &1
             ==> !e. &0 < e
                     ==> eventually
                          (\m. f(ring_div k (ring_pow k y m)
                                  (ring_add k (ring_1 k) (ring_pow k y m)))
                               < e) sequentially) /\
            (&1 < f y
             ==> !e. &0 < e
                     ==> eventually
                          (\m. f(ring_sub k
                                  (ring_div k (ring_pow k y m)
                                    (ring_add k (ring_1 k) (ring_pow k y m)))
                                  (ring_1 k)) < e) sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (f:A->real) y` ASSUME_TAC THENL
   [ASM_MESON_TAC[ABSOLUTE_VALUE_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. (f:A->real) y pow m - &1 <=
        f(ring_add k (ring_1 k) (ring_pow k y m)) /\
        &1 - f y pow m <= f(ring_add k (ring_1 k) (ring_pow k y m))`
  (LABEL_TAC "D") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `f:A->real`;
                   `ring_add k (ring_1 k) (ring_pow k y m):A`;
                   `ring_pow k y m:A`] ABSOLUTE_VALUE_ABS_SUB_LE) THEN
    MP_TAC(ISPECL [`k:A ring`; `f:A->real`;
                   `ring_add k (ring_1 k) (ring_pow k y m):A`;
                   `ring_1 k:A`] ABSOLUTE_VALUE_ABS_SUB_LE) THEN
    ASM_SIMP_TAC[RING_ADD; RING_1; RING_POW] THEN
    ASM_SIMP_TAC[RING_RULE
     `ring_sub k (ring_add k (ring_1 k) x) x = ring_1 k /\
      ring_sub k (ring_add k (ring_1 k) x) (ring_1 k) = (x:A)`;
      RING_POW; ABSOLUTE_VALUE_1; ABSOLUTE_VALUE_POW; FIELD_NONTRIVIAL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`(f:A->real) y`; `e / (&1 + e)`]
      REAL_POW_EVENTUALLY_LT) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < (e:real) ==> &0 < &1 + e`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    REMOVE_THEN "D" (MP_TAC o CONJUNCT2 o SPEC `m:num`) THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_DIV; RING_POW; RING_ADD; RING_1;
                 ABSOLUTE_VALUE_POW; FIELD_NONTRIVIAL] THEN
    ABBREV_TAC `D = (f:A->real)(ring_add k (ring_1 k) (ring_pow k y m))` THEN
    ABBREV_TAC `u = (f:A->real) y pow m` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (u:real) /\ u * (&1 + e) < e` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "u" THEN ASM_SIMP_TAC[REAL_POW_LE]; ALL_TAC] THEN
      UNDISCH_TAC `u < e / (&1 + e)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < (e:real) ==> &0 < &1 + e`];
      ALL_TAC] THEN
    SUBGOAL_THEN `e * (&1 - (u:real)) <= e * D` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real) < &1` ASSUME_TAC THENL
     [TRANS_TAC REAL_LT_TRANS `e / (&1 + e)` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ;
                   REAL_ARITH `&0 < (e:real) ==> &0 < &1 + e`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (D:real)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:A->real) y`; `&1 + inv e`] ARCH_EVENTUALLY_POW) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "D" (MP_TAC o CONJUNCT1 o SPEC `m:num`) THEN
  ABBREV_TAC `b = ring_add k (ring_1 k) (ring_pow k y m):A` THEN
  SUBGOAL_THEN `(b:A) IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_SIMP_TAC[RING_ADD; RING_1; RING_POW];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv e < (f:A->real) b` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(b:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `inv e < (f:A->real) b` THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0; REAL_NOT_LT; REAL_LE_INV_EQ;
                 REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub k (ring_div k (ring_pow k y m) b) (ring_1 k) =
    ring_neg k (ring_inv k b):A`
  SUBST1_TAC THENL
   [REWRITE_TAC[ring_div] THEN
    MP_TAC(ISPECL [`k:A ring`; `b:A`] FIELD_MUL_RINV) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ring_add k (ring_1 k) (ring_pow k y m):A = b` THEN
    SUBGOAL_THEN `ring_pow k y m:A IN ring_carrier k /\
                  ring_inv k b:A IN ring_carrier k`
    MP_TAC THENL [ASM_SIMP_TAC[RING_POW; RING_INV]; ALL_TAC] THEN
    SPEC_TAC(`ring_pow k y m:A`,`a:A`) THEN
    SPEC_TAC(`ring_inv k b:A`,`c:A`) THEN
    UNDISCH_TAC `(b:A) IN ring_carrier k` THEN
    SPEC_TAC(`b:A`,`b:A`) THEN
    RING_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_NEG; RING_INV; ABSOLUTE_VALUE_INV] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]);;

let ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE = prove
 (`!k (f1:A->real) f2.
        field k /\ absolute_value k f1 /\ absolute_value k f2 /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f1 x = &1)) /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f2 x = &1)) /\
        ~(?s. &0 < s /\ !x. x IN ring_carrier k ==> f2 x = f1 x rpow s)
        ==> ?z. z IN ring_carrier k /\ &1 < f1 z /\ f2 z < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~(?s. &0 < s /\ !x. x IN ring_carrier k ==> f1 x = (f2:A->real) x rpow s)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ABSOLUTE_VALUE_EQUIVALENT_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `f1:A->real`; `f2:A->real`]
    ABSOLUTE_VALUE_EQUIVALENT) THEN
  MP_TAC(ISPECL [`k:A ring`; `f2:A->real`; `f1:A->real`]
    ABSOLUTE_VALUE_EQUIVALENT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT]) THEN
  SUBGOAL_THEN
   `?a:A. a IN ring_carrier k /\ (f1:A->real) a < &1 /\ &1 <= (f2:A->real) a`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?b:A. b IN ring_carrier k /\ (f2:A->real) b < &1 /\ &1 <= (f1:A->real) b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(a:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 <= (f2:A->real) a` THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (f1:A->real) a /\ &0 < (f2:A->real) a`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `ring_div k b a:A` THEN
  ASM_SIMP_TAC[RING_DIV; ABSOLUTE_VALUE_DIV; REAL_LT_LDIV_EQ;
               REAL_LT_RDIV_EQ; REAL_MUL_LID] THEN
  ASM_REAL_ARITH_TAC);;

let ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT = prove
 (`!k (f:K->A->real) s i.
        field k /\ FINITE s /\ i IN s /\
        (!j. j IN s
             ==> absolute_value k (f j) /\
                 ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f j x = &1)) /\
        (!j. j IN s /\ ~(j = i)
             ==> ~(?c. &0 < c /\
                       !x. x IN ring_carrier k ==> f j x = f i x rpow c))
        ==> ?z. z IN ring_carrier k /\ &1 < f i z /\
                !j. j IN s /\ ~(j = i) ==> f j z < &1`,
  let EVENTUALLY_FORALL_FINITE = prove
   (`!net (p:K->A->bool) s.
        FINITE s
        ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
             !a. a IN s ==> eventually (p a) net)`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:K->bool = {}` THEN
    ASM_SIMP_TAC[EVENTUALLY_FORALL; NOT_IN_EMPTY; EVENTUALLY_TRUE]) in
  let RLEMMA = prove
   (`(!a b:real. &0 < a /\ inv a < b ==> &1 < a * b) /\
     (!a b:real. &0 < a /\ &0 <= b /\ b < inv a ==> a * b < &1) /\
     (!a b:real. &0 <= a /\ &0 <= b /\ b < inv(a + &1) ==> a * b < &1) /\
     (!a b:real. &1 <= a /\ &1 < b ==> &1 < a * b) /\
     (!a b:real. &0 <= a /\ a <= &1 /\ &0 <= b /\ b < &1 ==> a * b < &1)`,
    REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`a:real`; `inv a:real`; `b:real`] REAL_LT_LMUL) THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ];
      MP_TAC(ISPECL [`a:real`; `b:real`; `inv a:real`] REAL_LT_LMUL) THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ];
      TRANS_TAC REAL_LET_TRANS `a * inv(a + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH
         `&0 <= (a:real) ==> &0 < a + &1`] THEN
        REAL_ARITH_TAC];
      TRANS_TAC REAL_LTE_TRANS `b:real` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      TRANS_TAC REAL_LET_TRANS `b:real` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. FINITE t
        ==> t SUBSET s DELETE i
            ==> ?z. z IN ring_carrier k /\ &1 < (f:K->A->real) i z /\
                    !j. j IN t ==> f j z < &1`
  (MP_TAC o SPEC `s DELETE (i:K)`) THENL
   [ALL_TAC;
    ASM_SIMP_TAC[FINITE_DELETE; SUBSET_REFL; IN_DELETE]] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
    MP_TAC(ISPECL [`k:A ring`; `(f:K->A->real) i`]
      ABSOLUTE_VALUE_NONTRIVIAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:K`; `t:K->bool`] THEN
  REWRITE_TAC[INSERT_SUBSET; IN_DELETE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN REMOVE_THEN "ih" MP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  SUBGOAL_THEN
   `absolute_value k ((f:K->A->real) i) /\ absolute_value k (f j)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `(f:K->A->real) i`; `(f:K->A->real) j`]
    ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!l. l IN t ==> absolute_value k ((f:K->A->real) l)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `t SUBSET (s:K->bool) DELETE i` THEN
    REWRITE_TAC[SUBSET; IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 < (f:K->A->real) i w` THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (f:K->A->real) j w /\ &0 <= (f:K->A->real) i y /\
    &0 <= (f:K->A->real) j y /\
    !l. l IN t ==> &0 <= (f:K->A->real) l w /\ &0 <= f l y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT];
      ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
      ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
      ASM_MESON_TAC[ABSOLUTE_VALUE_POS]];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `(f:K->A->real) j y <= &1 \/ &1 < f j y`) THENL
   [SUBGOAL_THEN
     `eventually (\m. !l. l IN t
                    ==> (f:K->A->real) l y pow m * f l w < &1)
                 sequentially`
    MP_TAC THENL
     [ASM_SIMP_TAC[EVENTUALLY_FORALL_FINITE] THEN
      X_GEN_TAC `l:K` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(f:K->A->real) l y`; `inv((f:K->A->real) l w + &1)`]
        REAL_POW_EVENTUALLY_LT) THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH
       `&0 <= (a:real) ==> &0 < a + &1`] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC `m:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC(el 2 (CONJUNCTS RLEMMA)) THEN
      ASM_SIMP_TAC[REAL_POW_LE];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num` o BETA_RULE o
      MATCH_MP EVENTUALLY_HAPPENS_SEQUENTIALLY) THEN
    EXISTS_TAC `ring_mul k (ring_pow k y m) w:A` THEN
    ASM_SIMP_TAC[RING_MUL; RING_POW; ABSOLUTE_VALUE_MUL; ABSOLUTE_VALUE_POW;
                 FIELD_NONTRIVIAL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(el 3 (CONJUNCTS RLEMMA)) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(el 4 (CONJUNCTS RLEMMA)) THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; REAL_POW_1_LE]];
    ALL_TAC] THEN
  ABBREV_TAC
   `q = \m. ring_div k (ring_pow k y m)
              (ring_add k (ring_1 k) (ring_pow k y m)):A` THEN
  SUBGOAL_THEN `!m. (q:num->A) m IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    ASM_SIMP_TAC[RING_DIV; RING_ADD; RING_1; RING_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `eventually
     (\m. (f:K->A->real) i (ring_sub k (q m) (ring_1 k)) <
          &1 - inv(f i w) /\
          f j (ring_sub k (q m) (ring_1 k)) < inv(f j w) - &1 /\
          !l. l IN t ==> f l (q m) < inv(f l w + &1))
     sequentially`
  MP_TAC THENL
   [REWRITE_TAC[EVENTUALLY_AND] THEN ASM_SIMP_TAC[EVENTUALLY_FORALL_FINITE] THEN
    EXPAND_TAC "q" THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `(f:K->A->real) i`; `y:A`]
        ABSOLUTE_VALUE_POW_QUOTIENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_SIMP_TAC[REAL_SUB_LT; REAL_INV_LT_1];
      MP_TAC(ISPECL [`k:A ring`; `(f:K->A->real) j`; `y:A`]
        ABSOLUTE_VALUE_POW_QUOTIENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_SIMP_TAC[REAL_SUB_LT; REAL_INV_1_LT];
      X_GEN_TAC `l:K` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `(f:K->A->real) l`; `y:A`]
        ABSOLUTE_VALUE_POW_QUOTIENT) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ;
                   REAL_ARITH `&0 <= (a:real) ==> &0 < a + &1`]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o
    MATCH_MP EVENTUALLY_HAPPENS_SEQUENTIALLY) THEN
  EXISTS_TAC `ring_mul k w ((q:num->A) m)` THEN
  ASM_SIMP_TAC[RING_MUL; ABSOLUTE_VALUE_MUL] THEN
  SUBGOAL_THEN
   `!g:A->real. absolute_value k g
                ==> &1 - g(ring_sub k (q m) (ring_1 k)) <= g((q:num->A) m) /\
                    g(q m) <= &1 + g(ring_sub k (q m) (ring_1 k))`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:A->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `g:A->real`; `(q:num->A) m`; `ring_1 k:A`]
      ABSOLUTE_VALUE_ABS_SUB_LE) THEN
    ASM_SIMP_TAC[RING_1; ABSOLUTE_VALUE_1; FIELD_NONTRIVIAL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(el 0 (CONJUNCTS RLEMMA)) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:K->A->real) i`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(el 1 (CONJUNCTS RLEMMA)) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ABSOLUTE_VALUE_POS]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:K->A->real) j`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `l:K` THEN DISCH_TAC THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS RLEMMA)) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[ABSOLUTE_VALUE_POS]]);;

let ABSOLUTE_VALUE_WEAK_APPROXIMATION = prove
 (`!k (f:K->A->real) a s e.
        field k /\ FINITE s /\
        (!i. i IN s
             ==> absolute_value k (f i) /\
                 ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f i x = &1)) /\
        (!i j. i IN s /\ j IN s /\ ~(i = j)
               ==> ~(?c. &0 < c /\
                         !x. x IN ring_carrier k ==> f j x = f i x rpow c)) /\
        (!i. i IN s ==> a i IN ring_carrier k) /\ &0 < e
        ==> ?x. x IN ring_carrier k /\
                !i. i IN s ==> f i (ring_sub k x (a i)) < e`,
  let RLEMMA = prove
   (`!a b d. &0 <= a /\ &0 <= b /\ &0 < d /\ b < d / (a + &1)
             ==> a * b < d`,
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `b < d / (a + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ;
                 REAL_ARITH `&0 <= (a:real) ==> &0 < a + &1`] THEN
    ASM_REAL_ARITH_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:K->bool = {}` THENL
   [EXISTS_TAC `ring_0 k:A` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; RING_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN s
        ==> ?z. z IN ring_carrier k /\ &1 < (f:K->A->real) i z /\
                !j. j IN s /\ ~(j = i) ==> f j z < &1`
  MP_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MATCH_MP_TAC ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `z:K->A` o
      REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  ABBREV_TAC
   `q = \i m. ring_div k (ring_pow k ((z:K->A) i) m)
                (ring_add k (ring_1 k) (ring_pow k (z i) m))` THEN
  SUBGOAL_THEN `!i m. i IN s ==> (q:K->num->A) i m IN ring_carrier k`
  ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_DIV THEN
    ASM_SIMP_TAC[RING_ADD; RING_1; RING_POW];
    ALL_TAC] THEN
  ABBREV_TAC `d = e / &(CARD(s:K->bool))` THEN
  SUBGOAL_THEN `&0 < (d:real) /\ &(CARD(s:K->bool)) * d = e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(&0:real) < &(CARD(s:K->bool))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LT; CARD_EQ_0; LE_1]; ALL_TAC] THEN
    EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(&0:real) < &(CARD(s:K->bool))` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC
   `c = \i j m. if j = i
                then ring_mul k ((a:K->A) i)
                       (ring_sub k ((q:K->num->A) i m) (ring_1 k))
                else ring_mul k (a j) (q j m)` THEN
  SUBGOAL_THEN
   `eventually (\m. !i. i IN s ==> !j. j IN s
                    ==> (f:K->A->real) i ((c:K->K->num->A) i j m) < d)
               sequentially`
  MP_TAC THENL
   [ASM_SIMP_TAC[EVENTUALLY_FORALL] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `absolute_value k ((f:K->A->real) i)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:K->A) i IN ring_carrier k /\ (z:K->A) j IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (f:K->A->real) i (a i) /\ &0 <= f i (a j)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ABSOLUTE_VALUE_POS]; ALL_TAC] THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `j:K = i` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`k:A ring`; `(f:K->A->real) i`; `(z:K->A) i`]
        ABSOLUTE_VALUE_POW_QUOTIENT) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `d / ((f:K->A->real) i (a i) + &1)` o
        CONJUNCT2) THEN
      ASM_SIMP_TAC[REAL_LT_DIV;
                   REAL_ARITH `&0 <= (a:real) ==> &0 < a + &1`] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC `m:num` THEN EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `ring_sub k (ring_div k (ring_pow k ((z:K->A) i) m)
                      (ring_add k (ring_1 k) (ring_pow k (z i) m)))
                   (ring_1 k) IN ring_carrier k`
      ASSUME_TAC THENL
       [RING_CARRIER_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ABSOLUTE_VALUE_MUL] THEN MATCH_MP_TAC RLEMMA THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
      MP_TAC(ISPECL [`k:A ring`; `(f:K->A->real) i`; `(z:K->A) j`]
        ABSOLUTE_VALUE_POW_QUOTIENT) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `d / ((f:K->A->real) i ((a:K->A) j) + &1)` o
        CONJUNCT1) THEN
      ASM_SIMP_TAC[REAL_LT_DIV;
                   REAL_ARITH `&0 <= (a:real) ==> &0 < a + &1`] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC `m:num` THEN EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `ring_div k (ring_pow k ((z:K->A) j) m)
          (ring_add k (ring_1 k) (ring_pow k (z j) m)) IN ring_carrier k`
      ASSUME_TAC THENL
       [RING_CARRIER_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ABSOLUTE_VALUE_MUL] THEN MATCH_MP_TAC RLEMMA THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ABSOLUTE_VALUE_POS]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num` o BETA_RULE o
    MATCH_MP EVENTUALLY_HAPPENS_SEQUENTIALLY) THEN
  EXISTS_TAC
   `ring_sum k s (\j. ring_mul k ((a:K->A) j) ((q:K->num->A) j m))` THEN
  ASM_SIMP_TAC[RING_SUM] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_sub k (ring_sum k s (\j. ring_mul k ((a:K->A) j) ((q:K->num->A) j m)))
               (a i) =
    ring_sum k s (\j. (c:K->K->num->A) i j m)`
  SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `s = (i:K) INSERT (s DELETE i)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[INSERT_DELETE]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_SUM_CLAUSES; FINITE_DELETE; IN_DELETE; RING_MUL;
                 RING_SUB; RING_1] THEN
    SUBGOAL_THEN
     `ring_sum k (s DELETE i)
       (\j. if j = i
            then ring_mul k ((a:K->A) i)
                   (ring_sub k ((q:K->num->A) i m) (ring_1 k))
            else ring_mul k (a j) (q j m)) =
      ring_sum k (s DELETE i) (\j. ring_mul k (a j) (q j m))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_sum k (s DELETE i) (\j. ring_mul k ((a:K->A) j) ((q:K->num->A) j m))
      IN ring_carrier k /\ (a:K->A) i IN ring_carrier k /\
      (q:K->num->A) i m IN ring_carrier k`
    MP_TAC THENL [ASM_SIMP_TAC[RING_SUM]; ALL_TAC] THEN
    SPEC_TAC(`ring_sum k (s DELETE i)
               (\j. ring_mul k ((a:K->A) j) ((q:K->num->A) j m))`,`u:A`) THEN
    SPEC_TAC(`(a:K->A) i`,`v:A`) THEN
    SPEC_TAC(`(q:K->num->A) i m`,`w:A`) THEN
    RING_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j IN s ==> (c:K->K->num->A) i j m IN ring_carrier k`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL; RING_SUB; RING_1];
    ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
   `sum s (\j. (f:K->A->real) i ((c:K->K->num->A) i j m))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(BETA_RULE(ISPECL
     [`k:A ring`; `(f:K->A->real) i`; `\j. (c:K->K->num->A) i j m`;
      `s:K->bool`] ABSOLUTE_VALUE_RING_SUM)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME `&(CARD(s:K->bool)) * (d:real) = e`)) THEN
  MATCH_MP_TAC SUM_BOUND_LT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  EXISTS_TAC `i:K` THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Dedekind domains: the nonarchimedean absolute values bounded by 1 on the  *)
(* domain are the P-adic ones.                                               *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_VALUATION_ABSOLUTE_VALUE_NONTRIVIAL = prove
 (`!r k (h:A->B) P c (f:B->real).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\ &1 < c /\
        (!x. x IN ring_carrier k /\ ~(x = ring_0 k)
             ==> f x = c zpow --(dedekind_valuation (r,k) h P x))
        ==> ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ f x < &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  SUBGOAL_THEN `?a:A. a IN P /\ ~(a = ring_0 r)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
    REWRITE_TAC[ring_ideal] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `(h:A->B) a` THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier k /\ ~(h a = ring_0 k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; ring_monomorphism;
                  ring_homomorphism; SUBSET; IN_IMAGE];
    ASM_SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `a:A`]
    DEDEKIND_VALUATION_PRIME_IDEAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:real`;
                 `--(dedekind_valuation (r,k) (h:A->B) P (h a))`; `&0:int`]
    REAL_ZPOW_MONO_LT) THEN
  ASM_REWRITE_TAC[REAL_ZPOW_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_INT_ARITH_TAC);;

let DEDEKIND_ABSOLUTE_VALUE_PRIME = prove
 (`!r k (h:A->B) (f:B->real).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        nonarchimedean_absolute_value k f /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1)) /\
        (!a. a IN ring_carrier r ==> f(h a) <= &1)
        ==> prime_ideal r {a | a IN ring_carrier r /\ f(h a) < &1} /\
            ~({a | a IN ring_carrier r /\ f(h a) < &1} = {ring_0 r}) /\
            ?c. &1 < c /\
                !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                    ==> f x =
                        c zpow --(dedekind_valuation (r,k) h
                                   {a | a IN ring_carrier r /\ f(h a) < &1}
                                   x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nt")
     (LABEL_TAC "le1"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(fun th -> MAP_EVERY (fun t -> ASSUME_TAC(MATCH_MP t th))
   [RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_1; RING_HOMOMORPHISM_NEG;
    RING_HOMOMORPHISM_ADD; RING_HOMOMORPHISM_MUL]) THEN
  SUBGOAL_THEN `!a:A. a IN ring_carrier r ==> (h:A->B) a IN ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_homomorphism; SUBSET; IN_IMAGE]; ALL_TAC] THEN
  ABBREV_TAC `P = {a:A | a IN ring_carrier r /\ (f:B->real)(h a) < &1}` THEN
  SUBGOAL_THEN `prime_ideal r (P:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[prime_ideal; PROPER_IDEAL_ALT; ring_ideal] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; EXTENSION] THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[];
      REWRITE_TAC[RING_0];
      ASM_SIMP_TAC[RING_0; ABSOLUTE_VALUE_0;
                   REAL_LT_01];
      ASM_SIMP_TAC[RING_NEG; ABSOLUTE_VALUE_NEG];
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[RING_ADD] THEN
      TRANS_TAC REAL_LET_TRANS `max ((f:B->real)(h(x:A))) (f(h y))` THEN
      ASM_REWRITE_TAC[REAL_MAX_LT] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [nonarchimedean_absolute_value]) THEN
      ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[RING_MUL; ABSOLUTE_VALUE_MUL] THEN
      TRANS_TAC REAL_LET_TRANS `(f:B->real)(h(y:A))` THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
      DISCH_THEN(MP_TAC o SPEC `ring_1 r:A`) THEN
      ASM_SIMP_TAC[RING_1; ABSOLUTE_VALUE_1;
                   FIELD_NONTRIVIAL; REAL_LT_REFL];
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `(f:B->real)(h(ring_mul r x y:A)) < &1` THEN
      ASM_SIMP_TAC[ABSOLUTE_VALUE_MUL] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(P = {ring_0 r:A})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:B ring`; `f:B->real`] ABSOLUTE_VALUE_NONTRIVIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    USE_THEN "nt" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
      FIELD_FRACTION_NONZERO) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:A) IN P` MP_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[IN_SING]] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ring_mul k ((h:A->B) b) x = h a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[ABSOLUTE_VALUE_MUL] THEN
    TRANS_TAC REAL_LET_TRANS `(f:B->real) x` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `g = \x. if x = ring_0 k then &0
            else &2 zpow --(dedekind_valuation (r,k) (h:A->B) P x)` THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `&2:real`;
                 `g:B->real`] DEDEKIND_VALUATION_ABSOLUTE_VALUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `&2:real`;
                 `g:B->real`] DEDEKIND_VALUATION_ABSOLUTE_VALUE_NONTRIVIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    EXPAND_TAC "g" THEN SIMP_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:B ring`; `g:B->real`; `f:B->real`]
    ABSOLUTE_VALUE_EQUIVALENT_LE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE] THEN
    ASM_MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `x = ring_0 k \/ &0 <= dedekind_valuation (r,k) (h:A->B) P x`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`]
      DEDEKIND_VALUATION_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(f:B->real)(h(b:A)) = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `~((b:A) IN P)` THEN EXPAND_TAC "P" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
      MATCH_MP_TAC(REAL_ARITH `(x:real) <= &1 ==> &1 <= x ==> x = &1`) THEN
      USE_THEN "le1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ring_mul k ((h:A->B) b) x = h a` THEN
    DISCH_THEN(MP_TAC o AP_TERM `f:B->real`) THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_MUL; REAL_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `&2 rpow s` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LT_1 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:B` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  EXPAND_TAC "g" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_ZPOW_RPOW THEN REAL_ARITH_TAC);;

let DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE = prove
 (`!r k (h:A->B) P Q c d.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        prime_ideal r Q /\ ~(Q = {ring_0 r}) /\ &1 < c /\ &1 < d /\
        (!x. x IN ring_carrier k /\ ~(x = ring_0 k)
             ==> c zpow --(dedekind_valuation (r,k) h P x) =
                 d zpow --(dedekind_valuation (r,k) h Q x))
        ==> P = Q /\ c = d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "eq"))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  SUBGOAL_THEN `!a:A. a IN ring_carrier r ==> (h:A->B) a IN ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; ring_homomorphism;
                  SUBSET; IN_IMAGE];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `{Q:A->bool}`;
                   `\P:A->bool. --(&1):int`]
      DEDEKIND_VALUATION_WEAK_APPROXIMATION) THEN
    ASM_REWRITE_TAC[FINITE_SING; IN_SING; FORALL_UNWIND_THM2] THEN
    ASM_SIMP_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "eq" (MP_TAC o SPEC `x:B`) THEN
    ASM_REWRITE_TAC[INT_NEG_NEG; REAL_ZPOW_1]] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?a:A. a IN P /\ ~(a IN Q)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `P:A->bool`]
      DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL) THEN
    ASM_REWRITE_TAC[maximal_ideal] THEN
    DISCH_THEN(MP_TAC o SPEC `Q:A->bool` o
      REWRITE_RULE[NOT_EXISTS_THM] o CONJUNCT2) THEN
    ASM_SIMP_TAC[PRIME_IMP_PROPER_IDEAL; PSUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier r /\ ~(a = ring_0 r)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[PRIME_IDEAL_IMP_SUBSET; SUBSET];
      DISCH_TAC THEN UNDISCH_TAC `~((a:A) IN Q)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IN_RING_IDEAL_0 THEN ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dedekind_valuation (r,k) (h:A->B) Q (h a) = &0 /\
    &0 < dedekind_valuation (r,k) h P (h a)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `Q:A->bool`; `a:A`]
        DEDEKIND_VALUATION_PRIME_IDEAL) THEN
      MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `Q:A->bool`; `a:A`]
        DEDEKIND_VALUATION_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_EQ] THEN ARITH_TAC;
      MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `a:A`]
        DEDEKIND_VALUATION_PRIME_IDEAL) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "eq" (MP_TAC o SPEC `(h:A->B) a`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_NEG_0; REAL_ZPOW_0] THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  MP_TAC(ISPECL [`c:real`;
                 `--(dedekind_valuation (r,k) (h:A->B) P (h a))`; `&0:int`]
    REAL_ZPOW_MONO_LT) THEN
  ASM_REWRITE_TAC[REAL_ZPOW_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_INT_ARITH_TAC);;

let DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE = prove
 (`!r k (h:A->B) (f:B->real).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        nonarchimedean_absolute_value k f /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1)) /\
        (!a. a IN ring_carrier r ==> f(h a) <= &1)
        ==> ?!P. prime_ideal r P /\ ~(P = {ring_0 r}) /\
                 ?c. &1 < c /\
                     !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                         ==> f x = c zpow --(dedekind_valuation (r,k) h P x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `{a | a IN ring_carrier r /\ (f:B->real)((h:A->B) a) < &1}` THEN
    MATCH_MP_TAC DEDEKIND_ABSOLUTE_VALUE_PRIME THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`P:A->bool`; `Q:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)))
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `Q:A->bool`;
                 `c:real`; `d:real`]
    DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:B` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
