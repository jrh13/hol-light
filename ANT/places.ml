(* ========================================================================= *)
(* Places of number fields and of the rationals: the nontrivial              *)
(* nonarchimedean absolute values of a number field are the P-adic ones,     *)
(* Ostrowski theorem for the prime subfield of a field of characteristic 0,  *)
(* for any field of characteristic 0 that is its own prime subfield and for  *)
(* the rational field (the prime subfield of the reals,                      *)
(* subfield_generated real_ring {&0}), and the product formula for the       *)
(* rationals over all of their places.                                       *)
(*                                                                           *)
(* Main results, with O = ring_of_integers k and                             *)
(* v_P = dedekind_valuation (O,k) I P as in ANT/nf_valuation.ml:             *)
(*                                                                           *)
(*   f nonarchimedean on a field ==> f <= 1 on O                             *)
(*      (NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS)                     *)
(*   k number field, f nonarchimedean and nontrivial ==> f x = c zpow        *)
(*      --v_P(x) (x <> 0) for exactly one nonzero prime P of O and some      *)
(*      c > 1 (NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE); equivalently f   *)
(*      is equivalent to exactly one of the normalized |.|_P = N(P) zpow     *)
(*      --v_P (NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE_EQUIVALENT), those *)
(*      of the product formula of ANT/product_formula.ml; the norm(g         *)
(*      x) of the complex embeddings g are archimedean                       *)
(*      (COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE_ARCHIMEDEAN), so by               *)
(*      NONARCHIMEDEAN_ABSOLUTE_VALUE_RPOW equivalent to no P-adic one       *)
(*   Ostrowski: on the prime subfield of a field k of characteristic 0 a     *)
(*      nontrivial absolute value is, if archimedean, n |-> n rpow s on the  *)
(*      natural numbers for some 0 < s <= 1, and if nonarchimedean the       *)
(*      P-adic one for P = pO with p prime, for exactly one p                *)
(*      (OSTROWSKI_PRIME_SUBFIELD); if k is its own prime subfield (a number *)
(*      field of degree 1, NUMBER_FIELD_DEGREE_EQ_1), the archimedean ones   *)
(*      are x |-> abs(g x) rpow s for the ring homomorphism g from k to the  *)
(*      reals (OSTROWSKI); on the rational field they are abs rpow s         *)
(*      (OSTROWSKI_RATIONAL)                                                 *)
(*   for nonzero rational x, the product over the primes p of the            *)
(*      p zpow --v_p(x) (finitely many <> 1) times abs x is 1                *)
(*      (RATIONAL_PRODUCT_FORMULA)                                           *)
(*                                                                           *)
(* The archimedean absolute values of a number field (equivalent to the      *)
(* norm(g x) for the embeddings g into C) are not treated here: they need    *)
(* completions or the norm topology of k (x) R.                              *)
(*                                                                           *)
(* Routes. Number fields: an algebraic integer is integral over Z, on which  *)
(* a nonarchimedean f is <= 1 (NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL of     *)
(* ANT/dedekind_absolute.ml), so DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE      *)
(* applies to O, a Dedekind domain with fraction field k. Ostrowski,         *)
(* archimedean case: g n = f(n) is multiplicative and subadditive with g n > *)
(* 1 for some n; writing N in base b gives g(N) <= b (d + 1) max(1, g b)^d   *)
(* for N < b^(d + 1) (OSTROWSKI_DIGITS_LEMMA), applied to m^k this gives g m *)
(* <= max(1, g b) rpow (log m / log b) (OSTROWSKI_BOUND_LEMMA), so g > 1 on  *)
(* all m >= 2 and log g m / log m is constant (OSTROWSKI_NUM_LEMMA).         *)
(* Nonarchimedean case: the prime subfield is a number field whose nonzero   *)
(* primes are the pO (RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL of         *)
(* ANT/relative_split.ml), with pO = qO only for p = q                       *)
(* (PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ). A field that is its own prime  *)
(* subfield consists of the quotients a / b of integers                      *)
(* (PRIME_SUBFIELD_CHAR_0), with f(a / b) = f(a) / f(b) and g(a / b) = a / b *)
(* for a ring homomorphism g into the reals (OSTROWSKI). Product formula:    *)
(* the case of NUMBER_FIELD_PRODUCT_FORMULA for the rational field, which    *)
(* has one complex embedding, the inclusion                                  *)
(* (RATIONAL_FIELD_COMPLEX_EMBEDDINGS), so N(pO) = p                         *)
(* (NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS).                           *)
(*                                                                           *)
(* Uses: ANT/absolute_values.ml, ANT/numfield.ml, ANT/ring_of_integers.ml,   *)
(* ANT/nf_valuation.ml, ANT/ideal_norm.ml, ANT/prime_split.ml,               *)
(* ANT/relative_split.ml, ANT/complex_embeddings.ml, ANT/infinite_places.ml  *)
(* and ANT/product_formula.ml (and with them Multivariate/cauchy.ml). Also   *)
(* Multivariate/complex_ring.ml (complex_ring) and                           *)
(* Multivariate/transcendentals.ml (log, rpow).                              *)
(* ========================================================================= *)

needs "Library/products.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/nf_valuation.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/infinite_places.ml";;
needs "ANT/product_formula.ml";;
needs "ANT/absolute_values.ml";;
needs "Multivariate/complex_ring.ml";;
needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* Absolute values of number fields: the nonarchimedean ones are the P-adic  *)
(* ones, those of the complex embeddings are archimedean.                    *)
(* ------------------------------------------------------------------------- *)

let NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS = prove
 (`!k (f:A->real) x.
        field k /\ nonarchimedean_absolute_value k f /\
        x IN ring_carrier(ring_of_integers k)
        ==> f x <= &1`,
  REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`integer_ring`; `k:A ring`; `ring_of_int k:int->A`]
    NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
  ASM_SIMP_TAC[NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT]);;

let NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE = prove
 (`!k (f:A->real).
        number_field k /\ nonarchimedean_absolute_value k f /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1))
        ==> ?!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                 ?c. &1 < c /\
                     !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                         ==> f x = c zpow
                                   --(dedekind_valuation
                                       (ring_of_integers k,k) I P x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`;
                 `f:A->real`] DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS; I_THM] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS THEN
  EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[NUMBER_FIELD_IMP_FIELD]);;

let NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE_EQUIVALENT = prove
 (`!k (f:A->real).
        number_field k /\ nonarchimedean_absolute_value k f /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1))
        ==> ?!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                 ?s. &0 < s /\
                     !x. x IN ring_carrier k
                         ==> f x =
                             (if x = ring_0 k then &0
                              else &(ideal_norm (ring_of_integers k) P) zpow
                                   --(dedekind_valuation
                                       (ring_of_integers k,k) I P x))
                             rpow s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN ASSUME_TAC(CONJUNCT1 th) THEN
                       ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE) THEN
  MATCH_MP_TAC(MESON[]
   `(!P:A->bool. Q1 P /\ Q2 P ==> (R P <=> S P))
    ==> (?!P. Q1 P /\ Q2 P /\ R P) ==> (?!P. Q1 P /\ Q2 P /\ S P)`) THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&1:real) < &(ideal_norm (ring_of_integers k) (P:A->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_PROPER_IDEAL) THEN
      SIMP_TAC[PROPER_IDEAL_ALT];
      MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL]];
    ALL_TAC] THEN
  ABBREV_TAC `N = &(ideal_norm (ring_of_integers k) (P:A->bool)):real` THEN
  SUBGOAL_THEN `(f:A->real)(ring_0 k) = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[ABSOLUTE_VALUE_0; NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `log c / log N` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; LOG_POS_LT] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[RPOW_ZERO; REAL_LT_IMP_NZ; REAL_LT_DIV; LOG_POS_LT] THEN
    ASM_SIMP_TAC[REAL_ZPOW_RPOW; REAL_ARITH `&1 < (N:real) ==> &0 < N`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[rpow; REAL_ARITH `&1 < (N:real) ==> &0 < N`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; LOG_POS_LT; EXP_LOG;
                 REAL_ARITH `&1 < (c:real) ==> &0 < c`];
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N rpow s` THEN ASM_SIMP_TAC[RPOW_LT_1] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_ZPOW_RPOW THEN ASM_REAL_ARITH_TAC]);;

let COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE_ARCHIMEDEAN = prove
 (`!k (g:A->complex).
        field k /\ g IN complex_embeddings k
        ==> ~nonarchimedean_absolute_value k (\x. norm(g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `\x. norm((g:A->complex) x)`]
    NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED) THEN
  ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE] THEN
  DISCH_THEN(MP_TAC o SPEC `&2:int` o CONJUNCT1) THEN
  SUBGOAL_THEN `ring_homomorphism(k,complex_ring) (g:A->complex)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPLEX_EMBEDDINGS_MONOMORPHISM;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT
    th]) THEN
  REWRITE_TAC[COMPLEX_RING_OF_INT; COMPLEX_NORM_CX; int_of_num_th] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Ostrowski theorem: multiplicative subadditive functions on the natural    *)
(* numbers, the prime subfield of a field of characteristic 0, fields of     *)
(* characteristic 0 that are their own prime subfield, the rational field.   *)
(* ------------------------------------------------------------------------- *)

let OSTROWSKI_DIGITS_LEMMA = prove
 (`!(g:num->real) b.
         (!m n. g(m * n) = g m * g n) /\ (!m n. g(m + n) <= g m + g n) /\
         (!n. &0 <= g n) /\ (!n. g n <= &n) /\ 2 <= b
         ==> !d N. N < b EXP (d + 1)
                   ==> g N <= &b * &(d + 1) * max (&1) (g b) pow d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= max (&1) ((g:num->real) b) /\ g b <= max (&1) (g b)`
  STRIP_ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M = max (&1) ((g:num->real) b)` THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; EXP_1; real_pow; REAL_MUL_RID] THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `&N:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE; LT_IMP_LE];
    ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`N:num`; `b:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ONCE_REWRITE_TAC[th]) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N DIV b`) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN
    UNDISCH_TAC `N < b EXP (SUC d + 1)` THEN
    REWRITE_TAC[ADD1; EXP_ADD; EXP_1] THEN ARITH_TAC;
    DISCH_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(g:num->real)(N DIV b) * g b + g(N MOD b)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:num->real)(N MOD b) <= &b` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&(N MOD b):real` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE; LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:num->real)(N DIV b) * g b <= (&b * &(d + 1) * M pow d) * M`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (M:real) * M pow d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&b <= &b * (M:real) * M pow d` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_ADD]) THEN
  ASM_REAL_ARITH_TAC);;

let OSTROWSKI_BOUND_LEMMA = prove
 (`!g. (!m n. g(m * n) = g m * g n) /\ (!m n. g(m + n) <= g m + g n) /\
       (!n. &0 <= g n) /\ g 1 = &1 /\ (!n. g n <= &n)
       ==> !m b. 2 <= m /\ 2 <= b
                 ==> g m <= max (&1) (g b) rpow (log(&m) / log(&b))`,
  GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `b:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!n k. (g:num->real)(n EXP k) = g n pow k` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; real_pow]; ALL_TAC] THEN
  ABBREV_TAC `M = max (&1) ((g:num->real) b)` THEN
  SUBGOAL_THEN `&1 <= (M:real)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&m) /\ &0 < log(&b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = log(&m) / log(&b)` THEN
  SUBGOAL_THEN `&0 < (L:real)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  ABBREV_TAC `R = M rpow L` THEN
  SUBGOAL_THEN `&1 <= (R:real)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC RPOW_LE_1 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(g:num->real) m / R`; `&b * (L:real)`; `&b:real`]
    REAL_POW_EVENTUALLY_GT_LINEAR) THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&1 <= (R:real) ==> &0 < R`;
               REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N + 1`)) THEN
  REWRITE_TAC[ARITH_RULE `N <= N + 1`; REAL_NOT_LT] THEN
  ABBREV_TAC `k = N + 1` THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC;
                                         ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. m EXP k < b EXP (d + 1) /\ (!e. e < d ==> ~(m EXP k < b EXP (e + 1)))`
  (X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min")))
  THENL
   [GEN_REWRITE_TAC I [GSYM(REWRITE_RULE[] (ISPEC
      `\d. m EXP k < b EXP (d + 1)` num_WOP))] THEN
    EXISTS_TAC `m EXP k` THEN
    TRANS_TAC LTE_TRANS `2 EXP (m EXP k)` THEN REWRITE_TAC[LT_POW2_REFL] THEN
    TRANS_TAC LE_TRANS `b EXP (m EXP k)` THEN
    ASM_REWRITE_TAC[EXP_MONO_LE; LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b EXP d <= m EXP k` ASSUME_TAC THENL
   [ASM_CASES_TAC `d = 0` THENL
     [ASM_REWRITE_TAC[EXP; ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      REMOVE_THEN "min" (MP_TAC o SPEC `d - 1`) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(d = 0) ==> d - 1 < d /\ d - 1 + 1 = d`] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&d <= &k * (L:real)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    ASM_SIMP_TAC[REAL_ARITH `&k * x / y = (&k * x) / y`; REAL_LE_RDIV_EQ] THEN
    ASM_SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; LE_1;
                 ARITH_RULE `2 <= n ==> 0 < n`] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_OF_NUM_POW;
                 REAL_OF_NUM_LE; ARITH_RULE `2 <= n ==> 0 < n`] THEN
    REWRITE_TAC[EXP_LT_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:num->real) m pow k <= &b * (&k * L + &1) * R pow k`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:num->real) m pow k = g(m EXP k)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&b * &(d + 1) * (M:real) pow d` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`g:num->real`; `b:num`] OSTROWSKI_DIGITS_LEMMA) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= (M:real) ==> &0 <= M`];
      EXPAND_TAC "R" THEN
      ASM_SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW;
                   REAL_ARITH `&1 <= (M:real) ==> &0 <= M`]
      THEN MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT;
               REAL_ARITH `&1 <= (R:real) ==> &0 < R`] THEN
  UNDISCH_TAC `(g:num->real) m pow k <= &b * (&k * L + &1) * R pow k` THEN
  REAL_ARITH_TAC);;

let OSTROWSKI_NUM_LEMMA = prove
 (`!g. g 0 = &0 /\ g 1 = &1 /\ (!n. &0 <= g n) /\
       (!m n. g(m * n) = g m * g n) /\ (!m n. g(m + n) <= g m + g n) /\
       (?n. &1 < g n)
       ==> ?s. &0 < s /\ !n. g n = &n rpow s`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `n0:num`)))))) THEN
  SUBGOAL_THEN `!n. (g:num->real) n <= &n` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
    TRANS_TAC REAL_LE_TRANS `(g:num->real) n + g 1` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[REAL_LE_RADD]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `g:num->real` OSTROWSKI_BOUND_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "bd") THEN
  SUBGOAL_THEN `2 <= n0` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) /\ ~(n = 1) ==> 2 <= n`) THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. 2 <= m ==> &1 < (g:num->real) m` ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o SPECL [`n0:num`; `m:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `max (&1) ((g:num->real) m) = &1` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RPOW_ONE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m b. 2 <= m /\ 2 <= b
          ==> log((g:num->real) m) / log(&m) <= log(g b) / log(&b)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `b:num`] THEN STRIP_TAC THEN
    USE_THEN "bd" (MP_TAC o SPECL [`m:num`; `b:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `max (&1) ((g:num->real) b) = g b` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 < (x:real) ==> max (&1) x = x`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < log(&m) /\ &0 < log(&b) /\ &1 < (g:num->real) m /\ &1 < g b`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM LOG_MONO_LE; RPOW_POS_LT;
                 REAL_ARITH `&1 < (x:real) ==> &0 < x`; LOG_RPOW] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `(x / y) * (z:real) = (z * x) / y`;
                 REAL_LE_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < (g:num->real) 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log((g:num->real) 2) / log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `log((g:num->real) 2) / log(&2)` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_SIMP_TAC[RPOW_ZERO; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THENL
   [ASM_REWRITE_TAC[RPOW_ONE]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&m) /\ &0 < log(&2) /\ &1 < (g:num->real) m`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log((g:num->real) m) / log(&m) = log(g 2) / log(&2)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[rpow; REAL_OF_NUM_LT; ARITH_RULE `2 <= m ==> 0 < m`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; EXP_LOG;
               REAL_ARITH `&1 < (x:real) ==> &0 < x`]);;

let PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ = prove
 (`!k:A ring p q.
        field k /\ ring_char k = 0 /\ prime p /\ prime q
        ==> (ideal_generated
              (ring_of_integers(subfield_generated k {ring_0 k}))
              {ring_of_num k p} =
             ideal_generated
              (ring_of_integers(subfield_generated k {ring_0 k}))
              {ring_of_num k q} <=>
             p = q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ABBREV_TAC `O = ring_of_integers(subfield_generated k {ring_0 k:A})` THEN
  DISCH_THEN(LABEL_TAC "eq") THEN
  SUBGOAL_THEN `ring_of_num O = ring_of_num (k:A ring) /\
                ring_of_int O = ring_of_int (k:A ring)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    REWRITE_TAC[RING_OF_INTEGERS; RING_OF_NUM_SUBFIELD_GENERATED;
                RING_OF_INT_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `prime_ideal O (ideal_generated O {ring_of_num k q:A})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `ideal_generated O {ring_of_num k q:A}`]
      RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ring_of_num k n IN ideal_generated O {ring_of_num k n:A}`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
    REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[RING_OF_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:A ring`; `ideal_generated O {ring_of_num k q:A}`;
                 `q:num`] RING_OF_INT_IN_PRIME_IDEAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&p:int`) THEN
  REWRITE_TAC[RING_OF_INT_OF_NUM] THEN
  REMOVE_THEN "eq" (SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[GSYM num_divides] THEN
  ASM_MESON_TAC[DIVIDES_PRIME_PRIME]);;

let OSTROWSKI_PRIME_SUBFIELD = prove
 (`!k (f:A->real).
        field k /\ ring_char k = 0 /\
        absolute_value (subfield_generated k {ring_0 k}) f /\
        (?x. x IN ring_carrier(subfield_generated k {ring_0 k}) /\
             ~(x = ring_0 k) /\ ~(f x = &1))
        ==> (~nonarchimedean_absolute_value (subfield_generated k {ring_0 k}) f
             ==> ?s. &0 < s /\ s <= &1 /\
                     !n. f(ring_of_num k n) = &n rpow s) /\
            (nonarchimedean_absolute_value (subfield_generated k {ring_0 k}) f
             ==> ?!p. prime p /\
                      ?c. &1 < c /\
                          !x. x IN
                              ring_carrier(subfield_generated k {ring_0 k}) /\
                              ~(x = ring_0 k)
                              ==> f x =
                                  c zpow
                                  --(dedekind_valuation
                                      (ring_of_integers
                                        (subfield_generated k {ring_0 k}),
                                       subfield_generated k {ring_0 k}) I
                                      (ideal_generated
                                        (ring_of_integers
                                          (subfield_generated k {ring_0 k}))
                                        {ring_of_num k p}) x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = subfield_generated k {ring_0 k:A}` THEN
  SUBGOAL_THEN
   `ring_0 Q:A = ring_0 k /\ ring_1 Q = ring_1 k /\
    ring_neg Q = ring_neg k /\ ring_add Q = ring_add k /\
    ring_mul Q = ring_mul k /\ ring_of_num Q = ring_of_num k /\
    ring_of_int Q = ring_of_int k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[SUBFIELD_GENERATED; RING_OF_NUM_SUBFIELD_GENERATED;
                RING_OF_INT_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `!n. ring_of_num k n:A IN ring_carrier Q` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_NUM]; ALL_TAC] THEN
    MP_TAC(ISPEC `\n. (f:A->real)(ring_of_num k n)` OSTROWSKI_NUM_LEMMA) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`Q:A ring`; `f:A->real`; `2`]
        ABSOLUTE_VALUE_RING_OF_NUM_LE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`s:real`; `(&1:real)`; `(&2:real)`] RPOW_MONO_LE_EQ) THEN
      REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN ASM_REAL_ARITH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ring_of_num] THEN
      ASM_MESON_TAC[ABSOLUTE_VALUE_0];
      REWRITE_TAC[RING_OF_NUM_1] THEN
      ASM_MESON_TAC[ABSOLUTE_VALUE_1; FIELD_NONTRIVIAL];
      ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
      REWRITE_TAC[RING_OF_NUM_MUL] THEN ASM_MESON_TAC[ABSOLUTE_VALUE_MUL];
      REWRITE_TAC[RING_OF_NUM_ADD] THEN
      ASM_MESON_TAC[ABSOLUTE_VALUE_TRIANGLE];
      ALL_TAC] THEN
    UNDISCH_TAC `~nonarchimedean_absolute_value Q (f:A->real)` THEN
    MP_TAC(ISPECL [`Q:A ring`; `f:A->real`]
      NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE; FORALL_INT_CASES;
                EXISTS_INT_CASES] THEN
    REWRITE_TAC[RING_OF_INT_CASES] THEN
    ASM_MESON_TAC[ABSOLUTE_VALUE_NEG];
    DISCH_TAC] THEN
  SUBGOAL_THEN `number_field(Q:A ring)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN ASM_SIMP_TAC[NUMBER_FIELD_PRIME_SUBFIELD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. prime_ideal (ring_of_integers Q) P /\ ~(P = {ring_0 k}) <=>
        ?p. prime p /\
            P = ideal_generated (ring_of_integers Q) {ring_of_num k p:A}`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. prime p /\ prime q /\
          ideal_generated (ring_of_integers Q) {ring_of_num k p} =
          ideal_generated (ring_of_integers Q) {ring_of_num k q:A}
          ==> p = q`
  (LABEL_TAC "inj") THENL
   [EXPAND_TAC "Q" THEN ASM_MESON_TAC[PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:A ring`; `f:A->real`]
    NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; ASSUME `ring_0 Q:A = ring_0 k`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `P:A->bool` STRIP_ASSUME_TAC)
    (LABEL_TAC "un")) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `?p. prime p /\
          P = ideal_generated (ring_of_integers Q) {ring_of_num k p:A}`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `P:A->bool`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "un" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* Ostrowski for any field k of characteristic 0 that is its own prime       *)
(* subfield, equivalently a number field of degree 1                         *)
(* (NUMBER_FIELD_DEGREE_EQ_1). The ring homomorphism g from k to the reals   *)
(* in the archimedean case exists (PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) and   *)
(* is unique on k (RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED). The       *)
(* rational field is the case g = I (OSTROWSKI_RATIONAL).                    *)
let OSTROWSKI = prove
 (`!k (f:A->real).
        field k /\ ring_char k = 0 /\
        ring_carrier(subfield_generated k {ring_0 k}) = ring_carrier k /\
        absolute_value k f /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1))
        ==> (~nonarchimedean_absolute_value k f
             ==> ?s. &0 < s /\ s <= &1 /\
                     !g x. ring_homomorphism(k,real_ring) g /\
                           x IN ring_carrier k
                           ==> f x = abs(g x) rpow s) /\
            (nonarchimedean_absolute_value k f
             ==> ?!p. prime p /\
                      ?c. &1 < c /\
                          !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                              ==> f x =
                                  c zpow
                                  --(dedekind_valuation
                                      (ring_of_integers k,k) I
                                      (ideal_generated (ring_of_integers k)
                                        {ring_of_num k p}) x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `subfield_generated k {ring_0 k} = (k:A ring)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBFIELD_GENERATED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`] OSTROWSKI_PRIME_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> r) ==> p /\ q ==> r /\ q`) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g:A->real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a. (f:A->real)(ring_of_int k a) = abs(real_of_int a) rpow s`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_INT_CASES; RING_OF_INT_CASES; int_of_num_th;
                int_neg_th; REAL_ABS_NEG; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_NEG; RING_OF_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:A ring` PRIME_SUBFIELD_CHAR_0) THEN
  ASM_REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `real_ring`; `g:A->real`]
    FIELD_HOMOMORPHISM_DIV) THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_DIV; RING_OF_INT; REAL_RING_DIV] THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT
    th]) THEN
  REWRITE_TAC[REAL_RING_OF_INT; REAL_ABS_DIV; RPOW_DIV]);;

let OSTROWSKI_RATIONAL = prove
 (`!f. absolute_value (subfield_generated real_ring {&0}) f /\
       (?x. x IN ring_carrier(subfield_generated real_ring {&0}) /\
            ~(x = &0) /\ ~(f x = &1))
       ==> (~nonarchimedean_absolute_value (subfield_generated real_ring {&0}) f
            ==> ?s. &0 < s /\ s <= &1 /\
                    !x. x IN ring_carrier(subfield_generated real_ring {&0})
                        ==> f x = abs x rpow s) /\
           (nonarchimedean_absolute_value (subfield_generated real_ring {&0}) f
            ==> ?!p. prime p /\
                     ?c. &1 < c /\
                         !x. x IN ring_carrier
                                   (subfield_generated real_ring {&0}) /\
                             ~(x = &0)
                             ==> f x =
                                 c zpow
                                 --(dedekind_valuation
                                     (ring_of_integers
                                       (subfield_generated real_ring {&0}),
                                      subfield_generated real_ring {&0}) I
                                     (ideal_generated
                                       (ring_of_integers
                                         (subfield_generated real_ring {&0}))
                                       {&p}) x))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subfield_generated real_ring {&0}`; `f:real->real`]
    OSTROWSKI) THEN
  REWRITE_TAC[PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[RING_CHAR_SUBFIELD_GENERATED; CONJUNCT2 SUBFIELD_GENERATED;
              RING_OF_NUM_SUBFIELD_GENERATED; REAL_RING_CLAUSES;
              REAL_RING_CHAR; REAL_RING_OF_NUM] THEN
  SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_REAL_RING] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> r) ==> p /\ q ==> r /\ q`) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`I:real->real`; `y:real`]) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* The product formula for the rationals over all of their places.           *)
(* ------------------------------------------------------------------------- *)

let RATIONAL_FIELD_COMPLEX_EMBEDDINGS = prove
 (`complex_embeddings(subfield_generated real_ring {&0}) HAS_SIZE 1 /\
   !g x. g IN complex_embeddings(subfield_generated real_ring {&0}) /\
         x IN ring_carrier(subfield_generated real_ring {&0})
         ==> g x = Cx x`,
  ABBREV_TAC `Q = subfield_generated real_ring {&0}` THEN
  SUBGOAL_THEN `number_field (Q:real ring) /\ field Q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    SIMP_TAC[NUMBER_FIELD_RATIONAL_FIELD; FIELD_SUBFIELD_GENERATED;
             FIELD_REAL_RING];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `Q:real ring` COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    EXPAND_TAC "Q" THEN
    REWRITE_TAC[PRIME_SUBFIELD_SUBFIELD_GENERATED; REAL_RING_CLAUSES] THEN
    MP_TAC(ISPEC `real_ring` NUMBER_FIELD_PRIME_SUBFIELD) THEN
    REWRITE_TAC[FIELD_REAL_RING; REAL_RING_CHAR; REAL_RING_CLAUSES] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:real->complex`; `x:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(Q,complex_ring) (g:real->complex)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPLEX_EMBEDDINGS_MONOMORPHISM;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_carrier Q = {real_of_int a / real_of_int b | a,b | ~(b = &0)} /\
    ring_mul Q = ( * ) /\ ring_of_int Q = real_of_int`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    MP_TAC(ISPEC `real_ring` PRIME_SUBFIELD_CHAR_0) THEN
    REWRITE_TAC[FIELD_REAL_RING; REAL_RING_CHAR; REAL_RING_CLAUSES;
                REAL_RING_OF_INT; REAL_RING_DIV] THEN
    SIMP_TAC[SUBFIELD_GENERATED; RING_OF_INT_SUBFIELD_GENERATED;
             REAL_RING_CLAUSES; REAL_RING_OF_INT];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real) IN ring_carrier Q` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(real_of_int b = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(b:int = &0)` THEN REWRITE_TAC[int_eq; int_of_num_th];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_RING_OF_INT) THEN
  ASM_REWRITE_TAC[COMPLEX_RING_OF_INT] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:real`; `real_of_int b`] o
    MATCH_MP RING_HOMOMORPHISM_MUL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[RING_OF_INT]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; COMPLEX_RING_CLAUSES] THEN
  ASM_REWRITE_TAC[CX_DIV] THEN
  SUBGOAL_THEN `~(Cx(real_of_int b) = Cx(&0))` MP_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ]; ALL_TAC] THEN
  CONV_TAC COMPLEX_FIELD);;

let RATIONAL_PRODUCT_FORMULA = prove
 (`!x. x IN ring_carrier(subfield_generated real_ring {&0}) /\ ~(x = &0)
       ==> FINITE {p | prime p /\
                       ~(dedekind_valuation
                          (ring_of_integers(subfield_generated real_ring {&0}),
                           subfield_generated real_ring {&0}) I
                          (ideal_generated
                            (ring_of_integers
                              (subfield_generated real_ring {&0})) {&p})
                          x = &0)} /\
           product {p | prime p /\
                        ~(dedekind_valuation
                           (ring_of_integers
                             (subfield_generated real_ring {&0}),
                            subfield_generated real_ring {&0}) I
                           (ideal_generated
                             (ring_of_integers
                               (subfield_generated real_ring {&0})) {&p})
                           x = &0)}
                   (\p. &p zpow
                        --(dedekind_valuation
                            (ring_of_integers
                              (subfield_generated real_ring {&0}),
                             subfield_generated real_ring {&0}) I
                            (ideal_generated
                              (ring_of_integers
                                (subfield_generated real_ring {&0})) {&p})
                            x)) *
           abs x = &1`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = subfield_generated real_ring {&0}` THEN
  ABBREV_TAC `O = ring_of_integers(Q:real ring)` THEN
  SUBGOAL_THEN `number_field(Q:real ring) /\ ring_0 Q = &0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[NUMBER_FIELD_RATIONAL_FIELD; SUBFIELD_GENERATED;
                REAL_RING_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier Q
        ==> product (complex_embeddings Q) (\g. norm(g y)) = abs y`
  (LABEL_TAC "emb") THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    MP_TAC RATIONAL_FIELD_COMPLEX_EMBEDDINGS THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `product (complex_embeddings Q) (\g:real->complex. abs y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[COMPLEX_NORM_CX];
      ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_1]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:real ring`; `x:real`] NUMBER_FIELD_PRODUCT_FORMULA) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `{P | prime_ideal O P /\ ~(P = {&0}) /\
         ~(dedekind_valuation (O,Q) I P (x:real) = &0)} =
    IMAGE (\p. ideal_generated O {&p})
          {p | prime p /\
               ~(dedekind_valuation (O,Q) I (ideal_generated O {&p}) x = &0)}`
  SUBST1_TAC THENL
   [MP_TAC(ISPEC `real_ring` RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[FIELD_REAL_RING; REAL_RING_CHAR; REAL_RING_CLAUSES;
                    REAL_RING_OF_NUM] THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `P:real->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `p:num` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `P:real->bool`)) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `P:real->bool`)) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. p IN {p | prime p /\
                    ~(dedekind_valuation (O,Q) I (ideal_generated O {&p}) x =
                      &0)} /\
          q IN {p | prime p /\
                    ~(dedekind_valuation (O,Q) I (ideal_generated O {&p}) x =
                      &0)} /\
          ideal_generated O {&p} = ideal_generated O {&q:real}
          ==> p = q`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`real_ring`; `p:num`; `q:num`]
      PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ) THEN
    ASM_REWRITE_TAC[FIELD_REAL_RING; REAL_RING_CHAR; REAL_RING_CLAUSES;
                    REAL_RING_OF_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p. ideal_generated O {&p:real}`;
                 `{p | prime p /\
                       ~(dedekind_valuation (O,Q) I
                          (ideal_generated O {&p}) (x:real) = &0)}`]
    FINITE_IMAGE_INJ_EQ) THEN
  MP_TAC(ISPECL [`\p. ideal_generated O {&p:real}`;
                 `\P. &(ideal_norm O P) zpow
                      --(dedekind_valuation (O,Q) I P (x:real))`;
                 `{p | prime p /\
                       ~(dedekind_valuation (O,Q) I
                          (ideal_generated O {&p}) (x:real) = &0)}`]
    PRODUCT_IMAGE) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`Q:real ring`; `&p:real`]
    NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXPAND_TAC "O" THEN EXPAND_TAC "Q" THEN
    REWRITE_TAC[RING_OF_INTEGERS_RATIONAL_FIELD] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; REAL_OF_NUM_EQ; PRIME_IMP_NZ];
    DISCH_THEN SUBST1_TAC] THEN
  REMOVE_THEN "emb" (MP_TAC o SPEC `&p:real`) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`Q:real ring`; `&p:int`] RING_OF_INT) THEN
    EXPAND_TAC "Q" THEN
    REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED; REAL_RING_OF_INT;
                int_of_num_th];
    SIMP_TAC[REAL_ABS_NUM]]);;
