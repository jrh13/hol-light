(* ========================================================================= *)
(* The Dedekind zeta function of a number field k for Re s > 1, and the      *)
(* analytic facts behind densities of prime ideals: the number of nonzero    *)
(* ideals of bounded norm, the convergence and the Euler product of zeta_k,  *)
(* bounds near s = 1, the sums over the prime ideals and over the primes of  *)
(* degree one, Dirichlet densities and their elementary laws (Neukirch,      *)
(* Algebraic Number Theory, VII.5 and VII.13; Lang, Algebraic Number Theory, *)
(* VIII.2 and VIII.4).                                                       *)
(*                                                                           *)
(*   dedekind_zeta k s = the sum over m >= 1 of a(m) / m^s, a(m) the number  *)
(*                       of nonzero ideals of O = ring_of_integers k of norm *)
(*                       m (a complex Dirichlet series, convergent for       *)
(*                       Re s > 1)                                           *)
(*   has_dirichlet_density k S d <=> the sum over m >= 1 of                  *)
(*                       #{P in S : N(P) = m} / m^s, divided by              *)
(*                       log(1 / (s - 1)), tends to d as s tends to 1 from   *)
(*                       the right (Neukirch VII.13.1, for sets S of prime   *)
(*                       ideals)                                             *)
(*                                                                           *)
(* Main results, for a number field k, with N the ideal norm and the sums    *)
(* over the nonzero prime ideals P of O:                                     *)
(*   NUMBER_FIELD_IDEAL_COUNT_BOUNDS: c X <= #{j : N(j) <= X} <= C X         *)
(*   DEDEKIND_ZETA_CONVERGES, DEDEKIND_ZETA_REAL: the series converges to    *)
(*     dedekind_zeta k s for Re s > 1, with real values for real s > 1       *)
(*   DEDEKIND_ZETA_POLE_BOUNDS: c / (s - 1) <= zeta_k(s) <= C / (s - 1) for  *)
(*     1 < s <= 2, with c > 0                                                *)
(*   DEDEKIND_ZETA_EULER_PRODUCT, DEDEKIND_ZETA_EULER_PRODUCT_REAL: the      *)
(*     products over the P with N(P) <= n of 1 / (1 - N(P)^-s) tend to       *)
(*     zeta_k(s) for Re s > 1                                                *)
(*   DEDEKIND_ZETA_LOG_POLE: log zeta_k(s) = -log(s - 1) + O(1), 1 < s <= 2  *)
(*   NUMBER_FIELD_PRIME_IDEALS_LOG: sum N(P)^-s = -log(s - 1) + O(1)         *)
(*   NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG: the same over the P of residue      *)
(*     degree one over Z, which are the P of prime norm                      *)
(*     (NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE of ANT/prime_split.ml)           *)
(*   NUMBER_FIELD_PRIME_IDEALS_DENSITY and                                   *)
(*   NUMBER_FIELD_DEGREE_ONE_PRIMES_DENSITY: both sets have density 1        *)
(*   HAS_DIRICHLET_DENSITY_LOG: an estimate sum over S of N(P)^-s =          *)
(*     -d log(s - 1) + O(1) gives density d; HAS_DIRICHLET_DENSITY_UNIQUE,   *)
(*     HAS_DIRICHLET_DENSITY_FINITE, HAS_DIRICHLET_DENSITY_INFINITE: the     *)
(*     density is unique, finite sets have density 0, sets of nonzero        *)
(*     density are infinite                                                  *)
(*   the elementary laws of density, for sets S1, S2 of nonzero prime        *)
(*     ideals of O with densities d1, d2 (over such a set the series         *)
(*     converges for s > 1, NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE):    *)
(*     HAS_DIRICHLET_DENSITY_BOUNDS: 0 <= d1 <= 1                            *)
(*     HAS_DIRICHLET_DENSITY_SUBSET: S1 SUBSET S2 implies d1 <= d2           *)
(*     HAS_DIRICHLET_DENSITY_DISJOINT_UNION: for disjoint S1, S2 the union   *)
(*       has density d1 + d2                                                 *)
(*     HAS_DIRICHLET_DENSITY_DIFF_SUBSET: S2 SUBSET S1 implies that S1 DIFF  *)
(*       S2 has density d1 - d2                                              *)
(*     HAS_DIRICHLET_DENSITY_COMPLEMENT: the nonzero prime ideals outside S1 *)
(*       have density 1 - d1                                                 *)
(*     HAS_DIRICHLET_DENSITY_FINITE_SYMDIFF: sets with a finite symmetric    *)
(*       difference have the same densities                                  *)
(*                                                                           *)
(* The bounds and logarithmic estimates concern real s tending to 1 from     *)
(* above. Analytic continuation and a simple pole of zeta_k at 1 are not     *)
(* proved here. Dirichlet density has its usual prime-ideal interpretation   *)
(* when S consists of nonzero prime ideals of O_k; the definition itself     *)
(* also applies to other sets and does not require summability. The          *)
(* elementary laws above assume sets of nonzero prime ideals.                *)
(*                                                                           *)
(* Routes. Upper bound for the counting function                             *)
(* (NUMBER_FIELD_IDEAL_COUNT_UPPER): with t^n <= X < (t+1)^n, the box        *)
(* principle of ANT/classgroup.ml gives for each ideal j of norm at most X   *)
(* an ideal j1 of norm at most M = n! (n B)^n and an element with integer    *)
(* coordinates at most t in an integral basis generating j j1                *)
(* (NUMBER_FIELD_IDEAL_BOX_COFACTOR); j is determined by the pair, so there  *)
(* are at most (2t+1)^n #{j1 : N(j1) <= M} <= 3^n #{j1 : N(j1) <= M} X of    *)
(* them. Lower bound (NUMBER_FIELD_IDEAL_COUNT_LOWER): the elements m + sum  *)
(* c_i w_i with |c_i| <= m / (2B) have all conjugates between m/2 and 3m/2,  *)
(* so they generate ideals of norm at most (2m)^n, and two of them           *)
(* generating the same ideal differ by a factor with all conjugates at most  *)
(* 3, of which there are finitely many (NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY, *)
(* with the complex embeddings). Convergence and pole: summation by parts    *)
(* turns c X - c X0 <= A(X) <= C X into the bounds for sum a(m) m^-s in      *)
(* terms of zeta(s) = sum m^-s (DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS), and   *)
(* 1 / (s - 1) <= zeta(s) <= s / (s - 1) by the mean value theorem           *)
(* (REAL_INFSUM_ZETA_BOUNDS of Multivariate/realanalysis.ml). Euler product: *)
(* the product over the P with N(P) <= n of the truncated geometric series   *)
(* expands (CPRODUCT_VSUM_POW of Multivariate/transcendentals.ml) into the   *)
(* sum of N(j)^-s over the products j of powers of these P, each ideal once  *)
(* by unique factorization (DEDEKIND_FINITE_EULER_PRODUCT); it contains all  *)
(* j with N(j) <= n (NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT), so it differs  *)
(* from zeta_k(s) by at most a tail of the series                            *)
(* (DEDEKIND_ZETA_EULER_PRODUCT_BOUND).                                      *)
(* Logarithm: exp x <= 1 / (1 - x) <= exp(x + 2 x^2) for 0 <= x <= 1/2       *)
(* gives sum N(P)^-s <= log zeta_k(s) <= sum N(P)^-s + 2 zeta_k(2)           *)
(* (DEDEKIND_ZETA_LOG_PRIME_IDEALS, with REAL_EXP_LE_INV_1_SUB and           *)
(* REAL_INV_1_SUB_LE_EXP of Multivariate/transcendentals.ml); the P of       *)
(* nonprime norm p^f, f >= 2, contribute at most 2 [k:Q]                     *)
(* (NUMBER_FIELD_NONPRIME_NORM_SUM_LE). Density                              *)
(* laws: over a set of nonzero prime ideals the coefficients are at most     *)
(* those of zeta_k, so the series converge for s > 1 and are additive in the *)
(* set; the laws follow from the limit laws, from log(1 / (s - 1)) > 0 for   *)
(* 1 < s < 2, from the density 1 of all nonzero prime ideals                 *)
(* (NUMBER_FIELD_PRIME_IDEALS_DENSITY) and from the density 0 of finite sets *)
(* (HAS_DIRICHLET_DENSITY_FINITE).                                           *)
(*                                                                           *)
(* Uses: Multivariate/realanalysis.ml (real series, rpow, limits,            *)
(* REAL_INFSUM_ZETA_BOUNDS), Library/isum.ml (HAS_SIZE_INT_ABS_LE),          *)
(* Library/ring_det.ml (free bases, multiplication matrices), ANT/algmisc.ml *)
(* (NUM_ROOT_FLOOR, UPPER_BOUND_FINITE_SET_INT), ANT/ideal_arith.ml,         *)
(* ANT/dedekind.ml (factorization, valuations, cancellation),                *)
(* ANT/ideal_norm.ml, ANT/numfield.ml, ANT/ring_of_integers.ml (integral     *)
(* bases), ANT/norm_index.ml (the norm of a principal ideal),                *)
(* ANT/discriminant.ml, ANT/classgroup.ml (the box principle,                *)
(* NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM), ANT/prime_split.ml (N(P) =      *)
(* p^f), ANT/complex_embeddings.ml and ANT/infinite_places.ml (the norm of a *)
(* principal ideal as a product over the embeddings). Also                   *)
(* Multivariate/complex_ring.ml (COMPLEX_RING_CLAUSES, COMPLEX_RING_SUM) and *)
(* Multivariate/transcendentals.ml (log, cpow, CPRODUCT_VSUM_POW).           *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/prime.ml";;
needs "Library/products.ml";;
needs "Library/ring_det.ml";;
needs "Multivariate/realanalysis.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/norm_index.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/classgroup.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/infinite_places.ml";;
needs "Multivariate/complex_ring.ml";;
needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* Real Dirichlet series whose coefficient sums grow linearly.               *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS = prove
 (`!(a:num->real) C c N0 s.
        (!m. &0 <= a m) /\ &0 <= c /\
        (!N. sum(1..N) a <= C * &N) /\
        (!N. N0 <= N ==> c * &N <= sum(1..N) a) /\
        &1 < s
        ==> real_summable (from 1) (\m. a m / &m rpow s) /\
            c * real_infsum (from 1) (\m. inv(&m rpow s)) - c * &N0 <=
            real_infsum (from 1) (\m. a m / &m rpow s) /\
            real_infsum (from 1) (\m. a m / &m rpow s) <=
            C * real_infsum (from 1) (\m. inv(&m rpow s))`,
  let abel_lemma = prove
   (`!(a:num->real) (f:num->real) M.
          1 <= M
          ==> sum(1..M) (\m. a m * f m) =
              f(M + 1) * sum(1..M) a +
              sum(1..M) (\k. sum(1..k) a * (f k - f(k + 1)))`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:num->real`; `\k. sum(1..k) (a:num->real)`; `1`; `M:num`]
      SUM_PARTIAL_PRE) THEN
    ASM_REWRITE_TAC[SUB_REFL] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x:real = x' /\ y:real = --y' ==> x = z - y ==> x' = z + y'`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; ARITH_RULE `1 <= k ==> 0 < k`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC]) in
  let abs_lemma = prove
   (`!C x Z. &0 <= x /\ x <= Z ==> C * x <= abs C * (Z:real)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs C * x:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(C * x:real)` THEN
      REWRITE_TAC[REAL_ABS_LE; REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs x = x:real` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]]) in
  REWRITE_TAC[real_div] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real` REAL_INFSUM_ZETA_BOUNDS) THEN
  MP_TAC(SPECL [`1`; `s:real`] REAL_SUMMABLE_ZETA) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Z = real_infsum (from 1) (\m. inv(&m rpow s))` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `f = \m. inv(&m rpow s)` THEN
  SUBGOAL_THEN
   `(!m. &0 <= (f:num->real) m) /\ (!m. 1 <= m ==> f(m + 1) <= f m) /\
    (!m. 1 <= m ==> f m <= &1) /\ f 1 = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS; RPOW_ONE; REAL_INV_1] THEN
    CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_POS_LT THEN
        REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC RPOW_LE2 THEN
        REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
        CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      MATCH_MP_TAC(REAL_ARITH
                   `&1 rpow s = &1 /\ &1 rpow s <= x ==> &1 <= x`) THEN
      CONJ_TAC THENL [REWRITE_TAC[RPOW_ONE]; MATCH_MP_TAC RPOW_LE2] THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\m. (a:num->real) m * inv(&m rpow s)) = (\m. a m * f m)`
  SUBST1_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. 1 <= M
        ==> sum(1..M) (f:num->real) =
            f(M + 1) * &M + sum(1..M) (\k. &k * (f k - f(k + 1)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\m:num. &1:real`; `f:num->real`; `M:num`]
           abel_lemma) THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID] THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. sum(1..M) (\m. (a:num->real) m * f m) <= C * sum(1..M) f`
  ASSUME_TAC THENL
   [X_GEN_TAC `M:num` THEN ASM_CASES_TAC `M = 0` THENL
     [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_RZERO; REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:num->real`; `f:num->real`; `M:num`] abel_lemma) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(M = 0) ==> 1 <= M`] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `M:num` o check (fun th ->
      is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(M = 0) ==> 1 <= M`] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `C * x * y:real = x * C * y`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_SUB_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. 1 <= M /\ N0 <= M
        ==> c * sum(1..M) f - c * &N0 <= sum(1..M) (\m. (a:num->real) m * f m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:num->real`; `f:num->real`; `M:num`] abel_lemma) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `M:num` o check (fun th ->
      is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
      is_eq(rand(snd(dest_forall(concl th)))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x <= x' /\ y <= y' + e ==> (x + y) - e <= x' + y':real`) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `c * x * y:real = x * c * y`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..M) (\k. sum(1..k) a * (f k - f(k + 1)) +
                              c * &N0 * (f k - (f:num->real)(k + 1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= (f:num->real) k - f(k + 1)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_SUB_LE]; ALL_TAC] THEN
      ASM_CASES_TAC `N0 <= k:num` THENL
       [MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z:real`) THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_SIMP_TAC[];
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]];
        MATCH_MP_TAC(REAL_ARITH `x <= z /\ &0 <= y ==> x <= y + z:real`) THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
          UNDISCH_TAC `~(N0 <= k:num)` THEN ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]]];
      REWRITE_TAC[SUM_ADD_NUMSEG] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= e ==> x + y <= x + e:real`) THEN
      REWRITE_TAC[SUM_LMUL] THEN
      ASM_SIMP_TAC[SUM_DIFFS] THEN
      REWRITE_TAC[REAL_ARITH
                  `c * n * (&1 - f) <= c * n <=> &0 <= c * n * f:real`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_SUMS_INFSUM] o check
    (fun th -> concl th = `real_summable (from 1) (f:num->real)`)) THEN
  ASM_REWRITE_TAC[REAL_SERIES_FROM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!M. sum(1..M) (f:num->real) <= Z` ASSUME_TAC THENL
   [X_GEN_TAC `M:num` THEN
    MP_TAC(ISPECL [`f:num->real`; `from 1`; `M:num`]
      REAL_PARTIAL_SUMS_LE_INFSUM) THEN
    ASM_REWRITE_TAC[FROM_INTER_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\M. sum(1..M) (\m. (a:num->real) m * f m)`
    CONVERGENT_REAL_BOUNDED_MONOTONE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
      EXISTS_TAC `abs C * Z + &1:real` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x:real ==> &0 < x + &1`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(s - &1)` THEN
        ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `M:num` THEN
      SUBGOAL_THEN `&0 <= sum(1..M) (\m. (a:num->real) m * f m) /\
                    &0 <= sum(1..M) (f:num->real)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
        ASM_SIMP_TAC[REAL_LE_MUL];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `M:num` o check (fun th ->
        free_in `C:real` (concl th) && is_forall(concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `M:num` o check (fun th ->
        free_in `Z:real` (concl th) && is_forall(concl th))) THEN
      MP_TAC(SPECL [`C:real`; `sum(1..M) (f:num->real)`; `Z:real`]
        abs_lemma) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISJ1_TAC THEN X_GEN_TAC `M:num` THEN
      REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC M`] THEN
      ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_MUL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
  SUBGOAL_THEN `((\m. (a:num->real) m * f m) real_sums l) (from 1)` ASSUME_TAC
  THENL [ASM_REWRITE_TAC[REAL_SERIES_FROM]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[real_summable]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INFSUM_UNIQUE) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
    EXISTS_TAC `\M. c * sum(1..M) (f:num->real) - c * &N0` THEN
    EXISTS_TAC `\M. sum(1..M) (\m. (a:num->real) m * f m)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
      MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `N0 + 1` THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
    EXISTS_TAC `\M. sum(1..M) (\m. (a:num->real) m * f m)` THEN
    EXISTS_TAC `\M. C * sum(1..M) (f:num->real)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The number of nonzero ideals of norm at most N grows linearly in N.       *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_IDEAL_BOX_COFACTOR = prove
 (`!k:A ring n w B j.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        (!i l m. i < n /\ l < n /\ m < n
                 ==> abs(mul_matrix (integer_ring,ring_of_integers k)
                           (ring_of_int k) n w (w i) m l)
                     <= B) /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ?c t j'. t EXP n <= ideal_norm (ring_of_integers k) j /\
                     (!m. m < n ==> abs(c m) <= &t) /\
                     ring_ideal (ring_of_integers k) j' /\
                     ~(j' = {ring_0 k}) /\
                     &(ideal_norm (ring_of_integers k) j') <=
                     &(FACT n) * (&n * B) pow n /\
                     ideal_prod (ring_of_integers k) j j' =
                     ideal_generated (ring_of_integers k)
                      {ring_sum (ring_of_integers k) {m | m < n}
                        (\m. ring_mul k (ring_of_int k (c m)) (w m))}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_char(k:A ring) = 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
      RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
    MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DEGREE_POS) THEN
    ASM_SIMP_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (B:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `abs(mul_matrix (integer_ring,ring_of_integers k)
                      (ring_of_int k) n w ((w:num->A) 0) 0 0)` THEN
    REWRITE_TAC[INT_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(ring_carrier(quotient_ring (ring_of_integers k) (j:A->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `ideal_norm (ring_of_integers k) (j:A->bool)`]
    NUM_ROOT_FLOOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                 `j:A->bool`; `t:num`] FREE_BASIS_IDEAL_BOX_PRINCIPLE) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->int` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m0:num`) ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`c:num->int`; `t:num`] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = ring_sum (ring_of_integers k) {m | m < n}
      (\m. ring_mul k (ring_of_int k ((c:num->int) m)) ((w:num->A) m))` THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(a:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:num->int` o last o CONJUNCTS o
      GEN_REWRITE_RULE I [free_basis]) THEN
    ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV;
                    RING_OF_INTEGERS] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dedekind_domain(ring_of_integers k:A ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                 `ideal_generated (ring_of_integers k) {a:A}`; `j:A->bool`]
    DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j':A->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(j':A->bool = {ring_0 k})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`; `j':A->bool`]
      IDEAL_PROD_EQ_ZERO) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD;
                 RING_OF_INTEGERS; IDEAL_GENERATED_EQ_0] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `a:A`]
      IDEAL_GENERATED_EQ_0) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`k:A ring`; `j:A->bool`; `j':A->bool`]
    NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `a:A`]
    NUMBER_FIELD_NORM_INTEGRAL_BASIS) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[ring_monomorphism] o
    GEN_REWRITE_RULE I [GSYM RING_MONOMORPHISM_INTEGER_RING_OF_INT]) THEN
  REWRITE_TAC[INTEGER_RING; IN_UNIV] THEN
  DISCH_THEN(fun th -> DISCH_THEN(SUBST_ALL_TAC o MATCH_MP th)) THEN
  SUBGOAL_THEN `~(ideal_norm (ring_of_integers k) (j:A->bool) = 0)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ideal_norm; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC[RING_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                 `B:int`; `c:num->int`; `t:num`] FREE_BASIS_NORM_BOUND) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`&(ideal_norm (ring_of_integers k) (j':A->bool)):int`;
                 `(&(FACT n) * (&n * B) pow n):int`;
                 `&(ideal_norm (ring_of_integers k) (j:A->bool)):int`]
    INT_LE_LMUL_EQ) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LT; LT_NZ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INT_OF_NUM_MUL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && lhand(concl th) =
    `&(ideal_norm (ring_of_integers k) j *
       ideal_norm (ring_of_integers k) (j':A->bool)):int`)) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
   `x <= y ==> y <= z ==> x:int <= z`) o check (fun th ->
    free_in `t:num` (concl th))) THEN
  SUBGOAL_THEN
   `&(FACT n) * ((&n * B) * &t) pow n =
    (&(FACT n) * (&n * B) pow n) * &(t EXP n):int`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_POW_MUL; GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `(&(FACT n) * (&n * B) pow n) *
              &(ideal_norm (ring_of_integers k) (j:A->bool)):int` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_LMUL THEN
    ASM_SIMP_TAC[INT_POW_LE; INT_LE_MUL; INT_POS; INT_OF_NUM_LE];
    REWRITE_TAC[INT_MUL_AC; INT_LE_REFL]]);;

let NUMBER_FIELD_IDEAL_COUNT_UPPER = prove
 (`!k:A ring.
        number_field k
        ==> ?C. !N. CARD {j | ring_ideal (ring_of_integers k) j /\
                              ~(j = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) j <= N}
                    <= C * N`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
  MP_TAC(ISPECL
   [`\p. abs(mul_matrix (integer_ring,ring_of_integers k)
               (ring_of_int k) n w ((w:num->A)(FST p)) (SND(SND p))
               (FST(SND p)))`;
    `{i:num | i < n} CROSS ({l:num | l < n} CROSS {m:num | m < n})`]
    UPPER_BOUND_FINITE_SET_INT) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:int`) THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_SIMP_TAC[NUMBER_FIELD_DEGREE_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (B:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `abs(mul_matrix (integer_ring,ring_of_integers k)
                      (ring_of_int k) n w ((w:num->A) 0) 0 0)` THEN
    REWRITE_TAC[INT_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `M0 = num_of_int(&(FACT n) * (&n * B) pow n)` THEN
  SUBGOAL_THEN `(&M0:int) = &(FACT n) * (&n * B) pow n` ASSUME_TAC THENL
   [EXPAND_TAC "M0" THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    ASM_SIMP_TAC[INT_LE_MUL; INT_POW_LE; INT_POS];
    ALL_TAC] THEN
  ABBREV_TAC
   `Sm = {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
              ideal_norm (ring_of_integers k) (j:A->bool) <= M0}` THEN
  SUBGOAL_THEN `FINITE(Sm:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Sm" THEN ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM];
    ALL_TAC] THEN
  EXISTS_TAC `3 EXP n * CARD(Sm:(A->bool)->bool)` THEN
  X_GEN_TAC `N:num` THEN
  ABBREV_TAC
   `S = {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) <= N}` THEN
  SUBGOAL_THEN `FINITE(S:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM];
    ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL
   [SUBGOAL_THEN `S:(A->bool)->bool = {}` SUBST1_TAC THENL
     [ALL_TAC; REWRITE_TAC[CARD_CLAUSES; LE_0]] THEN
    EXPAND_TAC "S" THEN
    REWRITE_TAC[SET_RULE `{x:A->bool | P x} = {} <=> !x. ~P x`] THEN
    X_GEN_TAC `j:A->bool` THEN ASM_REWRITE_TAC[LE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `j:A->bool`]
      RING_OF_INTEGERS_FINITE_QUOTIENT) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ideal_norm (ring_of_integers k) (j:A->bool) = 0` THEN
    REWRITE_TAC[ideal_norm] THEN REPEAT DISCH_TAC THEN
    UNDISCH_TAC `CARD(ring_carrier(quotient_ring (ring_of_integers k)
                  (j:A->bool))) = 0` THEN
    ASM_SIMP_TAC[CARD_EQ_0; GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[RING_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `N:num`] NUM_ROOT_FLOOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tm:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `1 <= tm` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT; ARITH_RULE `tm < 1 <=> tm = 0`] THEN DISCH_TAC THEN
    UNDISCH_TAC `N < (tm + 1) EXP n` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; EXP_ONE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN S
        ==> ?c j'. (!m. m < n ==> abs(c m) <= &tm) /\ j' IN Sm /\
                   ideal_prod (ring_of_integers k) j j' =
                   ideal_generated (ring_of_integers k)
                    {ring_sum (ring_of_integers k) {m | m < n}
                      (\m. ring_mul k (ring_of_int k (c m)) ((w:num->A) m))}`
  MP_TAC THENL
   [X_GEN_TAC `j:A->bool` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `B:int`; `j:A->bool`]
      NUMBER_FIELD_IDEAL_BOX_COFACTOR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->int` (X_CHOOSE_THEN `t:num`
      (X_CHOOSE_THEN `j':A->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`c:num->int`; `j':A->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&t:int` THEN
      ASM_SIMP_TAC[INT_OF_NUM_LE] THEN
      REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(tm + 1) EXP n <= t EXP n` MP_TAC THENL
       [REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      EXPAND_TAC "Sm" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `cf:(A->bool)->num->int`
    (X_CHOOSE_TAC `jf:(A->bool)->(A->bool)`)) THEN
  ABBREV_TAC
   `Bx = {f:num->num | (!m. m IN {m | m < n} ==> f m IN 0..2 * tm) /\
                       (!m. ~(m IN {m | m < n}) ==> f m = 0)}` THEN
  SUBGOAL_THEN `(Bx:(num->num)->bool) HAS_SIZE (2 * tm + 1) EXP n`
  ASSUME_TAC THENL
   [EXPAND_TAC "Bx" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN
    REWRITE_TAC[HAS_SIZE_NUMSEG_LT] THEN
    MP_TAC(SPECL [`0`; `2 * tm`] HAS_SIZE_NUMSEG) THEN
    REWRITE_TAC[SUB_0];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD((Bx:(num->num)->bool) CROSS (Sm:(A->bool)->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD(IMAGE (\j:A->bool. (\m. if m < n
                     then num_of_int((cf:(A->bool)->num->int) j m + &tm)
                     else 0),
                    (jf:(A->bool)->(A->bool)) j) S)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
      MAP_EVERY X_GEN_TAC [`j1:A->bool`; `j2:A->bool`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `!m. m < n ==> (cf:(A->bool)->num->int) j1 m = cf j2 m`
        ASSUME_TAC THENL
         [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o C AP_THM `m:num` o check (fun th ->
            is_eq(concl th) && is_abs(lhand(concl th)))) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(MP_TAC o AP_TERM `int_of_num`) THEN
          FIRST_X_ASSUM(fun th ->
            MP_TAC(SPEC `j1:A->bool` th) THEN MP_TAC(SPEC `j2:A->bool` th)) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(MP_TAC o SPEC `m:num` o CONJUNCT1) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_TAC THEN
          DISCH_THEN(MP_TAC o SPEC `m:num` o CONJUNCT1) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_TAC THEN
          MP_TAC(ISPEC `(cf:(A->bool)->num->int) j1 m + &tm`
                 INT_OF_NUM_OF_INT) THEN
          MP_TAC(ISPEC `(cf:(A->bool)->num->int) j2 m + &tm`
                 INT_OF_NUM_OF_INT) THEN
          REPEAT(ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
          INT_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(fun th ->
          MP_TAC(SPEC `j1:A->bool` th) THEN MP_TAC(SPEC `j2:A->bool` th)) THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                             `(jf:(A->bool)->(A->bool)) j2`]
          DEDEKIND_IDEAL_PROD_CANCEL) THEN
        REWRITE_TAC[RING_OF_INTEGERS] THEN
        UNDISCH_TAC `(jf:(A->bool)->(A->bool)) j2 IN Sm` THEN
        EXPAND_TAC "Sm" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS] THEN
        UNDISCH_TAC `(j1:A->bool) IN S` THEN UNDISCH_TAC
          `(j2:A->bool) IN S` THEN
        EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                       `(jf:(A->bool)->(A->bool)) j2`;
                       `j1:A->bool`] IDEAL_PROD_COMM) THEN
        MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                       `(jf:(A->bool)->(A->bool)) j2`;
                       `j2:A->bool`] IDEAL_PROD_COMM) THEN
        ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
        REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN
        AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
      MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_CROSS; HAS_SIZE] THEN
      CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CROSS] THEN
          X_GEN_TAC `j:A->bool` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool` o check (fun th ->
            is_forall(concl th) && free_in `jf:(A->bool)->(A->bool)`
              (concl th))) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          EXPAND_TAC "Bx" THEN REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
          SIMP_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
          DISCH_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
          MP_TAC(ISPEC `(cf:(A->bool)->num->int) j m + &tm`
                 INT_OF_NUM_OF_INT) THEN
          ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
          REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN ASM_INT_ARITH_TAC;
          ASM_MESON_TAC[FINITE_CROSS; HAS_SIZE]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HAS_SIZE] o check
    (fun th -> is_comb(concl th) && rand(concl th) = `(2 * tm + 1) EXP n`)) THEN
  ASM_SIMP_TAC[CARD_CROSS] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(a * b) * c:num = (a * c) * b`] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(3 * tm) EXP n` THEN CONJ_TAC THENL
   [REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MULT_EXP] THEN ASM_SIMP_TAC[LE_MULT_LCANCEL]]);;

(* The elements m + sum_i c_i w_i with |c_i| <= m DIV 2Bn have all           *)
(* conjugates within m/2 of m; two of them generating the same ideal differ  *)
(* by a factor with all conjugates at most 3, and there are finitely many of *)
(* those (Northcott).                                                        *)
let NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY = prove
 (`!k:A ring n w Bn m.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        (!g. g IN complex_embeddings k
             ==> sum {i | i < n} (\i. norm(g(w i))) <= &Bn) /\
        1 <= m
        ==> (2 * (m DIV (2 * Bn)) + 1) EXP n <=
            CARD {x | x IN ring_carrier(ring_of_integers k) /\
                      !g. g IN complex_embeddings k ==> norm(g x) <= &3} *
            CARD {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                      ideal_norm (ring_of_integers k) j <= (2 * m) EXP n}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM o CONJUNCT1) THEN
  MP_TAC(ISPEC `k:A ring` COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  ABBREV_TAC `t = m DIV (2 * Bn)` THEN
  SUBGOAL_THEN `2 * t * Bn <= m` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    MP_TAC(SPECL [`m:num`; `2 * Bn`] DIV_MUL_LE) THEN
    REWRITE_TAC[MULT_AC];
    ALL_TAC] THEN
  ABBREV_TAC
   `U = {x | x IN ring_carrier(ring_of_integers k) /\
             !g. g IN complex_embeddings k ==> norm((g:A->complex) x)
               <= &3}` THEN
  ABBREV_TAC
   `S = {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) <= (2 * m) EXP n}` THEN
  SUBGOAL_THEN `FINITE(U:A->bool) /\ FINITE(S:(A->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "S"] THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE;
                 NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n ==> (w:num->A) i IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP FREE_BASIS_IN_CARRIER); ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_carrier(ring_of_integers k) SUBSET ring_carrier(k:A ring)`
  ASSUME_TAC THENL [REWRITE_TAC[RING_OF_INTEGERS_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC
   `psi = \z:num->int. ring_sum (ring_of_integers k) {i | i < n}
            (\i. ring_mul k (ring_of_int k (z i)) ((w:num->A) i))` THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                 `psi:(num->int)->A`] FREE_BASIS_INTEGER_RING_LINCOMB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN EXPAND_TAC "psi" THEN
    REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!(z:num->int) g. g IN complex_embeddings k
          ==> (g:A->complex)(psi z) =
              vsum {i:num | i < n} (\i. Cx(real_of_int(z i)) * g(w i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[complex_embeddings;
      IN_ELIM_THM] o check (fun th -> concl th =
      `(g:A->complex) IN complex_embeddings k`)) THEN
    DISCH_TAC THEN EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_RING_OF_INTEGERS o
      rand o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                     `ring_of_int k ((z:num->int) i):A`; `(w:num->A) i`]
        RING_MUL) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS; RING_OF_INT_IN_RING_OF_INTEGERS];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `!i. i < n ==> ring_mul k (ring_of_int k ((z:num->int) i))
                                 ((w:num->A) i) IN ring_carrier k /\
                      (w:num->A) i IN ring_carrier k`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[RING_OF_INT];
        ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
      (MATCH_MP RING_HOMOMORPHISM_SUM th) o lhand o snd)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[COMPLEX_RING_SUM; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
      (MATCH_MP RING_HOMOMORPHISM_MUL th) o lhand o snd)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_OF_INT]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th]) THEN
    REWRITE_TAC[COMPLEX_RING_OF_INT; COMPLEX_RING_CLAUSES];
    ALL_TAC] THEN
  ABBREV_TAC
   `Bx = {z:num->int |
          (!i. i IN {i:num | i < n} ==> z i IN {x:int | abs x <= &t}) /\
                       (!i. ~(i IN {i:num | i < n}) ==> z i = &0)}` THEN
  SUBGOAL_THEN `(Bx:(num->int)->bool) HAS_SIZE (2 * t + 1) EXP n`
  ASSUME_TAC THENL
   [EXPAND_TAC "Bx" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN
    REWRITE_TAC[HAS_SIZE_NUMSEG_LT; HAS_SIZE_INT_ABS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `elt = \z:num->int. ring_add k (ring_of_num k m) (psi z:A)` THEN
  SUBGOAL_THEN `!z. (elt:(num->int)->A) z IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "elt" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_num k m:A`;
                   `psi(z:num->int):A`] RING_ADD) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `m:num`] RING_OF_NUM) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z g. z IN Bx /\ g IN complex_embeddings k
          ==> norm((g:A->complex)((elt:(num->int)->A) z) - Cx(&m)) <= &m / &2`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:num->int`; `g:A->complex`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[complex_embeddings;
      IN_ELIM_THM] o check (fun th -> concl th =
      `(g:A->complex) IN complex_embeddings k`)) THEN
    DISCH_TAC THEN EXPAND_TAC "elt" THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
      (MATCH_MP RING_HOMOMORPHISM_ADD th) o lhand o rand o lhand o snd)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[RING_OF_NUM] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th]) THEN
    ASM_SIMP_TAC[COMPLEX_RING_OF_NUM; COMPLEX_RING_CLAUSES] THEN
    REWRITE_TAC[COMPLEX_RING_OF_NUM; COMPLEX_RING_CLAUSES;
                COMPLEX_RING `(a + b) - a:complex = b`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {i:num | i < n} (\i. &t * norm((g:A->complex)(w i)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      UNDISCH_TAC `(z:num->int) IN Bx` THEN EXPAND_TAC "Bx" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES; GSYM INT_OF_NUM_LE] THEN
      REWRITE_TAC[REAL_OF_INT_CLAUSES; GSYM int_le];
      REWRITE_TAC[SUM_LMUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&t * &Bn):real` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC `2 * t * Bn <= m` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z g. z IN Bx /\ g IN complex_embeddings k
          ==> &m / &2 <= norm((g:A->complex)((elt:(num->int)->A) z)) /\
              norm(g(elt z)) <= &3 * &m / &2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
      MP_TAC(MATCH_MP (ASSUME
       `!z g. z IN Bx /\ g IN complex_embeddings k
              ==> norm((g:A->complex)((elt:(num->int)->A) z) - Cx(&m)) <=
                  &m / &2`) th)) THEN
    MP_TAC(SPEC `&m:real` COMPLEX_NORM_CX) THEN
    REWRITE_TAC[REAL_ABS_NUM] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(complex_embeddings(k:A ring) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(complex_embeddings(k:A ring)) = n` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN
    MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DEGREE_POS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN Bx ==> ~((elt:(num->int)->A) z = ring_0 k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:num->int` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(complex_embeddings(k:A ring) = {})`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[complex_embeddings;
      IN_ELIM_THM] o check (fun th -> concl th =
      `(g:A->complex) IN complex_embeddings k`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
    REWRITE_TAC[COMPLEX_RING_CLAUSES] THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:num->int`; `g:A->complex`] o check
      (fun th -> free_in `&3 * &m / &2` (concl th))) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
    UNDISCH_TAC `1 <= m` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN Bx
        ==> ideal_generated (ring_of_integers k) {(elt:(num->int)->A) z} IN S`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:num->int` THEN DISCH_TAC THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `(elt:(num->int)->A) z`]
        IDEAL_GENERATED_EQ_0) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    MP_TAC(ISPECL [`k:A ring`; `(elt:(num->int)->A) z`]
      NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product (complex_embeddings(k:A ring)) (\g. &3 * &m / &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[NORM_POS_LE];
      ASM_SIMP_TAC[PRODUCT_CONST; GSYM REAL_OF_NUM_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z z'. z IN Bx /\ z' IN Bx /\ (elt:(num->int)->A) z = elt z' ==> z = z'`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:num->int`; `z':num->int`] THEN
    EXPAND_TAC "elt" THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(psi:(num->int)->A) z = psi z'` MP_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `ring_of_num k m:A`; `(psi:(num->int)->A) z`;
                     `(psi:(num->int)->A) z'`] RING_ADD_LCANCEL) THEN
      ASM_REWRITE_TAC[RING_OF_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num < n` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(z:num->int) IN Bx` THEN UNDISCH_TAC `(z':num->int) IN Bx` THEN
    EXPAND_TAC "Bx" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `rep = \J. @z. z IN Bx /\
                 ideal_generated (ring_of_integers k)
                   {(elt:(num->int)->A) z} = J` THEN
  SUBGOAL_THEN
   `!z. z IN Bx
        ==> (rep:(A->bool)->num->int)
              (ideal_generated (ring_of_integers k) {(elt:(num->int)->A) z})
            IN Bx /\
            ideal_generated (ring_of_integers k)
             {elt(rep(ideal_generated (ring_of_integers k) {elt z}))} =
            ideal_generated (ring_of_integers k) {elt z}`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:num->int` THEN DISCH_TAC THEN EXPAND_TAC "rep" THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `z:num->int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN Bx
        ==> ?x. x IN U /\
                (elt:(num->int)->A) z =
                ring_mul k (elt((rep:(A->bool)->num->int)
                   (ideal_generated (ring_of_integers k) {elt z}))) x`
  MP_TAC THENL
   [X_GEN_TAC `z:num->int` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:num->int` o check (fun th ->
      free_in `rep:(A->bool)->num->int` (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `z0 = (rep:(A->bool)->num->int)
                 (ideal_generated (ring_of_integers k)
                  {(elt:(num->int)->A) z})` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_divides (ring_of_integers k) ((elt:(num->int)->A) z0) (elt z)`
    MP_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `(elt:(num->int)->A) z0`;
                     `(elt:(num->int)->A) z`] IN_IDEAL_GENERATED_SING_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[IN_IDEAL_GENERATED_SELF];
      ALL_TAC] THEN
    REWRITE_TAC[ring_divides; RING_OF_INTEGERS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
    EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[complex_embeddings;
      IN_ELIM_THM] o check (fun th -> concl th =
      `(g:A->complex) IN complex_embeddings k`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP RING_HOMOMORPHISM_MUL) THEN
    DISCH_THEN(MP_TAC o SPECL [`(elt:(num->int)->A) z0`; `x:A`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_RING_CLAUSES] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhand(concl th) = `(elt:(num->int)->A) z`)) THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (CONJ (ASSUME `(z:num->int) IN Bx`)
      (ASSUME `(g:A->complex) IN complex_embeddings k`)) o
      SPECL [`z:num->int`; `g:A->complex`] o check
      (fun th -> free_in `&3 * &m / &2` (concl th))) THEN
    FIRST_ASSUM(MP_TAC o C MP (CONJ (ASSUME `(z0:num->int) IN Bx`)
      (ASSUME `(g:A->complex) IN complex_embeddings k`)) o
      SPECL [`z0:num->int`; `g:A->complex`] o check
      (fun th -> free_in `&3 * &m / &2` (concl th))) THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      lhand(concl th) = `(g:A->complex)((elt:(num->int)->A) z)`
      then ONCE_REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    UNDISCH_TAC `1 <= (m:num)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    MP_TAC(ISPEC `(g:A->complex) x` NORM_POS_LE) THEN
    SPEC_TAC(`norm((g:A->complex)((elt:(num->int)->A) z0))`,`a:real`) THEN
    SPEC_TAC(`norm((g:A->complex) x)`,`y:real`) THEN
    SPEC_TAC(`&m:real`,`mm:real`) THEN
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `mm / &2 * y <= a * y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `mm / &2 * y <= mm / &2 * &3` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ARITH `&1 <= mm ==> &0 < mm / &2`]];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `quo:(num->int)->A`) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [HAS_SIZE] o
              check (fun th ->
    is_comb(concl th) && rand(concl th) = `(2 * t + 1) EXP n`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP HAS_SIZE_CARD o check (fun th ->
    is_comb(concl th) && rand(concl th) = `(2 * t + 1) EXP n`)) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD((S:(A->bool)->bool) CROSS (U:A->bool))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[CARD_CROSS; LE_REFL]] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `CARD(IMAGE (\z. ideal_generated (ring_of_integers k)
                     {(elt:(num->int)->A) z},
                    (quo:(num->int)->A) z) Bx)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`z:num->int`; `z':num->int`] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      (let b = snd(strip_forall(concl th)) in
       is_imp b && rand b = `z:num->int = z'`))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM((fun th ->
      let th1 = CONJUNCT2(MP (SPEC `z:num->int` th)
                          (ASSUME `(z:num->int) IN Bx`))
      and th2 = CONJUNCT2(MP (SPEC `z':num->int` th)
                  (ASSUME `(z':num->int) IN Bx`)) in
      GEN_REWRITE_TAC (BINOP_CONV) [th1; th2]) o check (fun th ->
      free_in `quo:(num->int)->A` (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[FINITE_CROSS] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CROSS] THEN
    X_GEN_TAC `z:num->int` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        free_in `S:(A->bool)->bool` (concl th) &&
        not(free_in `quo:(num->int)->A` (concl th)))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `z:num->int` o check (fun th ->
        free_in `quo:(num->int)->A` (concl th) && is_forall(concl th))) THEN
      ASM_SIMP_TAC[]]]);;

let NUMBER_FIELD_IDEAL_COUNT_LOWER = prove
 (`!k:A ring.
        number_field k
        ==> ?c N0. !N. N0 <= N
                       ==> N <= c * CARD
                                {j | ring_ideal (ring_of_integers k) j /\
                                     ~(j = {ring_0 k}) /\
                                     ideal_norm (ring_of_integers k) j <= N}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
  MP_TAC(ISPECL
   [`\g:A->complex. sum {i:num | i < n} (\i. norm(g((w:num->A) i)))`;
    `complex_embeddings(k:A ring)`] UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_SIMP_TAC[FINITE_COMPLEX_EMBEDDINGS] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `B0:num`) THEN
  SUBGOAL_THEN
   `!g. g IN complex_embeddings k
        ==> sum {i:num | i < n} (\i. norm((g:A->complex)(w i))) <= &(B0 + 1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&B0:real` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `B0 + 1`]
    NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Bn = B0 + 1` THEN
  ABBREV_TAC
   `W = CARD {x | x IN ring_carrier(ring_of_integers k) /\
                  !g. g IN complex_embeddings k
                      ==> norm((g:A->complex) x) <= &3}` THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`(4 * Bn) EXP n * W`; `2 EXP n`] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DEGREE_POS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `N:num`] NUM_ROOT_FLOOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tm:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `2 <= tm` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(tm + 1) EXP n <= 2 EXP n` MP_TAC THENL
     [REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `m = tm DIV 2` THEN
  SUBGOAL_THEN `1 <= m /\ 2 * m <= tm /\ tm <= 2 * m + 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MP_TAC(SPECL [`tm:num`; `2`] DIVISION) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
    is_forall(concl th) && free_in `W:num` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `t = m DIV (2 * Bn)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `m < (t + 1) * (2 * Bn)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MP_TAC(SPECL [`m:num`; `2 * Bn`] DIVISION) THEN
    ANTS_TAC THENL [EXPAND_TAC "Bn" THEN ARITH_TAC; ALL_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `tm + 1 <= (4 * Bn) * (2 * t + 1)` ASSUME_TAC THENL
   [UNDISCH_TAC `m < (t + 1) * (2 * Bn)` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(tm + 1) EXP n` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `((4 * Bn) * (2 * t + 1)) EXP n` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[EXP_MONO_LE]; ALL_TAC] THEN
  REWRITE_TAC[MULT_EXP; GSYM MULT_ASSOC] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `a:num <= b ==> b <= c ==> a <= c`) o check (fun th ->
    free_in `W:num` (concl th) && not(is_eq(concl th)))) THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC LE_TRANS `(2 * m) EXP n` THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC LE_TRANS `tm EXP n` THEN ASM_REWRITE_TAC[EXP_MONO_LE]);;

let NUMBER_FIELD_IDEAL_COUNT_BOUNDS = prove
 (`!k:A ring.
        number_field k
        ==> ?c C. !N. N <= c * CARD {j | ring_ideal (ring_of_integers k) j /\
                                         ~(j = {ring_0 k}) /\
                                         ideal_norm (ring_of_integers k) j
                                         <= N} /\
                      CARD {j | ring_ideal (ring_of_integers k) j /\
                                ~(j = {ring_0 k}) /\
                                ideal_norm (ring_of_integers k) j <= N}
                      <= C * N`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_IDEAL_COUNT_UPPER) THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_IDEAL_COUNT_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_TAC `N0:num`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `C:num`) THEN
  MAP_EVERY EXISTS_TAC [`c + N0:num`; `C:num`] THEN X_GEN_TAC `N:num` THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `X = CARD {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                  ideal_norm (ring_of_integers k) (j:A->bool) <= N}` THEN
  ASM_CASES_TAC `N0:num <= N` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
      free_in `N0:num` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
  SUBGOAL_THEN `1 <= X` MP_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0; NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `ring_carrier(ring_of_integers k:A ring)` THEN
    REWRITE_TAC[RING_IDEAL_CARRIER; IDEAL_NORM_CARRIER] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\s. (ring_1 k:A) IN s`) THEN
    REWRITE_TAC[IN_SING] THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_1) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[NUMBER_FIELD_IMP_FIELD; FIELD_NONTRIVIAL];
    DISCH_TAC] THEN
  TRANS_TAC LE_TRANS `N0 * X:num` THEN CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `N0 * 1:num` THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Sums over finite sets of ideals, grouped by the norm.                     *)
(* ------------------------------------------------------------------------- *)

let SUM_GROUP_CARD = prove
 (`!(f:A->B) (g:B->real) s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> sum s (\x. g(f x)) =
            sum t (\y. &(CARD {x | x IN s /\ f x = y}) * g y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `\x:A. (g:B->real)(f x)`; `s:A->bool`;
                 `t:B->bool`] SUM_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `sum {x | x IN s /\ (f:A->B) x = y} (\x. (g:B->real) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT]]);;

let VSUM_GROUP_CARD = prove
 (`!(f:A->B) (g:B->complex) s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> vsum s (\x. g(f x)) =
            vsum t (\y. Cx(&(CARD {x | x IN s /\ f x = y})) * g y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `\x:A. (g:B->complex)(f x)`; `s:A->bool`;
                 `t:B->bool`] VSUM_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `vsum {x | x IN s /\ (f:A->B) x = y} (\x. (g:B->complex) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
    ASM_SIMP_TAC[VSUM_CONST; FINITE_RESTRICT; COMPLEX_CMUL]]);;

let NUMBER_FIELD_IDEAL_SUM_BY_NORM = prove
 (`!k:A ring S (g:num->real) M.
        number_field k /\
        (!j. j IN S
             ==> ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}))
        ==> FINITE {j | j IN S /\ ideal_norm (ring_of_integers k) j <= M} /\
            sum {j | j IN S /\ ideal_norm (ring_of_integers k) j <= M}
                (\j. g(ideal_norm (ring_of_integers k) j)) =
            sum(1..M) (\m. &(CARD {j | j IN S /\
                                       ideal_norm (ring_of_integers k) j =
                                       m}) * g m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                     ideal_norm (ring_of_integers k) (j:A->bool) <= M}` THEN
    ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`ideal_norm (ring_of_integers k):(A->bool)->num`;
                 `g:num->real`;
                 `{j | j IN S /\ ideal_norm (ring_of_integers k) (j:A->bool)
                                 <= M}`;
                 `1..M`] SUM_GROUP_CARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IDEAL_NORM_POS THEN
    MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The Dedekind zeta function.                                               *)
(* ------------------------------------------------------------------------- *)

let dedekind_zeta = new_definition
 `dedekind_zeta (k:A ring) s =
        infsum (from 1)
         (\m. Cx(&(CARD {j | ring_ideal (ring_of_integers k) j /\
                             ~(j = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) j = m})) /
              Cx(&m) cpow s)`;;

let NUMBER_FIELD_IDEAL_COUNT_SUM = prove
 (`!k:A ring N.
        number_field k
        ==> sum(1..N) (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                                      ~(j = {ring_0 k}) /\
                                      ideal_norm (ring_of_integers k) j =
                                      m})) =
            &(CARD {j | ring_ideal (ring_of_integers k) j /\
                        ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) j <= N})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`;
                 `{j | ring_ideal (ring_of_integers k) j /\
                       ~(j = {ring_0(k:A ring)})}`;
                 `\m:num. &1:real`; `N:num`]
    NUMBER_FIELD_IDEAL_SUM_BY_NORM) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_RID; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID]);;

let NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE = prove
 (`!k:A ring s.
        number_field k /\ &1 < s
        ==> real_summable (from 1)
             (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                              ~(j = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) j = m}) /
                  &m rpow s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_IDEAL_COUNT_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C:num`) THEN
  MP_TAC(ISPECL
   [`\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                    ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}):real`;
    `&C:real`; `&0:real`; `0`; `s:real`]
   DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS) THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_COUNT_SUM; REAL_POS; REAL_LE_REFL;
               REAL_MUL_LZERO; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_POS]);;

let DEDEKIND_ZETA_CONVERGES = prove
 (`!k:A ring s.
        number_field k /\ &1 < Re s
        ==> ((\m. Cx(&(CARD {j | ring_ideal (ring_of_integers k) j /\
                                 ~(j = {ring_0 k}) /\
                                 ideal_norm (ring_of_integers k) j = m})) /
                  Cx(&m) cpow s)
             sums dedekind_zeta k s) (from 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dedekind_zeta; SUMS_INFSUM] THEN
  MATCH_MP_TAC SUMMABLE_COMPARISON THEN
  EXISTS_TAC
   `\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                    ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
        &m rpow (Re s)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_SUMMABLE] THEN
    MATCH_MP_TAC NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `1` THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[IN_FROM; GE] THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[NORM_CPOW; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_LE_REFL]]);;

let DEDEKIND_ZETA_REAL = prove
 (`!k:A ring s.
        number_field k /\ &1 < s
        ==> ((\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                              ~(j = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) j = m}) /
                  &m rpow s)
             real_sums Re(dedekind_zeta k (Cx s))) (from 1) /\
            dedekind_zeta k (Cx s) = Cx(Re(dedekind_zeta k (Cx s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `s:real`]
    NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_SUMS_INFSUM]) THEN
  ABBREV_TAC
   `z = real_infsum (from 1)
         (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                          ~(j = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
              &m rpow s)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `dedekind_zeta (k:A ring) (Cx s) = Cx z` ASSUME_TAC THENL
   [MATCH_MP_TAC SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`\m. Cx(&(CARD {j | ring_ideal (ring_of_integers k) j /\
                          ~(j = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) (j:A->bool) = m})) /
           Cx(&m) cpow (Cx s)`; `from 1`] THEN
    ASM_SIMP_TAC[DEDEKIND_ZETA_CONVERGES; RE_CX] THEN
    MATCH_MP_TAC SUMS_EQ THEN
    EXISTS_TAC
     `Cx o (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                            ~(j = {ring_0 k}) /\
                            ideal_norm (ring_of_integers k) (j:A->bool) =
                            m}) / &m rpow s)` THEN
    ASM_REWRITE_TAC[GSYM REAL_SUMS_COMPLEX] THEN
    REWRITE_TAC[IN_FROM; o_THM] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[CX_DIV; CX_RPOW; REAL_OF_NUM_LT; LE_1];
    ASM_REWRITE_TAC[RE_CX]]);;

let DEDEKIND_ZETA_REAL_INFSUM = prove
 (`!k:A ring s.
        number_field k /\ &1 < s
        ==> real_infsum (from 1)
             (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                              ~(j = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) j = m}) /
                  &m rpow s) =
            Re(dedekind_zeta k (Cx s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  ASM_SIMP_TAC[DEDEKIND_ZETA_REAL]);;

let DEDEKIND_ZETA_POLE_BOUNDS = prove
 (`!k:A ring.
        number_field k
        ==> ?c C. &0 < c /\
                  !s. &1 < s /\ s <= &2
                      ==> c / (s - &1) <= Re(dedekind_zeta k (Cx s)) /\
                          Re(dedekind_zeta k (Cx s)) <= C / (s - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_IDEAL_COUNT_BOUNDS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  MAP_EVERY X_GEN_TAC [`c0:num`; `C0:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(c0 = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th ->
      free_in `c0:num` (concl th))) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv(&c0):real`; `&2 * &C0:real`] THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_NZ] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                    ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}):real`;
    `&C0:real`; `inv(&c0):real`; `0`; `s:real`]
   DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS) THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_COUNT_SUM; DEDEKIND_ZETA_REAL_INFSUM] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ; REAL_OF_NUM_MUL;
                    REAL_OF_NUM_LE; LE_0] THEN
    X_GEN_TAC `N:num` THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_NZ] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `s:real` REAL_INFSUM_ZETA_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Z = real_infsum (from 1) (\m. inv(&m rpow s))` THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&c0) * Z:real` THEN
    ASM_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&C0 * Z:real` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&C0 * s / (s - &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_LE_INV_EQ] THEN
                      ASM_REAL_ARITH_TAC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&2 * c = c * &2:real`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]]]);;

(* ------------------------------------------------------------------------- *)
(* The Euler product.                                                        *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_FINITE_EULER_PRODUCT = prove
 (`!r t E s.
        dedekind_domain r /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        FINITE(ring_carrier(quotient_ring r P)))
        ==> cproduct t (\P. vsum(0..E)
                              (\i. inv(Cx(&(ideal_norm r P)) cpow s) pow i)) =
            vsum (IMAGE (\e. ideal_product r t (\P. ideal_pow r P (e P)))
                        {e | (!P. P IN t ==> e P <= E) /\
                             (!P. ~(P IN t) ==> e P = 0)})
                 (\j:A->bool. inv(Cx(&(ideal_norm r j)) cpow s))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CPRODUCT_VSUM_POW] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{e:(A->bool)->num | (!P. P IN t ==> e P IN 0..E) /\
                                      (!P. ~(P IN t) ==> e P = 0)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_FUNSPACE THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`e:(A->bool)->num`; `f:(A->bool)->num`] THEN
    STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `P:A->bool` THEN
    ASM_CASES_TAC `(P:A->bool) IN t` THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `t:(A->bool)->bool`; `e:(A->bool)->num`]
      DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS) THEN
    MP_TAC(ISPECL [`r:A ring`; `t:(A->bool)->bool`; `f:(A->bool)->num`]
      DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `P:A->bool`) THEN ASM_SIMP_TAC[] THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `e:(A->bool)->num` THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `t:(A->bool)->bool`; `e:(A->bool)->num`]
    DEDEKIND_IDEAL_NORM_PRIME_POWERS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[CPOW_NPRODUCT; CPOW_NUM_EXP; GSYM CPRODUCT_INV] THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN REWRITE_TAC[COMPLEX_POW_INV]);;

let NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT = prove
 (`!k:A ring n E j.
        number_field k /\ n <= E /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
        ideal_norm (ring_of_integers k) j <= n
        ==> ?e. (!P. P IN {P | prime_ideal (ring_of_integers k) P /\
                               ~(P = {ring_0 k}) /\
                               ideal_norm (ring_of_integers k) P <= n}
                     ==> e P <= E) /\
                (!P. ~(P IN {P | prime_ideal (ring_of_integers k) P /\
                                 ~(P = {ring_0 k}) /\
                                 ideal_norm (ring_of_integers k) P <= n})
                     ==> e P = 0) /\
                j = ideal_product (ring_of_integers k)
                      {P | prime_ideal (ring_of_integers k) P /\
                           ~(P = {ring_0 k}) /\
                           ideal_norm (ring_of_integers k) P <= n}
                      (\P. ideal_pow (ring_of_integers k) P (e P))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `t = {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (P:A->bool) <= n}` THEN
  SUBGOAL_THEN `dedekind_domain(ring_of_integers k:A ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(t:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                     ideal_norm (ring_of_integers k) (j:A->bool) <= n}` THEN
    ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(ring_carrier(quotient_ring (ring_of_integers k) (j:A->bool)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(ideal_norm (ring_of_integers k) (j:A->bool) = 0)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[IDEAL_NORM_POS; ARITH_RULE `~(1 <= 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        ~(ideal_valuation (ring_of_integers k) P j = 0)
        ==> (P:A->bool) IN t /\
            ideal_valuation (ring_of_integers k) P j <= E`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    ABBREV_TAC `v = ideal_valuation (ring_of_integers k) P (j:A->bool)` THEN
    SUBGOAL_THEN
     `FINITE(ring_carrier(quotient_ring (ring_of_integers k) (P:A->bool))) /\
      2 <= ideal_norm (ring_of_integers k) P`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT; PRIME_IMP_RING_IDEAL] THEN
      REWRITE_TAC[ARITH_RULE `2 <= n <=> 1 < n`] THEN
      MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT; PRIME_IMP_RING_IDEAL] THEN
      ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL_ALT; prime_ideal;
                    proper_ideal];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ideal_norm (ring_of_integers k) P EXP v <=
      ideal_norm (ring_of_integers k) (j:A->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `v:num`]
        IDEAL_NORM_IDEAL_POW) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      MATCH_MP_TAC IDEAL_NORM_SUBSET_DIVIDES THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `j:A->bool`;
                     `v:num`] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN
      ASM_REWRITE_TAC[LE_REFL; RING_OF_INTEGERS];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `ideal_norm (ring_of_integers k) (j:A->bool)` THEN
      ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS
       `ideal_norm (ring_of_integers k) (P:A->bool) EXP v` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `a EXP 1 <= b ==> a <= b`) THEN
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LT_IMP_LE THEN
      TRANS_TAC LTE_TRANS `2 EXP v` THEN REWRITE_TAC[LT_POW2_REFL] THEN
      TRANS_TAC LE_TRANS
       `ideal_norm (ring_of_integers k) (P:A->bool) EXP v` THEN
      ASM_SIMP_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC
   `\P. if P IN t then ideal_valuation (ring_of_integers k) P (j:A->bool)
        else 0` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `ideal_valuation (ring_of_integers k) P (j:A->bool) = 0` THEN
    ASM_REWRITE_TAC[LE_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(P:A->bool) IN t` THEN EXPAND_TAC "t" THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `t:(A->bool)->bool`;
     `\P. if P IN t then ideal_valuation (ring_of_integers k) P (j:A->bool)
          else 0`] DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    SIMP_TAC[IN_ELIM_THM; RING_OF_INTEGERS];
    REWRITE_TAC[RING_OF_INTEGERS] THEN STRIP_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    (ISPEC `ring_of_integers k:A ring` DEDEKIND_IDEAL_EQ_VALUATION) o snd) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let DEDEKIND_ZETA_EULER_PRODUCT_BOUND = prove
 (`!k:A ring s n.
        number_field k /\ &1 < Re s
        ==> norm(cproduct {P | prime_ideal (ring_of_integers k) P /\
                               ~(P = {ring_0 k}) /\
                               ideal_norm (ring_of_integers k) P <= n}
                          (\P. inv(Cx(&1) -
                                   inv(Cx(&(ideal_norm (ring_of_integers k) P))
                                       cpow s))) -
                 dedekind_zeta k s)
            <= real_infsum (from (n + 1))
                 (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                                  ~(j = {ring_0 k}) /\
                                  ideal_norm (ring_of_integers k) j = m}) /
                      &m rpow Re s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dedekind_domain(ring_of_integers k:A ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS]; ALL_TAC] THEN
  ABBREV_TAC
   `t = {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (P:A->bool) <= n}` THEN
  ABBREV_TAC
   `g = \m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                        ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
            &m rpow Re s` THEN
  ABBREV_TAC
   `a = \m. CARD {j | ring_ideal (ring_of_integers k) j /\
                      ~(j = {ring_0 k}) /\
                      ideal_norm (ring_of_integers k) (j:A->bool) = m}` THEN
  SUBGOAL_THEN
   `FINITE(t:(A->bool)->bool) /\
    !P. P IN t
        ==> prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
            FINITE(ring_carrier(quotient_ring (ring_of_integers k) P)) /\
            2 <= ideal_norm (ring_of_integers k) P`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) <= n}` THEN
      ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[PRIME_IMP_RING_IDEAL];
      EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT; PRIME_IMP_RING_IDEAL];
        DISCH_TAC THEN REWRITE_TAC[ARITH_RULE `2 <= n <=> 1 < n`] THEN
        MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
        ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
        ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL_ALT; prime_ideal;
                      proper_ideal]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN t
        ==> norm(inv(Cx(&(ideal_norm (ring_of_integers k) (P:A->bool)))
                     cpow s)) < &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN
    SUBGOAL_THEN `2 <= ideal_norm (ring_of_integers k) (P:A->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_CPOW; REAL_CX; RE_CX; REAL_OF_NUM_LT;
                 ARITH_RULE `2 <= n ==> 0 < n`] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC RPOW_LT_1 THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 1) g /\ !m. &0 <= (g:num->real) m`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    SIMP_TAC[REAL_POS; RPOW_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!E. n <= E
        ==> norm(cproduct t (\P. vsum(0..E)
                   (\i. inv(Cx(&(ideal_norm (ring_of_integers k)
                                   (P:A->bool))) cpow s) pow i)) -
                 dedekind_zeta k s)
            <= real_infsum (from (n + 1)) g`
  ASSUME_TAC THENL
   [X_GEN_TAC `E:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `t:(A->bool)->bool`;
                   `E:num`; `s:complex`] DEDEKIND_FINITE_EULER_PRODUCT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_OF_INTEGERS]; DISCH_THEN SUBST1_TAC] THEN
    ABBREV_TAC
     `EF = {e | (!P. P IN t ==> e P <= E) /\
               (!P:A->bool. ~(P IN t) ==> e P = 0)}` THEN
    ABBREV_TAC
     `IM = IMAGE (\e. ideal_product (ring_of_integers k) t
                       (\P:A->bool. ideal_pow (ring_of_integers k) P (e P)))
                 EF` THEN
    SUBGOAL_THEN `FINITE(EF:((A->bool)->num)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{e:(A->bool)->num | (!P. P IN t ==> e P IN 0..E) /\
                                      (!P. ~(P IN t) ==> e P = 0)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_FUNSPACE THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
        EXPAND_TAC "EF" THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `FINITE(IM:(A->bool)->bool) /\
      !j. j IN IM
          ==> ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
              FINITE(ring_carrier(quotient_ring (ring_of_integers k) j)) /\
              1 <= ideal_norm (ring_of_integers k) j`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "IM" THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `e:(A->bool)->num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `t:(A->bool)->bool`;
                     `e:(A->bool)->num`]
        DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[RING_OF_INTEGERS];
        REWRITE_TAC[RING_OF_INTEGERS] THEN STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT];
        REWRITE_TAC[IDEAL_NORM_POS]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o
      ISPEC `ideal_norm (ring_of_integers k):(A->bool)->num` o
      MATCH_MP UPPER_BOUND_FINITE_SET) THEN
    DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    ABBREV_TAC
     `b = \m. CARD {j | j IN IM /\
                        ideal_norm (ring_of_integers k) (j:A->bool) = m}` THEN
    SUBGOAL_THEN `!m. (b:num->num) m <= (a:num->num) m` ASSUME_TAC THENL
     [X_GEN_TAC `m:num` THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC
         `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (j:A->bool) <= m}` THEN
        ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `!m. m <= n ==> (b:num->num) m = (a:num->num) m`
    ASSUME_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`k:A ring`; `n:num`; `E:num`; `j:A->bool`]
          NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:(A->bool)->num` STRIP_ASSUME_TAC) THEN
        EXPAND_TAC "IM" THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `e:(A->bool)->num` THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "EF" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC
     `\N. vsum (IM:(A->bool)->bool)
            (\j. inv(Cx(&(ideal_norm (ring_of_integers k) j)) cpow s)) -
          vsum(1..N) (\m. Cx(&((a:num->num) m)) / Cx(&m) cpow s)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
      MP_TAC(ISPECL [`k:A ring`; `s:complex`] DEDEKIND_ZETA_CONVERGES) THEN
      ASM_REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `M + n:num` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ideal_norm (ring_of_integers k):(A->bool)->num`;
                   `\m. inv(Cx(&m) cpow s)`; `IM:(A->bool)->bool`;
                   `1..N`] VSUM_GROUP_CARD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
      X_GEN_TAC `j:A->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      TRANS_TAC LE_TRANS `M:num` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; ASM_ARITH_TAC];
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
    SUBGOAL_THEN
     `!m. 1 <= m
          ==> norm(Cx(&(CARD {j | j IN IM /\
                                  ideal_norm (ring_of_integers k)
                                    (j:A->bool) = m})) *
                   inv(Cx(&m) cpow s) -
                   Cx(&((a:num->num) m)) / Cx(&m) cpow s) =
              (&(a m) - &((b:num->num) m)) / &m rpow Re s`
    ASSUME_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `CARD {j | j IN IM /\ ideal_norm (ring_of_integers k) (j:A->bool) = m} =
        (b:num->num) m`
      SUBST1_TAC THENL [EXPAND_TAC "b" THEN REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[complex_div; GSYM COMPLEX_SUB_RDISTRIB; GSYM CX_SUB] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_INV] THEN
      ASM_SIMP_TAC[NORM_CPOW; REAL_CX; RE_CX; REAL_OF_NUM_LT; LE_1] THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; real_div] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> abs(x - y) = y - x:real`) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum(1..N) (\m. (&((a:num->num) m) - &((b:num->num) m)) /
                     &m rpow Re s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `N:num = n + (N - n)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
    SUBGOAL_THEN
     `sum(1..n) (\m. (&((a:num->num) m) - &((b:num->num) m)) /
                     &m rpow Re s) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
      ASM_SIMP_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO];
      REWRITE_TAC[REAL_ADD_LID]] THEN
    TRANS_TAC REAL_LE_TRANS `sum(n + 1..n + (N - n)) (g:num->real)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS] THEN
      EXPAND_TAC "a" THEN REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `(x:real) - y <= x <=> &0 <= y`; REAL_POS];
      MP_TAC(ISPECL [`g:num->real`; `from (n + 1)`; `n + (N - n):num`]
        REAL_PARTIAL_SUMS_LE_INFSUM) THEN
      REWRITE_TAC[FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[REAL_SUMMABLE_FROM_ELSEWHERE_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
   `\E. cproduct t (\P. vsum(0..E)
          (\i. inv(Cx(&(ideal_norm (ring_of_integers k) (P:A->bool)))
                   cpow s) pow i)) - dedekind_zeta k s` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
  MATCH_MP_TAC LIM_CPRODUCT THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o MATCH_MP SUMS_GP) THEN
  REWRITE_TAC[sums; FROM_0; INTER_UNIV; complex_pow] THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LID]);;

let DEDEKIND_ZETA_EULER_PRODUCT = prove
 (`!k:A ring s.
        number_field k /\ &1 < Re s
        ==> ((\n. cproduct {P | prime_ideal (ring_of_integers k) P /\
                               ~(P = {ring_0 k}) /\
                               ideal_norm (ring_of_integers k) P <= n}
                          (\P. inv(Cx(&1) -
                                   inv(Cx(&(ideal_norm (ring_of_integers k) P))
                                       cpow s))))
             --> dedekind_zeta k s) sequentially`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `g = \m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                        ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
            &m rpow Re s` THEN
  MP_TAC(ISPECL [`k:A ring`; `Re s`]
    NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_SUMS_INFSUM]) THEN
  ABBREV_TAC `l = real_infsum (from 1) (g:num->real)` THEN DISCH_TAC THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_SERIES_FROM]) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `real_infsum (from (n + 1)) (g:num->real)` THEN CONJ_TAC THENL
   [EXPAND_TAC "g" THEN ASM_SIMP_TAC[DEDEKIND_ZETA_EULER_PRODUCT_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_infsum (from (n + 1)) g = l - sum(1..n) (g:num->real)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
    MP_TAC(ISPECL [`g:num->real`; `l:real`; `1`; `n + 1`]
      REAL_SUMS_OFFSET) THEN
    ASM_REWRITE_TAC[ADD_SUB] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The prime ideals near s = 1.                                              *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_ZETA_EULER_PRODUCT_REAL = prove
 (`!k:A ring s.
        number_field k /\ &1 < s
        ==> ((\n. product {P | prime_ideal (ring_of_integers k) P /\
                              ~(P = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) P <= n}
                         (\P. inv(&1 -
                                  inv(&(ideal_norm (ring_of_integers k) P)
                                      rpow s))))
             ---> Re(dedekind_zeta k (Cx s))) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_COMPLEX] THEN
  MP_TAC(ISPECL [`k:A ring`; `s:real`] DEDEKIND_ZETA_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  MP_TAC(ISPECL [`k:A ring`; `Cx s`] DEDEKIND_ZETA_EULER_PRODUCT) THEN
  ASM_REWRITE_TAC[RE_CX] THEN
  SUBGOAL_THEN
   `!n. cproduct {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0 k}) /\
                      ideal_norm (ring_of_integers k) P <= n}
                 (\P. inv(Cx(&1) -
                          inv(Cx(&(ideal_norm (ring_of_integers k) P))
                              cpow Cx s))) =
        Cx(product {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) (P:A->bool) <= n}
                   (\P. inv(&1 -
                            inv(&(ideal_norm (ring_of_integers k) P)
                                rpow s))))`
  (fun th -> REWRITE_TAC[th; o_DEF]) THEN
  X_GEN_TAC `n:num` THEN
  ASM_SIMP_TAC[CX_PRODUCT; NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `P:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`]
    NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CX_INV; CX_SUB; CX_RPOW; REAL_OF_NUM_LT;
               ARITH_RULE `2 <= n ==> 0 < n`]);;

let DEDEKIND_ZETA_LOG_PRIME_IDEALS = prove
 (`!k:A ring s.
        number_field k /\ &1 < s
        ==> real_summable (from 1)
             (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                              ~(P = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) P = m}) /
                  &m rpow s) /\
            &0 < Re(dedekind_zeta k (Cx s)) /\
            real_infsum (from 1)
             (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                              ~(P = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) P = m}) /
                  &m rpow s) <= log(Re(dedekind_zeta k (Cx s))) /\
            log(Re(dedekind_zeta k (Cx s))) <=
            real_infsum (from 1)
             (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                              ~(P = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) P = m}) /
                  &m rpow s) + &2 * Re(dedekind_zeta k (Cx(&2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `f = \m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
            &m rpow s` THEN
  ABBREV_TAC `Z = Re(dedekind_zeta (k:A ring) (Cx s))` THEN
  ABBREV_TAC `Z2 = Re(dedekind_zeta (k:A ring) (Cx(&2)))` THEN
  SUBGOAL_THEN
   `!m. &0 <= (f:num->real) m /\
        f m <= &(CARD {j | ring_ideal (ring_of_integers k) j /\
                           ~(j = {ring_0 k}) /\
                           ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
               &m rpow s`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS; RPOW_POS_LE] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_RING_IDEAL];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) <= m}` THEN
      ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 1) (f:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC
     `\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                      ~(j = {ring_0 k}) /\
                      ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
          &m rpow s` THEN
    ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE] THEN
    EXISTS_TAC `0` THEN ASM_SIMP_TAC[real_abs];
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `PS = real_infsum (from 1) (f:num->real)` THEN
  ABBREV_TAC
   `TP = \n. {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                 ideal_norm (ring_of_integers k) (P:A->bool) <= n}` THEN
  SUBGOAL_THEN
   `!n. FINITE((TP:num->(A->bool)->bool) n) /\
        !P. P IN TP n
            ==> &0 < inv(&(ideal_norm (ring_of_integers k) P) rpow s) /\
                inv(&(ideal_norm (ring_of_integers k) P) rpow s) <= inv(&2) /\
                inv(&(ideal_norm (ring_of_integers k) P) rpow s) pow 2 <=
                inv(&(ideal_norm (ring_of_integers k) P) rpow &2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "TP" THEN
    ASM_SIMP_TAC[NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN
    X_GEN_TAC `P:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`]
      NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `q = &(ideal_norm (ring_of_integers k) (P:A->bool)):real` THEN
    SUBGOAL_THEN `&2 <= (q:real)` ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 <= q rpow s` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q rpow &1` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1];
        MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_INV] THEN
      REWRITE_TAC[REAL_POW_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(q rpow s) pow 2 = q rpow (s + s)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[RPOW_ADD; REAL_POW_2;
                     REAL_ARITH `&2 <= (q:real) ==> &0 < q`];
        MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. sum ((TP:num->(A->bool)->bool) n)
            (\P. inv(&(ideal_norm (ring_of_integers k) P) rpow s)) =
        sum(1..n) f`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "TP" THEN
    MP_TAC(ISPECL [`k:A ring`;
       `{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0(k:A ring)})}`;
       `\m. inv(&m rpow s)`; `n:num`] NUMBER_FIELD_IDEAL_SUM_BY_NORM) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[IN_ELIM_THM; PRIME_IMP_RING_IDEAL]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. sum ((TP:num->(A->bool)->bool) n)
            (\P. inv(&(ideal_norm (ring_of_integers k) P) rpow s) pow 2) <= Z2`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    TRANS_TAC REAL_LE_TRANS
     `sum ((TP:num->(A->bool)->bool) n)
          (\P. inv(&(ideal_norm (ring_of_integers k) P) rpow &2))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_LE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (j:A->bool) <= n}
          (\j. inv(&(ideal_norm (ring_of_integers k) j) rpow &2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
      SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS] THEN
      EXPAND_TAC "TP" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[PRIME_IMP_RING_IDEAL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`;
       `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0(k:A ring)})}`;
       `\m. inv(&m rpow &2)`; `n:num`] NUMBER_FIELD_IDEAL_SUM_BY_NORM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`k:A ring`; `(&2:real)`] DEDEKIND_ZETA_REAL_INFSUM) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM real_div] THEN
    MP_TAC(ISPECL
     [`\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                       ~(j = {ring_0 k}) /\
                       ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
           &m rpow &2`; `from 1`; `n:num`] REAL_PARTIAL_SUMS_LE_INFSUM) THEN
    REWRITE_TAC[FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE; REAL_OF_NUM_LT;
                 ARITH] THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS; RPOW_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. exp(sum(1..n) f) <=
        product ((TP:num->(A->bool)->bool) n)
          (\P. inv(&1 - inv(&(ideal_norm (ring_of_integers k) P) rpow s))) /\
        product ((TP:num->(A->bool)->bool) n)
          (\P. inv(&1 - inv(&(ideal_norm (ring_of_integers k) P) rpow s))) <=
        exp(PS + &2 * Z2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && is_conj(snd(dest_forall(concl th))))) THEN
    CONJ_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM(SPEC `n:num` th)]) o check
       (fun th -> is_forall(concl th) &&
                  is_eq(snd(dest_forall(concl th))) &&
                  free_in `f:num->real` (concl th))) THEN
      ASM_SIMP_TAC[REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_LE THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
      X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_EXP_LE_INV_1_SUB THEN
      FIRST_ASSUM(MP_TAC o SPEC `P:A->bool` o check (fun th ->
        is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(REAL_ARITH `inv(&2) < &1`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `exp(sum ((TP:num->(A->bool)->bool) n)
            (\P. inv(&(ideal_norm (ring_of_integers k) P) rpow s) +
                 &2 * inv(&(ideal_norm (ring_of_integers k) P) rpow s)
                      pow 2))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_LE THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `P:A->bool` o check (fun th ->
        is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN
        MP_TAC(REAL_ARITH `inv(&2) < &1`) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_1_SUB_LE_EXP THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[SUM_ADD; SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [EXPAND_TAC "PS" THEN
      MP_TAC(ISPECL [`f:num->real`; `from 1`; `n:num`]
        REAL_PARTIAL_SUMS_LE_INFSUM) THEN
      ASM_REWRITE_TAC[FROM_INTER_NUMSEG];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `s:real`] DEDEKIND_ZETA_EULER_PRODUCT_REAL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (P:A->bool) <= n} = TP n`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "TP" THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `exp PS <= Z /\ Z <= exp(PS + &2 * Z2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
      EXISTS_TAC `\n. exp(sum(1..n) (f:num->real))` THEN
      EXISTS_TAC
       `\n. product ((TP:num->(A->bool)->bool) n)
              (\P. inv(&1 - inv(&(ideal_norm (ring_of_integers k) P)
                               rpow s)))` THEN
      ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE] THEN
      MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
      REWRITE_TAC[REAL_CONTINUOUS_AT_EXP] THEN
      REWRITE_TAC[GSYM REAL_SERIES_FROM] THEN EXPAND_TAC "PS" THEN
      ASM_REWRITE_TAC[REAL_SUMS_INFSUM];
      MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
      EXISTS_TAC
       `\n. product ((TP:num->(A->bool)->bool) n)
              (\P. inv(&1 - inv(&(ideal_norm (ring_of_integers k) P)
                               rpow s)))` THEN
      ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Z:real)` ASSUME_TAC THENL
   [MP_TAC(SPEC `PS:real` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[]]);;

let NUMBER_FIELD_NONPRIME_NORM_SUM_LE = prove
 (`!k:A ring s N.
        number_field k /\ &1 <= s
        ==> sum {q | prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
                     ~prime(ideal_norm (ring_of_integers k) q) /\
                     ideal_norm (ring_of_integers k) q <= N}
                (\q. inv(&(ideal_norm (ring_of_integers k) q) rpow s))
            <= &2 * &(extension_degree (subfield_generated k {ring_0 k},k) I)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
  ABBREV_TAC
   `Cc = {q | prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
              ~prime(ideal_norm (ring_of_integers k) q) /\
              ideal_norm (ring_of_integers k) (q:A->bool) <= N}` THEN
  SUBGOAL_THEN `FINITE(Cc:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
           ideal_norm (ring_of_integers k) (j:A->bool) <= N}` THEN
    ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
    EXPAND_TAC "Cc" THEN SIMP_TAC[SUBSET; IN_ELIM_THM; PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?pb. !q:A->bool. q IN Cc ==> prime(pb q) /\ ring_of_num k (pb q) IN q`
  (X_CHOOSE_TAC `pb:(A->bool)->num`) THENL
   [REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM; GSYM SKOLEM_THM] THEN
    X_GEN_TAC `q:A->bool` THEN EXPAND_TAC "Cc" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `q:A->bool`]
      RING_OF_INTEGERS_PRIME_IDEAL_ABOVE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:A->bool. q IN Cc
        ==> inv(&(ideal_norm (ring_of_integers k) q) rpow s) <=
            inv(&(pb q) pow 2) /\
            1 <= pb q /\ pb q <= N`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:A->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(q:A->bool) IN Cc`)) THEN
    STRIP_TAC THEN UNDISCH_TAC `(q:A->bool) IN Cc` THEN EXPAND_TAC "Cc" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `q:A->bool`; `pb(q:A->bool):num`]
      RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN
    MP_TAC(ISPECL [`k:A ring`; `q:A->bool`; `pb(q:A->bool):num`]
      NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `f = residue_degree (integer_ring,ring_of_integers k)
                      (ring_of_int k) (q:A->bool)` THEN
    STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `2 <= f` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= f <=> 1 <= f /\ ~(f = 1)`] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~prime(ideal_norm (ring_of_integers k) (q:A->bool))` THEN
      ASM_REWRITE_TAC[EXP_1];
      ALL_TAC] THEN
    SUBGOAL_THEN `2 <= pb(q:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    SUBGOAL_THEN
     `pb(q:A->bool) EXP 2 <= ideal_norm (ring_of_integers k) q`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `pb(q:A->bool) <= pb q EXP 2` ASSUME_TAC THENL
     [REWRITE_TAC[EXP_2; LE_SQUARE_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `ideal_norm (ring_of_integers k) (q:A->bool)`)) THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(ideal_norm (ring_of_integers k) (q:A->bool)):real` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE];
      MP_TAC(SPECL [`&1:real`; `s:real`;
                    `&(ideal_norm (ring_of_integers k) (q:A->bool)):real`]
        RPOW_MONO_LE) THEN
      REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Cc (\q:A->bool. inv(&(pb q) pow 2))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`pb:(A->bool)->num`; `\q:A->bool. inv(&(pb q) pow 2)`;
                 `Cc:(A->bool)->bool`; `1..N`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\p. &n * inv(&p pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {q | q IN Cc /\ pb q = p} (\q:A->bool. inv(&p pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS; REAL_OF_NUM_LE] THEN
    ASM_CASES_TAC `prime p` THENL
     [EXPAND_TAC "n" THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD {P | prime_ideal (ring_of_integers k) P /\
                            ring_of_num k p IN (P:A->bool)}` THEN
      ASM_SIMP_TAC[NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q] THEN
      MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `q:A->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:A->bool` o check (fun th ->
        free_in `ring_of_num (k:A ring)` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q:A->bool) IN Cc` THEN EXPAND_TAC "Cc" THEN
      SIMP_TAC[IN_ELIM_THM];
      SUBGOAL_THEN
       `{q | q IN Cc /\ (pb:(A->bool)->num) q = p} = {}:(A->bool)->bool`
      SUBST1_TAC THENL
       [REWRITE_TAC[SET_RULE
         `{x:A->bool | x IN s /\ P x} = {} <=> !x. x IN s ==> ~P x`] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[CARD_CLAUSES; LE_0]]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MP_TAC(SPEC `&2:real` REAL_INFSUM_ZETA_BOUNDS) THEN
  MP_TAC(SPECL [`1`; `&2:real`] REAL_SUMMABLE_ZETA) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[RPOW_POW] THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_infsum (from 1) (\m. inv(&m pow 2))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\m. inv(&m pow 2)`; `from 1`; `N:num`]
    REAL_PARTIAL_SUMS_LE_INFSUM) THEN
  ASM_REWRITE_TAC[FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS]);;

let DEDEKIND_ZETA_LOG_POLE = prove
 (`!k:A ring.
        number_field k
        ==> ?C. !s. &1 < s /\ s <= &2
                    ==> &0 < Re(dedekind_zeta k (Cx s)) /\
                        abs(log(Re(dedekind_zeta k (Cx s))) + log(s - &1))
                        <= C`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DEDEKIND_ZETA_POLE_BOUNDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `abs(log c) + abs(log C)` THEN X_GEN_TAC `s:real` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Z = Re(dedekind_zeta (k:A ring) (Cx s))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (s:real) - &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c / (s - &1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Z:real) /\ &0 < (C:real)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < C / (s - &1)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`c / (s - &1)`; `Z:real`] LOG_MONO_LE_IMP) THEN
  MP_TAC(ISPECL [`Z:real`; `C / (s - &1)`] LOG_MONO_LE_IMP) THEN
  ASM_SIMP_TAC[LOG_DIV] THEN REAL_ARITH_TAC);;

let NUMBER_FIELD_PRIME_IDEALS_LOG = prove
 (`!k:A ring.
        number_field k
        ==> ?C. !s. &1 < s /\ s <= &2
                    ==> real_summable (from 1)
                         (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                                          ~(P = {ring_0 k}) /\
                                          ideal_norm (ring_of_integers k) P =
                                          m}) /
                              &m rpow s) /\
                        abs(real_infsum (from 1)
                             (\m. &(CARD {P | prime_ideal
                                               (ring_of_integers k) P /\
                                              ~(P = {ring_0 k}) /\
                                              ideal_norm
                                               (ring_of_integers k) P = m}) /
                                  &m rpow s) +
                            log(s - &1)) <= C`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `C:real` o MATCH_MP DEDEKIND_ZETA_LOG_POLE) THEN
  SUBGOAL_THEN `&0 < Re(dedekind_zeta (k:A ring) (Cx(&2)))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `(&2:real)`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `C + &2 * Re(dedekind_zeta (k:A ring) (Cx(&2)))` THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `s:real`] DEDEKIND_ZETA_LOG_PRIME_IDEALS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 < z2
    ==> (&0 < (z:real) /\ abs((lz:real) + l) <= C)
        ==> (&0 < z /\ x <= lz /\ lz <= x + &2 * z2)
            ==> abs(x + l) <= C + &2 * z2`) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG = prove
 (`!k:A ring.
        number_field k
        ==> ?C. !s. &1 < s /\ s <= &2
                    ==> real_summable (from 1)
                         (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                                          ~(P = {ring_0 k}) /\
                                          residue_degree
                                           (integer_ring,ring_of_integers k)
                                           (ring_of_int k) P = 1 /\
                                          ideal_norm (ring_of_integers k) P =
                                          m}) /
                              &m rpow s) /\
                        abs(real_infsum (from 1)
                             (\m. &(CARD {P | prime_ideal
                                               (ring_of_integers k) P /\
                                              ~(P = {ring_0 k}) /\
                                              residue_degree
                                               (integer_ring,
                                                ring_of_integers k)
                                               (ring_of_int k) P = 1 /\
                                              ideal_norm
                                               (ring_of_integers k) P = m}) /
                                  &m rpow s) +
                            log(s - &1)) <= C`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `C:real` o
    MATCH_MP NUMBER_FIELD_PRIME_IDEALS_LOG) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
  EXISTS_TAC `(C:real) + &2 * &n` THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `pf = \m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\
                         ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
             &m rpow s` THEN
  ABBREV_TAC
   `df = \m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\
                         residue_degree (integer_ring,ring_of_integers k)
                           (ring_of_int k) P = 1 /\
                         ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
             &m rpow s` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!N. sum(1..N) (\m. (pf:num->real) m - df m) =
        sum {q | prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
                 ~prime(ideal_norm (ring_of_integers k) q) /\
                 ideal_norm (ring_of_integers k) (q:A->bool) <= N}
            (\q. inv(&(ideal_norm (ring_of_integers k) q) rpow s))`
  ASSUME_TAC THENL
   [X_GEN_TAC `N:num` THEN REWRITE_TAC[SUM_SUB_NUMSEG] THEN
    MAP_EVERY EXPAND_TAC ["pf"; "df"] THEN REWRITE_TAC[real_div] THEN
    MP_TAC(ISPECL [`k:A ring`;
       `{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0(k:A ring)})}`;
       `\m. inv(&m rpow s)`; `N:num`] NUMBER_FIELD_IDEAL_SUM_BY_NORM) THEN
    MP_TAC(ISPECL [`k:A ring`;
       `{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0(k:A ring)}) /\
             residue_degree (integer_ring,ring_of_integers k)
               (ring_of_int k) P = 1}`;
       `\m. inv(&m rpow s)`; `N:num`] NUMBER_FIELD_IDEAL_SUM_BY_NORM) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; PRIME_IMP_RING_IDEAL] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC(REAL_ARITH `x:real = y + z ==> x - y = z`) THEN
    MATCH_MP_TAC(MESON[SUM_UNION]
     `FINITE s /\ FINITE t /\ DISJOINT s t /\ u = s UNION t
      ==> sum u f = sum s f + sum t (f:(A->bool)->real)`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
       `{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (P:A->bool) <= N}` THEN
      ASM_SIMP_TAC[NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. &0 <= (df:num->real) m /\ df m <= pf m` ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN MAP_EVERY EXPAND_TAC ["pf"; "df"] THEN
    REWRITE_TAC[real_div] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_INV_EQ; RPOW_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
           ideal_norm (ring_of_integers k) (P:A->bool) <= m}` THEN
    ASM_SIMP_TAC[NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 1) (df:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `pf:num->real` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `0` THEN ASM_SIMP_TAC[real_abs];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `&0 <= real_infsum (from 1) (\m. (pf:num->real) m - df m) /\
    real_infsum (from 1) (\m. (pf:num->real) m - df m) <= &2 * &n`
  MP_TAC THENL
   [SUBGOAL_THEN `real_summable (from 1) (\m. (pf:num->real) m - df m)`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_SUMMABLE_SUB]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_SUMS_INFSUM]) THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SERIES_POS THEN
      EXISTS_TAC `\m. (pf:num->real) m - df m` THEN
      EXISTS_TAC `from 1` THEN ASM_REWRITE_TAC[REAL_SUB_LE];
      MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
      EXISTS_TAC `\N. sum(1..N) (\m. (pf:num->real) m - df m)` THEN
      ASM_REWRITE_TAC[GSYM REAL_SERIES_FROM; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `N:num` THEN
      ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "n" THEN MATCH_MP_TAC NUMBER_FIELD_NONPRIME_NORM_SUM_LE THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_INFSUM_SUB] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Dirichlet densities.                                                      *)
(* ------------------------------------------------------------------------- *)

let has_dirichlet_density = new_definition
 `has_dirichlet_density (k:A ring) S d <=>
        ((\s. real_infsum (from 1)
                (\m. &(CARD {P | P IN S /\
                                 ideal_norm (ring_of_integers k) P = m}) /
                     &m rpow s) /
              log(inv(s - &1)))
         ---> d) (atreal (&1) within {s | &1 < s})`;;

let HAS_DIRICHLET_DENSITY_LOG = prove
 (`!k:A ring S d C.
        (!s. &1 < s /\ s <= &2
             ==> abs(real_infsum (from 1)
                      (\m. &(CARD {P | P IN S /\
                                       ideal_norm (ring_of_integers k) P =
                                       m}) /
                           &m rpow s) + d * log(s - &1)) <= C)
        ==> has_dirichlet_density k S d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[has_dirichlet_density; REALLIM_WITHINREAL; IN_ELIM_THM] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min (&1) (exp(--((abs C + &1) / e)))` THEN
  REWRITE_TAC[REAL_LT_MIN; REAL_EXP_POS_LT; REAL_LT_01] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `ds = real_infsum (from 1)
          (\m. &(CARD {P | P IN S /\
                           ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
               &m rpow s)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s - &1 /\ s - &1 < exp(--((abs C + &1) / e))`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(s - &1) < --((abs C + &1) / e)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_INV] THEN
  SUBGOAL_THEN `abs C + &1 < e * --log(s - &1)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --log(s - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(abs C + &1) / e` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ds / --log(s - &1) - d = (ds + d * log(s - &1)) / --log(s - &1)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < --log(s - &1)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < (x:real) ==> abs x = x`;
               REAL_LT_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_DIRICHLET_DENSITY_UNIQUE = prove
 (`!k:A ring S d d'.
        has_dirichlet_density k S d /\ has_dirichlet_density k S d'
        ==> d = d'`,
  REWRITE_TAC[has_dirichlet_density] THEN
  MESON_TAC[REALLIM_UNIQUE; SPEC `&1:real` TRIVIAL_LIMIT_ATREAL_RIGHT]);;

let HAS_DIRICHLET_DENSITY_FINITE = prove
 (`!k:A ring S. FINITE S ==> has_dirichlet_density k S (&0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_LOG THEN
  ABBREV_TAC
   `NS = IMAGE (ideal_norm (ring_of_integers k)) (S:(A->bool)->bool)` THEN
  EXISTS_TAC `(&(CARD(NS:num->bool)) * &(CARD(S:(A->bool)->bool))):real` THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
  SUBGOAL_THEN `FINITE(NS:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "NS" THEN ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\m. &(CARD {P | P IN (S:(A->bool)->bool) /\
                     ideal_norm (ring_of_integers k) P = m}) /
         &m rpow s`; `NS:num->bool`; `from 1`] REAL_SERIES_FINITE_SUPPORT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_INTER] THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[IN_INTER; IN_FROM; DE_MORGAN_THM] THEN STRIP_TAC THENL
     [SUBGOAL_THEN
       `{P | P IN S /\ ideal_norm (ring_of_integers k) P = m} =
        {}:(A->bool)->bool`
      (fun th -> REWRITE_TAC[th; CARD_CLAUSES; real_div; REAL_MUL_LZERO]) THEN
      UNDISCH_TAC `~((m:num) IN NS)` THEN EXPAND_TAC "NS" THEN SET_TAC[];
      SUBGOAL_THEN `m = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[RPOW_ZERO] THEN COND_CASES_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO]]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INFSUM_UNIQUE) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&(CARD(NS INTER from 1)) * &(CARD(S:(A->bool)->bool))):real` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_BOUND THEN ASM_SIMP_TAC[FINITE_INTER] THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_INTER; IN_FROM] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
    SUBGOAL_THEN `&1 <= &m rpow s` ASSUME_TAC THENL
     [MATCH_MP_TAC RPOW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> abs x = x:real`; REAL_LE_LDIV_EQ;
                 REAL_ARITH `&1 <= x:real ==> &0 < x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(CARD(S:(A->bool)->bool))):real` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[INTER_SUBSET]]);;

let HAS_DIRICHLET_DENSITY_INFINITE = prove
 (`!k:A ring S d.
        has_dirichlet_density k S d /\ ~(d = &0) ==> INFINITE S`,
  REWRITE_TAC[INFINITE] THEN
  MESON_TAC[HAS_DIRICHLET_DENSITY_FINITE; HAS_DIRICHLET_DENSITY_UNIQUE]);;

let NUMBER_FIELD_PRIME_IDEALS_DENSITY = prove
 (`!k:A ring.
        number_field k
        ==> has_dirichlet_density k
             {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})}
             (&1)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_LOG THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_PRIME_IDEALS_LOG) THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC; REAL_MUL_LID] THEN
  MESON_TAC[]);;

let NUMBER_FIELD_DEGREE_ONE_PRIMES_DENSITY = prove
 (`!k:A ring.
        number_field k
        ==> has_dirichlet_density k
             {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                  residue_degree (integer_ring,ring_of_integers k)
                    (ring_of_int k) P = 1}
             (&1)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_LOG THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG) THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC; REAL_MUL_LID] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The elementary laws of Dirichlet density, for sets of nonzero prime       *)
(* ideals.                                                                   *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE = prove
 (`!k:A ring S.
        number_field k /\
        S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0 k})}
        ==> (!m. FINITE {P | P IN S /\
                             ideal_norm (ring_of_integers k) P = m}) /\
            (!s. &1 < s
                 ==> real_summable (from 1)
                      (\m. &(CARD {P | P IN S /\
                                       ideal_norm (ring_of_integers k) P =
                                       m}) /
                           &m rpow s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. {P | P IN S /\ ideal_norm (ring_of_integers k) P = m} SUBSET
        {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) = m} /\
        FINITE {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN CONJ_TAC THENL
     [UNDISCH_TAC
       `S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0(k:A ring)})}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_RING_IDEAL];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) <= m}` THEN
      ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
      SIMP_TAC[SUBSET; IN_ELIM_THM; LE_REFL]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC
   `\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
        &m rpow s` THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_RPOW] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]);;

let HAS_DIRICHLET_DENSITY_DISJOINT_UNION = prove
 (`!k:A ring S1 S2 d1 d2.
        number_field k /\
        S1 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        S2 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        has_dirichlet_density k S1 d1 /\ has_dirichlet_density k S2 d2 /\
        DISJOINT S1 S2
        ==> has_dirichlet_density k (S1 UNION S2) (d1 + d2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `S2:(A->bool)->bool`]
    NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN
  MP_TAC(ISPECL [`k:A ring`; `S1:(A->bool)->bool`]
    NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `has_dirichlet_density (k:A ring) S2 d2` THEN
  UNDISCH_TAC `has_dirichlet_density (k:A ring) S1 d1` THEN
  REWRITE_TAC[has_dirichlet_density; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ADD) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_WITHIN_IMP] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM real_div] THEN
  MP_TAC(ISPECL
   [`\m. &(CARD {P | P IN S1 /\
                     ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
         &m rpow s`;
    `\m. &(CARD {P | P IN S2 /\
                     ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
         &m rpow s`;
    `from 1`] REAL_INFSUM_ADD) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB; REAL_OF_NUM_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{P | P IN S1 /\ ideal_norm (ring_of_integers k) P = m} UNION
      {P | P IN S2 /\ ideal_norm (ring_of_integers k) (P:A->bool) = m}` THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN SET_TAC[];
    UNDISCH_TAC `DISJOINT (S1:(A->bool)->bool) S2` THEN SET_TAC[];
    SET_TAC[]]);;

let HAS_DIRICHLET_DENSITY_DIFF_SUBSET = prove
 (`!k:A ring S1 S2 d1 d2.
        number_field k /\
        S1 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        has_dirichlet_density k S1 d1 /\ has_dirichlet_density k S2 d2 /\
        S2 SUBSET S1
        ==> has_dirichlet_density k (S1 DIFF S2) (d1 - d2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `S1 DIFF S2:(A->bool)->bool`]
    NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN
  MP_TAC(ISPECL [`k:A ring`; `S2:(A->bool)->bool`]
    NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN
  MP_TAC(ISPECL [`k:A ring`; `S1:(A->bool)->bool`]
    NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `has_dirichlet_density (k:A ring) S2 d2` THEN
  UNDISCH_TAC `has_dirichlet_density (k:A ring) S1 d1` THEN
  REWRITE_TAC[has_dirichlet_density; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_SUB) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_WITHIN_IMP] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `x:real = y + z ==> x - y = z`) THEN
  MP_TAC(ISPECL
   [`\m. &(CARD {P | P IN S2 /\
                     ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
         &m rpow s`;
    `\m. &(CARD {P | P IN S1 DIFF S2 /\
                     ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
         &m rpow s`;
    `from 1`] REAL_INFSUM_ADD) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB; REAL_OF_NUM_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let HAS_DIRICHLET_DENSITY_COMPLEMENT = prove
 (`!k:A ring S d.
        number_field k /\
        S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0 k})} /\
        has_dirichlet_density k S d
        ==> has_dirichlet_density k
             ({P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})}
              DIFF S)
             (&1 - d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_DIFF_SUBSET THEN
  ASM_SIMP_TAC[SUBSET_REFL; NUMBER_FIELD_PRIME_IDEALS_DENSITY]);;

let HAS_DIRICHLET_DENSITY_BOUNDS = prove
 (`!k:A ring S d.
        number_field k /\
        S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0 k})} /\
        has_dirichlet_density k S d
        ==> &0 <= d /\ d <= &1`,
  SUBGOAL_THEN
   `!k:A ring S d.
        number_field k /\
        S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0 k})} /\
        has_dirichlet_density k S d
        ==> &0 <= d`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[has_dirichlet_density] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`]
      NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `atreal (&1) within {s | &1 < s}` REALLIM_LBOUND) THEN
    EXISTS_TAC
     `\s. real_infsum (from 1)
            (\m. &(CARD {P | P IN S /\
                             ideal_norm (ring_of_integers k) (P:A->bool) =
                             m}) /
                 &m rpow s) /
          log(inv(s - &1))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_ATREAL_RIGHT] THEN
    REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM] THEN
    EXISTS_TAC `&1:real` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SERIES_POS THEN
      MAP_EVERY EXISTS_TAC
       [`\m. &(CARD {P | P IN S /\
                         ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
             &m rpow s`; `from 1`] THEN
      ASM_SIMP_TAC[REAL_SUMS_INFSUM; REAL_LE_DIV; REAL_POS; RPOW_POS_LE];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC LOG_POS_LT THEN
      MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= &1 - d ==> (d:real) <= &1`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPECL
     [`k:A ring`;
      `{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})} DIFF
       (S:(A->bool)->bool)`]) THEN
    ASM_SIMP_TAC[HAS_DIRICHLET_DENSITY_COMPLEMENT; SUBSET_DIFF]]);;

let HAS_DIRICHLET_DENSITY_SUBSET = prove
 (`!k:A ring S1 S2 d1 d2.
        number_field k /\
        S2 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        has_dirichlet_density k S1 d1 /\ has_dirichlet_density k S2 d2 /\
        S1 SUBSET S2
        ==> d1 <= d2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `S2:(A->bool)->bool`; `S1:(A->bool)->bool`;
                 `d2:real`; `d1:real`] HAS_DIRICHLET_DENSITY_DIFF_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `S2 DIFF S1:(A->bool)->bool`; `d2 - d1:real`]
    HAS_DIRICHLET_DENSITY_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC]);;

let HAS_DIRICHLET_DENSITY_FINITE_SYMDIFF = prove
 (`!k:A ring S1 S2 d.
        number_field k /\
        S1 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        S2 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        FINITE((S1 DIFF S2) UNION (S2 DIFF S1))
        ==> (has_dirichlet_density k S1 d <=> has_dirichlet_density k S2 d)`,
  SUBGOAL_THEN
   `!k:A ring S1 S2 d.
        number_field k /\
        S1 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        S2 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        FINITE((S1 DIFF S2) UNION (S2 DIFF S1)) /\
        has_dirichlet_density k S1 d
        ==> has_dirichlet_density k S2 d`
  (fun th -> MESON_TAC[th; UNION_COMM]) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `has_dirichlet_density (k:A ring)
     ((S1 DIFF (S1 DIFF S2)) UNION (S2 DIFF S1)) ((d - &0) + &0)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DIRICHLET_DENSITY_DISJOINT_UNION THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC HAS_DIRICHLET_DENSITY_DIFF_SUBSET THEN
      ASM_REWRITE_TAC[SUBSET_DIFF] THEN
      MATCH_MP_TAC HAS_DIRICHLET_DENSITY_FINITE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `(S1 DIFF S2) UNION (S2 DIFF S1):(A->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC HAS_DIRICHLET_DENSITY_FINITE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `(S1 DIFF S2) UNION (S2 DIFF S1):(A->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[]];
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_RID] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM SET_TAC[]]);;
