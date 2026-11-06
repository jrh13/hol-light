(* ========================================================================= *)
(* Absolute values, and the P-adic absolute values of a Dedekind valuation.  *)
(* absolute_value k f says that f : A->real is nonnegative, zero exactly at  *)
(* 0, multiplicative and subadditive on the ring k;                          *)
(* nonarchimedean_absolute_value k f adds the ultrametric inequality f(x +   *)
(* y) <= max (f x) (f y), which with nonnegativity implies subadditivity     *)
(* (NONARCHIMEDEAN_ABSOLUTE_VALUE). The basic properties                     *)
(* (ABSOLUTE_VALUE_POS, ABSOLUTE_VALUE_0, ABSOLUTE_VALUE_1,                  *)
(* ABSOLUTE_VALUE_NEG, ABSOLUTE_VALUE_SUB, ABSOLUTE_VALUE_ABS_SUB_LE: abs(f  *)
(* x - f y) <= f(x - y), ABSOLUTE_VALUE_POW, ABSOLUTE_VALUE_INV,             *)
(* ABSOLUTE_VALUE_DIV, ABSOLUTE_VALUE_RING_SUM, f(n) <= n:                   *)
(* ABSOLUTE_VALUE_RING_OF_NUM_LE) and nontriviality                          *)
(* (ABSOLUTE_VALUE_NONTRIVIAL: on a field, f is nontrivial iff f x > 1 for   *)
(* some x iff f x < 1 for some nonzero x). For a Dedekind domain r with      *)
(* fraction field k along h (field_of_fractions (r,k) h), a nonzero prime P  *)
(* of r and a real c > 1, the function                                       *)
(*                                                                           *)
(*   f x = if x = ring_0 k then &0                                           *)
(*         else c zpow --(dedekind_valuation (r,k) h P x)                    *)
(*                                                                           *)
(* is a nonarchimedean absolute value on k with unit ball the valuation ring *)
(* {x | x = 0 \/ &0 <= v_P(x)} (DEDEKIND_VALUATION_ABSOLUTE_VALUE). When r/P *)
(* is finite, the normalized choice c = ideal_norm r P (= |r/P| > 1,         *)
(* IDEAL_NORM_GT_1 of ANT/ideal_norm.ml) gives |h a|_P N(P^v_P(a)) = 1 for   *)
(* nonzero a in r (DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE), and when   *)
(* r/(a) is finite the product of N(P) zpow v_P(a) over the finitely many P  *)
(* with v_P(a) nonzero is N((a)) (DEDEKIND_VALUATION_IDEAL_NORM), so the     *)
(* product of the normalized |h a|_P is 1 / N((a)). The integer powers zpow  *)
(* of core int.ml are monotone in the exponent for bases >= 1                *)
(* (REAL_ZPOW_MONO, REAL_ZPOW_MONO_LT).                                      *)
(*                                                                           *)
(* Nonarchimedean absolute values: f(n) <= 1 for the integers n              *)
(* (NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM,                               *)
(* NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT), and conversely, on any ring,  *)
(* f is nonarchimedean iff f(n) <= 1 for all integers n iff f is bounded on  *)
(* the integers (NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED), so every absolute   *)
(* value is nonarchimedean in positive characteristic                        *)
(* (NONARCHIMEDEAN_ABSOLUTE_VALUE_CHAR) and trivial on a finite integral     *)
(* domain (ABSOLUTE_VALUE_FINITE); on a field the unit ball {x | f x <= 1}   *)
(* of a nonarchimedean f is a valuation subring with maximal ideal {x | f x  *)
(* < 1} (NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING) and contains the   *)
(* elements integral over a subring on which f <= 1                          *)
(* (NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL). The real helper: a power t^n    *)
(* with t > 1 exceeds a n + b for all large n                                *)
(* (REAL_POW_EVENTUALLY_GT_LINEAR).                                          *)
(*                                                                           *)
(* Routes: the nonarchimedean criterion by the binomial expansion            *)
(* (RING_BINOMIAL_THEOREM), f(x + y)^m <= (m + 1) c max(f x, f y)^m, against *)
(* REAL_POW_EVENTUALLY_GT_LINEAR; the unit ball is integrally closed         *)
(* (VALUATION_SUBRING_INTEGRAL_ELEMENT of ANT/valuation_ring.ml). The P-adic *)
(* absolute values: the homomorphism and ultrametric properties of v_P       *)
(* (DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_ADD) and REAL_ZPOW_ADD; the   *)
(* unit ball by monotonicity; the norm from IDEAL_NORM_FACTORIZATION of      *)
(* ANT/ideal_norm.ml, the primes containing (a) being those with v_P(a) > 0  *)
(* (DEDEKIND_VALUATION_PRIME_IDEAL, DEDEKIND_VALUATION_IMAGE).               *)
(*                                                                           *)
(* Uses: Library/products.ml (product), ANT/dedekind.ml,                     *)
(* ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, ANT/integral.ml and         *)
(* ANT/valuation_ring.ml (valuation subrings).                               *)
(* ========================================================================= *)

needs "Library/products.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_valuation.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/integral.ml";;
needs "ANT/valuation_ring.ml";;

(* ------------------------------------------------------------------------- *)
(* Absolute values: real functions on a ring that are nonnegative, zero      *)
(* exactly at 0, multiplicative and subadditive; the nonarchimedean ones are *)
(* ultrametric, which with nonnegativity gives subadditivity                 *)
(* (NONARCHIMEDEAN_ABSOLUTE_VALUE).                                          *)
(* ------------------------------------------------------------------------- *)

let absolute_value = new_definition
 `absolute_value (k:A ring) (f:A->real) <=>
        (!x. x IN ring_carrier k
             ==> &0 <= f x /\ (f x = &0 <=> x = ring_0 k)) /\
        (!x y. x IN ring_carrier k /\ y IN ring_carrier k
               ==> f(ring_mul k x y) = f x * f y) /\
        (!x y. x IN ring_carrier k /\ y IN ring_carrier k
               ==> f(ring_add k x y) <= f x + f y)`;;

let nonarchimedean_absolute_value = new_definition
 `nonarchimedean_absolute_value (k:A ring) (f:A->real) <=>
        absolute_value k f /\
        !x y. x IN ring_carrier k /\ y IN ring_carrier k
              ==> f(ring_add k x y) <= max (f x) (f y)`;;

let NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE = prove
 (`!k (f:A->real). nonarchimedean_absolute_value k f ==> absolute_value k f`,
  SIMP_TAC[nonarchimedean_absolute_value]);;

let NONARCHIMEDEAN_ABSOLUTE_VALUE = prove
 (`!k (f:A->real).
        nonarchimedean_absolute_value k f <=>
        (!x. x IN ring_carrier k
             ==> &0 <= f x /\ (f x = &0 <=> x = ring_0 k)) /\
        (!x y. x IN ring_carrier k /\ y IN ring_carrier k
               ==> f(ring_mul k x y) = f x * f y) /\
        (!x y. x IN ring_carrier k /\ y IN ring_carrier k
               ==> f(ring_add k x y) <= max (f x) (f y))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nonarchimedean_absolute_value; absolute_value] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= (a:real) /\ &0 <= (b:real) /\ (c:real) <= max a b
    ==> c <= a + b`) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties of absolute values.                                      *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTE_VALUE_POS = prove
 (`!k (f:A->real) x.
        absolute_value k f /\ x IN ring_carrier k ==> &0 <= f x`,
  SIMP_TAC[absolute_value]);;

let ABSOLUTE_VALUE_EQ_0 = prove
 (`!k (f:A->real) x.
        absolute_value k f /\ x IN ring_carrier k
        ==> (f x = &0 <=> x = ring_0 k)`,
  SIMP_TAC[absolute_value]);;

let ABSOLUTE_VALUE_POS_LT = prove
 (`!k (f:A->real) x.
        absolute_value k f /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> &0 < f x`,
  MESON_TAC[ABSOLUTE_VALUE_POS; ABSOLUTE_VALUE_EQ_0; REAL_LT_LE]);;

let ABSOLUTE_VALUE_0 = prove
 (`!k (f:A->real). absolute_value k f ==> f(ring_0 k) = &0`,
  MESON_TAC[absolute_value; RING_0]);;

let ABSOLUTE_VALUE_MUL = prove
 (`!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_mul k x y) = f x * f y`,
  SIMP_TAC[absolute_value]);;

let ABSOLUTE_VALUE_TRIANGLE = prove
 (`!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_add k x y) <= f x + f y`,
  SIMP_TAC[absolute_value]);;

let ABSOLUTE_VALUE_1 = prove
 (`!k (f:A->real).
        absolute_value k f /\ ~(ring_1 k = ring_0 k) ==> f(ring_1 k) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `ring_1 k:A`; `ring_1 k:A`]
    ABSOLUTE_VALUE_MUL) THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `ring_1 k:A`]
    ABSOLUTE_VALUE_POS_LT) THEN
  ASM_SIMP_TAC[RING_1; RING_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `(a:real) = a * a <=> a * (a - &1) = &0`;
              REAL_ENTIRE] THEN
  REAL_ARITH_TAC);;

let ABSOLUTE_VALUE_NEG = prove
 (`!k (f:A->real) x.
        absolute_value k f /\ x IN ring_carrier k
        ==> f(ring_neg k x) = f x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `ring_1 k:A = ring_0 k` THENL
   [SUBGOAL_THEN `!y:A. y IN ring_carrier k ==> y = ring_0 k`
     (fun th -> ASM_SIMP_TAC[th; RING_NEG]) THEN
    ASM_MESON_TAC[RING_MUL_LID; RING_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_neg k x:A = ring_mul k (ring_neg k (ring_1 k)) x`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_LNEG; RING_1; RING_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_MUL; RING_NEG; RING_1] THEN
  MATCH_MP_TAC(REAL_RING `(a:real) = &1 ==> a * x = x`) THEN
  SUBGOAL_THEN
   `f(ring_neg k (ring_1 k):A) * f(ring_neg k (ring_1 k)) = (&1:real)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `ring_neg k (ring_1 k):A`;
                   `ring_neg k (ring_1 k):A`] ABSOLUTE_VALUE_MUL) THEN
    ASM_SIMP_TAC[RING_NEG; RING_1; RING_MUL_LNEG; RING_MUL_RNEG;
                 RING_NEG_NEG; RING_MUL_LID; ABSOLUTE_VALUE_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `ring_neg k (ring_1 k):A`]
    ABSOLUTE_VALUE_POS) THEN
  ASM_SIMP_TAC[RING_NEG; RING_1] THEN
  SPEC_TAC(`f(ring_neg k (ring_1 k):A):real`,`a:real`) THEN
  REWRITE_TAC[REAL_ARITH `(a:real) * a = &1 <=> (a - &1) * (a + &1) = &0`;
              REAL_ENTIRE] THEN
  REAL_ARITH_TAC);;

let ABSOLUTE_VALUE_SUB = prove
 (`!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_sub k x y) = f(ring_sub k y x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `ring_sub k x y:A`]
    ABSOLUTE_VALUE_NEG) THEN
  ASM_SIMP_TAC[RING_SUB; RING_NEG_SUB]);;

let ABSOLUTE_VALUE_SUB_LE = prove
 (`!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_sub k x y) <= f x + f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sub] THEN
  ASM_MESON_TAC[ABSOLUTE_VALUE_TRIANGLE; ABSOLUTE_VALUE_NEG; RING_NEG]);;

let ABSOLUTE_VALUE_ABS_SUB_LE = prove
 (`!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> abs(f x - f y) <= f(ring_sub k x y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `ring_sub k x y:A`; `y:A`]
    ABSOLUTE_VALUE_TRIANGLE) THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `ring_sub k y x:A`; `x:A`]
    ABSOLUTE_VALUE_TRIANGLE) THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `x:A`; `y:A`]
    ABSOLUTE_VALUE_SUB) THEN
  ASM_SIMP_TAC[RING_SUB] THEN
  ASM_SIMP_TAC[RING_RULE
   `ring_add k (ring_sub k x y) y = (x:A) /\
    ring_add k (ring_sub k y x) x = (y:A)`] THEN
  REAL_ARITH_TAC);;

let ABSOLUTE_VALUE_POW = prove
 (`!k (f:A->real) x n.
        absolute_value k f /\ ~(ring_1 k = ring_0 k) /\ x IN ring_carrier k
        ==> f(ring_pow k x n) = f x pow n`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; real_pow; ABSOLUTE_VALUE_1; ABSOLUTE_VALUE_MUL;
               RING_POW]);;

let ABSOLUTE_VALUE_INV = prove
 (`!k (f:A->real) x.
        field k /\ absolute_value k f /\ x IN ring_carrier k
        ==> f(ring_inv k x) = inv(f x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:A = ring_0 k` THEN
  ASM_SIMP_TAC[RING_INV_0; ABSOLUTE_VALUE_0; REAL_INV_0] THEN
  MATCH_MP_TAC(REAL_FIELD `x * y = &1 ==> y = inv x`) THEN
  ASM_SIMP_TAC[GSYM ABSOLUTE_VALUE_MUL; RING_INV; FIELD_MUL_RINV] THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_1; FIELD_NONTRIVIAL]);;

let ABSOLUTE_VALUE_DIV = prove
 (`!k (f:A->real) x y.
        field k /\ absolute_value k f /\
        x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_div k x y) = f x / f y`,
  SIMP_TAC[ring_div; real_div; ABSOLUTE_VALUE_MUL; ABSOLUTE_VALUE_INV;
           RING_INV]);;

let ABSOLUTE_VALUE_RING_SUM = prove
 (`!k (f:A->real) (g:K->A) s.
        absolute_value k f /\ FINITE s /\
        (!i. i IN s ==> g i IN ring_carrier k)
        ==> f(ring_sum k s g) <= sum s (\i. f(g i))`,
  REPLICATE_TAC 3 GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; SUM_CLAUSES; FORALL_IN_INSERT] THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_0; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `(f:A->real)((g:K->A) x) + f(ring_sum k s g)` THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_TRIANGLE; RING_SUM; REAL_LE_LADD]);;

let ABSOLUTE_VALUE_RING_OF_NUM_LE = prove
 (`!k (f:A->real) n.
        absolute_value k f ==> f(ring_of_num k n) <= &n`,
  REPLICATE_TAC 2 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_of_num; ABSOLUTE_VALUE_0; REAL_LE_REFL] THEN
  TRANS_TAC REAL_LE_TRANS `(f:A->real)(ring_of_num k n) + f(ring_1 k)` THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_TRIANGLE; RING_OF_NUM; RING_1] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ring_1 k:A = ring_0 k` THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_0; ABSOLUTE_VALUE_1; REAL_POS; REAL_LE_REFL]);;

let ABSOLUTE_VALUE_EQ = prove
 (`!k (f:A->real) g.
        (!x. x IN ring_carrier k ==> f x = g x)
        ==> (absolute_value k f <=> absolute_value k g) /\
            (nonarchimedean_absolute_value k f <=>
             nonarchimedean_absolute_value k g)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NONARCHIMEDEAN_ABSOLUTE_VALUE; absolute_value; RING_ADD;
               RING_MUL]);;

let ABSOLUTE_VALUE_NONTRIVIAL = prove
 (`!k (f:A->real).
        field k /\ absolute_value k f
        ==> ((?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1)) <=>
             (?x. x IN ring_carrier k /\ &1 < f x)) /\
            ((?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1)) <=>
             (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ f x < &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> q /\ r) /\ (q ==> p) /\ (r ==> p)
                     ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(&0:real) < f(x:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `~(ring_inv k x:A = ring_0 k) /\ ring_inv k x IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_INV; FIELD_MUL_RINV; RING_MUL_RZERO;
                    FIELD_NONTRIVIAL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `f:A->real`; `x:A`] ABSOLUTE_VALUE_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH
      `f(x:A) < (&1:real) \/ &1 < f x \/ f x = &1`) THENL
     [CONJ_TAC THENL [EXISTS_TAC `ring_inv k x:A`; EXISTS_TAC `x:A`] THEN
      ASM_SIMP_TAC[REAL_INV_LT_1] THEN ASM_SIMP_TAC[REAL_INV_1_LT];
      FIRST_X_ASSUM DISJ_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      CONJ_TAC THENL [EXISTS_TAC `x:A`; EXISTS_TAC `ring_inv k x:A`] THEN
      ASM_SIMP_TAC[REAL_INV_LT_1]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(&1:real) < f(x:A)` THEN
      ASM_SIMP_TAC[ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Nonarchimedean absolute values: bounded on the integers, their unit balls *)
(* are valuation subrings containing the integral elements.                  *)
(* ------------------------------------------------------------------------- *)

let NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM = prove
 (`!k (f:A->real) n.
        nonarchimedean_absolute_value k f ==> f(ring_of_num k n) <= &1`,
  REPLICATE_TAC 2 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE) THEN
  SUBGOAL_THEN `(f:A->real)(ring_1 k) <= &1` ASSUME_TAC THENL
   [ASM_CASES_TAC `ring_1 k:A = ring_0 k` THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0; ABSOLUTE_VALUE_1; REAL_POS; REAL_LE_REFL];
    ALL_TAC] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_of_num; ABSOLUTE_VALUE_0; REAL_POS] THEN
  TRANS_TAC REAL_LE_TRANS
   `max ((f:A->real)(ring_of_num k n)) (f(ring_1 k))` THEN
  ASM_REWRITE_TAC[REAL_MAX_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
    GEN_REWRITE_RULE I [nonarchimedean_absolute_value]) THEN
  REWRITE_TAC[RING_OF_NUM; RING_1]);;

let NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT = prove
 (`!k (f:A->real) n.
        nonarchimedean_absolute_value k f ==> f(ring_of_int k n) <= &1`,
  REPLICATE_TAC 2 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE) THEN
  REWRITE_TAC[FORALL_INT_CASES; RING_OF_INT_CASES] THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_NEG; RING_OF_NUM;
               NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM]);;

let REAL_POW_EVENTUALLY_GT_LINEAR = prove
 (`!(t:real) a b. &1 < t ==> ?N. !n. N <= n ==> a * &n + b < t pow n`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e = sqrt t - &1` THEN
  SUBGOAL_THEN `&0 < (e:real)` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[REAL_SUB_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM SQRT_1] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `(e:real) pow 2` REAL_ARCH) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num` o SPEC `abs (a:real) + abs b + &1`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs (a:real) + abs b + &1 < &n * e pow 2` ASSUME_TAC THENL
   [TRANS_TAC REAL_LTE_TRANS `&N * (e:real) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1:real) <= &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `abs (a:real) + abs b + &1 < &n * e pow 2` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &n * (e:real)) pow 2 <= t pow n` ASSUME_TAC THENL
   [SUBGOAL_THEN `t pow n = (sqrt t pow n) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      REWRITE_TAC[GSYM REAL_POW_POW] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_ARITH `&1 < (t:real) ==> &0 <= t`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= (x:real) ==> &0 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE];
      SUBGOAL_THEN `sqrt t = &1 + e` SUBST1_TAC THENL
       [EXPAND_TAC "e" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LBOUND THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `(x:real) <= y ==> z < x ==> z < y`)) THEN
  SUBGOAL_THEN `&n * (abs (a:real) + abs b + &1) < &n * (&n * e pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &n * (e:real)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs (b:real) <= &n * abs b` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_ABS_POS)) [`a:real`; `b:real`] THEN
  MP_TAC(REAL_ARITH `(a:real) <= abs a /\ (b:real) <= abs b`) THEN
  SUBGOAL_THEN `(a:real) * &n <= abs a * &n` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED = prove
 (`!k (f:A->real).
        absolute_value k f
        ==> (nonarchimedean_absolute_value k f <=>
             !n. f(ring_of_int k n) <= &1) /\
            (nonarchimedean_absolute_value k f <=>
             ?c. !n. f(ring_of_int k n) <= c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ (q ==> r) /\ (r ==> p)
                     ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT];
    MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `c:real` (LABEL_TAC "c"))] THEN
  ASM_REWRITE_TAC[nonarchimedean_absolute_value] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `ring_1 k:A = ring_0 k` THENL
   [SUBGOAL_THEN `!z:A. z IN ring_carrier k ==> z = ring_0 k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_MUL_LID; RING_MUL_LZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_add k x y:A = ring_0 k /\ x = ring_0 k`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_SIMP_TAC[RING_ADD]; ALL_TAC] THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0; REAL_LE_MAX; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. (f:A->real)(ring_of_num k j) <= c` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM RING_OF_INT_OF_NUM] THEN
    USE_THEN "c" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c:real)` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(f:A->real)(ring_of_num k 0)` THEN
    ASM_REWRITE_TAC[ring_of_num] THEN
    ASM_SIMP_TAC[ABSOLUTE_VALUE_0; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `M = max ((f:A->real) x) (f y)` THEN
  SUBGOAL_THEN `&0 <= (f:A->real) x /\ &0 <= f y /\ f x <= M /\ f y <= M`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
    ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. (f:A->real)(ring_add k x y) pow m <= (c * &m + c) * M pow m`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN
    SUBGOAL_THEN
     `(f:A->real)(ring_add k x y) pow m = f(ring_pow k (ring_add k x y) m)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTE_VALUE_POW; RING_ADD]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_BINOMIAL_THEOREM] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum(0..m) (\i. (f:A->real)
        (ring_mul k (ring_of_num k (binom(m,i)))
          (ring_mul k (ring_pow k x i) (ring_pow k y (m - i)))))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`k:A ring`; `f:A->real`;
        `\i. ring_mul k (ring_of_num k (binom(m,i)))
                (ring_mul k (ring_pow k x i) (ring_pow k (y:A) (m - i)))`;
        `0..m`] ABSOLUTE_VALUE_RING_SUM) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; RING_MUL; RING_POW; RING_OF_NUM] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `sum(0..m) (\i. c * M pow m)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[ABSOLUTE_VALUE_MUL; ABSOLUTE_VALUE_POW; RING_MUL; RING_POW;
                   RING_OF_NUM] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE] THEN
      SUBGOAL_THEN `(M:real) pow m = M pow i * M pow (m - i)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[ABSOLUTE_VALUE_POS; RING_OF_NUM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_LE2];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM REAL_OF_NUM_ADD] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(M:real) = &0` THENL
   [SUBGOAL_THEN `x:A = ring_0 k /\ y = ring_0 k` (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [ASM_MESON_TAC[ABSOLUTE_VALUE_EQ_0; REAL_LE_ANTISYM]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_ADD_LZERO; RING_0; ABSOLUTE_VALUE_0; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (M:real)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:A->real)(ring_add k x y) / M`; `c:real`; `c:real`]
    REAL_POW_EVENTUALLY_GT_LINEAR) THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL; REAL_NOT_LT; REAL_POW_DIV] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT]);;

let NONARCHIMEDEAN_ABSOLUTE_VALUE_CHAR = prove
 (`!k (f:A->real).
        absolute_value k f /\ ~(ring_char k = 0)
        ==> nonarchimedean_absolute_value k f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`]
    NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  EXISTS_TAC `&(ring_char(k:A ring)):real` THEN X_GEN_TAC `n:int` THEN
  ONCE_REWRITE_TAC[GSYM RING_OF_INT_REM] THEN
  MP_TAC(ISPECL [`n:int`; `&(ring_char(k:A ring)):int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_ABS_NUM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `&(num_of_int(n rem &(ring_char(k:A ring)))) = n rem &(ring_char k)`
  (SUBST1_TAC o SYM) THENL [ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC] THEN
  REWRITE_TAC[RING_OF_INT_OF_NUM] THEN
  TRANS_TAC REAL_LE_TRANS
   `&(num_of_int(n rem &(ring_char(k:A ring)))):real` THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_RING_OF_NUM_LE; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;

let ABSOLUTE_VALUE_FINITE = prove
 (`!k (f:A->real) x.
        integral_domain k /\ FINITE(ring_carrier k) /\ absolute_value k f /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> f x = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(ring_1 k:A = ring_0 k)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_DOMAIN_NONTRIVIAL]; ALL_TAC] THEN
  ABBREV_TAC `N = CARD(ring_carrier k:A->bool)` THEN
  SUBGOAL_THEN `2 <= N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN
    TRANS_TAC LE_TRANS `CARD {ring_0 k:A,ring_1 k}` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                   NOT_IN_EMPTY] THEN
      ARITH_TAC;
      MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; RING_0; RING_1]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] FINITE_INTEGRAL_DOMAIN_POW_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `f:A->real`) THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_POW] THEN
  SUBGOAL_THEN `&0 < (f:A->real) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `N = SUC(N - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[real_pow]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(f:A->real) x pow (N - 1) = &1` MP_TAC THENL
   [UNDISCH_TAC `(f:A->real) x * f x pow (N - 1) = f x` THEN
    UNDISCH_TAC `&0 < (f:A->real) x` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:A->real) x`; `N - 1`] REAL_POW_EQ_1_IMP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING = prove
 (`!k (f:A->real).
        field k /\ nonarchimedean_absolute_value k f
        ==> valuation_subring k {x | x IN ring_carrier k /\ f x <= &1} /\
            maximal_ideal
             (subring_generated k {x | x IN ring_carrier k /\ f x <= &1})
             {x | x IN ring_carrier k /\ f x < &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[valuation_subring; subring_of] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL; RING_INV;
                 ABSOLUTE_VALUE_0; ABSOLUTE_VALUE_1; FIELD_NONTRIVIAL;
                 ABSOLUTE_VALUE_NEG; ABSOLUTE_VALUE_MUL; ABSOLUTE_VALUE_INV;
                 REAL_POS; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      TRANS_TAC REAL_LE_TRANS `max ((f:A->real) x) (f y)` THEN
      ASM_REWRITE_TAC[REAL_MAX_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [nonarchimedean_absolute_value]) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_MESON_TAC[ABSOLUTE_VALUE_POS];
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      DISJ_CASES_TAC(REAL_ARITH `(f:A->real) x <= &1 \/ &1 < f x`) THEN
      ASM_SIMP_TAC[REAL_INV_LT_1; REAL_LT_IMP_LE]];
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP VALUATION_SUBRING_MAXIMAL_IDEAL
    th]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x:A = ring_0 k` THEN
  ASM_SIMP_TAC[ABSOLUTE_VALUE_0; REAL_LT_01; REAL_POS] THEN
  ASM_SIMP_TAC[RING_INV; ABSOLUTE_VALUE_INV] THEN
  SUBGOAL_THEN `&0 < (f:A->real) x` MP_TAC THENL
   [ASM_MESON_TAC[ABSOLUTE_VALUE_POS_LT]; ALL_TAC] THEN
  SPEC_TAC(`(f:A->real) x`,`t:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  EQ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_NOT_LE; REAL_INV_1_LT];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `&1 < inv t` THEN ASM_REWRITE_TAC[REAL_INV_1] THEN
  REAL_ARITH_TAC);;

let NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL = prove
 (`!r k (h:B->A) (f:A->real) x.
        field k /\ nonarchimedean_absolute_value k f /\
        ring_homomorphism(r,k) h /\
        (!a. a IN ring_carrier r ==> f(h a) <= &1) /\
        integral_element (r,k) h x
        ==> f x <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->real`]
    NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(x:A) IN {x | x IN ring_carrier k /\ f x <= (&1:real)}`
  MP_TAC THENL
   [ALL_TAC; SIMP_TAC[IN_ELIM_THM]] THEN
  MATCH_MP_TAC VALUATION_SUBRING_INTEGRAL_ELEMENT THEN
  EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL [`r:B ring`; `k:A ring`; `h:B->A`]
    INTEGRAL_ELEMENT_OVER_SUBRING) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
   REWRITE_TAC[MATCH_MP CARRIER_SUBRING_GENERATED_SUBRING
    (CONJUNCT1(CONJUNCT2(GEN_REWRITE_RULE I [valuation_subring] th)))]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[ring_homomorphism; SUBSET; IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* The P-adic absolute values of a Dedekind valuation.                       *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_VALUATION_ABSOLUTE_VALUE = prove
 (`!r k (h:A->B) P c (f:B->real).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\ &1 < c /\
        (!x. f x = if x = ring_0 k then &0
                   else c zpow --(dedekind_valuation (r,k) h P x))
        ==> nonarchimedean_absolute_value k f /\
            (!x. x IN ring_carrier k
                 ==> (f x <= &1 <=>
                      x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x))`,
  REWRITE_TAC[NONARCHIMEDEAN_ABSOLUTE_VALUE; GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < c /\ ~(c = &0) /\ &1 <= (c:real)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_ZPOW_LE; REAL_LT_IMP_LE; REAL_ZPOW_EQ_0];
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:B = ring_0 k` THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; REAL_MUL_LZERO] THEN
    ASM_CASES_TAC `y:B = ring_0 k` THEN
    ASM_SIMP_TAC[RING_MUL_RZERO; REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                   `x:B`; `y:B`] DEDEKIND_VALUATION_MUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[INT_NEG_ADD; REAL_ZPOW_ADD];
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:B = ring_0 k` THENL
     [ASM_SIMP_TAC[RING_ADD_LZERO] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_MAX; REAL_LE_REFL];
      ALL_TAC] THEN
    ASM_CASES_TAC `y:B = ring_0 k` THENL
     [ASM_SIMP_TAC[RING_ADD_RZERO; REAL_LE_MAX; REAL_LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MAX; REAL_ZPOW_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                   `x:B`; `y:B`] DEDEKIND_VALUATION_ADD) THEN
    ASM_REWRITE_TAC[INT_MIN_LE; REAL_LE_MAX] THEN
    MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_ZPOW_MONO THEN ASM_REWRITE_TAC[INT_LE_NEG2];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:B = ring_0 k` THEN ASM_REWRITE_TAC[REAL_POS] THEN
    EQ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[INT_NOT_LE; REAL_NOT_LE] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:real`; `&0:int`;
                     `--(dedekind_valuation (r,k) (h:A->B) P x)`]
        REAL_ZPOW_MONO_LT) THEN
      ASM_REWRITE_TAC[REAL_ZPOW_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_INT_ARITH_TAC;
      DISCH_TAC THEN
      MP_TAC(ISPECL [`c:real`; `--(dedekind_valuation (r,k) (h:A->B) P x)`;
                     `&0:int`] REAL_ZPOW_MONO) THEN
      ASM_REWRITE_TAC[REAL_ZPOW_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_INT_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The normalized absolute value and the ideal norm.                         *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_VALUATION_IDEAL_NORM = prove
 (`!r k (h:A->B) a.
        dedekind_domain r /\ ring_monomorphism(r,k) h /\
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        FINITE(ring_carrier(quotient_ring r (ideal_generated r {a})))
        ==> FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        ~(dedekind_valuation (r,k) h P (h a) = &0)} /\
            product {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                         ~(dedekind_valuation (r,k) h P (h a) = &0)}
                    (\P. &(ideal_norm r P) zpow
                         dedekind_valuation (r,k) h P (h a)) =
            &(ideal_norm r (ideal_generated r {a}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
         ~(dedekind_valuation (r,k) (h:A->B) P (h a) = &0)} =
    {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
         ideal_generated r {a} SUBSET P}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `P:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `prime_ideal r (P:A->bool)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `P = {ring_0 r:A}` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ideal_generated r {a} SUBSET P <=> (a:A) IN P`
    SUBST1_TAC THENL
     [EQ_TAC THEN DISCH_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
        ASM_REWRITE_TAC[IN_SING];
        MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
        ASM_SIMP_TAC[SING_SUBSET; PRIME_IMP_RING_IDEAL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `a:A`]
      DEDEKIND_VALUATION_PRIME_IDEAL) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `a:A`]
      DEDEKIND_VALUATION_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_generated r {a:A}`]
    DEDEKIND_IDEAL_FACTORIZATION) THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_generated r {a:A}`]
    IDEAL_NORM_FACTORIZATION) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `P:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `a:A`]
    DEDEKIND_VALUATION_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ZPOW_NUM; REAL_OF_NUM_POW]);;

let DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE = prove
 (`!r k (h:A->B) P (f:B->real).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r P)) /\
        (!x. f x = if x = ring_0 k then &0
                   else &(ideal_norm r P) zpow
                        --(dedekind_valuation (r,k) h P x))
        ==> 1 < ideal_norm r P /\
            nonarchimedean_absolute_value k f /\
            (!x. x IN ring_carrier k
                 ==> (f x <= &1 <=>
                      x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x)) /\
            (!a. a IN ring_carrier r /\ ~(a = ring_0 r)
                 ==> f(h a) *
                     &(ideal_norm r
                        (ideal_pow r P
                          (ideal_valuation r P (ideal_generated r {a})))) =
                     &1)`,
  REWRITE_TAC[NONARCHIMEDEAN_ABSOLUTE_VALUE; GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  SUBGOAL_THEN `1 < ideal_norm r (P:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_PROPER_IDEAL) THEN
    SIMP_TAC[PROPER_IDEAL_ALT];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(p /\ q /\ r /\ s) /\ t ==> p /\ q /\ r /\ s /\ t`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[NONARCHIMEDEAN_ABSOLUTE_VALUE; GSYM CONJ_ASSOC]
      DEDEKIND_VALUATION_ABSOLUTE_VALUE) THEN
    EXISTS_TAC `&(ideal_norm r (P:A->bool)):real` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT];
    X_GEN_TAC `a:A` THEN STRIP_TAC] THEN
  SUBGOAL_THEN `~((h:A->B) a = ring_0 k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `a:A`]
    DEDEKIND_VALUATION_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`;
                 `ideal_valuation r P (ideal_generated r {a:A})`]
    IDEAL_NORM_IDEAL_POW) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_ZPOW_POW; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN
  REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC);;
