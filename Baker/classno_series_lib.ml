(* ========================================================================= *)
(* Series tools: interlacing of unimodal sums, Dirichlet products, right     *)
(* continuity of L-series.                                                   *)
(*                                                                           *)
(* Purpose: three library-style results on real series, used for the limit   *)
(* s -> 1+ in the class number one problem. UNIMODAL_SHIFT, the interlacing  *)
(* lemma: for g >= 0, increasing up to t0 and decreasing after t0, the sums  *)
(* over all integers n of g(al + k n) and g(be + k n) differ by at most      *)
(* 2 g(t0) for any two shifts al, be (UNIMODAL_SHIFT_SHARP: by at most       *)
(* g(t0)). DIRICHLET_SERIES_PRODUCT: for bounded a, b and s > 1 the          *)
(* Dirichlet series of the convolution, the sum over l of (sum over m        *)
(* dividing l of a(m) b(l DIV m)) / l^s, converges to the product of the     *)
(* sums of a(n) / n^s and b(n) / n^s. LSERIES_RIGHT_CONTINUOUS: for a        *)
(* non-principal Dirichlet character c, the sum of Re(c n) / n^s tends to    *)
(* Re(L(1,c)) as s tends to 1 from the right (Abel summation gives a block   *)
(* bound uniform in s >= 1).                                                 *)
(*                                                                           *)
(* Note: the helper lemmas are parsed with real arithmetic as the default;   *)
(* the three main results after prioritize_num, as in the other files of     *)
(* this directory.                                                           *)
(*                                                                           *)
(* Main results: UNIMODAL_SHIFT, UNIMODAL_SHIFT_SHARP, UNIMODAL_SHIFT_LE,    *)
(* DIRICHLET_SERIES_PRODUCT, LSERIES_RIGHT_CONTINUOUS; helper names          *)
(* UNIMODAL_*, DIRICHLET_SERIES_*, LSERIES_*.                                *)
(*                                                                           *)
(* Uses: 100/dirichlet.ml (dirichlet_character, chi_0, Lfunction,            *)
(* BOUNDED_LFUNCTION_PARTIAL_SUMS), Library/pocklington.ml                   *)
(* (ITERATE_ITERATE_DIVISORS), Multivariate/canal.ml                         *)
(* (SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT), Multivariate/realanalysis.ml    *)
(* (REALLIM_RPOW and the real limits).                                       *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;
needs "100/dirichlet.ml";;

prioritize_real();;
prioritize_num();;

(* The helper lemmas are parsed with real arithmetic as the default (the     *)
(* overloading defaults left by dirichlet.ml differ between bases); the      *)
(* three main results are parsed after prioritize_num, the project           *)
(* default.                                                                  *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Generic facts about real series.                                          *)
(* ------------------------------------------------------------------------- *)

let UNIMODAL_INFSUM_LE = prove
 (`!f:num->real k c.
        real_summable (from k) f /\ (!n. sum(k..n) f <= c)
        ==> real_infsum (from k) f <= c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\n. sum(k..n) (f:num->real)` THEN
  ASM_REWRITE_TAC[GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM;
                  TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The interlacing lemma for unimodal functions.                             *)
(* A sum over all integers j of h(j) is written as the series over n >= 0    *)
(* of h(n) + h(-n-1); its partial sums are sums over finite sets of          *)
(* integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

let UNIMODAL_PARTIAL_SUM = prove
 (`!h:real->real N.
     sum(0..N) (\n. h(&n) + h(--(&n + &1))) =
     sum (IMAGE (\n. &n) (0..N) UNION IMAGE (\n. --(&n + &1)) (0..N)) h`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real` THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `m:num` (MP_TAC o CONJUNCT1))
     (X_CHOOSE_THEN `n:num` (MP_TAC o CONJUNCT1))) THEN
    REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o rand o snd) THEN
  ANTS_TAC THENL [SIMP_TAC[REAL_OF_NUM_EQ]; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o rand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[REAL_EQ_NEG2; REAL_EQ_ADD_RCANCEL; REAL_OF_NUM_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF; SUM_ADD_NUMSEG]);;

let UNIMODAL_PARTIAL_SUM_INTEGER = prove
 (`!N j. j IN IMAGE (\n. &n) (0..N) UNION IMAGE (\n. --(&n + &1)) (0..N)
         ==> integer j`,
  REWRITE_TAC[IN_UNION; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let UNIMODAL_FINITE_LE = prove
 (`!(g:real->real) (k:real) (x:real) (s:real->bool).
        (!x. &0 <= g x) /\
        real_summable (from 0) (\n. g(x + k * &n) + g(x - k * (&n + &1))) /\
        FINITE s /\ (!j. j IN s ==> integer j)
        ==> sum s (\j. g(x + k * j)) <=
            real_infsum (from 0) (\n. g(x + k * &n) + g(x - k * (&n + &1)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `abs:real->real` o
    MATCH_MP UPPER_BOUND_FINITE_SET_REAL) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  MP_TAC(SPEC `a:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..N) (\n. (g:real->real)(x + k * &n) +
                             g(x - k * (&n + &1)))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\j. (g:real->real)(x + k * j)`; `N:num`]
       UNIMODAL_PARTIAL_SUM) THEN
    REWRITE_TAC[REAL_ARITH `x + k * --(&n + &1) = x - k * (&n + &1)`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `j:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `integer j /\ abs j <= &N` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[INTEGER_CASES] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_NEG; REAL_OF_NUM_LE] THENL
     [DISCH_TAC THEN DISJ1_TAC THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `n = 0` THENL
     [DISCH_TAC THEN DISJ1_TAC THEN EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC[LE_0] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN DISJ2_TAC THEN EXISTS_TAC `n - 1` THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC]];
    MP_TAC(ISPECL [`\n. (g:real->real)(x + k * &n) + g(x - k * (&n + &1))`;
                   `from 0`; `N:num`] REAL_PARTIAL_SUMS_LE_INFSUM) THEN
    ASM_SIMP_TAC[FROM_INTER_NUMSEG; REAL_LE_ADD]]);;

let UNIMODAL_INTEGER_LT = prove
 (`!x y. integer x /\ integer y /\ x < y ==> x + &1 <= y`,
  MESON_TAC[REAL_LT_INTEGERS]);;

let UNIMODAL_REINDEX_INJ = prove
 (`!u v j0 m.
        integer u /\ integer v /\ integer j0 /\ ~(u = j0) /\ ~(v = j0) /\
        (if u < j0 then u + m + &1 else u + m) =
        (if v < j0 then v + m + &1 else v + m)
        ==> u = v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  MP_TAC(SPECL [`u:real`; `j0:real`] REAL_LT_INTEGERS) THEN
  MP_TAC(SPECL [`v:real`; `j0:real`] REAL_LT_INTEGERS) THEN
  MP_TAC(SPECL [`j0:real`; `u:real`] REAL_LT_INTEGERS) THEN
  MP_TAC(SPECL [`j0:real`; `v:real`] REAL_LT_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* The key comparison: with y = x + k m + r (m integer, 0 <= r < k) and q    *)
(* the integer with x + k q < t0 <= x + k (q + 1), the terms g(y + k j)      *)
(* for j < q - m are bounded by g(x + k (j + m + 1)), those for j > q - m    *)
(* by g(x + k (j + m)) (an injective reindexing), and the one exceptional    *)
(* term by g(t0).                                                            *)

let UNIMODAL_SHIFT_LE = prove
 (`!(g:real->real) (t0:real) (k:real) (x:real) (y:real).
     &0 < k /\ (!x. &0 <= g x) /\
     (!x y. x <= y /\ y <= t0 ==> g x <= g y) /\
     (!x y. t0 <= x /\ x <= y ==> g y <= g x) /\
     real_summable (from 0) (\n. g(x + k * &n) + g(x - k * (&n + &1))) /\
     real_summable (from 0) (\n. g(y + k * &n) + g(y - k * (&n + &1)))
     ==> real_infsum (from 0) (\n. g(y + k * &n) + g(y - k * (&n + &1))) <=
         real_infsum (from 0) (\n. g(x + k * &n) + g(x - k * (&n + &1))) +
         g t0`,
  INTRO_TAC "!g t0 k x y; kpos gpos gleft gright sumx sumy" THEN
  SUBGOAL_THEN `!z:real. (g:real->real) z <= g t0` (LABEL_TAC "gmax") THENL
   [X_GEN_TAC `z:real` THEN
    DISJ_CASES_TAC(REAL_ARITH `z <= t0 \/ t0 <= (z:real)`) THENL
     [USE_THEN "gleft" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      USE_THEN "gright" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `m = floor((y - x) / k)` THEN
  ABBREV_TAC `q = --floor((x - t0) / k) - &1` THEN
  SUBGOAL_THEN `integer m /\ integer q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "q"] THEN SIMP_TAC[FLOOR; INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real) + k * m <= y /\ y < x + k * m + k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `(y - x) / k` FLOOR) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real) + k * q < t0 /\ t0 <= x + k * (q + &1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `(x - t0) / k` FLOOR) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
    EXPAND_TAC "q" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC UNIMODAL_INFSUM_LE THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN
  MP_TAC(ISPECL [`\j. (g:real->real)(y + k * j)`; `N:num`]
     UNIMODAL_PARTIAL_SUM) THEN
  REWRITE_TAC[REAL_ARITH `y + k * --(&n + &1) = y - k * (&n + &1)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!G. FINITE G /\ (!j. j IN G ==> integer j)
        ==> sum G (\j. (g:real->real)(y + k * j)) <=
            real_infsum (from 0) (\n. g(x + k * &n) + g(x - k * (&n + &1))) +
            g t0`
   (fun th -> MATCH_MP_TAC th) THENL
   [ALL_TAC;
    SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[UNIMODAL_PARTIAL_SUM_INTEGER]] THEN
  X_GEN_TAC `G:real->bool` THEN INTRO_TAC "gfin gint" THEN
  ABBREV_TAC `j0 = (q:real) - m` THEN
  SUBGOAL_THEN `integer j0` ASSUME_TAC THENL
   [EXPAND_TAC "j0" THEN ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (G DELETE j0) (\j. (g:real->real)(y + k * j)) + g t0` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_DELETE_CASES] THEN COND_CASES_TAC THENL
     [USE_THEN "gmax" (MP_TAC o SPEC `(y:real) + k * j0`) THEN REAL_ARITH_TAC;
      USE_THEN "gpos" (MP_TAC o SPEC `t0:real`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> a + c <= b + c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (G DELETE j0) (\j. (g:real->real)
                (x + k * (if j < j0 then j + m + &1 else j + m)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    X_GEN_TAC `j:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `integer j` ASSUME_TAC THENL
     [USE_THEN "gint" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `(j:real) + &1 <= j0` ASSUME_TAC THENL
       [MATCH_MP_TAC UNIMODAL_INTEGER_LT THEN
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      USE_THEN "gleft" MATCH_MP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `(y:real) < x + k * m + k` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(x:real) + k * q` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
        REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        UNDISCH_TAC `&0 < (k:real)` THEN UNDISCH_TAC `(j:real) + &1 <= j0` THEN
        UNDISCH_TAC `(q:real) - m = j0` THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `(j0:real) + &1 <= j` ASSUME_TAC THENL
       [SUBGOAL_THEN `(j0:real) < j` MP_TAC THENL
         [UNDISCH_TAC `~(j:real = j0)` THEN UNDISCH_TAC `~((j:real) < j0)` THEN
          REAL_ARITH_TAC;
          DISCH_TAC THEN MATCH_MP_TAC UNIMODAL_INTEGER_LT THEN
          REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      USE_THEN "gright" MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(x:real) + k * (q + &1)` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        UNDISCH_TAC `&0 < (k:real)` THEN UNDISCH_TAC `(j0:real) + &1 <= j` THEN
        UNDISCH_TAC `(q:real) - m = j0` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `(x:real) + k * m <= y` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j:real. if j < j0 then j + m + &1 else j + m`;
                 `\i. (g:real->real)(x + k * i)`; `G DELETE (j0:real)`]
     SUM_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
    MATCH_MP_TAC UNIMODAL_REINDEX_INJ THEN
    MAP_EVERY EXISTS_TAC [`j0:real`; `m:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "gint" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC UNIMODAL_FINITE_LE THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_DELETE] THEN
  X_GEN_TAC `j:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `integer j` ASSUME_TAC THENL
   [USE_THEN "gint" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]);;

let UNIMODAL_SHIFT_SHARP = prove
 (`!(g:real->real) t0 k al be.
     &0 < k /\ (!x. &0 <= g x) /\
     (!x y. x <= y /\ y <= t0 ==> g x <= g y) /\
     (!x y. t0 <= x /\ x <= y ==> g y <= g x) /\
     real_summable (from 0) (\n. g(al + k * &n) + g(al - k * (&n + &1))) /\
     real_summable (from 0) (\n. g(be + k * &n) + g(be - k * (&n + &1)))
     ==> abs(real_infsum (from 0)
               (\n. g(al + k * &n) + g(al - k * (&n + &1))) -
             real_infsum (from 0)
               (\n. g(be + k * &n) + g(be - k * (&n + &1))))
         <= g t0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `t0:real`; `k:real`; `al:real`; `be:real`]
    UNIMODAL_SHIFT_LE) THEN
  MP_TAC(ISPECL [`g:real->real`; `t0:real`; `k:real`; `be:real`; `al:real`]
    UNIMODAL_SHIFT_LE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The main result, parsed after prioritize_num.                             *)

prioritize_num();;

let UNIMODAL_SHIFT = prove
 (`!g t0 k al be.
     &0 < k /\ (!x. &0 <= g x) /\
     (!x y. x <= y /\ y <= t0 ==> g x <= g y) /\
     (!x y. t0 <= x /\ x <= y ==> g y <= g x) /\
     (!al. real_summable (from 0) (\n. g(al + k * &n) + g(al - k * (&n + &1))))
     ==> abs(real_infsum (from 0) (\n. g(al + k * &n) + g(al - k * (&n + &1))) -
             real_infsum (from 0) (\n. g(be + k * &n) + g(be - k * (&n + &1))))
         <= &2 * g t0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `t0:real`; `k:real`; `al:real`; `be:real`]
    UNIMODAL_SHIFT_SHARP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (g:real->real) t0` MP_TAC THENL
   [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* The Dirichlet product of two absolutely convergent Dirichlet series.      *)
(* With A_N, B_N, C_N the partial sums of                                    *)
(* sum a(n)/n^s, sum b(n)/n^s and sum (a * b)(l)/l^s: C_N = sum over m <= N  *)
(* of a(m)/m^s B_(N DIV m), so A_N B_N - C_N only contains terms with        *)
(* k m > N, which are bounded by N^-t (k m)^-u (t = (s-1)/2, u = (s+1)/2).   *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_SERIES_SUM_DIVISORS = prove
 (`!f:num->num->real x.
        sum (1..x) (\n. sum {d | d divides n} (f n)) =
        sum (1..x) (\n. sum (1..(x DIV n)) (\k. f (k * n) n))`,
  REWRITE_TAC[sum] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC ITERATE_ITERATE_DIVISORS THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let DIRICHLET_SERIES_PARTIAL_PRODUCT = prove
 (`!a b s N.
     sum(1..N) (\l. sum {m | m divides l} (\m. a m * b (l DIV m)) /
                    &l rpow s) =
     sum(1..N) (\m. a m / &m rpow s *
                    sum(1..(N DIV m)) (\k. b k / &k rpow s))`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum(1..N) (\l. sum {m | m divides l}
                      (\m. ((a:num->real) m * b (l DIV m)) / &l rpow s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC[real_div; SUM_RMUL];
    REWRITE_TAC[DIRICHLET_SERIES_SUM_DIVISORS]] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN SUBGOAL_THEN `(k * m) DIV m = k` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC DIV_MULT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; RPOW_MUL; real_div; REAL_INV_MUL] THEN
  REAL_ARITH_TAC);;

let DIRICHLET_SERIES_PRODUCT_DIFF = prove
 (`!a b s N.
     sum(1..N) (\n. a n / &n rpow s) * sum(1..N) (\n. b n / &n rpow s) -
     sum(1..N) (\l. sum {m | m divides l} (\m. a m * b (l DIV m)) /
                    &l rpow s) =
     sum(1..N) (\m. a m / &m rpow s *
                    sum(N DIV m + 1..N) (\k. b k / &k rpow s))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DIRICHLET_SERIES_PARTIAL_PRODUCT; GSYM SUM_RMUL;
              GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x + y = z ==> z - x = (y:real)`) THEN
  MATCH_MP_TAC SUM_COMBINE_R THEN REWRITE_TAC[DIV_LE] THEN ARITH_TAC);;

let DIRICHLET_SERIES_RPOW_BOUND = prove
 (`!s t u N m k.
        &0 <= t /\ t + u = s /\ 1 <= m /\ 1 <= k /\ 1 <= N /\ N <= m * k
        ==> inv(&m rpow s * &k rpow s) <=
            inv(&N rpow t) * inv(&m rpow u) * inv(&k rpow u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N /\ &0 < &m /\ &0 < &k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_LT_MUL; RPOW_POS_LT] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[RPOW_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&m * &k) rpow t * &m rpow u * &k rpow u` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC RPOW_LE2 THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_MUL; REAL_OF_NUM_LE];
    REWRITE_TAC[RPOW_MUL] THEN REAL_ARITH_TAC]);;

let DIRICHLET_SERIES_SUMMABLE = prove
 (`!a s. &1 < s /\ (?B. !n. abs(a n) <= B)
         ==> real_summable (from 1) (\n. a n / &n rpow s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n. B * inv(&n rpow s)` THEN
  ASM_SIMP_TAC[REAL_SUMMABLE_LMUL; REAL_SUMMABLE_ZETA] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_RPOW; REAL_ABS_NUM; real_div] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS]);;

let DIRICHLET_SERIES_LIM_RPOW = prove
 (`!t. &0 < t ==> ((\n. inv(&n rpow t)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`; `\n. inv(&n)`; `&0`; `t:real`]
    REALLIM_RPOW) THEN
  ASM_SIMP_TAC[REALLIM_1_OVER_N; REAL_LT_IMP_LE; RPOW_ZERO; REAL_LT_IMP_NZ;
               RPOW_INV]);;

let DIRICHLET_SERIES_DOUBLE_SUM = prove
 (`!f:num->real c N.
        sum(1..N) (\m. sum(1..N) (\k. c * f m * f k)) =
        c * sum(1..N) f * sum(1..N) f`,
  REWRITE_TAC[SUM_LMUL; SUM_RMUL; ETA_AX]);;

let DIRICHLET_SERIES_PRODUCT_BOUND = prove
 (`!a b s Ba Bb N.
     &1 < s /\ (!n. abs(a n) <= Ba) /\ (!n. abs(b n) <= Bb) /\ 1 <= N
     ==> abs(sum(1..N) (\n. a n / &n rpow s) *
             sum(1..N) (\n. b n / &n rpow s) -
             sum(1..N) (\l. sum {m | m divides l} (\m. a m * b (l DIV m)) /
                            &l rpow s))
         <= (Ba * Bb * real_infsum (from 1) (\n. inv(&n rpow ((s + &1) / &2)))
             pow 2) * inv(&N rpow ((s - &1) / &2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIRICHLET_SERIES_PRODUCT_DIFF] THEN
  ABBREV_TAC `t = (s - &1) / &2` THEN ABBREV_TAC `u = (s + &1) / &2` THEN
  SUBGOAL_THEN `&0 < t /\ t + u = s /\ &1 < u` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t"; "u"] THEN UNDISCH_TAC `&1 < s` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Z = real_infsum (from 1) (\n. inv(&n rpow u))` THEN
  SUBGOAL_THEN `&0 <= sum(1..N) (\n. inv(&n rpow u)) /\
                sum(1..N) (\n. inv(&n rpow u)) <= Z`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS] THEN
    EXPAND_TAC "Z" THEN
    MP_TAC(ISPECL [`\n. inv(&n rpow u)`; `from 1`; `N:num`]
      REAL_PARTIAL_SUMS_LE_INFSUM) THEN
    REWRITE_TAC[FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_SUMMABLE_ZETA; REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Ba /\ &0 <= Bb` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..N) (\m. sum(1..N) (\k. (Ba * Bb * inv(&N rpow t)) *
                                   inv(&m rpow u) * inv(&k rpow u)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..N) (\m. abs((a:num->real) m / &m rpow s *
                 sum(N DIV m + 1..N) (\k. (b:num->real) k / &k rpow s)))` THEN
    REWRITE_TAC[SUM_ABS_NUMSEG] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(N DIV m + 1..N) (\k. (Ba * Bb * inv(&N rpow t)) *
                                   inv(&m rpow u) * inv(&k rpow u))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(N DIV m + 1..N) (\k. abs((a:num->real) m / &m rpow s *
                                         (b:num->real) k / &k rpow s))` THEN
      REWRITE_TAC[SUM_ABS_NUMSEG] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      BETA_TAC THEN
      SUBGOAL_THEN
       `abs((a:num->real) m / &m rpow s * (b:num->real) k / &k rpow s) =
        (abs(a m) * abs(b k)) * inv(&m rpow s * &k rpow s)`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_INV; REAL_ABS_RPOW;
                    REAL_ABS_NUM; real_div; REAL_INV_MUL] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(Ba * Bb) * (inv(&N rpow t) * inv(&m rpow u) *
                               inv(&k rpow u))` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; REAL_LE_INV_EQ; RPOW_POS_LE;
               REAL_POS] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC DIRICHLET_SERIES_RPOW_BOUND THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LT_IMP_LE THEN
        MP_TAC(SPECL [`m:num`; `N:num`; `k:num`] RDIV_LT_EQ) THEN
        ASM_ARITH_TAC];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS]];
    ALL_TAC] THEN
  REWRITE_TAC[BETA_RULE(ISPECL [`\n. inv(&n rpow u)`;
    `Ba * Bb * inv(&N rpow t)`; `N:num`] DIRICHLET_SERIES_DOUBLE_SUM)] THEN
  ABBREV_TAC `ZN = sum(1..N) (\n. inv(&n rpow u))` THEN
  SUBGOAL_THEN `ZN * ZN <= Z * Z` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Ba * Bb * inv(&N rpow t)) * (ZN * ZN) <=
                (Ba * Bb * inv(&N rpow t)) * (Z * Z)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS];
    REAL_ARITH_TAC]);;

(* The main result, parsed after prioritize_num.                             *)

prioritize_num();;

let DIRICHLET_SERIES_PRODUCT = prove
 (`!a b s. &1 < s /\ (?B. !n. abs(a n) <= B) /\ (?B. !n. abs(b n) <= B)
          ==> ((\l. sum {m | m divides l} (\m. a m * b (l DIV m)) / &l rpow s)
               real_sums
               (real_infsum (from 1) (\n. a n / &n rpow s) *
                real_infsum (from 1) (\n. b n / &n rpow s))) (from 1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `Ba:real`) (X_CHOOSE_TAC `Bb:real`))) THEN
  REWRITE_TAC[REAL_SERIES_FROM] THEN MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC `\N. sum(1..N) (\n. (a:num->real) n / &n rpow s) *
                  sum(1..N) (\n. (b:num->real) n / &n rpow s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC `\N. ((Ba:real) * Bb *
                     real_infsum (from 1) (\n. inv(&n rpow ((s + &1) / &2)))
                     pow 2) * inv(&N rpow ((s - &1) / &2))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
      X_GEN_TAC `N:num` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC DIRICHLET_SERIES_PRODUCT_BOUND THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      MATCH_MP_TAC DIRICHLET_SERIES_LIM_RPOW THEN
      UNDISCH_TAC `&1 < (s:real)` THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REALLIM_MUL THEN
    REWRITE_TAC[GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM] THEN
    CONJ_TAC THEN MATCH_MP_TAC DIRICHLET_SERIES_SUMMABLE THEN
    ASM_MESON_TAC[]]);;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Right continuity at s = 1 of sum chi(n) / n^s for a non-principal         *)
(* character: Abel summation gives the block bound                           *)
(* |sum(m..n) Re(chi k) / k^s| <= B / m for all s >= 1, hence a tail bound   *)
(* B / (N + 1) uniform in s, and the finite partial sums are continuous.     *)
(* ------------------------------------------------------------------------- *)

let LSERIES_ARCH = prove
 (`!C e. &0 < e ==> ?N. 1 <= N /\ !m. N <= m ==> C / &m < e`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `C / e` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0 + 1` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &m /\ &N0 + &1 <= &m` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `C / e < &m` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ]] THEN
  REAL_ARITH_TAC);;

let LSERIES_BLOCK_TAIL = prove
 (`!f:num->real C.
        (!m n. 1 <= m ==> abs(sum(m..n) f) <= C / &m)
        ==> real_summable (from 1) f /\
            !n. abs(real_infsum (from 1) f - sum(1..n) f) <= C / (&n + &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `real_summable (from 1) (f:num->real)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUMMABLE_CAUCHY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`C:real`; `e:real`] LSERIES_ARCH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REWRITE_TAC[GE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `from 1 INTER (m..n) = m..n` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_FROM; IN_NUMSEG] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C / &m` THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `n:num` THEN MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\M. abs(sum(1..M) (f:num->real) - sum(1..n) f)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_ABS THEN MATCH_MP_TAC REALLIM_SUB THEN
    ASM_REWRITE_TAC[REALLIM_CONST; GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM];
    EXISTS_TAC `n + 1` THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`f:num->real`; `1`; `n:num`; `M:num`] SUM_COMBINE_R) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `(x + y) - x = y:real`; REAL_OF_NUM_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let LSERIES_BLOCK_BOUND = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !s m n. &1 <= s /\ 1 <= m
                         ==> abs(sum(m..n) (\n. Re(c n) / &n rpow s))
                             <= B / &m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] BOUNDED_LFUNCTION_PARTIAL_SUMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_PARTIAL_SUMS) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 * (B:real)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `m:num`; `n:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num->complex`; `\k. Cx(inv(&k rpow s))`; `B:real`; `1`]
    SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL; REAL_CX; RE_CX] THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_POS]; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC RPOW_LE2 THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE; LE_ADD] THEN
      UNDISCH_TAC `&1 <= s` THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= x /\ y <= z ==> x <= y ==> a <= (z:real)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(Re(vsum(m..n) (\k. (c:num->complex) k *
                                        Cx(inv(&k rpow s)))))` THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG; RE_MUL_CX; real_div; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_RPOW; REAL_ABS_NUM; real_div;
              GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1:real`; `s:real`; `&m:real`] RPOW_MONO_LE) THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let LSERIES_FINITE_CONTINUOUS = prove
 (`!c:num->complex N.
        (\s. sum(1..N) (\n. Re(c n) / &n rpow s)) real_continuous atreal (&1)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
  MATCH_MP_TAC REAL_CONTINUOUS_INV_ATREAL THEN
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_AT_RPOW_RIGHT; RPOW_EQ_0; REAL_LT_IMP_NZ]);;

(* The main result, parsed after prioritize_num. The hypothesis that c is    *)
(* real is not needed.                                                       *)

prioritize_num();;

let LSERIES_RIGHT_CONTINUOUS = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n))
        ==> ((\s. real_infsum (from 1) (\n. Re(c n) / &n rpow s)) --->
             Re(Lfunction c)) (atreal (&1) within {s | &1 < s})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LSERIES_BLOCK_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "blk"))) THEN
  SUBGOAL_THEN
   `((\n. Re((c:num->complex) n) / &n rpow &1) real_sums Re(Lfunction c))
    (from 1)`
  (LABEL_TAC "one") THENL
   [REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMS_RE) THEN
    REWRITE_TAC[o_DEF; RE_DIV_CX];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`B:real`; `e / &3`] LSERIES_ARCH) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `&0 < (e:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(B:real) / (&N + &1) < e / &3` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &1 <= s
        ==> abs(real_infsum (from 1) (\n. Re((c:num->complex) n) / &n rpow s) -
                sum(1..N) (\n. Re(c n) / &n rpow s)) < e / &3`
  (LABEL_TAC "tail") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\n. Re((c:num->complex) n) / &n rpow s`; `B:real`]
      LSERIES_BLOCK_TAIL) THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`m:num`; `k:num`] THEN DISCH_TAC THEN
      USE_THEN "blk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `N:num` o CONJUNCT2) THEN
      UNDISCH_TAC `(B:real) / (&N + &1) < e / &3` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:num->complex`; `N:num`] LSERIES_FINITE_CONTINUOUS) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `&0 < (e:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "cont"))) THEN
  EXISTS_TAC `dd:real` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "tail" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `&1 < (s:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "tail" (MP_TAC o SPEC `&1:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
  SUBGOAL_THEN
   `real_infsum (from 1) (\n. Re((c:num->complex) n) / &n rpow &1) =
    Re(Lfunction c)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN USE_THEN "one" ACCEPT_TAC;
    ALL_TAC] THEN
  USE_THEN "cont" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; BETA_TAC THEN REAL_ARITH_TAC]);;

(* Leave the project default (as after any file beginning with               *)
(* prioritize_num).                                                          *)

prioritize_num();;
