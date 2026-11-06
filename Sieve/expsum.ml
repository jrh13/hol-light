(* ========================================================================= *)
(* Exponential sums for the circle method, e(x) = expi x (gauss.ml).         *)
(*                                                                           *)
(* * ndist x (distance to the nearest integer) and emin V x = min(V,         *)
(*   1/ndist x), with V when x is an integer: NDIST_* and EMIN_* lemmas;     *)
(*   NORM_EXPI_SUB_1_LOWER (ndist x <= |e(x) - 1|), VSUM_EXPI_GEOM and       *)
(*   VSUM_EXPI_INTERVAL (|sum of e(m y) over an interval| <= 2 emin L y).    *)
(* * Nathanson's Lemmas 4.9-4.11: for |alpha - a/q| <= 1/q^2, (a,q) = 1,     *)
(*   BLOCK_EMIN_SUM: sum_{r=1..q} emin V (c + r alpha) <= 7 V + 4 q (1 +     *)
(*   log q), through the grid of the c + a r / q (GRID_POINT_BOUND);         *)
(*   EMIN_SUM_CONST and EMIN_SUM_DIV:                                        *)
(*     sum_{k <= U} emin (n/k) (k alpha)                                     *)
(*       <= 14 n / q (1 + log(U + 1)) + 8 (U + q) (1 + log q).               *)
(* * ABEL_BOUND, LOG_EXPSUM_BOUND: Abel summation for the log weights.       *)
(* * SIEVE_SUM_CAUCHY_SCHWARZ; NORM_VSUM_EXPI_POW2:                          *)
(*   |sum c_k e(x_k)|^2 is the double sum of c_i c_j Re e(x_i - x_j)         *)
(*   (for the Type II sums).                                                 *)
(* * GENERAL_CIRCLE and PARSEVAL_EXPSUM: for 3 N < M and any shift t,        *)
(*     sum_{k < M} S(k/M + t)^3 e(-N (k/M + t)) = M #{m1 + m2 + m3 = N}      *)
(*   weighted by w, and sum_{k < M} |S(k/M + t)|^2 = M sum w(m)^2, where     *)
(*   S(x) = sum_{m <= N} w(m) e(m x) (discrete orthogonality; no integrals). *)
(* * DIRICHLET_APPROX: |q x - a| < 1/K with 1 <= q <= K and (a,q) = 1.       *)
(* * Ramanujan sums: RAMANUJAN_FORMULA (sum over reduced residues b of       *)
(*   e(n b/q) = sum_{d | q, d | n} d mu(q/d) =: ramanujan_sum q n),          *)
(*   RAMANUJAN_SUM_MULTIPLICATIVE and RAMANUJAN_SUM_PRIME.                   *)
(* ========================================================================= *)

needs "Sieve/largesieve.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Distance to the nearest integer; truncated reciprocals.                   *)
(* ------------------------------------------------------------------------- *)

let ndist = new_definition
 `ndist x = min (frac x) (&1 - frac x)`;;

let NDIST_BOUNDS = prove
 (`!x. &0 <= ndist x /\ ndist x <= &1 / &2`,
  GEN_TAC THEN REWRITE_TAC[ndist] THEN
  MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN REAL_ARITH_TAC);;

let NDIST_INTEGER_ADD = prove
 (`!x n. integer n ==> ndist(x + n) = ndist x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ndist; REAL_FRAC_ADD] THEN
  ASM_SIMP_TAC[REAL_FRAC_ZERO; REAL_ADD_RID] THEN
  MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let NDIST_NEG = prove
 (`!x. ndist(--x) = ndist x`,
  GEN_TAC THEN REWRITE_TAC[ndist; FRAC_NEG] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_FRAC_ZERO] THEN REAL_ARITH_TAC);;

let NDIST_EQ_0 = prove
 (`!x. ndist x = &0 <=> integer x`,
  GEN_TAC THEN REWRITE_TAC[ndist; GSYM REAL_FRAC_EQ_0] THEN
  MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN REAL_ARITH_TAC);;

let INTEGER_SIGN_CASES = prove
 (`!k. integer k ==> &0 <= k \/ k <= -- &1`,
  GEN_TAC THEN REWRITE_TAC[INTEGER_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_POS] THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[REAL_NEG_0; REAL_LE_REFL] THEN
  DISJ2_TAC THEN REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_LE] THEN
  ASM_ARITH_TAC);;

let NDIST_LE_ABS = prove
 (`!x n. integer n ==> ndist x <= abs(x - n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN STRIP_TAC THEN
  MP_TAC(SPEC `floor x - n` INTEGER_SIGN_CASES) THEN
  ASM_SIMP_TAC[INTEGER_SUB] THEN REWRITE_TAC[ndist] THEN
  ASM_REAL_ARITH_TAC);;

let NDIST_EXISTS = prove
 (`!x. ?n. integer n /\ ndist x = abs(x - n)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN STRIP_TAC THEN
  REWRITE_TAC[ndist] THEN ASM_CASES_TAC `frac x <= &1 - frac x` THENL
   [EXISTS_TAC `floor x` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `floor x + &1` THEN ASM_SIMP_TAC[INTEGER_ADD; INTEGER_CLOSED]
    THEN ASM_REAL_ARITH_TAC]);;

let NDIST_LIPSCHITZ = prove
 (`!x y. ndist x <= ndist y + abs(x - y)`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `y:real` NDIST_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`x:real`; `n:real`] NDIST_LE_ABS) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let NDIST_LE = prove
 (`!x. ndist x <= abs x`,
  GEN_TAC THEN MP_TAC(SPECL [`x:real`; `&0`] NDIST_LE_ABS) THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_SUB_RZERO]);;

let emin = new_definition
 `emin V x = if integer x then V else min V (inv(ndist x))`;;

let EMIN_LE = prove
 (`!V x. emin V x <= V`,
  REPEAT GEN_TAC THEN REWRITE_TAC[emin] THEN COND_CASES_TAC THEN
  REAL_ARITH_TAC);;

let EMIN_POS = prove
 (`!V x. &0 <= V ==> &0 <= emin V x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[emin] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_MIN; REAL_LE_INV_EQ; NDIST_BOUNDS]);;

let EMIN_LE_INV = prove
 (`!V x d. &0 < d /\ d <= ndist x ==> emin V x <= inv d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[emin] THEN
  SUBGOAL_THEN `~(integer x)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NDIST_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `y <= z ==> min x y <= z`) THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]);;

let EMIN_MONO = prove
 (`!V W x. V <= W ==> emin V x <= emin W x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[emin] THEN COND_CASES_TAC THEN
  ASM_REAL_ARITH_TAC);;

let EMIN_INTEGER_ADD = prove
 (`!V x n. integer n ==> emin V (x + n) = emin V x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[emin; NDIST_INTEGER_ADD] THEN
  SUBGOAL_THEN `integer(x + n) <=> integer x` (fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN ASM_SIMP_TAC[INTEGER_ADD] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x = (x + n) - n:real` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_SIMP_TAC[INTEGER_SUB]]);;

let EMIN_NEG = prove
 (`!V x. emin V (--x) = emin V x`,
  REWRITE_TAC[emin; NDIST_NEG; INTEGER_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Geometric sums of e(x).                                                   *)
(* ------------------------------------------------------------------------- *)

let NORM_EXPI_SUB_1_LOWER = prove
 (`!x. ndist x <= norm(expi x - Cx(&1))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  ONCE_REWRITE_TAC[GSYM EXPI_FRAC] THEN REWRITE_TAC[NORM_ONE_SUB_EXPI] THEN
  REWRITE_TAC[ndist] THEN MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN STRIP_TAC THEN
  ABBREV_TAC `u = frac x` THEN
  ASM_CASES_TAC `u <= &1 / &2` THENL
   [MP_TAC(SPEC `u:real` SIN_PI_LOWER_HALF) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPEC `&1 - u` SIN_PI_LOWER_HALF) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sin(pi * (&1 - u)) = sin(pi * u)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID; SIN_SUB; SIN_PI;
                  COS_PI] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let NORM_EXPI_SUB_1_UPPER = prove
 (`!x. norm(expi x - Cx(&1)) <= &2 * pi * abs x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[NORM_ONE_SUB_EXPI]
  THEN MP_TAC(SPEC `pi * x` REAL_ABS_SIN_BOUND_LE) THEN
  SIMP_TAC[REAL_ABS_MUL; PI_POS; REAL_ARITH `&0 < p ==> abs p = p`] THEN
  REAL_ARITH_TAC);;

let VSUM_EXPI_GEOM = prove
 (`!y H. norm(vsum(1..H) (\h. expi(&h * y))) <= &2 * emin (&H) y`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `norm(vsum(1..H) (\h. expi(&h * y))) <= &H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..H) (\h. &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN
      REWRITE_TAC[FINITE_NUMSEG; NORM_EXPI; REAL_LE_REFL];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[emin] THEN COND_CASES_TAC THENL
   [MP_TAC(SPEC `H:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&2 * min a b = min (&2 * a) (&2 * b)`;
              REAL_LE_MIN] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `H:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXPI_NUM_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / norm(Cx(&1) - expi y)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NORM_VSUM_GP_UNIT THEN ASM_REWRITE_TAC[NORM_EXPI; EXPI_EQ_1];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[NORM_EXPI_SUB_1_LOWER] THEN
  REWRITE_TAC[REAL_LT_LE; NDIST_BOUNDS] THEN ASM_MESON_TAC[NDIST_EQ_0]);;

let VSUM_EXPI_INTERVAL = prove
 (`!y a b. norm(vsum(a+1..b) (\m. expi(&m * y))) <= &2 * emin (&(b - a)) y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b <= a:num` THENL
   [ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; ARITH_RULE `b <= a ==> b < a + 1`;
                 NORM_0; ARITH_RULE `b <= a ==> b - a = 0`] THEN
    MP_TAC(SPECL [`&0`; `y:real`] EMIN_POS) THEN REWRITE_TAC[REAL_LE_REFL]
    THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num`; `\m. expi(&m * y)`; `1`; `b - a:num`] VSUM_OFFSET)
  THEN
  SUBGOAL_THEN `1 + a = a + 1 /\ (b - a) + a = b` (fun th -> REWRITE_TAC[th])
  THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; EXPI_ADD] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_NUMSEG; COMPLEX_NORM_MUL;
           NORM_EXPI; REAL_MUL_RID; VSUM_EXPI_GEOM]);;

(* ------------------------------------------------------------------------- *)
(* Sums over residue classes; grids of points.                               *)
(* ------------------------------------------------------------------------- *)

let ITERATE_OVER_RESIDUES_ADD = prove
 (`!op (f:num->V) n k.
        monoidal(op) /\ (!x y. (x == y) (mod n) ==> f x = f y)
        ==> iterate op {d | d < n} (\m. f(k + m)) =
            iterate op {d | d < n} f`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[LT; SET_RULE `{x:num | F} = {}`; ITERATE_CLAUSES];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL_INVERSES) THEN
  MAP_EVERY EXISTS_TAC
   [`\x. (k + x) MOD n`; `\x. (x + (n - k MOD n)) MOD n`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
  SUBGOAL_THEN `k MOD n < n /\ (k MOD n == k) (mod n)` STRIP_ASSUME_TAC
  THENL [ASM_REWRITE_TAC[MOD_LT_EQ; CONG_MOD]; ALL_TAC] THEN
  ABBREV_TAC `u = k MOD n` THEN
  SUBGOAL_THEN `(n - u) + u = n:num` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `v = n - u:num` THEN CONJ_TAC THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(k + (x + v) MOD n == x) (mod n)` MP_TAC THENL
     [MP_TAC(SPECL [`x + v:num`; `n:num`] CONG_MOD) THEN
      UNDISCH_TAC `(u:num == k) (mod n)` THEN UNDISCH_TAC `v + u = n:num` THEN
      CONV_TAC NUMBER_RULE;
      ASM_SIMP_TAC[CONG; MOD_LT]];
    CONJ_TAC THENL
     [SUBGOAL_THEN `((k + x) MOD n + v == x) (mod n)` MP_TAC THENL
       [MP_TAC(SPECL [`k + x:num`; `n:num`] CONG_MOD) THEN
        UNDISCH_TAC `(u:num == k) (mod n)` THEN
        UNDISCH_TAC `v + u = n:num` THEN CONV_TAC NUMBER_RULE;
        ASM_SIMP_TAC[CONG; MOD_LT]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CONG_MOD]]]);;

let SUM_OVER_RESIDUES_ADD = prove
 (`!(f:num->real) n k.
        (!x y. (x == y) (mod n) ==> f x = f y)
        ==> sum {d | d < n} (\m. f(k + m)) = sum {d | d < n} f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sum] THEN
  MATCH_MP_TAC ITERATE_OVER_RESIDUES_ADD THEN
  ASM_REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_OVER_RESIDUES_MUL = prove
 (`!(f:num->real) n k.
        coprime(k,n) /\ (!x y. (x == y) (mod n) ==> f x = f y)
        ==> sum {d | d < n} (\m. f(k * m)) = sum {d | d < n} f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sum] THEN
  MATCH_MP_TAC ITERATE_OVER_RESIDUES_MUL THEN
  ASM_REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_NUMSEG_RESIDUES = prove
 (`!(f:num->real) q.
        1 <= q /\ (!x y. (x == y) (mod q) ==> f x = f y)
        ==> sum(1..q) f = sum {d | d < q} f`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMSEG_LT; ARITH_RULE `1 <= q ==> ~(q = 0)`] THEN
  SUBGOAL_THEN `q = SUC(q - 1)` (fun th -> GEN_REWRITE_TAC
    (LAND_CONV o LAND_CONV o RAND_CONV) [th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  SUBGOAL_THEN `0 + 1 = 1 /\ SUC(q - 1) = q` (fun th -> REWRITE_TAC[th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:num->real) q = f 0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC NUMBER_RULE;
    REAL_ARITH_TAC]);;

let SUM_INV_LT = prove
 (`!q. 1 <= q ==> sum {t | t < q} (\t. inv(&t)) <= &1 + log(&q)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMSEG_LT; ARITH_RULE `1 <= q ==> ~(q = 0)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..q) (\t. inv(&t))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_LE_INV_EQ; REAL_POS] THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; REAL_INV_0; REAL_ADD_LID] THEN
    ASM_SIMP_TAC[HARMONIC_LE_LOG; ARITH_RULE `0 + 1 = 1`]]);;

let SUM_INV_SUB_LT = prove
 (`!q. 1 <= q ==> sum {t | t < q} (\t. inv(&(q - t))) <= &1 + log(&q)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMSEG_LT; ARITH_RULE `1 <= q ==> ~(q = 0)`] THEN
  MP_TAC(ISPECL [`\s:num. inv(&s)`; `1`; `q:num`] SUM_REFLECT) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= q ==> ~(q < 1)`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[HARMONIC_LE_LOG]);;

let GRID_SUM_BOUND = prove
 (`!q V. 1 <= q /\ &0 <= V
         ==> sum {t | t < q}
                 (\t. (if t <= 3 then V else &0) +
                      (if q <= t + 3 then V else &0) +
                      &2 * &q * inv(&t) + &2 * &q * inv(&(q - t)))
             <= &7 * V + &4 * &q * (&1 + log(&q))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {t:num | t < q}` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL] THEN
  SUBGOAL_THEN `{t:num | t < q} = 0..q-1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NUMSEG_LT; ARITH_RULE `1 <= q ==> ~(q = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {t | t < q} (\t. if t <= 3 then V else &0) <= &4 * V`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..3) (\t:num. V)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {t | t < q} (\t. if q <= t + 3 then V else &0) <= &3 * V`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(q-3..q-1) (\t:num. V)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum {t | t < q} (\t. inv(&t)) <= &1 + log(&q) /\
                sum {t | t < q} (\t. inv(&(q - t))) <= &1 + log(&q)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUM_INV_LT; SUM_INV_SUB_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&q * sum {t | t < q} (\t. inv(&t)) <= &q * (&1 + log(&q)) /\
    &q * sum {t | t < q} (\t. inv(&(q - t))) <= &q * (&1 + log(&q))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= &4 * V /\ b <= &3 * V /\ q * c <= q * l /\ q * d <= q * l
    ==> a + b + &2 * q * c + &2 * q * d <= &7 * V + &4 * q * l`) THEN
  ASM_REWRITE_TAC[]);;

let GRID_POINT_BOUND = prove
 (`!q t V x. 1 <= q /\ t < q /\ &0 <= V /\
             abs(x - &t / &q) <= &3 / (&2 * &q)
             ==> emin V x <= (if t <= 3 then V else &0) +
                             (if q <= t + 3 then V else &0) +
                             &2 * &q * inv(&t) + &2 * &q * inv(&(q - t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &2 * &q * inv(&t) /\ &0 <= &2 * &q * inv(&(q - t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `t <= 3` THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPECL [`V:real`; `x:real`] EMIN_LE) THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `q <= t + 3` THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPECL [`V:real`; `x:real`] EMIN_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN
  SUBGOAL_THEN `&0 < &q:real /\ &4 <= &t:real /\ &4 <= &(q - t):real /\
                &t < &q:real`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(x - &t * inv(&q)) <= &3 / &2 * inv(&q)` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(x - &t / &q) <= &3 / (&2 * &q)` THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&q) /\ &q * inv(&q) = &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_RINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(inv(&q)) = &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
  ABBREV_TAC `w = inv(&q)` THEN
  SUBGOAL_THEN `ndist(&t * w) = min (&t * w) (&(q - t) * w)` ASSUME_TAC THENL
   [REWRITE_TAC[ndist] THEN
    SUBGOAL_THEN `frac(&t * w) = &t * w` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_FRAC_EQ] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&q * w` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[REAL_LE_REFL]]];
      AP_TERM_TAC THEN
      SUBGOAL_THEN `&(q - t):real = &q - &t` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
        ASM_ARITH_TAC;
        UNDISCH_TAC `&q * w = &1` THEN CONV_TAC REAL_RING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * w <= ndist(&t * w)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&5 / &8 * ndist(&t * w) <= ndist x` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&t * w`; `x:real`] NDIST_LIPSCHITZ) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&5 / &8 * ndist(&t * w))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EMIN_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_INV_MUL; real_min] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Nathanson Lemmas 4.9-4.11.                                                *)
(* ------------------------------------------------------------------------- *)

let BLOCK_EMIN_SUM = prove
 (`!alpha a q c V.
     1 <= q /\ coprime(a,q) /\ abs(alpha - &a / &q) <= inv(&q pow 2) /\
     &0 <= V
     ==> sum(1..q) (\r. emin V (c + &r * alpha)) <=
         &7 * V + &4 * &q * (&1 + log(&q))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = \t. (if t <= 3 then V else &0) +
                      (if q <= t + 3 then V else &0) +
                      &2 * &q * inv(&t) + &2 * &q * inv(&(q - t))` THEN
  MP_TAC(SPEC `c:real` FLOOR_FRAC) THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = frac c` THEN
  SUBGOAL_THEN `&0 < &q:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `c0 * &q + &1 / &2` FLOOR_POS) THEN ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1 / &2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    DISCH_THEN(X_CHOOSE_TAC `m:num`)] THEN
  MP_TAC(SPEC `c0 * &q + &1 / &2` FLOOR) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `abs(c0 - &m / &q) <= &1 / (&2 * &q)` ASSUME_TAC THENL
   [SUBGOAL_THEN `c0 - &m / &q = (c0 * &q - &m) / &q /\
                  &1 / (&2 * &q) = (&1 / &2) / &q` (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [CONJ_TAC THEN UNDISCH_TAC `&0 < &q:real` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < q ==> abs q = q`;
                   REAL_LE_DIV2_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..q) (\r. (G:num->real)((m + a * r) MOD q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`m + a * r:num`; `q:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `t = (m + a * r) MOD q` THEN
    ABBREV_TAC `d = (m + a * r) DIV q` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real`; `c0 + &r * alpha - &d`; `floor c + &d`]
      EMIN_INTEGER_ADD) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INTEGER_ADD; INTEGER_CLOSED]; ALL_TAC] THEN
    SUBGOAL_THEN `(c0 + &r * alpha - &d) + (floor c + &d) = c + &r * alpha`
    SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "G" THEN MATCH_MP_TAC GRID_POINT_BOUND THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c0 + &r * alpha - &d) - &t / &q =
                  (c0 - &m / &q) + &r * (alpha - &a / &q)` SUBST1_TAC THENL
     [SUBGOAL_THEN `&m + &a * &r = &d * &q + &t` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
        ASM_ARITH_TAC;
        UNDISCH_TAC `&0 < &q:real` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(&r * (alpha - &a / &q)) <= inv(&q)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&q * inv(&q pow 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS; REAL_ABS_POS]
        THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &q:real` THEN
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&3 / (&2 * &q) = &1 / (&2 * &q) + inv(&q)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &q:real` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    UNDISCH_TAC `abs(c0 - &m / &q) <= &1 / (&2 * &q)` THEN
    UNDISCH_TAC `abs(&r * (alpha - &a / &q)) <= inv(&q)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. (x == y) (mod q)
                      ==> (G:num->real)((m + a * x) MOD q) =
                          G((m + a * y) MOD q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CONG] THEN
    UNDISCH_TAC `(x:num == y) (mod q)` THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. (G:num->real)((m + a * r) MOD q)`; `q:num`]
    SUM_NUMSEG_RESIDUES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\s. (G:num->real)((m + s) MOD q)`; `q:num`; `a:num`]
    SUM_OVER_RESIDUES_MUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM CONG] THEN UNDISCH_TAC `(x:num == y) (mod q)` THEN
    CONV_TAC NUMBER_RULE;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\t. (G:num->real)(t MOD q)`; `q:num`; `m:num`]
    SUM_OVER_RESIDUES_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[GSYM CONG];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t < q} (G:num->real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; MOD_LT];
    EXPAND_TAC "G" THEN MATCH_MP_TAC GRID_SUM_BOUND THEN ASM_REWRITE_TAC[]]);;

let SUM_BLOCKS_LE = prove
 (`!f q B H. (!h. sum(1..q) (\r. f(h * q + r)) <= B h)
             ==> sum(1..(H + 1) * q) f <= sum(0..H) B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`H:num`,`H:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUM_SING_NUMSEG] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  SUBGOAL_THEN `(SUC H + 1) * q = (H + 1) * q + q` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sum((H + 1) * q + 1..(H + 1) * q + q) f =
                sum(1..q) (\r. f(SUC H * q + r))` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`(H + 1) * q`; `f:num->real`; `1`; `q:num`] SUM_OFFSET)
    THEN
    SUBGOAL_THEN `1 + (H + 1) * q = (H + 1) * q + 1 /\
                  q + (H + 1) * q = (H + 1) * q + q`
    (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let EMIN_SUM_CONST = prove
 (`!alpha a q n U c.
     1 <= q /\ coprime(a,q) /\ abs(alpha - &a / &q) <= inv(&q pow 2) /\
     &0 <= n
     ==> sum(1..U) (\k. emin n (c + &k * alpha)) <=
         (&U / &q + &1) * (&7 * n + &4 * &q * (&1 + log(&q)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = &7 * n + &4 * &q * (&1 + log(&q))` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC REAL_LE_ADD THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`U:num`; `q:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `H = U DIV q` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..(H + 1) * q) (\k. emin n (c + &k * alpha))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; EMIN_POS; SUBSET; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..H) (\h. B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BLOCKS_LE THEN X_GEN_TAC `h:num` THEN REWRITE_TAC[] THEN
    EXPAND_TAC "B" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
                REAL_ADD_RDISTRIB; REAL_ADD_ASSOC] THEN
    MATCH_MP_TAC BLOCK_EMIN_SUM THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_LE_RADD] THEN
  SUBGOAL_THEN `&0 < &q:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  ASM_ARITH_TAC);;

let GRID_POINT_BOUND2 = prove
 (`!q t V x. 1 <= t /\ t < q /\ abs(x - &t / &q) <= &1 / (&2 * &q)
             ==> emin V x <= &2 * &q * inv(&t) + &2 * &q * inv(&(q - t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &2 * &q * inv(&t) /\ &0 <= &2 * &q * inv(&(q - t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q:real /\ &1 <= &t:real /\ &1 <= &(q - t):real /\
                &t < &q:real`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(x - &t * inv(&q)) <= &1 / &2 * inv(&q)` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(x - &t / &q) <= &1 / (&2 * &q)` THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&q) /\ &q * inv(&q) = &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_RINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(inv(&q)) = &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
  ABBREV_TAC `w = inv(&q)` THEN
  SUBGOAL_THEN `ndist(&t * w) = min (&t * w) (&(q - t) * w)` ASSUME_TAC THENL
   [REWRITE_TAC[ndist] THEN
    SUBGOAL_THEN `frac(&t * w) = &t * w` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_FRAC_EQ] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&q * w` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[REAL_LE_REFL]]];
      AP_TERM_TAC THEN
      SUBGOAL_THEN `&(q - t):real = &q - &t` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
        ASM_ARITH_TAC;
        UNDISCH_TAC `&q * w = &1` THEN CONV_TAC REAL_RING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `w <= ndist(&t * w)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 * ndist(&t * w) <= ndist x` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&t * w`; `x:real`] NDIST_LIPSCHITZ) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&1 / &2 * ndist(&t * w))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EMIN_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_INV_MUL; real_min] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REAL_ARITH_TAC);;

let HALF_BLOCK_SUM = prove
 (`!alpha a q (V:num->real).
     1 <= q /\ coprime(a,q) /\ abs(alpha - &a / &q) <= inv(&q pow 2)
     ==> sum(1..q DIV 2) (\r. emin (V r) (&r * alpha)) <=
         &4 * &q * (&1 + log(&q))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = \t. &2 * &q * inv(&t) + &2 * &q * inv(&(q - t))` THEN
  SUBGOAL_THEN `!t. &0 <= (g:num->real) t` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..q) (\r. (g:num->real)((a * r) MOD q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..q DIV 2) (\r. (g:num->real)((a * r) MOD q))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `2 * r <= q /\ r < q` STRIP_ASSUME_TAC THENL
       [MP_TAC(SPECL [`q:num`; `2`] DIVISION) THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`a * r:num`; `q:num`] DIVISION) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `t = (a * r) MOD q` THEN
      ABBREV_TAC `d = (a * r) DIV q` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(t = 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `q divides r` MP_TAC THENL
         [MATCH_MP_TAC COPRIME_DIVPROD THEN EXISTS_TAC `a:num` THEN
          CONJ_TAC THENL
           [REWRITE_TAC[divides] THEN EXISTS_TAC `d:num` THEN ASM_ARITH_TAC;
            ASM_MESON_TAC[COPRIME_SYM]];
          DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(V:num->real) r`; `&r * alpha - &d`; `&d`]
        EMIN_INTEGER_ADD) THEN
      REWRITE_TAC[INTEGER_CLOSED; REAL_SUB_ADD] THEN
      DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "g" THEN
      MATCH_MP_TAC GRID_POINT_BOUND2 THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      SUBGOAL_THEN `(&r * alpha - &d) - &t / &q = &r * (alpha - &a / &q)`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `&a * &r = &d * &q + &t` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
          ASM_ARITH_TAC;
          UNDISCH_TAC `&0 < &q:real` THEN CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&q / &2 * inv(&q pow 2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS; REAL_ABS_POS]
        THEN UNDISCH_TAC `2 * r <= q` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &q:real` THEN
        CONV_TAC REAL_FIELD];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG] THEN
      MP_TAC(SPECL [`q:num`; `2`] DIV_LE) THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. (x == y) (mod q)
                      ==> (g:num->real)((a * x) MOD q) = g((a * y) MOD q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CONG] THEN
    UNDISCH_TAC `(x:num == y) (mod q)` THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. (g:num->real)((a * r) MOD q)`; `q:num`]
    SUM_NUMSEG_RESIDUES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\s. (g:num->real)(s MOD q)`; `q:num`; `a:num`]
    SUM_OVER_RESIDUES_MUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[GSYM CONG];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t < q} (g:num->real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; MOD_LT];
    ALL_TAC] THEN
  EXPAND_TAC "g" THEN SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT; SUM_LMUL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `q * a <= q * l /\ q * b <= q * l
    ==> &2 * q * a + &2 * q * b <= &4 * q * l`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[SUM_INV_LT; SUM_INV_SUB_LT; REAL_POS]);;

let EMIN_SUM_DIV = prove
 (`!alpha a q n U.
     1 <= q /\ coprime(a,q) /\ abs(alpha - &a / &q) <= inv(&q pow 2) /\
     &0 <= n
     ==> sum(1..U) (\k. emin (n / &k) (&k * alpha)) <=
         &14 * n / &q * (&1 + log(&U + &1)) +
         &8 * (&U + &q) * (&1 + log(&q))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &q:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + log(&q)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..U) (\k. emin (n / &k) (&k * alpha)) =
    sum(1..U) (\k. if 2 * k <= q then emin (n / &k) (&k * alpha) else &0) +
    sum(1..U) (\k. if 2 * k <= q then &0 else emin (n / &k) (&k * alpha))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= &4 * q * l /\ b <= c + &4 * (u + q) * l /\ &0 <= q * l /\
    &0 <= u * l
    ==> a + b <= c + &8 * (u + q) * l`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..q DIV 2) (\k. emin (n / &k) (&k * alpha))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM; IN_DIFF] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_EQ];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC EMIN_POS THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_POS]];
      MP_TAC(ISPECL [`alpha:real`; `a:num`; `q:num`; `\k:num. n / &k`]
        HALF_BLOCK_SUM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]] THEN
  MP_TAC(SPECL [`U:num`; `q:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `H = U DIV q` THEN STRIP_TAC THEN
  ABBREV_TAC
   `f = \k. if 2 * k <= q then &0 else emin (n / &k) (&k * alpha)` THEN
  SUBGOAL_THEN `!k. &0 <= (f:num->real) k` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC EMIN_POS THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..(H + 1) * q) f` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..H) (\h. &14 * n / &q * inv(&h + &1) +
                             &4 * &q * (&1 + log(&q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BLOCKS_LE THEN X_GEN_TAC `h:num` THEN
    SUBGOAL_THEN `&0 <= &2 * n / ((&h + &1) * &q)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..q) (\r. emin (&2 * n / ((&h + &1) * &q))
                                    (&(h * q) * alpha + &r * alpha))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `&(h * q) * alpha + &r * alpha = &(h * q + r) * alpha`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [MATCH_MP_TAC EMIN_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC EMIN_MONO THEN
      SUBGOAL_THEN `(h + 1) * q <= 2 * (h * q + r)` ASSUME_TAC THENL
       [ASM_CASES_TAC `h = 0` THENL
         [UNDISCH_TAC `~(2 * (h * q + r) <= q)` THEN
          ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ARITH_TAC;
          SUBGOAL_THEN `q <= h * q:num` MP_TAC THENL
           [MATCH_MP_TAC(ARITH_RULE `1 * q <= h * q ==> q <= h * q`) THEN
            REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
            ARITH_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (&h + &1) * &q / &2 /\
                    (&h + &1) * &q / &2 <= &(h * q + r)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
          UNDISCH_TAC `(h + 1) * q <= 2 * (h * q + r)` THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL;
                      GSYM REAL_OF_NUM_ADD] THEN
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&2 * n / ((&h + &1) * &q) = n * inv((&h + &1) * &q / &2)`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `&0 < (&h + &1) * &q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[GSYM real_div];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&7 * (&2 * n / ((&h + &1) * &q)) +
                &4 * &q * (&1 + log(&q))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BLOCK_EMIN_SUM THEN EXISTS_TAC `a:num` THEN
      ASM_REWRITE_TAC[];
      BETA_TAC THEN MATCH_MP_TAC(REAL_ARITH `a = b ==> a + c <= b + c`) THEN
      SUBGOAL_THEN `&0 < &h + &1` MP_TAC THENL
       [REAL_ARITH_TAC; UNDISCH_TAC `&0 < &q:real` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG; SUB_0] THEN
  MP_TAC(ISPECL [`1`; `\j:num. inv(&j)`; `0`; `H:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ADD_CLAUSES; GSYM REAL_OF_NUM_ADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `sum(1..H + 1) (\j. inv(&j)) <= &1 + log(&U + &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + log(&(H + 1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HARMONIC_LE_LOG THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_LE_RADD] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `H * q:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `H * 1 <= H * q ==> H <= H * q`) THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(H + 1) * &q <= &U + &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &14 * n / &q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
    THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&(H + 1) * &q <= &U + &q` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Abel summation.                                                           *)
(* ------------------------------------------------------------------------- *)

let ABEL_SUM_NUMSEG = prove
 (`!(x:num->complex) y H.
     vsum(1..H) (\h. x h * y h) =
     vsum(1..H) x * y H -
     vsum(1..H-1) (\h. vsum(1..h) x * (y(h + 1) - y h))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH; COMPLEX_MUL_LZERO; SUB_0;
                COMPLEX_VEC_0; COMPLEX_SUB_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `H = 0` THENL
   [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH; SUB_REFL] THEN
    REWRITE_TAC[VSUM_SING_NUMSEG; COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`; SUC_SUB1] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\h. vsum(1..h) (x:num->complex) * (y(h + 1) - y h)`;
                 `1`; `H:num`] VSUM_CLAUSES_RIGHT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ADD1] THEN CONV_TAC COMPLEX_RING);;

let ABEL_BOUND = prove
 (`!(x:num->complex) y H M.
     &0 <= M /\ (!h. 1 <= h /\ h <= H ==> norm(vsum(1..h) x) <= M)
     ==> norm(vsum(1..H) (\h. x h * y h)) <=
         M * (norm(y H) + sum(1..H-1) (\h. norm(y(h + 1) - y h)))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ABEL_SUM_NUMSEG] THEN
  ASM_CASES_TAC `H = 0` THENL
   [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH; COMPLEX_VEC_0;
                    COMPLEX_MUL_LZERO; COMPLEX_SUB_REFL; COMPLEX_NORM_0;
                    SUB_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_ADD_RID; NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:complex) <= x /\ norm(b:complex) <= y
    ==> norm(a - b) <= x + y`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; COMPLEX_NORM_MUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

let LOG_EXPSUM_BOUND = prove
 (`!y H. norm(vsum(1..H) (\h. Cx(log(&h)) * expi(&h * y))) <=
         &4 * log(&H) * emin (&H) y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `H = 0` THENL
   [SUBGOAL_THEN `emin (&0) y = &0` ASSUME_TAC THENL
     [MP_TAC(SPECL [`&0`; `y:real`] EMIN_LE) THEN
      MP_TAC(SPECL [`&0`; `y:real`] EMIN_POS) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH; NORM_0; REAL_MUL_RZERO;
                      REAL_LE_REFL]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MP_TAC(ISPECL [`\h. expi(&h * y)`; `\h. Cx(log(&h))`; `H:num`;
                 `&2 * emin (&H) y`] ABEL_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC EMIN_POS THEN REWRITE_TAC[REAL_POS];
      X_GEN_TAC `h:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * emin (&h) y` THEN REWRITE_TAC[VSUM_EXPI_GEOM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC EMIN_MONO THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&0 <= log(&H)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..H-1) (\h. norm(Cx(log(&(h + 1))) - Cx(log(&h)))) =
                log(&H)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..H-1) (\h. log(&(h + 1)) - log(&h))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> abs(b - a) = b - a`) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUM_DIFFS_ALT] THEN COND_CASES_TAC THENL
       [SUBGOAL_THEN `H - 1 + 1 = H` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REWRITE_TAC[LOG_1; REAL_SUB_RZERO]];
        SUBGOAL_THEN `H = 1` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REWRITE_TAC[LOG_1]]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cauchy-Schwarz; squares of exponential sums.                              *)
(* ------------------------------------------------------------------------- *)

let SIEVE_SUM_CAUCHY_SCHWARZ = prove
 (`!(f:A->real) g s.
     FINITE s
     ==> sum s (\x. f x * g x) pow 2 <=
         sum s (\x. f x pow 2) * sum s (\x. g x pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = sum s (\x. (f:A->real) x pow 2)` THEN
  ABBREV_TAC `B = sum s (\x. (g:A->real) x pow 2)` THEN
  ABBREV_TAC `Cb = sum s (\x. (f:A->real) x * g x)` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_CASES_TAC `B = &0` THENL
   [SUBGOAL_THEN `!x:A. x IN s ==> g x = &0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x:A. (g:A->real) x pow 2`; `s:A->bool`]
        SUM_POS_EQ_0) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_POW_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `Cb = &0` SUBST1_TAC THENL
     [EXPAND_TAC "Cb" THEN MATCH_MP_TAC SUM_EQ_0 THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO];
      ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum s (\x:A. ((f:A->real) x - Cb / B * g x) pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(a - t * b) pow 2 = a pow 2 - &2 * t * (a * b) + t pow 2 * b pow 2`] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_SUB; SUM_LMUL] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `A - &2 * Cb / B * Cb + (Cb / B) pow 2 * B = A - Cb pow 2 / B`
  SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < B` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPECL [`(Cb:real) pow 2`; `A:real`; `B:real`] REAL_LE_LDIV_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REAL_ARITH_TAC);;

let NORM_VSUM_CAUCHY_SCHWARZ = prove
 (`!(f:A->real) (z:A->complex) s.
     FINITE s
     ==> norm(vsum s (\x. Cx(f x) * z x)) pow 2 <=
         sum s (\x. f x pow 2) * sum s (\x. norm(z x) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum s (\x. abs((f:A->real) x) * norm((z:A->complex) x)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_LE_REFL];
    MP_TAC(ISPECL [`\x. abs((f:A->real) x)`; `\x. norm((z:A->complex) x)`;
                   `s:A->bool`] SIEVE_SUM_CAUCHY_SCHWARZ) THEN
    ASM_REWRITE_TAC[REAL_POW2_ABS]]);;

let RE_MUL_CNJ_EXPI = prove
 (`!a b u v. Re((Cx a * expi u) * cnj(Cx b * expi v)) =
             a * b * Re(expi(u - v))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CNJ_MUL; CNJ_CX; CNJ_EXPI; real_sub; EXPI_ADD] THEN
  SUBGOAL_THEN `(Cx a * expi u) * (Cx b * expi(--v)) =
                Cx(a * b) * (expi u * expi(--v))` SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[RE_MUL_CX; REAL_MUL_ASSOC]]);;

let NORM_VSUM_EXPI_POW2 = prove
 (`!(c:num->real) (x:num->real) Kw.
     norm(vsum(1..Kw) (\k. Cx(c k) * expi(x k))) pow 2 =
     sum(1..Kw) (\i. sum(1..Kw) (\j. c i * c j * Re(expi(x i - x j))))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!z. norm z pow 2 = Re(z * cnj z)` (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_NORM_POW_2; GSYM CX_POW; RE_CX];
    ALL_TAC] THEN
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  SIMP_TAC[RE_VSUM; FINITE_NUMSEG] THEN
  REWRITE_TAC[RE_MUL_CNJ_EXPI]);;

let SUM_SYM_BILINEAR_LE = prove
 (`!(b:num->real) (E:num->num->real) Kw.
     (!i j. E i j = E j i) /\ (!i j. &0 <= E i j)
     ==> sum(1..Kw) (\i. sum(1..Kw) (\j. abs(b i) * abs(b j) * E i j)) <=
         sum(1..Kw) (\i. b i pow 2 * sum(1..Kw) (\j. E i j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Kw) (\i. sum(1..Kw) (\j. b i pow 2 / &2 * E i j)) +
              sum(1..Kw) (\i. sum(1..Kw) (\j. b j pow 2 / &2 * E i j))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[SPECL [`i:num`; `j:num`]
      (ASSUME `!i j. &0 <= (E:num->num->real) i j`)] THEN
    MP_TAC(SPEC `abs((b:num->real) i) - abs(b j)` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(b:num->real) i` REAL_POW2_ABS) THEN
    MP_TAC(SPEC `(b:num->real) j` REAL_POW2_ABS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..Kw) (\i. sum(1..Kw) (\j. b j pow 2 / &2 * E i j)) =
    sum(1..Kw) (\i. sum(1..Kw) (\j. (b:num->real) i pow 2 / &2 * E i j))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC(ASSUME `!i j. (E:num->num->real) i j = E j i`);
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `x + x = &2 * x`; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Discrete orthogonality: the circle identity and Parseval.                 *)
(* ------------------------------------------------------------------------- *)

let VSUM_EXPI_RESIDUES_INT = prove
 (`!M n. ~(M = 0) /\ integer n /\ abs n < &M
         ==> vsum {k | k < M} (\k. expi(n * &k / &M)) =
             if n = &0 then Cx(&M) else Cx(&0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VSUM_EXPI_RESIDUES] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `&0 < &M:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `n = &0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `n / &M` REAL_ABS_INTEGER_LEMMA) THEN
    ASM_REWRITE_TAC[REAL_DIV_EQ_0; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LE_RDIV_EQ; REAL_MUL_LID]
    THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; INTEGER_CLOSED]]);;

let VSUM_MUL_VSUM = prove
 (`!(f:A->complex) (g:B->complex) s t.
     FINITE s /\ FINITE t
     ==> vsum s f * vsum t g = vsum s (\i. vsum t (\j. f i * g j))`,
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL]);;

let EXPI_TRIPLE = prove
 (`!a b c p q r n x.
     ((Cx a * expi(p * x)) * ((Cx b * expi(q * x)) * (Cx c * expi(r * x)))) *
     expi(--(n * x)) =
     Cx(a * b * c) * expi(((p + q + r) - n) * x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `((p + q + r) - n) * x:real =
                          p * x + (q * x + (r * x + --(n * x)))`] THEN
  REWRITE_TAC[EXPI_ADD; CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let CUBE_EXPAND = prove
 (`!(w:num->real) N x.
     vsum(1..N) (\m. Cx(w m) * expi(&m * x)) pow 3 * expi(--(&N * x)) =
     vsum(1..N) (\m1. vsum(1..N) (\m2. vsum(1..N) (\m3.
       Cx(w m1 * w m2 * w m3) * expi(((&m1 + &m2 + &m3) - &N) * x))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `3 = SUC 2`; complex_pow; COMPLEX_POW_2] THEN
  SIMP_TAC[VSUM_MUL_VSUM; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[EXPI_TRIPLE]);;

let VSUM_SWAP3 = prove
 (`!(G:num->num->num->num->complex) N M.
     vsum {k | k < M} (\k. vsum(1..N) (\m1. vsum(1..N) (\m2.
       vsum(1..N) (\m3. G m1 m2 m3 k)))) =
     vsum(1..N) (\m1. vsum(1..N) (\m2. vsum(1..N) (\m3.
       vsum {k | k < M} (\k. G m1 m2 m3 k))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(GEN `f:num->num->complex`
   (MP (ISPECL [`f:num->num->complex`; `{k:num | k < M}`; `1..N`] VSUM_SWAP)
       (CONJ (SPEC `M:num` FINITE_NUMSEG_LT)
             (SPECL [`1`; `N:num`] FINITE_NUMSEG)))) THEN
  DISCH_THEN(fun sw ->
    GEN_REWRITE_TAC LAND_CONV [sw] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m1:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [sw] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m2:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [sw] THEN REWRITE_TAC[]));;

let GENERAL_CIRCLE = prove
 (`!(w:num->real) N M t.
     3 * N < M
     ==> vsum {k | k < M}
           (\k. vsum(1..N) (\m. Cx(w m) * expi(&m * (&k / &M + t))) pow 3 *
                expi(--(&N * (&k / &M + t)))) =
         Cx(&M * sum(1..N) (\m1. sum(1..N) (\m2. sum(1..N) (\m3.
                   if m1 + m2 + m3 = N then w m1 * w m2 * w m3 else &0))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CUBE_EXPAND; VSUM_SWAP3] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m1:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m2:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `m3:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `s = (&m1 + &m2 + &m3) - &N` THEN
  SUBGOAL_THEN `!k. expi(s * (&k / &M + t)) = expi(s * t) * expi(s * &k / &M)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM EXPI_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  MP_TAC(SPECL [`M:num`; `s:real`] VSUM_EXPI_RESIDUES_INT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      EXPAND_TAC "s" THEN SIMP_TAC[INTEGER_CLOSED];
      EXPAND_TAC "s" THEN
      SUBGOAL_THEN `&1 <= &m1 /\ &m1 <= &N /\ &1 <= &m2 /\ &m2 <= &N /\
                    &1 <= &m3 /\ &m3 <= &N /\ &3 * &N < &M`
      MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL; REAL_OF_NUM_LT];
        REAL_ARITH_TAC]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `s = &0 <=> m1 + m2 + m3 = N:num` (fun th -> REWRITE_TAC[th])
  THENL
   [EXPAND_TAC "s" THEN
    REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; CX_MUL] THEN
  SUBGOAL_THEN `s = &0` SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN
    ASM_REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ];
    REWRITE_TAC[REAL_MUL_LZERO; EXPI_0] THEN CONV_TAC COMPLEX_RING]);;

let PARSEVAL_EXPSUM = prove
 (`!(w:num->real) N M t.
     N < M
     ==> sum {k | k < M}
           (\k. norm(vsum(1..N) (\m. Cx(w m) * expi(&m * (&k / &M + t))))
                pow 2) =
         &M * sum(1..N) (\m. w m pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_VSUM_EXPI_POW2] THEN
  SUBGOAL_THEN `FINITE {k:num | k < M}` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  MP_TAC(GEN `f:num->num->real`
   (MP (ISPECL [`f:num->num->real`; `{k:num | k < M}`; `1..N`] SUM_SWAP)
       (CONJ (SPEC `M:num` FINITE_NUMSEG_LT)
             (SPECL [`1`; `N:num`] FINITE_NUMSEG)))) THEN
  DISCH_THEN(fun sw ->
    GEN_REWRITE_TAC LAND_CONV [sw] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [sw]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..N) (\j. if j = i then &M * w i pow 2 else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `s = &i - &j` THEN
  SUBGOAL_THEN
   `!k. &i * (&k / &M + t) - &j * (&k / &M + t) = s * t + s * &k / &M`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "s" THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXPI_ADD] THEN
  SIMP_TAC[GSYM RE_MUL_CX; GSYM RE_VSUM; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  MP_TAC(SPECL [`M:num`; `s:real`] VSUM_EXPI_RESIDUES_INT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      EXPAND_TAC "s" THEN SIMP_TAC[INTEGER_CLOSED];
      EXPAND_TAC "s" THEN
      SUBGOAL_THEN `&1 <= &i /\ &i <= &N /\ &1 <= &j /\ &j <= &N /\
                    &N < &M:real`
      MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT]; REAL_ARITH_TAC]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `s = &0 <=> j = i:num` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; RE_CX; REAL_MUL_RZERO] THEN
  UNDISCH_TAC `j = i:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `s = &0` SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[REAL_SUB_REFL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LZERO; EXPI_0; COMPLEX_MUL_RID; GSYM CX_MUL; RE_CX]
  THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Dirichlet approximation.                                                  *)
(* ------------------------------------------------------------------------- *)

let PIGEONHOLE_NUMSEG = prove
 (`!(g:num->num) Kw.
     (!j. j <= Kw ==> g j < Kw)
     ==> ?j1 j2. j1 < j2 /\ j2 <= Kw /\ g j1 = g j2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(!x y. x IN 0..Kw /\ y IN 0..Kw /\ (g:num->num) x = g y
                       ==> x = y)` MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`g:num->num`; `0..Kw`] CARD_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG] THEN
    MATCH_MP_TAC(ARITH_RULE `c <= Kw ==> ~(c = (Kw + 1) - 0)`) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {n:num | n < Kw}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
      ASM_MESON_TAC[LE_0];
      REWRITE_TAC[CARD_NUMSEG_LT; LE_REFL]];
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; IN_NUMSEG; LE_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num`
      STRIP_ASSUME_TAC)) THEN
    DISJ_CASES_TAC(ARITH_RULE `x < y \/ y < x \/ x = y:num`) THENL
     [MAP_EVERY EXISTS_TAC [`x:num`; `y:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MAP_EVERY EXISTS_TAC [`y:num`; `x:num`] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]]]);;

let DIRICHLET_APPROX = prove
 (`!x Kw. &0 <= x /\ 1 <= Kw
         ==> ?a q. 1 <= q /\ q <= Kw /\ coprime(a,q) /\
                   abs(&q * x - &a) < inv(&Kw)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Kw:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!j. ?n. floor(&Kw * frac(&j * x)) = &n /\ n < Kw` MP_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `&j * x` FLOOR_FRAC) THEN STRIP_TAC THEN
    MP_TAC(SPEC `&Kw * frac(&j * x)` FLOOR_POS) THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    MP_TAC(SPEC `&Kw * frac(&j * x)` FLOOR) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&Kw * frac(&j * x) < &Kw * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:num->num`)] THEN
  MP_TAC(SPECL [`g:num->num`; `Kw:num`] PIGEONHOLE_NUMSEG) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:num` (X_CHOOSE_THEN `j2:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `abs(frac(&j2 * x) - frac(&j1 * x)) < inv(&Kw)` ASSUME_TAC
  THENL
   [MP_TAC(SPEC `&Kw * frac(&j1 * x)` FLOOR) THEN
    MP_TAC(SPEC `&Kw * frac(&j2 * x)` FLOOR) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(SPEC `j1:num` th);
                                      CONJUNCT1(SPEC `j2:num` th)]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `abs(frac(&j2 * x) - frac(&j1 * x)) =
                  abs(&Kw * frac(&j2 * x) - &Kw * frac(&j1 * x)) / &Kw`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
      UNDISCH_TAC `&0 < &Kw:real` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&j1 * x` FLOOR_POS) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
                  DISCH_THEN(X_CHOOSE_TAC `n1:num`)] THEN
  MP_TAC(SPEC `&j2 * x` FLOOR_POS) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
                  DISCH_THEN(X_CHOOSE_TAC `n2:num`)] THEN
  SUBGOAL_THEN `n1 <= n2:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FLOOR_MONO THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(&(j2 - j1) * x - &(n2 - n1)) < inv(&Kw)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    UNDISCH_TAC `abs(frac(&j2 * x) - frac(&j1 * x)) < inv(&Kw)` THEN
    ASM_REWRITE_TAC[FRAC_FLOOR] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n2 - n1:num`; `j2 - j1:num`] GCD_COPRIME_EXISTS) THEN
  ABBREV_TAC `d = gcd(n2 - n1,j2 - j1)` THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `q:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(q = 0) /\ ~(d = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `j2 - j1 = q * d:num` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `q:num`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j2 - j1:num` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `q * 1 <= q * d ==> q <= q * d`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(&(j2 - j1) * x - &(n2 - n1))` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_ARITH `(q * d) * x - a * d = d * (q * x - a):real`] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * y <= d * y ==> y <= d * y`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Ramanujan sums.                                                           *)
(* ------------------------------------------------------------------------- *)

let VSUM_MULTIPLES_LT = prove
 (`!(f:num->complex) d q.
     1 <= d /\ d divides q
     ==> vsum {b | b < q /\ d divides b} f =
         vsum {j | j < q DIV d} (\j. f(d * j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{b | b < q
    /\ d divides b} = IMAGE (\j. d * j) {j | j < q DIV d}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `b:num` THEN
    UNDISCH_TAC `d divides q` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST1_TAC) THEN
    ASM_SIMP_TAC[DIV_MULT; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `j:num`)) THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `b < d * e:num` THEN ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
      ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j:num. d * j`; `f:num->complex`; `{j:num | j < q DIV d}`]
    VSUM_IMAGE) THEN
  REWRITE_TAC[o_DEF; FINITE_NUMSEG_LT; IN_ELIM_THM; EQ_MULT_LCANCEL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;

let INTEGER_DIV_DIVIDES = prove
 (`!m n. ~(m = 0) ==> (integer(&n / &m) <=> m divides n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `n:num`; `0`] INTEGER_QUOTIENT_CONG) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; CONG_0]);;

let VSUM_RESTRICT_IND = prove
 (`!(c:real) P (f:num->complex) q.
     vsum {b | b < q} (\b. Cx(if P b then c else &0) * f b) =
     Cx c * vsum {b | b < q /\ P b} f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `{b:num | b < q /\ P b} = {b | b IN {b | b < q}
    /\ P b}`]
  THEN
  REWRITE_TAC[VSUM_RESTRICT_SET] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC VSUM_EQ THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_VEC_0]);;

let RAMANUJAN_FORMULA = prove
 (`!q n. 1 <= q
         ==> vsum {b | b < q /\ coprime(b,q)} (\b. expi(&n * &b / &q)) =
             Cx(sum {d | d divides q /\ d divides n}
                    (\d. &d * mobius(q DIV d)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {d | d divides q}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. (if coprime(b,q) then &1 else &0) =
        sum {d | d divides q} (\d. if d divides b then mobius d else &0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[COPRIME_GCD] THEN
    MP_TAC(SPEC `gcd(b,q)` DIVISORSUM_MOBIUS) THEN ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; GCD_ZERO] THEN
      ASM_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET; ETA_AX] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; DIVIDES_GCD] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {b | b < q}
                (\b. Cx(if coprime(b,q) then &1 else &0) *
                     expi(&n * &b / &q))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM VSUM_CX; GSYM VSUM_COMPLEX_RMUL] THEN
  MP_TAC(GEN `f:num->num->complex`
   (MP (ISPECL [`f:num->num->complex`; `{b:num | b < q}`;
                `{d | d divides q}`] VSUM_SWAP)
       (CONJ (SPEC `q:num` FINITE_NUMSEG_LT)
             (ASSUME `FINITE {d | d divides q}`)))) THEN
  DISCH_THEN(fun sw -> GEN_REWRITE_TAC LAND_CONV [sw]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {d | d divides q}
               (\d. Cx(mobius d *
                       (if (q DIV d) divides n then &(q DIV d) else &0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= d /\ q = d * q DIV d` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= d <=> ~(d = 0)`] THEN DISCH_TAC THEN
        UNDISCH_TAC `d divides q` THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
        ASM_ARITH_TAC;
        ASM_MESON_TAC[DIVIDES_DIV_MULT; MULT_SYM]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(q DIV d = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `q = d * q DIV d` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VSUM_RESTRICT_IND] THEN ASM_SIMP_TAC[VSUM_MULTIPLES_LT] THEN
    SUBGOAL_THEN `!j. expi(&n * &(d * j) / &q) =
                      expi(&n * &j / &(q DIV d))` (fun th -> REWRITE_TAC[th])
    THENL
     [GEN_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `&q = &d * &(q DIV d)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ]
         THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      SUBGOAL_THEN `~(&d = &0) /\ ~(&(q DIV d) = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VSUM_EXPI_RESIDUES; INTEGER_CLOSED; INTEGER_DIV_DIVIDES] THEN
    COND_CASES_TAC THEN REWRITE_TAC[CX_MUL; REAL_MUL_RZERO; COMPLEX_MUL_RZERO];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_CX] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\e. mobius(q DIV e) * (if e divides n then &e else &0)`;
                 `q:num`] SUM_DIVISORS_REFLECT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]] THEN
  MATCH_MP_TAC(MESON[]
   `(a:real) = b /\ (c:real) = d ==> b = c ==> a = d`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `q DIV (q DIV d) = d` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `d divides q` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
    ASM_CASES_TAC `d = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; DIV_0]; ALL_TAC] THEN
    ASM_CASES_TAC `e = 0` THENL
     [UNDISCH_TAC `1 <= d * e` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[DIV_MULT; ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT];
    REWRITE_TAC[COND_RAND; REAL_MUL_RZERO; GSYM SUM_RESTRICT_SET] THEN
    REWRITE_TAC[SET_RULE `{x | x IN {d | d divides q} /\ x divides n} =
                          {d | d divides q /\ d divides n}`] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let ramanujan_sum = new_definition
 `ramanujan_sum q n = sum {d | d divides q
   /\ d divides n} (\d. &d * mobius(q DIV d))`;;

let REAL_MULTIPLICATIVE_MUL = prove
 (`!f g. real_multiplicative f /\ real_multiplicative g
         ==> real_multiplicative (\n. f n * g n)`,
  REWRITE_TAC[real_multiplicative] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC);;

let REAL_MULTIPLICATIVE_ABS = prove
 (`!f. real_multiplicative f ==> real_multiplicative (\n. abs(f n))`,
  SIMP_TAC[real_multiplicative; REAL_ABS_MUL; REAL_ABS_NUM]);;

let REAL_MULTIPLICATIVE_INV_POW = prove
 (`!f k. real_multiplicative f ==> real_multiplicative (\n. inv(f n) pow k)`,
  SIMP_TAC[real_multiplicative; REAL_INV_MUL; REAL_POW_MUL; REAL_INV_1;
           REAL_POW_ONE]);;

let REAL_MULTIPLICATIVE_PHI = prove
 (`real_multiplicative (\n. &(phi n))`,
  MP_TAC MULTIPLICATIVE_PHI THEN
  SIMP_TAC[multiplicative; real_multiplicative; REAL_OF_NUM_MUL]);;

let RAMANUJAN_SUM_MULTIPLICATIVE = prove
 (`!n. real_multiplicative (\q. ramanujan_sum q n)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(\q. ramanujan_sum q n) =
    (\q. sum {d | d divides q}
             (\d. (\d. if d divides n then &d else &0) d * mobius(q DIV d)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ramanujan_sum] THEN GEN_TAC THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_MULTIPLICATIVE_CONVOLUTION THEN
  REWRITE_TAC[REAL_MULTIPLICATIVE_MOBIUS; real_multiplicative] THEN
  REWRITE_TAC[DIVIDES_1; REAL_OF_NUM_EQ] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a * b divides n <=> a divides n /\ b divides n`
  (fun th -> REWRITE_TAC[th]) THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THEN MATCH_MP_TAC DIVIDES_TRANS THEN
      EXISTS_TAC `a * b:num` THEN ASM_REWRITE_TAC[] THEN NUMBER_TAC;
      STRIP_TAC THEN MATCH_MP_TAC DIVIDES_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY ASM_CASES_TAC [`a divides n`; `b divides n`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_OF_NUM_MUL;
                  MULT_CLAUSES]);;

let RAMANUJAN_SUM_PRIME = prove
 (`!p n. prime p
         ==> ramanujan_sum p n = if p divides n then &p - &1 else -- &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ramanujan_sum] THEN
  SUBGOAL_THEN `~(p = 1) /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_1; PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `{d | d divides p /\ d divides n} =
                if p divides n then {1,p} else {1}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN
    COND_CASES_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    EQ_TAC THENL
     [ASM_MESON_TAC[prime];
      STRIP_TAC THEN ASM_REWRITE_TAC[DIVIDES_1; DIVIDES_REFL];
      ASM_MESON_TAC[prime];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIVIDES_1]];
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[DIV_1; MOBIUS_1] THEN
  ASM_SIMP_TAC[DIV_REFL; MOBIUS_PRIME; MOBIUS_1] THEN REAL_ARITH_TAC);;
