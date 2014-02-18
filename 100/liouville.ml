(* ========================================================================= *)
(* Liouville approximation theorem.                                          *)
(* ========================================================================= *)

needs "Library/floor.ml";;
needs "Library/poly.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of algebraic and transcendental.                               *)
(* ------------------------------------------------------------------------- *)

let algebraic = new_definition
 `algebraic(x) <=> ?p. ALL integer p /\ ~(poly p = poly []) /\ poly p x = &0`;;

let transcendental = new_definition
 `transcendental(x) <=> ~(algebraic x)`;;

(* ------------------------------------------------------------------------- *)
(* Some trivialities.                                                        *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGER_EQ_0 = prove
 (`!x. integer x /\ abs(x) < &1 ==> x = &0`,
  MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_NOT_LE]);;

let FACT_LE_REFL = prove
 (`!n. n <= FACT n`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ARITH] THEN
  MATCH_MP_TAC(ARITH_RULE `x * 1 <= a ==> x <= a`) THEN
  REWRITE_TAC[LE_MULT_LCANCEL; NOT_SUC; FACT_LT;
              ARITH_RULE `1 <= n <=> 0 < n`]);;

let EXP_LE_REFL = prove
 (`!a. 1 < a ==> !n. n <= a EXP n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `n <= x ==> 1 * x < y ==> SUC n <= y`)) THEN
  REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Archimedian properties taken from Multivariate/misc.ml                    *)
(* ------------------------------------------------------------------------- *)

let REAL_POW_LBOUND = prove
 (`!x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + x) * (&1 + &n * x)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_ARITH
   `&1 + (n + &1) * x <= (&1 + x) * (&1 + n * x) <=> &0 <= n * x * x`]);;

let REAL_ARCH_POW = prove
 (`!x y. &1 < x ==> ?n. y < x pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x - &1` REAL_ARCH) THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real`) THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&1 + &n * (x - &1)` THEN
  ASM_SIMP_TAC[REAL_ARITH `x < y ==> x < &1 + y`] THEN
  ASM_MESON_TAC[REAL_POW_LBOUND; REAL_SUB_ADD2; REAL_ARITH
    `&1 < x ==> &0 <= x - &1`]);;

(* ------------------------------------------------------------------------- *)
(* Inequality variant of mean value theorem.                                 *)
(* ------------------------------------------------------------------------- *)

let MVT_INEQ = prove
 (`!f f' a d M.
        &0 < M /\ &0 < d /\
        (!x. abs(x - a) <= d ==> (f diffl f'(x)) x /\ abs(f' x) < M)
        ==> !x. abs(x - a) <= d ==> abs(f x - f a) < M * d`,
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `x = a \/ x < a \/ a < x`)
  THENL
   [ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_LT_MUL];
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `x:real`; `a:real`]
                 MVT_ALT);
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `a:real`; `x:real`]
                 MVT_ALT)] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  STRIP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d * abs(f'(z:real))` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL;
     MATCH_MP_TAC REAL_LT_LMUL THEN
     ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Appropriate multiple of poly on rational is an integer.                   *)
(* ------------------------------------------------------------------------- *)

let POLY_MULTIPLE_INTEGER = prove
 (`!p q l. ALL integer l ==> integer(&q pow (LENGTH l) * poly l (&p / &q))`,
  GEN_TAC THEN GEN_TAC THEN ASM_CASES_TAC `q = 0` THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[poly; REAL_MUL_RZERO; INTEGER_CLOSED] THEN
    ASM_REWRITE_TAC[LENGTH; real_pow; REAL_MUL_LZERO; INTEGER_CLOSED];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly; REAL_MUL_RZERO; INTEGER_CLOSED] THEN
  REWRITE_TAC[LENGTH; real_pow; ALL] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH
   `(q * qp) * (h + pq * pol) = q * h * qp + (q * pq) * (qp * pol)`] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(el 1 (CONJUNCTS INTEGER_CLOSED)) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* First show any root is surrounded by an other-root-free zone.             *)
(* ------------------------------------------------------------------------- *)

let SEPARATE_FINITE_SET = prove
 (`!a s. FINITE s
         ==> ~(a IN s) ==> ?d. &0 < d /\ !x. x IN s ==> d <= abs(x - a)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `min d (abs(x - a))` THEN
  ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; GSYM REAL_ABS_NZ; REAL_SUB_0] THEN
  ASM_MESON_TAC[REAL_LE_REFL]);;

let POLY_ROOT_SEPARATE_LE = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) < d
                      ==> ~(poly p x' = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `{x | poly p x = &0} DELETE x`]
    SEPARATE_FINITE_SET) THEN
  ASM_SIMP_TAC[POLY_ROOTS_FINITE_SET; FINITE_DELETE; IN_DELETE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN MESON_TAC[REAL_NOT_LT]);;

let POLY_ROOT_SEPARATE_LT = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) <= d
                      ==> ~(poly p x' = &0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP POLY_ROOT_SEPARATE_LE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_MESON_TAC[REAL_ARITH
   `&0 < d ==> &0 < d / &2 /\ (x <= d / &2 ==> x < d)`]);;

(* ------------------------------------------------------------------------- *)
(* And also there is a positive bound on a polynomial in an interval.        *)
(* ------------------------------------------------------------------------- *)

let POLY_BOUND_INTERVAL = prove
 (`!p d x. ?M. &0 < M /\ !x'. abs(x' - x) <= d ==> abs(poly p x') < M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`poly p`; `x - d`; `x + d`] CONT_BOUNDED_ABS) THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] (SPEC_ALL POLY_CONT)] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `&1 + abs M` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `M:real` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Now put these together to get the interval we need.                       *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_INTERVAL = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?c. &0 < c /\
                 (!x'. abs(x' - x) <= c
                       ==> abs(poly(poly_diff p) x') < &1 / c) /\
                 (!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c
                       ==> ~(poly p x' = &0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real list`; `x:real`] POLY_ROOT_SEPARATE_LT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`poly_diff p`; `d:real`; `x:real`] POLY_BOUND_INTERVAL) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `min d (inv M)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LE_MIN; REAL_LT_INV_EQ] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `M:real` THEN
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN] THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Liouville's approximation theorem.                                        *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE = prove
 (`!x. algebraic x
       ==> ?n c. c > &0 /\
                 !p q. ~(q = 0) ==> &p / &q = x \/
                                    abs(x - &p / &q) > c / &q pow n`,
  GEN_TAC THEN REWRITE_TAC[algebraic; real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `LENGTH(l:real list)` THEN
  MP_TAC(SPECL [`l:real list`; `x:real`] LIOUVILLE_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&p / &q = x` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC
   `!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c ==> ~(poly l x' = &0)` THEN
  DISCH_THEN(MP_TAC o SPEC `&p / &q`) THEN REWRITE_TAC[NOT_IMP] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `abs(x - y) <= d ==> d <= e ==> abs(y - x) <= e`)) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LE_LDIV_EQ; LT_NZ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow (LENGTH(l:real list)) * poly l (&p / &q) = &0`
  MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_OF_NUM_EQ]] THEN
  MATCH_MP_TAC REAL_INTEGER_EQ_0 THEN
  ASM_SIMP_TAC[POLY_MULTIPLE_INTEGER] THEN
  MP_TAC(SPECL [`poly l`; `poly(poly_diff l)`; `x:real`;
                `c / &q pow (LENGTH(l:real list))`; `&1 / c`]
               MVT_INEQ) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; LT_NZ; REAL_POW_LT] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REWRITE_RULE[ETA_AX] (SPEC_ALL POLY_DIFF)] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x <= d ==> d <= e ==> x <= e`)) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LE_LDIV_EQ; LT_NZ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[GSYM real_div] THEN DISCH_THEN(MP_TAC o SPEC `&p / &q`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LT_RDIV_EQ; LT_NZ] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Corollary for algebraic irrationals.                                      *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_IRRATIONAL = prove
 (`!x. algebraic x /\ ~rational x
       ==> ?n c. c > &0 /\ !p q. ~(q = 0) ==> abs(x - &p / &q) > c / &q pow n`,
  REWRITE_TAC[RATIONAL_ALT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LIOUVILLE) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  ASM_MESON_TAC[LIOUVILLE; REAL_ABS_DIV; REAL_ABS_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Liouville's constant.                                                     *)
(* ------------------------------------------------------------------------- *)

let liouville = new_definition
 `liouville = suminf (\n. &1 / &10 pow (FACT n))`;;

(* ------------------------------------------------------------------------- *)
(* Some bounds on the partial sums and hence convergence.                    *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_SUM_BOUND = prove
 (`!d n. ~(n = 0)
         ==> sum(n..n+d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`,
  INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; SUM_SING_NUMSEG; real_div] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_OF_NUM_LE; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_ADD] THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= x ==> &1 * x + y <= &2 * x`) THEN
  REWRITE_TAC[ARITH_RULE `n + SUC d = (n + 1) + d`; GSYM real_div] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN REWRITE_TAC[ADD_EQ_0; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[GSYM REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH; FACT_MONO; LE_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow 1` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_POW_MONO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM ADD1; FACT] THEN
  MATCH_MP_TAC(ARITH_RULE
   `1 * x <= SUC n * x /\ ~(n * x = 0) ==> 1 <= SUC n * x - x`) THEN
  ASM_SIMP_TAC[LE_MULT_RCANCEL; MULT_EQ_0] THEN
  REWRITE_TAC[GSYM LT_NZ; FACT_LT] THEN ARITH_TAC);;

let LIOUVILLE_PSUM_BOUND = prove
 (`!n d. ~(n = 0)
         ==> sum(n,d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_SIMP_TAC[sum; REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
  ASM_SIMP_TAC[PSUM_SUM_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(d = 0) ==> (n + d) - 1 = n + (d - 1)`] THEN
  ASM_SIMP_TAC[LIOUVILLE_SUM_BOUND]);;

let LIOUVILLE_SUMS = prove
 (`(\k. &1 / &10 pow FACT k) sums liouville`,
  REWRITE_TAC[liouville] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  REWRITE_TAC[SER_CAUCHY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `inv(e)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `2 * N + 1` THEN
  REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 / &10 pow (FACT m)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= a ==> abs x <= a`) THEN
    ASM_SIMP_TAC[SUM_POS; REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC LIOUVILLE_PSUM_BOUND THEN
    UNDISCH_TAC `2 * N + 1 <= m` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e * &(2 * N + 1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&1 < (n + &1 / &2) * e ==> &2 < e * (&2 * n + &1)`) THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; real_div; REAL_MUL_LID] THEN
    UNDISCH_TAC `inv(e) <= &N` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `10 EXP m` THEN
  REWRITE_TAC[FACT_LE_REFL; LE_EXP; ARITH] THEN SIMP_TAC[EXP_LE_REFL; ARITH]);;

let LIOUVILLE_PSUM_LE = prove
 (`!n. sum(0,n) (\k. &1 / &10 pow FACT k) <= liouville`,
  GEN_TAC THEN REWRITE_TAC[suminf] THEN MATCH_MP_TAC SEQ_LE THEN
  EXISTS_TAC `\j:num. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  EXISTS_TAC `\n:num. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  REWRITE_TAC[SEQ_CONST; GSYM sums; LIOUVILLE_SUMS] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN SIMP_TAC[GE; LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; ADD_CLAUSES; REAL_LE_ADDR] THEN
  SIMP_TAC[SUM_POS; REAL_LE_DIV; REAL_POW_LE; REAL_POS]);;

let LIOUVILLE_PSUM_LT = prove
 (`!n. sum(0,n) (\k. &1 / &10 pow FACT k) < liouville`,
  GEN_TAC THEN MP_TAC(SPEC `SUC n` LIOUVILLE_PSUM_LE) THEN SIMP_TAC[sum] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> x + e <= y ==> x < y`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]);;

let LIOVILLE_PSUM_DIFF = prove
 (`!n. ~(n = 0)
       ==> liouville
             <= sum(0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow (FACT n)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SEQ_LE THEN
  EXISTS_TAC `\n. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  EXISTS_TAC
    `\j:num. sum (0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow FACT n` THEN
  REWRITE_TAC[SEQ_CONST; GSYM sums; LIOUVILLE_SUMS] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN SIMP_TAC[GE; LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_LADD] THEN
  ASM_SIMP_TAC[ADD_CLAUSES; LIOUVILLE_PSUM_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let TRANSCENDENTAL_LIOUVILLE = prove
 (`transcendental(liouville)`,
  REWRITE_TAC[transcendental] THEN DISCH_THEN(MP_TAC o MATCH_MP LIOUVILLE) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `c:real`] THEN
  REWRITE_TAC[DE_MORGAN_THM; real_gt; REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&10`; `&2 / c`] REAL_ARCH_POW) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  ABBREV_TAC `n = m + k + 1` THEN
  EXISTS_TAC `nsum(0..n-1) (\i. 10 EXP (FACT(n-1) - FACT i))` THEN
  EXISTS_TAC `10 EXP (FACT(n-1))` THEN REWRITE_TAC[EXP_EQ_0; ARITH] THEN
  SUBGOAL_THEN
   `&(nsum(0..n-1) (\i. 10 EXP (FACT(n-1) - FACT i))) / &(10 EXP (FACT(n-1))) =
    sum(0..n-1) (\k. &1 / &10 pow (FACT k))`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG; GSYM SUM_LMUL] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_POW; REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH;
             FACT_MONO; real_div; REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ; REAL_POW_EQ_0; ARITH] THEN
    REWRITE_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(GEN `f:num->real`
   (SPECL [`f:num->real`; `0`; `m + k + 1`] PSUM_SUM_NUMSEG)) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  SIMP_TAC[LIOUVILLE_PSUM_LT; REAL_LT_IMP_NE] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  REWRITE_TAC[REAL_SUB_LE; LIOUVILLE_PSUM_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / &10 pow (FACT n)` THEN
  REWRITE_TAC[REAL_LE_SUB_RADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIOVILLE_PSUM_DIFF THEN EXPAND_TAC "n" THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIOVILLE_PSUM_DIFF] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; GSYM EXP_MULT] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow k` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[ARITH_RULE `(m + k + 1) - 1 = m + k`] THEN
  REWRITE_TAC[num_CONV `1`; ADD_CLAUSES; FACT] THEN
  REWRITE_TAC[ARITH_RULE
   `k + f * m <= SUC(m + k) * f <=> k <= (k + 1) * f`] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k = k * 1`] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_ADD] THEN
  REWRITE_TAC[FACT_LT; ARITH_RULE `1 <= x <=> 0 < x`]);;
