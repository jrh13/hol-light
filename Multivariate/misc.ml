(* ========================================================================= *)
(* Various convenient background stuff not specifically to do with R^n.      *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*                (c) Copyright, Marco Maggesi 2014                          *)
(* ========================================================================= *)

needs "Library/card.ml";;
needs "Library/floor.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* A couple of extra tactics used in some proofs below.                      *)
(* ------------------------------------------------------------------------- *)

let ASSERT_TAC tm =
  SUBGOAL_THEN tm STRIP_ASSUME_TAC;;

let EQ_TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)

let FORALL_DIFF = prove
 (`(!s:A->bool. P(UNIV DIFF s)) <=> (!s. P s)`,
  MESON_TAC[COMPL_COMPL]);;

let EXISTS_DIFF = prove
 (`(?s:A->bool. P(UNIV DIFF s)) <=> (?s. P s)`,
  MESON_TAC[COMPL_COMPL]);;

let FORALL_DIFF_ALT = prove
 (`!u:A->bool.
    (!s. s SUBSET u ==> P(u DIFF s)) <=> (!s. s SUBSET u ==> P s)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u DIFF s:A->bool`) THEN
  REWRITE_TAC[SUBSET_DIFF] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN ASM SET_TAC[]);;

let FORALL_DIFF_GEN = prove
 (`!u:A->bool.
    (!s. P(u DIFF s)) <=> (!s. s SUBSET u ==> P s)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN TRY DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u DIFF s:A->bool`) THEN
  REWRITE_TAC[SUBSET_DIFF] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN ASM SET_TAC[]);;

let GE_REFL = prove
 (`!n:num. n >= n`,
  REWRITE_TAC[GE; LE_REFL]);;

let FORALL_SUC = prove
 (`(!n. ~(n = 0) ==> P n) <=> (!n. P(SUC n))`,
  MESON_TAC[num_CASES; NOT_SUC]);;

let SEQ_MONO_LEMMA = prove
 (`!d e. (!n. n >= m ==> d(n) < e(n)) /\ (!n. n >= m ==> e(n) <= e(m))
         ==> !n:num. n >= m ==> d(n) < e(m)`,
  MESON_TAC[GE; REAL_LTE_TRANS]);;

let REAL_HALF = prove
 (`(!e. &0 < e / &2 <=> &0 < e) /\
   (!e. e / &2 + e / &2 = e) /\
   (!e. &2 * (e / &2) = e)`,
  REAL_ARITH_TAC);;

let UPPER_BOUND_FINITE_SET = prove
 (`!f:(A->num) s. FINITE(s) ==> ?a. !x. x IN s ==> f(x) <= a`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  METIS_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let UPPER_BOUND_FINITE_SET_REAL = prove
 (`!f:(A->real) s. FINITE(s) ==> ?a. !x. x IN s ==> f(x) <= a`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  METIS_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let LOWER_BOUND_FINITE_SET = prove
 (`!f:(A->num) s. FINITE(s) ==> ?a. !x. x IN s ==> a <= f(x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  METIS_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let LOWER_BOUND_FINITE_SET_REAL = prove
 (`!f:(A->real) s. FINITE(s) ==> ?a. !x. x IN s ==> a <= f(x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  METIS_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let REAL_CONVEX_BOUND2_LT = prove
 (`!x y a u v. x < a /\ y < b /\ &0 <= u /\ &0 <= v /\ u + v = &1
               ==> u * x + v * y < u * a + v * b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `u = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN REPEAT STRIP_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_ADD2 THEN
    ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE]] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC);;

let REAL_CONVEX_BOUND_LT = prove
 (`!x y a u v. x < a /\ y < a /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
               ==> u * x + v * y < a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `u * a + v * a:real` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_CONVEX_BOUND2_LT];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `u + v = &1` THEN CONV_TAC REAL_RING]);;

let REAL_CONVEX_BOUND_LE = prove
 (`!x y a u v. x <= a /\ y <= a /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
               ==> u * x + v * y <= a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(u + v) * a` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LID]] THEN
  ASM_SIMP_TAC[REAL_ADD_RDISTRIB; REAL_LE_ADD2; REAL_LE_LMUL]);;

let REAL_CONVEX_SUM_BOUND_LE = prove
 (`!s d a b x:A->real.
        (!i. i IN s ==> &0 <= x i) /\ sum s x = &1 /\
        (!i. i IN s ==> abs(a i - b) <= d)
        ==> abs(sum s (\i. a i * x i) - b) <= d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sum] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[GSYM sum; NEUTRAL_REAL_ADD; support; REAL_ENTIRE] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN s /\ ~(P x \/ Q x)} =
    {x | x IN {y | y IN s /\ ~Q y} /\ ~P x}`] THEN
  ABBREV_TAC `t = {i | i IN s /\ ~((x:A->real) i = &0)}` THEN
  ASM_CASES_TAC `FINITE(t:A->bool)` THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i. i IN t ==> &0 <= (x:A->real) i) /\
    (!i. i IN t ==> abs(a i - b) <= d)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_RESTRICT_SET; MESON[REAL_MUL_LZERO]
   `(if ~(a = &0) then a * x else &0) = a * x`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a - b = a - b * &1`] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
  ASM_REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  TRANS_TAC REAL_LE_TRANS `sum t (\i:A. d * x i)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[REAL_LE_RMUL];
    ASM_REWRITE_TAC[SUM_LMUL; REAL_MUL_RID; REAL_LE_REFL]]);;

let REAL_CONVEX_SUM_BOUND_LT = prove
 (`!s d a b x:A->real.
        (!i. i IN s ==> &0 <= x i) /\ sum s x = &1 /\
        (!i. i IN s ==> abs(a i - b) < d)
        ==> abs(sum s (\i. a i * x i) - b) < d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sum] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[GSYM sum; NEUTRAL_REAL_ADD; support; REAL_ENTIRE] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN s /\ ~(P x \/ Q x)} =
    {x | x IN {y | y IN s /\ ~Q y} /\ ~P x}`] THEN
  ABBREV_TAC `t = {i | i IN s /\ ~((x:A->real) i = &0)}` THEN
  ASM_CASES_TAC `FINITE(t:A->bool)` THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i. i IN t ==> &0 < (x:A->real) i) /\
    (!i. i IN t ==> abs(a i - b) < d)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    SIMP_TAC[IN_ELIM_THM; REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RESTRICT_SET; MESON[REAL_MUL_LZERO]
   `(if ~(a = &0) then a * x else &0) = a * x`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a - b = a - b * &1`] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
  ASM_REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS) THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  TRANS_TAC REAL_LTE_TRANS `sum t (\i:A. d * x i)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LT_ALL THEN ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUM_CLAUSES]) THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUM_LMUL; REAL_MUL_RID; REAL_LE_REFL]]);;

let APPROACHABLE_LT_LE = prove
 (`!P f. (?d. &0 < d /\ !x. f(x) < d ==> P x) =
         (?d. &0 < d /\ !x. f(x) <= d ==> P x)`,
  let lemma = prove
   (`&0 < d ==> x <= d / &2 ==> x < d`,
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN REAL_ARITH_TAC) in
  MESON_TAC[REAL_LT_IMP_LE; lemma; REAL_HALF]);;

let REAL_LE_BETWEEN = prove
 (`!a b. a <= b <=> ?x. a <= x /\ x <= b`,
  MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL]);;

let REAL_LET_BETWEEN = prove
 (`!a b. a < b <=> (?x. a <= x /\ x < b)`,
  MESON_TAC[REAL_LE_REFL; REAL_LET_TRANS]);;

let REAL_LTE_BETWEEN = prove
 (`!a b. a < b <=> (?x. a < x /\ x <= b)`,
  MESON_TAC[REAL_LE_REFL; REAL_LTE_TRANS]);;

let REAL_LT_BETWEEN = prove
 (`!a b. a < b <=> ?x. a < x /\ x < b`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LT_TRANS]] THEN
  DISCH_TAC THEN EXISTS_TAC `(a + b) / &2` THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let REAL_LT_BETWEEN_GEN = prove
 (`!s t:real->bool.
        FINITE s /\ FINITE t
        ==> ((?x. (!a. a IN s ==> a < x) /\ (!b. b IN t ==> x < b)) <=>
             !a b. a IN s /\ b IN t ==> a < b)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[MESON[REAL_SUP_LT_FINITE; NOT_IN_EMPTY]
   `FINITE s ==> ((!a. a IN s ==> a < x) <=> s = {} \/ sup s < x)`] THEN
  SIMP_TAC[MESON[REAL_LT_INF_FINITE; NOT_IN_EMPTY]
   `FINITE t ==> ((!b. b IN t ==> x < b) <=> t = {} \/ x < inf t)`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `s:real->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL
   [MESON_TAC[REAL_ARITH `s - &1 < s`]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL
   [MESON_TAC[REAL_ARITH `t < t + &1`]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LT_BETWEEN] THEN
  ASM_SIMP_TAC[REAL_SUP_LT_FINITE; REAL_LT_INF_FINITE] THEN MESON_TAC[]);;

let TRIANGLE_LEMMA = prove
 (`!x y z. &0 <= x /\ &0 <= y /\ &0 <= z /\ x pow 2 <= y pow 2 + z pow 2
           ==> x <= y + z`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(y + z) pow 2` THEN
  ASM_SIMP_TAC[REAL_POW_LT2; REAL_LE_ADD; ARITH_EQ] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_2; REAL_ARITH
   `x * x + y * y <= (x + y) * (x + y) <=> &0 <= x * y`]);;

let LAMBDA_SKOLEM = prove
 (`(!i. 1 <= i /\ i <= dimindex(:N) ==> ?x. P i x) =
   (?x:A^N. !i. 1 <= i /\ i <= dimindex(:N) ==> P i (x$i))`,
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `x:num->A`) THEN
    EXISTS_TAC `(lambda i. x i):A^N` THEN ASM_SIMP_TAC[LAMBDA_BETA];
    DISCH_THEN(X_CHOOSE_TAC `x:A^N`) THEN
    EXISTS_TAC `\i. (x:A^N)$i` THEN ASM_REWRITE_TAC[]]);;

let LAMBDA_PAIR = prove
 (`(\(x,y). P x y) = (\p. P (FST p) (SND p))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let EPSILON_DELTA_MINIMAL = prove
 (`!P:real->A->bool Q.
        FINITE {x | Q x} /\
        (!d e x. Q x /\ &0 < e /\ e < d ==> P d x ==> P e x) /\
        (!x. Q x ==> ?d. &0 < d /\ P d x)
        ==> ?d. &0 < d /\ !x. Q x ==> P d x`,
  REWRITE_TAC[IMP_IMP] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `{x:A | Q x} = {}` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_ELIM_THM] THEN
    DISCH_TAC THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01];
    FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:A->real` THEN DISCH_TAC THEN
    EXISTS_TAC `inf(IMAGE d {x:A | Q x})` THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 < inf(IMAGE d {x:A | Q x}) /\ inf(IMAGE d {x | Q x}) <= d a`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INF_FINITE; REAL_INF_LE_FINITE;
                   FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_LE_REFL];
      REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `(d:A->real) a` THEN ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Handy definitions and basic lemmas for real intervals.                    *)
(* ------------------------------------------------------------------------- *)

let is_realinterval = new_definition
 `is_realinterval s <=>
        !a b c. a IN s /\ b IN s /\ a <= c /\ c <= b ==> c IN s`;;

let IS_REALINTERVAL_EMPTY = prove
 (`is_realinterval {}`,
  REWRITE_TAC[is_realinterval; NOT_IN_EMPTY]);;

let IS_REALINTERVAL_UNION = prove
 (`!s t. is_realinterval s /\ is_realinterval t /\ ~(s INTER t = {})
         ==> is_realinterval(s UNION t)`,
  REWRITE_TAC[is_realinterval; IN_UNION; IN_INTER;
              NOT_IN_EMPTY; EXTENSION] THEN
  MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL]);;

let IS_REALINTERVAL_UNIV = prove
 (`is_realinterval (:real)`,
  REWRITE_TAC[is_realinterval; IN_UNIV]);;

let open_real_interval = new_definition
  `open_real_interval(a:real,b:real) = {x:real | a < x /\ x < b}`;;

let closed_real_interval = define
  `closed_real_interval[a:real,b:real] = {x:real | a <= x /\ x <= b}`;;

make_overloadable "real_interval" `:A`;;

overload_interface("real_interval",`open_real_interval`);;
overload_interface("real_interval",`closed_real_interval`);;

let real_interval = prove
 (`real_interval(a,b) = {x | a < x /\ x < b} /\
   real_interval[a,b] = {x | a <= x /\ x <= b}`,
  REWRITE_TAC[open_real_interval; closed_real_interval]);;

let IN_REAL_INTERVAL = prove
 (`!a b x. (x IN real_interval[a,b] <=> a <= x /\ x <= b) /\
           (x IN real_interval(a,b) <=> a < x /\ x < b)`,
  REWRITE_TAC[real_interval; IN_ELIM_THM]);;

let EMPTY_AS_REAL_INTERVAL = prove
 (`{} = real_interval[&1,&0]`,
  REWRITE_TAC[EXTENSION; IN_REAL_INTERVAL; NOT_IN_EMPTY] THEN REAL_ARITH_TAC);;

let REAL_INTERVAL_OPEN_SUBSET_CLOSED = prove
 (`!a b. real_interval(a,b) SUBSET real_interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let REAL_INTERVAL_EQ_EMPTY = prove
 (`(!a b. real_interval[a,b] = {} <=> b < a) /\
   (!a b. real_interval(a,b) = {} <=> b <= a)`,
  REWRITE_TAC[EXTENSION; IN_REAL_INTERVAL; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM NOT_EXISTS_THM] THEN
  REWRITE_TAC[GSYM REAL_LT_BETWEEN; GSYM REAL_LE_BETWEEN] THEN
  REAL_ARITH_TAC);;

let REAL_INTERVAL_NE_EMPTY = prove
 (`(!a b. ~(real_interval[a,b] = {}) <=> a <= b) /\
   (!a b. ~(real_interval(a,b) = {}) <=> a < b)`,
  REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LE; REAL_NOT_LT]);;

let REAL_INTERVAL_SING = prove
 (`!a. real_interval[a,a] = {a} /\ real_interval(a,a) = {}`,
  REWRITE_TAC[EXTENSION; IN_SING; NOT_IN_EMPTY; IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

let ENDS_IN_REAL_INTERVAL = prove
 (`(!a b. a IN real_interval[a,b] <=> ~(real_interval[a,b] = {})) /\
   (!a b. b IN real_interval[a,b] <=> ~(real_interval[a,b] = {})) /\
   (!a b. ~(a IN real_interval(a,b))) /\
   (!a b. ~(b IN real_interval(a,b)))`,
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN REAL_ARITH_TAC);;

let IN_REAL_INTERVAL_REFLECT = prove
 (`(!a b x. --x IN real_interval[--b,--a] <=> x IN real_interval[a,b]) /\
   (!a b x. --x IN real_interval(--b,--a) <=> x IN real_interval(a,b))`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let REFLECT_REAL_INTERVAL = prove
 (`(!a b. IMAGE (--) (real_interval[a,b]) = real_interval[--b,--a]) /\
   (!a b. IMAGE (--) (real_interval(a,b)) = real_interval(--b,--a))`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_REAL_INTERVAL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x:real = --y <=> --x = y`] THEN
  REWRITE_TAC[UNWIND_THM1] THEN REAL_ARITH_TAC);;

let IS_REALINTERVAL_INTERVAL = prove
 (`!a b. is_realinterval(real_interval(a,b)) /\
         is_realinterval(real_interval[a,b])`,
  REWRITE_TAC[is_realinterval; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let ENDS_IN_UNIT_REAL_INTERVAL = prove
 (`&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`,
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL]);;

let INTER_REAL_INTERVAL = prove
 (`!a b c d.
        real_interval[a,b] INTER real_interval[c,d] =
        real_interval[max a c,min b d]`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

let REAL_OPEN_CLOSED_INTERVAL = prove
 (`!a b. real_interval(a,b) = real_interval[a,b] DIFF {a,b}`,
  SIMP_TAC[EXTENSION; IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let REAL_CLOSED_OPEN_INTERVAL = prove
 (`!a b. a <= b ==> real_interval[a,b] = real_interval(a,b) UNION {a,b}`,
  SIMP_TAC[EXTENSION; IN_UNION; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let IS_REALINTERVAL_SHRINK = prove
 (`!s. is_realinterval (IMAGE (\x. x / (&1 + abs x)) s) <=>
       is_realinterval s`,
  REWRITE_TAC[is_realinterval; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[SET_RULE `y IN IMAGE f s <=> ?x. f x = y /\ x IN s`] THEN
  REWRITE_TAC[MESON[REAL_SHRINK_GALOIS]
   `(?x. x / (&1 + abs x) = c /\ x IN s) <=>
    (?x. x / (&1 + abs x) = c) /\ (!x. x / (&1 + abs x) = c ==> x IN s)`] THEN
  REWRITE_TAC[TAUT `(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_IMP_FORALL_THM] THEN
  MATCH_MP_TAC(TAUT `(q <=> r) /\ p ==> (p /\ q <=> r)`) THEN
  CONJ_TAC THENL [MESON_TAC[REAL_SHRINK_LE]; ALL_TAC] THEN
  MESON_TAC[REAL_SHRINK_RANGE; REAL_SHRINK_GROW; REAL_ARITH
   `a <= x /\ x <= b /\ abs a < &1 /\ abs b < &1 ==> abs x < &1`]);;

let SUBSET_REAL_INTERVAL = prove
 (`!a b c d.
        (real_interval[a,b] SUBSET real_interval[c,d] <=>
                b < a \/ c <= a /\ a <= b /\ b <= d) /\
        (real_interval[a,b] SUBSET real_interval(c,d) <=>
                b < a \/ c < a /\ a <= b /\ b < d) /\
        (real_interval(a,b) SUBSET real_interval[c,d] <=>
                b <= a \/ c <= a /\ a < b /\ b <= d) /\
        (real_interval(a,b) SUBSET real_interval(c,d) <=>
                b <= a \/ c <= a /\ a < b /\ b <= d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
  REPEAT CONJ_TAC THEN (EQ_TAC THENL [ALL_TAC; REAL_ARITH_TAC]) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `(a + min b c) / &2` th) THEN
    MP_TAC(SPEC `(max d a + b) / &2` th)) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Converting between matrices/arrays and flattened vectors. We can consider *)
(* these as curry and uncurry for Cartesian powers.                          *)
(* ------------------------------------------------------------------------- *)

let vectorize = new_definition
 `(vectorize:A^N^M->A^(M,N)finite_prod) =
        \x. lambda i. x$(1 + (i - 1) DIV dimindex(:N))
                       $(1 + (i - 1) MOD dimindex(:N))`;;

let matrify = new_definition
 `(matrify:A^(M,N)finite_prod->A^N^M) =
        \x. lambda i j. x$((i - 1) * dimindex(:N) + j)`;;

let VECTORIZE_COMPONENT = prove
 (`!m:A^N^M i.
        1 <= i /\ i <= dimindex(:M) * dimindex(:N)
        ==> (vectorize m)$i = m$(1 + (i - 1) DIV dimindex(:N))
                              $(1 + (i - 1) MOD dimindex(:N))`,
  SIMP_TAC[vectorize; LAMBDA_BETA; DIMINDEX_FINITE_PROD]);;

let MATRIFY_COMPONENT = prove
 (`!v:A^(M,N)finite_prod i j.
        1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (matrify v)$i$j = v$((i - 1) * dimindex(:N) + j)`,
  SIMP_TAC[matrify; LAMBDA_BETA]);;

let VECTORIZE_MATRIFY = prove
 (`!a:A^(M,N)finite_prod. vectorize(matrify a) = a`,
  GEN_TAC THEN SIMP_TAC[CART_EQ; vectorize; matrify; LAMBDA_BETA] THEN
  REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LAMBDA_BETA o lhand o lhand o snd) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 1 + x /\ 1 + y <= z <=> y < z`] THEN
  SIMP_TAC[RDIV_LT_EQ; DIMINDEX_GE_1; LE_1] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LAMBDA_BETA o lhand o snd) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 1 + x /\ 1 + y <= z <=> y < z`] THEN
  SIMP_TAC[DIVISION; DIMINDEX_GE_1; LE_1] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[ADD_SUB2] THEN
  MATCH_MP_TAC(ARITH_RULE
   `1 <= i /\ i - 1 = d * n + m /\ m < n
     ==> d * n + 1 + m = i`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1]);;

let MATRIFY_VECTORIZE = prove
 (`!m:A^N^M. matrify(vectorize m) = m`,
  GEN_TAC THEN SIMP_TAC[CART_EQ; vectorize; matrify; LAMBDA_BETA] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LAMBDA_BETA o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC LE_TRANS `(i - 1) * dimindex(:N) + dimindex(:N)` THEN
    ASM_REWRITE_TAC[LE_ADD_LCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `x * n + n = (x + 1) * n`] THEN
    ASM_SIMP_TAC[SUB_ADD; DIMINDEX_FINITE_PROD] THEN
    ASM_SIMP_TAC[LE_MULT_RCANCEL; DIMINDEX_GE_1];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[] THEN BINOP_TAC THENL
   [AP_TERM_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `1 <= i /\ j = i - 1 ==> 1 + j = i`) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j - 1` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i - 1` THEN ASM_ARITH_TAC]);;

let FORALL_VECTORIZE = prove
 (`!P. (!x. P x) <=> (!x. P(vectorize x))`,
  MESON_TAC[MATRIFY_VECTORIZE; VECTORIZE_MATRIFY]);;

let FORALL_MATRIFY = prove
 (`!P. (!x. P x) <=> (!x. P(matrify x))`,
  MESON_TAC[MATRIFY_VECTORIZE; VECTORIZE_MATRIFY]);;

let EXISTS_VECTORIZE = prove
 (`!P. (?x. P x) <=> (?x. P(vectorize x))`,
  MESON_TAC[MATRIFY_VECTORIZE; VECTORIZE_MATRIFY]);;

let EXISTS_MATRIFY = prove
 (`!P. (?x. P x) <=> (?x. P(matrify x))`,
  MESON_TAC[MATRIFY_VECTORIZE; VECTORIZE_MATRIFY]);;

let VECTORIZE_GSPEC = prove
 (`!P:A^N^M->bool. {vectorize m | P m} = {v | P(matrify v)}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[VECTORIZE_MATRIFY; MATRIFY_VECTORIZE]);;

let VECTORIZE_EQ = prove
 (`!m1 m2:real^N^M. vectorize m1 = vectorize m2 <=> m1 = m2`,
  MESON_TAC[MATRIFY_VECTORIZE]);;

let MATRIFY_EQ = prove
 (`!m1 m2:real^(M,N)finite_prod. matrify m1 = matrify m2 <=> m1 = m2`,
  MESON_TAC[VECTORIZE_MATRIFY]);;

(* ------------------------------------------------------------------------- *)
(* A generic notion of "hull" (convex, affine, conic hull and closure).      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("hull",(21,"left"));;

let hull = new_definition
  `P hull s = INTERS {t | P t /\ s SUBSET t}`;;

let HULL_P = prove
 (`!P s. P s ==> (P hull s = s)`,
  REWRITE_TAC[hull; EXTENSION; IN_INTERS; IN_ELIM_THM] THEN
  MESON_TAC[SUBSET]);;

let P_HULL = prove
 (`!P s. (!f. (!s. s IN f ==> P s) ==> P(INTERS f)) ==> P(P hull s)`,
  REWRITE_TAC[hull] THEN SIMP_TAC[IN_ELIM_THM]);;

let HULL_EQ = prove
 (`!P s. (!f. (!s. s IN f ==> P s) ==> P(INTERS f))
         ==> ((P hull s = s) <=> P s)`,
  MESON_TAC[P_HULL; HULL_P]);;

let HULL_HULL = prove
 (`!P s. P hull (P hull s) = P hull s`,
  REWRITE_TAC[hull; EXTENSION; IN_INTERS; IN_ELIM_THM; SUBSET] THEN
  MESON_TAC[]);;

let HULL_SUBSET = prove
 (`!P s. s SUBSET (P hull s)`,
  REWRITE_TAC[hull; SUBSET; IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

let HULL_MONO = prove
 (`!P s t. s SUBSET t ==> (P hull s) SUBSET (P hull t)`,
   REWRITE_TAC[hull; SUBSET; IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

let HULL_ANTIMONO = prove
 (`!P Q s. P SUBSET Q ==> (Q hull s) SUBSET (P hull s)`,
  REWRITE_TAC[SUBSET; hull; IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[IN]);;

let HULL_UNIV = prove
 (`!P:(A->bool)->bool. P hull UNIV = UNIV`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIV; HULL_SUBSET]);;

let HULL_MINIMAL = prove
 (`!P s t. s SUBSET t /\ P t ==> (P hull s) SUBSET t`,
  REWRITE_TAC[hull; SUBSET; IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

let SUBSET_HULL = prove
 (`!P s t. P t ==> ((P hull s) SUBSET t <=> s SUBSET t)`,
  REWRITE_TAC[hull; SUBSET; IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

let HULL_UNIQUE = prove
 (`!P s t. s SUBSET t /\ P t /\ (!t'. s SUBSET t' /\ P t' ==> t SUBSET t')
           ==> (P hull s = t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[hull; SUBSET; IN_INTERS; IN_ELIM_THM] THEN
  ASM_MESON_TAC[SUBSET_HULL; SUBSET]);;

let HULL_UNION_SUBSET = prove
 (`!P s t. (P hull s) UNION (P hull t) SUBSET (P hull (s UNION t))`,
  SIMP_TAC[UNION_SUBSET; HULL_MONO; SUBSET_UNION]);;

let HULL_UNION = prove
 (`!P s t. P hull (s UNION t) = P hull (P hull s UNION P hull t)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; UNION_SUBSET] THEN
  MESON_TAC[SUBSET_HULL]);;

let HULL_UNION_LEFT = prove
 (`!P s t:A->bool.
        P hull (s UNION t) = P hull (P hull s UNION t)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; UNION_SUBSET] THEN
  MESON_TAC[SUBSET_HULL]);;

let HULL_UNION_RIGHT = prove
 (`!P s t:A->bool.
        P hull (s UNION t) = P hull (s UNION P hull t)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; UNION_SUBSET] THEN
  MESON_TAC[SUBSET_HULL]);;

let HULL_INSERT = prove
 (`!P a s. P hull (a INSERT s) = P hull (a INSERT P hull s)`,
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  ONCE_REWRITE_TAC[HULL_UNION] THEN REWRITE_TAC[HULL_HULL]);;

let HULL_REDUNDANT_EQ = prove
 (`!P a s. a IN (P hull s) <=> (P hull (a INSERT s) = P hull s)`,
  REWRITE_TAC[hull] THEN SET_TAC[]);;

let HULL_REDUNDANT = prove
 (`!P a s. a IN (P hull s) ==> (P hull (a INSERT s) = P hull s)`,
  REWRITE_TAC[HULL_REDUNDANT_EQ]);;

let HULL_INDUCT = prove
 (`!P p s. (!x:A. x IN s ==> p x) /\ P {x | p x}
           ==> !x. x IN P hull s ==> p x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`P:(A->bool)->bool`; `s:A->bool`; `{x:A | p x}`]
                HULL_MINIMAL) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM]);;

let HULL_INC = prove
 (`!P s x. x IN s ==> x IN P hull s`,
  MESON_TAC[REWRITE_RULE[SUBSET] HULL_SUBSET]);;

let HULL_IMAGE_SUBSET = prove
 (`!P f s. P(P hull s) /\ (!s. P s ==> P(IMAGE f s))
           ==> P hull (IMAGE f s) SUBSET (IMAGE f (P hull s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; HULL_SUBSET]);;

let HULL_IMAGE_GALOIS = prove
 (`!P f g s. (!s. P(P hull s)) /\
             (!s. P s ==> P(IMAGE f s)) /\ (!s. P s ==> P(IMAGE g s)) /\
             (!s t. s SUBSET IMAGE g t <=> IMAGE f s SUBSET t)
             ==> P hull (IMAGE f s) = IMAGE f (P hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[HULL_IMAGE_SUBSET] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC[HULL_SUBSET]);;

let HULL_IMAGE = prove
 (`!P f s. (!s. P(P hull s)) /\ (!s. P(IMAGE f s) <=> P s) /\
           (!x y:A. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> P hull (IMAGE f s) = IMAGE f (P hull s)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[BIJECTIVE_LEFT_RIGHT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A->A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HULL_IMAGE_GALOIS THEN EXISTS_TAC `g:A->A` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  X_GEN_TAC `s:A->bool` THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let IS_HULL = prove
 (`!P s. (!f. (!s. s IN f ==> P s) ==> P(INTERS f))
         ==> (P s <=> ?t. s = P hull t)`,
  MESON_TAC[HULL_P; P_HULL]);;

let HULLS_EQ = prove
 (`!P s t.
        (!f. (!s. s IN f ==> P s) ==> P (INTERS f)) /\
        s SUBSET P hull t /\ t SUBSET P hull s
        ==> P hull s = P hull t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC[P_HULL]);;

let HULL_P_AND_Q = prove
 (`!P Q. (!f. (!s. s IN f ==> P s) ==> P(INTERS f)) /\
         (!f. (!s. s IN f ==> Q s) ==> Q(INTERS f)) /\
         (!s. Q s ==> Q(P hull s))
         ==> (\x. P x /\ Q x) hull s = P hull (Q hull s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HULL_UNIQUE THEN ASM_SIMP_TAC[HULL_INC; SUBSET_HULL] THEN
  ASM_MESON_TAC[P_HULL; HULL_SUBSET; SUBSET_TRANS]);;

let HULL_UNIONS_SUBSET = prove
 (`!P f. UNIONS {P hull s | s IN f} SUBSET P hull (UNIONS f)`,
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let HULL_INTERS_SUBSET = prove
 (`!P f. P hull (INTERS f) SUBSET INTERS {P hull s | s IN f}`,
  REWRITE_TAC[SUBSET_INTERS; FORALL_IN_GSPEC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let HULL_INTER_SUBSET = prove
 (`!P s t. P hull (s INTER t) SUBSET (P hull s) INTER (P hull t)`,
  REWRITE_TAC[hull; INTERS_GSPEC] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Handy lemmas switching between versions of limit arguments.               *)
(* ------------------------------------------------------------------------- *)

let FORALL_POS_MONO = prove
 (`!P. (!d e. d < e /\ P d ==> P e) /\ (!n. ~(n = 0) ==> P(inv(&n)))
       ==> !e. &0 < e ==> P e`,
  MESON_TAC[REAL_ARCH_INV; REAL_LT_TRANS]);;

let FORALL_POS_MONO_1 = prove
 (`!P. (!d e. d < e /\ P d ==> P e) /\ (!n. P(inv(&n + &1)))
       ==> !e. &0 < e ==> P e`,
  REWRITE_TAC[REAL_OF_NUM_SUC; GSYM FORALL_SUC; FORALL_POS_MONO]);;

let FORALL_POS_MONO_EQ = prove
 (`!P. (!d e. d < e /\ P d ==> P e)
       ==> ((!e. &0 < e ==> P e) <=> (!n. ~(n = 0) ==> P(inv(&n))))`,
  MESON_TAC[REAL_ARCH_INV; REAL_LT_INV_EQ; REAL_LT_TRANS; LE_1;
            REAL_OF_NUM_LT]);;

let FORALL_POS_MONO_1_EQ = prove
 (`!P. (!d e. d < e /\ P d ==> P e)
       ==> ((!e. &0 < e ==> P e) <=> (!n. P(inv(&n + &1))))`,
  GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP FORALL_POS_MONO_EQ) THEN
  REWRITE_TAC[REAL_OF_NUM_SUC; GSYM FORALL_SUC]);;

let REAL_ARCH_RDIV_EQ_0 = prove
 (`!x c. &0 <= x /\ &0 <= c /\ (!m. 0 < m ==> &m * x <= c) ==> x = &0`,
  SIMP_TAC [GSYM REAL_LE_ANTISYM; GSYM REAL_NOT_LT] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (STRIP_ASSUME_TAC o SPEC `c:real` o MATCH_MP REAL_ARCH) THEN
  ASM_CASES_TAC `n=0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_MUL_LZERO]) THEN
    ASM_MESON_TAC [REAL_LET_ANTISYM];
    ASM_MESON_TAC [REAL_LET_ANTISYM; REAL_MUL_SYM; LT_NZ]]);;

(* ------------------------------------------------------------------------- *)
(* A slightly sharper indexing lemma.                                        *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDEX_NUMSEG_SPECIAL = prove
 (`!s a:A.
        FINITE s /\ a IN s
        ==> ?f. (!i j. i IN 1..CARD s /\ j IN 1..CARD s /\ f i = f j
                       ==> i = j) /\
                s = IMAGE f (1..CARD s) /\
                f 1 = a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k. k IN 1..CARD(s:A->bool) /\ (a:A) = f k`
  STRIP_ASSUME_TAC THENL[ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC
   `(f:num->A) o (\j. if j = 1 then k else if j = k then 1 else j)` THEN
  SUBGOAL_THEN `1 IN 1..CARD(s:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0; ARITH_EQ] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_THEN `s = IMAGE (f:num->A) (1..CARD(s:A->bool))`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
  X_GEN_TAC `b:A` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `if i = 1 then k else if i = k then 1 else i` THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Geometric progression.                                                    *)
(* ------------------------------------------------------------------------- *)

let SUM_GP_BASIC = prove
 (`!x n. (&1 - x) * sum(0..n) (\i. x pow i) = &1 - x pow (SUC n)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID; LE_0] THEN
  ASM_REWRITE_TAC[REAL_ADD_LDISTRIB; real_pow] THEN REAL_ARITH_TAC);;

let SUM_GP_MULTIPLIED = prove
 (`!x m n. m <= n
           ==> ((&1 - x) * sum(m..n) (\i. x pow i) = x pow m - x pow (SUC n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC
   [SUM_OFFSET_0; REAL_POW_ADD; REAL_MUL_ASSOC; SUM_GP_BASIC; SUM_RMUL] THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; GSYM REAL_POW_ADD; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> (SUC(n - m) + m = SUC n)`]);;

let SUM_GP = prove
 (`!x m n.
        sum(m..n) (\i. x pow i) =
                if n < m then &0
                else if x = &1 then &((n + 1) - m)
                else (x pow m - x pow (SUC n)) / (&1 - x)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `n < m \/ ~(n < m) /\ m <= n:num`) THEN
  ASM_SIMP_TAC[SUM_TRIV_NUMSEG] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_ONE; SUM_CONST_NUMSEG; REAL_MUL_RID]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `&1 - x` THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_SUB_0; SUM_GP_MULTIPLIED]);;

let SUM_GP_OFFSET = prove
 (`!x m n. sum(m..m+n) (\i. x pow i) =
                if x = &1 then &n + &1
                else x pow m * (&1 - x pow (SUC n)) / (&1 - x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUM_GP; ARITH_RULE `~(m + n < m:num)`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[real_div; real_pow; REAL_POW_ADD] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Segment of natural numbers starting at a specific number.                 *)
(* ------------------------------------------------------------------------- *)

let from = new_definition
  `from n = {m:num | n <= m}`;;

let FROM_0 = prove
 (`from 0 = (:num)`,
  REWRITE_TAC[from; LE_0] THEN SET_TAC[]);;

let IN_FROM = prove
 (`!m n. m IN from n <=> n <= m`,
  REWRITE_TAC[from; IN_ELIM_THM]);;

let FROM_MONO = prove
 (`!m n. from m SUBSET from n <=> n <= m`,
  REWRITE_TAC[SUBSET; IN_FROM] THEN MESON_TAC[LE_TRANS; LE_REFL]);;

let FROM_INTER_NUMSEG_GEN = prove
 (`!k m n. (from k) INTER (m..n) = (if m < k then k..n else m..n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[from; IN_ELIM_THM; IN_INTER; IN_NUMSEG; EXTENSION] THEN
  ARITH_TAC);;

let FROM_INTER_NUMSEG_MAX = prove
 (`!m n p. from p INTER (m..n) = (MAX p m..n)`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG; IN_FROM] THEN ARITH_TAC);;

let FROM_INTER_NUMSEG = prove
 (`!k n. (from k) INTER (0..n) = k..n`,
  REWRITE_TAC[from; IN_ELIM_THM; IN_INTER; IN_NUMSEG; EXTENSION] THEN
  ARITH_TAC);;

let INFINITE_FROM = prove
 (`!n. INFINITE(from n)`,
  GEN_TAC THEN
  SUBGOAL_THEN `from n = (:num) DIFF {i | i < n}`
   (fun th -> SIMP_TAC[th; INFINITE_DIFF_FINITE; FINITE_NUMSEG_LT;
   num_INFINITE]) THEN
  REWRITE_TAC[EXTENSION; from; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN ARITH_TAC);;

let FINITE_INTER_NUMSEG = prove
 (`!s m n. FINITE(s INTER (m..n))`,
  MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG; INTER_SUBSET]);;

let FROM_NONEMPTY = prove
 (`!n. ~(from n = {})`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_FROM; NOT_IN_EMPTY] THEN
  MESON_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Make a Horner-style evaluation of sum(m..n) (\k. a(k) * x pow k).         *)
(* ------------------------------------------------------------------------- *)

let HORNER_SUM_CONV =
  let horner_0,horner_s = (CONJ_PAIR o prove)
   (`(sum(0..0) (\i. c(i) * x pow i) = c 0) /\
     (sum(0..SUC n) (\i. c(i) * x pow i) =
      c(0) + x * sum(0..n) (\i. c(i+1) * x pow i))`,
    REWRITE_TAC[CONJUNCT1 SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * c * y:real = c * x * y`] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow); ADD1] THEN
    REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET)] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; real_pow; REAL_MUL_RID]) in
  let conv_0 = GEN_REWRITE_CONV I [horner_0] THENC NUM_REDUCE_CONV
  and conv_s = LAND_CONV(RAND_CONV(num_CONV)) THENC
               GEN_REWRITE_CONV I [horner_s] THENC
               GEN_REWRITE_CONV ONCE_DEPTH_CONV [LEFT_ADD_DISTRIB] THENC
               GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM ADD_ASSOC] THENC
               NUM_REDUCE_CONV in
  let rec conv tm =
    try (conv_0 THENC REAL_RAT_REDUCE_CONV) tm with Failure _ ->
    (conv_s THENC RAND_CONV(RAND_CONV conv) THENC REAL_RAT_REDUCE_CONV) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Some general lemmas about subsequences.                                   *)
(* ------------------------------------------------------------------------- *)

let SUBSEQUENCE_STEPWISE = prove
 (`!r:num->num. (!m n. m < n ==> r m < r n) <=> (!n. r n < r(SUC n))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[ARITH_RULE `n < SUC n`] THEN
  DISCH_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let SUBSEQUENCE_IMP_INJECTIVE = prove
 (`!r:num->num. (!m n. m < n ==> r m < r n) ==> (!m n. r m = r n <=> m = n)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WLOG_LT THEN
  ASM_MESON_TAC[LT_REFL]);;

let MONOTONE_BIGGER = prove
 (`!r. (!m n. m < n ==> r(m) < r(n)) ==> !n:num. n <= r(n)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_MESON_TAC[LE_0; ARITH_RULE `n <= m /\ m < p ==> SUC n <= p`; LT]);;

let INFINITE_ENUMERATE_WEAK = prove
 (`!s:num->bool.
       INFINITE s
       ==> ?r:num->num. (!m n. m < n ==> r(m) < r(n)) /\ (!n. r n IN s)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_ENUMERATE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

let INFINITE_ENUMERATE_EQ_ALT = prove
 (`!s:num->bool.
        INFINITE s <=> ?r. (!m n:num. m < n ==> r m < r n) /\ (!n. r n IN s)`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[INFINITE_ENUMERATE_WEAK] THEN
  STRIP_TAC THEN MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC `IMAGE (r:num->num) (:num)` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC INFINITE_IMAGE THEN
  REWRITE_TAC[num_INFINITE; IN_UNIV] THEN
  ASM_MESON_TAC[SUBSEQUENCE_IMP_INJECTIVE]);;

let MONOTONE_SUBSEQUENCE = prove
 (`!s:num->real. ?r:num->num.
           (!m n. m < n ==> r(m) < r(n)) /\
           ((!m n. m <= n ==> s(r(m)) <= s(r(n))) \/
            (!m n. m <= n ==> s(r(n)) <= s(r(m))))`,
  GEN_TAC THEN
  ASM_CASES_TAC `!n:num. ?p. n < p /\ !m. p <= m ==> s(m) <= s(p)` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[RIGHT_OR_EXISTS_THM; SKOLEM_THM; REAL_NOT_LE; REAL_NOT_LT] THENL
   [ABBREV_TAC `N = 0`; DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC)] THEN
  DISCH_THEN(X_CHOOSE_THEN `next:num->num` STRIP_ASSUME_TAC) THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(r 0 = next(SUC N)) /\ (!n. r(SUC n) = next(r n))` THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `!m:num n:num. r n <= m ==> s(m) <= s(r n):real`
    ASSUME_TAC THEN TRY CONJ_TAC THEN TRY DISJ2_TAC THEN
    GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT; LE] THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL; LT_IMP_LE; LT_TRANS];
    SUBGOAL_THEN `!n. N < (r:num->num) n` ASSUME_TAC THEN
    TRY(CONJ_TAC THENL [GEN_TAC; DISJ1_TAC THEN GEN_TAC]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[LT; LE] THEN
    TRY STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_LT_REFL; LT_LE; LTE_TRANS; REAL_LE_REFL;
                  REAL_LT_LE; REAL_LE_TRANS; LT]]);;

let CONVERGENT_BOUNDED_INCREASING = prove
 (`!s:num->real b. (!m n. m <= n ==> s m <= s n) /\ (!n. abs(s n) <= b)
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\x. ?n. (s:num->real) n = x` REAL_COMPLETE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `abs(x) <= b ==> x <= b`]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l - e`) THEN
  ASM_MESON_TAC[REAL_ARITH `&0 < e ==> ~(l <= l - e)`;
      REAL_ARITH `x <= y /\ y <= l /\ ~(x <= l - e) ==> abs(y - l) < e`]);;

let CONVERGENT_BOUNDED_MONOTONE = prove
 (`!s:num->real b. (!n. abs(s n) <= b) /\
                   ((!m n. m <= n ==> s m <= s n) \/
                    (!m n. m <= n ==> s n <= s m))
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CONVERGENT_BOUNDED_INCREASING]; ALL_TAC] THEN
  MP_TAC(SPEC `\n. --((s:num->real) n)` CONVERGENT_BOUNDED_INCREASING) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_ABS_NEG] THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - --l) = abs(--x - l)`]);;

(* ------------------------------------------------------------------------- *)
(* A characterization of monotonicity.                                       *)
(* ------------------------------------------------------------------------- *)

let REAL_NON_MONOTONE = prove
 (`!P f:real->real.
        (!x y. P x /\ P y /\ x <= y ==> f x <= f y) \/
        (!x y. P x /\ P y /\ x <= y ==> f y <= f x) <=>
        ~(?x y z. P x /\ P y /\ P z /\ x < y /\ y < z /\
                 (f x < f y /\ f z < f y \/ f y < f x /\ f y < f z))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[REAL_LT_IMP_LE; REAL_LET_ANTISYM]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP; DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; REAL_NOT_LE; MESON[REAL_LT_LE]
   `(x <= y /\ (f:real->real) y < f x <=> x < y /\ f y < f x) /\
    (x <= y /\ f x < f y <=> x < y /\ f x < f y)`] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:real`; `z:real`] THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
   `u:real = w \/ u < w \/ w < u`)
  THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(MESON[] `P w v z \/ P w z v ==> ?x y z. P x y z`);
    MATCH_MP_TAC(MESON[] `P u v \/ P u w \/ P u z ==> ?x y. P x y`) THEN
    ASM_REWRITE_TAC[OR_EXISTS_THM; REAL_LT_REFL] THEN
    MATCH_MP_TAC(MESON[] `P(v:real) \/ P z ==> ?x. P x`);
    MATCH_MP_TAC(MESON[] `P w u \/ P w v \/ P w z ==> ?x y. P x y`) THEN
    ASM_REWRITE_TAC[OR_EXISTS_THM; REAL_LT_REFL] THEN
    MATCH_MP_TAC(MESON[] `P(v:real) \/ P z ==> ?x. P x`)] THEN
  ASM_SIMP_TAC[REAL_LT_REFL; REAL_ARITH `a < b ==> ~(b < a)`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  CONV_TAC NNFC_CONV THEN CONV_TAC CNF_CONV THEN
  REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
  ASM_CASES_TAC `u:real = w` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  ASM_CASES_TAC `u:real = z` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  ASM_CASES_TAC `v:real = w` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  ASM_CASES_TAC `v:real = z` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A generic form of the argument "pick a subsequence satisfying P_0,        *)
(* then a subsequence of that satisfying P_1, then a subsequece of that..."  *)
(* ------------------------------------------------------------------------- *)

let SUBSEQUENCE_DIAGONALIZATION_LEMMA = prove
 (`!P:num->(num->A)->bool.
    (!i r:num->A. ?k. (!m n. m < n ==> k m < k n) /\ P i (r o k)) /\
    (!i r:num->A k1 k2 N.
        P i (r o k1) /\ (!j. N <= j ==> ?j'. j <= j' /\ k2 j = k1 j')
        ==> P i (r o k2))
    ==> !r:num->A. ?k. (!m n. m < n ==> k m < k n) /\ (!i. P i (r o k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [SKOLEM_THM] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT
   `(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)`] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `kk:num->(num->A)->num->num` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `r:num->A` THEN
  (STRIP_ASSUME_TAC o prove_recursive_functions_exist num_RECURSION)
    `(rr 0 = (kk:num->(num->A)->num->num) 0 r) /\
     (!n. rr(SUC n) = rr n o kk (SUC n) (r o rr n))` THEN
  EXISTS_TAC `\n. (rr:num->num->num) n n` THEN REWRITE_TAC[ETA_AX] THEN
  SUBGOAL_THEN
   `(!i. (!m n. m < n ==> (rr:num->num->num) i m < rr i n)) /\
    (!i. (P:num->(num->A)->bool) i (r o rr i))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[AND_FORALL_THM] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[o_ASSOC] THEN
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j n. i <= j ==> (rr:num->num->num) i n <= rr j n`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN SPEC_TAC(`j:num`,`j:num`) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN SIMP_TAC[FORALL_UNWIND_THM2] THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] LE_TRANS)) THEN REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (MESON[LE_LT]
       `!f:num->num.
        (!m n. m < n ==> f m < f n) ==> (!m n. m <= n ==> f m <= f n)`) o
       SPEC `i + d:num`) THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `(rr:num->num->num) n m` THEN
    ASM_MESON_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n i. n <= m ==> ?j. i <= j /\ (rr:num->num->num) m i = rr n j`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `i:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(rr:num->num->num) i` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i:num` THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN
   `!p d i. ?j. i <= j /\ (rr:num->num->num) (p + d) i = rr p j`
   (fun th -> MESON_TAC[LE_EXISTS; th]) THEN
  X_GEN_TAC `p:num` THEN  MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
   [MESON_TAC[LE_REFL]; ALL_TAC] THEN
  X_GEN_TAC `d:num` THEN DISCH_THEN(LABEL_TAC "+") THEN
  X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[o_THM] THEN
  REMOVE_THEN "+" (MP_TAC o SPEC
   `(kk:num->(num->A)->num->num) (SUC(p + d))
        ((r:num->A) o (rr:num->num->num) (p + d)) i`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
  SPEC_TAC(`i:num`,`i:num`) THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
  ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Countability of some relevant sets.                                       *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_INTEGER = prove
 (`COUNTABLE integer`,
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC
   `IMAGE (\n. (&n:real)) (:num) UNION IMAGE (\n. --(&n)) (:num)` THEN
  SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_UNION; NUM_COUNTABLE] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[IN; INTEGER_CASES]);;

let CARD_EQ_INTEGER = prove
 (`integer =_c (:num)`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM; GSYM COUNTABLE_ALT; COUNTABLE_INTEGER] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC `real_of_num` THEN
  REWRITE_TAC[IN_UNIV; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[IN; INTEGER_CLOSED]);;

let COUNTABLE_RATIONAL = prove
 (`COUNTABLE rational`,
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(x,y). x / y) (integer CROSS integer)` THEN
  SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_CROSS; COUNTABLE_INTEGER] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[rational; IN] THEN MESON_TAC[]);;

let CARD_EQ_RATIONAL = prove
 (`rational =_c (:num)`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM; GSYM COUNTABLE_ALT; COUNTABLE_RATIONAL] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC `real_of_num` THEN
  REWRITE_TAC[IN_UNIV; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[IN; RATIONAL_CLOSED]);;

let COUNTABLE_INTEGER_COORDINATES = prove
 (`COUNTABLE { x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }`,
  MATCH_MP_TAC COUNTABLE_CART THEN
  REWRITE_TAC[SET_RULE `{x | P x} = P`; COUNTABLE_INTEGER]);;

let COUNTABLE_RATIONAL_COORDINATES = prove
 (`COUNTABLE { x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }`,
  MATCH_MP_TAC COUNTABLE_CART THEN
  REWRITE_TAC[SET_RULE `{x | P x} = P`; COUNTABLE_RATIONAL]);;

(* ------------------------------------------------------------------------- *)
(* Natural "irrational" variants of rational approximations.                 *)
(* ------------------------------------------------------------------------- *)

let IRRATIONAL_APPROXIMATION = prove
 (`!x e. &0 < e ==> ?y. ~(rational y) /\ abs(y - x) < e`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `?z. ~rational z` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s = (:real)) ==> ?z. ~s z`) THEN
    MESON_TAC[COUNTABLE_RATIONAL; UNCOUNTABLE_REAL];
    MP_TAC(ISPECL [`z + x:real`; `e:real`] RATIONAL_APPROXIMATION) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `q:real` THEN STRIP_TAC THEN EXISTS_TAC `q - z:real` THEN
    ASM_REWRITE_TAC[REAL_ARITH `q - z - x:real = q - (z + x)`] THEN
    DISCH_TAC THEN UNDISCH_TAC `~rational z` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[RATIONAL_CLOSED; REAL_ARITH `z:real = q - (q - z)`]]);;

let IRRATIONAL_BETWEEN = prove
 (`!a b. a < b ==> ?q. ~rational q /\ a < q /\ q < b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(a + b) / &2`; `(b - a) / &4`] IRRATIONAL_APPROXIMATION) THEN
  ANTS_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]] THEN
  ASM_REAL_ARITH_TAC);;

let IRRATIONAL_BETWEEN_EQ = prove
 (`!a b. (?q. ~rational q /\ a < q /\ q < b) <=> a < b`,
  MESON_TAC[IRRATIONAL_BETWEEN; REAL_LT_TRANS]);;

let IRRATIONAL_APPROXIMATION_STRADDLE = prove
 (`!x e. &0 < e
         ==> ?a b. ~rational a /\ ~rational b /\
                   a < x /\ x < b /\ abs(b - a) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x - e / &4`; `e / &4`] IRRATIONAL_APPROXIMATION) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`x + e / &4`; `e / &4`] IRRATIONAL_APPROXIMATION) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let IRRATIONAL_APPROXIMATION_ABOVE = prove
 (`!x e. &0 < e ==> ?q. ~rational q /\ x < q /\ q < x + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `e:real`] IRRATIONAL_APPROXIMATION_STRADDLE) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let IRRATIONAL_APPROXIMATION_BELOW = prove
 (`!x e. &0 < e ==> ?q. ~rational q /\ x - e < q /\ q < x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `e:real`] IRRATIONAL_APPROXIMATION_STRADDLE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let INFINITE_IRRATIONAL_IN_RANGE = prove
 (`!a b. a < b ==> INFINITE {q | ~rational q /\ a < q /\ q < b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?q. (!n. ~rational(q n) /\ a < q n /\ q n < b) /\ (!n. q(SUC n) < q n)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM REAL_LT_MIN] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IRRATIONAL_BETWEEN THEN
    ASM_REWRITE_TAC[REAL_LT_MIN];
    MATCH_MP_TAC INFINITE_SUPERSET THEN
    EXISTS_TAC `IMAGE (q:num->real) (:num)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC INFINITE_IMAGE THEN REWRITE_TAC[num_INFINITE; IN_UNIV] THEN
    SUBGOAL_THEN `!m n. m < n ==> (q:num->real) n < q m`
     (fun th -> MESON_TAC[LT_CASES; th; REAL_LT_REFL]) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
    ASM_MESON_TAC[REAL_LT_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* Countability of extrema for arbitrary function R->R.                      *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_LOCAL_MAXIMA = prove
 (`!f:real->real.
    COUNTABLE {f x |x| ?d. &0 < d /\ !x'. abs(x' - x) < d ==> f(x') <= f(x)}`,
  GEN_TAC THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\(a,b). sup {f x | a <= x /\ x <= b})
          ((rational CROSS rational) INTER
           {(a,b) | ?x. a < x /\ x < b /\
                        !x'. a <= x' /\ x' <= b ==> f x' <= f x})` THEN
  SIMP_TAC[COUNTABLE_INTER; COUNTABLE_CROSS; COUNTABLE_RATIONAL;
           COUNTABLE_IMAGE; SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER; EXISTS_PAIR_THM] THEN
  MP_TAC(ISPECL [`x:real`; `d:real`] RATIONAL_APPROXIMATION_STRADDLE) THEN
  ASM_REWRITE_TAC[IN_CROSS; IN_ELIM_PAIR_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN] THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_SUP_UNIQUE THEN
    REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN TRY(EXISTS_TAC `x:real`) THEN
  REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_REAL_ARITH_TAC);;

let COUNTABLE_LOCAL_MINIMA = prove
 (`!f:real->real.
    COUNTABLE {f x |x| ?d. &0 < d /\ !x'. abs(x' - x) < d ==> f(x) <= f(x')}`,
  GEN_TAC THEN MP_TAC(SPEC `(--) o (f:real->real)` COUNTABLE_LOCAL_MAXIMA) THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[ETA_AX; IMAGE_o] THEN
  REWRITE_TAC[o_THM; REAL_LE_NEG2] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC COUNTABLE_IMAGE_INJ_EQ THEN SIMP_TAC[REAL_EQ_NEG2]);;

let COUNTABLE_STRICT_LOCAL_MAXIMA = prove
 (`!f:real->real.
    COUNTABLE {x | ?d. &0 < d /\
                       !x'. abs(x' - x) < d /\ ~(x' = x) ==> f(x') < f(x)}`,
  GEN_TAC THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\(a,b). @x. a < x /\ x < b /\
                        !x'. a <= x' /\ x' <= b /\ ~(x' = x)
                             ==> f x' < f x)
          ((rational CROSS rational) INTER
           {(a,b) | ?x. a < x /\ x < b /\
                        !x'. a <= x' /\ x' <= b /\ ~(x' = x)
                             ==> f x' < f x})` THEN
  SIMP_TAC[COUNTABLE_INTER; COUNTABLE_CROSS; COUNTABLE_RATIONAL;
           COUNTABLE_IMAGE; SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER; EXISTS_PAIR_THM] THEN
  MP_TAC(ISPECL [`x:real`; `d:real`] RATIONAL_APPROXIMATION_STRADDLE) THEN
  ASM_REWRITE_TAC[IN_CROSS; IN_ELIM_PAIR_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN] THEN
  MATCH_MP_TAC(MESON[]
   `P x /\ (!x y. P x /\ P y ==> x = y) ==> x = (@y. P y) /\ (?y. P y)`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_LT_ANTISYM; REAL_LT_IMP_LE]]);;

let COUNTABLE_STRICT_LOCAL_MINIMA = prove
 (`!f:real->real.
    COUNTABLE {x | ?d. &0 < d /\
                       !x'. abs(x' - x) < d /\ ~(x' = x) ==> f(x) < f(x')}`,
  GEN_TAC THEN
  MP_TAC(SPEC `(--) o (f:real->real)` COUNTABLE_STRICT_LOCAL_MAXIMA) THEN
   ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[ETA_AX; IMAGE_o] THEN
  REWRITE_TAC[o_THM; REAL_LT_NEG2] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC COUNTABLE_IMAGE_INJ_EQ THEN SIMP_TAC[REAL_EQ_NEG2]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of a function on a set.                                       *)
(* ------------------------------------------------------------------------- *)

let RESTRICTION = new_definition
  `RESTRICTION s (f:A->B) x = if x IN s then f x else ARB`;;

let RESTRICTION_DEFINED = prove
 (`!s f:A->B x. x IN s ==> RESTRICTION s f x = f x`,
  SIMP_TAC[RESTRICTION]);;

let RESTRICTION_UNDEFINED = prove
 (`!s f:A->B x. ~(x IN s) ==> RESTRICTION s f x = ARB`,
  SIMP_TAC[RESTRICTION]);;

let RESTRICTION_EQ = prove
 (`!s f:A->B x y. x IN s /\ f x = y ==> RESTRICTION s f x = y`,
  SIMP_TAC[RESTRICTION_DEFINED]);;

let RESTRICTION_IN_EXTENSIONAL = prove
 (`!s f:A->B. RESTRICTION s f IN EXTENSIONAL s`,
  SIMP_TAC[IN_EXTENSIONAL; RESTRICTION]);;

let RESTRICTION_EXTENSION = prove
 (`!s f g:A->B. RESTRICTION s f = RESTRICTION s g <=>
                (!x. x IN s ==> f x = g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RESTRICTION; FUN_EQ_THM] THEN MESON_TAC[]);;

let RESTRICTION_FIXPOINT = prove
 (`!s f:A->B. RESTRICTION s f = f <=> f IN EXTENSIONAL s`,
  REWRITE_TAC[IN_EXTENSIONAL; FUN_EQ_THM; RESTRICTION] THEN MESON_TAC[]);;

let RESTRICTION_RESTRICTION = prove
 (`!s t f:A->B.
        s SUBSET t ==> RESTRICTION s (RESTRICTION t f) = RESTRICTION s f`,
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN SET_TAC[]);;

let RESTRICTION_IDEMP = prove
 (`!s f:A->B. RESTRICTION s (RESTRICTION s f) = RESTRICTION s f`,
  REWRITE_TAC[RESTRICTION_FIXPOINT; RESTRICTION_IN_EXTENSIONAL]);;

let IMAGE_RESTRICTION = prove
 (`!f:A->B s t. s SUBSET t ==> IMAGE (RESTRICTION t f) s = IMAGE f s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; RESTRICTION] THEN SET_TAC[]);;

let RESTRICTION_COMPOSE_RIGHT = prove
 (`!f:A->B g:B->C s.
        RESTRICTION s (g o RESTRICTION s f) =
        RESTRICTION s (g o f)`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; RESTRICTION] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN SET_TAC[]);;

let RESTRICTION_COMPOSE_LEFT = prove
 (`!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o f) =
            RESTRICTION s (g o f)`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; RESTRICTION] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN SET_TAC[]);;

let RESTRICTION_COMPOSE = prove
 (`!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o RESTRICTION s f) =
            RESTRICTION s (g o f)`,
  SIMP_TAC[RESTRICTION_COMPOSE_LEFT; RESTRICTION_COMPOSE_RIGHT]);;

(* ------------------------------------------------------------------------- *)
(* A somewhat cheap but handy way of getting localized forms of various      *)
(* topological concepts (open, closed, borel, fsigma, gdelta etc.)           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("relative_to",(14,"left"));;

let relative_to = define
 `(P relative_to s) t <=> ?u. P u /\ s INTER u = t`;;

let RELATIVE_TO_UNIV = prove
 (`!P s. (P relative_to (:A)) s <=> P s`,
  REWRITE_TAC[relative_to; INTER_UNIV] THEN MESON_TAC[]);;

let RELATIVE_TO_IMP_SUBSET = prove
 (`!P s t. (P relative_to s) t ==> t SUBSET s`,
  REWRITE_TAC[relative_to] THEN SET_TAC[]);;

let FORALL_RELATIVE_TO = prove
 (`(!s. (P relative_to u) s ==> Q s) <=>
   (!s. P s ==> Q(u INTER s))`,
  REWRITE_TAC[relative_to] THEN MESON_TAC[]);;

let RELATIVE_TO_INC = prove
 (`!P u s. P s ==> (P relative_to u) (u INTER s)`,
  REWRITE_TAC[relative_to] THEN MESON_TAC[]);;

let RELATIVE_TO = prove
 (`(P relative_to u) = {u INTER s | P s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
  REWRITE_TAC[relative_to; IN] THEN SET_TAC[]);;

let RELATIVE_TO_RELATIVE_TO = prove
 (`!P:(A->bool)->bool s t.
        P relative_to s relative_to t = P relative_to (s INTER t)`,
  REWRITE_TAC[RELATIVE_TO] THEN
  REWRITE_TAC[SET_RULE `{f x | {g y | P y} x} = {f(g y) | P y}`] THEN
  REWRITE_TAC[SET_RULE `(s INTER t) INTER s' = t INTER s INTER s'`]);;

let RELATIVE_TO_COMPL = prove
 (`!P u s:A->bool.
        s SUBSET u
        ==> ((P relative_to u) (u DIFF s) <=>
             ((\c. P(UNIV DIFF c)) relative_to u) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_to] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM EXISTS_DIFF] THEN
  REWRITE_TAC[COMPL_COMPL] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM SET_TAC[]);;

let RELATIVE_TO_SUBSET = prove
 (`!P s t:A->bool. s SUBSET t /\ P s ==> (P relative_to t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_to] THEN
  EXISTS_TAC `s:A->bool` THEN ASM SET_TAC[]);;

let RELATIVE_TO_SUBSET_TRANS = prove
 (`!P u s t:A->bool.
      (P relative_to u) s /\ s SUBSET t /\ t SUBSET u ==> (P relative_to t) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[relative_to] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let RELATIVE_TO_MONO = prove
 (`!P Q.
     (!s. P s ==> Q s) ==> !u. (P relative_to u) s ==> (Q relative_to u) s`,
  REWRITE_TAC[relative_to] THEN MESON_TAC[]);;

let RELATIVE_TO_INTER = prove
 (`!P s. (!c d:A->bool. P c /\ P d ==> P(c INTER d))
         ==> !c d. (P relative_to s) c /\ (P relative_to s) d
                   ==> (P relative_to s) (c INTER d)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[relative_to] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `c':A->bool` (STRIP_ASSUME_TAC o GSYM))
   (X_CHOOSE_THEN `d':A->bool` (STRIP_ASSUME_TAC o GSYM))) THEN
  EXISTS_TAC `c' INTER d':A->bool` THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let RELATIVE_TO_UNION = prove
 (`!P s. (!c d:A->bool. P c /\ P d ==> P(c UNION d))
         ==> !c d. (P relative_to s) c /\ (P relative_to s) d
                   ==> (P relative_to s) (c UNION d)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[relative_to] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `c':A->bool` (STRIP_ASSUME_TAC o GSYM))
   (X_CHOOSE_THEN `d':A->bool` (STRIP_ASSUME_TAC o GSYM))) THEN
  EXISTS_TAC `c' UNION d':A->bool` THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let ARBITRARY_UNION_OF_RELATIVE_TO = prove
 (`!P u:A->bool.
        ((ARBITRARY UNION_OF P) relative_to u) =
        (ARBITRARY UNION_OF (P relative_to u))`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_OF; relative_to] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `{u INTER c | (c:A->bool) IN f}` THEN
    ASM_REWRITE_TAC[INTER_UNIONS] THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; ARBITRARY; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:(A->bool)->(A->bool)` THEN STRIP_TAC THEN
    EXISTS_TAC `UNIONS (IMAGE (g:(A->bool)->(A->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    EXISTS_TAC `IMAGE (g:(A->bool)->(A->bool)) f` THEN
    ASM_SIMP_TAC[ARBITRARY; FORALL_IN_IMAGE]]);;

let FINITE_UNION_OF_RELATIVE_TO = prove
 (`!P u:A->bool.
        ((FINITE UNION_OF P) relative_to u) =
        (FINITE UNION_OF (P relative_to u))`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_OF; relative_to] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `{u INTER c | (c:A->bool) IN f}` THEN
    ASM_REWRITE_TAC[INTER_UNIONS] THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:(A->bool)->(A->bool)` THEN STRIP_TAC THEN
    EXISTS_TAC `UNIONS (IMAGE (g:(A->bool)->(A->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    EXISTS_TAC `IMAGE (g:(A->bool)->(A->bool)) f` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE]]);;

let COUNTABLE_UNION_OF_RELATIVE_TO = prove
 (`!P u:A->bool.
        ((COUNTABLE UNION_OF P) relative_to u) =
        (COUNTABLE UNION_OF (P relative_to u))`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_OF; relative_to] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `{u INTER c | (c:A->bool) IN f}` THEN
    ASM_REWRITE_TAC[INTER_UNIONS] THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:(A->bool)->(A->bool)` THEN STRIP_TAC THEN
    EXISTS_TAC `UNIONS (IMAGE (g:(A->bool)->(A->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    EXISTS_TAC `IMAGE (g:(A->bool)->(A->bool)) f` THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE]]);;

let ARBITRARY_INTERSECTION_OF_RELATIVE_TO = prove
 (`!P u:A->bool.
        ((ARBITRARY INTERSECTION_OF P) relative_to u) =
        ((ARBITRARY INTERSECTION_OF (P relative_to u)) relative_to u)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:A->bool` THEN REWRITE_TAC[INTERSECTION_OF; relative_to] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `INTERS {u INTER c | (c:A->bool) IN f}` THEN CONJ_TAC THENL
     [EXISTS_TAC `{u INTER c | (c:A->bool) IN f}` THEN
      ASM_SIMP_TAC[ARBITRARY; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_INTERS] THEN
      REWRITE_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; INTERS_IMAGE; FORALL_IN_IMAGE;
                  SET_RULE `u INTER u INTER s = u INTER s`]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:(A->bool)->(A->bool)` THEN STRIP_TAC THEN
    EXISTS_TAC `INTERS (IMAGE (g:(A->bool)->(A->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    EXISTS_TAC `IMAGE (g:(A->bool)->(A->bool)) f` THEN
    ASM_SIMP_TAC[ARBITRARY; FORALL_IN_IMAGE]]);;

let FINITE_INTERSECTION_OF_RELATIVE_TO = prove
 (`!P u:A->bool.
        ((FINITE INTERSECTION_OF P) relative_to u) =
        ((FINITE INTERSECTION_OF (P relative_to u)) relative_to u)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:A->bool` THEN REWRITE_TAC[INTERSECTION_OF; relative_to] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `INTERS {u INTER c | (c:A->bool) IN f}` THEN CONJ_TAC THENL
     [EXISTS_TAC `{u INTER c | (c:A->bool) IN f}` THEN
      ASM_SIMP_TAC[FINITE_IMAGE; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_INTERS] THEN
      REWRITE_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; INTERS_IMAGE; FORALL_IN_IMAGE;
                  SET_RULE `u INTER u INTER s = u INTER s`]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:(A->bool)->(A->bool)` THEN STRIP_TAC THEN
    EXISTS_TAC `INTERS (IMAGE (g:(A->bool)->(A->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    EXISTS_TAC `IMAGE (g:(A->bool)->(A->bool)) f` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE]]);;

let COUNTABLE_INTERSECTION_OF_RELATIVE_TO = prove
 (`!P u:A->bool.
        ((COUNTABLE INTERSECTION_OF P) relative_to u) =
        ((COUNTABLE INTERSECTION_OF (P relative_to u)) relative_to u)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `s:A->bool` THEN REWRITE_TAC[INTERSECTION_OF; relative_to] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `INTERS {u INTER c | (c:A->bool) IN f}` THEN CONJ_TAC THENL
     [EXISTS_TAC `{u INTER c | (c:A->bool) IN f}` THEN
      ASM_SIMP_TAC[COUNTABLE_IMAGE; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_INTERS] THEN
      REWRITE_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; INTERS_IMAGE; FORALL_IN_IMAGE;
                  SET_RULE `u INTER u INTER s = u INTER s`]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:(A->bool)->(A->bool)` THEN STRIP_TAC THEN
    EXISTS_TAC `INTERS (IMAGE (g:(A->bool)->(A->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    EXISTS_TAC `IMAGE (g:(A->bool)->(A->bool)) f` THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* Reduction theorem used for sigma-sets doesn't really depend on much.      *)
(* Besides, our formulation of "Delta" via "baire" doesn't work for          *)
(* n = 0 so we want to avoid a separate proof for clopen sets.               *)
(* ------------------------------------------------------------------------- *)

let GENERAL_REDUCTION_THEOREM = prove
 (`!P. P {} /\
       (!s t. P s /\ P t ==> P(s UNION t)) /\
       (!s t. P s /\ P t ==> P(s DIFF t))
       ==> !s:num->A->bool.
              (!n. (COUNTABLE UNION_OF P) (s n))
              ==> ?t. (!n. (COUNTABLE UNION_OF P) (t n)) /\
                      (!n. t n SUBSET s n) /\
                      pairwise (\m n. DISJOINT (t m) (t n)) (:num) /\
                      UNIONS {t n | n IN (:num)} = UNIONS {s n | n IN (:num)}`,
  REWRITE_TAC[UNION_OF; o_THM] THEN REPEAT STRIP_TAC THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k:(A->bool)->bool. FINITE k /\ (!i. i IN k ==> P i) ==> P(UNIONS k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c:num->num->A->bool.
        (!n m. P (c n m)) /\
        (!n. UNIONS {c n m | m IN (:num)} = s n)`
  MP_TAC THENL
   [REWRITE_TAC[AND_FORALL_THM; GSYM SKOLEM_THM] THEN
    X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:(A->bool)->bool` MP_TAC) THEN
    ASM_CASES_TAC `u:(A->bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[UNIONS_0] THEN
      DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
      EXISTS_TAC `(\n. {}):num->A->bool` THEN
      ASM_REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPEC `u:(A->bool)->bool` COUNTABLE_AS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [SKOLEM_THM])] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num->A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC CARD_SQUARE_NUM THEN
  REWRITE_TAC[EQ_C_BIJECTIONS; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[mul_c; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num#num->num`; `q:num->num#num`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_UNIV] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `d:num->num->A->bool =
        \m n. c m n DIFF UNIONS {c i j | (p:num#num->num)(i,j) < p(m,n)}` THEN
  EXISTS_TAC `\n. UNIONS { d i j | i,j |
                           (d:num->num->A->bool) i j SUBSET s n /\
                           !m:num. m < n ==> ~(d i j SUBSET s m)}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    EXISTS_TAC `{ d i j | i,j |
                  (d:num->num->A->bool) i j SUBSET s n /\
                  !m:num. m < n ==> ~(d i j SUBSET s m)}` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC
       `{(d:num->num->A->bool) i j | i IN (:num) /\ j IN (:num)}` THEN
      SIMP_TAC[COUNTABLE_PRODUCT_DEPENDENT; COUNTABLE_SUBSET_NUM] THEN
      SET_TAC[];

      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      EXPAND_TAC "d" THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
      SUBGOAL_THEN
       `{(c:num->num->A->bool) k l | (p(k,l):num) < p(i,j)} =
        IMAGE (\r. c (FST(q r)) (SND(q r))) {r | r < p(i,j)}`
       (fun th -> SIMP_TAC[th; FINITE_IMAGE; FINITE_NUMSEG_LT]) THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `v:A->bool` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THEN
      SIMP_TAC[LEFT_IMP_EXISTS_THM] THENL
       [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
        EXISTS_TAC `(p:num#num->num)(a,b)` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `c:num` THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
         [`FST((q:num->num#num) c)`; `SND((q:num->num#num) c)`] THEN
        ASM_REWRITE_TAC[]]];
    ASM SET_TAC[];
    REWRITE_TAC[pairwise] THEN MATCH_MP_TAC WLOG_LT THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN REWRITE_TAC[IN_UNIV] THEN
      BINOP_TAC THENL [MESON_TAC[]; MATCH_ACCEPT_TAC DISJOINT_SYM];
      REWRITE_TAC[IN_UNIV; DISJOINT; INTER_UNIONS]] THEN
    REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p:num#num->num)(a,b) < p(m,n) \/ p(m,n) < p(a,b)`
    MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `m < n \/ n < m <=> ~(m:num = n)`] THEN
      DISCH_THEN(MP_TAC o AP_TERM `q:num->num#num`) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN ASM SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; UNIONS_GSPEC] THEN
      SET_TAC[]];
     GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
     REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
     ONCE_REWRITE_TAC[MESON[] `(?n i j. P n i j) <=> (?i j n. P n i j)`] THEN
     REWRITE_TAC[LEFT_EXISTS_AND_THM; GSYM num_WOP] THEN
     TRANS_TAC EQ_TRANS `?i j. x IN (d:num->num->A->bool) i j` THEN
     CONJ_TAC THENL
      [REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
       MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
       EXPAND_TAC "d" THEN REWRITE_TAC[] THEN ASM SET_TAC[];
       ALL_TAC] THEN
     FIRST_ASSUM(fun t -> GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o RAND_CONV)
        [GSYM t]) THEN
     REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN MATCH_MP_TAC(MESON[]
      `!p:num#num->num.
           (P <=> ?n i j. p(i,j) = n /\ Q i j) ==> (P <=> ?i j. Q i j)`) THEN
     EXISTS_TAC `p:num#num->num` THEN
     GEN_REWRITE_TAC RAND_CONV [num_WOP] THEN
     EXPAND_TAC "d" THEN REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
     MESON_TAC[]]);;

let GENERAL_REDUCTION_THEOREM_2 = prove
 (`!P. P {} /\
       (!s t:A->bool. P s /\ P t ==> P(s UNION t)) /\
       (!s t. P s /\ P t ==> P(s DIFF t))
       ==> !s t. (COUNTABLE UNION_OF P) s /\ (COUNTABLE UNION_OF P) t
                 ==> ?s' t'. (COUNTABLE UNION_OF P) s' /\
                             (COUNTABLE UNION_OF P) t' /\
                             s' SUBSET s /\ t' SUBSET t /\ DISJOINT s' t' /\
                             s' UNION t' = s UNION t`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o
   ISPEC `\n. if n = 0 then s:A->bool else if n = 1 then t else {}` o
   MATCH_MP GENERAL_REDUCTION_THEOREM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_SIMP_TAC[COUNTABLE_UNION_OF_INC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->A->bool` MP_TAC) THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP
   (MESON[] `(!n. P n) ==> P 0 /\ P 1`)) THEN
  ONCE_REWRITE_TAC[MESON[]
   `(!n. P n) <=> P 0 /\ P 1 /\ (!n. ~(n = 0) /\ ~(n = 1) ==> P n)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[SUBSET_EMPTY] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `(:num) = 0 INSERT 1 INSERT ((:num) DIFF {0,1})`] THEN
  SIMP_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT; PAIRWISE_INSERT] THEN
  DISCH_THEN(MP_TAC o SPEC `1` o CONJUNCT1) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `s UNION t UNION u = s' UNION t' UNION u'
    ==> u = {} /\ u' = {} ==> s UNION t = s' UNION t'`)) THEN
  REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_IMAGE; IN_UNIV; IN_DIFF] THEN
  ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A somewhat general formulation of "back and forth" arguments.             *)
(* ------------------------------------------------------------------------- *)

let BACK_AND_FORTH_ALT = prove
 (`!P s:A->bool t:B->bool.
    COUNTABLE s /\ COUNTABLE t /\
    (!R. FINITE R /\ R SUBSET s CROSS t /\ pairwise P R
         ==> (!x. x IN s ==> ?y. y IN t /\ pairwise P ((x,y) INSERT R)) /\
             (!y. y IN t ==> ?x. x IN s /\ pairwise P ((x,y) INSERT R)))
    ==> ?R. R SUBSET s CROSS t /\ pairwise P R /\
            (!x. x IN s ==> ?y. y IN t /\ (x,y) IN R) /\
            (!y. y IN t ==> ?x. x IN s /\ (x,y) IN R)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?x:num->A. ?y:num->B. s SUBSET IMAGE x (:num) /\ t SUBSET IMAGE y (:num)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COUNTABLE_AS_IMAGE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?R:num->A#B->bool.
        (!n. FINITE(R n) /\ (R n) SUBSET s CROSS t /\ pairwise P (R n) /\
             (x n IN s ==> x n IN IMAGE FST(R n)) /\
             (y n IN t ==> y n IN IMAGE SND(R n))) /\
        (!n. R n  SUBSET R(SUC n))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN MATCH_MP_TAC(MESON[]
     `((!n x. P x /\ Q x /\ R x ==> ?y. B n x y) ==> X) /\
      (!n x. P x /\ Q x /\ R x ==> ?y. B n x y)
      ==> X /\
          (!n x. P x /\ Q x /\ R x /\ S n x ==> ?y. B (SUC n) x y)`) THEN
    CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPECL [`0`; `{}:A#B->bool`]) THEN
      REWRITE_TAC[EMPTY_SUBSET; PAIRWISE_EMPTY; FINITE_RULES];
      MAP_EVERY X_GEN_TAC [`n:num`; `R:A#B->bool`] THEN STRIP_TAC] THEN
    ASM_CASES_TAC `(x:num->A) n IN s` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(MP_TAC o SPEC `R:A#B->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `(x:num->A) n` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `z:B` THEN STRIP_TAC THEN
      ASM_CASES_TAC `(y:num->B) n IN t` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `((x:num->A) n,z:B) INSERT R`) THEN
        ASM_REWRITE_TAC[FINITE_INSERT; INSERT_SUBSET] THEN
        ASM_REWRITE_TAC[IN_CROSS] THEN
        DISCH_THEN(MP_TAC o SPEC `(y:num->B) n` o CONJUNCT2) THEN
        ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC `w:A` THEN STRIP_TAC THEN
        EXISTS_TAC `(w,y(n:num)) INSERT (x n,z) INSERT (R:A#B->bool)` THEN
        ASM_REWRITE_TAC[FINITE_INSERT; INSERT_SUBSET; IN_CROSS] THEN
        REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT] THEN SET_TAC[];
        EXISTS_TAC `(x(n:num),z) INSERT (R:A#B->bool)` THEN
        ASM_REWRITE_TAC[FINITE_INSERT; INSERT_SUBSET; IN_CROSS] THEN
        REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT] THEN SET_TAC[]];
      ASM_CASES_TAC `(y:num->B) n IN t` THEN ASM_REWRITE_TAC[] THENL
       [ALL_TAC; ASM_MESON_TAC[SUBSET_REFL]] THEN
      FIRST_ASSUM(MP_TAC o SPEC `R:A#B->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `(y:num->B) n` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `w:A` THEN STRIP_TAC THEN
      EXISTS_TAC `(w,y(n:num)) INSERT (R:A#B->bool)` THEN
      ASM_REWRITE_TAC[FINITE_INSERT; INSERT_SUBSET; IN_CROSS] THEN
      REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT] THEN SET_TAC[]];
    EXISTS_TAC `UNIONS {R n | n IN (:num)} :A#B->bool` THEN
    ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PAIRWISE_CHAIN_UNIONS THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[IN_UNIV] THEN MATCH_MP_TAC WLOG_LE THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(MESON[]
       `(!x y. P x y ==> Q x y) ==> (!x y. P x y ==> Q x y \/ R x y)`) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; UNWIND_THM1; RIGHT_EXISTS_AND_THM;
                  SUBSET; FORALL_PAIR_THM; IN_CROSS] THEN
      SET_TAC[]]]);;

let BACK_AND_FORTH = prove
 (`!R s:A->bool t:B->bool.
        (!x y. x IN s /\ y IN t ==> R x x y y) /\
        (!x y x' y'. x IN s /\ x' IN s /\ y IN t /\ y' IN t /\
                     ~(x = x') /\ ~(y = y') /\ R x x' y y'
                     ==> R x' x y' y) /\
        COUNTABLE s /\ COUNTABLE t /\
        (!f s' t'. FINITE s' /\ s' SUBSET s /\ FINITE t' /\ t' SUBSET t /\
                   IMAGE f s' = t' /\
                   (!x y. x IN s' /\ y IN s' ==> (f x = f y <=> x = y)) /\
                   (!x y. x IN s' /\ y IN s' ==> R x y (f x) (f y))
                   ==> (!x. x IN s DIFF s'
                            ==> ?y. y IN t DIFF t' /\
                                    !z. z IN s' ==> R x z y (f z)) /\
                       (!y. y IN t DIFF t'
                            ==> ?x. x IN s DIFF s' /\
                                    !z. z IN s' ==> R x z y (f z)))
    ==> ?f. IMAGE f s = t /\
            (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
            (!x y. x IN s /\ y IN s ==> R x y (f x) (f y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\(x:A,y:B) (x',y').
        (x = x' <=> y = y') /\ R x x' y y'`;
    `s:A->bool`; `t:B->bool`] BACK_AND_FORTH_ALT) THEN
  ASM_SIMP_TAC[PAIRWISE_INSERT; FORALL_PAIR_THM; PAIR_EQ] THEN ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[pairwise; FORALL_PAIR_THM; PAIR_EQ; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r:A#B->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN STRIP_TAC THEN
    ABBREV_TAC `f:A->B = \x. @y. (x,y) IN r` THEN EXISTS_TAC `f:A->B` THEN
    SUBGOAL_THEN `!x:A y:B. x IN s ==> (f x = y <=> (x,y) IN r)`
    ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o
      SPECL [`x:A`; `(f:A->B) x`; `y:A`; `(f:A->B) y`]) THEN
    ASM_CASES_TAC `x:A = y` THEN ASM_MESON_TAC[]] THEN
  X_GEN_TAC `r:A#B->bool` THEN REWRITE_TAC[SUBSET; pairwise] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; LEFT_IMP_EXISTS_THM; IN_CROSS] THEN
  STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`s' = IMAGE FST (r:A#B->bool)`;
    `t' = IMAGE SND (r:A#B->bool)`;
    `f:A->B = \x. @y. (x,y) IN r`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`f:A->B`; `s':A->bool`; `t':B->bool`]) THEN
  SUBGOAL_THEN
   `!x:A y:B. (x,y) IN r <=> x IN s' /\ y IN t' /\ f x = y`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f"; "s'"; "t'"] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(s':A->bool) SUBSET s /\ (t':B->bool) SUBSET t`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s'"; "t'"] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:A->B) s' = t'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s'"; "t'"] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  ANTS_TAC THENL
   [REPLICATE_TAC 2
      (CONJ_TAC THENL [ASM_MESON_TAC[FINITE_IMAGE]; ALL_TAC]) THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN MATCH_MP_TAC MONO_FORALL THENL
   [X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN s` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    ASM_CASES_TAC `(x:A) IN s'` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `(f:A->B) x` THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    X_GEN_TAC `y:B` THEN
    ASM_CASES_TAC `(y:B) IN t` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    ASM_CASES_TAC `(y:B) IN t'` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `?x:A. x IN s' /\ (f:A->B) x = y` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; EXISTS_TAC `x:A` THEN ASM SET_TAC[]];
      MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]]]);;

let BACK_AND_FORTH_2 = prove
 (`!R s:A->bool t:B->bool.
        (!x y. x IN s /\ y IN t ==> R x x y y) /\
        (!x y x' y'. x IN s /\ x' IN s /\ y IN t /\ y' IN t /\
                     ~(x = x') /\ ~(y = y') /\ R x x' y y'
                     ==> R x' x y' y) /\
        COUNTABLE s /\ COUNTABLE t /\
        (!f s' t' x. FINITE s' /\ s' SUBSET s /\ FINITE t' /\ t' SUBSET t /\
                     IMAGE f s' = t' /\
                     (!x y. x IN s' /\ y IN s' ==> (f x = f y <=> x = y)) /\
                     (!x y. x IN s' /\ y IN s' ==> R x y (f x) (f y)) /\
                     x IN s DIFF s'
                     ==> ?y. y IN t DIFF t' /\
                             !z. z IN s' ==> R x z y (f z)) /\
         (!f t' s' x. FINITE t' /\ t' SUBSET t /\ FINITE s' /\ s' SUBSET s /\
                     IMAGE f t' = s' /\
                     (!x y. x IN t' /\ y IN t' ==> (f x = f y <=> x = y)) /\
                     (!x y. x IN t' /\ y IN t' ==> R (f x) (f y) x y) /\
                     x IN t DIFF t'
                     ==> ?y. y IN s DIFF s' /\
                             !z. z IN t' ==> R y (f z) x z)
    ==> ?f. IMAGE f s = t /\
            (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
            (!x y. x IN s /\ y IN s ==> R x y (f x) (f y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BACK_AND_FORTH THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`f:A->B`; `s':A->bool`; `t':B->bool`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(K ALL_TAC o SPEC `f:A->B`)] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INJECTIVE_ON_ALT]) THEN
  GEN_REWRITE_TAC LAND_CONV [INJECTIVE_ON_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`g:B->A`; `t':B->bool`; `s':A->bool`; `y:B`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]; ALL_TAC] THEN
  EXPAND_TAC "t'" THEN REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_IMAGE_2] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Definition by recursion on dyadic rationals in [0,1].                     *)
(* ------------------------------------------------------------------------- *)

let RECURSION_ON_DYADIC_FRACTIONS = prove
 (`!R a b:A.
        (!x y z. R x y /\ R y z ==> R x z) /\
        R a b /\ (!x y. R x y ==> ?z. R x z /\ R z y)
        ==> ?f. f(&0) = a /\ f(&1) = b /\
                !x y. x IN {&k / &2 pow n | k <= 2 EXP n} /\
                      y IN {&k / &2 pow n | k <= 2 EXP n} /\
                      x < y
                      ==> R (f x) (f y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?f. (f 0 = \k. if k = 0 then a else b) /\
        (!n. f(SUC n) = \k.
                if EVEN k then f n (k DIV 2)
                else @z:A. R (f n ((k - 1) DIV 2)) z /\
                           R z (f n ((k + 1) DIV 2)))`
  MP_TAC THENL [REWRITE_TAC[num_RECURSION]; ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:num->num->A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?f. !k n. f(&k / &2 pow n):A = g n k` MP_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MP_TAC(ISPECL
     [`\(k,n). (g:num->num->A) n k`; `\(k,n). &k / &2 pow n`]
     FUNCTION_FACTORS_LEFT) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FUN_EQ_THM; o_THM] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC[MESON[]
      `(!a b c d. P a b c d) <=> (!b d a c. P a b c d)`] THEN
    MATCH_MP_TAC WLOG_LE THEN REPEAT CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[REAL_FIELD `~(y = &0) /\ ~(y' = &0)
                         ==> (x / y = x' / y' <=> y' / y * x = x')`;
       REAL_POW_EQ_0; REAL_OF_NUM_EQ; REAL_DIV_POW2; ARITH_EQ] THEN
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[ADD_SUB2; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ; REAL_OF_NUM_POW] THEN
    REWRITE_TAC[MESON[]
     `(!n n' d. n' = f d n ==> !m m'. g d m = m' ==> P m m' n d) <=>
      (!d m n. P m (g d m) n d)`] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    INDUCT_TAC THEN SIMP_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[EVEN_MULT; ARITH_EVEN; GSYM MULT_ASSOC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n`];
    MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `f:real->A` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [SUBST1_TAC(REAL_ARITH `&0 = &0 / &2 pow 0`) THEN
    ASM_REWRITE_TAC[];
    SUBST1_TAC(REAL_ARITH `&1 = &1 / &2 pow 0`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`k1:num`; `n1:num`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k2:num`; `n2:num`] THEN DISCH_TAC THEN
    CONJUNCTS_THEN SUBST1_TAC (REAL_FIELD
     `&k1 / &2 pow n1 = (&2 pow n2 * &k1) / &2 pow (n1 + n2) /\
      &k2 / &2 pow n2 = (&2 pow n1 * &k2) / &2 pow (n1 + n2)`) THEN
    SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LT_POW2;
        MESON[REAL_OF_NUM_MUL; REAL_OF_NUM_POW]
         `&2 pow n * &k = &(2 EXP n * k)`] THEN
    SUBGOAL_THEN `&(2 EXP n1 * k2) <= &2 pow (n1 + n2)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; EXP_ADD] THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL];
      SPEC_TAC(`2 EXP n1 * k2`,`j2:num`) THEN
      SPEC_TAC(`2 EXP n2 * k1`,`j1:num`) THEN
      SPEC_TAC(`n1 + n2:num`,`n:num`)] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_POW; GSYM IMP_CONJ_ALT] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LT]))] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `j1 < j2 /\ j2 <= 2 EXP 0 <=> j1 = 0 /\ j2 = 1`;
                 ARITH_EQ];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `j:num`] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[EXP] THEN STRIP_TAC THEN
  DISJ_CASES_THEN MP_TAC (SPEC `j:num` EVEN_OR_ODD) THEN
  DISJ_CASES_THEN MP_TAC (SPEC `k:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  X_GEN_TAC `a:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[ADD1; ADD_SUB; EVEN_ADD; EVEN_MULT; ARITH_EVEN;
                  ARITH_RULE `(2 * a) DIV 2 = a`;
                  ARITH_RULE `((2 * a + 1) + 1) DIV 2 = a + 1`]
  THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  (ABBREV_TAC `w = @z. R ((g:num->num->A) n a) z /\  R z (g n (a + 1))` THEN
   SUBGOAL_THEN `R ((g:num->num->A) n a) w /\ R w (g n (a + 1))`
   STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "w" THEN CONV_TAC SELECT_CONV THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_ARITH_TAC;
     ALL_TAC])
  THENL
   [ALL_TAC;
    ASM_CASES_TAC `b:num = a + 1` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(g:num->num->A) n (a + 1)` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (ABBREV_TAC `z = @z. R ((g:num->num->A) n b) z /\ R z (g n (b + 1))` THEN
   SUBGOAL_THEN `R ((g:num->num->A) n b) z /\ R z (g n (b + 1))`
   STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "z" THEN CONV_TAC SELECT_CONV THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_ARITH_TAC;
     ALL_TAC])
  THENL
   [ASM_CASES_TAC `a:num = b` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(g:num->num->A) n b` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ASM_CASES_TAC `a + 1 = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(g:num->num->A) n (a + 1)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(g:num->num->A) n b`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Suslin operation. The proof of the only non-trivial result,           *)
(* idempotence, is taken from Fremlin's "Measure Theory" volume 4.           *)
(* ------------------------------------------------------------------------- *)

let suslin_operation = new_definition
 `suslin_operation (f:num list->A->bool) =
        UNIONS { INTERS {f (list_of_seq s n) | 1 <= n} | s IN (:num->num)}`;;

let suslin = new_definition
 `suslin u = {suslin_operation f | !l. ~(l = []) ==> f l IN u}`;;

let SUSLIN_INC = prove
 (`!C s:A->bool. C s ==> suslin C s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[suslin; IN_ELIM_THM] THEN
  EXISTS_TAC `(\i. s):num list->A->bool` THEN
  ASM_REWRITE_TAC[suslin_operation] THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[IMAGE_CONST; UNIV_NOT_EMPTY] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INTERS_1; UNIONS_1] THEN
  MP_TAC LE_REFL THEN ASM SET_TAC[]);;

let SUSLIN_SUPERSET = prove
 (`!u:(A->bool)->bool. u SUBSET suslin u`,
  REWRITE_TAC[SUBSET; IN; SUSLIN_INC]);;

let SUSLIN_SUBSET = prove
 (`!C D:(A->bool)->bool. C SUBSET D ==> suslin C SUBSET suslin D`,
  REWRITE_TAC[suslin] THEN SET_TAC[]);;

let SUSLIN_MONO = prove
 (`!C D s:A->bool.
        (!t. C t ==> D t) /\ suslin C s ==> suslin D s`,
  REWRITE_TAC[suslin] THEN SET_TAC[]);;

let SUSLIN_REGULAR = prove
 (`!u:(A->bool)->bool.
        (!c. FINITE c /\ ~(c = {}) /\ c SUBSET u ==> INTERS c IN u)
        ==> (suslin u =
             {suslin_operation f | (!l. ~(l = []) ==> f l IN u) /\
                                   !s m n. 1 <= m /\ m <= n
                                           ==> f(list_of_seq s n) SUBSET
                                               f(list_of_seq s m)})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[suslin; GSYM SUBSET_ANTISYM_EQ] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `f:num list->A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `\l. INTERS {(f:num list->A->bool)(list_of_seq (\i. EL i l) n) |n|
                          1 <= n /\ n <= LENGTH l}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    SIMP_TAC[GSYM numseg; FINITE_NUMSEG; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[NUMSEG_EMPTY; NOT_LT; LENGTH_EQ_NIL; LE_1] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GSYM LENGTH_EQ_NIL; LENGTH_LIST_OF_SEQ; LE_1];
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; LENGTH_LIST_OF_SEQ] THEN
    MAP_EVERY X_GEN_TAC [`s:num->num`; `m:num`; `n:num`] THEN
    DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[LIST_EQ] THEN
    SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    ASM_MESON_TAC[EL_LIST_OF_SEQ; LT_TRANS; LTE_TRANS];
    REWRITE_TAC[suslin_operation] THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC(SET_RULE
     `(!x. f x = g x) ==> IMAGE f UNIV = IMAGE g UNIV`) THEN
    X_GEN_TAC `s:num->num` THEN
    REWRITE_TAC[EXTENSION] THEN
    X_GEN_TAC `a:A` THEN REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_UNIV; LENGTH_LIST_OF_SEQ] THEN
    SUBGOAL_THEN
     `!m n. 1 <= m /\ m <= n
            ==> list_of_seq (\i. EL i (list_of_seq s n)) m :num list =
                list_of_seq s m`
     (fun th -> SIMP_TAC[th])
    THENL
     [SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
      MESON_TAC[EL_LIST_OF_SEQ; LTE_TRANS];
      ASM_MESON_TAC[LE_TRANS; LE_REFL]]]);;

let SUSLIN_SUSLIN = prove
 (`!u:(A->bool)->bool. suslin (suslin u) = suslin u`,
  GEN_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUSLIN_SUPERSET] THEN
  REWRITE_TAC[suslin; SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `f:num list->A->bool` THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [IN_ELIM_THM; RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:(num)list->(num)list->A->bool` THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  SUBGOAL_THEN
   `suslin_operation(f:num list->A->bool) =
    suslin_operation(\l. suslin_operation (g l))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC BINOP_CONV [suslin_operation] THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `s:num->num` THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GSYM LENGTH_EQ_NIL; LENGTH_LIST_OF_SEQ; LE_1];
    REMOVE_THEN "*" (K ALL_TAC)] THEN
  REWRITE_TAC[IN_ELIM_THM; suslin_operation] THEN
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; INTERS_GSPEC; UNIONS_GSPEC; IN_UNIV] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  SUBGOAL_THEN
   `?h:num->A->bool.
        {g l m | ~(l:num list = []) /\ ~(m:num list = [])} = IMAGE h (:num)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC COUNTABLE_AS_IMAGE THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `~(x = []) <=> x IN {l | ~(l = [])}`] THEN
      MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT THEN
      MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN SIMP_TAC[] THEN
      MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC `(:num list)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC COUNTABLE_LIST THEN
      REWRITE_TAC[NUM_COUNTABLE];
      MATCH_MP_TAC(SET_RULE `(?x. P x) ==> ~({f x y | P x /\ P y} = {})`) THEN
      MESON_TAC[NOT_CONS_NIL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?q:num#num->num.
        (!a b. 1 <= q(a,b)) /\
        q(0,0) = 1 /\ q(0,1) = 2 /\
        (!a b a' b'. q(a,b) = q(a',b') <=> a = a' /\ b = b')`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(:num#num) DIFF {(0,0), (0,1)} =_c (:num) DIFF {0,1,2}`
    MP_TAC THENL
     [TRANS_TAC CARD_EQ_TRANS `(:num#num)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_DIFF_ABSORB THEN
        REWRITE_TAC[INFINITE_UNIV_PAIR; num_INFINITE] THEN
        TRANS_TAC CARD_LTE_TRANS `(:num)` THEN
        REWRITE_TAC[GSYM FINITE_CARD_LT; FINITE_INSERT; FINITE_EMPTY] THEN
        MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
        REWRITE_TAC[CARD_SQUARE_NUM; GSYM MUL_C_UNIV];
        REWRITE_TAC[GSYM MUL_C_UNIV] THEN TRANS_TAC CARD_EQ_TRANS `(:num)` THEN
        REWRITE_TAC[CARD_SQUARE_NUM] THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
        MATCH_MP_TAC CARD_DIFF_ABSORB THEN REWRITE_TAC[num_INFINITE] THEN
        REWRITE_TAC[GSYM FINITE_CARD_LT; FINITE_INSERT; FINITE_EMPTY]];
      REWRITE_TAC[EQ_C_BIJECTIONS; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`q:num#num->num`; `q':num->num#num`] THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_DIFF; IN_UNIV; IN_INSERT] THEN
      REWRITE_TAC[PAIR_EQ; NOT_IN_EMPTY; DE_MORGAN_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `!a b a' b'. q(a,b):num = q(a',b')
                    ==> a = 0 /\ (b = 0 \/ b = 1) \/
                        a' = 0 /\ (b' = 0 \/ b' = 1) \/
                        a = a' /\ b = b'`
      ASSUME_TAC THENL
       [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`; `d:num`] THEN
        REWRITE_TAC[TAUT `p ==> q \/ r <=> p ==> ~q ==> r`] THEN
        REPEAT DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
          MP_TAC(SPECL [`a:num`; `b:num`] th) THEN
          MP_TAC(SPECL [`c:num`; `d:num`] th)) THEN
        ASM_REWRITE_TAC[GSYM PAIR_EQ] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `\(a,b). if (a,b) = (0,0) then 1
                          else if (a,b) = (0,1) then 2 else q(a,b)` THEN
      ASM_REWRITE_TAC[PAIR_EQ; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `J = \(k,m). {(i,0) | i < k} UNION {(i,k) | i < m}` THEN
  SUBGOAL_THEN
   `?k:num->num m:num->num.
        IMAGE (\n. k n,m n) {n | 3 <= n} =
        ((:num) DELETE 0) CROSS ((:num) DELETE 0) /\
        !n. 3 <= n ==> IMAGE (q:num#num->num) (J(k n,m n)) SUBSET {a | a < n}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?r:num#num->num.
        (!a. a IN ((:num) DELETE 0) CROSS ((:num) DELETE 0)
             ==> r a IN {n | 3 <= n}) /\
        (!a. a IN ((:num) DELETE 0) CROSS ((:num) DELETE 0)
             ==> IMAGE (q:num#num->num) (J a) SUBSET {m | m < r a}) /\
        (!a b. a IN ((:num) DELETE 0) CROSS ((:num) DELETE 0) /\
               b IN ((:num) DELETE 0) CROSS ((:num) DELETE 0) /\
               r a = r b
               ==> a = b)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `((:num) DELETE 0) CROSS ((:num) DELETE 0) =_c (:num)`
      MP_TAC THENL
       [TRANS_TAC CARD_EQ_TRANS `(:num) *_c (:num)` THEN
        REWRITE_TAC[CARD_SQUARE_NUM; CROSS; GSYM mul_c] THEN
        MATCH_MP_TAC CARD_MUL_CONG THEN REWRITE_TAC[] THEN
        REWRITE_TAC[SET_RULE `s DELETE a = s DIFF {a}`] THEN
        MATCH_MP_TAC CARD_DIFF_ABSORB THEN
        REWRITE_TAC[num_INFINITE; GSYM FINITE_CARD_LT; FINITE_SING];
        REWRITE_TAC[EQ_C_BIJECTIONS; LEFT_IMP_EXISTS_THM; IN_UNIV]] THEN
      MAP_EVERY X_GEN_TAC [`p':num#num->num`; `p:num->num#num`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `?t:num->num. (!n. IMAGE q ((J:num#num->num#num->bool)(p n)) SUBSET
                          {a | a < t n} /\ 2 < t n) /\
                     (!n. t n < t (SUC n))`
      MP_TAC THENL
       [MATCH_MP_TAC DEPENDENT_CHOICE THEN
        REWRITE_TAC[SET_RULE `s SUBSET {a | a < y} /\ x < y <=>
                              (x INSERT s) SUBSET {a:num | a < y}`] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(MESON[] `(?a. P(SUC a)) ==> (?a. P a)`) THEN
        REWRITE_TAC[LT_SUC_LE; SUBSET; IN_ELIM_THM] THEN
        MATCH_MP_TAC UPPER_BOUND_FINITE_SET THEN
        REWRITE_TAC[FINITE_INSERT] THEN MATCH_MP_TAC FINITE_IMAGE  THEN
        EXPAND_TAC "J" THEN
        MATCH_MP_TAC(MESON[] `(!x. FINITE(f x)) ==> FINITE(f a)`) THEN
        REWRITE_TAC[FORALL_PAIR_THM; FINITE_UNION] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
        SIMP_TAC[FINITE_NUMSEG_LT; FINITE_IMAGE];
        REWRITE_TAC[ARITH_RULE `2 < n <=> 3 <= n`] THEN STRIP_TAC] THEN
      EXISTS_TAC `(t:num->num) o (p':num#num->num)` THEN
      ASM_REWRITE_TAC[o_THM; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `((:num) DELETE 0) CROSS ((:num) DELETE 0) =
        IMAGE p (:num)`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN
      MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `!m n. m < n ==> (t:num->num) m < t n` MP_TAC THENL
       [ALL_TAC; MESON_TAC[LT_REFL]] THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
      ASM_REWRITE_TAC[LT_TRANS];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [INJECTIVE_ON_LEFT_INVERSE]) THEN
      DISCH_THEN(X_CHOOSE_TAC `l:num->num#num`) THEN
      EXISTS_TAC
       `\n. if n IN IMAGE r (((:num) DELETE 0) CROSS ((:num) DELETE 0))
                then FST((l:num->num#num) n) else 1` THEN
      EXISTS_TAC
       `\n. if n IN IMAGE r (((:num) DELETE 0) CROSS ((:num) DELETE 0))
                then SND((l:num->num#num) n) else 1` THEN
      REWRITE_TAC[MESON[]
       `(if p then x else 1),(if p then y else 1) =
        (if p then x,y else 1,1)`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM SUBSET_ANTISYM_EQ] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[IN_CROSS; IN_UNIV; IN_DELETE] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM SET_TAC[];
        ASM SET_TAC[];
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        GEN_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[IN_CROSS; IN_UNIV; IN_DELETE] THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "J" THEN REWRITE_TAC[IN_UNION] THEN
        REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
        REWRITE_TAC[SET_RULE `{f x | x = a} = {f a}`] THEN
        REWRITE_TAC[IN_SING] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC
   `f = \l. if LENGTH l <= 2 then h(EL 0 l)
            else (g:(num)list->(num)list->A->bool)
                (list_of_seq (\i. EL (q(i,0)) l) (k(LENGTH l)))
                (list_of_seq (\i. EL (q(i,k(LENGTH l))) l) (m(LENGTH l)))` THEN
  EXISTS_TAC `f:num list->A->bool` THEN EXPAND_TAC "f" THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC] THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_LIST_OF_SEQ] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `IMAGE f s = t ==> !x. x IN s ==> f x IN t`)) THEN
    DISCH_THEN(MP_TAC o SPEC `LENGTH(l:num list)`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_CROSS; IN_UNIV; IN_DELETE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`s:num->num`; `s':num->num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?t. h(t 0) = (g:(num)list->(num)list->A->bool)
                   (list_of_seq s 1) (list_of_seq (s' 1) 1) /\
          (!i. t(q(i,0)) = s i) /\
          (!i j. 1 <= j ==> t(q(i,j)) = s' j i)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `?t:num->num.
          (\(i,j). if j = 0 then s i else s' j i) = t o (q:num#num->num)`
      MP_TAC THENL
       [REWRITE_TAC[GSYM FUNCTION_FACTORS_LEFT] THEN
        ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[];
        REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:num->num` o GSYM) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `t = IMAGE f UNIV ==> !y. y IN t ==> ?x. f x = y`)) THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      DISCH_THEN(MP_TAC o SPECL
       [`list_of_seq s 1:num list`; `list_of_seq (s' 1) 1:num list`]) THEN
      REWRITE_TAC[LIST_OF_SEQ_EQ_NIL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(X_CHOOSE_THEN `p:num` (SUBST1_TAC o SYM)) THEN
      EXISTS_TAC `\n. if n = 0 then p:num else t n` THEN
      ASM_SIMP_TAC[LE_1];
      EXISTS_TAC `t:num->num`] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    SIMP_TAC[LE_1; EL_LIST_OF_SEQ] THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONV_TAC NUM_REDUCE_CONV;
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `~(n <= 2) <=> 3 <= n`])] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `IMAGE f s = t ==> !x. x IN s ==> f x IN t`)) THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_CROSS; IN_DELETE; IN_UNIV] THEN
    REWRITE_TAC[ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
    DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
     FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
    SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EL_LIST_OF_SEQ o rand o snd) THEN
    ASM_SIMP_TAC[LE_1] THEN DISCH_THEN(MATCH_MP_TAC o GSYM);
    X_GEN_TAC `t:num->num` THEN DISCH_THEN(LABEL_TAC "*") THEN
    EXISTS_TAC `\i:num. (t:num->num)(q(i,0))` THEN
    EXISTS_TAC `\j:num i:num. (t:num->num)(q(i,j))` THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `mm:num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`)) THEN
    DISCH_THEN(MP_TAC o SPEC `(kk:num),(mm:num)`) THEN
    ASM_SIMP_TAC[IN_CROSS; IN_DELETE; IN_UNIV; LE_1; PAIR_EQ; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; ARITH_RULE
     `3 <= n ==> 1 <= n /\ ~(n <= 2)`] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
    SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC EL_LIST_OF_SEQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SUBSET; IN_ELIM_THM; FORALL_IN_IMAGE; RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "J" THEN REWRITE_TAC[IN_UNION; IN_ELIM_PAIR_THM] THEN
  ASM SET_TAC[]);;

let SUSLIN_INTERS = prove
 (`!C f:(A->bool)->bool.
        COUNTABLE f /\ ~(f = {}) /\
        (!s. s IN f ==> suslin C s)
        ==> suslin C (INTERS f)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPEC `f:(A->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:num->A->bool` THEN DISCH_THEN SUBST1_TAC THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM SUSLIN_SUSLIN] THEN
  ONCE_REWRITE_TAC[suslin] THEN
  REWRITE_TAC[IN_ELIM_THM; suslin_operation] THEN
  EXISTS_TAC `(f:num->A->bool) o (\n. n - 1) o (LENGTH:num list->num)` THEN
  ASM_REWRITE_TAC[o_THM; LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CONST; UNIV_NOT_EMPTY; UNIONS_1] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; AP_TERM_TAC] THEN
  MP_TAC(ARITH_RULE `!n. 1 <= SUC n /\ SUC n - 1 = n`) THEN
  SET_TAC[]);;

let SUSLIN_INTER = prove
 (`!C s t:A->bool. suslin C s /\ suslin C t ==> suslin C (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC SUSLIN_INTERS THEN
  REWRITE_TAC[COUNTABLE_INSERT; COUNTABLE_EMPTY; NOT_INSERT_EMPTY] THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let SUSLIN_UNIONS = prove
 (`!C f:(A->bool)->bool.
        COUNTABLE f /\ ~(f = {}) /\
        (!s. s IN f ==> suslin C s)
        ==> suslin C (UNIONS f)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPEC `f:(A->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:num->A->bool` THEN DISCH_THEN SUBST1_TAC THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM SUSLIN_SUSLIN] THEN
  ONCE_REWRITE_TAC[suslin] THEN
  REWRITE_TAC[IN_ELIM_THM; suslin_operation] THEN
  EXISTS_TAC `(f:num->A->bool) o (EL 0:num list->num)` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:num->A->bool s.
        {f (EL 0 (list_of_seq s n)) | 1 <= n} = {f(s 0)}`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REPEAT GEN_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(?x. P x) /\ (!x. P x ==> f x = a) ==> {f x | P x} = {a}`) THEN
    SIMP_TAC[EL_LIST_OF_SEQ; LE_1] THEN MESON_TAC[LE_REFL];
    REWRITE_TAC[INTERS_1] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
    SIMP_TAC[FUN_IN_IMAGE; IN_UNIV; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `(\i. n):num->num` THEN REWRITE_TAC[]]);;

let SUSLIN_UNION = prove
 (`!C s t:A->bool. suslin C s /\ suslin C t ==> suslin C (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC SUSLIN_UNIONS THEN
  REWRITE_TAC[COUNTABLE_INSERT; COUNTABLE_EMPTY; NOT_INSERT_EMPTY] THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let CARD_SUSLIN_LE = prove
 (`!C:(A->bool)->bool. C <=_c (:real) ==> suslin C <=_c (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[suslin] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  TRANS_TAC CARD_LE_TRANS
   `IMAGE suslin_operation ((C:(A->bool)->bool) ^_c (:num list))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC[exp_c; IN_UNIV] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> ?y. y IN t /\ f x = f y)
      ==> IMAGE f s SUBSET IMAGE f t`) THEN
    X_GEN_TAC `f:num list->A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\l. if l = [] then f[0] else f l:A->bool` THEN
    REWRITE_TAC[suslin_operation] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NOT_CONS_NIL]; ALL_TAC] THEN
    REPEAT(AP_TERM_TAC THEN
           MATCH_MP_TAC(SET_RULE
            `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
           REPEAT STRIP_TAC) THEN
    ASM_SIMP_TAC[LIST_OF_SEQ_EQ_NIL; LE_1];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH lhand CARD_LE_IMAGE o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_TRANS) THEN
  TRANS_TAC CARD_LE_TRANS `(:real) ^_c (:num list)` THEN
  ASM_SIMP_TAC[CARD_LE_EXP_LEFT] THEN
  TRANS_TAC CARD_LE_TRANS `(:num->bool) ^_c (:num)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_IMP_LE THEN MATCH_MP_TAC CARD_EXP_CONG THEN
    SIMP_TAC[CARD_EQ_REAL; CARD_EQ_LIST; num_INFINITE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CARD_EXP_UNIV] THEN
  W(MP_TAC o PART_MATCH rand CARD_EXP_MUL o lhand o snd) THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_TRANS) THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  TRANS_TAC CARD_EQ_TRANS `(:num->bool)` THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[CARD_EQ_REAL] THEN
  REWRITE_TAC[GSYM CARD_EXP_UNIV] THEN
  MATCH_MP_TAC CARD_EXP_CONG THEN REWRITE_TAC[CARD_EQ_REFL] THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[CARD_SQUARE_NUM]);;

let CARD_SUSLIN_EQ = prove
 (`!C:(A->bool)->bool. C =_c (:real) ==> suslin C =_c (:real)`,
  GEN_TAC THEN SIMP_TAC[GSYM CARD_LE_ANTISYM] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[CARD_SUSLIN_LE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_TRANS) THEN
  MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC[SUSLIN_SUPERSET]);;
