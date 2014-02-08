(* ========================================================================= *)
(* Various convenient background stuff.                                      *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

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

let EXISTS_DIFF = prove
 (`(?s:A->bool. P(UNIV DIFF s)) <=> (?s. P s)`,
  MESON_TAC[prove(`UNIV DIFF (UNIV DIFF s) = s`,SET_TAC[])]);;

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
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let UPPER_BOUND_FINITE_SET_REAL = prove
 (`!f:(A->real) s. FINITE(s) ==> ?a. !x. x IN s ==> f(x) <= a`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let LOWER_BOUND_FINITE_SET = prove
 (`!f:(A->num) s. FINITE(s) ==> ?a. !x. x IN s ==> a <= f(x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let LOWER_BOUND_FINITE_SET_REAL = prove
 (`!f:(A->real) s. FINITE(s) ==> ?a. !x. x IN s ==> a <= f(x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

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

let INFINITE_ENUMERATE_WEAK = prove
 (`!s:num->bool.
       INFINITE s
       ==> ?r:num->num. (!m n. m < n ==> r(m) < r(n)) /\ (!n. r n IN s)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_ENUMERATE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

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

(* ------------------------------------------------------------------------- *)
(* More variants of the Archimedian property and useful consequences.        *)
(* ------------------------------------------------------------------------- *)

let REAL_ARCH_INV = prove
 (`!e. &0 < e <=> ?n. ~(n = 0) /\ &0 < inv(&n) /\ inv(&n) < e`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LT_TRANS]] THEN
  DISCH_TAC THEN MP_TAC(SPEC `inv(e)` REAL_ARCH_LT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[REAL_LT_INV2; REAL_INV_INV; REAL_LT_INV_EQ; REAL_LT_TRANS;
                REAL_LT_ANTISYM]);;

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

let REAL_ARCH_POW2 = prove
 (`!x. ?n. x < &2 pow n`,
  SIMP_TAC[REAL_ARCH_POW; REAL_OF_NUM_LT; ARITH]);;

let REAL_ARCH_POW_INV = prove
 (`!x y. &0 < y /\ x < &1 ==> ?n. x pow n < y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < x` THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_POW_1; REAL_LET_TRANS; REAL_NOT_LT]] THEN
  SUBGOAL_THEN `inv(&1) < inv(x)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV2]; REWRITE_TAC[REAL_INV_1]] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(y)` o MATCH_MP REAL_ARCH_POW) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_INV; REAL_LT_INV; REAL_LT_INV2]);;

let FORALL_POS_MONO = prove
 (`!P. (!d e. d < e /\ P d ==> P e) /\ (!n. ~(n = 0) ==> P(inv(&n)))
       ==> !e. &0 < e ==> P e`,
  MESON_TAC[REAL_ARCH_INV; REAL_LT_TRANS]);;

let FORALL_POS_MONO_1 = prove
 (`!P. (!d e. d < e /\ P d ==> P e) /\ (!n. P(inv(&n + &1)))
       ==> !e. &0 < e ==> P e`,
  REWRITE_TAC[REAL_OF_NUM_SUC; GSYM FORALL_SUC; FORALL_POS_MONO]);;

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
(* Relate max and min to sup and inf.                                        *)
(* ------------------------------------------------------------------------- *)

let REAL_MAX_SUP = prove
 (`!x y. max x y = sup {x,y}`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_SUP_LE_FINITE; REAL_LE_SUP_FINITE;
           FINITE_RULES; NOT_INSERT_EMPTY; REAL_MAX_LE; REAL_LE_MAX] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LE_TOTAL]);;

let REAL_MIN_INF = prove
 (`!x y. min x y = inf {x,y}`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_INF_LE_FINITE; REAL_LE_INF_FINITE;
           FINITE_RULES; NOT_INSERT_EMPTY; REAL_MIN_LE; REAL_LE_MIN] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LE_TOTAL]);;

(* ------------------------------------------------------------------------- *)
(* Define square root here to decouple it from the existing analysis theory. *)
(* ------------------------------------------------------------------------- *)

let sqrt = new_definition
  `sqrt(x) = @y. &0 <= y /\ (y pow 2 = x)`;;

let SQRT_UNIQUE = prove
 (`!x y. &0 <= y /\ (y pow 2 = x) ==> (sqrt(x) = y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sqrt] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_POW_2] THEN
  REWRITE_TAC[REAL_ARITH `(x * x = y * y) <=> ((x + y) * (x - y) = &0)`] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let POW_2_SQRT = prove
 (`!x. &0 <= x ==> (sqrt(x pow 2) = x)`,
  MESON_TAC[SQRT_UNIQUE]);;

let SQRT_0 = prove
 (`sqrt(&0) = &0`,
  MESON_TAC[SQRT_UNIQUE; REAL_POW_2; REAL_MUL_LZERO; REAL_POS]);;

let SQRT_1 = prove
 (`sqrt(&1) = &1`,
   MESON_TAC[SQRT_UNIQUE; REAL_POW_2; REAL_MUL_LID; REAL_POS]);;

let POW_2_SQRT_ABS = prove
 (`!x. sqrt(x pow 2) = abs(x)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN
  REWRITE_TAC[REAL_ABS_POS; REAL_POW_2; GSYM REAL_ABS_MUL] THEN
  REWRITE_TAC[real_abs; REAL_LE_SQUARE]);;

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

let FROM_INTER_NUMSEG_GEN = prove
 (`!k m n. (from k) INTER (m..n) = (if m < k then k..n else m..n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[from; IN_ELIM_THM; IN_INTER; IN_NUMSEG; EXTENSION] THEN
  ARITH_TAC);;

let FROM_INTER_NUMSEG = prove
 (`!k n. (from k) INTER (0..n) = k..n`,
  REWRITE_TAC[from; IN_ELIM_THM; IN_INTER; IN_NUMSEG; EXTENSION] THEN
  ARITH_TAC);;

let IN_FROM = prove
 (`!m n. m IN from n <=> n <= m`,
  REWRITE_TAC[from; IN_ELIM_THM]);;

let INFINITE_FROM = prove
 (`!n. INFINITE(from n)`,
  GEN_TAC THEN
  SUBGOAL_THEN `from n = (:num) DIFF {i | i < n}`
   (fun th -> SIMP_TAC[th; INFINITE_DIFF_FINITE; FINITE_NUMSEG_LT;
   num_INFINITE]) THEN
  REWRITE_TAC[EXTENSION; from; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN ARITH_TAC);;

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
