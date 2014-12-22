(* ========================================================================= *)
(* Real vectors in Euclidean space, and elementary linear algebra.           *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*               (c) Copyright, Marco Maggesi 2014                           *)
(* ========================================================================= *)

needs "Library/card.ml";;
needs "Library/floor.ml";;
needs "Multivariate/misc.ml";;

(* ------------------------------------------------------------------------- *)
(* Some common special cases.                                                *)
(* ------------------------------------------------------------------------- *)

let FORALL_1 = prove
 (`(!i. 1 <= i /\ i <= 1 ==> P i) <=> P 1`,
  MESON_TAC[LE_ANTISYM]);;

let FORALL_2 = prove
 (`!P. (!i. 1 <= i /\ i <= 2 ==> P i) <=> P 1 /\ P 2`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`]);;

let FORALL_3 = prove
 (`!P. (!i. 1 <= i /\ i <= 3 ==> P i) <=> P 1 /\ P 2 /\ P 3`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`]);;

let FORALL_4 = prove
 (`!P. (!i. 1 <= i /\ i <= 4 ==> P i) <=> P 1 /\ P 2 /\ P 3 /\ P 4`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 4 <=>
    i = 1 \/ i = 2 \/ i = 3 \/ i = 4`]);;

let SUM_1 = prove
 (`sum(1..1) f = f(1)`,
  REWRITE_TAC[SUM_SING_NUMSEG]);;

let SUM_2 = prove
 (`!t. sum(1..2) t = t(1) + t(2)`,
  REWRITE_TAC[num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let SUM_3 = prove
 (`!t. sum(1..3) t = t(1) + t(2) + t(3)`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let SUM_4 = prove
 (`!t. sum(1..4) t = t(1) + t(2) + t(3) + t(4)`,
  SIMP_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Basic componentwise operations on vectors.                                *)
(* ------------------------------------------------------------------------- *)

let vector_add = new_definition
  `(vector_add:real^N->real^N->real^N) x y = lambda i. x$i + y$i`;;

let vector_sub = new_definition
  `(vector_sub:real^N->real^N->real^N) x y = lambda i. x$i - y$i`;;

let vector_neg = new_definition
  `(vector_neg:real^N->real^N) x = lambda i. --(x$i)`;;

overload_interface ("+",`(vector_add):real^N->real^N->real^N`);;
overload_interface ("-",`(vector_sub):real^N->real^N->real^N`);;
overload_interface ("--",`(vector_neg):real^N->real^N`);;

prioritize_real();;

let prioritize_vector = let ty = `:real^N` in
  fun () -> prioritize_overload ty;;

(* ------------------------------------------------------------------------- *)
(* Also the scalar-vector multiplication.                                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("%",(21,"right"));;

let vector_mul = new_definition
  `((%):real->real^N->real^N) c x = lambda i. c * x$i`;;

(* ------------------------------------------------------------------------- *)
(* Vectors corresponding to small naturals. Perhaps should overload "&"?     *)
(* ------------------------------------------------------------------------- *)

let vec = new_definition
  `(vec:num->real^N) n = lambda i. &n`;;

(* ------------------------------------------------------------------------- *)
(* Dot products.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("dot",(20,"right"));;

let dot = new_definition
  `(x:real^N) dot (y:real^N) = sum(1..dimindex(:N)) (\i. x$i * y$i)`;;

let DOT_1 = prove
 (`(x:real^1) dot (y:real^1) = x$1 * y$1`,
  REWRITE_TAC[dot; DIMINDEX_1; SUM_1]);;

let DOT_2 = prove
 (`(x:real^2) dot (y:real^2) = x$1 * y$1 + x$2 * y$2`,
  REWRITE_TAC[dot; DIMINDEX_2; SUM_2]);;

let DOT_3 = prove
 (`(x:real^3) dot (y:real^3) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3`,
  REWRITE_TAC[dot; DIMINDEX_3; SUM_3]);;

let DOT_4 = prove
 (`(x:real^4) dot (y:real^4) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3 + x$4 * y$4`,
  REWRITE_TAC[dot; DIMINDEX_4; SUM_4]);;

(* ------------------------------------------------------------------------- *)
(* A naive proof procedure to lift really trivial arithmetic stuff from R.   *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ARITH_TAC =
  let RENAMED_LAMBDA_BETA th =
    if fst(dest_fun_ty(type_of(funpow 3 rand (concl th)))) = aty
    then INST_TYPE [aty,bty; bty,aty] LAMBDA_BETA else LAMBDA_BETA in
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_TAC ORELSE EQ_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[dot; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG;
              GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_NEG] THEN
  (MATCH_MP_TAC SUM_EQ_NUMSEG ORELSE MATCH_MP_TAC SUM_EQ_0_NUMSEG ORELSE
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ]) THEN
  REWRITE_TAC[AND_FORALL_THM] THEN TRY EQ_TAC THEN
  TRY(MATCH_MP_TAC MONO_FORALL) THEN GEN_TAC THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`;
              TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`] THEN
  TRY(MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`)) THEN
  REWRITE_TAC[vector_add; vector_sub; vector_neg; vector_mul; vec] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP(RENAMED_LAMBDA_BETA th) th]) THEN
  REAL_ARITH_TAC;;

let VECTOR_ARITH tm = prove(tm,VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Obvious "component-pushing".                                              *)
(* ------------------------------------------------------------------------- *)

let VEC_COMPONENT = prove
 (`!k i. (vec k :real^N)$i = &k`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vec; CART_EQ; LAMBDA_BETA]]);;

let VECTOR_ADD_COMPONENT = prove
 (`!x:real^N y i. (x + y)$i = x$i + y$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vector_add; CART_EQ; LAMBDA_BETA]]);;

let VECTOR_SUB_COMPONENT = prove
 (`!x:real^N y i. (x - y)$i = x$i - y$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vector_sub; CART_EQ; LAMBDA_BETA]]);;

let VECTOR_NEG_COMPONENT = prove
 (`!x:real^N i. (--x)$i = --(x$i)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vector_neg; CART_EQ; LAMBDA_BETA]]);;

let VECTOR_MUL_COMPONENT = prove
 (`!c x:real^N i. (c % x)$i = c * x$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vector_mul; CART_EQ; LAMBDA_BETA]]);;

let COND_COMPONENT = prove
 (`(if b then x else y)$i = if b then x$i else y$i`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some frequently useful arithmetic lemmas over vectors.                    *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ADD_SYM = VECTOR_ARITH `!x y:real^N. x + y = y + x`;;

let VECTOR_ADD_LID = VECTOR_ARITH `!x. vec 0 + x = x`;;

let VECTOR_ADD_RID = VECTOR_ARITH `!x. x + vec 0 = x`;;

let VECTOR_SUB_REFL = VECTOR_ARITH `!x. x - x = vec 0`;;

let VECTOR_ADD_LINV = VECTOR_ARITH `!x. --x + x = vec 0`;;

let VECTOR_ADD_RINV = VECTOR_ARITH `!x. x + --x = vec 0`;;

let VECTOR_SUB_RADD = VECTOR_ARITH `!x y. x - (x + y) = --y:real^N`;;

let VECTOR_NEG_SUB = VECTOR_ARITH `!x:real^N y. --(x - y) = y - x`;;

let VECTOR_SUB_EQ = VECTOR_ARITH `!x y. (x - y = vec 0) <=> (x = y)`;;

let VECTOR_MUL_ASSOC = VECTOR_ARITH `!a b x. a % (b % x) = (a * b) % x`;;

let VECTOR_MUL_LID = VECTOR_ARITH `!x. &1 % x = x`;;

let VECTOR_MUL_LZERO = VECTOR_ARITH `!x. &0 % x = vec 0`;;

let VECTOR_SUB_ADD = VECTOR_ARITH `(x - y) + y = x:real^N`;;

let VECTOR_SUB_ADD2 = VECTOR_ARITH `y + (x - y) = x:real^N`;;

let VECTOR_ADD_LDISTRIB = VECTOR_ARITH `c % (x + y) = c % x + c % y`;;

let VECTOR_SUB_LDISTRIB = VECTOR_ARITH `c % (x - y) = c % x - c % y`;;

let VECTOR_ADD_RDISTRIB = VECTOR_ARITH `(a + b) % x = a % x + b % x`;;

let VECTOR_SUB_RDISTRIB = VECTOR_ARITH `(a - b) % x = a % x - b % x`;;

let VECTOR_ADD_SUB = VECTOR_ARITH `(x + y:real^N) - x = y`;;

let VECTOR_EQ_ADDR = VECTOR_ARITH `(x + y = x) <=> (y = vec 0)`;;

let VECTOR_SUB = VECTOR_ARITH `x - y = x + --(y:real^N)`;;

let VECTOR_SUB_RZERO = VECTOR_ARITH `x - vec 0 = x`;;

let VECTOR_MUL_RZERO = VECTOR_ARITH `c % vec 0 = vec 0`;;

let VECTOR_NEG_MINUS1 = VECTOR_ARITH `--x = (--(&1)) % x`;;

let VECTOR_ADD_ASSOC = VECTOR_ARITH `(x:real^N) + y + z = (x + y) + z`;;

let VECTOR_SUB_LZERO = VECTOR_ARITH `vec 0 - x = --x`;;

let VECTOR_NEG_NEG = VECTOR_ARITH `--(--(x:real^N)) = x`;;

let VECTOR_MUL_LNEG = VECTOR_ARITH `--c % x = --(c % x)`;;

let VECTOR_MUL_RNEG = VECTOR_ARITH `c % --x = --(c % x)`;;

let VECTOR_NEG_0 = VECTOR_ARITH `--(vec 0) = vec 0`;;

let VECTOR_NEG_EQ_0 = VECTOR_ARITH `--x = vec 0 <=> x = vec 0`;;

let VECTOR_EQ_NEG2 = VECTOR_ARITH `!x y:real^N. --x = --y <=> x = y`;;

let VECTOR_ADD_AC = VECTOR_ARITH
  `(m + n = n + m:real^N) /\
   ((m + n) + p = m + n + p) /\
   (m + n + p = n + m + p)`;;

let VEC_EQ = prove
 (`!m n. (vec m = vec n) <=> (m = n)`,
  SIMP_TAC[CART_EQ; VEC_COMPONENT; REAL_OF_NUM_EQ] THEN
  MESON_TAC[LE_REFL; DIMINDEX_GE_1]);;

(* ------------------------------------------------------------------------- *)
(* Analogous theorems for set-sums.                                          *)
(* ------------------------------------------------------------------------- *)

let SUMS_SYM = prove
 (`!s t:real^N->bool.
        {x + y | x IN s /\ y IN t} = {y + x | y IN t /\ x IN s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_SYM]);;

let SUMS_ASSOC = prove
 (`!s t u:real^N->bool.
        {w + z | w IN {x + y | x IN s /\ y IN t} /\ z IN u} =
        {x + v | x IN s /\ v IN {y + z | y IN t /\ z IN u}}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Infinitude of Euclidean space.                                            *)
(* ------------------------------------------------------------------------- *)

let EUCLIDEAN_SPACE_INFINITE = prove
 (`INFINITE(:real^N)`,
  REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `vec:num->real^N` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] FINITE_IMAGE_INJ)) THEN
  REWRITE_TAC[VEC_EQ; SET_RULE `{x | f x IN UNIV} = UNIV`] THEN
  REWRITE_TAC[GSYM INFINITE; num_INFINITE]);;

(* ------------------------------------------------------------------------- *)
(* Properties of the dot product.                                            *)
(* ------------------------------------------------------------------------- *)

let DOT_SYM = VECTOR_ARITH `!x y. x dot y = y dot x`;;

let DOT_LADD = VECTOR_ARITH `!x y z. (x + y) dot z = (x dot z) + (y dot z)`;;

let DOT_RADD = VECTOR_ARITH `!x y z. x dot (y + z) = (x dot y) + (x dot z)`;;

let DOT_LSUB = VECTOR_ARITH `!x y z. (x - y) dot z = (x dot z) - (y dot z)`;;

let DOT_RSUB = VECTOR_ARITH `!x y z. x dot (y - z) = (x dot y) - (x dot z)`;;

let DOT_LMUL = VECTOR_ARITH `!c x y. (c % x) dot y = c * (x dot y)`;;

let DOT_RMUL = VECTOR_ARITH `!c x y. x dot (c % y) = c * (x dot y)`;;

let DOT_LNEG = VECTOR_ARITH `!x y. (--x) dot y = --(x dot y)`;;

let DOT_RNEG = VECTOR_ARITH `!x y. x dot (--y) = --(x dot y)`;;

let DOT_LZERO = VECTOR_ARITH `!x. (vec 0) dot x = &0`;;

let DOT_RZERO = VECTOR_ARITH `!x. x dot (vec 0) = &0`;;

let DOT_POS_LE = prove
 (`!x. &0 <= x dot x`,
  SIMP_TAC[dot; SUM_POS_LE_NUMSEG; REAL_LE_SQUARE]);;

let DOT_EQ_0 = prove
 (`!x:real^N. ((x dot x = &0) <=> (x = vec 0))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[DOT_LZERO]] THEN
  SIMP_TAC[dot; CART_EQ; vec; LAMBDA_BETA] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[REAL_ENTIRE] `x * x = &0`)] THEN
  MATCH_MP_TAC SUM_POS_EQ_0_NUMSEG THEN ASM_REWRITE_TAC[REAL_LE_SQUARE]);;

let DOT_POS_LT = prove
 (`!x. (&0 < x dot x) <=> ~(x = vec 0)`,
  REWRITE_TAC[REAL_LT_LE; DOT_POS_LE] THEN MESON_TAC[DOT_EQ_0]);;

let FORALL_DOT_EQ_0 = prove
 (`(!y. (!x. x dot y = &0) <=> y = vec 0) /\
   (!x. (!y. x dot y = &0) <=> x = vec 0)`,
  MESON_TAC[DOT_LZERO; DOT_RZERO; DOT_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Introduce norms, but defer many properties till we get square roots.      *)
(* ------------------------------------------------------------------------- *)

make_overloadable "norm" `:A->real`;;
overload_interface("norm",`vector_norm:real^N->real`);;

let vector_norm = new_definition
  `norm x = sqrt(x dot x)`;;

(* ------------------------------------------------------------------------- *)
(* Useful for the special cases of 1 dimension.                              *)
(* ------------------------------------------------------------------------- *)

let FORALL_DIMINDEX_1 = prove
 (`(!i. 1 <= i /\ i <= dimindex(:1) ==> P i) <=> P 1`,
  MESON_TAC[DIMINDEX_1; LE_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* The collapse of the general concepts to the real line R^1.                *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ONE = prove
 (`!x:real^1. x = lambda i. x$1`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN MESON_TAC[DIMINDEX_1; LE_ANTISYM]);;

let FORALL_REAL_ONE = prove
 (`(!x:real^1. P x) <=> (!x. P(lambda i. x))`,
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^1)$1`) THEN
  REWRITE_TAC[GSYM VECTOR_ONE]);;

let NORM_REAL = prove
 (`!x:real^1. norm(x) = abs(x$1)`,
  REWRITE_TAC[vector_norm; dot; DIMINDEX_1; SUM_SING_NUMSEG;
              GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

(* ------------------------------------------------------------------------- *)
(* Metric function.                                                          *)
(* ------------------------------------------------------------------------- *)

override_interface("dist",`distance:real^N#real^N->real`);;

let dist = new_definition
  `dist(x,y) = norm(x - y)`;;

let DIST_REAL = prove
 (`!x:real^1 y. dist(x,y) = abs(x$1 - y$1)`,
  SIMP_TAC[dist; NORM_REAL; vector_sub; LAMBDA_BETA; LE_REFL; DIMINDEX_1]);;

(* ------------------------------------------------------------------------- *)
(* A connectedness or intermediate value lemma with several applications.    *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_REAL_LEMMA = prove
 (`!f:real->real^N a b e1 e2.
        a <= b /\ f(a) IN e1 /\ f(b) IN e2 /\
        (!e x. a <= x /\ x <= b /\ &0 < e
               ==> ?d. &0 < d /\
                       !y. abs(y - x) < d ==> dist(f(y),f(x)) < e) /\
        (!y. y IN e1 ==> ?e. &0 < e /\ !y'. dist(y',y) < e ==> y' IN e1) /\
        (!y. y IN e2 ==> ?e. &0 < e /\ !y'. dist(y',y) < e ==> y' IN e2) /\
        ~(?x. a <= x /\ x <= b /\ f(x) IN e1 /\ f(x) IN e2)
        ==> ?x. a <= x /\ x <= b /\ ~(f(x) IN e1) /\ ~(f(x) IN e2)`,
  let tac = ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TOTAL; REAL_LE_ANTISYM] in
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\c. !x. a <= x /\ x <= c ==> (f(x):real^N) IN e1`
              REAL_COMPLETE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [tac; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `a <= x /\ x <= b` STRIP_ASSUME_TAC THENL [tac; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z. a <= z /\ z < x ==> (f(z):real^N) IN e1` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN
     `?d. &0 < d /\ !y. abs(y - x) < d ==> (f(y):real^N) IN e1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ARITH `z <= x + e /\ e < d ==> z < x \/ abs(z - x) < d`;
                  REAL_ARITH `&0 < e ==> ~(x + e <= x)`; REAL_DOWN];
    SUBGOAL_THEN
     `?d. &0 < d /\ !y. abs(y - x) < d ==> (f(y):real^N) IN e2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`x - a`; `d:real`] REAL_DOWN2) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[REAL_LT_LE; REAL_SUB_LT]; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ARITH `e < x - a ==> a <= x - e`;
                  REAL_ARITH `&0 < e /\ x <= b ==> x - e <= b`;
      REAL_ARITH `&0 < e /\ e < d ==> x - e < x /\ abs((x - e) - x) < d`]]);;

(* ------------------------------------------------------------------------- *)
(* One immediately useful corollary is the existence of square roots!        *)
(* ------------------------------------------------------------------------- *)

let SQUARE_BOUND_LEMMA = prove
 (`!x. x < (&1 + x) * (&1 + x)`,
  GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_LE_SQUARE)) [`x:real`; `&1 + x`] THEN
  REAL_ARITH_TAC);;

let SQUARE_CONTINUOUS = prove
 (`!x e. &0 < e
         ==> ?d. &0 < d /\ !y. abs(y - x) < d ==> abs(y * y - x * x) < e`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    EXISTS_TAC `inv(&1 + inv(e))` THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_ADD; REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC  REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&1 + inv(e)) * inv(&1 + inv(e))` THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_LT_MUL2; REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQUARE_BOUND_LEMMA; REAL_LT_INV_EQ];
    MP_TAC(SPECL [`abs(x)`; `e / (&3 * abs(x))`] REAL_DOWN2)THEN
    ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT;
                 ARITH; REAL_LT_RDIV_EQ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN
    REWRITE_TAC[REAL_ARITH `x * x - y * y = (x - y) * (x + y)`] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `d * &3 * abs(x)` THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE] THEN
    MAP_EVERY UNDISCH_TAC [`abs (y - x) < d`; `d < abs(x)`] THEN
    REAL_ARITH_TAC]);;

let SQRT_WORKS_GEN = prove
 (`!x. real_sgn(sqrt x) = real_sgn x /\ sqrt(x) pow 2 = abs x`,
  GEN_TAC THEN REWRITE_TAC[sqrt] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `!x. &0 < x ==> ?y. &0 < y /\ y pow 2 = x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\u. lambda i. u):real->real^1`; `&0`; `&1 + x`;
            `{u:real^1 | u$1 * u$1 < x}`; `{u:real^1 | u$1 * u$1 > x}`]
         CONNECTED_REAL_LEMMA) THEN
    SIMP_TAC[LAMBDA_BETA; LE_REFL; DIMINDEX_1; DIST_REAL; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `~(x < y) /\ ~(x > y) <=> x = y`] THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LT_LE; REAL_ENTIRE]] THEN
    ASM_REWRITE_TAC[real_gt; SQUARE_BOUND_LEMMA; REAL_MUL_LZERO] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LT_ANTISYM]] THEN
    MESON_TAC[SQUARE_CONTINUOUS; REAL_SUB_LT;
              REAL_ARITH `abs(z2 - x2) < y - x2 ==> z2 < y`;
              REAL_ARITH `abs(z2 - x2) < x2 - y ==> y < z2`];
    ASM_CASES_TAC `x = &0` THEN
    ASM_REWRITE_TAC[REAL_SGN_0; REAL_SGN_EQ; UNWIND_THM2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `abs x`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `real_sgn x * y` THEN
    ASM_REWRITE_TAC[REAL_POW_MUL; GSYM REAL_SGN_POW; REAL_SGN_POW_2] THEN
    REWRITE_TAC[REAL_SGN_MUL; REAL_SGN_REAL_SGN] THEN
    ASM_SIMP_TAC[real_sgn; REAL_ARITH `&0 < abs x <=> ~(x = &0)`] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID]]);;

let SQRT_UNIQUE_GEN = prove
 (`!x y. real_sgn y = real_sgn x /\ y pow 2 = abs x ==> sqrt x = y`,
  REPEAT GEN_TAC THEN
  MP_TAC(GSYM(SPEC `x:real` SQRT_WORKS_GEN)) THEN
  SIMP_TAC[REAL_RING `x pow 2 = y pow 2 <=> x:real = y \/ x = --y`] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[IMP_CONJ_ALT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SGN_NEG] THEN
  SIMP_TAC[REAL_ARITH `--x = x <=> x = &0`; REAL_SGN_EQ; REAL_NEG_0; SQRT_0]);;

let SQRT_NEG = prove
 (`!x. sqrt(--x) = --sqrt(x)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_NEG; REAL_POW_NEG; REAL_ABS_NEG; ARITH] THEN
  REWRITE_TAC[SQRT_WORKS_GEN]);;

let REAL_SGN_SQRT = prove
 (`!x. real_sgn(sqrt x) = real_sgn x`,
  REWRITE_TAC[SQRT_WORKS_GEN]);;

let SQRT_WORKS = prove
 (`!x. &0 <= x ==> &0 <= sqrt(x) /\ sqrt(x) pow 2 = x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` SQRT_WORKS_GEN) THEN
  REWRITE_TAC[real_sgn] THEN ASM_REAL_ARITH_TAC);;

let SQRT_POS_LE = prove
 (`!x. &0 <= x ==> &0 <= sqrt(x)`,
  MESON_TAC[SQRT_WORKS]);;

let SQRT_POW_2 = prove
 (`!x. &0 <= x ==> sqrt(x) pow 2 = x`,
  MESON_TAC[SQRT_WORKS]);;

let SQRT_POW2 = prove
 (`!x. sqrt(x) pow 2 = x <=> &0 <= x`,
  MESON_TAC[REAL_POW_2; REAL_LE_SQUARE; SQRT_POW_2]);;

let SQRT_MUL = prove
 (`!x y. sqrt(x * y) = sqrt x * sqrt y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_MUL; REAL_POW_MUL; SQRT_WORKS_GEN; REAL_ABS_MUL]);;

let SQRT_INV = prove
 (`!x. sqrt (inv x) = inv(sqrt x)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_INV; REAL_POW_INV; REAL_ABS_INV; SQRT_WORKS_GEN]);;

let SQRT_DIV = prove
 (`!x y. sqrt (x / y) = sqrt x / sqrt y`,
  REWRITE_TAC[real_div; SQRT_MUL; SQRT_INV]);;

let SQRT_LT_0 = prove
 (`!x. &0 < sqrt x <=> &0 < x`,
  REWRITE_TAC[GSYM real_gt; GSYM REAL_SGN_EQ; REAL_SGN_SQRT]);;

let SQRT_EQ_0 = prove
 (`!x. sqrt x = &0 <=> x = &0`,
  ONCE_REWRITE_TAC[GSYM REAL_SGN_EQ] THEN REWRITE_TAC[REAL_SGN_SQRT]);;

let SQRT_LE_0 = prove
 (`!x. &0 <= sqrt x <=> &0 <= x`,
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> &0 < x \/ x = &0`] THEN
  REWRITE_TAC[SQRT_LT_0; SQRT_EQ_0]);;

let SQRT_MONO_LT = prove
 (`!x y. x < y ==> sqrt(x) < sqrt(y)`,
  SUBGOAL_THEN `!x y. &0 <= x /\ x < y ==> sqrt x < sqrt y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN
    EXISTS_TAC `2` THEN ASM_REWRITE_TAC[SQRT_WORKS_GEN; SQRT_LE_0] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= x` THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `&0 <= y` THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LE; SQRT_LE_0];
      FIRST_X_ASSUM(MP_TAC o SPECL [`--y:real`; `--x:real`]) THEN
      REWRITE_TAC[SQRT_NEG] THEN ASM_REAL_ARITH_TAC]]);;

let SQRT_MONO_LE = prove
 (`!x y. x <= y ==> sqrt(x) <= sqrt(y)`,
  MESON_TAC[REAL_LE_LT; SQRT_MONO_LT]);;

let SQRT_MONO_LT_EQ = prove
 (`!x y. sqrt(x) < sqrt(y) <=> x < y`,
  MESON_TAC[REAL_NOT_LT; SQRT_MONO_LT; SQRT_MONO_LE]);;

let SQRT_MONO_LE_EQ = prove
 (`!x y. sqrt(x) <= sqrt(y) <=> x <= y`,
  MESON_TAC[REAL_NOT_LT; SQRT_MONO_LT; SQRT_MONO_LE]);;

let SQRT_INJ = prove
 (`!x y. sqrt(x) = sqrt(y) <=> x = y`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; SQRT_MONO_LE_EQ]);;

let SQRT_POS_LT = prove
 (`!x. &0 < x ==> &0 < sqrt(x)`,
  MESON_TAC[REAL_LT_LE; SQRT_POS_LE; SQRT_EQ_0]);;

let REAL_LE_LSQRT = prove
 (`!x y. &0 <= y /\ x <= y pow 2 ==> sqrt(x) <= y`,
  MESON_TAC[SQRT_MONO_LE; REAL_POW_LE; POW_2_SQRT]);;

let REAL_LE_RSQRT = prove
 (`!x y. x pow 2 <= y ==> x <= sqrt(y)`,
  MESON_TAC[REAL_LE_TOTAL; SQRT_MONO_LE; SQRT_POS_LE; REAL_POW_2;
            REAL_LE_SQUARE; REAL_LE_TRANS; POW_2_SQRT]);;

let REAL_LT_LSQRT = prove
 (`!x y. &0 <= y /\ x < y pow 2 ==> sqrt x < y`,
  MESON_TAC[SQRT_MONO_LT; REAL_POW_LE; POW_2_SQRT]);;

let REAL_LT_RSQRT = prove
 (`!x y. x pow 2 < y ==> x < sqrt(y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs x < a ==> x < a`) THEN
  REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
  ASM_REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

let SQRT_EVEN_POW2 = prove
 (`!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))`,
  SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; DIV_MULT; ARITH_EQ] THEN
  MESON_TAC[SQRT_UNIQUE; REAL_POW_POW; MULT_SYM; REAL_POW_LE; REAL_POS]);;

let REAL_DIV_SQRT = prove
 (`!x. &0 <= x ==> x / sqrt(x) = sqrt(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SQRT_0; real_div; REAL_MUL_LZERO]] THEN
  ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; SQRT_POS_LT; GSYM REAL_POW_2] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]);;

let REAL_RSQRT_LE = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x <= sqrt y ==> x pow 2 <= y`,
  MESON_TAC[REAL_POW_LE2; SQRT_POW_2]);;

let REAL_LSQRT_LE = prove
 (`!x y. &0 <= x /\ sqrt x <= y ==> x <= y pow 2`,
  MESON_TAC[REAL_POW_LE2; SQRT_POS_LE; REAL_LE_TRANS; SQRT_POW_2]);;

let REAL_SQRT_POW_2 = prove
 (`!x. sqrt x pow 2 = abs x`,
  REWRITE_TAC[SQRT_WORKS_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Hence derive more interesting properties of the norm.                     *)
(* ------------------------------------------------------------------------- *)

let NORM_0 = prove
 (`norm(vec 0) = &0`,
  REWRITE_TAC[vector_norm; DOT_LZERO; SQRT_0]);;

let NORM_POS_LE = prove
 (`!x. &0 <= norm x`,
  GEN_TAC THEN SIMP_TAC[DOT_POS_LE; vector_norm; SQRT_POS_LE]);;

let NORM_NEG = prove
 (`!x. norm(--x) = norm x`,
  REWRITE_TAC[vector_norm; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG]);;

let NORM_SUB = prove
 (`!x y. norm(x - y) = norm(y - x)`,
  MESON_TAC[NORM_NEG; VECTOR_NEG_SUB]);;

let NORM_MUL = prove
 (`!a x. norm(a % x) = abs(a) * norm x`,
  REWRITE_TAC[vector_norm; DOT_LMUL; DOT_RMUL; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[SQRT_MUL; GSYM REAL_POW_2; REAL_SQRT_POW_2]);;

let NORM_EQ_0_DOT = prove
 (`!x. (norm x = &0) <=> (x dot x = &0)`,
  SIMP_TAC[vector_norm; SQRT_EQ_0; DOT_POS_LE]);;

let NORM_EQ_0 = prove
 (`!x. (norm x = &0) <=> (x = vec 0)`,
  SIMP_TAC[vector_norm; DOT_EQ_0; SQRT_EQ_0; DOT_POS_LE]);;

let NORM_POS_LT = prove
 (`!x. &0 < norm x <=> ~(x = vec 0)`,
  MESON_TAC[REAL_LT_LE; NORM_POS_LE; NORM_EQ_0]);;

let NORM_POW_2 = prove
 (`!x. norm(x) pow 2 = x dot x`,
  SIMP_TAC[vector_norm; SQRT_POW_2; DOT_POS_LE]);;

let NORM_EQ_0_IMP = prove
 (`!x. (norm x = &0) ==> (x = vec 0)`,
  MESON_TAC[NORM_EQ_0]);;

let NORM_LE_0 = prove
 (`!x. norm x <= &0 <=> (x = vec 0)`,
  MESON_TAC[REAL_LE_ANTISYM; NORM_EQ_0; NORM_POS_LE]);;

let VECTOR_MUL_EQ_0 = prove
 (`!a x. (a % x = vec 0) <=> (a = &0) \/ (x = vec 0)`,
  REWRITE_TAC[GSYM NORM_EQ_0; NORM_MUL; REAL_ABS_ZERO; REAL_ENTIRE]);;

let VECTOR_MUL_LCANCEL = prove
 (`!a x y. (a % x = a % y) <=> (a = &0) \/ (x = y)`,
  MESON_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_LDISTRIB; VECTOR_SUB_EQ]);;

let VECTOR_MUL_RCANCEL = prove
 (`!a b x. (a % x = b % x) <=> (a = b) \/ (x = vec 0)`,
  MESON_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_RDISTRIB; REAL_SUB_0; VECTOR_SUB_EQ]);;

let VECTOR_MUL_LCANCEL_IMP = prove
 (`!a x y. ~(a = &0) /\ (a % x = a % y) ==> (x = y)`,
  MESON_TAC[VECTOR_MUL_LCANCEL]);;

let VECTOR_MUL_RCANCEL_IMP = prove
 (`!a b x. ~(x = vec 0) /\ (a % x = b % x) ==> (a = b)`,
  MESON_TAC[VECTOR_MUL_RCANCEL]);;

let NORM_CAUCHY_SCHWARZ = prove
 (`!(x:real^N) y. x dot y <= norm(x) * norm(y)`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`norm(x:real^N) = &0`; `norm(y:real^N) = &0`] THEN
  ASM_SIMP_TAC[NORM_EQ_0_IMP; DOT_LZERO; DOT_RZERO;
               REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  MP_TAC(ISPEC `norm(y:real^N) % x - norm(x:real^N) % y` DOT_POS_LE) THEN
  REWRITE_TAC[DOT_RSUB; DOT_LSUB; DOT_LMUL; DOT_RMUL; GSYM NORM_POW_2;
              REAL_POW_2; REAL_LE_REFL] THEN
  REWRITE_TAC[DOT_SYM; REAL_ARITH
   `&0 <= y * (y * x * x - x * d) - x * (y * d - x * y * y) <=>
    x * y * d <= x * y * x * y`] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LE; NORM_POS_LE]);;

let NORM_CAUCHY_SCHWARZ_ABS = prove
 (`!x:real^N y. abs(x dot y) <= norm(x) * norm(y)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:real^N` NORM_CAUCHY_SCHWARZ) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `y:real^N` th) THEN
        MP_TAC(SPEC `--(y:real^N)` th)) THEN
  REWRITE_TAC[DOT_RNEG; NORM_NEG] THEN REAL_ARITH_TAC);;

let REAL_ABS_NORM = prove
 (`!x. abs(norm x) = norm x`,
  REWRITE_TAC[NORM_POS_LE; REAL_ABS_REFL]);;

let NORM_CAUCHY_SCHWARZ_DIV = prove
 (`!x:real^N y. abs((x dot y) / (norm x * norm y)) <= &1`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  ASM_REWRITE_TAC[NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO; real_div;
             REAL_INV_1; DOT_LZERO; DOT_RZERO; REAL_ABS_NUM; REAL_POS] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_LE_LDIV_EQ; REAL_LT_MUL;
     REAL_ABS_INV; NORM_POS_LT; REAL_ABS_MUL; REAL_ABS_NORM] THEN
  REWRITE_TAC[REAL_MUL_LID; NORM_CAUCHY_SCHWARZ_ABS]);;

let NORM_TRIANGLE = prove
 (`!x y. norm(x + y) <= norm(x) + norm(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_norm] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN
  SIMP_TAC[GSYM vector_norm; DOT_POS_LE; NORM_POS_LE; REAL_LE_ADD] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; REAL_POW_2; GSYM NORM_POW_2] THEN
  SIMP_TAC[NORM_CAUCHY_SCHWARZ; DOT_SYM; REAL_ARITH
   `d <= x * y ==> (x * x + d) + (d + y * y) <= (x + y) * (x + y)`]);;

let NORM_TRIANGLE_SUB = prove
 (`!x y:real^N. norm(x) <= norm(y) + norm(x - y)`,
  MESON_TAC[NORM_TRIANGLE; VECTOR_SUB_ADD2]);;

let NORM_TRIANGLE_LE = prove
 (`!x y. norm(x) + norm(y) <= e ==> norm(x + y) <= e`,
  MESON_TAC[REAL_LE_TRANS; NORM_TRIANGLE]);;

let NORM_TRIANGLE_LT = prove
 (`!x y. norm(x) + norm(y) < e ==> norm(x + y) < e`,
  MESON_TAC[REAL_LET_TRANS; NORM_TRIANGLE]);;

let COMPONENT_LE_NORM = prove
 (`!x:real^N i. abs(x$i) <= norm x`,
  REPEAT GEN_TAC THEN SUBGOAL_THEN
  `?k. 1 <= k /\ k <= dimindex(:N) /\ !x:real^N. x$i = x$k`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[vector_norm] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[GSYM REAL_ABS_POW] THEN
  REWRITE_TAC[real_abs; REAL_POW_2; REAL_LE_SQUARE] THEN
  SUBGOAL_THEN
   `x$k * (x:real^N)$k =
     sum(1..dimindex(:N)) (\i. if i = k then x$k * x$k else &0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_DELTA] THEN ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_SQUARE]);;

let NORM_BOUND_COMPONENT_LE = prove
 (`!x:real^N e. norm(x) <= e
                ==> !i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) <= e`,
  MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]);;

let NORM_BOUND_COMPONENT_LT = prove
 (`!x:real^N e. norm(x) < e
                ==> !i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) < e`,
  MESON_TAC[COMPONENT_LE_NORM; REAL_LET_TRANS]);;

let NORM_LE_L1 = prove
 (`!x:real^N. norm x <= sum(1..dimindex(:N)) (\i. abs(x$i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_norm; dot] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
  SIMP_TAC[SUM_POS_LE; FINITE_NUMSEG; REAL_LE_SQUARE; REAL_ABS_POS] THEN
  SPEC_TAC(`dimindex(:N)`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
  SIMP_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a2 <= a * a /\ &0 <= a * b /\ b2 <= b * b
    ==> a2 + b2 <= (a + b) * (a + b)`) THEN
  ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_MUL; REAL_ABS_POS; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC);;

let REAL_ABS_SUB_NORM = prove
 (`abs(norm(x) - norm(y)) <= norm(x - y)`,
  REWRITE_TAC[REAL_ARITH `abs(x - y) <= a <=> x <= y + a /\ y <= x + a`] THEN
  MESON_TAC[NORM_TRIANGLE_SUB; NORM_SUB]);;

let NORM_LE = prove
 (`!x y. norm(x) <= norm(y) <=> x dot x <= y dot y`,
  REWRITE_TAC[vector_norm] THEN MESON_TAC[SQRT_MONO_LE_EQ; DOT_POS_LE]);;

let NORM_LT = prove
 (`!x y. norm(x) < norm(y) <=> x dot x < y dot y`,
  REWRITE_TAC[vector_norm] THEN MESON_TAC[SQRT_MONO_LT_EQ; DOT_POS_LE]);;

let NORM_EQ = prove
 (`!x y. (norm x = norm y) <=> (x dot x = y dot y)`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; NORM_LE]);;

let NORM_EQ_1 = prove
 (`!x. norm(x) = &1 <=> x dot x = &1`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM SQRT_1] THEN
  SIMP_TAC[vector_norm; SQRT_INJ; DOT_POS_LE; REAL_POS]);;

let NORM_LE_COMPONENTWISE = prove
 (`!x:real^N y:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) <= abs(y$i))
        ==> norm(x) <= norm(y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LE; dot] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; GSYM REAL_LE_SQUARE_ABS]);;

let L1_LE_NORM = prove
 (`!x:real^N.
    sum(1..dimindex(:N)) (\i. abs(x$i)) <= sqrt(&(dimindex(:N))) * norm x`,
  let lemma = prove
   (`!x n. &n * sum(1..n) (\i. x i pow 2) - (sum(1..n) x) pow 2 =
           sum(1..n) (\i. sum(i+1..n) (\j. (x i - x j) pow 2))`,
    GEN_TAC THEN CONV_TAC(BINDER_CONV SYM_CONV) THEN INDUCT_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; ARITH_RULE `1 <= SUC n`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[ARITH_RULE `i <= n ==> i + 1 <= SUC n`; SUM_TRIV_NUMSEG;
             ARITH_RULE `~(n + 1 <= n)`; ARITH_RULE `n < SUC n + 1`] THEN
    ASM_REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_ARITH
     `(x - y) pow 2 = (x pow 2 + y pow 2) - &2 * x * y`] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_LMUL; SUM_RMUL;
                GSYM REAL_OF_NUM_SUC; SUM_CONST_NUMSEG; ADD_SUB] THEN
    REAL_ARITH_TAC) in
  GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ abs x <= abs y ==> x <= y`) THEN
  SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; SQRT_POS_LE; REAL_POS] THEN
  REWRITE_TAC[REAL_LE_SQUARE_ABS; REAL_POW_MUL] THEN
  SIMP_TAC[SQRT_POW_2; REAL_POS; NORM_POW_2; dot] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_POW2_ABS] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN REWRITE_TAC[lemma] THEN
  SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_POW_2]);;

(* ------------------------------------------------------------------------- *)
(* Squaring equations and inequalities involving norms.                      *)
(* ------------------------------------------------------------------------- *)

let DOT_SQUARE_NORM = prove
 (`!x. x dot x = norm(x) pow 2`,
  SIMP_TAC[vector_norm; SQRT_POW_2; DOT_POS_LE]);;

let NORM_EQ_SQUARE = prove
 (`!x:real^N. norm(x) = a <=> &0 <= a /\ x dot x = a pow 2`,
  REWRITE_TAC[DOT_SQUARE_NORM] THEN
  ONCE_REWRITE_TAC[REAL_RING `x pow 2 = a pow 2 <=> x = a \/ x + a = &0`] THEN
  GEN_TAC THEN MP_TAC(ISPEC `x:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC);;

let NORM_LE_SQUARE = prove
 (`!x:real^N. norm(x) <= a <=> &0 <= a /\ x dot x <= a pow 2`,
  REWRITE_TAC[DOT_SQUARE_NORM; GSYM REAL_LE_SQUARE_ABS] THEN
  GEN_TAC THEN MP_TAC(ISPEC `x:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC);;

let NORM_GE_SQUARE = prove
 (`!x:real^N. norm(x) >= a <=> a <= &0 \/ x dot x >= a pow 2`,
  REWRITE_TAC[real_ge; DOT_SQUARE_NORM; GSYM REAL_LE_SQUARE_ABS] THEN
  GEN_TAC THEN MP_TAC(ISPEC `x:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC);;

let NORM_LT_SQUARE = prove
 (`!x:real^N. norm(x) < a <=> &0 < a /\ x dot x < a pow 2`,
  REWRITE_TAC[REAL_ARITH `x < a <=> ~(x >= a)`; NORM_GE_SQUARE] THEN
  REAL_ARITH_TAC);;

let NORM_GT_SQUARE = prove
 (`!x:real^N. norm(x) > a <=> a < &0 \/ x dot x > a pow 2`,
  REWRITE_TAC[REAL_ARITH `x > a <=> ~(x <= a)`; NORM_LE_SQUARE] THEN
  REAL_ARITH_TAC);;

let NORM_LT_SQUARE_ALT = prove
 (`!x:real^N. norm(x) < a <=> &0 <= a /\ x dot x < a pow 2`,
  REWRITE_TAC[REAL_ARITH `x < a <=> ~(x >= a)`; NORM_GE_SQUARE] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = &0` THENL
   [ASM_REWRITE_TAC[real_ge] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[DOT_POS_LE];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* General linear decision procedure for normed spaces.                      *)
(* ------------------------------------------------------------------------- *)

let NORM_ARITH =
  let find_normedterms =
    let augment_norm b tm acc =
      match tm with
        Comb(Const("vector_norm",_),v) -> insert (b,v) acc
      | _ -> acc in
    let rec find_normedterms tm acc =
      match tm with
        Comb(Comb(Const("real_add",_),l),r) ->
            find_normedterms l (find_normedterms r acc)
      | Comb(Comb(Const("real_mul",_),c),n) ->
            if not (is_ratconst c) then acc else
            augment_norm (rat_of_term c >=/ Int 0) n acc
      | _ -> augment_norm true tm acc in
    find_normedterms in
  let lincomb_neg t = mapf minus_num t in
  let lincomb_cmul c t = if c =/ Int 0 then undefined else mapf (( */ ) c) t in
  let lincomb_add l r = combine (+/) (fun x -> x =/ Int 0) l r in
  let lincomb_sub l r = lincomb_add l (lincomb_neg r) in
  let lincomb_eq l r = lincomb_sub l r = undefined in
  let rec vector_lincomb tm =
    match tm with
        Comb(Comb(Const("vector_add",_),l),r) ->
          lincomb_add (vector_lincomb l) (vector_lincomb r)
      | Comb(Comb(Const("vector_sub",_),l),r) ->
          lincomb_sub (vector_lincomb l) (vector_lincomb r)
      | Comb(Comb(Const("%",_),l),r) ->
          lincomb_cmul (rat_of_term l) (vector_lincomb r)
      | Comb(Const("vector_neg",_),t) ->
          lincomb_neg (vector_lincomb t)
      | Comb(Const("vec",_),n) when is_numeral n & dest_numeral n =/ Int 0 ->
          undefined
      | _ -> (tm |=> Int 1) in
  let vector_lincombs tms =
    itlist (fun t fns ->
                  if can (assoc t) fns then fns else
                  let f = vector_lincomb t in
                  try let _,f' = find (fun (_,f') -> lincomb_eq f f') fns in
                      (t,f')::fns
                  with Failure _ -> (t,f)::fns) tms [] in
  let rec replacenegnorms fn tm =
    match tm with
      Comb(Comb(Const("real_add",_),l),r) ->
          BINOP_CONV (replacenegnorms fn) tm
    | Comb(Comb(Const("real_mul",_),c),n) when rat_of_term c </ Int 0 ->
          RAND_CONV fn tm
    | _ -> REFL tm in
  let flip v eq =
    if defined eq v then (v |-> minus_num(apply eq v)) eq else eq in
  let rec allsubsets s =
    match s with
      [] -> [[]]
    | (a::t) -> let res = allsubsets t in
                map (fun b -> a::b) res @ res in
  let evaluate env lin =
    foldr (fun x c s -> s +/ c */ apply env x) lin (Int 0) in
  let rec solve (vs,eqs) =
    match (vs,eqs) with
      [],[] -> (0 |=> Int 1)
    | _,eq::oeqs ->
          let v = hd(intersect vs (dom eq)) in
          let c = apply eq v in
          let vdef = lincomb_cmul (Int(-1) // c) eq in
          let eliminate eqn =
            if not(defined eqn v) then eqn else
            lincomb_add (lincomb_cmul (apply eqn v) vdef) eqn in
          let soln = solve (subtract vs [v],map eliminate oeqs) in
          (v |-> evaluate soln (undefine v vdef)) soln in
  let rec combinations k l =
    if k = 0 then [[]] else
    match l with
      [] -> []
    | h::t -> map (fun c -> h::c) (combinations (k - 1) t) @
              combinations k t in
  let vertices vs eqs =
    let vertex cmb =
      let soln = solve(vs,cmb) in
      map (fun v -> tryapplyd soln v (Int 0)) vs in
    let rawvs = mapfilter vertex (combinations (length vs) eqs) in
    let unset = filter (forall (fun c -> c >=/ Int 0)) rawvs in
    itlist (insert' (forall2 (=/))) unset [] in
  let subsumes l m = forall2 (fun x y -> abs_num x <=/ abs_num y) l m in
  let rec subsume todo dun =
    match todo with
      [] -> dun
    | v::ovs -> let dun' = if exists (fun w -> subsumes w v) dun then dun
                           else v::(filter (fun w -> not(subsumes v w)) dun) in
                subsume ovs dun' in
  let NORM_CMUL_RULE =
    let MATCH_pth = (MATCH_MP o prove)
     (`!b x. b >= norm(x) ==> !c. abs(c) * b >= norm(c % x)`,
      SIMP_TAC[NORM_MUL; real_ge; REAL_LE_LMUL; REAL_ABS_POS]) in
    fun c th -> ISPEC(term_of_rat c) (MATCH_pth th) in
  let NORM_ADD_RULE =
    let MATCH_pth = (MATCH_MP o prove)
     (`!b1 b2 x1 x2. b1 >= norm(x1) /\ b2 >= norm(x2)
                     ==> b1 + b2 >= norm(x1 + x2)`,
      REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC NORM_TRIANGLE_LE THEN ASM_SIMP_TAC[REAL_LE_ADD2]) in
    fun th1 th2 -> MATCH_pth (CONJ th1 th2) in
  let INEQUALITY_CANON_RULE =
    CONV_RULE(LAND_CONV REAL_POLY_CONV) o
    CONV_RULE(LAND_CONV REAL_RAT_REDUCE_CONV) o
    GEN_REWRITE_RULE I [REAL_ARITH `s >= t <=> s - t >= &0`] in
  let NORM_CANON_CONV =
    let APPLY_pth1 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `x:real^N = &1 % x`]
    and APPLY_pth2 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `x - y:real^N = x + --y`]
    and APPLY_pth3 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `--x:real^N = -- &1 % x`]
    and APPLY_pth4 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `&0 % x:real^N = vec 0`;
      VECTOR_ARITH `c % vec 0:real^N = vec 0`]
    and APPLY_pth5 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `c % (d % x) = (c * d) % x`]
    and APPLY_pth6 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `c % (x + y) = c % x + c % y`]
    and APPLY_pth7 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `vec 0 + x = x`;
      VECTOR_ARITH `x + vec 0 = x`]
    and APPLY_pth8 =
     GEN_REWRITE_CONV I [VECTOR_ARITH `c % x + d % x = (c + d) % x`] THENC
     LAND_CONV REAL_RAT_ADD_CONV THENC
     GEN_REWRITE_CONV TRY_CONV [VECTOR_ARITH `&0 % x = vec 0`]
    and APPLY_pth9 =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `(c % x + z) + d % x = (c + d) % x + z`;
       VECTOR_ARITH `c % x + (d % x + z) = (c + d) % x + z`;
       VECTOR_ARITH `(c % x + w) + (d % x + z) = (c + d) % x + (w + z)`] THENC
     LAND_CONV(LAND_CONV REAL_RAT_ADD_CONV)
    and APPLY_ptha =
     GEN_REWRITE_CONV I [VECTOR_ARITH `&0 % x + y = y`]
    and APPLY_pthb =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `c % x + d % y = c % x + d % y`;
       VECTOR_ARITH `(c % x + z) + d % y = c % x + (z + d % y)`;
       VECTOR_ARITH `c % x + (d % y + z) = c % x + (d % y + z)`;
       VECTOR_ARITH `(c % x + w) + (d % y + z) = c % x + (w + (d % y + z))`]
    and APPLY_pthc =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `c % x + d % y = d % y + c % x`;
       VECTOR_ARITH `(c % x + z) + d % y = d % y + (c % x + z)`;
       VECTOR_ARITH `c % x + (d % y + z) = d % y + (c % x + z)`;
       VECTOR_ARITH `(c % x + w) + (d % y + z) = d % y + ((c % x + w) + z)`]
    and APPLY_pthd =
     GEN_REWRITE_CONV TRY_CONV
      [VECTOR_ARITH `x + vec 0 = x`] in
    let headvector tm =
      match tm with
        Comb(Comb(Const("vector_add",_),Comb(Comb(Const("%",_),l),v)),r) -> v
      | Comb(Comb(Const("%",_),l),v) -> v
      | _ -> failwith "headvector: non-canonical term" in
    let rec VECTOR_CMUL_CONV tm =
     ((APPLY_pth5 THENC LAND_CONV REAL_RAT_MUL_CONV) ORELSEC
      (APPLY_pth6 THENC BINOP_CONV VECTOR_CMUL_CONV)) tm
    and VECTOR_ADD_CONV tm =
      try APPLY_pth7 tm with Failure _ ->
      try APPLY_pth8 tm with Failure _ ->
      match tm with
        Comb(Comb(Const("vector_add",_),lt),rt) ->
          let l = headvector lt and r = headvector rt in
          if l < r then (APPLY_pthb THENC
                         RAND_CONV VECTOR_ADD_CONV THENC
                         APPLY_pthd) tm
          else if r < l then (APPLY_pthc THENC
                              RAND_CONV VECTOR_ADD_CONV THENC
                              APPLY_pthd) tm else
          (APPLY_pth9 THENC
            ((APPLY_ptha THENC VECTOR_ADD_CONV) ORELSEC
             RAND_CONV VECTOR_ADD_CONV THENC
             APPLY_pthd)) tm
      | _ -> REFL tm in
    let rec VECTOR_CANON_CONV tm =
      match tm with
        Comb(Comb(Const("vector_add",_),l),r) ->
          let lth = VECTOR_CANON_CONV l and rth = VECTOR_CANON_CONV r in
          let th = MK_COMB(AP_TERM (rator(rator tm)) lth,rth) in
          CONV_RULE (RAND_CONV VECTOR_ADD_CONV) th
      | Comb(Comb(Const("%",_),l),r) ->
          let rth = AP_TERM (rator tm) (VECTOR_CANON_CONV r) in
          CONV_RULE (RAND_CONV(APPLY_pth4 ORELSEC VECTOR_CMUL_CONV)) rth
      | Comb(Comb(Const("vector_sub",_),l),r) ->
          (APPLY_pth2 THENC VECTOR_CANON_CONV) tm
      | Comb(Const("vector_neg",_),t) ->
          (APPLY_pth3 THENC VECTOR_CANON_CONV) tm
      | Comb(Const("vec",_),n) when is_numeral n & dest_numeral n =/ Int 0 ->
          REFL tm
      | _ -> APPLY_pth1 tm in
    fun tm ->
      match tm with
       Comb(Const("vector_norm",_),e) -> RAND_CONV VECTOR_CANON_CONV tm
      | _ -> failwith "NORM_CANON_CONV" in
  let REAL_VECTOR_COMBO_PROVER =
    let pth_zero = prove(`norm(vec 0:real^N) = &0`,REWRITE_TAC[NORM_0])
    and tv_n = mk_vartype "N" in
    fun translator (nubs,ges,gts) ->
      let sources = map (rand o rand o concl) nubs
      and rawdests = itlist (find_normedterms o lhand o concl) (ges @ gts) [] in
      if not (forall fst rawdests) then failwith "Sanity check" else
      let dests = setify (map snd rawdests) in
      let srcfuns = map vector_lincomb sources
      and destfuns = map vector_lincomb dests in
      let vvs = itlist (union o dom) (srcfuns @ destfuns) [] in
      let n = length srcfuns in
      let nvs = 1--n in
      let srccombs = zip srcfuns nvs in
      let consider d =
        let coefficients x =
            let inp = if defined d x then 0 |=> minus_num(apply d x)
                      else undefined in
          itlist (fun (f,v) g -> if defined f x then (v |-> apply f x) g else g)
                 srccombs inp in
        let equations = map coefficients vvs
        and inequalities = map (fun n -> (n |=> Int 1)) nvs in
        let plausiblevertices f =
          let flippedequations = map (itlist flip f) equations in
          let constraints = flippedequations @ inequalities in
          let rawverts = vertices nvs constraints in
          let check_solution v =
            let f = itlist2 (|->) nvs v (0 |=> Int 1) in
            forall (fun e -> evaluate f e =/ Int 0) flippedequations in
          let goodverts = filter check_solution rawverts in
          let signfixups = map (fun n -> if mem n f then -1 else 1) nvs in
          map (map2 (fun s c -> Int s */ c) signfixups) goodverts in
        let allverts = itlist (@) (map plausiblevertices (allsubsets nvs)) [] in
        subsume allverts [] in
      let compute_ineq v =
        let ths = mapfilter (fun (v,t) -> if v =/ Int 0 then fail()
                                          else  NORM_CMUL_RULE v t)
                            (zip v nubs) in
        INEQUALITY_CANON_RULE (end_itlist NORM_ADD_RULE ths) in
      let ges' = mapfilter compute_ineq (itlist ((@) o consider) destfuns []) @
                 map INEQUALITY_CANON_RULE nubs @ ges in
      let zerodests = filter
        (fun t -> dom(vector_lincomb t) = []) (map snd rawdests) in
      REAL_LINEAR_PROVER translator
       (map (fun t -> INST_TYPE [last(snd(dest_type(type_of t))),tv_n] pth_zero)
            zerodests,
        map (CONV_RULE(ONCE_DEPTH_CONV NORM_CANON_CONV THENC
                       LAND_CONV REAL_POLY_CONV)) ges',
        map (CONV_RULE(ONCE_DEPTH_CONV NORM_CANON_CONV THENC
                       LAND_CONV REAL_POLY_CONV)) gts) in
  let REAL_VECTOR_INEQ_PROVER =
    let pth = prove
     (`norm(x) = n ==> norm(x) >= &0 /\ n >= norm(x)`,
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[real_ge; NORM_POS_LE] THEN REAL_ARITH_TAC) in
    let NORM_MP = MATCH_MP pth in
    fun translator (ges,gts) ->
    let ntms = itlist find_normedterms (map (lhand o concl) (ges @ gts)) [] in
    let lctab = vector_lincombs (map snd (filter (not o fst) ntms)) in
    let asl = map (fun (t,_) ->
       ASSUME(mk_eq(mk_icomb(mk_const("vector_norm",[]),t),
                    genvar `:real`))) lctab in
    let replace_conv = GEN_REWRITE_CONV TRY_CONV asl in
    let replace_rule = CONV_RULE (LAND_CONV (replacenegnorms replace_conv)) in
    let ges' =
       itlist (fun th ths -> CONJUNCT1(NORM_MP th)::ths)
              asl (map replace_rule ges)
    and gts' = map replace_rule gts
    and nubs = map (CONJUNCT2 o NORM_MP) asl in
    let th1 = REAL_VECTOR_COMBO_PROVER translator (nubs,ges',gts') in
    let th2 = INST
     (map (fun th -> let l,r = dest_eq(concl th) in (l,r)) asl) th1 in
    itlist PROVE_HYP (map (REFL o lhand o concl) asl) th2 in
  let REAL_VECTOR_PROVER =
    let rawrule =
      GEN_REWRITE_RULE I [REAL_ARITH `x = &0 <=> x >= &0 /\ --x >= &0`] in
    let splitequation th acc =
      let th1,th2 = CONJ_PAIR(rawrule th) in
      th1::CONV_RULE(LAND_CONV REAL_POLY_NEG_CONV) th2::acc in
    fun translator (eqs,ges,gts) ->
      REAL_VECTOR_INEQ_PROVER translator
         (itlist splitequation eqs ges,gts) in
  let pth = prove
   (`(!x y:real^N. x = y <=> norm(x - y) <= &0) /\
     (!x y:real^N. ~(x = y) <=> ~(norm(x - y) <= &0))`,
    REWRITE_TAC[NORM_LE_0; VECTOR_SUB_EQ]) in
  let conv1 = GEN_REWRITE_CONV TRY_CONV [pth] in
  let conv2 tm = (conv1 tm,conv1(mk_neg tm)) in
  let init = GEN_REWRITE_CONV ONCE_DEPTH_CONV [DECIMAL] THENC
             REAL_RAT_REDUCE_CONV THENC
             GEN_REWRITE_CONV ONCE_DEPTH_CONV [dist] THENC
             GEN_NNF_CONV true (conv1,conv2)
  and pure = GEN_REAL_ARITH REAL_VECTOR_PROVER in
  fun tm -> let th = init tm in EQ_MP (SYM th) (pure(rand(concl th)));;

let NORM_ARITH_TAC = CONV_TAC NORM_ARITH;;

let ASM_NORM_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  NORM_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* There are no non-trivial homomorphisms R->R                               *)
(* ------------------------------------------------------------------------- *)

let HOMOMORPHISM_REAL_TO_REAL = prove
 (`!f:real->real.
        (!x y. f(x + y) = f x + f y) /\ (!x y. f(x * y) = f x * f y) <=>
        (f = \x. &0) \/ (f = \x. x)`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LZERO] THEN
  REWRITE_TAC[FUN_EQ_THM; TAUT `p \/ q <=> ~p ==> q`] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real->real)(&0) = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_EQ_ADD_LCANCEL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real)(&1) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_MUL_LID; REAL_RING `x = y * x <=> y = &1 \/ x = &0`];
    FIRST_X_ASSUM(CHOOSE_THEN (K ALL_TAC))] THEN
  SUBGOAL_THEN `!x. (f:real->real)(--x) = --(f x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `x:real = --y <=> x + y = &0`]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. (f:real->real)(x - y) = f x - f y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[real_sub]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. (f:real->real) x = &0 <=> x = &0` ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real = &0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:real->real)(inv x * x) = f(&1)` MP_TAC THENL
     [ASM_MESON_TAC[REAL_MUL_LINV]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. (f:real->real) x = f y <=> x = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_SUB_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x <= y ==> (f:real->real) x <= f y` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM th]) THEN
    SPEC_TAC(`y - x:real`,`z:real`) THEN GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM SQRT_POW2] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. (f:real->real) x <= f y <=> x <= y` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LE_ANTISYM]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. (f:real->real) x < f y <=> x < y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_NOT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (f:real->real)(&n) = &n` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. integer x ==> f x = x` ASSUME_TAC THENL
   [REWRITE_TAC[is_int] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. rational x ==> f x = x` ASSUME_TAC THENL
   [REWRITE_TAC[rational; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real`; `x:real`; `y:real`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[REAL_FIELD
     `~(y = &0) ==> (z = x / y <=> y * z = x)`] THEN
    TRANS_TAC EQ_TRANS `(f:real->real) y * f(x / y)` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN
  MATCH_MP_TAC(REAL_ARITH `~(x < y) /\ ~(y < x) ==> x:real = y`) THEN
  CONJ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` MP_TAC o MATCH_MP RATIONAL_BETWEEN) THEN
  ASM_MESON_TAC[REAL_LT_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Dot product in terms of the norm rather than conversely.                  *)
(* ------------------------------------------------------------------------- *)

let DOT_NORM = prove
 (`!x y. x dot y = (norm(x + y) pow 2 - norm(x) pow 2 - norm(y) pow 2) / &2`,
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_SYM] THEN REAL_ARITH_TAC);;

let DOT_NORM_NEG = prove
 (`!x y. x dot y = ((norm(x) pow 2 + norm(y) pow 2) - norm(x - y) pow 2) / &2`,
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  REAL_ARITH_TAC);;

let DOT_NORM_SUB = prove
 (`!x y. x dot y = ((norm(x) pow 2 + norm(y) pow 2) - norm(x - y) pow 2) / &2`,
  REWRITE_TAC[NORM_POW_2; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Equality of vectors in terms of dot products.                             *)
(* ------------------------------------------------------------------------- *)

let VECTOR_EQ = prove
 (`!x y. (x = y) <=> (x dot x = x dot y) /\ (y dot y = x dot x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM DOT_EQ_0] THEN
  SIMP_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence more metric properties.                                             *)
(* ------------------------------------------------------------------------- *)

let DIST_REFL = prove
 (`!x. dist(x,x) = &0`,
  NORM_ARITH_TAC);;

let DIST_SYM = prove
 (`!x y. dist(x,y) = dist(y,x)`,
  NORM_ARITH_TAC);;

let DIST_POS_LE = prove
 (`!x y. &0 <= dist(x,y)`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE = prove
 (`!x:real^N y z. dist(x,z) <= dist(x,y) + dist(y,z)`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_ALT = prove
 (`!x y z. dist(y,z) <= dist(x,y) + dist(x,z)`,
  NORM_ARITH_TAC);;

let DIST_EQ_0 = prove
 (`!x y. (dist(x,y) = &0) <=> (x = y)`,
  NORM_ARITH_TAC);;

let DIST_POS_LT = prove
 (`!x y. ~(x = y) ==> &0 < dist(x,y)`,
  NORM_ARITH_TAC);;

let DIST_NZ = prove
 (`!x y. ~(x = y) <=> &0 < dist(x,y)`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_LE = prove
 (`!x y z e. dist(x,z) + dist(y,z) <= e ==> dist(x,y) <= e`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_LT = prove
 (`!x y z e. dist(x,z) + dist(y,z) < e ==> dist(x,y) < e`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_HALF_L = prove
 (`!x1 x2 y. dist(x1,y) < e / &2 /\ dist(x2,y) < e / &2 ==> dist(x1,x2) < e`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_HALF_R = prove
 (`!x1 x2 y. dist(y,x1) < e / &2 /\ dist(y,x2) < e / &2 ==> dist(x1,x2) < e`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_ADD = prove
 (`!x x' y y'. dist(x + y,x' + y') <= dist(x,x') + dist(y,y')`,
  NORM_ARITH_TAC);;

let DIST_MUL = prove
 (`!x y c. dist(c % x,c % y) = abs(c) * dist(x,y)`,
  REWRITE_TAC[dist; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL]);;

let DIST_TRIANGLE_ADD_HALF = prove
 (`!x x' y y':real^N.
    dist(x,x') < e / &2 /\ dist(y,y') < e / &2 ==> dist(x + y,x' + y') < e`,
  NORM_ARITH_TAC);;

let DIST_LE_0 = prove
 (`!x y. dist(x,y) <= &0 <=> x = y`,
  NORM_ARITH_TAC);;

let DIST_EQ = prove
 (`!w x y z. dist(w,x) = dist(y,z) <=> dist(w,x) pow 2 = dist(y,z) pow 2`,
  REWRITE_TAC[dist; NORM_POW_2; NORM_EQ]);;

let DIST_0 = prove
 (`!x. dist(x,vec 0) = norm(x) /\ dist(vec 0,x) = norm(x)`,
  NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bounding distances between scaled versions of vectors.                    *)
(* ------------------------------------------------------------------------- *)

let DIST_RESCALE = prove
 (`!a x y:real^N. norm(x) = norm(y) ==> dist(a % x,y) = dist(x,a % y)`,
  SIMP_TAC[dist; NORM_EQ_SQUARE; NORM_POS_LE; NORM_POW_2] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
  CONV_TAC REAL_RING);;

let DIST_DESCALE = prove
 (`!a b x y:real^N.
        &0 <= a /\ &0 <= b /\ norm(x) = norm(y)
        ==> dist(a % x,b % y) >= min a b * dist(x,y)`,
  MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
   [MESON_TAC[DIST_SYM; REAL_ARITH `min a b:real = min b a`]; ALL_TAC] THEN
  SIMP_TAC[real_min] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[dist; NORM_GE_SQUARE; REAL_POW_MUL; NORM_POW_2] THEN
  DISJ2_TAC THEN REWRITE_TAC[real_ge] THEN REWRITE_TAC[VECTOR_ARITH
   `(x - y:real^N) dot (x - y) = (x dot x + y dot y) - &2 * x dot y`] THEN
  ASM_REWRITE_TAC[GSYM NORM_POW_2; NORM_MUL; real_abs; REAL_ARITH
   `a pow 2 * ((y pow 2 + y pow 2) - &2 * d) <=
    ((a * y) pow 2 + (b * y) pow 2) - &2 * e <=>
    &2 * (e - a pow 2 * d) <= (b pow 2 - a pow 2) * y pow 2`] THEN
  REWRITE_TAC[DOT_LMUL] THEN REWRITE_TAC[DOT_RMUL] THEN
  REWRITE_TAC[REAL_POW2_ABS; REAL_MUL_ASSOC; GSYM REAL_SUB_RDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH `abs a <= b ==> a <= b`) THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN TRANS_TAC REAL_LE_TRANS
    `abs (&2 * (a * b - a pow 2)) * norm(x:real^N) * norm(y:real^N)` THEN
  SIMP_TAC[REAL_LE_LMUL; REAL_ABS_POS; NORM_CAUCHY_SCHWARZ_ABS] THEN
  ASM_REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  REWRITE_TAC[REAL_ARITH `(a * b - a pow 2):real = a * (b - a)`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_SUB_LE] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; REAL_ARITH
   `(b pow 2 - a pow 2):real = (a + b) * (b - a)`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sums of vectors.                                                          *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_VECTOR_ADD = prove
 (`neutral(+) = vec 0:real^N`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[VECTOR_ARITH `x + y = y <=> x = vec 0`;
              VECTOR_ARITH `x + y = x <=> y = vec 0`]);;

let MONOIDAL_VECTOR_ADD = prove
 (`monoidal((+):real^N->real^N->real^N)`,
  REWRITE_TAC[monoidal; NEUTRAL_VECTOR_ADD] THEN
  REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);;

let vsum = new_definition
  `(vsum:(A->bool)->(A->real^N)->real^N) s f = lambda i. sum s (\x. f(x)$i)`;;

let VSUM_CLAUSES = prove
 (`(!f. vsum {} f = vec 0) /\
   (!x f s. FINITE s
            ==> (vsum (x INSERT s) f =
                 if x IN s then vsum s f else f(x) + vsum s f))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; SUM_CLAUSES] THEN
  SIMP_TAC[VEC_COMPONENT] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT]);;

let VSUM = prove
 (`!f s. FINITE s ==> vsum s f = iterate (+) s f`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; ITERATE_CLAUSES; MONOIDAL_VECTOR_ADD] THEN
  REWRITE_TAC[NEUTRAL_VECTOR_ADD]);;

let VSUM_EQ_0 = prove
 (`!f s. (!x:A. x IN s ==> (f(x) = vec 0)) ==> (vsum s f = vec 0)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; vec; SUM_EQ_0]);;

let VSUM_0 = prove
 (`vsum s (\x. vec 0) = vec 0`,
  SIMP_TAC[VSUM_EQ_0]);;

let VSUM_LMUL = prove
 (`!f c s.  vsum s (\x. c % f(x)) = c % vsum s f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT; SUM_LMUL]);;

let VSUM_RMUL = prove
 (`!c s v. vsum s (\x. c x % v) = (sum s c) % v`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT; SUM_RMUL]);;

let VSUM_ADD = prove
 (`!f g s. FINITE s ==> (vsum s (\x. f x + g x) = vsum s f + vsum s g)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; SUM_ADD]);;

let VSUM_SUB = prove
 (`!f g s. FINITE s ==> (vsum s (\x. f x - g x) = vsum s f - vsum s g)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_SUB_COMPONENT; SUM_SUB]);;

let VSUM_CONST = prove
 (`!c s. FINITE s ==> (vsum s (\n. c) = &(CARD s) % c)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_CONST; VECTOR_MUL_COMPONENT]);;

let VSUM_COMPONENT = prove
 (`!s f i. 1 <= i /\ i <= dimindex(:N)
           ==> ((vsum s (f:A->real^N))$i = sum s (\x. f(x)$i))`,
  SIMP_TAC[vsum; LAMBDA_BETA]);;

let VSUM_IMAGE = prove
 (`!f g s. FINITE s /\ (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (vsum (IMAGE f s) g = vsum s (g o f))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhs o snd) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let VSUM_UNION = prove
 (`!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (vsum (s UNION t) f = vsum s f + vsum t f)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_UNION; VECTOR_ADD_COMPONENT]);;

let VSUM_DIFF = prove
 (`!f s t. FINITE s /\ t SUBSET s
           ==> (vsum (s DIFF t) f = vsum s f - vsum t f)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_DIFF; VECTOR_SUB_COMPONENT]);;

let VSUM_DELETE = prove
 (`!f s a. FINITE s /\ a IN s
           ==> vsum (s DELETE a) f = vsum s f - f a`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_DELETE; VECTOR_SUB_COMPONENT]);;

let VSUM_INCL_EXCL = prove
 (`!s t (f:A->real^N).
        FINITE s /\ FINITE t
        ==> vsum s f + vsum t f = vsum (s UNION t) f + vsum (s INTER t) f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT] THEN
  SIMP_TAC[SUM_INCL_EXCL]);;

let VSUM_NEG = prove
 (`!f s. vsum s (\x. --f x) = --vsum s f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_NEG; VECTOR_NEG_COMPONENT]);;

let VSUM_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (vsum s f = vsum s g)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]);;

let VSUM_SUPERSET = prove
 (`!f:A->real^N u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = vec 0))
        ==> (vsum v f = vsum u f)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_SUPERSET]);;

let VSUM_SUPPORT = prove
 (`!f:A->real^N s. vsum {x | x IN s /\ ~(f x = vec 0)} f = vsum s f`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
  SET_TAC[]);;

let VSUM_EQ_SUPERSET = prove
 (`!f s t:A->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> f(x) = vec 0)
        ==> vsum s f = vsum t g`,
  MESON_TAC[VSUM_SUPERSET; VSUM_EQ]);;

let VSUM_UNION_RZERO = prove
 (`!f:A->real^N u v.
        (!x. x IN v /\ ~(x IN u) ==> (f(x) = vec 0))
        ==> (vsum (u UNION v) f = vsum u f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN ASM SET_TAC[]);;

let VSUM_UNION_LZERO = prove
 (`!f:A->real^N u v.
        (!x. x IN u /\ ~(x IN v) ==> (f(x) = vec 0))
        ==> (vsum (u UNION v) f = vsum v f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN ASM SET_TAC[]);;

let VSUM_RESTRICT = prove
 (`!f s. vsum s (\x. if x IN s then f(x) else vec 0) = vsum s f`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[]);;

let VSUM_RESTRICT_SET = prove
 (`!P s f. vsum {x | x IN s /\ P x} f =
           vsum s (\x. if P x then f x else vec 0)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_RESTRICT_SET;
           COND_COMPONENT]);;

let VSUM_CASES = prove
 (`!s P f g. FINITE s
             ==> vsum s (\x:A. if P x then (f x):real^N else g x) =
                 vsum {x | x IN s /\ P x} f + vsum {x | x IN s /\ ~P x} g`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; SUM_CASES;
           COND_COMPONENT]);;

let VSUM_SING = prove
 (`!f x. vsum {x} f = f(x)`,
  SIMP_TAC[VSUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; VECTOR_ADD_RID]);;

let VSUM_NORM = prove
 (`!f s. FINITE s ==> norm(vsum s f) <= sum s (\x. norm(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; NORM_0; REAL_LE_REFL] THEN
  NORM_ARITH_TAC);;

let VSUM_NORM_LE = prove
 (`!s f:A->real^N g.
        FINITE s /\ (!x. x IN s ==> norm(f x) <= g(x))
        ==> norm(vsum s f) <= sum s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x:A. norm(f x :real^N))` THEN
  ASM_SIMP_TAC[VSUM_NORM; SUM_LE]);;

let VSUM_NORM_TRIANGLE = prove
 (`!s f b. FINITE s /\ sum s (\a. norm(f a)) <= b ==> norm(vsum s f) <= b`,
  MESON_TAC[VSUM_NORM; REAL_LE_TRANS]);;

let VSUM_NORM_BOUND = prove
 (`!s f b. FINITE s /\ (!x:A. x IN s ==> norm(f(x)) <= b)
           ==> norm(vsum s f) <= &(CARD s) * b`,
  SIMP_TAC[GSYM SUM_CONST; VSUM_NORM_LE]);;

let VSUM_CLAUSES_NUMSEG = prove
 (`(!m. vsum(m..0) f = if m = 0 then f(0) else vec 0) /\
   (!m n. vsum(m..SUC n) f = if m <= SUC n then vsum(m..n) f + f(SUC n)
                             else vsum(m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[VSUM_SING; VSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; VECTOR_ADD_AC]);;

let VSUM_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> vsum(m..n) f = vsum(m..n-1) f + (f n):real^N`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; VSUM_CLAUSES_NUMSEG; SUC_SUB1]);;

let VSUM_CMUL_NUMSEG = prove
 (`!f c m n. vsum (m..n) (\x. c % f x) = c % vsum (m..n) f`,
  SIMP_TAC[VSUM_LMUL; FINITE_NUMSEG]);;

let VSUM_EQ_NUMSEG = prove
 (`!f g m n.
         (!x. m <= x /\ x <= n ==> (f x = g x))
         ==> (vsum(m .. n) f = vsum(m .. n) g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]);;

let VSUM_IMAGE_GEN = prove
 (`!f:A->B g s.
        FINITE s
        ==> (vsum s g =
             vsum (IMAGE f s) (\y. vsum {x | x IN s /\ (f(x) = y)} g))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_IMAGE_GEN]);;

let VSUM_GROUP = prove
 (`!f:A->B g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> vsum t (\y. vsum {x | x IN s /\ f(x) = y} g) = vsum s g`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_GROUP]);;

let VSUM_GROUP_RELATION = prove
 (`!R:A->B->bool g s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> vsum t (\y. vsum {x | x IN s /\ R x y} g) = vsum s g`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_GROUP_RELATION]);;

let VSUM_VMUL = prove
 (`!f v s. (sum s f) % v = vsum s (\x. f(x) % v)`,
  REWRITE_TAC[VSUM_RMUL]);;

let VSUM_DELTA = prove
 (`!s a. vsum s (\x. if x = a then b else vec 0) =
         if a IN s then b else vec 0`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; COND_COMPONENT] THEN
  SIMP_TAC[VEC_COMPONENT; SUM_DELTA]);;

let VSUM_ADD_NUMSEG = prove
 (`!f g m n. vsum(m..n) (\i. f i + g i) = vsum(m..n) f + vsum(m..n) g`,
  SIMP_TAC[VSUM_ADD; FINITE_NUMSEG]);;

let VSUM_SUB_NUMSEG = prove
 (`!f g m n. vsum(m..n) (\i. f i - g i) = vsum(m..n) f - vsum(m..n) g`,
  SIMP_TAC[VSUM_SUB; FINITE_NUMSEG]);;

let VSUM_ADD_SPLIT = prove
 (`!f m n p.
       m <= n + 1 ==> vsum(m..n + p) f = vsum(m..n) f + vsum(n + 1..n + p) f`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; VECTOR_ADD_COMPONENT;
           SUM_ADD_SPLIT]);;

let VSUM_VSUM_PRODUCT = prove
 (`!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> vsum s (\i. vsum (t i) (x i)) =
            vsum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; COND_COMPONENT] THEN
  SIMP_TAC[SUM_SUM_PRODUCT] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let VSUM_IMAGE_NONZERO = prove
 (`!d:B->real^N i:A->B s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = vec 0)
    ==> vsum (IMAGE i s) d = vsum s (d o i)`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; VSUM_CLAUSES; FINITE_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `vsum s ((d:B->real^N) o (i:A->B)) = vsum (IMAGE i s) d`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `a = x + a <=> x = vec 0`] THEN
  ASM_MESON_TAC[IN_IMAGE]);;

let VSUM_UNION_NONZERO = prove
 (`!f s t. FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = vec 0)
           ==> vsum (s UNION t) f = vsum s f + vsum t f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT] THEN
  SIMP_TAC[VEC_COMPONENT; SUM_UNION_NONZERO]);;

let VSUM_UNIONS_NONZERO = prove
 (`!f s. FINITE s /\ (!t:A->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> f x = vec 0)
         ==> vsum (UNIONS s) f = vsum s (\t. vsum t f)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; VSUM_CLAUSES; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `s:(A->bool)->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ASM_SIMP_TAC[VSUM_CLAUSES] THEN
  ANTS_TAC THENL  [ASM_MESON_TAC[]; DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  STRIP_TAC THEN MATCH_MP_TAC VSUM_UNION_NONZERO THEN
  ASM_SIMP_TAC[FINITE_UNIONS; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[]);;

let VSUM_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> vsum(m..n) f = f m + vsum(m + 1..n) f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT] THEN
  SIMP_TAC[VEC_COMPONENT; SUM_CLAUSES_LEFT]);;

let VSUM_DIFFS = prove
 (`!m n. vsum(m..n) (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else vec 0`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[VSUM_CLAUSES_NUMSEG; LE] THEN
  ASM_CASES_TAC `m = SUC n` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; VECTOR_ADD_LID] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1] THEN VECTOR_ARITH_TAC);;

let VSUM_DIFFS_ALT = prove
 (`!m n. vsum(m..n) (\k. f(k + 1) - f(k)) =
          if m <= n then f(n + 1) - f(m) else vec 0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_NEG_SUB] THEN
  SIMP_TAC[VSUM_NEG; VSUM_DIFFS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_NEG_SUB; VECTOR_NEG_0]);;

let VSUM_DELETE_CASES = prove
 (`!x f s.
        FINITE(s:A->bool)
        ==> vsum(s DELETE x) f = if x IN s then vsum s f - f x else vsum s f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SET_RULE `~(x IN s) ==> s DELETE x = s`] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [MATCH_MP (SET_RULE `x IN s ==> s = x INSERT (s DELETE x)`) th]) THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN VECTOR_ARITH_TAC);;

let VSUM_EQ_GENERAL = prove
  (`!s:A->bool t:B->bool (f:A->real^N) g h.
        (!y. y IN t ==> ?!x. x IN s /\ h x = y) /\
        (!x. x IN s ==> h x IN t /\ g(h x) = f x)
        ==> vsum s f = vsum t g`,
   SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL THEN
   EXISTS_TAC `h:A->B` THEN ASM_MESON_TAC[]);;

let VSUM_EQ_GENERAL_INVERSES = prove
 (`!s t (f:A->real^N) (g:B->real^N) h k.
        (!y. y IN t ==> k y IN s /\ h (k y) = y) /\
        (!x. x IN s ==> h x IN t /\ k (h x) = x /\ g (h x) = f x)
        ==> vsum s f = vsum t g`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:B->A`] THEN ASM_MESON_TAC[]);;

let VSUM_NORM_ALLSUBSETS_BOUND = prove
 (`!f:A->real^N p e.
        FINITE p /\
        (!q. q SUBSET p ==> norm(vsum q f) <= e)
        ==> sum p (\x. norm(f x)) <= &2 * &(dimindex(:N)) * e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum p (\x:A. sum (1..dimindex(:N)) (\i. abs((f x:real^N)$i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[NORM_LE_L1]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&2 * &n * e = &n * &2 * e`] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
   [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {x:A | x IN p /\ &0 <= (f x:real^N)$k} (\x. abs((f x)$k)) +
              sum {x | x IN p /\ (f x)$k < &0} (\x. abs((f x)$k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= a`) THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN p` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= e /\ y <= e ==> x + y <= &2 * e`) THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_ABS_NEG] THEN
  CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `!g. sum s g = sum s f /\ sum s g <= e ==> sum s f <= e`)
  THENL
   [EXISTS_TAC `\x. ((f:A->real^N) x)$k`;
    EXISTS_TAC `\x. --(((f:A->real^N) x)$k)`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPONENT; SUM_NEG; FINITE_RESTRICT] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= e ==> x <= e`) THEN
  REWRITE_TAC[REAL_ABS_NEG] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs((vsum q f)$k) <= norm(vsum q f) /\
    norm(vsum q f) <= e
    ==> abs((vsum q f)$k) <= e`) THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[]);;

let DOT_LSUM = prove
 (`!s f y. FINITE s ==> (vsum s f) dot y = sum s (\x. f(x) dot y)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES; DOT_LZERO; DOT_LADD]);;

let DOT_RSUM = prove
 (`!s f x. FINITE s ==> x dot (vsum s f) = sum s (\y. x dot f(y))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES; DOT_RZERO; DOT_RADD]);;

let VSUM_OFFSET = prove
 (`!p f m n. vsum(m + p..n + p) f = vsum(m..n) (\i. f (i + p))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_OFFSET]);;

let VSUM_OFFSET_0 = prove
 (`!f m n. m <= n ==> vsum(m..n) f = vsum(0..n - m) (\i. f (i + m))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_OFFSET_0]);;

let VSUM_TRIV_NUMSEG = prove
 (`!f m n. n < m ==> vsum(m..n) f = vec 0`,
  SIMP_TAC[GSYM NUMSEG_EMPTY; VSUM_CLAUSES]);;

let VSUM_CONST_NUMSEG = prove
 (`!c m n. vsum(m..n) (\n. c) = &((n + 1) - m) % c`,
  SIMP_TAC[VSUM_CONST; FINITE_NUMSEG; CARD_NUMSEG]);;

let VSUM_SUC = prove
 (`!f m n. vsum (SUC n..SUC m) f = vsum (n..m) (f o SUC)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `SUC n..SUC m = IMAGE SUC (n..m)` SUBST1_TAC THENL
   [REWRITE_TAC [ADD1; NUMSEG_OFFSET_IMAGE] THEN
    REWRITE_TAC [ONE; ADD_SUC; ADD_0; ETA_AX];
    SIMP_TAC [VSUM_IMAGE; FINITE_NUMSEG; SUC_INJ]]);;

let VSUM_BIJECTION = prove
 (`!f:A->real^N p s:A->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
                ==> vsum s f = vsum s (f o p)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VSUM_EQ_GENERAL THEN EXISTS_TAC `p:A->A` THEN
  ASM_REWRITE_TAC[o_THM]);;

let VSUM_PARTIAL_SUC = prove
 (`!f g:num->real^N m n.
        vsum (m..n) (\k. f(k) % (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) % g(n + 1) - f(m) % g(m) -
                           vsum (m..n) (\k. (f(k + 1) - f(k)) % g(k + 1))
            else vec 0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; GSYM NOT_LE] THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[ARITH] THENL
     [VECTOR_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[GSYM NOT_LT; VSUM_TRIV_NUMSEG; ARITH_RULE `n < SUC n`] THEN
  ASM_SIMP_TAC[GSYM ADD1; ADD_CLAUSES] THEN VECTOR_ARITH_TAC);;

let VSUM_PARTIAL_PRE = prove
 (`!f g:num->real^N m n.
        vsum (m..n) (\k. f(k) % (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) % g(n) - f(m) % g(m - 1) -
                           vsum (m..n) (\k. (f(k + 1) - f(k)) % g(k))
            else vec 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `\k. (g:num->real^N)(k - 1)`;
                 `m:num`; `n:num`] VSUM_PARTIAL_SUC) THEN
  REWRITE_TAC[ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let VSUM_COMBINE_L = prove
 (`!f m n p.
        0 < n /\ m <= n /\ n <= p + 1
        ==> vsum(m..n - 1) f + vsum(n..p) f = vsum(m..p) f`,
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VSUM_COMPONENT; SUM_COMBINE_L]);;

let VSUM_COMBINE_R = prove
 (`!f m n p.
        m <= n + 1 /\ n <= p
        ==> vsum(m..n) f + vsum(n + 1..p) f = vsum(m..p) f`,
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VSUM_COMPONENT; SUM_COMBINE_R]);;

let VSUM_INJECTION = prove
 (`!f p s.
         FINITE s /\
         (!x. x IN s ==> p x IN s) /\
         (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
         ==> vsum s (f o p) = vsum s f`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SUM_INJECTION) THEN
  SIMP_TAC[CART_EQ; VSUM_COMPONENT; o_DEF]);;

let VSUM_SWAP = prove
 (`!f s t.
         FINITE s /\ FINITE t
         ==> vsum s (\i. vsum t (f i)) = vsum t (\j. vsum s (\i. f i j))`,
   SIMP_TAC[CART_EQ; VSUM_COMPONENT] THEN REPEAT STRIP_TAC THEN
   W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhs o snd) THEN
   ASM_REWRITE_TAC[]);;

let VSUM_SWAP_NUMSEG = prove
  (`!a b c d f.
         vsum (a..b) (\i. vsum (c..d) (f i)) =
         vsum (c..d) (\j. vsum (a..b) (\i. f i j))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_SWAP THEN REWRITE_TAC[FINITE_NUMSEG]);;

let VSUM_ADD_GEN = prove
 (`!f g s.
       FINITE {x | x IN s /\ ~(f x = vec 0)} /\
       FINITE {x | x IN s /\ ~(g x = vec 0)}
       ==> vsum s (\x. f x + g x) = vsum s f + vsum s g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[CART_EQ; vsum; LAMBDA_BETA; VECTOR_ADD_COMPONENT] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_ADD_GEN THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VEC_COMPONENT]);;

let VSUM_CASES_1 = prove
 (`!s a. FINITE s /\ a IN s
         ==> vsum s (\x. if x = a then y else f(x)) = vsum s f + (y - f a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VSUM_CASES] THEN
  ASM_SIMP_TAC[GSYM DELETE; VSUM_DELETE] THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`] THEN
  REWRITE_TAC[VSUM_SING] THEN VECTOR_ARITH_TAC);;

let VSUM_SING_NUMSEG = prove
 (`vsum(n..n) f = f n`,
  REWRITE_TAC[NUMSEG_SING; VSUM_SING]);;

let VSUM_1 = prove
 (`vsum(1..1) f = f(1)`,
  REWRITE_TAC[VSUM_SING_NUMSEG]);;

let VSUM_2 = prove
 (`!t. vsum(1..2) t = t(1) + t(2)`,
  REWRITE_TAC[num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let VSUM_3 = prove
 (`!t. vsum(1..3) t = t(1) + t(2) + t(3)`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_4 = prove
 (`!t. vsum(1..4) t = t(1) + t(2) + t(3) + t(4)`,
  SIMP_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_PAIR = prove
 (`!f:num->real^N m n.
        vsum(2*m..2*n+1) f = vsum(m..n) (\i. f(2*i) + f(2*i+1))`,
  SIMP_TAC[CART_EQ; VSUM_COMPONENT; VECTOR_ADD_COMPONENT; SUM_PAIR]);;

let VSUM_PAIR_0 = prove
 (`!f:num->real^N n. vsum(0..2*n+1) f = vsum(0..n) (\i. f(2*i) + f(2*i+1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real^N`; `0`; `n:num`] VSUM_PAIR) THEN
  ASM_REWRITE_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Add useful congruences to the simplifier.                                 *)
(* ------------------------------------------------------------------------- *)

let th = prove
 (`(!f g s.   (!x. x IN s ==> f(x) = g(x))
              ==> vsum s (\i. f(i)) = vsum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> vsum(a..b) (\i. f(i)) = vsum(a..b) g) /\
   (!f g p.   (!x. p x ==> f x = g x)
              ==> vsum {y | p y} (\i. f(i)) = vsum {y | p y} g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
  extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* A conversion for evaluation of `vsum(m..n) f` for numerals m and n.       *)
(* ------------------------------------------------------------------------- *)

let EXPAND_VSUM_CONV =
  let [pth_0; pth_1; pth_2] = (CONJUNCTS o prove)
   (`(n < m ==> vsum(m..n) (f:num->real^N) = vec 0) /\
     vsum(m..m) (f:num->real^N) = f m /\
     (m <= n ==> vsum (m..n) (f:num->real^N) = f m + vsum (m + 1..n) f)`,
    REWRITE_TAC[VSUM_CLAUSES_LEFT; VSUM_SING_NUMSEG; VSUM_TRIV_NUMSEG])
  and ns_tm = `..` and f_tm = `f:num->real^N`
  and m_tm = `m:num` and n_tm = `n:num`
  and n_ty = `:N` in
  let rec conv tm =
    let smn,ftm = dest_comb tm in
    let s,mn = dest_comb smn in
    if not(is_const s & fst(dest_const s) = "vsum")
    then failwith "EXPAND_VSUM_CONV" else
    let mtm,ntm = dest_binop ns_tm mn in
    let m = dest_numeral mtm and n = dest_numeral ntm in
    let nty = hd(tl(snd(dest_type(snd(dest_fun_ty(type_of ftm)))))) in
    let ilist = [nty,n_ty] in
    let ifn = inst ilist and tfn = INST_TYPE ilist in
    if n < m then
      let th1 = INST [ftm,ifn f_tm; mtm,m_tm; ntm,n_tm] (tfn pth_0) in
      MP th1 (EQT_ELIM(NUM_LT_CONV(lhand(concl th1))))
    else if n = m then CONV_RULE (RAND_CONV(TRY_CONV BETA_CONV))
                                 (INST [ftm,ifn f_tm; mtm,m_tm] (tfn pth_1))
    else
      let th1 = INST [ftm,ifn f_tm; mtm,m_tm; ntm,n_tm] (tfn pth_2) in
      let th2 = MP th1 (EQT_ELIM(NUM_LE_CONV(lhand(concl th1)))) in
      CONV_RULE (RAND_CONV(COMB2_CONV (RAND_CONV(TRY_CONV BETA_CONV))
       (LAND_CONV(LAND_CONV NUM_ADD_CONV) THENC conv))) th2 in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Basis vectors in coordinate directions.                                   *)
(* ------------------------------------------------------------------------- *)

let basis = new_definition
  `basis k = lambda i. if i = k then &1 else &0`;;

let NORM_BASIS = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> (norm(basis k :real^N) = &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[basis; dot; vector_norm] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum (1..dimindex(:N)) (\i. if i = k then &1 else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[LAMBDA_BETA; IN_NUMSEG; EQ_SYM_EQ] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]]);;

let NORM_BASIS_1 = prove
 (`norm(basis 1) = &1`,
  SIMP_TAC[NORM_BASIS; ARITH_EQ; ARITH_RULE `1 <= k <=> ~(k = 0)`;
           DIMINDEX_NONZERO]);;

let VECTOR_CHOOSE_SIZE = prove
 (`!c. &0 <= c ==> ?x:real^N. norm(x) = c`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `c % basis 1 :real^N` THEN
  ASM_REWRITE_TAC[NORM_MUL; real_abs; NORM_BASIS_1; REAL_MUL_RID]);;

let VECTOR_CHOOSE_DIST = prove
 (`!x e. &0 <= e ==> ?y:real^N. dist(x,y) = e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?c:real^N. norm(c) = e` CHOOSE_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_SIZE]; ALL_TAC] THEN
  EXISTS_TAC `x - c:real^N` THEN REWRITE_TAC[dist] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x - (x - c) = c:real^N`]);;

let BASIS_INJ = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N) /\
         (basis i :real^N = basis j)
         ==> (i = j)`,
  SIMP_TAC[basis; CART_EQ; LAMBDA_BETA] THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; ARITH_EQ]);;

let BASIS_INJ_EQ = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> (basis i:real^N = basis j <=> i = j)`,
  MESON_TAC[BASIS_INJ]);;

let BASIS_NE = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N) /\
         ~(i = j)
         ==> ~(basis i :real^N = basis j)`,
  MESON_TAC[BASIS_INJ]);;

let BASIS_COMPONENT = prove
 (`!k i. 1 <= i /\ i <= dimindex(:N)
         ==> ((basis k :real^N)$i = if i = k then &1 else &0)`,
  SIMP_TAC[basis; LAMBDA_BETA] THEN MESON_TAC[]);;

let BASIS_EXPANSION = prove
 (`!x:real^N. vsum(1..dimindex(:N)) (\i. x$i % basis i) = x`,
  SIMP_TAC[CART_EQ; VSUM_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_MUL_RID]);;

let BASIS_EXPANSION_UNIQUE = prove
 (`!f x:real^N. (vsum(1..dimindex(:N)) (\i. f(i) % basis i) = x) <=>
                (!i. 1 <= i /\ i <= dimindex(:N) ==> f(i) = x$i)`,
  SIMP_TAC[CART_EQ; VSUM_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[COND_RAND; REAL_MUL_RZERO; REAL_MUL_RID] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o LAND_CONV o
                   ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  SIMP_TAC[SUM_DELTA; IN_NUMSEG]);;

let DOT_BASIS = prove
 (`!x:real^N i.
        1 <= i /\ i <= dimindex(:N)
        ==> ((basis i) dot x = x$i) /\ (x dot (basis i) = x$i)`,
  SIMP_TAC[dot; basis; LAMBDA_BETA] THEN
  REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_MUL_LID; REAL_MUL_RID]);;

let DOT_BASIS_BASIS = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N)
         ==> (basis i:real^N) dot (basis j) = if i = j then &1 else &0`,
  SIMP_TAC[DOT_BASIS; BASIS_COMPONENT]);;

let DOT_BASIS_BASIS_UNEQUAL = prove
 (`!i j. ~(i = j) ==> (basis i) dot (basis j) = &0`,
  SIMP_TAC[basis; dot; LAMBDA_BETA] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[SUM_0; REAL_MUL_RZERO; REAL_MUL_LZERO; COND_ID]);;

let BASIS_EQ_0 = prove
 (`!i. (basis i :real^N = vec 0) <=> ~(i IN 1..dimindex(:N))`,
  SIMP_TAC[CART_EQ; BASIS_COMPONENT; VEC_COMPONENT; IN_NUMSEG] THEN
  MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;

let BASIS_NONZERO = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> ~(basis k :real^N = vec 0)`,
  REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG]);;

let VECTOR_EQ_LDOT = prove
 (`!y z. (!x. x dot y = x dot z) <=> y = z`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[CART_EQ] THEN MESON_TAC[DOT_BASIS]);;

let VECTOR_EQ_RDOT = prove
 (`!x y. (!z. x dot z = y dot z) <=> x = y`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[CART_EQ] THEN MESON_TAC[DOT_BASIS]);;

(* ------------------------------------------------------------------------- *)
(* Orthogonality.                                                            *)
(* ------------------------------------------------------------------------- *)

let orthogonal = new_definition
  `orthogonal x y <=> (x dot y = &0)`;;

let ORTHOGONAL_0 = prove
 (`!x. orthogonal (vec 0) x /\ orthogonal x (vec 0)`,
  REWRITE_TAC[orthogonal; DOT_LZERO; DOT_RZERO]);;

let ORTHOGONAL_REFL = prove
 (`!x. orthogonal x x <=> x = vec 0`,
  REWRITE_TAC[orthogonal; DOT_EQ_0]);;

let ORTHOGONAL_SYM = prove
 (`!x y. orthogonal x y <=> orthogonal y x`,
  REWRITE_TAC[orthogonal; DOT_SYM]);;

let ORTHOGONAL_LNEG = prove
 (`!x y. orthogonal (--x) y <=> orthogonal x y`,
  REWRITE_TAC[orthogonal; DOT_LNEG; REAL_NEG_EQ_0]);;

let ORTHOGONAL_RNEG = prove
 (`!x y. orthogonal x (--y) <=> orthogonal x y`,
  REWRITE_TAC[orthogonal; DOT_RNEG; REAL_NEG_EQ_0]);;

let ORTHOGONAL_MUL = prove
 (`(!a x y:real^N. orthogonal (a % x) y <=> a = &0 \/ orthogonal x y) /\
   (!a x y:real^N. orthogonal x (a % y) <=> a = &0 \/ orthogonal x y)`,
  REWRITE_TAC[orthogonal; DOT_LMUL; DOT_RMUL; REAL_ENTIRE]);;

let ORTHOGONAL_BASIS = prove
 (`!x:real^N i. 1 <= i /\ i <= dimindex(:N)
                ==> (orthogonal (basis i) x <=> (x$i = &0))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[orthogonal; dot; basis; LAMBDA_BETA] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_MUL_LID]);;

let ORTHOGONAL_BASIS_BASIS = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N)
         ==> (orthogonal (basis i :real^N) (basis j) <=> ~(i = j))`,
  ASM_SIMP_TAC[ORTHOGONAL_BASIS] THEN ASM_SIMP_TAC[BASIS_COMPONENT] THEN
  MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;

let ORTHOGONAL_CLAUSES = prove
 (`(!a. orthogonal a (vec 0)) /\
   (!a x c. orthogonal a x ==> orthogonal a (c % x)) /\
   (!a x. orthogonal a x ==> orthogonal a (--x)) /\
   (!a x y. orthogonal a x /\ orthogonal a y ==> orthogonal a (x + y)) /\
   (!a x y. orthogonal a x /\ orthogonal a y ==> orthogonal a (x - y)) /\
   (!a. orthogonal (vec 0) a) /\
   (!a x c. orthogonal x a ==> orthogonal (c % x) a) /\
   (!a x. orthogonal x a ==> orthogonal (--x) a) /\
   (!a x y. orthogonal x a /\ orthogonal y a ==> orthogonal (x + y) a) /\
   (!a x y. orthogonal x a /\ orthogonal y a ==> orthogonal (x - y) a)`,
  REWRITE_TAC[orthogonal; DOT_RNEG; DOT_RMUL; DOT_RADD; DOT_RSUB;
    DOT_LZERO; DOT_RZERO; DOT_LNEG; DOT_LMUL; DOT_LADD; DOT_LSUB] THEN
  SIMP_TAC[] THEN REAL_ARITH_TAC);;

let ORTHOGONAL_RVSUM = prove
 (`!f:A->real^N s x.
        FINITE s /\
        (!y. y IN s ==> orthogonal x (f y))
        ==> orthogonal x (vsum s f)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT; ORTHOGONAL_CLAUSES; VSUM_CLAUSES]);;

let ORTHOGONAL_LVSUM = prove
 (`!f:A->real^N s y.
        FINITE s /\
        (!x. x IN s ==> orthogonal (f x) y)
        ==> orthogonal (vsum s f) y`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT; ORTHOGONAL_CLAUSES; VSUM_CLAUSES]);;

let NORM_ADD_PYTHAGOREAN = prove
 (`!a b:real^N.
        orthogonal a b
        ==> norm(a + b) pow 2 = norm(a) pow 2 + norm(b) pow 2`,
  SIMP_TAC[NORM_POW_2; orthogonal; DOT_LADD; DOT_RADD; DOT_SYM] THEN
  REAL_ARITH_TAC);;

let NORM_VSUM_PYTHAGOREAN = prove
 (`!k u:A->real^N.
        FINITE k /\ pairwise (\i j. orthogonal (u i) (u j)) k
        ==> norm(vsum k u) pow 2 = sum k (\i. norm(u i) pow 2)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN SIMP_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES; NORM_0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[PAIRWISE_INSERT] THEN
  REWRITE_TAC[pairwise] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NORM_ADD_PYTHAGOREAN THEN MATCH_MP_TAC ORTHOGONAL_RVSUM THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Explicit vector construction from lists.                                  *)
(* ------------------------------------------------------------------------- *)

let VECTOR_1 = prove
 (`(vector[x]:A^1)$1 = x`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_1; ARITH; LENGTH; EL; HD; TL]);;

let VECTOR_2 = prove
 (`(vector[x;y]:A^2)$1 = x /\
   (vector[x;y]:A^2)$2 = y`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_2; ARITH; LENGTH; EL] THEN
  REWRITE_TAC[num_CONV `1`; HD; TL; EL]);;

let VECTOR_3 = prove
 (`(vector[x;y;z]:A^3)$1 = x /\
   (vector[x;y;z]:A^3)$2 = y /\
   (vector[x;y;z]:A^3)$3 = z`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_3; ARITH; LENGTH; EL] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; HD; TL; EL]);;

let VECTOR_4 = prove
 (`(vector[w;x;y;z]:A^4)$1 = w /\
   (vector[w;x;y;z]:A^4)$2 = x /\
   (vector[w;x;y;z]:A^4)$3 = y /\
   (vector[w;x;y;z]:A^4)$4 = z`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_4; ARITH; LENGTH; EL] THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; HD; TL; EL]);;

let FORALL_VECTOR_1 = prove
 (`(!v:A^1. P v) <=> !x. P(vector[x])`,
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(v:A^1)$1`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_1; VECTOR_1; DIMINDEX_1]);;

let FORALL_VECTOR_2 = prove
 (`(!v:A^2. P v) <=> !x y. P(vector[x;y])`,
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(v:A^2)$1`; `(v:A^2)$2`]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_2; VECTOR_2; DIMINDEX_2]);;

let FORALL_VECTOR_3 = prove
 (`(!v:A^3. P v) <=> !x y z. P(vector[x;y;z])`,
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`(v:A^3)$1`; `(v:A^3)$2`; `(v:A^3)$3`]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_3; VECTOR_3; DIMINDEX_3]);;

let FORALL_VECTOR_4 = prove
 (`(!v:A^4. P v) <=> !w x y z. P(vector[w;x;y;z])`,
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`(v:A^4)$1`; `(v:A^4)$2`; `(v:A^4)$3`; `(v:A^4)$4`]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_4; VECTOR_4; DIMINDEX_4]);;

let EXISTS_VECTOR_1 = prove
 (`(?v:A^1. P v) <=> ?x. P(vector[x])`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_VECTOR_1]);;

let EXISTS_VECTOR_2 = prove
 (`(?v:A^2. P v) <=> ?x y. P(vector[x;y])`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_VECTOR_2]);;

let EXISTS_VECTOR_3 = prove
 (`(?v:A^3. P v) <=> ?x y z. P(vector[x;y;z])`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_VECTOR_3]);;

let EXISTS_VECTOR_4 = prove
 (`(?v:A^4. P v) <=> ?w x y z. P(vector[w;x;y;z])`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_VECTOR_4]);;

let VECTOR_EXPAND_1 = prove
 (`!x:real^1. x = vector[x$1]`,
  SIMP_TAC[CART_EQ; DIMINDEX_1; FORALL_1; VECTOR_1]);;

let VECTOR_EXPAND_2 = prove
 (`!x:real^2. x = vector[x$1;x$2]`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let VECTOR_EXPAND_3 = prove
 (`!x:real^3. x = vector[x$1;x$2;x$3]`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]);;

let VECTOR_EXPAND_4 = prove
 (`!x:real^4. x = vector[x$1;x$2;x$3;x$4]`,
  SIMP_TAC[CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_4]);;

(* ------------------------------------------------------------------------- *)
(* Linear functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let linear = new_definition
  `linear (f:real^M->real^N) <=>
        (!x y. f(x + y) = f(x) + f(y)) /\
        (!c x. f(c % x) = c % f(x))`;;

let LINEAR_COMPOSE_CMUL = prove
 (`!f c. linear f ==> linear (\x. c % f(x))`,
  SIMP_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE_NEG = prove
 (`!f. linear f ==> linear (\x. --(f(x)))`,
  SIMP_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE_NEG_EQ = prove
 (`!f:real^M->real^N. linear(\x. --(f x)) <=> linear f`,
  MATCH_MP_TAC(MESON[]
   `(!x. P x ==> P(f x)) /\ (!x. f(f x) = x)
    ==> (!x. P(f x) <=> P x)`) THEN
  REWRITE_TAC[LINEAR_COMPOSE_NEG; VECTOR_NEG_NEG; ETA_AX]);;

let LINEAR_COMPOSE_ADD = prove
 (`!f g. linear f /\ linear g ==> linear (\x. f(x) + g(x))`,
  SIMP_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE_SUB = prove
 (`!f g. linear f /\ linear g ==> linear (\x. f(x) - g(x))`,
  SIMP_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE = prove
 (`!f g. linear f /\ linear g ==> linear (g o f)`,
  SIMP_TAC[linear; o_THM]);;

let LINEAR_ID = prove
 (`linear (\x. x)`,
  REWRITE_TAC[linear]);;

let LINEAR_I = prove
 (`linear I`,
  REWRITE_TAC[I_DEF; LINEAR_ID]);;

let LINEAR_ZERO = prove
 (`linear (\x. vec 0)`,
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_NEGATION = prove
 (`linear(--)`,
  REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE_VSUM = prove
 (`!f s. FINITE s /\ (!a. a IN s ==> linear(f a))
         ==> linear(\x. vsum s (\a. f a x))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; LINEAR_ZERO] THEN
  ASM_SIMP_TAC[ETA_AX; IN_INSERT; LINEAR_COMPOSE_ADD]);;

let LINEAR_VMUL_COMPONENT = prove
 (`!f:real^M->real^N v k.
     linear f /\ 1 <= k /\ k <= dimindex(:N)
     ==> linear (\x. f(x)$k % v)`,
  SIMP_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_0 = prove
 (`!f. linear f ==> (f(vec 0) = vec 0)`,
  MESON_TAC[VECTOR_MUL_LZERO; linear]);;

let LINEAR_CMUL = prove
 (`!f c x. linear f ==> (f(c % x) = c % f(x))`,
  SIMP_TAC[linear]);;

let LINEAR_NEG = prove
 (`!f x. linear f ==> (f(--x) = --(f x))`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC[LINEAR_CMUL]);;

let LINEAR_ADD = prove
 (`!f x y. linear f ==> (f(x + y) = f(x) + f(y))`,
  SIMP_TAC[linear]);;

let LINEAR_SUB = prove
 (`!f x y. linear f ==> (f(x - y) = f(x) - f(y))`,
  SIMP_TAC[VECTOR_SUB; LINEAR_ADD; LINEAR_NEG]);;

let LINEAR_VSUM = prove
 (`!f g s. linear f /\ FINITE s ==> (f(vsum s g) = vsum s (f o g))`,
  GEN_TAC THEN GEN_TAC THEN SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES] THEN FIRST_ASSUM(fun th ->
    SIMP_TAC[MATCH_MP LINEAR_0 th; MATCH_MP LINEAR_ADD th; o_THM]));;

let LINEAR_VSUM_MUL = prove
 (`!f s c v.
        linear f /\ FINITE s
        ==> f(vsum s (\i. c i % v i)) = vsum s (\i. c(i) % f(v i))`,
  SIMP_TAC[LINEAR_VSUM; o_DEF; LINEAR_CMUL]);;

let LINEAR_INJECTIVE_0 = prove
 (`!f. linear f
       ==> ((!x y. (f(x) = f(y)) ==> (x = y)) <=>
            (!x. (f(x) = vec 0) ==> (x = vec 0)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN MESON_TAC[VECTOR_SUB_RZERO]);;

let LINEAR_BOUNDED = prove
 (`!f:real^M->real^N. linear f ==> ?B. !x. norm(f x) <= B * norm(x)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
   `sum(1..dimindex(:M)) (\i. norm((f:real^M->real^N)(basis i)))` THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; IN_NUMSEG] THEN
  ASM_SIMP_TAC[o_DEF; NORM_MUL; LINEAR_CMUL] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE; COMPONENT_LE_NORM]);;

let LINEAR_BOUNDED_POS = prove
 (`!f:real^M->real^N. linear f ==> ?B. &0 < B /\ !x. norm(f x) <= B * norm(x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o MATCH_MP LINEAR_BOUNDED) THEN
  EXISTS_TAC `abs(B) + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  REAL_ARITH_TAC);;

let SYMMETRIC_LINEAR_IMAGE = prove
 (`!f s. (!x. x IN s ==> --x IN s) /\ linear f
          ==> !x. x IN (IMAGE f s) ==> --x IN (IMAGE f s)`,
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[GSYM LINEAR_NEG] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bilinear functions.                                                       *)
(* ------------------------------------------------------------------------- *)

let bilinear = new_definition
  `bilinear f <=> (!x. linear(\y. f x y)) /\ (!y. linear(\x. f x y))`;;

let BILINEAR_SWAP = prove
 (`!op:real^M->real^N->real^P.
        bilinear(\x y. op y x) <=> bilinear op`,
  REWRITE_TAC[bilinear; ETA_AX] THEN MESON_TAC[]);;

let BILINEAR_LADD = prove
 (`!h x y z. bilinear h ==> h (x + y) z = (h x z) + (h y z)`,
  SIMP_TAC[bilinear; linear]);;

let BILINEAR_RADD = prove
 (`!h x y z. bilinear h ==> h x (y + z) = (h x y) + (h x z)`,
  SIMP_TAC[bilinear; linear]);;

let BILINEAR_LMUL = prove
 (`!h c x y. bilinear h ==> h (c % x) y = c % (h x y)`,
  SIMP_TAC[bilinear; linear]);;

let BILINEAR_RMUL = prove
 (`!h c x y. bilinear h ==> h x (c % y) = c % (h x y)`,
  SIMP_TAC[bilinear; linear]);;

let BILINEAR_LNEG = prove
 (`!h x y. bilinear h ==> h (--x) y = --(h x y)`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC[BILINEAR_LMUL]);;

let BILINEAR_RNEG = prove
 (`!h x y. bilinear h ==> h x (--y) = --(h x y)`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC[BILINEAR_RMUL]);;

let BILINEAR_LZERO = prove
 (`!h x. bilinear h ==> h (vec 0) x = vec 0`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `x = vec 0 <=> x + x = x`] THEN
  SIMP_TAC[GSYM BILINEAR_LADD; VECTOR_ADD_LID]);;

let BILINEAR_RZERO = prove
 (`!h x. bilinear h ==> h x (vec 0) = vec 0`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `x = vec 0 <=> x + x = x`] THEN
  SIMP_TAC[GSYM BILINEAR_RADD; VECTOR_ADD_LID]);;

let BILINEAR_LSUB = prove
 (`!h x y z. bilinear h ==> h (x - y) z = (h x z) - (h y z)`,
  SIMP_TAC[VECTOR_SUB; BILINEAR_LNEG; BILINEAR_LADD]);;

let BILINEAR_RSUB = prove
 (`!h x y z. bilinear h ==> h x (y - z) = (h x y) - (h x z)`,
  SIMP_TAC[VECTOR_SUB; BILINEAR_RNEG; BILINEAR_RADD]);;

let BILINEAR_VSUM = prove
 (`!h:real^M->real^N->real^P.
       bilinear h /\ FINITE s /\ FINITE t
       ==> h (vsum s f) (vsum t g) = vsum (s CROSS t) (\(i,j). h (f i) (g j))`,
  REPEAT GEN_TAC THEN SIMP_TAC[bilinear; ETA_AX] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> (a /\ d) /\ (b /\ c)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[LEFT_AND_FORALL_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_ALL o MATCH_MP LINEAR_VSUM o SPEC_ALL) THEN
  SIMP_TAC[] THEN ASM_SIMP_TAC[LINEAR_VSUM; o_DEF; VSUM_VSUM_PRODUCT] THEN
  REWRITE_TAC[GSYM CROSS]);;

let BILINEAR_BOUNDED = prove
 (`!h:real^M->real^N->real^P.
        bilinear h ==> ?B. !x y. norm(h x y) <= B * norm(x) * norm(y)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `sum ((1..dimindex(:M)) CROSS (1..dimindex(:N)))
                  (\(i,j). norm((h:real^M->real^N->real^P)
                                (basis i) (basis j)))` THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC
   (LAND_CONV o RAND_CONV o BINOP_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[BILINEAR_VSUM; FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BILINEAR_LMUL; NORM_MUL] THEN
  ASM_SIMP_TAC[BILINEAR_RMUL; NORM_MUL; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM; REAL_ABS_POS; REAL_LE_MUL2]);;

let BILINEAR_BOUNDED_POS = prove
 (`!h. bilinear h
       ==> ?B. &0 < B /\ !x y. norm(h x y) <= B * norm(x) * norm(y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o MATCH_MP BILINEAR_BOUNDED) THEN
  EXISTS_TAC `abs(B) + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_RMUL THEN
         SIMP_TAC[NORM_POS_LE; REAL_LE_MUL]) THEN
  REAL_ARITH_TAC);;

let BILINEAR_VSUM_PARTIAL_SUC = prove
 (`!f g h:real^M->real^N->real^P m n.
        bilinear h
        ==> vsum (m..n) (\k. h (f k) (g(k + 1) - g(k))) =
                if m <= n then h (f(n + 1)) (g(n + 1)) - h (f m) (g m) -
                               vsum (m..n) (\k. h (f(k + 1) - f(k)) (g(k + 1)))
                else vec 0`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; GSYM NOT_LE] THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[ARITH] THENL
     [ASM_SIMP_TAC[BILINEAR_RSUB; BILINEAR_LSUB] THEN VECTOR_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[GSYM NOT_LT; VSUM_TRIV_NUMSEG; ARITH_RULE `n < SUC n`] THEN
  ASM_SIMP_TAC[GSYM ADD1; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[BILINEAR_RSUB; BILINEAR_LSUB] THEN VECTOR_ARITH_TAC);;

let BILINEAR_VSUM_PARTIAL_PRE = prove
 (`!f g h:real^M->real^N->real^P m n.
        bilinear h
        ==> vsum (m..n) (\k. h (f k) (g(k) - g(k - 1))) =
                if m <= n then h (f(n + 1)) (g(n)) - h (f m) (g(m - 1)) -
                               vsum (m..n) (\k. h (f(k + 1) - f(k)) (g(k)))
                else vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPECL [`f:num->real^M`; `\k. (g:num->real^N)(k - 1)`;
                 `m:num`; `n:num`] o MATCH_MP BILINEAR_VSUM_PARTIAL_SUC) THEN
   REWRITE_TAC[ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Adjoints.                                                                 *)
(* ------------------------------------------------------------------------- *)

let adjoint = new_definition
 `adjoint(f:real^M->real^N) = @f'. !x y. f(x) dot y = x dot f'(y)`;;

let ADJOINT_WORKS = prove
 (`!f:real^M->real^N. linear f ==> !x y. f(x) dot y = x dot (adjoint f)(y)`,
  GEN_TAC THEN DISCH_TAC THEN SIMP_TAC[adjoint] THEN CONV_TAC SELECT_CONV THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN ONCE_REWRITE_TAC[GSYM SKOLEM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  EXISTS_TAC `(lambda i. (f:real^M->real^N) (basis i) dot y):real^M` THEN
  X_GEN_TAC `x:real^M` THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG] THEN
  SIMP_TAC[dot; LAMBDA_BETA; VSUM_COMPONENT; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  ASM_SIMP_TAC[o_THM; VECTOR_MUL_COMPONENT; LINEAR_CMUL; REAL_MUL_ASSOC]);;

let ADJOINT_LINEAR = prove
 (`!f:real^M->real^N. linear f ==> linear(adjoint f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[linear; GSYM VECTOR_EQ_LDOT] THEN
  ASM_SIMP_TAC[DOT_RMUL; DOT_RADD; GSYM ADJOINT_WORKS]);;

let ADJOINT_CLAUSES = prove
 (`!f:real^M->real^N.
     linear f ==> (!x y. x dot (adjoint f)(y) = f(x) dot y) /\
                  (!x y. (adjoint f)(y) dot x = y dot f(x))`,
  MESON_TAC[ADJOINT_WORKS; DOT_SYM]);;

let ADJOINT_ADJOINT = prove
 (`!f:real^M->real^N. linear f ==> adjoint(adjoint f) = f`,
  SIMP_TAC[FUN_EQ_THM; GSYM VECTOR_EQ_LDOT; ADJOINT_CLAUSES; ADJOINT_LINEAR]);;

let ADJOINT_UNIQUE = prove
 (`!f f'. linear f /\ (!x y. f'(x) dot y = x dot f(y))
          ==> f' = adjoint f`,
  SIMP_TAC[FUN_EQ_THM; GSYM VECTOR_EQ_RDOT; ADJOINT_CLAUSES]);;

let ADJOINT_COMPOSE = prove
 (`!f g:real^N->real^N.
        linear f /\ linear g ==> adjoint(f o g) = adjoint g o adjoint f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; o_THM; ADJOINT_CLAUSES]);;

let SELF_ADJOINT_COMPOSE = prove
 (`!f g:real^N->real^N.
        linear f /\ linear g /\ adjoint f = f /\ adjoint g = g
        ==> (adjoint(f o g) = f o g <=> f o g = g o f)`,
  SIMP_TAC[ADJOINT_COMPOSE] THEN MESON_TAC[]);;

let SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS = prove
 (`!f:real^N->real^N v w a b.
        linear f /\ adjoint f = f /\ f v = a % v /\ f w = b % w /\ ~(a = b)
        ==> orthogonal v w`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPECL [`v:real^N`; `w:real^N`] o
        MATCH_MP ADJOINT_WORKS) THEN
  ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; orthogonal; REAL_EQ_MUL_RCANCEL]);;

let ORTHOGONAL_PROJECTION_ALT = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x y. orthogonal (f x - x) (f x - f y)) <=>
             (!x y. orthogonal (f x - x) (f y)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x - y:real^N`) THEN
  ASM_SIMP_TAC[LINEAR_SUB; VECTOR_ARITH `x - (x - y):real^N = y`]);;

let ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x y. orthogonal (f x - x) (f x - f y)) <=>
             adjoint f = f /\ f o f = f)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ORTHOGONAL_PROJECTION_ALT] THEN
  EQ_TAC THENL
   [REPEAT STRIP_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      FIRST_X_ASSUM(fun th ->
        MP_TAC(ISPECL [`x:real^N`; `y:real^N`] th) THEN
        MP_TAC(ISPECL [`y:real^N`; `x:real^N`] th)) THEN
      REWRITE_TAC[orthogonal; DOT_LSUB] THEN
      REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^N` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`(f:real^N->real^N) x`; `f x - x:real^N`]) THEN
      ASM_SIMP_TAC[LINEAR_SUB; ORTHOGONAL_REFL; VECTOR_SUB_EQ]];
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o GSYM o MATCH_MP ADJOINT_WORKS) THEN
   ASM_SIMP_TAC[orthogonal; LINEAR_SUB; VECTOR_SUB_REFL; DOT_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Matrix notation. NB: an MxN matrix is of type real^N^M, not real^M^N.     *)
(* We could define a special type if we're going to use them a lot.          *)
(* ------------------------------------------------------------------------- *)

overload_interface ("--",`(matrix_neg):real^N^M->real^N^M`);;
overload_interface ("+",`(matrix_add):real^N^M->real^N^M->real^N^M`);;
overload_interface ("-",`(matrix_sub):real^N^M->real^N^M->real^N^M`);;

make_overloadable "**" `:A->B->C`;;

overload_interface ("**",`(vector_matrix_mul):real^M->real^N^M->real^N`);;
overload_interface ("**",`(matrix_mul):real^N^M->real^P^N->real^P^M`);;
overload_interface ("**",`(matrix_vector_mul):real^N^M->real^N->real^M`);;

parse_as_infix("%%",(21,"right"));;

prioritize_real();;

let matrix_cmul = new_definition
  `((%%):real->real^N^M->real^N^M) c A = lambda i j. c * A$i$j`;;

let matrix_neg = new_definition
  `!A:real^N^M. --A = lambda i j. --(A$i$j)`;;

let matrix_add = new_definition
  `!A:real^N^M B:real^N^M. A + B = lambda i j. A$i$j + B$i$j`;;

let matrix_sub = new_definition
  `!A:real^N^M B:real^N^M. A - B = lambda i j. A$i$j - B$i$j`;;

let matrix_mul = new_definition
  `!A:real^N^M B:real^P^N.
        A ** B =
          lambda i j. sum(1..dimindex(:N)) (\k. A$i$k * B$k$j)`;;

let matrix_vector_mul = new_definition
  `!A:real^N^M x:real^N.
        A ** x = lambda i. sum(1..dimindex(:N)) (\j. A$i$j * x$j)`;;

let vector_matrix_mul = new_definition
  `!A:real^N^M x:real^M.
        x ** A = lambda j. sum(1..dimindex(:M)) (\i. A$i$j * x$i)`;;

let mat = new_definition
  `(mat:num->real^N^M) k = lambda i j. if i = j then &k else &0`;;

let transp = new_definition
  `(transp:real^N^M->real^M^N) A = lambda i j. A$j$i`;;

let row = new_definition
 `(row:num->real^N^M->real^N) i A = lambda j. A$i$j`;;

let column = new_definition
 `(column:num->real^N^M->real^M) j A = lambda i. A$i$j`;;

let rows = new_definition
 `rows(A:real^N^M) = { row i A | 1 <= i /\ i <= dimindex(:M)}`;;

let columns = new_definition
 `columns(A:real^N^M) = { column i A | 1 <= i /\ i <= dimindex(:N)}`;;

let MATRIX_CMUL_COMPONENT = prove
 (`!c A:real^N^M i. (c %% A)$i$j = c * A$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_cmul; CART_EQ; LAMBDA_BETA]);;

let MATRIX_ADD_COMPONENT = prove
 (`!A B:real^N^M i j. (A + B)$i$j = A$i$j + B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_add; LAMBDA_BETA]);;

let MATRIX_SUB_COMPONENT = prove
 (`!A B:real^N^M i j. (A - B)$i$j = A$i$j - B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_sub; LAMBDA_BETA]);;

let MATRIX_NEG_COMPONENT = prove
 (`!A:real^N^M i j. (--A)$i$j = --(A$i$j)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_neg; LAMBDA_BETA]);;

let TRANSP_COMPONENT = prove
 (`!A:real^N^M i j. (transp A)$i$j = A$j$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\
                    (!A:real^M^N. A$i = A$k) /\ (!z:real^N. z$i = z$k)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:M) /\
                    (!A:real^N^M. A$j = A$l) /\ (!z:real^M. z$j = z$l)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[transp; LAMBDA_BETA]);;

let MAT_COMPONENT = prove
 (`!n i j.
        1 <= i /\ i <= dimindex(:M) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (mat n:real^N^M)$i$j = if i = j then &n else &0`,
  SIMP_TAC[mat; LAMBDA_BETA]);;

let MAT_0_COMPONENT = prove
 (`!i j. (mat 0:real^N^M)$i$j = &0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[mat; COND_ID; LAMBDA_BETA]);;

let MAT_CMUL = prove
 (`!a. mat a = &a %% mat 1`,
  SIMP_TAC[CART_EQ; MAT_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  MESON_TAC[REAL_MUL_RID; REAL_MUL_RZERO]);;

let ROW_0 = prove
 (`!i. row i (mat 0:real^N^N) = vec 0`,
  SIMP_TAC[MAT_0_COMPONENT; CART_EQ; row; VEC_COMPONENT; LAMBDA_BETA]);;

let COLUMN_0 = prove
 (`!i. column i (mat 0:real^N^N) = vec 0`,
  SIMP_TAC[MAT_0_COMPONENT; CART_EQ; column; VEC_COMPONENT; LAMBDA_BETA]);;

let MATRIX_CMUL_ASSOC = prove
 (`!a b X:real^M^N. a %% (b %% X) = (a * b) %% X`,
  SIMP_TAC[CART_EQ; matrix_cmul; LAMBDA_BETA; REAL_MUL_ASSOC]);;

let MATRIX_CMUL_LID = prove
 (`!X:real^M^N. &1 %% X = X`,
  SIMP_TAC[CART_EQ; matrix_cmul; LAMBDA_BETA; REAL_MUL_LID]);;

let MATRIX_ADD_SYM = prove
 (`!A:real^N^M B. A + B = B + A`,
  SIMP_TAC[matrix_add; CART_EQ; LAMBDA_BETA; REAL_ADD_AC]);;

let MATRIX_ADD_ASSOC = prove
 (`!A:real^N^M B C. A + (B + C) = (A + B) + C`,
  SIMP_TAC[matrix_add; CART_EQ; LAMBDA_BETA; REAL_ADD_AC]);;

let MATRIX_ADD_LID = prove
 (`!A. mat 0 + A = A`,
  SIMP_TAC[matrix_add; mat; COND_ID; CART_EQ; LAMBDA_BETA; REAL_ADD_LID]);;

let MATRIX_ADD_RID = prove
 (`!A. A + mat 0 = A`,
  SIMP_TAC[matrix_add; mat; COND_ID; CART_EQ; LAMBDA_BETA; REAL_ADD_RID]);;

let MATRIX_ADD_LNEG = prove
 (`!A. --A + A = mat 0`,
  SIMP_TAC[matrix_neg; matrix_add; mat; COND_ID;
           CART_EQ; LAMBDA_BETA; REAL_ADD_LINV]);;

let MATRIX_ADD_RNEG = prove
 (`!A. A + --A = mat 0`,
  SIMP_TAC[matrix_neg; matrix_add; mat; COND_ID;
           CART_EQ; LAMBDA_BETA; REAL_ADD_RINV]);;

let MATRIX_SUB = prove
 (`!A:real^N^M B. A - B = A + --B`,
  SIMP_TAC[matrix_neg; matrix_add; matrix_sub; CART_EQ; LAMBDA_BETA;
           real_sub]);;

let MATRIX_SUB_REFL = prove
 (`!A. A - A = mat 0`,
  REWRITE_TAC[MATRIX_SUB; MATRIX_ADD_RNEG]);;

let MATRIX_SUB_EQ = prove
 (`!A B:real^N^M. A - B = mat 0 <=> A = B`,
  SIMP_TAC[CART_EQ; MAT_COMPONENT;
           MATRIX_SUB_COMPONENT; COND_ID; REAL_SUB_0]);;

let MATRIX_ADD_LDISTRIB = prove
 (`!A:real^N^M B:real^P^N C. A ** (B + C) = A ** B + A ** C`,
  SIMP_TAC[matrix_mul; matrix_add; CART_EQ; LAMBDA_BETA;
           GSYM SUM_ADD_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  ASM_SIMP_TAC[LAMBDA_BETA; REAL_ADD_LDISTRIB]);;

let MATRIX_MUL_LID = prove
 (`!A:real^N^M. mat 1 ** A = A`,
  REWRITE_TAC[matrix_mul;
   GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ]
    (SPEC_ALL mat)] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  SIMP_TAC[SUM_DELTA; REAL_MUL_LZERO; IN_NUMSEG; REAL_MUL_LID]);;

let MATRIX_MUL_RID = prove
 (`!A:real^N^M. A ** mat 1 = A`,
  REWRITE_TAC[matrix_mul; mat] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  SIMP_TAC[SUM_DELTA; REAL_MUL_RZERO; IN_NUMSEG; REAL_MUL_RID]);;

let MATRIX_MUL_ASSOC = prove
 (`!A:real^N^M B:real^P^N C:real^Q^P. A ** B ** C = (A ** B) ** C`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[matrix_mul; CART_EQ; LAMBDA_BETA; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let MATRIX_MUL_LZERO = prove
 (`!A. (mat 0:real^N^M) ** (A:real^P^N) = mat 0`,
  SIMP_TAC[matrix_mul; mat; CART_EQ; LAMBDA_BETA; COND_ID; REAL_MUL_LZERO] THEN
  REWRITE_TAC[SUM_0]);;

let MATRIX_MUL_RZERO = prove
 (`!A. (A:real^N^M) ** (mat 0:real^P^N) = mat 0`,
  SIMP_TAC[matrix_mul; mat; CART_EQ; LAMBDA_BETA; COND_ID; REAL_MUL_RZERO] THEN
  REWRITE_TAC[SUM_0]);;

let MATRIX_ADD_RDISTRIB = prove
 (`!A:real^N^M B C:real^P^N. (A + B) ** C = A ** C + B ** C`,
  SIMP_TAC[matrix_mul; matrix_add; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG]);;

let MATRIX_SUB_LDISTRIB = prove
 (`!A:real^N^M B C:real^P^N. A ** (B - C) = A ** B - A ** C`,
  SIMP_TAC[matrix_mul; matrix_sub; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG]);;

let MATRIX_SUB_RDISTRIB = prove
 (`!A:real^N^M B C:real^P^N. (A - B) ** C = A ** C - B ** C`,
  SIMP_TAC[matrix_mul; matrix_sub; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG]);;

let MATRIX_MUL_LMUL = prove
 (`!A:real^N^M B:real^P^N c. (c %% A) ** B = c %% (A ** B)`,
  SIMP_TAC[matrix_mul; matrix_cmul; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL]);;

let MATRIX_MUL_RMUL = prove
 (`!A:real^N^M B:real^P^N c. A ** (c %% B) = c %% (A ** B)`,
  SIMP_TAC[matrix_mul; matrix_cmul; CART_EQ; LAMBDA_BETA] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `A * c * B:real = c * A * B`] THEN
  REWRITE_TAC[SUM_LMUL]);;

let MATRIX_CMUL_ADD_LDISTRIB = prove
 (`!A:real^N^M B c. c %% (A + B) = c %% A + c %% B`,
  SIMP_TAC[matrix_cmul; matrix_add; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB]);;

let MATRIX_CMUL_SUB_LDISTRIB = prove
 (`!A:real^N^M B c. c %% (A - B) = c %% A - c %% B`,
  SIMP_TAC[matrix_cmul; matrix_sub; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB]);;

let MATRIX_CMUL_ADD_RDISTRIB = prove
 (`!A:real^N^M b c. (b + c) %% A = b %% A + c %% A`,
  SIMP_TAC[matrix_cmul; matrix_add; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB]);;

let MATRIX_CMUL_SUB_RDISTRIB = prove
 (`!A:real^N^M b c. (b - c) %% A = b %% A - c %% A`,
  SIMP_TAC[matrix_cmul; matrix_sub; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB]);;

let MATRIX_CMUL_RZERO = prove
 (`!c. c %% mat 0 = mat 0`,
  SIMP_TAC[matrix_cmul; mat; CART_EQ; LAMBDA_BETA; COND_ID; REAL_MUL_RZERO]);;

let MATRIX_CMUL_LZERO = prove
 (`!A. &0 %% A = mat 0`,
  SIMP_TAC[matrix_cmul; mat; CART_EQ; LAMBDA_BETA; COND_ID; REAL_MUL_LZERO]);;

let MATRIX_NEG_MINUS1 = prove
 (`!A:real^N^M. --A = --(&1) %% A`,
  REWRITE_TAC[matrix_cmul; matrix_neg; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM REAL_NEG_MINUS1]);;

let MATRIX_ADD_AC = prove
 (`(A:real^N^M) + B = B + A /\
   (A + B) + C = A + (B + C) /\
   A + (B + C) = B + (A + C)`,
  MESON_TAC[MATRIX_ADD_ASSOC; MATRIX_ADD_SYM]);;

let MATRIX_NEG_ADD = prove
 (`!A B:real^N^M. --(A + B) = --A + --B`,
  SIMP_TAC[matrix_neg; matrix_add; CART_EQ; LAMBDA_BETA; REAL_NEG_ADD]);;

let MATRIX_NEG_SUB = prove
 (`!A B:real^N^M. --(A - B) = B - A`,
  SIMP_TAC[matrix_neg; matrix_sub; CART_EQ; LAMBDA_BETA; REAL_NEG_SUB]);;

let MATRIX_NEG_0 = prove
 (`--(mat 0) = mat 0`,
  SIMP_TAC[CART_EQ; mat; matrix_neg; LAMBDA_BETA; REAL_NEG_0; COND_ID]);;

let MATRIX_SUB_RZERO = prove
 (`!A:real^N^M. A - mat 0 = A`,
  SIMP_TAC[CART_EQ; mat; matrix_sub; LAMBDA_BETA; REAL_SUB_RZERO; COND_ID]);;

let MATRIX_SUB_LZERO = prove
 (`!A:real^N^M. mat 0 - A = --A`,
  SIMP_TAC[CART_EQ; mat; matrix_sub; matrix_neg;
           LAMBDA_BETA; REAL_SUB_LZERO; COND_ID]);;

let MATRIX_NEG_EQ_0 = prove
 (`!A:real^N^M. --A = mat 0 <=> A = mat 0`,
  SIMP_TAC[CART_EQ; matrix_neg; mat; LAMBDA_BETA; REAL_NEG_EQ_0; COND_ID]);;

let MATRIX_VECTOR_MUL_ASSOC = prove
 (`!A:real^N^M B:real^P^N x:real^P. A ** B ** x = (A ** B) ** x`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[matrix_mul; matrix_vector_mul;
           CART_EQ; LAMBDA_BETA; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let MATRIX_VECTOR_MUL_LID = prove
 (`!x:real^N. mat 1 ** x = x`,
  REWRITE_TAC[matrix_vector_mul;
   GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ]
    (SPEC_ALL mat)] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  SIMP_TAC[SUM_DELTA; REAL_MUL_LZERO; IN_NUMSEG; REAL_MUL_LID]);;

let MATRIX_VECTOR_MUL_LZERO = prove
 (`!x:real^N. mat 0 ** x = vec 0`,
  SIMP_TAC[mat; matrix_vector_mul; CART_EQ; VEC_COMPONENT; LAMBDA_BETA;
           COND_ID; REAL_MUL_LZERO; SUM_0]);;

let MATRIX_VECTOR_MUL_RZERO = prove
 (`!A:real^M^N. A ** vec 0 = vec 0`,
  SIMP_TAC[mat; matrix_vector_mul; CART_EQ; VEC_COMPONENT; LAMBDA_BETA;
           COND_ID; REAL_MUL_RZERO; SUM_0]);;

let MATRIX_VECTOR_MUL_ADD_LDISTRIB = prove
 (`!A:real^M^N x:real^M y. A ** (x + y) = A ** x + A ** y`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
           SUM_ADD_NUMSEG; REAL_ADD_LDISTRIB]);;

let MATRIX_VECTOR_MUL_SUB_LDISTRIB = prove
 (`!A:real^M^N x:real^M y. A ** (x - y) = A ** x - A ** y`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; VECTOR_SUB_COMPONENT; LAMBDA_BETA;
           SUM_SUB_NUMSEG; REAL_SUB_LDISTRIB]);;

let MATRIX_VECTOR_MUL_ADD_RDISTRIB = prove
 (`!A:real^M^N B x:real^M. (A + B) ** x = (A ** x) + (B ** x)`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; matrix_add; LAMBDA_BETA;
           VECTOR_ADD_COMPONENT; REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG]);;

let MATRIX_VECTOR_MUL_SUB_RDISTRIB = prove
 (`!A:real^M^N B x:real^M. (A - B) ** x = (A ** x) - (B ** x)`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; matrix_sub; LAMBDA_BETA;
           VECTOR_SUB_COMPONENT; REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG]);;

let MATRIX_VECTOR_MUL_RMUL = prove
 (`!A:real^M^N x:real^M c. A ** (c % x) = c % (A ** x)`,
  SIMP_TAC[CART_EQ; VECTOR_MUL_COMPONENT; matrix_vector_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN REWRITE_TAC[REAL_MUL_AC]);;

let MATRIX_MUL_LNEG = prove
 (`!A:real^N^M B:real^P^N. (--A) ** B = --(A ** B)`,
  REWRITE_TAC[MATRIX_NEG_MINUS1; MATRIX_MUL_LMUL]);;

let MATRIX_MUL_RNEG = prove
 (`!A:real^N^M B:real^P^N. A ** --B = --(A ** B)`,
  REWRITE_TAC[MATRIX_NEG_MINUS1; MATRIX_MUL_RMUL]);;

let MATRIX_NEG_NEG = prove
 (`!A:real^N^N. --(--A) = A`,
  SIMP_TAC[CART_EQ; MATRIX_NEG_COMPONENT; REAL_NEG_NEG]);;

let MATRIX_TRANSP_MUL = prove
 (`!A B. transp(A ** B) = transp(B) ** transp(A)`,
  SIMP_TAC[matrix_mul; transp; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let TRANSP_EQ_0 = prove
 (`!A:real^N^M. transp A = mat 0 <=> A = mat 0`,
  REWRITE_TAC[MAT_0_COMPONENT; CART_EQ; TRANSP_COMPONENT] THEN MESON_TAC[]);;

let SYMMETRIC_MATRIX_MUL = prove
 (`!A B:real^N^N.
        transp(A) = A /\ transp(B) = B
        ==> (transp(A ** B) = A ** B <=> A ** B = B ** A)`,
  SIMP_TAC[MATRIX_TRANSP_MUL] THEN MESON_TAC[]);;

let MATRIX_EQ = prove
 (`!A:real^N^M B. (A = B) = !x:real^N. A ** x = B ** x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN `i:num` o SPEC `(basis i):real^N`) THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; basis] THEN
  SIMP_TAC[SUM_DELTA; COND_RAND; REAL_MUL_RZERO] THEN
  REWRITE_TAC[TAUT `(if p then b else T) <=> p ==> b`] THEN
  SIMP_TAC[REAL_MUL_RID; IN_NUMSEG]);;

let MATRIX_EQ_0 = prove
 (`!A:real^N^N. A = mat 0 <=> !x. A ** x = vec 0`,
  REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LZERO]);;

let MATRIX_VECTOR_MUL_COMPONENT = prove
 (`!A:real^N^M x k.
    1 <= k /\ k <= dimindex(:M) ==> ((A ** x)$k = (A$k) dot x)`,
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; dot]);;

let DOT_LMUL_MATRIX = prove
 (`!A:real^N^M x:real^M y:real^N. (x ** A) dot y = x dot (A ** y)`,
  SIMP_TAC[dot; matrix_vector_mul; vector_matrix_mul; dot; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_AC]);;

let TRANSP_MATRIX_CMUL = prove
 (`!A:real^M^N c. transp(c %% A) = c %% transp A`,
  SIMP_TAC[CART_EQ; transp; MATRIX_CMUL_COMPONENT; LAMBDA_BETA]);;

let TRANSP_MATRIX_ADD = prove
 (`!A B:real^N^M. transp(A + B) = transp A + transp B`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; matrix_add]);;

let TRANSP_MATRIX_SUB = prove
 (`!A B:real^N^M. transp(A - B) = transp A - transp B`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; matrix_sub]);;

let TRANSP_MATRIX_NEG = prove
 (`!A:real^N^M. transp(--A) = --(transp A)`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; matrix_neg]);;

let TRANSP_MAT = prove
 (`!n. transp(mat n) = mat n`,
  SIMP_TAC[transp; mat; LAMBDA_BETA; CART_EQ; EQ_SYM_EQ]);;

let TRANSP_TRANSP = prove
 (`!A:real^N^M. transp(transp A) = A`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA]);;

let SYMMETRIX_MATRIX_CONJUGATE = prove
 (`!A B:real^N^N. transp B = B
                  ==> transp(transp A ** B ** A) = transp A ** B ** A`,
  SIMP_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC]);;

let TRANSP_EQ = prove
 (`!A B:real^M^N. transp A = transp B <=> A = B`,
  MESON_TAC[TRANSP_TRANSP]);;

let ROW_TRANSP = prove
 (`!A:real^N^M i.
        1 <= i /\ i <= dimindex(:N) ==> row i (transp A) = column i A`,
  SIMP_TAC[row; column; transp; CART_EQ; LAMBDA_BETA]);;

let COLUMN_TRANSP = prove
 (`!A:real^N^M i.
        1 <= i /\ i <= dimindex(:M) ==> column i (transp A) = row i A`,
  SIMP_TAC[row; column; transp; CART_EQ; LAMBDA_BETA]);;

let ROWS_TRANSP = prove
 (`!A:real^N^M. rows(transp A) = columns A`,
  REWRITE_TAC[rows; columns; EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[ROW_TRANSP]);;

let COLUMNS_TRANSP = prove
 (`!A:real^N^M. columns(transp A) = rows A`,
  MESON_TAC[TRANSP_TRANSP; ROWS_TRANSP]);;

let VECTOR_MATRIX_MUL_TRANSP = prove
 (`!A:real^M^N x:real^N. x ** A = transp A ** x`,
  REWRITE_TAC[matrix_vector_mul; vector_matrix_mul; transp] THEN
  SIMP_TAC[LAMBDA_BETA; CART_EQ]);;

let MATRIX_VECTOR_MUL_TRANSP = prove
 (`!A:real^M^N x:real^M. A ** x = x ** transp A`,
  REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP; TRANSP_TRANSP]);;

let ROWS_NONEMPTY = prove
 (`!A:real^N^M. ~(rows A = {})`,
  REWRITE_TAC[rows] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; GSYM numseg; NUMSEG_EMPTY] THEN
  REWRITE_TAC[NOT_LT; DIMINDEX_GE_1]);;

let COLUMNS_NONEMPTY = prove
 (`!A:real^N^M. ~(columns A = {})`,
  REWRITE_TAC[columns] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; GSYM numseg; NUMSEG_EMPTY] THEN
  REWRITE_TAC[NOT_LT; DIMINDEX_GE_1]);;

let FINITE_ROWS = prove
 (`!A:real^N^M. FINITE(rows A)`,
  REWRITE_TAC[rows] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  SIMP_TAC[GSYM numseg; FINITE_IMAGE; FINITE_NUMSEG]);;

let FINITE_COLUMNS = prove
 (`!A:real^N^M. FINITE(columns A)`,
  REWRITE_TAC[columns] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  SIMP_TAC[GSYM numseg; FINITE_IMAGE; FINITE_NUMSEG]);;

let CARD_ROWS_LE = prove
 (`!A:real^M^N. CARD(rows A) <= dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[rows] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM numseg] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
  SIMP_TAC[CARD_IMAGE_LE; FINITE_NUMSEG]);;

let CARD_COLUMNS_LE = prove
 (`!A:real^M^N. CARD(columns A) <= dimindex(:M)`,
  GEN_TAC THEN REWRITE_TAC[columns] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM numseg] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
  SIMP_TAC[CARD_IMAGE_LE; FINITE_NUMSEG]);;

let MATRIX_EQUAL_ROWS = prove
 (`!A B:real^N^M.
        A = B <=> !i. 1 <= i /\ i <= dimindex(:M) ==> row i A = row i B`,
  SIMP_TAC[row; CART_EQ; LAMBDA_BETA]);;

let MATRIX_EQUAL_COLUMNS = prove
 (`!A B:real^N^M.
        A = B <=> !i. 1 <= i /\ i <= dimindex(:N) ==> column i A = column i B`,
  SIMP_TAC[column; CART_EQ; LAMBDA_BETA] THEN MESON_TAC[]);;

let MATRIX_CMUL_EQ_0 = prove
 (`!A:real^M^N c. c %% A = mat 0 <=> c = &0 \/ A = mat 0`,
  SIMP_TAC[CART_EQ; MATRIX_CMUL_COMPONENT; MAT_COMPONENT; COND_ID] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[REAL_ENTIRE]);;

let MAT_EQ = prove
 (`!m n. mat m = mat n <=> m = n`,
  SIMP_TAC[CART_EQ; MAT_COMPONENT] THEN REPEAT STRIP_TAC THEN
  MESON_TAC[REAL_OF_NUM_EQ; DIMINDEX_GE_1; LE_REFL]);;

let MATRIX_VECTOR_LMUL = prove
 (`!A:real^M^N c x:real^M. (c %% A) ** x = c % (A ** x)`,
  SIMP_TAC[matrix_cmul; CART_EQ; LAMBDA_BETA; matrix_vector_mul;
           VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL]);;

let COLUMN_MATRIX_MUL = prove
 (`!A:real^N^M B:real^P^N.
      1 <= i /\ i <= dimindex(:P) ==> column i (A ** B) = A ** column i B`,
  SIMP_TAC[column; matrix_mul; matrix_vector_mul; LAMBDA_BETA; CART_EQ]);;

let ROW_MATRIX_MUL = prove
 (`!A:real^N^M B:real^P^N.
      1 <= i /\ i <= dimindex(:M) ==> row i (A ** B) = transp B ** row i A`,
  SIMP_TAC[GSYM COLUMN_TRANSP] THEN
  SIMP_TAC[MATRIX_TRANSP_MUL; COLUMN_MATRIX_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Two sometimes fruitful ways of looking at matrix-vector multiplication.   *)
(* ------------------------------------------------------------------------- *)

let MATRIX_MUL_DOT = prove
 (`!A:real^N^M x. A ** x = lambda i. A$i dot x`,
  REWRITE_TAC[matrix_vector_mul; dot] THEN SIMP_TAC[CART_EQ; LAMBDA_BETA]);;

let MATRIX_MUL_VSUM = prove
 (`!A:real^N^M x. A ** x = vsum(1..dimindex(:N)) (\i. x$i % column i A)`,
  SIMP_TAC[matrix_vector_mul; CART_EQ; VSUM_COMPONENT; LAMBDA_BETA;
           VECTOR_MUL_COMPONENT; column; REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Slightly gruesome lemmas: better to define sums over vectors really...    *)
(* ------------------------------------------------------------------------- *)

let VECTOR_COMPONENTWISE = prove
 (`!x:real^N.
    x = lambda j. sum(1..dimindex(:N))
                     (\i. x$i * (basis i :real^N)$j)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; basis] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(m:num = n) <=> (n = m)`] THEN
  SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG] THEN
  REWRITE_TAC[REAL_MUL_RID; COND_ID]);;

let LINEAR_COMPONENTWISE_EXPANSION = prove
 (`!f:real^M->real^N.
      linear(f)
      ==> !x j. 1 <= j /\ j <= dimindex(:N)
                ==> (f x $j =
                     sum(1..dimindex(:M)) (\i. x$i * f(basis i)$j))`,
  REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
   [VECTOR_COMPONENTWISE] THEN
  SPEC_TAC(`dimindex(:M)`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THENL
   [REWRITE_TAC[GSYM vec] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
     [GSYM VECTOR_MUL_LZERO] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC[vec; LAMBDA_BETA];
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
    ASSUM_LIST(fun thl -> REWRITE_TAC(map GSYM thl)) THEN
    SIMP_TAC[GSYM VECTOR_MUL_COMPONENT;
             ASSUME `1 <= j`; ASSUME `j <= dimindex(:N)`] THEN
    ASSUM_LIST(fun thl -> REWRITE_TAC(map GSYM thl)) THEN
    SIMP_TAC[GSYM VECTOR_ADD_COMPONENT;
             ASSUME `1 <= j`; ASSUME `j <= dimindex(:N)`] THEN
    ASSUM_LIST(fun thl -> REWRITE_TAC(map GSYM thl)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT]]);;

(* ------------------------------------------------------------------------- *)
(* Invertible matrices (not assumed square, but it's vacuous otherwise).     *)
(* ------------------------------------------------------------------------- *)

let invertible = new_definition
  `invertible(A:real^N^M) <=>
        ?A':real^M^N. (A ** A' = mat 1) /\ (A' ** A = mat 1)`;;

let INVERTIBLE_I = prove
 (`invertible(mat 1:real^N^N)`,
  REWRITE_TAC[invertible] THEN MESON_TAC[MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let INVERTIBLE_NEG = prove
 (`!A:real^N^M. invertible(--A) <=> invertible A`,
  REWRITE_TAC[invertible] THEN
  MESON_TAC[MATRIX_MUL_LNEG; MATRIX_MUL_RNEG; MATRIX_NEG_NEG]);;

let INVERTIBLE_CMUL = prove
 (`!A:real^N^M c. invertible(c %% A) <=> ~(c = &0) /\ invertible(A)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[invertible; MATRIX_MUL_LZERO; MATRIX_CMUL_LZERO; MAT_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[invertible; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^M^N` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `c %% B:real^M^N`;
    EXISTS_TAC `inv c %% B:real^M^N`] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_RINV; MATRIX_CMUL_LID]);;

let INVERTIBLE_MAT = prove
 (`!a. invertible(mat a:real^N^N) <=> ~(a = 0)`,
  ONCE_REWRITE_TAC[MAT_CMUL] THEN
  REWRITE_TAC[INVERTIBLE_CMUL; INVERTIBLE_I; REAL_OF_NUM_EQ]);;

let MATRIX_ENTIRE = prove
 (`(!A:real^N^M B:real^P^N. invertible A ==> (A ** B = mat 0 <=> B = mat 0)) /\
   (!A:real^N^M B:real^P^N. invertible B ==> (A ** B = mat 0 <=> A = mat 0))`,
  REWRITE_TAC[invertible] THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `A':real^M^N` STRIP_ASSUME_TAC);
    DISCH_THEN(X_CHOOSE_THEN `B':real^N^P` STRIP_ASSUME_TAC)] THEN
  EQ_TAC THEN SIMP_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO] THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(**) A':real^P^M->real^P^N`) THEN
    ASM_REWRITE_TAC[MATRIX_MUL_ASSOC; MATRIX_MUL_LID; MATRIX_MUL_RZERO];
    DISCH_THEN(MP_TAC o AP_TERM `\C:real^P^M. C ** (B':real^N^P)`) THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID;
                    MATRIX_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence between matrices and linear operators.                     *)
(* ------------------------------------------------------------------------- *)

let matrix = new_definition
  `(matrix:(real^M->real^N)->real^M^N) f = lambda i j. f(basis j)$i`;;

let MATRIX_VECTOR_MUL_LINEAR = prove
 (`!A:real^N^M. linear(\x. A ** x)`,
  REWRITE_TAC[linear; matrix_vector_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
    VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ADD_AC; REAL_MUL_AC]);;

let MATRIX_WORKS = prove
 (`!f:real^M->real^N. linear f ==> !x. matrix f ** x = f(x)`,
  REWRITE_TAC[matrix; matrix_vector_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM LINEAR_COMPONENTWISE_EXPANSION]);;

let MATRIX_VECTOR_MUL = prove
 (`!f:real^M->real^N. linear f ==> f = \x. matrix f ** x`,
  SIMP_TAC[FUN_EQ_THM; MATRIX_WORKS]);;

let MATRIX_OF_MATRIX_VECTOR_MUL = prove
 (`!A:real^N^M. matrix(\x. A ** x) = A`,
  SIMP_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LINEAR; MATRIX_WORKS]);;

let MATRIX_COMPOSE = prove
 (`!f g. linear f /\ linear g ==> (matrix(g o f) = matrix g ** matrix f)`,
  SIMP_TAC[MATRIX_EQ; MATRIX_WORKS; LINEAR_COMPOSE;
           GSYM MATRIX_VECTOR_MUL_ASSOC; o_THM]);;

let MATRIX_VECTOR_COLUMN = prove
 (`!A:real^N^M x.
        A ** x = vsum(1..dimindex(:N)) (\i. x$i % (transp A)$i)`,
  REWRITE_TAC[matrix_vector_mul; transp] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let MATRIX_MUL_COMPONENT = prove
 (`!i. 1 <= i /\ i <= dimindex(:N)
       ==> ((A:real^N^N) ** (B:real^N^N))$i = transp B ** A$i`,
  SIMP_TAC[matrix_mul; LAMBDA_BETA; matrix_vector_mul; vector_matrix_mul;
       transp; CART_EQ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let ADJOINT_MATRIX = prove
 (`!A:real^N^M. adjoint(\x. A ** x) = (\x. transp A ** x)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN REPEAT GEN_TAC THEN
  SIMP_TAC[transp; dot; LAMBDA_BETA; matrix_vector_mul;
           GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_AC]);;

let MATRIX_ADJOINT = prove
 (`!f. linear f ==> matrix(adjoint f) = transp(matrix f)`,
  GEN_TAC THEN DISCH_THEN
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV)
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
  REWRITE_TAC[ADJOINT_MATRIX; MATRIX_OF_MATRIX_VECTOR_MUL]);;

let MATRIX_ID = prove
 (`matrix(\x. x) = mat 1`,
  SIMP_TAC[MATRIX_EQ; LINEAR_ID; MATRIX_WORKS; MATRIX_VECTOR_MUL_LID]);;

let MATRIX_I = prove
 (`matrix I = mat 1`,
  REWRITE_TAC[I_DEF; MATRIX_ID]);;

let LINEAR_EQ_MATRIX = prove
 (`!f g. linear f /\ linear g /\ matrix f = matrix g ==> f = g`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MATRIX_VECTOR_MUL)) THEN
  ASM_REWRITE_TAC[]);;

let MATRIX_CMUL = prove
 (`!f:real^M->real^N c.
        linear f ==> matrix(\x. c % f x) = c %% matrix f`,
  SIMP_TAC[MATRIX_EQ; MATRIX_WORKS; LINEAR_COMPOSE_CMUL; MATRIX_VECTOR_LMUL]);;

let MATRIX_NEG = prove
 (`!f:real^M->real^N.
        linear f ==> matrix(\x. --(f x)) = --(matrix f)`,
  SIMP_TAC[GSYM MATRIX_NEG_MINUS1; VECTOR_NEG_MINUS1; MATRIX_CMUL]);;

let MATRIX_ADD = prove
 (`!f g:real^M->real^N.
        linear f /\ linear g ==> matrix(\x. f x + g x) = matrix f + matrix g`,
  REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN
  SIMP_TAC[MATRIX_WORKS; LINEAR_COMPOSE_ADD]);;

let MATRIX_SELF_ADJOINT = prove
 (`!f. linear f ==> (adjoint f = f <=> transp(matrix f) = matrix f)`,
  SIMP_TAC[GSYM MATRIX_ADJOINT] THEN
  MESON_TAC[LINEAR_EQ_MATRIX; ADJOINT_LINEAR]);;

let LINEAR_MATRIX_EXISTS = prove
 (`!f:real^M->real^N. linear f <=> ?A:real^M^N. f = \x. A ** x`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_LINEAR; LEFT_IMP_EXISTS_THM] THEN
  DISCH_TAC THEN EXISTS_TAC `matrix(f:real^M->real^N)` THEN
  ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL]);;

let LINEAR_1_GEN = prove
 (`!f:real^N->real^N.
        dimindex(:N) = 1 ==> (linear f <=> ?c. f = \x. c % x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_ID] THEN
  ASM_SIMP_TAC[FUN_EQ_THM; CART_EQ; FORALL_1] THEN
  EXISTS_TAC `(f:real^N->real^N)(basis 1)$1` THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_COMPONENT] THEN
  X_GEN_TAC `x:real^N` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [linear]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; FORALL_1; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
               ARITH; REAL_MUL_RID]);;

let LINEAR_1 = prove
 (`!f:real^1->real^1. linear f <=> ?c. f = \x. c % x`,
  SIMP_TAC[LINEAR_1_GEN; DIMINDEX_1]);;

let SYMMETRIC_MATRIX = prove
 (`!A:real^N^N. transp A = A <=> adjoint(\x. A ** x) = \x. A ** x`,
  SIMP_TAC[MATRIX_SELF_ADJOINT; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL]);;

let DOT_MATRIX_TRANSP_LMUL = prove
 (`!A x y:real^N. (transp A ** x) dot y = x dot (A ** y)`,
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] (GSYM ADJOINT_MATRIX)] THEN
  SIMP_TAC[ADJOINT_CLAUSES; MATRIX_VECTOR_MUL_LINEAR]);;

let DOT_MATRIX_TRANSP_RMUL = prove
 (`!A x y:real^N. x dot (transp A ** y) = (A ** x) dot y`,
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL]);;

let SYMMETRIC_MATRIX_ORTHOGONAL_EIGENVECTORS = prove
 (`!A:real^N^N v w a b.
        transp A = A /\ A ** v = a % v /\ A ** w = b % w /\ ~(a = b)
        ==> orthogonal v w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SYMMETRIC_MATRIX] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS)) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

(* ------------------------------------------------------------------------- *)
(* Operator norm.                                                            *)
(* ------------------------------------------------------------------------- *)

let onorm = new_definition
 `onorm (f:real^M->real^N) = sup { norm(f x) | norm(x) = &1 }`;;

let NORM_BOUND_GENERALIZE = prove
 (`!f:real^M->real^N b.
        linear f
        ==> ((!x. (norm(x) = &1) ==> norm(f x) <= b) <=>
             (!x. norm(f x) <= b * norm(x)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_MUL_RID]] THEN
  X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `x:real^M = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO] THEN
    ASM_MESON_TAC[LINEAR_0; NORM_0; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; NORM_POS_LT; real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(a * b) <= c ==> b * a <= c`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; GSYM NORM_MUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV;
               NORM_EQ_0]);;

let ONORM = prove
 (`!f:real^M->real^N.
        linear f
        ==> (!x. norm(f x) <= onorm f * norm(x)) /\
            (!b. (!x. norm(f x) <= b * norm(x)) ==> onorm f <= b)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `{ norm((f:real^M->real^N) x) | norm(x) = &1 }` SUP) THEN
  SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  ASM_SIMP_TAC[NORM_BOUND_GENERALIZE; GSYM onorm; GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[VECTOR_CHOOSE_SIZE; LINEAR_BOUNDED; REAL_POS]);;

let ONORM_POS_LE = prove
 (`!f. linear f ==> &0 <= onorm f`,
  MESON_TAC[ONORM; VECTOR_CHOOSE_SIZE; REAL_POS; REAL_MUL_RID; NORM_POS_LE;
            REAL_LE_TRANS]);;

let ONORM_EQ_0 = prove
 (`!f:real^M->real^N. linear f ==> ((onorm f = &0) <=> (!x. f x = vec 0))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `f:real^M->real^N` ONORM) THEN
  ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; ONORM_POS_LE; NORM_0; REAL_MUL_LZERO;
               NORM_LE_0; REAL_LE_REFL]);;

let ONORM_CONST = prove
 (`!y:real^N. onorm(\x:real^M. y) = norm(y)`,
  GEN_TAC THEN REWRITE_TAC[onorm] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sup {norm(y:real^N)}` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `(?x. P x) ==> {f y | x | P x} = {f y}`) THEN
    EXISTS_TAC `basis 1 :real^M` THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL];
    MATCH_MP_TAC REAL_SUP_UNIQUE THEN SET_TAC[REAL_LE_REFL]]);;

let ONORM_POS_LT = prove
 (`!f. linear f ==> (&0 < onorm f <=> ~(!x. f x = vec 0))`,
  SIMP_TAC[GSYM ONORM_EQ_0; ONORM_POS_LE;
           REAL_ARITH `(&0 < x <=> ~(x = &0)) <=> &0 <= x`]);;

let ONORM_COMPOSE = prove
 (`!f g. linear f /\ linear g ==> onorm(f o g) <= onorm f * onorm g`,
  MESON_TAC[ONORM; LINEAR_COMPOSE; o_THM; REAL_MUL_ASSOC; REAL_LE_TRANS; ONORM;
            REAL_LE_LMUL; ONORM_POS_LE]);;

let ONORM_NEG_LEMMA = prove
 (`!f. linear f ==> onorm(\x. --(f x)) <= onorm f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ONORM o
    MATCH_MP LINEAR_COMPOSE_NEG) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[NORM_NEG; ONORM]);;

let ONORM_NEG = prove
 (`!f:real^M->real^N. linear f ==> (onorm(\x. --(f x)) = onorm f)`,
  REPEAT STRIP_TAC THEN  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  ASM_SIMP_TAC[ONORM_NEG_LEMMA] THEN
  SUBGOAL_THEN `f:real^M->real^N = \x. --(--(f x))`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  ASM_SIMP_TAC[ONORM_NEG_LEMMA; LINEAR_COMPOSE_NEG] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let ONORM_TRIANGLE = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g ==> onorm(\x. f x + g x) <= onorm f + onorm g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o MATCH_MP ONORM o MATCH_MP
              LINEAR_COMPOSE_ADD) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  ASM_MESON_TAC[REAL_LE_ADD2; REAL_LE_TRANS; NORM_TRIANGLE; ONORM]);;

let ONORM_TRIANGLE_LE = prove
 (`!f g. linear f /\ linear g /\ onorm(f) + onorm(g) <= e
         ==> onorm(\x. f x + g x) <= e`,
  MESON_TAC[REAL_LE_TRANS; ONORM_TRIANGLE]);;

let ONORM_TRIANGLE_LT = prove
 (`!f g. linear f /\ linear g /\ onorm(f) + onorm(g) < e
         ==> onorm(\x. f x + g x) < e`,
  MESON_TAC[REAL_LET_TRANS; ONORM_TRIANGLE]);;

let ONORM_ID = prove
 (`onorm(\x:real^N. x) = &1`,
  REWRITE_TAC[onorm] THEN
  SUBGOAL_THEN `{norm(x:real^N) | norm x = &1} = {&1}`
   (fun th -> REWRITE_TAC[th; SUP_SING]) THEN
  SUBGOAL_THEN `norm(basis 1:real^N) = &1` MP_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL]; SET_TAC[]]);;

let ONORM_I = prove
 (`onorm(I:real^N->real^N) = &1`,
  REWRITE_TAC[I_DEF; ONORM_ID]);;

(* ------------------------------------------------------------------------- *)
(* It's handy to "lift" from R to R^1 and "drop" from R^1 to R.              *)
(* ------------------------------------------------------------------------- *)

let lift = new_definition
 `(lift:real->real^1) x = lambda i. x`;;

let drop = new_definition
 `(drop:real^1->real) x = x$1`;;

let LIFT_COMPONENT = prove
 (`!x. (lift x)$1 = x`,
  SIMP_TAC[lift; LAMBDA_BETA; DIMINDEX_1; LE_ANTISYM]);;

let LIFT_DROP = prove
 (`(!x. lift(drop x) = x) /\ (!x. drop(lift x) = x)`,
  SIMP_TAC[lift; drop; CART_EQ; LAMBDA_BETA; DIMINDEX_1; LE_ANTISYM]);;

let IMAGE_LIFT_DROP = prove
 (`(!s. IMAGE (lift o drop) s = s) /\ (!s. IMAGE (drop o lift) s = s)`,
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN SET_TAC[]);;

let IN_IMAGE_LIFT_DROP = prove
 (`(!x s. x IN IMAGE lift s <=> drop x IN s) /\
   (!x s. x IN IMAGE drop s <=> lift x IN s)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LIFT_DROP]);;

let FORALL_LIFT = prove
 (`(!x. P x) = (!x. P(lift x))`,
  MESON_TAC[LIFT_DROP]);;

let EXISTS_LIFT = prove
 (`(?x. P x) = (?x. P(lift x))`,
  MESON_TAC[LIFT_DROP]);;

let FORALL_DROP = prove
 (`(!x. P x) = (!x. P(drop x))`,
  MESON_TAC[LIFT_DROP]);;

let EXISTS_DROP = prove
 (`(?x. P x) = (?x. P(drop x))`,
  MESON_TAC[LIFT_DROP]);;

let FORALL_LIFT_FUN = prove
 (`!P:(A->real^1)->bool. (!f. P f) <=> (!f. P(lift o f))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `f:A->real^1` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop o (f:A->real^1)`) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]);;

let FORALL_DROP_FUN = prove
 (`!P:(A->real)->bool. (!f. P f) <=> (!f. P(drop o f))`,
  REWRITE_TAC[FORALL_LIFT_FUN; o_DEF; LIFT_DROP; ETA_AX]);;

let EXISTS_LIFT_FUN = prove
 (`!P:(A->real^1)->bool. (?f. P f) <=> (?f. P(lift o f))`,
  ONCE_REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_LIFT_FUN]);;

let EXISTS_DROP_FUN = prove
 (`!P:(A->real)->bool. (?f. P f) <=> (?f. P(drop o f))`,
  ONCE_REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_DROP_FUN]);;

let LIFT_EQ = prove
 (`!x y. (lift x = lift y) <=> (x = y)`,
  MESON_TAC[LIFT_DROP]);;

let DROP_EQ = prove
 (`!x y. (drop x = drop y) <=> (x = y)`,
  MESON_TAC[LIFT_DROP]);;

let LIFT_IN_IMAGE_LIFT = prove
 (`!x s. (lift x) IN (IMAGE lift s) <=> x IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LIFT_DROP]);;

let FORALL_LIFT_IMAGE = prove
 (`!P. (!s. P s) <=> (!s. P(IMAGE lift s))`,
  MESON_TAC[IMAGE_LIFT_DROP; IMAGE_o]);;

let EXISTS_LIFT_IMAGE = prove
 (`!P. (?s. P s) <=> (?s. P(IMAGE lift s))`,
  MESON_TAC[IMAGE_LIFT_DROP; IMAGE_o]);;

let SUBSET_LIFT_IMAGE = prove
 (`!s t. IMAGE lift s SUBSET IMAGE lift t <=> s SUBSET t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[IMAGE_SUBSET] THEN
  DISCH_THEN(MP_TAC o ISPEC `drop` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP]);;

let FORALL_DROP_IMAGE = prove
 (`!P. (!s. P s) <=> (!s. P(IMAGE drop s))`,
  MESON_TAC[IMAGE_LIFT_DROP; IMAGE_o]);;

let EXISTS_DROP_IMAGE = prove
 (`!P. (?s. P s) <=> (?s. P(IMAGE drop s))`,
  MESON_TAC[IMAGE_LIFT_DROP; IMAGE_o]);;

let SUBSET_DROP_IMAGE = prove
 (`!s t. IMAGE drop s SUBSET IMAGE drop t <=> s SUBSET t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[IMAGE_SUBSET] THEN
  DISCH_THEN(MP_TAC o ISPEC `lift` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP]);;

let DROP_IN_IMAGE_DROP = prove
 (`!x s. (drop x) IN (IMAGE drop s) <=> x IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LIFT_DROP]);;

let LIFT_NUM = prove
 (`!n. lift(&n) = vec n`,
  SIMP_TAC[CART_EQ; lift; vec; LAMBDA_BETA]);;

let LIFT_ADD = prove
 (`!x y. lift(x + y) = lift x + lift y`,
  SIMP_TAC[CART_EQ; lift; LAMBDA_BETA; VECTOR_ADD_COMPONENT]);;

let LIFT_SUB = prove
 (`!x y. lift(x - y) = lift x - lift y`,
  SIMP_TAC[CART_EQ; lift; LAMBDA_BETA; VECTOR_SUB_COMPONENT]);;

let LIFT_CMUL = prove
 (`!x c. lift(c * x) = c % lift(x)`,
  SIMP_TAC[CART_EQ; lift; LAMBDA_BETA; VECTOR_MUL_COMPONENT]);;

let LIFT_NEG = prove
 (`!x. lift(--x) = --(lift x)`,
  SIMP_TAC[CART_EQ; lift; LAMBDA_BETA; VECTOR_NEG_COMPONENT]);;

let LIFT_EQ_CMUL = prove
 (`!x. lift x = x % vec 1`,
  REWRITE_TAC[GSYM LIFT_NUM; GSYM LIFT_CMUL; REAL_MUL_RID]);;

let SUM_VSUM = prove
 (`!f s. sum s f = drop(vsum s(lift o f))`,
  SIMP_TAC[vsum; drop; LAMBDA_BETA; DIMINDEX_1; ARITH] THEN
  REWRITE_TAC[o_THM; GSYM drop; LIFT_DROP; ETA_AX]);;

let VSUM_REAL = prove
 (`!f s. vsum s f = lift(sum s (drop o f))`,
  REWRITE_TAC[o_DEF; SUM_VSUM; LIFT_DROP; ETA_AX]);;

let LIFT_SUM = prove
 (`!k x. lift(sum k x) = vsum k (lift o x)`,
  REWRITE_TAC[SUM_VSUM; LIFT_DROP]);;

let DROP_VSUM = prove
 (`!k x. drop(vsum k x) = sum k (drop o x)`,
  REWRITE_TAC[VSUM_REAL; LIFT_DROP]);;

let DROP_LAMBDA = prove
 (`!x. drop(lambda i. x i) = x 1`,
  SIMP_TAC[drop; LAMBDA_BETA; DIMINDEX_1; LE_REFL]);;

let DROP_VEC = prove
 (`!n. drop(vec n) = &n`,
  MESON_TAC[LIFT_DROP; LIFT_NUM]);;

let DROP_ADD = prove
 (`!x y. drop(x + y) = drop x + drop y`,
  MESON_TAC[LIFT_DROP; LIFT_ADD]);;

let DROP_SUB = prove
 (`!x y. drop(x - y) = drop x - drop y`,
  MESON_TAC[LIFT_DROP; LIFT_SUB]);;

let DROP_CMUL = prove
 (`!x c. drop(c % x) = c * drop(x)`,
  MESON_TAC[LIFT_DROP; LIFT_CMUL]);;

let DROP_NEG = prove
 (`!x. drop(--x) = --(drop x)`,
  MESON_TAC[LIFT_DROP; LIFT_NEG]);;

let NORM_1 = prove
 (`!x. norm x = abs(drop x)`,
  REWRITE_TAC[drop; NORM_REAL]);;

let NORM_1_POS = prove
 (`!x. &0 <= drop x ==> norm x = drop x`,
  SIMP_TAC[NORM_1; real_abs]);;

let NORM_LIFT = prove
 (`!x. norm(lift x) = abs(x)`,
  SIMP_TAC[lift; NORM_REAL; LIFT_COMPONENT]);;

let DIST_LIFT = prove
 (`!x y. dist(lift x,lift y) = abs(x - y)`,
  REWRITE_TAC[DIST_REAL; LIFT_COMPONENT]);;

let ABS_DROP = prove
 (`!x. norm x = abs(drop x)`,
  REWRITE_TAC[FORALL_LIFT; LIFT_DROP; NORM_LIFT]);;

let LINEAR_VMUL_DROP = prove
 (`!f v. linear f ==> linear (\x. drop(f x) % v)`,
  SIMP_TAC[drop; LINEAR_VMUL_COMPONENT; DIMINDEX_1; LE_REFL]);;

let LINEAR_FROM_REALS = prove
 (`!f:real^1->real^N. linear f ==> f = \x. drop x % column 1 (matrix f)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; vector_mul; LAMBDA_BETA;
           DIMINDEX_1; SUM_SING_NUMSEG; drop; column] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let LINEAR_TO_REALS = prove
 (`!f:real^N->real^1. linear f ==> f = \x. lift(row 1 (matrix f) dot x)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; dot; LAMBDA_BETA;
           DIMINDEX_1; SUM_SING_NUMSEG; lift; row; LE_ANTISYM]);;

let DROP_EQ_0 = prove
 (`!x. drop x = &0 <=> x = vec 0`,
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]);;

let DROP_WLOG_LE = prove
 (`(!x y. P x y <=> P y x) /\ (!x y. drop x <= drop y ==> P x y)
   ==> (!x y. P x y)`,
  MESON_TAC[REAL_LE_TOTAL]);;

let IMAGE_LIFT_UNIV = prove
 (`IMAGE lift (:real) = (:real^1)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN MESON_TAC[LIFT_DROP]);;

let IMAGE_DROP_UNIV = prove
 (`IMAGE drop (:real^1) = (:real)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN MESON_TAC[LIFT_DROP]);;

let LINEAR_LIFT_DOT = prove
 (`!a. linear(\x. lift(a dot x))`,
  REWRITE_TAC[linear; DOT_RMUL; DOT_RADD; LIFT_ADD; LIFT_CMUL]);;

let LINEAR_LIFT_COMPONENT = prove
 (`!k. linear(\x:real^N. lift(x$k))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:N) /\ !z:real^N. z$k = z$j`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    MP_TAC(ISPEC `basis j:real^N` LINEAR_LIFT_DOT) THEN
    ASM_SIMP_TAC[DOT_BASIS]]);;

let BILINEAR_DROP_MUL = prove
 (`bilinear (\x y:real^N. drop x % y)`,
  REWRITE_TAC[bilinear; linear] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPONENTWISE = prove
 (`!f:real^M->real^N.
        linear f <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> linear(\x. lift(f(x)$i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linear] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN
  SIMP_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pasting vectors.                                                          *)
(* ------------------------------------------------------------------------- *)

let LINEAR_FSTCART = prove
 (`linear fstcart`,
  SIMP_TAC[linear; fstcart; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; DIMINDEX_FINITE_SUM;
           ARITH_RULE `x <= a ==> x <= a + b:num`]);;

let LINEAR_SNDCART = prove
 (`linear sndcart`,
  SIMP_TAC[linear; sndcart; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; DIMINDEX_FINITE_SUM;
           ARITH_RULE `x <= a ==> x <= a + b:num`;
           ARITH_RULE `x <= b ==> x + a <= a + b:num`]);;

let FSTCART_VEC = prove
 (`!n. fstcart(vec n) = vec n`,
  SIMP_TAC[vec; fstcart; LAMBDA_BETA; CART_EQ; DIMINDEX_FINITE_SUM;
           ARITH_RULE `m <= n:num ==> m <= n + p`]);;

let FSTCART_ADD = prove
 (`!x:real^(M,N)finite_sum y. fstcart(x + y) = fstcart(x) + fstcart(y)`,
  REWRITE_TAC[REWRITE_RULE[linear] LINEAR_FSTCART]);;

let FSTCART_CMUL = prove
 (`!x:real^(M,N)finite_sum c. fstcart(c % x) = c % fstcart(x)`,
  REWRITE_TAC[REWRITE_RULE[linear] LINEAR_FSTCART]);;

let FSTCART_NEG = prove
 (`!x:real^(M,N)finite_sum. --(fstcart x) = fstcart(--x)`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `--x = --(&1) % x`] THEN
  REWRITE_TAC[FSTCART_CMUL]);;

let FSTCART_SUB = prove
 (`!x:real^(M,N)finite_sum y. fstcart(x - y) = fstcart(x) - fstcart(y)`,
  REWRITE_TAC[VECTOR_SUB; FSTCART_NEG; FSTCART_ADD]);;

let FSTCART_VSUM = prove
 (`!k x. FINITE k ==> (fstcart(vsum k x) = vsum k (\i. fstcart(x i)))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_RULES; FSTCART_ADD; FSTCART_VEC]);;

let SNDCART_VEC = prove
 (`!n. sndcart(vec n) = vec n`,
  SIMP_TAC[vec; sndcart; LAMBDA_BETA; CART_EQ; DIMINDEX_FINITE_SUM;
           ARITH_RULE `x <= a ==> x <= a + b:num`;
           ARITH_RULE `x <= b ==> x + a <= a + b:num`]);;

let SNDCART_ADD = prove
 (`!x:real^(M,N)finite_sum y. sndcart(x + y) = sndcart(x) + sndcart(y)`,
  REWRITE_TAC[REWRITE_RULE[linear] LINEAR_SNDCART]);;

let SNDCART_CMUL = prove
 (`!x:real^(M,N)finite_sum c. sndcart(c % x) = c % sndcart(x)`,
  REWRITE_TAC[REWRITE_RULE[linear] LINEAR_SNDCART]);;

let SNDCART_NEG = prove
 (`!x:real^(M,N)finite_sum. --(sndcart x) = sndcart(--x)`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `--x = --(&1) % x`] THEN
  REWRITE_TAC[SNDCART_CMUL]);;

let SNDCART_SUB = prove
 (`!x:real^(M,N)finite_sum y. sndcart(x - y) = sndcart(x) - sndcart(y)`,
  REWRITE_TAC[VECTOR_SUB; SNDCART_NEG; SNDCART_ADD]);;

let SNDCART_VSUM = prove
 (`!k x. FINITE k ==> (sndcart(vsum k x) = vsum k (\i. sndcart(x i)))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_RULES; SNDCART_ADD; SNDCART_VEC]);;

let PASTECART_VEC = prove
 (`!n. pastecart (vec n) (vec n) = vec n`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_VEC; SNDCART_VEC;
              FSTCART_PASTECART; SNDCART_PASTECART]);;

let PASTECART_ADD = prove
 (`!x1 y1 x2:real^M y2:real^N.
     pastecart x1 y1 + pastecart x2 y2 = pastecart (x1 + x2) (y1 + y2)`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_ADD; SNDCART_ADD;
              FSTCART_PASTECART; SNDCART_PASTECART]);;

let PASTECART_CMUL = prove
 (`!x1 y1 c. pastecart (c % x1) (c % y1) = c % pastecart x1 y1`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_CMUL; SNDCART_CMUL;
              FSTCART_PASTECART; SNDCART_PASTECART]);;

let PASTECART_NEG = prove
 (`!x:real^M y:real^N. pastecart (--x) (--y) = --(pastecart x y)`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `--x = --(&1) % x`] THEN
  REWRITE_TAC[PASTECART_CMUL]);;

let PASTECART_SUB = prove
 (`!x1 y1 x2:real^M y2:real^N.
     pastecart x1 y1 - pastecart x2 y2 = pastecart (x1 - x2) (y1 - y2)`,
  REWRITE_TAC[VECTOR_SUB; GSYM PASTECART_NEG; PASTECART_ADD]);;

let PASTECART_VSUM = prove
 (`!k x y. FINITE k ==> (pastecart (vsum k x) (vsum k y) =
                         vsum k (\i. pastecart (x i) (y i)))`,
  SIMP_TAC[PASTECART_EQ; FSTCART_VSUM; SNDCART_VSUM;
           FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX]);;

let PASTECART_EQ_VEC = prove
 (`!x y n. pastecart x y = vec n <=> x = vec n /\ y = vec n`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_VEC; SNDCART_VEC;
              FSTCART_PASTECART; SNDCART_PASTECART]);;

let NORM_FSTCART = prove
 (`!x. norm(fstcart x) <= norm x`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
  SIMP_TAC[SQRT_MONO_LE_EQ; DOT_POS_LE; vector_norm] THEN
  SIMP_TAC[pastecart; dot; DIMINDEX_FINITE_SUM; LAMBDA_BETA; DIMINDEX_NONZERO;
           SUM_ADD_SPLIT; REAL_LE_ADDR; SUM_POS_LE; FINITE_NUMSEG;
           REAL_LE_SQUARE; ARITH_RULE `x <= a ==> x <= a + b:num`;
           ARITH_RULE `~(d = 0) ==> 1 <= d + 1`]);;

let DIST_FSTCART = prove
 (`!x y. dist(fstcart x,fstcart y) <= dist(x,y)`,
  REWRITE_TAC[dist; GSYM FSTCART_SUB; NORM_FSTCART]);;

let NORM_SNDCART = prove
 (`!x. norm(sndcart x) <= norm x`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
  SIMP_TAC[SQRT_MONO_LE_EQ; DOT_POS_LE; vector_norm] THEN
  SIMP_TAC[pastecart; dot; DIMINDEX_FINITE_SUM; LAMBDA_BETA; DIMINDEX_NONZERO;
           SUM_ADD_SPLIT; ARITH_RULE `x <= a ==> x <= a + b:num`;
           ARITH_RULE `~(d = 0) ==> 1 <= d + 1`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
  SIMP_TAC[SUM_IMAGE; FINITE_NUMSEG; EQ_ADD_RCANCEL; o_DEF; ADD_SUB] THEN
  SIMP_TAC[ARITH_RULE `1 <= x ==> ~(x + a <= a)`; SUM_POS_LE; FINITE_NUMSEG;
           REAL_LE_ADDL; REAL_LE_SQUARE]);;

let DIST_SNDCART = prove
 (`!x y. dist(sndcart x,sndcart y) <= dist(x,y)`,
  REWRITE_TAC[dist; GSYM SNDCART_SUB; NORM_SNDCART]);;

let DOT_PASTECART = prove
 (`!x1 x2 y1 y2. (pastecart x1 x2) dot (pastecart y1 y2) =
                x1 dot y1 + x2 dot y2`,
  SIMP_TAC[pastecart; dot; LAMBDA_BETA; DIMINDEX_FINITE_SUM] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `~(d = 0) ==> 1 <= d + 1`;
           DIMINDEX_NONZERO; REAL_LE_LADD] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
  SIMP_TAC[SUM_IMAGE; FINITE_NUMSEG; EQ_ADD_RCANCEL; o_DEF; ADD_SUB] THEN
  SIMP_TAC[ARITH_RULE `1 <= x ==> ~(x + a <= a)`; REAL_LE_REFL]);;

let SQNORM_PASTECART = prove
 (`!x y. norm(pastecart x y) pow 2 = norm(x) pow 2 + norm(y) pow 2`,
  REWRITE_TAC[NORM_POW_2; DOT_PASTECART]);;

let NORM_PASTECART = prove
 (`!x y. norm(pastecart x y) = sqrt(norm(x) pow 2 + norm(y) pow 2)`,
  REWRITE_TAC[NORM_EQ_SQUARE] THEN
  SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LE_ADD; REAL_LE_POW_2] THEN
  REWRITE_TAC[DOT_PASTECART; NORM_POW_2]);;

let NORM_PASTECART_LE = prove
 (`!x y. norm(pastecart x y) <= norm(x) + norm(y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC TRIANGLE_LEMMA THEN
  REWRITE_TAC[NORM_POS_LE; NORM_POW_2; DOT_PASTECART; REAL_LE_REFL]);;

let DIST_PASTECART_LE = prove
 (`!x1 y1 x2 y2.
        dist(pastecart x1 y1,pastecart x2 y2)
        <= dist(x1,x2) + dist(y1,y2)`,
  REWRITE_TAC[dist; PASTECART_SUB; NORM_PASTECART_LE]);;

let NORM_LE_PASTECART = prove
 (`!x:real^M y:real^N.
    norm(x) <= norm(pastecart x y) /\
    norm(y) <= norm(pastecart x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_PASTECART] THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  REWRITE_TAC[REAL_LE_ADDL; REAL_LE_ADDR; REAL_LE_POW_2]);;

let DIST_LE_PASTECART = prove
 (`!x1 y1 x2 y2.
        dist(x1,x2) <= dist(pastecart x1 y1,pastecart x2 y2) /\
        dist(y1,y2) <= dist(pastecart x1 y1,pastecart x2 y2)`,
  REWRITE_TAC[dist; PASTECART_SUB; NORM_LE_PASTECART]);;

let NORM_PASTECART_0 = prove
 (`(!x. norm(pastecart x (vec 0)) = norm x) /\
   (!y. norm(pastecart (vec 0) y) = norm y)`,
  REWRITE_TAC[NORM_EQ_SQUARE; NORM_POW_2; NORM_POS_LE] THEN
  REWRITE_TAC[DOT_PASTECART; DOT_LZERO; REAL_ADD_LID; REAL_ADD_RID]);;

let DIST_PASTECART_CANCEL = prove
 (`(!x x' y. dist(pastecart x y,pastecart x' y) = dist(x,x')) /\
   (!x y y'. dist(pastecart x y,pastecart x y') = dist(y,y'))`,
  REWRITE_TAC[dist; PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0]);;

let LINEAR_PASTECART = prove
 (`!f:real^M->real^N g:real^M->real^P.
        linear f /\ linear g ==> linear (\x. pastecart (f x) (g x))`,
  SIMP_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* A bit of linear algebra.                                                  *)
(* ------------------------------------------------------------------------- *)

let subspace = new_definition
 `subspace s <=>
        vec(0) IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!c x. x IN s ==> (c % x) IN s)`;;

let span = new_definition
  `span s = subspace hull s`;;

let dependent = new_definition
 `dependent s <=> ?a. a IN s /\ a IN span(s DELETE a)`;;

let independent = new_definition
 `independent s <=> ~(dependent s)`;;

(* ------------------------------------------------------------------------- *)
(* Closure properties of subspaces.                                          *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_UNIV = prove
 (`subspace(UNIV:real^N->bool)`,
  REWRITE_TAC[subspace; IN_UNIV]);;

let SUBSPACE_IMP_NONEMPTY = prove
 (`!s. subspace s ==> ~(s = {})`,
  REWRITE_TAC[subspace] THEN SET_TAC[]);;

let SUBSPACE_0 = prove
 (`subspace s ==> vec(0) IN s`,
  SIMP_TAC[subspace]);;

let SUBSPACE_ADD = prove
 (`!x y s. subspace s /\ x IN s /\ y IN s ==> (x + y) IN s`,
  SIMP_TAC[subspace]);;

let SUBSPACE_MUL = prove
 (`!x c s. subspace s /\ x IN s ==> (c % x) IN s`,
  SIMP_TAC[subspace]);;

let SUBSPACE_NEG = prove
 (`!x s. subspace s /\ x IN s ==> (--x) IN s`,
  SIMP_TAC[VECTOR_ARITH `--x = --(&1) % x`; SUBSPACE_MUL]);;

let SUBSPACE_SUB = prove
 (`!x y s. subspace s /\ x IN s /\ y IN s ==> (x - y) IN s`,
  SIMP_TAC[VECTOR_SUB; SUBSPACE_ADD; SUBSPACE_NEG]);;

let SUBSPACE_VSUM = prove
 (`!s f t. subspace s /\ FINITE t /\ (!x. x IN t ==> f(x) IN s)
           ==> (vsum t f) IN s`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; SUBSPACE_0; IN_INSERT; SUBSPACE_ADD]);;

let SUBSPACE_LINEAR_IMAGE = prove
 (`!f s. linear f /\ subspace s ==> subspace(IMAGE f s)`,
  REWRITE_TAC[subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
  MESON_TAC[linear; LINEAR_0]);;

let SUBSPACE_LINEAR_PREIMAGE = prove
 (`!f s. linear f /\ subspace s ==> subspace {x | f(x) IN s}`,
  REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  MESON_TAC[linear; LINEAR_0]);;

let SUBSPACE_TRIVIAL = prove
 (`subspace {vec 0}`,
  SIMP_TAC[subspace; IN_SING] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let SUBSPACE_INTER = prove
 (`!s t. subspace s /\ subspace t ==> subspace (s INTER t)`,
  REWRITE_TAC[subspace; IN_INTER] THEN MESON_TAC[]);;

let SUBSPACE_INTERS = prove
 (`!f. (!s. s IN f ==> subspace s) ==> subspace(INTERS f)`,
  SIMP_TAC[subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_INTERS]);;

let LINEAR_INJECTIVE_0_SUBSPACE = prove
 (`!f:real^M->real^N s.
        linear f /\ subspace s
         ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              (!x. x IN s /\ f x = vec 0 ==> x = vec 0))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN
  ASM_MESON_TAC[VECTOR_SUB_RZERO; SUBSPACE_SUB; SUBSPACE_0]);;

let SUBSPACE_UNION_CHAIN = prove
 (`!s t:real^N->bool.
        subspace s /\ subspace t /\ subspace(s UNION t)
         ==> s SUBSET t \/ t SUBSET s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE
   `s SUBSET t \/ t SUBSET s <=>
    ~(?x y. x IN s /\ ~(x IN t) /\ y IN t /\ ~(y IN s))`] THEN
  STRIP_TAC THEN SUBGOAL_THEN `(x + y:real^N) IN s UNION t` MP_TAC THENL
   [MATCH_MP_TAC SUBSPACE_ADD THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN
    ASM_MESON_TAC[SUBSPACE_SUB; VECTOR_ARITH
     `(x + y) - x:real^N = y /\ (x + y) - y = x`]]);;

let SUBSPACE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> subspace(s PCROSS t)`,
  REWRITE_TAC[subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  REWRITE_TAC[GSYM PASTECART_VEC; PASTECART_IN_PCROSS] THEN SIMP_TAC[]);;

let SUBSPACE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace(s PCROSS t) <=> subspace s /\ subspace t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_MESON_TAC[PCROSS_EMPTY; SUBSPACE_IMP_NONEMPTY]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_MESON_TAC[PCROSS_EMPTY; SUBSPACE_IMP_NONEMPTY]; ALL_TAC] THEN
  EQ_TAC THEN REWRITE_TAC[SUBSPACE_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] SUBSPACE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] SUBSPACE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SPAN_SPAN = prove
 (`!s. span(span s) = span s`,
  REWRITE_TAC[span; HULL_HULL]);;

let SPAN_MONO = prove
 (`!s t. s SUBSET t ==> span s SUBSET span t`,
  REWRITE_TAC[span; HULL_MONO]);;

let SUBSPACE_SPAN = prove
 (`!s. subspace(span s)`,
  GEN_TAC THEN REWRITE_TAC[span] THEN MATCH_MP_TAC P_HULL THEN
  SIMP_TAC[subspace; IN_INTERS]);;

let SPAN_CLAUSES = prove
 (`(!a s. a IN s ==> a IN span s) /\
   (vec(0) IN span s) /\
   (!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s) /\
   (!x c s. x IN span s ==> (c % x) IN span s)`,
  MESON_TAC[span; HULL_SUBSET; SUBSET; SUBSPACE_SPAN; subspace]);;

let SPAN_INDUCT = prove
 (`!s h. (!x. x IN s ==> x IN h) /\ subspace h ==> !x. x IN span(s) ==> h(x)`,
  REWRITE_TAC[span] THEN MESON_TAC[SUBSET; HULL_MINIMAL; IN]);;

let SPAN_EMPTY = prove
 (`span {} = {vec 0}`,
  REWRITE_TAC[span] THEN MATCH_MP_TAC HULL_UNIQUE THEN
  SIMP_TAC[subspace; SUBSET; IN_SING; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let INDEPENDENT_EMPTY = prove
 (`independent {}`,
  REWRITE_TAC[independent; dependent; NOT_IN_EMPTY]);;

let INDEPENDENT_NONZERO = prove
 (`!s. independent s ==> ~(vec 0 IN s)`,
  REWRITE_TAC[independent; dependent] THEN MESON_TAC[SPAN_CLAUSES]);;

let INDEPENDENT_MONO = prove
 (`!s t. independent t /\ s SUBSET t ==> independent s`,
  REWRITE_TAC[independent; dependent] THEN
  ASM_MESON_TAC[SPAN_MONO; SUBSET; IN_DELETE]);;

let DEPENDENT_MONO = prove
 (`!s t:real^N->bool. dependent s /\ s SUBSET t ==> dependent t`,
  ONCE_REWRITE_TAC[TAUT `p /\ q ==> r <=> ~r /\ q ==> ~p`] THEN
  REWRITE_TAC[GSYM independent; INDEPENDENT_MONO]);;

let SPAN_SUBSPACE = prove
 (`!b s. b SUBSET s /\ s SUBSET (span b) /\ subspace s ==> (span b = s)`,
  MESON_TAC[SUBSET_ANTISYM; span; HULL_MINIMAL]);;

let SPAN_INDUCT_ALT = prove
 (`!s h. h(vec 0) /\
         (!c x y. x IN s /\ h(y) ==> h(c % x + y))
          ==> !x:real^N. x IN span(s) ==> h(x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o prove_inductive_relations_exist o concl) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^N. x IN span(s) ==> g(x)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  REWRITE_TAC[IN; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_MESON_TAC[IN; VECTOR_ADD_LID; VECTOR_ADD_ASSOC; VECTOR_ADD_SYM;
                VECTOR_MUL_LID; VECTOR_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Individual closure properties.                                            *)
(* ------------------------------------------------------------------------- *)

let SPAN_SUPERSET = prove
 (`!x. x IN s ==> x IN span s`,
  MESON_TAC[SPAN_CLAUSES]);;

let SPAN_INC = prove
 (`!s. s SUBSET span s`,
  REWRITE_TAC[SUBSET; SPAN_SUPERSET]);;

let SPAN_UNION_SUBSET = prove
 (`!s t. span s UNION span t SUBSET span(s UNION t)`,
  REWRITE_TAC[span; HULL_UNION_SUBSET]);;

let SPAN_UNIV = prove
 (`span(:real^N) = (:real^N)`,
  SIMP_TAC[SPAN_INC; SET_RULE `UNIV SUBSET s ==> s = UNIV`]);;

let SPAN_0 = prove
 (`vec(0) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_0]);;

let SPAN_ADD = prove
 (`!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_ADD]);;

let SPAN_MUL = prove
 (`!x c s. x IN span s ==> (c % x) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_MUL]);;

let SPAN_MUL_EQ = prove
 (`!x:real^N c s. ~(c = &0) ==> ((c % x) IN span s <=> x IN span s)`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_SIMP_TAC[SPAN_MUL] THEN
  SUBGOAL_THEN `(inv(c) % c % x:real^N) IN span s` MP_TAC THENL
   [ASM_SIMP_TAC[SPAN_MUL];
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID]]);;

let SPAN_NEG = prove
 (`!x s. x IN span s ==> (--x) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_NEG]);;

let SPAN_NEG_EQ = prove
 (`!x s. --x IN span s <=> x IN span s`,
  MESON_TAC[SPAN_NEG; VECTOR_NEG_NEG]);;

let SPAN_SUB = prove
 (`!x y s. x IN span s /\ y IN span s ==> (x - y) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_SUB]);;

let SPAN_VSUM = prove
 (`!s f t. FINITE t /\ (!x. x IN t ==> f(x) IN span(s))
           ==> (vsum t f) IN span(s)`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_VSUM]);;

let SPAN_ADD_EQ = prove
 (`!s x y. x IN span s ==> ((x + y) IN span s <=> y IN span s)`,
  MESON_TAC[SPAN_ADD; SPAN_SUB; VECTOR_ARITH `(x + y) - x:real^N = y`]);;

let SPAN_EQ_SELF = prove
 (`!s. span s = s <=> subspace s`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[SUBSPACE_SPAN]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SPAN_SUBSPACE THEN
  ASM_REWRITE_TAC[SUBSET_REFL; SPAN_INC]);;

let SPAN_OF_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> span s = s`,
  REWRITE_TAC[SPAN_EQ_SELF]);;

let SPAN_SUBSET_SUBSPACE = prove
 (`!s t:real^N->bool. s SUBSET t /\ subspace t ==> span s SUBSET t`,
  MESON_TAC[SPAN_MONO; SPAN_EQ_SELF]);;

let SUBSPACE_TRANSLATION_SELF = prove
 (`!s a. subspace s /\ a IN s ==> IMAGE (\x. a + x) s = s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o GEN_REWRITE_RULE I [GSYM SPAN_EQ_SELF]) THEN
  ASM_SIMP_TAC[SPAN_ADD_EQ; SPAN_CLAUSES] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = y <=> x = y - a`; EXISTS_REFL]);;

let SUBSPACE_TRANSLATION_SELF_EQ = prove
 (`!s a:real^N. subspace s ==> (IMAGE (\x. a + x) s = s <=> a IN s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[SUBSPACE_TRANSLATION_SELF] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s. (a:real^N) IN s`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^N` THEN
  ASM_MESON_TAC[subspace; VECTOR_ADD_RID]);;

let SUBSPACE_SUMS = prove
 (`!s t. subspace s /\ subspace t
         ==> subspace {x + y | x IN s /\ y IN t}`,
  REWRITE_TAC[subspace; FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[VECTOR_ADD_LID];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `(x + y) + (x' + y'):real^N = (x + x') + (y + y')`] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN ASM_MESON_TAC[]]);;

let SPAN_UNION = prove
 (`!s t. span(s UNION t) = {x + y:real^N | x IN span s /\ y IN span t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    SIMP_TAC[SUBSPACE_SUMS; SUBSPACE_SPAN] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; SPAN_0; VECTOR_ADD_RID];
      MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `x:real^N`] THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; SPAN_0; VECTOR_ADD_LID]];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_ADD THEN
    ASM_MESON_TAC[SPAN_MONO; SUBSET_UNION; SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Mapping under linear image.                                               *)
(* ------------------------------------------------------------------------- *)

let SPAN_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. linear f ==> (span(IMAGE f s) = IMAGE f (span s))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [SPEC_TAC(`x:real^N`,`x:real^N`) THEN MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC[SET_RULE `(\x. x IN s) = s`] THEN
    ASM_SIMP_TAC[SUBSPACE_SPAN; SUBSPACE_LINEAR_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[SPAN_SUPERSET; SUBSET];
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC[SET_RULE `(\x. f x IN span(s)) = {x | f(x) IN span s}`] THEN
    ASM_SIMP_TAC[SUBSPACE_LINEAR_PREIMAGE; SUBSPACE_SPAN] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[SPAN_SUPERSET; SUBSET; IN_IMAGE]]);;

let DEPENDENT_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (dependent(IMAGE f s) <=> dependent s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dependent; EXISTS_IN_IMAGE] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:real^M` THEN
  ASM_CASES_TAC `(a:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(f:real^M->real^N) a IN span(IMAGE f (s DELETE a))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE] THEN ASM SET_TAC[]]);;

let DEPENDENT_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        dependent(s)
        ==> dependent(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dependent; EXISTS_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^M` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s DELETE f a = IMAGE f (s DELETE a)`
   (fun th -> ASM_SIMP_TAC[FUN_IN_IMAGE; SPAN_LINEAR_IMAGE; th]) THEN
  ASM SET_TAC[]);;

let INDEPENDENT_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (independent(IMAGE f s) <=> independent s)`,
  REWRITE_TAC[independent; TAUT `(~p <=> ~q) <=> (p <=> q)`] THEN
  REWRITE_TAC[DEPENDENT_LINEAR_IMAGE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The key breakdown property.                                               *)
(* ------------------------------------------------------------------------- *)

let SPAN_BREAKDOWN = prove
 (`!b s a:real^N.
      b IN s /\ a IN span s ==> ?k. (a - k % b) IN span(s DELETE b)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
  REWRITE_TAC[subspace; IN_ELIM_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `a:real^N = b`; ALL_TAC] THEN
  ASM_MESON_TAC[SPAN_CLAUSES; IN_DELETE; VECTOR_ARITH
   `(a - &1 % a = vec 0) /\ (a - &0 % b = a) /\
    ((x + y) - (k1 + k2) % b = (x - k1 % b) + (y - k2 % b)) /\
    (c % x - (c * k) % y = c % (x - k % y))`]);;

let SPAN_BREAKDOWN_EQ = prove
 (`!a:real^N s. (x IN span(a INSERT s) <=> (?k. (x - k % a) IN span s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o CONJ(SET_RULE `(a:real^N) IN (a INSERT s)`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SPAN_BREAKDOWN) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
    SPEC_TAC(`x - k % a:real^N`,`y:real^N`) THEN
    REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
    SUBST1_TAC(VECTOR_ARITH `x = (x - k % a) + k % a:real^N`) THEN
    MATCH_MP_TAC SPAN_ADD THEN
    ASM_MESON_TAC[SPAN_MONO; SUBSET; IN_INSERT; SPAN_CLAUSES]]);;

let SPAN_INSERT_0 = prove
 (`!s. span(vec 0 INSERT s) = span s`,
  SIMP_TAC[EXTENSION; SPAN_BREAKDOWN_EQ; VECTOR_MUL_RZERO; VECTOR_SUB_RZERO]);;

let SPAN_SING = prove
 (`!a. span {a} = {u % a | u IN (:real)}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; SPAN_BREAKDOWN_EQ; SPAN_EMPTY] THEN
  REWRITE_TAC[IN_UNIV; IN_SING; VECTOR_SUB_EQ]);;

let SPAN_2 = prove
 (`!a b. span {a,b} = {u % a + v % b | u IN (:real) /\ v IN (:real)}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; SPAN_BREAKDOWN_EQ; SPAN_EMPTY] THEN
  REWRITE_TAC[IN_UNIV; IN_SING; VECTOR_SUB_EQ] THEN
  REWRITE_TAC[VECTOR_ARITH `x - y:real^N = z <=> x = y + z`]);;

let SPAN_3 = prove
 (`!a b c. span {a,b,c} =
      {u % a + v % b + w % c | u IN (:real) /\ v IN (:real) /\ w IN (:real)}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; SPAN_BREAKDOWN_EQ; SPAN_EMPTY] THEN
  REWRITE_TAC[IN_UNIV; IN_SING; VECTOR_SUB_EQ] THEN
  REWRITE_TAC[VECTOR_ARITH `x - y:real^N = z <=> x = y + z`]);;

(* ------------------------------------------------------------------------- *)
(* Hence some "reversal" results.                                            *)
(* ------------------------------------------------------------------------- *)

let IN_SPAN_INSERT = prove
 (`!a b:real^N s.
        a IN span(b INSERT s) /\ ~(a IN span s) ==> b IN span(a INSERT s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^N`; `(b:real^N) INSERT s`; `a:real^N`]
    SPAN_BREAKDOWN) THEN ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THEN ASM_CASES_TAC `k = &0` THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `a - &0 % b = a`; DELETE_INSERT] THENL
   [ASM_MESON_TAC[SPAN_MONO; SUBSET; DELETE_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(k)` o MATCH_MP SPAN_MUL) THEN
  ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC; REAL_MUL_LINV] THEN
  DISCH_TAC THEN SUBST1_TAC(VECTOR_ARITH
   `b:real^N = inv(k) % a - (inv(k) % a - &1 % b)`) THEN
  MATCH_MP_TAC SPAN_SUB THEN
  ASM_MESON_TAC[SPAN_CLAUSES; IN_INSERT; SUBSET; IN_DELETE; SPAN_MONO]);;

let IN_SPAN_DELETE = prove
 (`!a b s.
         a IN span s /\ ~(a IN span (s DELETE b))
         ==> b IN span (a INSERT (s DELETE b))`,
  ASM_MESON_TAC[IN_SPAN_INSERT; SPAN_MONO; SUBSET; IN_INSERT; IN_DELETE]);;

let EQ_SPAN_INSERT_EQ = prove
 (`!s x y:real^N. (x - y) IN span s ==> span(x INSERT s) = span(y INSERT s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SPAN_BREAKDOWN_EQ; EXTENSION] THEN
  ASM_MESON_TAC[SPAN_ADD; SPAN_SUB; SPAN_MUL;
                VECTOR_ARITH `(z - k % y) - k % (x - y) = z - k % x`;
                VECTOR_ARITH `(z - k % x) + k % (x - y) = z - k % y`]);;

(* ------------------------------------------------------------------------- *)
(* Transitivity property.                                                    *)
(* ------------------------------------------------------------------------- *)

let SPAN_TRANS = prove
 (`!x y:real^N s. x IN span(s) /\ y IN span(x INSERT s) ==> y IN span(s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real^N`; `(x:real^N) INSERT s`; `y:real^N`]
         SPAN_BREAKDOWN) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBST1_TAC(VECTOR_ARITH `y:real^N = (y - k % x) + k % x`) THEN
  MATCH_MP_TAC SPAN_ADD THEN ASM_SIMP_TAC[SPAN_MUL] THEN
  ASM_MESON_TAC[SPAN_MONO; SUBSET; IN_INSERT; IN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* An explicit expansion is sometimes needed.                                *)
(* ------------------------------------------------------------------------- *)

let SPAN_EXPLICIT = prove
 (`!(p:real^N -> bool).
        span p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SPAN_SUPERSET; SPAN_MUL]] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
   [EXISTS_TAC `{}:real^N->bool` THEN
    REWRITE_TAC[FINITE_RULES; VSUM_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `u:real^N->real`] THEN
  STRIP_TAC THEN EXISTS_TAC `(x:real^N) INSERT s` THEN
  EXISTS_TAC `\y. if y = x then (if x IN s then (u:real^N->real) y + c else c)
                  else u y` THEN
  ASM_SIMP_TAC[FINITE_INSERT; IN_INSERT; VSUM_CLAUSES] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
    ASM_SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_DELETE; IN_DELETE] THEN
    MATCH_MP_TAC(VECTOR_ARITH
      `y = z ==> (c + d) % x + y = d % x + c % x + z`);
    AP_TERM_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN ASM_MESON_TAC[IN_DELETE]);;

let DEPENDENT_EXPLICIT = prove
 (`!p. dependent (p:real^N -> bool) <=>
                ?s u. FINITE s /\ s SUBSET p /\
                      (?v. v IN s /\ ~(u v = &0)) /\
                      vsum s (\v. u v % v) = vec 0`,
  GEN_TAC THEN REWRITE_TAC[dependent; SPAN_EXPLICIT; IN_ELIM_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`a:real^N`; `s:real^N->bool`; `u:real^N->real`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`(a:real^N) INSERT s`;
      `\y. if y = a then -- &1 else (u:real^N->real) y`;
      `a:real^N`] THEN
    ASM_REWRITE_TAC[IN_INSERT; INSERT_SUBSET; FINITE_INSERT] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    ASM_SIMP_TAC[VSUM_CLAUSES] THEN
    COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `-- &1 % a + s = vec 0 <=> a = s`] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MATCH_MP_TAC VSUM_EQ THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `u:real^N->real`; `a:real^N`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`a:real^N`; `s DELETE (a:real^N)`;
      `\i. --((u:real^N->real) i) / (u a)`] THEN
    ASM_SIMP_TAC[VSUM_DELETE; FINITE_DELETE] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LNEG; GSYM VECTOR_MUL_ASSOC; VSUM_LMUL;
                    VSUM_NEG; VECTOR_MUL_RNEG; VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV] THEN VECTOR_ARITH_TAC]);;

let DEPENDENT_FINITE = prove
 (`!s:real^N->bool.
        FINITE s
        ==> (dependent s <=> ?u. (?v. v IN s /\ ~(u v = &0)) /\
                                 vsum s (\v. u(v) % v) = vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DEPENDENT_EXPLICIT] THEN EQ_TAC THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    EXISTS_TAC `\v:real^N. if v IN t then u(v) else &0` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`];
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let SPAN_FINITE = prove
 (`!s:real^N->bool.
        FINITE s ==> span s = {y | ?u. vsum s (\v. u v % v) = y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SPAN_EXPLICIT; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `\x:real^N. if x IN t then u(x) else &0` THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC[GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`];
    X_GEN_TAC `u:real^N->real` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Standard bases are a spanning set, and obviously finite.                  *)
(* ------------------------------------------------------------------------- *)

let SPAN_STDBASIS = prove
 (`span {basis i :real^N | 1 <= i /\ i <= dimindex(:N)} = UNIV`,
  REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `x:real^N` THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
  MATCH_MP_TAC SPAN_VSUM THEN SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let HAS_SIZE_STDBASIS = prove
 (`{basis i :real^N | 1 <= i /\ i <= dimindex(:N)} HAS_SIZE
        dimindex(:N)`,
  ONCE_REWRITE_TAC[SET_RULE `{f x | P x} = IMAGE f {x | P x}`] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  REWRITE_TAC[GSYM numseg; HAS_SIZE_NUMSEG_1; IN_NUMSEG] THEN
  MESON_TAC[BASIS_INJ]);;

let FINITE_STDBASIS = prove
 (`FINITE {basis i :real^N | 1 <= i /\ i <= dimindex(:N)}`,
  MESON_TAC[HAS_SIZE_STDBASIS; HAS_SIZE]);;

let CARD_STDBASIS = prove
 (`CARD {basis i :real^N | 1 <= i /\ i <= dimindex(:N)} =
        dimindex(:N)`,
   MESON_TAC[HAS_SIZE_STDBASIS; HAS_SIZE]);;

let IN_SPAN_IMAGE_BASIS = prove
 (`!x:real^N s.
        x IN span(IMAGE basis s) <=>
          !i. 1 <= i /\ i <= dimindex(:N) /\ ~(i IN s) ==> x$i = &0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`x:real^N`,`x:real^N`) THEN MATCH_MP_TAC SPAN_INDUCT THEN
    SIMP_TAC[subspace; IN_ELIM_THM; VEC_COMPONENT; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    SIMP_TAC[FORALL_IN_IMAGE; BASIS_COMPONENT] THEN MESON_TAC[];
    DISCH_TAC THEN REWRITE_TAC[SPAN_EXPLICIT; IN_ELIM_THM] THEN
    EXISTS_TAC `(IMAGE basis ((1..dimindex(:N)) INTER s)):real^N->bool` THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\v:real^N. x dot v` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG] THEN
      REWRITE_TAC[IN_INTER; IN_NUMSEG] THEN MESON_TAC[BASIS_INJ];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]] THEN
    REWRITE_TAC[o_DEF] THEN
    SIMP_TAC[CART_EQ; VSUM_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(if x = y then p else q) = (if y = x then p else q)`] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_RZERO; IN_INTER; IN_NUMSEG; DOT_BASIS] THEN
    ASM_MESON_TAC[REAL_MUL_RID]]);;

let INDEPENDENT_STDBASIS = prove
 (`independent {basis i :real^N | 1 <= i /\ i <= dimindex(:N)}`,
  REWRITE_TAC[independent; dependent] THEN
  ONCE_REWRITE_TAC[SET_RULE `{f x | P x} = IMAGE f {x | P x}`] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `IMAGE basis {i | 1 <= i /\ i <= dimindex(:N)} DELETE
           (basis k:real^N) =
    IMAGE basis ({i | 1 <= i /\ i <= dimindex(:N)} DELETE k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_ELIM_THM] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[BASIS_INJ];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SPAN_IMAGE_BASIS] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  ASM_SIMP_TAC[IN_DELETE; BASIS_COMPONENT; REAL_OF_NUM_EQ; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* This is useful for building a basis step-by-step.                         *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_INSERT = prove
 (`!a:real^N s. independent(a INSERT s) <=>
                  if a IN s then independent s
                  else independent s /\ ~(a IN span s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THEN
  ASM_SIMP_TAC[SET_RULE `x IN s ==> (x INSERT s = s)`] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INDEPENDENT_MONO; SUBSET; IN_INSERT];
      POP_ASSUM MP_TAC THEN REWRITE_TAC[independent; dependent] THEN
      ASM_MESON_TAC[IN_INSERT; SET_RULE
        `~(a IN s) ==> ((a INSERT s) DELETE a = s)`]];
    ALL_TAC] THEN
  REWRITE_TAC[independent; dependent; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN X_GEN_TAC `b:real^N` THEN
  REWRITE_TAC[IN_INSERT] THEN ASM_CASES_TAC `b:real^N = a` THEN
  ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> ((a INSERT s) DELETE a = s)`] THEN
  ASM_SIMP_TAC[SET_RULE
    `~(a IN s) /\ ~(b = a)
     ==> ((a INSERT s) DELETE b = a INSERT (s DELETE b))`] THEN
  ASM_MESON_TAC[IN_SPAN_INSERT; SET_RULE
    `b IN s ==> (b INSERT (s DELETE b) = s)`]);;

(* ------------------------------------------------------------------------- *)
(* The degenerate case of the Exchange Lemma.                                *)
(* ------------------------------------------------------------------------- *)

let SPANNING_SUBSET_INDEPENDENT = prove
 (`!s t:real^N->bool.
        t SUBSET s /\ independent s /\ s SUBSET span(t) ==> (s = t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [independent]) THEN
  REWRITE_TAC[dependent; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SPAN_MONO; SUBSET; IN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* The general case of the Exchange Lemma, the key to what follows.          *)
(* ------------------------------------------------------------------------- *)

let EXCHANGE_LEMMA = prove
 (`!s t:real^N->bool.
        FINITE t /\ independent s /\ s SUBSET span t
        ==> ?t'. t' HAS_SIZE (CARD t) /\
                 s SUBSET t' /\ t' SUBSET (s UNION t) /\ s SUBSET (span t')`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `CARD(t DIFF s :real^N->bool)` THEN
  ASM_CASES_TAC `(s:real^N->bool) SUBSET t` THENL
   [ASM_MESON_TAC[HAS_SIZE; SUBSET_UNION]; ALL_TAC] THEN
  ASM_CASES_TAC `t SUBSET (s:real^N->bool)` THENL
   [ASM_MESON_TAC[SPANNING_SUBSET_INDEPENDENT; HAS_SIZE]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBSET] o check(is_neg o concl)) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `s SUBSET span(t DELETE (b:real^N))` THENL
   [FIRST_X_ASSUM(MP_TAC o
     SPECL [`t DELETE (b:real^N)`; `s:real^N->bool`]) THEN
    ASM_REWRITE_TAC[SET_RULE `s DELETE a DIFF t = (s DIFF t) DELETE a`] THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DIFF; IN_DIFF; FINITE_DELETE;
                 CARD_EQ_0; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~((s:real^N->bool) SUBSET t)` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(b:real^N) INSERT u` THEN
    ASM_SIMP_TAC[SUBSET_INSERT; INSERT_SUBSET; IN_UNION] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(u:real^N->bool) HAS_SIZE CARD(t:real^N->bool) - 1` THEN
      SIMP_TAC[HAS_SIZE; FINITE_RULES; CARD_CLAUSES] THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_UNION; IN_DELETE]; ALL_TAC] THEN
      ASM_MESON_TAC[ARITH_RULE `~(n = 0) ==> (SUC(n - 1) = n)`;
                    CARD_EQ_0; MEMBER_NOT_EMPTY];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `u SUBSET s UNION t DELETE (b:real^N)` THEN SET_TAC[];
      ASM_MESON_TAC[SUBSET; SPAN_MONO; IN_INSERT]];
    ALL_TAC] THEN
  UNDISCH_TAC `~(s SUBSET span (t DELETE (b:real^N)))` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SUBSET] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^N) IN t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_DELETE; SPAN_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(a:real^N) INSERT (t DELETE b)`; `s:real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SET_RULE
     `a IN s ==> ((a INSERT (t DELETE b) DIFF s) = (t DIFF s) DELETE b)`] THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DELETE; FINITE_DIFF; IN_DIFF] THEN
    ASM_SIMP_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`; CARD_EQ_0;
                 FINITE_DIFF] THEN
    UNDISCH_TAC `~((s:real^N->bool) SUBSET t)` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RULES; FINITE_DELETE] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN MATCH_MP_TAC SPAN_TRANS THEN EXISTS_TAC `b:real^N` THEN
    ASM_MESON_TAC[IN_SPAN_DELETE; SUBSET; SPAN_MONO;
                  SET_RULE `t SUBSET (b INSERT (a INSERT (t DELETE b)))`];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  ASM_SIMP_TAC[HAS_SIZE; CARD_CLAUSES; CARD_DELETE; FINITE_DELETE; IN_DELETE;
               ARITH_RULE `(SUC(n - 1) = n) <=> ~(n = 0)`;
               CARD_EQ_0] THEN
  UNDISCH_TAC `(b:real^N) IN t` THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* This implies corresponding size bounds.                                   *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_SPAN_BOUND = prove
 (`!s t. FINITE t /\ independent s /\ s SUBSET span(t)
         ==> FINITE s /\ CARD(s) <= CARD(t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EXCHANGE_LEMMA) THEN
  ASM_MESON_TAC[HAS_SIZE; CARD_SUBSET; FINITE_SUBSET]);;

let INDEPENDENT_BOUND = prove
 (`!s:real^N->bool.
        independent s ==> FINITE s /\ CARD(s) <= dimindex(:N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM CARD_STDBASIS] THEN
  MATCH_MP_TAC INDEPENDENT_SPAN_BOUND THEN
  ASM_REWRITE_TAC[FINITE_STDBASIS; SPAN_STDBASIS; SUBSET_UNIV]);;

let DEPENDENT_BIGGERSET = prove
 (`!s:real^N->bool. (FINITE s ==> CARD(s) > dimindex(:N)) ==> dependent s`,
  MP_TAC INDEPENDENT_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[GT; GSYM NOT_LE; independent] THEN MESON_TAC[]);;

let INDEPENDENT_IMP_FINITE = prove
 (`!s:real^N->bool. independent s ==> FINITE s`,
  SIMP_TAC[INDEPENDENT_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Explicit formulation of independence.                                     *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_EXPLICIT = prove
 (`!b:real^N->bool.
        independent b <=>
            FINITE b /\
            !c. vsum b (\v. c(v) % v) = vec 0 ==> !v. v IN b ==> c(v) = &0`,
  GEN_TAC THEN
  ASM_CASES_TAC `FINITE(b:real^N->bool)` THENL
   [ALL_TAC; ASM_MESON_TAC[INDEPENDENT_BOUND]] THEN
  ASM_SIMP_TAC[independent; DEPENDENT_FINITE] THEN MESON_TAC[]);;

let INDEPENDENT_SING = prove
 (`!x. independent {x} <=> ~(x = vec 0)`,
  REWRITE_TAC[INDEPENDENT_INSERT; NOT_IN_EMPTY; SPAN_EMPTY] THEN
  REWRITE_TAC[INDEPENDENT_EMPTY] THEN SET_TAC[]);;

let DEPENDENT_SING = prove
 (`!x. dependent {x} <=> x = vec 0`,
  MESON_TAC[independent; INDEPENDENT_SING]);;

let DEPENDENT_2 = prove
 (`!a b:real^N.
        dependent {a,b} <=>
                if a = b then a = vec 0
                else ?x y. x % a + y % b = vec 0 /\ ~(x = &0 /\ y = &0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[DEPENDENT_SING; SET_RULE `{x,x} = {x}`] THEN
  SIMP_TAC[DEPENDENT_FINITE; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; VECTOR_ADD_RID; EXISTS_IN_INSERT] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(u:real^N->real) a`; `(u:real^N->real) b`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN DISCH_TAC THEN EXISTS_TAC
     `\v:real^N. if v = a then x else if v = b then y else z:real` THEN
    ASM_MESON_TAC[]]);;

let DEPENDENT_3 = prove
 (`!a b c:real^N.
        ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> (dependent {a,b,c} <=>
             ?x y z. x % a + y % b + z % c = vec 0 /\
                     ~(x = &0 /\ y = &0 /\ z = &0))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[DEPENDENT_FINITE; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; VECTOR_ADD_RID; IN_INSERT] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`(u:real^N->real) a`; `(u:real^N->real) b`; `(u:real^N->real) c`];
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `z:real`] THEN DISCH_TAC THEN
    EXISTS_TAC
     `\v:real^N. if v = a then x else if v = b then y else z:real`] THEN
  ASM_MESON_TAC[]);;

let INDEPENDENT_2 = prove
 (`!a b:real^N x y.
        independent{a,b} /\ ~(a = b)
        ==> (x % a + y % b = vec 0 <=> x = &0 /\ y = &0)`,
  SIMP_TAC[IMP_CONJ_ALT; independent; DEPENDENT_2] THEN
  MESON_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID]);;

let INDEPENDENT_3 = prove
 (`!a b c:real^N x y z.
        independent{a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> (x % a + y % b + z % c = vec 0 <=> x = &0 /\ y = &0 /\ z = &0)`,
  SIMP_TAC[IMP_CONJ_ALT; independent; DEPENDENT_3] THEN
  MESON_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* Hence we can create a maximal independent subset.                         *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_INDEPENDENT_SUBSET_EXTEND = prove
 (`!s v:real^N->bool.
        s SUBSET v /\ independent s
        ==> ?b. s SUBSET b /\ b SUBSET v /\ independent b /\
                v SUBSET (span b)`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `dimindex(:N) - CARD(s:real^N->bool)` THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `v SUBSET (span(s:real^N->bool))` THENL
   [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SUBSET]) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N) INSERT s`) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [ALL_TAC; MESON_TAC[INSERT_SUBSET]] THEN
  SUBGOAL_THEN `independent ((a:real^N) INSERT s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INDEPENDENT_INSERT; COND_ID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET] THEN
  MATCH_MP_TAC(ARITH_RULE `(b = a + 1) /\ b <= n ==> n - b < n - a`) THEN
  ASM_SIMP_TAC[CARD_CLAUSES; INDEPENDENT_BOUND] THEN
  ASM_MESON_TAC[SPAN_SUPERSET; ADD1]);;

let MAXIMAL_INDEPENDENT_SUBSET = prove
 (`!v:real^N->bool. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b)`,
  MP_TAC(SPEC `EMPTY:real^N->bool` MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  REWRITE_TAC[EMPTY_SUBSET; INDEPENDENT_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* A kind of closed graph property for linearity.                            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_SUBSPACE_GRAPH = prove
 (`!f:real^M->real^N.
        linear f <=> subspace {pastecart x (f x) | x IN (:real^M)}`,
  REWRITE_TAC[linear; subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; GSYM(SPEC `0` PASTECART_VEC); IN_UNIV] THEN
  REWRITE_TAC[IN_ELIM_THM; PASTECART_INJ; UNWIND_THM1; PASTECART_ADD;
              GSYM PASTECART_CMUL] THEN
  MESON_TAC[VECTOR_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Notion of dimension.                                                      *)
(* ------------------------------------------------------------------------- *)

let dim = new_definition
  `dim v = @n. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
                   b HAS_SIZE n`;;

let BASIS_EXISTS = prove
 (`!v. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
           b HAS_SIZE (dim v)`,
  GEN_TAC THEN REWRITE_TAC[dim] THEN CONV_TAC SELECT_CONV THEN
  MESON_TAC[MAXIMAL_INDEPENDENT_SUBSET; HAS_SIZE; INDEPENDENT_BOUND]);;

let BASIS_EXISTS_FINITE = prove
 (`!v. ?b. FINITE b /\
           b SUBSET v /\
           independent b /\
           v SUBSET (span b) /\
           b HAS_SIZE (dim v)`,
  MESON_TAC[BASIS_EXISTS; INDEPENDENT_IMP_FINITE]);;

let BASIS_SUBSPACE_EXISTS = prove
 (`!s:real^N->bool.
        subspace s
        ==> ?b. FINITE b /\
                b SUBSET s /\
                independent b /\
                span b = s /\
                b HAS_SIZE dim s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  ASM_MESON_TAC[SPAN_EQ_SELF; SPAN_MONO; INDEPENDENT_IMP_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* Consequences of independence or spanning for cardinality.                 *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_CARD_LE_DIM = prove
 (`!v b:real^N->bool.
        b SUBSET v /\ independent b ==> FINITE b /\ CARD(b) <= dim v`,
  MESON_TAC[BASIS_EXISTS; INDEPENDENT_SPAN_BOUND; HAS_SIZE;SUBSET_TRANS]);;

let SPAN_CARD_GE_DIM = prove
 (`!v b:real^N->bool.
        v SUBSET (span b) /\ FINITE b ==> dim(v) <= CARD(b)`,
  MESON_TAC[BASIS_EXISTS; INDEPENDENT_SPAN_BOUND; HAS_SIZE;SUBSET_TRANS]);;

let BASIS_CARD_EQ_DIM = prove
 (`!v b. b SUBSET v /\ v SUBSET (span b) /\ independent b
         ==> FINITE b /\ (CARD b = dim v)`,
  MESON_TAC[LE_ANTISYM; INDEPENDENT_CARD_LE_DIM; SPAN_CARD_GE_DIM]);;

let BASIS_HAS_SIZE_DIM = prove
 (`!v b. independent b /\ span b = v ==> b HAS_SIZE (dim v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC BASIS_CARD_EQ_DIM THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SPAN_INC]);;

let DIM_UNIQUE = prove
 (`!v b. b SUBSET v /\ v SUBSET (span b) /\ independent b /\ b HAS_SIZE n
         ==> (dim v = n)`,
  MESON_TAC[BASIS_CARD_EQ_DIM; HAS_SIZE]);;

let DIM_LE_CARD = prove
 (`!s. FINITE s ==> dim s <= CARD s`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
  ASM_REWRITE_TAC[SPAN_INC; SUBSET_REFL]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas about dimension.                                              *)
(* ------------------------------------------------------------------------- *)

let DIM_UNIV = prove
 (`dim(:real^N) = dimindex(:N)`,
  MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}` THEN
  REWRITE_TAC[SUBSET_UNIV; SPAN_STDBASIS; HAS_SIZE_STDBASIS;
              INDEPENDENT_STDBASIS]);;

let DIM_SUBSET = prove
 (`!s t:real^N->bool. s SUBSET t ==> dim(s) <= dim(t)`,
  MESON_TAC[BASIS_EXISTS; INDEPENDENT_SPAN_BOUND; SUBSET; HAS_SIZE]);;

let DIM_SUBSET_UNIV = prove
 (`!s:real^N->bool. dim(s) <= dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[GSYM DIM_UNIV] THEN
  MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);;

let BASIS_HAS_SIZE_UNIV = prove
 (`!b. independent b /\ span b = (:real^N) ==> b HAS_SIZE (dimindex(:N))`,
  REWRITE_TAC[GSYM DIM_UNIV; BASIS_HAS_SIZE_DIM]);;

(* ------------------------------------------------------------------------- *)
(* Converses to those.                                                       *)
(* ------------------------------------------------------------------------- *)

let CARD_GE_DIM_INDEPENDENT = prove
 (`!v b:real^N->bool.
        b SUBSET v /\ independent b /\ dim v <= CARD(b)
        ==> v SUBSET (span b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a:real^N. ~(a IN v /\ ~(a IN span b))` MP_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `independent((a:real^N) INSERT b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INDEPENDENT_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->bool`; `(a:real^N) INSERT b`]
                INDEPENDENT_CARD_LE_DIM) THEN
  ASM_SIMP_TAC[INSERT_SUBSET; CARD_CLAUSES; INDEPENDENT_BOUND] THEN
  ASM_MESON_TAC[SPAN_SUPERSET; SUBSET; ARITH_RULE
    `x <= y ==> ~(SUC y <= x)`]);;

let CARD_LE_DIM_SPANNING = prove
 (`!v b:real^N->bool.
        v SUBSET (span b) /\ FINITE b /\ CARD(b) <= dim v
        ==> independent b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[independent; dependent] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `dim(v:real^N->bool) <= CARD(b DELETE (a:real^N))` MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CARD_DELETE] THEN MATCH_MP_TAC
     (ARITH_RULE `b <= n /\ ~(b = 0) ==> ~(n <= b - 1)`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM_MESON_TAC[MEMBER_NOT_EMPTY]] THEN
  MATCH_MP_TAC SPAN_CARD_GE_DIM THEN ASM_SIMP_TAC[FINITE_DELETE] THEN
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SPAN_TRANS THEN EXISTS_TAC `a:real^N` THEN
  ASM_SIMP_TAC[SET_RULE `a IN b ==> (a INSERT (b DELETE a) = b)`] THEN
  ASM_MESON_TAC[SUBSET]);;

let CARD_EQ_DIM = prove
 (`!v b. b SUBSET v /\ b HAS_SIZE (dim v)
         ==> (independent b <=> v SUBSET (span b))`,
  REWRITE_TAC[HAS_SIZE; GSYM LE_ANTISYM] THEN
  MESON_TAC[CARD_LE_DIM_SPANNING; CARD_GE_DIM_INDEPENDENT]);;

(* ------------------------------------------------------------------------- *)
(* More general size bound lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_BOUND_GENERAL = prove
 (`!s:real^N->bool. independent s ==> FINITE s /\ CARD(s) <= dim(s)`,
  MESON_TAC[INDEPENDENT_CARD_LE_DIM; INDEPENDENT_BOUND; SUBSET_REFL]);;

let DEPENDENT_BIGGERSET_GENERAL = prove
 (`!s:real^N->bool. (FINITE s ==> CARD(s) > dim(s)) ==> dependent s`,
  MP_TAC INDEPENDENT_BOUND_GENERAL THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[GT; GSYM NOT_LE; independent] THEN MESON_TAC[]);;

let DIM_SPAN = prove
 (`!s:real^N->bool. dim(span s) = dim s`,
  GEN_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC DIM_SUBSET THEN MESON_TAC[SUBSET; SPAN_SUPERSET]] THEN
  MP_TAC(ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SPAN_CARD_GE_DIM THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_SPAN] THEN
  MATCH_MP_TAC SPAN_MONO THEN ASM_REWRITE_TAC[]);;

let DIM_INSERT_0 = prove
 (`!s:real^N->bool. dim(vec 0 INSERT s) = dim s`,
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  REWRITE_TAC[SPAN_INSERT_0]);;

let DIM_EQ_CARD = prove
 (`!s:real^N->bool. independent s ==> dim s = CARD s`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`span s:real^N->bool`; `s:real^N->bool`] BASIS_CARD_EQ_DIM) THEN
  ASM_SIMP_TAC[SUBSET_REFL; SPAN_INC; DIM_SPAN]);;

let DEPENDENT_EQ_DIM_LT_CARD = prove
 (`!s:real^N->bool. dependent s <=> FINITE s ==> dim s < CARD s`,
  GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[GSYM GT; DEPENDENT_BIGGERSET_GENERAL] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM independent; NOT_IMP] THEN
  STRIP_TAC THEN MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SPAN_INC] THEN
  ASM_ARITH_TAC);;

let INDEPENDENT_EQ_DIM_EQ_CARD = prove
 (`!s:real^N->bool. independent s <=> FINITE s /\ dim s = CARD s`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[DIM_EQ_CARD; INDEPENDENT_IMP_FINITE] THEN
  SIMP_TAC[DEPENDENT_EQ_DIM_LT_CARD; independent; LT_REFL]);;

let SUBSET_LE_DIM = prove
 (`!s t:real^N->bool. s SUBSET (span t) ==> dim s <= dim t`,
  MESON_TAC[DIM_SPAN; DIM_SUBSET]);;

let SPAN_EQ_DIM = prove
 (`!s t. span s = span t ==> dim s = dim t`,
  MESON_TAC[DIM_SPAN]);;

let SPANS_IMAGE = prove
 (`!f b v. linear f /\ v SUBSET (span b)
           ==> (IMAGE f v) SUBSET span(IMAGE f b)`,
  SIMP_TAC[SPAN_LINEAR_IMAGE; IMAGE_SUBSET]);;

let DIM_LINEAR_IMAGE_LE = prove
 (`!f:real^M->real^N s. linear f ==> dim(IMAGE f s) <= dim s`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^M->bool` BASIS_EXISTS) THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(IMAGE (f:real^M->real^N) b)` THEN
  ASM_SIMP_TAC[CARD_IMAGE_LE] THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
  ASM_MESON_TAC[SPAN_LINEAR_IMAGE; SPANS_IMAGE; SUBSET_IMAGE; FINITE_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Some stepping theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

let DIM_EMPTY = prove
 (`dim({}:real^N->bool) = 0`,
  MATCH_MP_TAC DIM_UNIQUE THEN EXISTS_TAC `{}:real^N->bool` THEN
  REWRITE_TAC[SUBSET_REFL; SPAN_EMPTY; INDEPENDENT_EMPTY; HAS_SIZE_0;
              EMPTY_SUBSET]);;

let DIM_INSERT = prove
 (`!x:real^N s. dim(x INSERT s) = if x IN span s then dim s else dim s + 1`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC SPAN_EQ_DIM THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_MESON_TAC[SPAN_TRANS; SUBSET; SPAN_MONO; IN_INSERT];
    ALL_TAC] THEN
  X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
   (ISPEC `span s:real^N->bool` BASIS_EXISTS) THEN
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `(x:real^N) INSERT b` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET] THEN
    ASM_MESON_TAC[SUBSET; SPAN_MONO; IN_INSERT; SPAN_SUPERSET];
    REWRITE_TAC[SUBSET; SPAN_BREAKDOWN_EQ] THEN
    ASM_MESON_TAC[SUBSET];
    REWRITE_TAC[INDEPENDENT_INSERT] THEN
    ASM_MESON_TAC[SUBSET; SPAN_SUPERSET; SPAN_MONO; SPAN_SPAN];
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT; ADD1] THEN
    ASM_MESON_TAC[SUBSET; SPAN_SUPERSET; SPAN_MONO; SPAN_SPAN]]);;

let DIM_SING = prove
 (`!x. dim{x} = if x = vec 0 then 0 else 1`,
  REWRITE_TAC[DIM_INSERT; DIM_EMPTY; SPAN_EMPTY; IN_SING; ARITH]);;

let DIM_EQ_0 = prove
 (`!s:real^N->bool. dim s = 0 <=> s SUBSET {vec 0}`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~(?b. ~(b = a) /\ {b} SUBSET s) ==> s SUBSET {a}`) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP DIM_SUBSET);
    MATCH_MP_TAC(ARITH_RULE `!m. m = 0 /\ n <= m ==> n = 0`) THEN
    EXISTS_TAC `dim{vec 0:real^N}` THEN ASM_SIMP_TAC[DIM_SUBSET]] THEN
  ASM_REWRITE_TAC[DIM_SING; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Choosing a subspace of a given dimension.                                 *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_SUBSPACE_OF_SUBSPACE = prove
 (`!s:real^N->bool n.
        n <= dim s ==> ?t. subspace t /\ t SUBSET span s /\ dim t = n`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `{vec 0:real^N}` THEN
    REWRITE_TAC[SUBSPACE_TRIVIAL; DIM_SING; SING_SUBSET; SPAN_0];
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `span (s:real^N->bool) SUBSET span t` THENL
     [SUBGOAL_THEN `dim(s:real^N->bool) = dim(t:real^N->bool)` MP_TAC THENL
       [ALL_TAC; ASM_ARITH_TAC] THEN MATCH_MP_TAC SPAN_EQ_DIM THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN ASM_REWRITE_TAC[SUBSPACE_SPAN];
      FIRST_ASSUM(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC o MATCH_MP(SET_RULE
       `~(s SUBSET t) ==> ?a. a IN s /\ ~(a IN t)`)) THEN
      EXISTS_TAC `span((y:real^N) INSERT t)` THEN
      REWRITE_TAC[SUBSPACE_SPAN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
        ASM_REWRITE_TAC[SUBSPACE_SPAN] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[DIM_SPAN; DIM_INSERT; ADD1]]]]);;

(* ------------------------------------------------------------------------- *)
(* Relation between bases and injectivity/surjectivity of map.               *)
(* ------------------------------------------------------------------------- *)

let SPANNING_SURJECTIVE_IMAGE = prove
 (`!f:real^M->real^N s.
        UNIV SUBSET (span s) /\ linear f /\ (!y. ?x. f(x) = y)
        ==> UNIV SUBSET span(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) UNIV` THEN
  ASM_SIMP_TAC[SPANS_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_UNIV; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let INDEPENDENT_INJECTIVE_IMAGE_GEN = prove
 (`!f:real^M->real^N s.
        independent s /\ linear f /\
        (!x y. x IN span s /\ y IN span s /\ f(x) = f(y) ==> x = y)
        ==> independent (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[independent; DEPENDENT_EXPLICIT] THEN
  REWRITE_TAC[CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[MESON[]
     `(?s u. ((?t. p t /\ s = f t) /\ q s u) /\ r s u) <=>
      (?t u. p t /\ q (f t) u /\ r (f t) u)`] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `u:real^N->real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`t:real^M->bool`; `(u:real^N->real) o (f:real^M->real^N)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[];
    REWRITE_TAC[SPAN_0];
    ASM_SIMP_TAC[LINEAR_VSUM] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP LINEAR_0) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    ASM_SIMP_TAC[o_DEF; LINEAR_CMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[SPAN_SUPERSET; SUBSET]]);;

let INDEPENDENT_INJECTIVE_IMAGE = prove
 (`!f:real^M->real^N s.
        independent s /\ linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> independent (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Picking an orthogonal replacement for a spanning set.                     *)
(* ------------------------------------------------------------------------- *)

let VECTOR_SUB_PROJECT_ORTHOGONAL = prove
 (`!b:real^N x. b dot (x - ((b dot x) / (b dot b)) % b) = &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b = vec 0 :real^N` THENL
   [ASM_REWRITE_TAC[DOT_LZERO]; ALL_TAC] THEN
  ASM_SIMP_TAC[DOT_RSUB; DOT_RMUL] THEN
  ASM_SIMP_TAC[REAL_SUB_REFL; REAL_DIV_RMUL; DOT_EQ_0]);;

let BASIS_ORTHOGONAL = prove
 (`!b:real^N->bool.
        FINITE b
        ==> ?c. FINITE c /\ CARD c <= CARD b /\
                span c = span b /\ pairwise orthogonal c`,
  REWRITE_TAC[pairwise; orthogonal] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [EXISTS_TAC `{}:real^N->bool` THEN
    REWRITE_TAC[FINITE_RULES; NOT_IN_EMPTY; LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a - vsum c (\x. ((x dot a) / (x dot x)) % x):real^N)
              INSERT c` THEN
  ASM_SIMP_TAC[FINITE_RULES; CARD_CLAUSES] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[EXTENSION; SPAN_BREAKDOWN_EQ] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN GEN_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN
    REWRITE_TAC[VECTOR_ARITH `a - (x - y):real^N = y + (a - x)`] THEN
    MATCH_MP_TAC SPAN_ADD_EQ THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    ASM_SIMP_TAC[SPAN_SUPERSET];
    REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC;
      FIRST_X_ASSUM SUBST_ALL_TAC;
      ASM_MESON_TAC[]] THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB; REAL_SUB_0] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
    ASM_SIMP_TAC[VSUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    MATCH_MP_TAC(REAL_ARITH `s = &0 /\ a = b ==> b = a + s`) THEN
    ASM_SIMP_TAC[DOT_LSUM; DOT_RSUM; FINITE_DELETE] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC SUM_EQ_0 THEN
       ASM_SIMP_TAC[DOT_LMUL; DOT_RMUL; IN_DELETE;
                    REAL_MUL_RZERO; REAL_MUL_LZERO];
       W(MP_TAC o PART_MATCH (lhand o rand) REAL_DIV_RMUL o lhand o snd) THEN
       REWRITE_TAC[DOT_SYM] THEN
       MATCH_MP_TAC(TAUT `(p ==> q) ==> (~p ==> q) ==> q`) THEN
       SIMP_TAC[] THEN SIMP_TAC[DOT_EQ_0; DOT_RZERO; DOT_LZERO] THEN
       REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]])]);;

let ORTHOGONAL_BASIS_EXISTS = prove
 (`!v:real^N->bool.
        ?b. independent b /\
            b SUBSET span v /\
            v SUBSET span b /\
            b HAS_SIZE dim v /\
            pairwise orthogonal b`,
  GEN_TAC THEN MP_TAC(ISPEC `v:real^N->bool` BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `b:real^N->bool` BASIS_ORTHOGONAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `span(v):real^N->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SPAN_SPAN; SPAN_MONO];
      ASM_MESON_TAC[LE_TRANS; HAS_SIZE; DIM_SPAN]];
    ASM_MESON_TAC[SUBSET_TRANS; SPAN_INC; SPAN_SPAN; SPAN_MONO];
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_REWRITE_TAC[HAS_SIZE; GSYM LE_ANTISYM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SPAN_SPAN; SPAN_MONO; SUBSET_TRANS; SPAN_INC]]);;

let SPAN_EQ = prove
 (`!s t. span s = span t <=> s SUBSET span t /\ t SUBSET span s`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  MESON_TAC[SUBSET_TRANS; SPAN_SPAN; SPAN_MONO; SPAN_INC]);;

let SPAN_EQ_INSERT = prove
 (`!s x. span(x INSERT s) = span s <=> x IN span s`,
  REWRITE_TAC[SPAN_EQ; INSERT_SUBSET] THEN
  MESON_TAC[SPAN_INC; SUBSET; SET_RULE `s SUBSET (x INSERT s)`]);;

let SPAN_SPECIAL_SCALE = prove
 (`!s a x:real^N.
     span((a % x) INSERT s) = if a = &0 then span s else span(x INSERT s)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; SPAN_INSERT_0] THEN
  REWRITE_TAC[SPAN_EQ; SUBSET; FORALL_IN_INSERT] THEN
  SIMP_TAC[SPAN_MUL; SPAN_SUPERSET; IN_INSERT] THEN
  REWRITE_TAC[SPAN_BREAKDOWN_EQ] THEN EXISTS_TAC `inv a:real` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  REWRITE_TAC[SPAN_0; VECTOR_SUB_REFL]);;

(* ------------------------------------------------------------------------- *)
(* We can extend a linear basis-basis injection to the whole set.            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INDEP_IMAGE_LEMMA = prove
 (`!f b. linear(f:real^M->real^N) /\
         FINITE b /\
         independent (IMAGE f b) /\
         (!x y. x IN b /\ y IN b /\ (f x = f y) ==> (x = y))
         ==> !x. x IN span b ==> (f(x) = vec 0) ==> (x = vec 0)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [IMP_IMP] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [SIMP_TAC[IN_SING; SPAN_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M->bool`] THEN STRIP_TAC THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INDEPENDENT_MONO; IMAGE_CLAUSES; SUBSET; IN_INSERT];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^M`; `(a:real^M) INSERT b`; `x:real^M`]
    SPAN_BREAKDOWN) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  SIMP_TAC[ASSUME `~((a:real^M) IN b)`; SET_RULE
    `~(a IN b) ==> ((a INSERT b) DELETE a = b)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N)(x - k % a) IN span(IMAGE f b)` MP_TAC THENL
   [ASM_MESON_TAC[SPAN_LINEAR_IMAGE; IN_IMAGE]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `vec 0 - k % x = (--k) % x`] THEN
  ASM_CASES_TAC `k = &0` THENL
   [ASM_MESON_TAC[VECTOR_ARITH `x - &0 % y = x`]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `--inv(k)` o MATCH_MP SPAN_MUL) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  SIMP_TAC[REAL_NEGNEG; REAL_MUL_LINV; ASSUME `~(k = &0)`] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [independent]) THEN
  REWRITE_TAC[dependent; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) a`) THEN
  SUBGOAL_THEN
   `IMAGE (f:real^M->real^N) (a INSERT b) DELETE f a =
    IMAGE f ((a INSERT b) DELETE a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_INSERT] THEN
    ASM_MESON_TAC[IN_INSERT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DELETE_INSERT] THEN
  SIMP_TAC[SET_RULE `~(a IN b) ==> (b DELETE a = b)`;
           ASSUME `~(a:real^M IN b)`] THEN
  SIMP_TAC[IMAGE_CLAUSES; IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* We can extend a linear mapping from basis.                                *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INDEPENDENT_EXTEND_LEMMA = prove
 (`!f b. FINITE b
         ==> independent b
             ==> ?g:real^M->real^N.
                        (!x y. x IN span b /\ y IN span b
                                ==> (g(x + y) = g(x) + g(y))) /\
                        (!x c. x IN span b ==> (g(c % x) = c % g(x))) /\
                        (!x. x IN b ==> (g x = f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; INDEPENDENT_INSERT] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `(\x. vec 0):real^M->real^N` THEN
    SIMP_TAC[SPAN_EMPTY] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = \z:real^M. @k. (z - k % a) IN span b` THEN
  SUBGOAL_THEN `!z:real^M. z IN span(a INSERT b)
                    ==> (z - h(z) % a) IN span(b) /\
                        !k. (z - k % a) IN span(b) ==> (k = h(z))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "h" THEN CONV_TAC SELECT_CONV THEN
      ASM_MESON_TAC[SPAN_BREAKDOWN_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP SPAN_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `(z - a % v) - (z - b % v) = (b - a) % v`] THEN
    ASM_CASES_TAC `k = (h:real^M->real) z` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(k - (h:real^M->real) z)` o
               MATCH_MP SPAN_MUL) THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_ASSOC; REAL_SUB_0] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_AND_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `\z:real^M. h(z) % (f:real^M->real^N)(a) + g(z - h(z) % a)` THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^M->real)(x + y) = h(x) + h(y)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x + y) - (k + l) % a = (x - k % a) + (y - l % a)`] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_ADD THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
       `(x + y) - (k + l) % a = (x - k % a) + (y - l % a)`] THEN
    ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^M`; `c:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^M->real)(c % x) = c * h(x)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH
       `c % x - (c * k) % a = c % (x - k % a)`] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_MUL THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
       `c % x - (c * k) % a = c % (x - k % a)`] THEN
    ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [SUBGOAL_THEN `&1 = h(a:real^M)` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `a - &1 % a = vec 0`; SPAN_0] THENL
     [ASM_MESON_TAC[SPAN_SUPERSET; SUBSET; IN_INSERT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^M`; `vec 0:real^M`]) THEN
    REWRITE_TAC[SPAN_0; VECTOR_ADD_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(a = a + a) <=> (a = vec 0)`] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = h(x:real^M)` (SUBST1_TAC o SYM) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  ASM_MESON_TAC[SUBSET; IN_INSERT; SPAN_SUPERSET]);;

let LINEAR_INDEPENDENT_EXTEND = prove
 (`!f b. independent b
         ==> ?g:real^M->real^N. linear g /\ (!x. x IN b ==> (g x = f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^M->bool`; `(:real^M)`]
           MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; UNIV_SUBSET] THEN
  REWRITE_TAC[EXTENSION; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `c:real^M->bool`]
    LINEAR_INDEPENDENT_EXTEND_LEMMA) THEN
  ASM_SIMP_TAC[INDEPENDENT_BOUND; linear] THEN
  ASM_MESON_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Linear functions are equal on a subspace if they are on a spanning set.   *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_KERNEL = prove
 (`!f. linear f ==> subspace {x | f(x) = vec 0}`,
  REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; VECTOR_ADD_LID; VECTOR_MUL_RZERO] THEN
  MESON_TAC[LINEAR_0]);;

let LINEAR_EQ_0_SPAN = prove
 (`!f:real^M->real^N b.
        linear f /\ (!x. x IN b ==> f(x) = vec 0)
        ==> !x. x IN span(b) ==> f(x) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN ASM_REWRITE_TAC[IN] THEN
  MP_TAC(ISPEC `f:real^M->real^N` SUBSPACE_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM]);;

let LINEAR_EQ_0 = prove
 (`!f b s. linear f /\ s SUBSET (span b) /\ (!x. x IN b ==> f(x) = vec 0)
           ==> !x. x IN s ==> f(x) = vec 0`,
  MESON_TAC[LINEAR_EQ_0_SPAN; SUBSET]);;

let LINEAR_EQ = prove
 (`!f g b s. linear f /\ linear g /\ s SUBSET (span b) /\
             (!x. x IN b ==> f(x) = g(x))
              ==> !x. x IN s ==> f(x) = g(x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  STRIP_TAC THEN MATCH_MP_TAC LINEAR_EQ_0 THEN
  ASM_MESON_TAC[LINEAR_COMPOSE_SUB]);;

let LINEAR_EQ_STDBASIS = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g /\
        (!i. 1 <= i /\ i <= dimindex(:M)
             ==> f(basis i) = g(basis i))
        ==> f = g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN UNIV ==> (f:real^M->real^N) x = g x`
   (fun th -> MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM; IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_EQ THEN
  EXISTS_TAC `{basis i :real^M | 1 <= i /\ i <= dimindex(:M)}` THEN
  ASM_REWRITE_TAC[SPAN_STDBASIS; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let SUBSPACE_LINEAR_FIXED_POINTS = prove
 (`!f:real^N->real^N. linear f ==> subspace {x | f(x) = x}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC SUBSPACE_KERNEL THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE_SUB; LINEAR_ID]);;

(* ------------------------------------------------------------------------- *)
(* Similar results for bilinear functions.                                   *)
(* ------------------------------------------------------------------------- *)

let BILINEAR_EQ = prove
 (`!f:real^M->real^N->real^P g b c s.
        bilinear f /\ bilinear g /\
        s SUBSET (span b) /\ t SUBSET (span c) /\
        (!x y. x IN b /\ y IN c ==> f x y = g x y)
         ==> !x y. x IN s /\ y IN t ==> f x y = g x y`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
    `!x:real^M. x IN span b
                ==> !y:real^N. y IN span c ==> (f x y :real^P = g x y)`
    (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC;
    ASM_SIMP_TAC[BILINEAR_LADD; BILINEAR_LMUL] THEN
    ASM_MESON_TAC[BILINEAR_LZERO]] THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[BILINEAR_RADD; BILINEAR_RMUL] THEN
  ASM_MESON_TAC[BILINEAR_RZERO]);;

let BILINEAR_EQ_STDBASIS = prove
 (`!f:real^M->real^N->real^P g.
        bilinear f /\ bilinear g /\
        (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N)
             ==> f (basis i) (basis j) = g (basis i) (basis j))
        ==> f = g`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `!x y. x IN UNIV /\ y IN UNIV ==> (f:real^M->real^N->real^P) x y = g x y`
   (fun th -> MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM; IN_UNIV]) THEN
  MATCH_MP_TAC BILINEAR_EQ THEN
  EXISTS_TAC `{basis i :real^M | 1 <= i /\ i <= dimindex(:M)}` THEN
  EXISTS_TAC `{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}` THEN
  ASM_REWRITE_TAC[SPAN_STDBASIS; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Detailed theorems about left and right invertibility in general case.     *)
(* ------------------------------------------------------------------------- *)

let LEFT_INVERTIBLE_TRANSP = prove
 (`!A:real^N^M.
    (?B:real^N^M. B ** transp A = mat 1) <=> (?B:real^M^N. A ** B = mat 1)`,
  MESON_TAC[MATRIX_TRANSP_MUL; TRANSP_MAT; TRANSP_TRANSP]);;

let RIGHT_INVERTIBLE_TRANSP = prove
 (`!A:real^N^M.
    (?B:real^N^M. transp A ** B = mat 1) <=> (?B:real^M^N. B ** A = mat 1)`,
  MESON_TAC[MATRIX_TRANSP_MUL; TRANSP_MAT; TRANSP_TRANSP]);;

let INVERTIBLE_TRANSP = prove
 (`!A:real^N^M. invertible(transp A) <=> invertible A`,
  GEN_TAC THEN REWRITE_TAC[invertible] THEN
  GEN_REWRITE_TAC LAND_CONV [MESON[TRANSP_TRANSP]
    `(?A:real^M^N. P A) <=> (?A:real^N^M. P(transp A))`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM TRANSP_MAT] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL; TRANSP_EQ] THEN MESON_TAC[]);;

let LINEAR_INJECTIVE_LEFT_INVERSE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?g. linear g /\ g o f = I`,
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?h. linear(h:real^N->real^M) /\
        !x. x IN IMAGE (f:real^M->real^N)
               {basis i | 1 <= i /\ i <= dimindex(:M)} ==> h x = g x`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
    MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE THEN
    ASM_MESON_TAC[INJECTIVE_LEFT_INVERSE; INDEPENDENT_STDBASIS];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^N->real^M` THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC[I_DEF; LINEAR_COMPOSE; LINEAR_ID; o_THM] THEN
    ASM_MESON_TAC[]]);;

let LINEAR_SURJECTIVE_RIGHT_INVERSE = prove
 (`!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y) ==> ?g. linear g /\ f o g = I`,
  REWRITE_TAC[SURJECTIVE_RIGHT_INVERSE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?h. linear(h:real^N->real^M) /\
        !x. x IN {basis i | 1 <= i /\ i <= dimindex(:N)} ==> h x = g x`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
    REWRITE_TAC[INDEPENDENT_STDBASIS];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^N->real^M` THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC[I_DEF; LINEAR_COMPOSE; LINEAR_ID; o_THM] THEN
    ASM_MESON_TAC[]]);;

let MATRIX_LEFT_INVERTIBLE_INJECTIVE = prove
 (`!A:real^N^M.
        (?B:real^M^N. B ** A = mat 1) <=>
        !x y:real^N. A ** x = A ** y ==> x = y`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^M. (B:real^M^N) ** x`) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    DISCH_TAC THEN MP_TAC(ISPEC
     `\x:real^N. (A:real^N^M) ** x` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; FUN_EQ_THM; I_THM; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(g):real^M^N` THEN
    REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LID] THEN
    ASM_MESON_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_WORKS]]);;

let MATRIX_LEFT_INVERTIBLE_KER = prove
 (`!A:real^N^M.
        (?B:real^M^N. B ** A = mat 1) <=> !x. A ** x = vec 0 ==> x = vec 0`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  MATCH_MP_TAC LINEAR_INJECTIVE_0 THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let MATRIX_RIGHT_INVERTIBLE_SURJECTIVE = prove
 (`!A:real^N^M.
        (?B:real^M^N. A ** B = mat 1) <=> !y:real^M. ?x. A ** x = y`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `y:real^M` THEN
    EXISTS_TAC `(B:real^M^N) ** (y:real^M)` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    DISCH_TAC THEN MP_TAC(ISPEC
     `\x:real^N. (A:real^N^M) ** x` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; FUN_EQ_THM; I_THM; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(g):real^M^N` THEN
    REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LID] THEN
    ASM_MESON_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_WORKS]]);;

let MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS = prove
 (`!A:real^N^M. (?B:real^M^N. B ** A = mat 1) <=>
                !c. vsum(1..dimindex(:N)) (\i. c(i) % column i A) = vec 0 ==>
                    !i. 1 <= i /\ i <= dimindex(:N) ==> c(i) = &0`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_KER; MATRIX_MUL_VSUM] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `c:num->real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(lambda i. c(i)):real^N`);
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (x:real^N)$i`)] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; CART_EQ; VEC_COMPONENT]);;

let MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS = prove
 (`!A:real^N^M. (?B:real^M^N. A ** B = mat 1) <=>
                !c. vsum(1..dimindex(:M)) (\i. c(i) % row i A) = vec 0 ==>
                    !i. 1 <= i /\ i <= dimindex(:M) ==> c(i) = &0`,
  ONCE_REWRITE_TAC[GSYM LEFT_INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS] THEN
  SIMP_TAC[COLUMN_TRANSP]);;

let MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS = prove
 (`!A:real^N^M. (?B:real^M^N. A ** B = mat 1) <=> span(columns A) = (:real^M)`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
  REWRITE_TAC[MATRIX_MUL_VSUM; EXTENSION; IN_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC(CONJUNCT1 SPAN_CLAUSES) THEN
    REWRITE_TAC[columns; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`y:real^M`,`y:real^M`) THEN MATCH_MP_TAC SPAN_INDUCT_ALT THEN
  CONJ_TAC THENL
   [EXISTS_TAC `vec 0 :real^N` THEN
    SIMP_TAC[VEC_COMPONENT; VECTOR_MUL_LZERO; VSUM_0];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `y1:real^M`; `y2:real^M`] THEN
  REWRITE_TAC[columns; IN_ELIM_THM] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `x:real^N` (SUBST1_TAC o SYM))) THEN
  EXISTS_TAC `(lambda j. if j = i then c + (x:real^N)$i else x$j):real^N` THEN
  SUBGOAL_THEN `1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)`
  SUBST1_TAC THENL [ASM_MESON_TAC[INSERT_DELETE; IN_NUMSEG]; ALL_TAC] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_RDISTRIB; VECTOR_ADD_ASSOC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  SIMP_TAC[FINITE_DELETE; IN_DELETE; FINITE_NUMSEG; LAMBDA_BETA; IN_NUMSEG]);;

let MATRIX_LEFT_INVERTIBLE_SPAN_ROWS = prove
 (`!A:real^N^M. (?B:real^M^N. B ** A = mat 1) <=> span(rows A) = (:real^N)`,
  MESON_TAC[RIGHT_INVERTIBLE_TRANSP; COLUMNS_TRANSP;
            MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS]);;

(* ------------------------------------------------------------------------- *)
(* An injective map real^N->real^N is also surjective.                       *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INJECTIVE_IMP_SURJECTIVE = prove
 (`!f:real^N->real^N.
        linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> !y. ?x. f(x) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:real^N)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_UNIV; HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIV SUBSET span(IMAGE (f:real^N->real^N) b)` MP_TAC THENL
   [MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
    ASM_MESON_TAC[INDEPENDENT_INJECTIVE_IMAGE; LE_REFL;
                  SUBSET_UNIV; CARD_IMAGE_INJ];
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE] THEN
    ASM_MESON_TAC[SUBSET; IN_IMAGE; IN_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* And vice versa.                                                           *)
(* ------------------------------------------------------------------------- *)

let LINEAR_SURJECTIVE_IMP_INJECTIVE = prove
 (`!f:real^N->real^N.
        linear f /\ (!y. ?x. f(x) = y)
        ==> !x y. (f(x) = f(y)) ==> (x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:real^N)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_UNIV; HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN span b ==> (f:real^N->real^N) x = vec 0 ==> x = vec 0`
   (fun th -> ASM_MESON_TAC[th; LINEAR_INJECTIVE_0; SUBSET; IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_INDEP_IMAGE_LEMMA THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN
    EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; FINITE_IMAGE; SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_UNIV; IN_IMAGE] THEN
    ASM_MESON_TAC[CARD_IMAGE_LE; SUBSET; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `dim(:real^N) <= CARD(IMAGE (f:real^N->real^N) b)`
  MP_TAC THENL
   [MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
    ASM_SIMP_TAC[SUBSET_UNIV; FINITE_IMAGE] THEN
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^N->real^N) UNIV` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    ASM_REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ISPEC `f:real^N->real^N` o
                MATCH_MP CARD_IMAGE_LE) THEN
  ASM_REWRITE_TAC[IMP_IMP; LE_ANTISYM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`b:real^N->bool`; `IMAGE (f:real^N->real^N) b`; `f:real^N->real^N`]
   SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; INDEPENDENT_BOUND; SUBSET_REFL] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN MESON_TAC[]);;

let LINEAR_SURJECTIVE_IFF_INJECTIVE = prove
 (`!f:real^N->real^N.
      linear f ==> ((!y. ?x. f x = y) <=> (!x y. f x = f y ==> x = y))`,
  MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE;
            LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

(* ------------------------------------------------------------------------- *)
(* Hence either is enough for isomorphism.                                   *)
(* ------------------------------------------------------------------------- *)

let LEFT_RIGHT_INVERSE_EQ = prove
 (`!f:A->A g h. f o g = I /\ g o h = I ==> f = h`,
  MESON_TAC[o_ASSOC; I_O_ID]);;

let ISOMORPHISM_EXPAND = prove
 (`!f g. f o g = I /\ g o f = I <=> (!x. f(g x) = x) /\ (!x. g(f x) = x)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM]);;

let LINEAR_INJECTIVE_ISOMORPHISM = prove
 (`!f:real^N->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ISOMORPHISM_EXPAND] THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN MESON_TAC[LEFT_RIGHT_INVERSE_EQ]);;

let LINEAR_SURJECTIVE_ISOMORPHISM = prove
 (`!f:real^N->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ISOMORPHISM_EXPAND] THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_SURJECTIVE_IMP_INJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN MESON_TAC[LEFT_RIGHT_INVERSE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Left and right inverses are the same for R^N->R^N.                        *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVERSE_LEFT = prove
 (`!f:real^N->real^N f'.
        linear f /\ linear f' ==> ((f o f' = I) <=> (f' o f = I))`,
  SUBGOAL_THEN
   `!f:real^N->real^N f'.
        linear f /\ linear f' /\ (f o f' = I) ==> (f' o f = I)`
   (fun th -> MESON_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Moreover, a one-sided inverse is automatically linear.                    *)
(* ------------------------------------------------------------------------- *)

let LEFT_INVERSE_LINEAR = prove
 (`!f g:real^N->real^N. linear f /\ (g o f = I) ==> linear g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  STRIP_TAC THEN SUBGOAL_THEN
   `?h:real^N->real^N. linear h /\ (!x. h(f x) = x) /\ (!x. f(h x) = x)`
  CHOOSE_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_ISOMORPHISM THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `g:real^N->real^N = h` (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]]);;

let RIGHT_INVERSE_LINEAR = prove
 (`!f g:real^N->real^N. linear f /\ (f o g = I) ==> linear g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  STRIP_TAC THEN SUBGOAL_THEN
   `?h:real^N->real^N. linear h /\ (!x. h(f x) = x) /\ (!x. f(h x) = x)`
  CHOOSE_TAC THENL [ASM_MESON_TAC[LINEAR_SURJECTIVE_ISOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `g:real^N->real^N = h` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Without (ostensible) constraints on types, though dimensions must match.  *)
(* ------------------------------------------------------------------------- *)

let LEFT_RIGHT_INVERSE_LINEAR = prove
 (`!f g:real^M->real^N.
        linear f /\ g o f = I /\ f o g = I ==> linear g`,
  REWRITE_TAC[linear; FUN_EQ_THM; o_THM; I_THM] THEN MESON_TAC[]);;

let LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ?g. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BIJECTIVE_LEFT_RIGHT_INVERSE]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LEFT_RIGHT_INVERSE_LINEAR THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* The same result in terms of square matrices.                              *)
(* ------------------------------------------------------------------------- *)

let MATRIX_LEFT_RIGHT_INVERSE = prove
 (`!A:real^N^N A':real^N^N. (A ** A' = mat 1) <=> (A' ** A = mat 1)`,
  SUBGOAL_THEN
    `!A:real^N^N A':real^N^N. (A ** A' = mat 1) ==> (A' ** A = mat 1)`
    (fun th -> MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^N. A:(real^N^N) ** x`
    LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXISTS_TAC `(A':real^N^N) ** (x:real^N)` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `matrix (f':real^N->real^N) ** (A:real^N^N) = mat 1`
  MP_TAC THENL
   [ASM_SIMP_TAC[MATRIX_EQ; MATRIX_WORKS; GSYM MATRIX_VECTOR_MUL_ASSOC;
                 MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o AP_TERM `(\m:real^N^N. m ** (A':real^N^N))`) THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RID; MATRIX_MUL_LID] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Invertibility of matrices and corresponding linear functions.             *)
(* ------------------------------------------------------------------------- *)

let MATRIX_LEFT_INVERTIBLE = prove
 (`!f:real^M->real^N.
    linear f ==> ((?B:real^N^M. B ** matrix f = mat 1) <=>
                  (?g. linear g /\ g o f = I))`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `\y:real^N. (B:real^N^M) ** y` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; MATRIX_VECTOR_MUL_ASSOC;
                    MATRIX_VECTOR_MUL_LID];
    EXISTS_TAC `matrix(g:real^N->real^M)` THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE; MATRIX_I]]);;

let MATRIX_RIGHT_INVERTIBLE = prove
 (`!f:real^M->real^N.
    linear f ==> ((?B:real^N^M. matrix f ** B = mat 1) <=>
                  (?g. linear g /\ f o g = I))`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `\y:real^N. (B:real^N^M) ** y` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; MATRIX_VECTOR_MUL_ASSOC;
                    MATRIX_VECTOR_MUL_LID];
    EXISTS_TAC `matrix(g:real^N->real^M)` THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE; MATRIX_I]]);;

let INVERTIBLE_LEFT_INVERSE = prove
 (`!A:real^N^N. invertible(A) <=> ?B:real^N^N. B ** A = mat 1`,
  MESON_TAC[invertible; MATRIX_LEFT_RIGHT_INVERSE]);;

let INVERTIBLE_RIGHT_INVERSE = prove
 (`!A:real^N^N. invertible(A) <=> ?B:real^N^N. A ** B = mat 1`,
  MESON_TAC[invertible; MATRIX_LEFT_RIGHT_INVERSE]);;

let MATRIX_INVERTIBLE = prove
 (`!f:real^N->real^N.
        linear f
        ==> (invertible(matrix f) <=>
             ?g. linear g /\ f o g = I /\ g o f = I)`,
  SIMP_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE] THEN
  MESON_TAC[LINEAR_INVERSE_LEFT]);;

(* ------------------------------------------------------------------------- *)
(* Left-invertible linear transformation has a lower bound.                  *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVERTIBLE_BOUNDED_BELOW_POS = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g /\ (g o f = I)
        ==> ?B. &0 < B /\ !x. B * norm(x) <= norm(f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^N->real^M` LINEAR_BOUNDED_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv B:real` THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  X_GEN_TAC `x:real^M` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(B) * norm(((g:real^N->real^M) o (f:real^M->real^N)) x)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[I_THM; REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `inv B * x = x / B`] THEN
  ASM_SIMP_TAC[o_THM; REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

let LINEAR_INVERTIBLE_BOUNDED_BELOW = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g /\ (g o f = I)
        ==> ?B. !x. B * norm(x) <= norm(f x)`,
  MESON_TAC[LINEAR_INVERTIBLE_BOUNDED_BELOW_POS]);;

let LINEAR_INJECTIVE_BOUNDED_BELOW_POS = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?B. &0 < B /\ !x. norm(x) * B <= norm(f x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC LINEAR_INVERTIBLE_BOUNDED_BELOW_POS THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_LEFT_INVERSE]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of dimension by injective map.                               *)
(* ------------------------------------------------------------------------- *)

let DIM_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) ==> dim(IMAGE f s) = dim s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIM_LINEAR_IMAGE_LE]; ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `dim(IMAGE (g:real^N->real^M) (IMAGE (f:real^M->real^N) s))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID; LE_REFL];
    MATCH_MP_TAC DIM_LINEAR_IMAGE_LE THEN ASM_REWRITE_TAC[]]);;

let LINEAR_INJECTIVE_DIMINDEX_LE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> dimindex(:M) <= dimindex(:N)`,
  REWRITE_TAC[GSYM DIM_UNIV] THEN REPEAT GEN_TAC THEN DISCH_THEN
   (SUBST1_TAC o SYM o SPEC `(:real^M)` o
    MATCH_MP DIM_INJECTIVE_LINEAR_IMAGE) THEN
  MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);;

let LINEAR_SURJECTIVE_DIMINDEX_LE = prove
 (`!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> dimindex(:N) <= dimindex(:M)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^N->real^M` THEN STRIP_TAC THEN
  MATCH_MP_TAC LINEAR_INJECTIVE_DIMINDEX_LE THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM_MESON_TAC[]);;

let LINEAR_BIJECTIVE_DIMINDEX_EQ = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> dimindex(:M) = dimindex(:N)`,
  REWRITE_TAC[GSYM LE_ANTISYM] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_DIMINDEX_LE;
    MATCH_MP_TAC LINEAR_SURJECTIVE_DIMINDEX_LE] THEN
  EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[]);;

let INVERTIBLE_IMP_SQUARE_MATRIX = prove
 (`!A:real^N^M. invertible A ==> dimindex(:M) = dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[invertible; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:real^M^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC LINEAR_BIJECTIVE_DIMINDEX_EQ THEN
  EXISTS_TAC `\x:real^M. (B:real^M^N) ** x` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR;
                  GSYM MATRIX_LEFT_INVERTIBLE_INJECTIVE;
                  GSYM MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Considering an n-element vector as an n-by-1 or 1-by-n matrix.            *)
(* ------------------------------------------------------------------------- *)

let rowvector = new_definition
 `(rowvector:real^N->real^N^1) v = lambda i j. v$j`;;

let columnvector = new_definition
 `(columnvector:real^N->real^1^N) v = lambda i j. v$i`;;

let TRANSP_COLUMNVECTOR = prove
 (`!v. transp(columnvector v) = rowvector v`,
  SIMP_TAC[transp; columnvector; rowvector; CART_EQ; LAMBDA_BETA]);;

let TRANSP_ROWVECTOR = prove
 (`!v. transp(rowvector v) = columnvector v`,
  SIMP_TAC[transp; columnvector; rowvector; CART_EQ; LAMBDA_BETA]);;

let DOT_ROWVECTOR_COLUMNVECTOR = prove
 (`!A:real^N^M v:real^N. columnvector(A ** v) = A ** columnvector v`,
  REWRITE_TAC[rowvector; columnvector; matrix_mul; matrix_vector_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA]);;

let DOT_MATRIX_PRODUCT = prove
 (`!x y:real^N. x dot y = (rowvector x ** columnvector y)$1$1`,
  REWRITE_TAC[matrix_mul; columnvector; rowvector; dot] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_1; LE_REFL]);;

let DOT_MATRIX_VECTOR_MUL = prove
 (`!A:real^N^N B:real^N^N x:real^N y:real^N.
      (A ** x) dot (B ** y) =
      ((rowvector x) ** (transp(A) ** B) ** (columnvector y))$1$1`,
  REWRITE_TAC[DOT_MATRIX_PRODUCT] THEN
  ONCE_REWRITE_TAC[GSYM TRANSP_COLUMNVECTOR] THEN
  REWRITE_TAC[DOT_ROWVECTOR_COLUMNVECTOR; MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Rank of a matrix. Equivalence of row and column rank is taken from        *)
(* George Mackiw's paper, Mathematics Magazine 1995, p. 285.                 *)
(* ------------------------------------------------------------------------- *)

let MATRIX_VECTOR_MUL_IN_COLUMNSPACE = prove
 (`!A:real^M^N x:real^M. (A ** x) IN span(columns A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_COLUMN; columns] THEN
  MATCH_MP_TAC SPAN_VSUM THEN
  SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; transp; LAMBDA_BETA] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN
  REWRITE_TAC[IN_ELIM_THM; column] THEN EXISTS_TAC `k:num` THEN
  ASM_REWRITE_TAC[]);;

let SUBSPACE_ORTHOGONAL_TO_VECTOR = prove
 (`!x. subspace {y | orthogonal x y}`,
  SIMP_TAC[subspace; IN_ELIM_THM; ORTHOGONAL_CLAUSES]);;

let SUBSPACE_ORTHOGONAL_TO_VECTORS = prove
 (`!s. subspace {y | (!x. x IN s ==> orthogonal x y)}`,
  SIMP_TAC[subspace; IN_ELIM_THM; ORTHOGONAL_CLAUSES]);;

let ORTHOGONAL_TO_SPAN = prove
 (`!s x. (!y. y IN s ==> orthogonal x y)
         ==> !y. y IN span(s) ==> orthogonal x y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
  REWRITE_TAC[SET_RULE `(\y. orthogonal x y) = {y | orthogonal x y}`] THEN
  ASM_SIMP_TAC[SUBSPACE_ORTHOGONAL_TO_VECTOR; IN_ELIM_THM]);;

let ORTHOGONAL_TO_SPAN_EQ = prove
 (`!s x. (!y. y IN span(s) ==> orthogonal x y) <=>
         (!y. y IN s ==> orthogonal x y)`,
  MESON_TAC[SPAN_SUPERSET; ORTHOGONAL_TO_SPAN]);;

let ORTHOGONAL_TO_SPANS_EQ = prove
 (`!s t. (!x y. x IN span(s) /\ y IN span(t) ==> orthogonal x y) <=>
         (!x y. x IN s /\ y IN t ==> orthogonal x y)`,
  MESON_TAC[ORTHOGONAL_TO_SPAN_EQ; ORTHOGONAL_SYM]);;

let ORTHOGONAL_NULLSPACE_ROWSPACE = prove
 (`!A:real^M^N x y:real^M.
        A ** x = vec 0 /\ y IN span(rows A) ==> orthogonal x y`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
  REWRITE_TAC[SET_RULE `(\y. orthogonal x y) = {y | orthogonal x y}`] THEN
  REWRITE_TAC[SUBSPACE_ORTHOGONAL_TO_VECTOR; rows; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\y:real^N. y$k`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; VEC_COMPONENT; row; dot;
               orthogonal; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let NULLSPACE_INTER_ROWSPACE = prove
 (`!A:real^M^N x:real^M. A ** x = vec 0 /\ x IN span(rows A) <=> x = vec 0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[ORTHOGONAL_NULLSPACE_ROWSPACE; ORTHOGONAL_REFL];
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; SPAN_0]]);;

let MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE = prove
 (`!A:real^M^N x y:real^M.
        x IN span(rows A) /\ y IN span(rows A) /\ A ** x = A ** y ==> x = y`,
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NULLSPACE_INTER_ROWSPACE] THEN
  ASM_SIMP_TAC[SPAN_SUB]);;

let DIM_ROWS_LE_DIM_COLUMNS = prove
 (`!A:real^M^N. dim(rows A) <= dim(columns A)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC
   (ISPEC `span(rows(A:real^M^N))` BASIS_EXISTS) THEN
  SUBGOAL_THEN `FINITE(IMAGE (\x:real^M. (A:real^M^N) ** x) b) /\
                CARD (IMAGE (\x:real^M. (A:real^M^N) ** x) b) <=
                dim(span(columns A))`
  MP_TAC THENL
   [MATCH_MP_TAC INDEPENDENT_CARD_LE_DIM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MATRIX_VECTOR_MUL_IN_COLUMNSPACE] THEN
    MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    SUBGOAL_THEN `span(b) = span(rows(A:real^M^N))` SUBST1_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE]] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_SPAN] THEN
    ASM_SIMP_TAC[SPAN_MONO];
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM) o
      GEN_REWRITE_RULE I [HAS_SIZE]) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC
     (ISPEC `A:real^M^N` MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE) THEN
    ASM SET_TAC[]]);;

let rank = new_definition
 `rank(A:real^M^N) = dim(columns A)`;;

let RANK_ROW = prove
 (`!A:real^M^N. rank(A) = dim(rows A)`,
  GEN_TAC THEN REWRITE_TAC[rank] THEN
  MP_TAC(ISPEC `A:real^M^N` DIM_ROWS_LE_DIM_COLUMNS) THEN
  MP_TAC(ISPEC `transp(A:real^M^N)` DIM_ROWS_LE_DIM_COLUMNS) THEN
  REWRITE_TAC[ROWS_TRANSP; COLUMNS_TRANSP] THEN ARITH_TAC);;

let RANK_TRANSP = prove
 (`!A:real^M^N. rank(transp A) = rank A`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [RANK_ROW] THEN
  REWRITE_TAC[rank; COLUMNS_TRANSP]);;

let MATRIX_VECTOR_MUL_BASIS = prove
 (`!A:real^M^N k. 1 <= k /\ k <= dimindex(:M)
                 ==> A ** (basis k) = column k A`,
  SIMP_TAC[CART_EQ; column; MATRIX_VECTOR_MUL_COMPONENT; DOT_BASIS;
           LAMBDA_BETA]);;

let COLUMNS_IMAGE_BASIS = prove
 (`!A:real^M^N.
     columns A = IMAGE (\x. A ** x) {basis i | 1 <= i /\ i <= dimindex(:M)}`,
  GEN_TAC THEN REWRITE_TAC[columns] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC(SET_RULE
    `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  SIMP_TAC[IN_ELIM_THM; MATRIX_VECTOR_MUL_BASIS]);;

let RANK_DIM_IM = prove
 (`!A:real^M^N. rank A = dim(IMAGE (\x. A ** x) (:real^M))`,
  GEN_TAC THEN REWRITE_TAC[rank] THEN
  MATCH_MP_TAC SPAN_EQ_DIM THEN REWRITE_TAC[COLUMNS_IMAGE_BASIS] THEN
  SIMP_TAC[SPAN_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM SPAN_SPAN] THEN
  REWRITE_TAC[SPAN_STDBASIS]);;

let DIM_EQ_SPAN = prove
 (`!s t:real^N->bool. s SUBSET t /\ dim t <= dim s ==> span s = span t`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
   (ISPEC `span s:real^N->bool` BASIS_EXISTS) THEN
  MP_TAC(ISPECL [`span t:real^N->bool`; `b:real^N->bool`]
    CARD_GE_DIM_INDEPENDENT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_REWRITE_TAC[DIM_SPAN] THEN
  ASM_MESON_TAC[SPAN_MONO; SPAN_SPAN; SUBSET_TRANS; SUBSET_ANTISYM]);;

let DIM_EQ_FULL = prove
 (`!s:real^N->bool. dim s = dimindex(:N) <=> span s = (:real^N)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN EQ_TAC THEN
  SIMP_TAC[DIM_UNIV] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_UNIV] THEN MATCH_MP_TAC DIM_EQ_SPAN THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; DIM_UNIV] THEN
  ASM_MESON_TAC[LE_REFL; DIM_SPAN]);;

let DIM_PSUBSET = prove
 (`!s t. (span s) PSUBSET (span t) ==> dim s < dim t`,
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  SIMP_TAC[PSUBSET; DIM_SUBSET; LT_LE] THEN
  MESON_TAC[EQ_IMP_LE; DIM_EQ_SPAN; SPAN_SPAN]);;

let RANK_BOUND = prove
 (`!A:real^M^N. rank(A) <= MIN (dimindex(:M)) (dimindex(:N))`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `x <= MIN a b <=> x <= a /\ x <= b`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DIM_SUBSET_UNIV; RANK_ROW];
    REWRITE_TAC[DIM_SUBSET_UNIV; rank]]);;

let FULL_RANK_INJECTIVE = prove
 (`!A:real^M^N.
        rank A = dimindex(:M) <=>
        (!x y:real^M. A ** x = A ** y ==> x = y)`,
  REWRITE_TAC[GSYM MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_SPAN_ROWS] THEN
  REWRITE_TAC[RANK_ROW; DIM_EQ_FULL]);;

let FULL_RANK_SURJECTIVE = prove
 (`!A:real^M^N.
        rank A = dimindex(:N) <=> (!y:real^N. ?x:real^M. A ** x = y)`,
  REWRITE_TAC[GSYM MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
  REWRITE_TAC[GSYM LEFT_INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  REWRITE_TAC[GSYM FULL_RANK_INJECTIVE; RANK_TRANSP]);;

let RANK_I = prove
 (`rank(mat 1:real^N^N) = dimindex(:N)`,
  REWRITE_TAC[FULL_RANK_INJECTIVE; MATRIX_VECTOR_MUL_LID]);;

let MATRIX_FULL_LINEAR_EQUATIONS = prove
 (`!A:real^M^N b:real^N.
        rank A = dimindex(:N) ==> ?x. A ** x = b`,
  SIMP_TAC[FULL_RANK_SURJECTIVE]);;

let MATRIX_NONFULL_LINEAR_EQUATIONS_EQ = prove
 (`!A:real^M^N.
        (?x. ~(x = vec 0) /\ A ** x = vec 0) <=> ~(rank A = dimindex(:M))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FULL_RANK_INJECTIVE] THEN
  SIMP_TAC[LINEAR_INJECTIVE_0; MATRIX_VECTOR_MUL_LINEAR] THEN
  MESON_TAC[]);;

let MATRIX_NONFULL_LINEAR_EQUATIONS = prove
 (`!A:real^M^N.
        ~(rank A = dimindex(:M)) ==> ?x. ~(x = vec 0) /\ A ** x = vec 0`,
  REWRITE_TAC[MATRIX_NONFULL_LINEAR_EQUATIONS_EQ]);;

let MATRIX_TRIVIAL_LINEAR_EQUATIONS = prove
 (`!A:real^M^N.
        dimindex(:N) < dimindex(:M)
        ==> ?x. ~(x = vec 0) /\ A ** x = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_NONFULL_LINEAR_EQUATIONS THEN
  MATCH_MP_TAC(ARITH_RULE
   `!a. x <= MIN b a /\ a < b ==> ~(x = b)`) THEN
  EXISTS_TAC `dimindex(:N)` THEN ASM_REWRITE_TAC[RANK_BOUND]);;

let RANK_EQ_0 = prove
 (`!A:real^M^N. rank A = 0 <=> A = mat 0`,
  REWRITE_TAC[RANK_DIM_IM; DIM_EQ_0; SUBSET; FORALL_IN_IMAGE; IN_SING;
              IN_UNIV] THEN
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN
  SIMP_TAC[CART_EQ; MATRIX_MUL_DOT; VEC_COMPONENT; LAMBDA_BETA; mat] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_DOT_EQ_0; COND_ID] THEN
  REWRITE_TAC[CART_EQ; VEC_COMPONENT]);;

let RANK_0 = prove
 (`rank(mat 0) = 0`,
  REWRITE_TAC[RANK_EQ_0]);;

let RANK_MUL_LE_RIGHT = prove
 (`!A:real^N^M B:real^P^N. rank(A ** B) <= rank(B)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `dim(IMAGE (\y. (A:real^N^M) ** y)
                        (IMAGE (\x. (B:real^P^N) ** x) (:real^P)))` THEN
  REWRITE_TAC[RANK_DIM_IM] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; MATRIX_VECTOR_MUL_ASSOC; LE_REFL];
    MATCH_MP_TAC DIM_LINEAR_IMAGE_LE THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]]);;

let RANK_MUL_LE_LEFT = prove
 (`!A:real^N^M B:real^P^N. rank(A ** B) <= rank(A)`,
  ONCE_REWRITE_TAC[GSYM RANK_TRANSP] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[RANK_MUL_LE_RIGHT]);;

let SPAN_COLUMNSPACE = prove
 (`!A:real^M^N. span(columns A) = {y | ?x. A ** x = y}`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[MATRIX_VECTOR_MUL_IN_COLUMNSPACE]] THEN
  SPEC_TAC(`y:real^N`,`y:real^N`) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[columns; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[IN] THEN
    EXISTS_TAC `basis i:real^M` THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS];
    REWRITE_TAC[subspace; IN] THEN
    MESON_TAC[MATRIX_VECTOR_MUL_RZERO; MATRIX_VECTOR_MUL_RMUL;
              MATRIX_VECTOR_MUL_ADD_LDISTRIB]]);;

let MATRIX_AUGMENTED_LINEAR_EQUATIONS = prove
 (`!A:real^N^M y:real^N.
        (?x. transp A ** x = y) <=>
        rank(pastecart A (rowvector y)) = rank A`,
  REWRITE_TAC[RANK_ROW; rows] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM numseg; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
  SIMP_TAC[GSYM ADD1; NUMSEG_REC; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[IMAGE_CLAUSES; DIM_INSERT] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `(?x. f x = y) <=> y IN {z | ?x. f x = z}`] THEN
  REWRITE_TAC[GSYM SPAN_COLUMNSPACE; COLUMNS_TRANSP] THEN
  SUBGOAL_THEN
    `IMAGE (\i. row i (pastecart (A:real^N^M) (rowvector(y:real^N))))
           (1..dimindex (:M)) =
     rows A`
  SUBST1_TAC THENL
   [REWRITE_TAC[rows] THEN MATCH_MP_TAC(SET_RULE
     `{x | P x} = s /\ (!x. x IN s ==> f x = g x)
      ==> IMAGE f s = {g x | P x}`) THEN
    SIMP_TAC[numseg; FORALL_IN_GSPEC; row; pastecart; LAMBDA_BETA; CART_EQ;
             LAMBDA_ETA; DIMINDEX_FINITE_SUM;
             ARITH_RULE `i:num <= n ==> i <= n + m`];
    REWRITE_TAC[ETA_AX; GSYM SIMPLE_IMAGE; IN_NUMSEG; GSYM rows]] THEN
  SUBGOAL_THEN
   `row (SUC(dimindex(:M))) (pastecart (A:real^N^M) (rowvector(y:real^N))) = y`
  SUBST1_TAC THENL
   [SIMP_TAC[row; pastecart; CART_EQ; LAMBDA_BETA; DIMINDEX_1; rowvector;
             DIMINDEX_FINITE_SUM; DIMINDEX_GE_1; ARITH_RULE `1 <= SUC m`;
             ARITH_RULE `1 <= m ==> SUC m <= m + 1`; LAMBDA_ETA;
             ARITH_RULE `~(SUC m <= m) /\ SUC m - m = 1`; DIMINDEX_1; ARITH];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Some bounds on components etc. relative to operator norm.                 *)
(* ------------------------------------------------------------------------- *)

let NORM_COLUMN_LE_ONORM = prove
 (`!A:real^N^M i. norm(column i A) <= onorm(\x. A ** x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[column] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$i = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPEC `\x:real^N. (A:real^N^M) ** x` ONORM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
  DISCH_THEN(MP_TAC o SPEC `basis l:real^N` o CONJUNCT1) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; NORM_BASIS; column; REAL_MUL_RID]);;

let MATRIX_COMPONENT_LE_ONORM = prove
 (`!A:real^N^M i j. abs(A$i$j) <= onorm(\x. A ** x)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(column l (A:real^N^M))` THEN
  REWRITE_TAC[NORM_COLUMN_LE_ONORM] THEN
  MP_TAC(ISPECL [`column l (A:real^N^M)`; `k:num`]
        COMPONENT_LE_NORM) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  ASM_SIMP_TAC[column; LAMBDA_BETA; REAL_LE_REFL]);;

let COMPONENT_LE_ONORM = prove
 (`!f:real^M->real^N i j. linear f ==> abs(matrix f$i$j) <= onorm f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
        [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
  REWRITE_TAC[MATRIX_COMPONENT_LE_ONORM]);;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about hyperplanes and halfspaces.                            *)
(* ------------------------------------------------------------------------- *)

let HYPERPLANE_EQ_EMPTY = prove
 (`!a:real^N b. {x | a dot x = b} = {} <=> a = vec 0 /\ ~(b = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THENL
   [MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `b / (a dot a) % a:real^N`) THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0]]);;

let HYPERPLANE_EQ_UNIV = prove
 (`!a b. {x | a dot x = b} = (:real^N) <=> a = vec 0 /\ b = &0`,
  REPEAT GEN_TAC THEN  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THENL
   [MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `(b + &1) / (a dot a) % a:real^N`) THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN REAL_ARITH_TAC]);;

let HALFSPACE_EQ_EMPTY_LT = prove
 (`!a:real^N b. {x | a dot x < b} = {} <=> a = vec 0 /\ b <= &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | p} = if p then UNIV else {}`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[UNIV_NOT_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(b - &1) / (a dot a) % a:real^N` THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN
    REAL_ARITH_TAC]);;

let HALFSPACE_EQ_EMPTY_GT = prove
 (`!a:real^N b. {x | a dot x > b} = {} <=> a = vec 0 /\ b >= &0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `--b:real`] HALFSPACE_EQ_EMPTY_LT) THEN
  SIMP_TAC[real_gt; DOT_LNEG; REAL_LT_NEG2; VECTOR_NEG_EQ_0] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let HALFSPACE_EQ_EMPTY_LE = prove
 (`!a:real^N b. {x | a dot x <= b} = {} <=> a = vec 0 /\ b < &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | p} = if p then UNIV else {}`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[UNIV_NOT_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(b - &1) / (a dot a) % a:real^N` THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN
    REAL_ARITH_TAC]);;

let HALFSPACE_EQ_EMPTY_GE = prove
 (`!a:real^N b. {x | a dot x >= b} = {} <=> a = vec 0 /\ b > &0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `--b:real`] HALFSPACE_EQ_EMPTY_LE) THEN
  SIMP_TAC[real_ge; DOT_LNEG; REAL_LE_NEG2; VECTOR_NEG_EQ_0] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A non-injective linear function maps into a hyperplane.                   *)
(* ------------------------------------------------------------------------- *)

let ADJOINT_INJECTIVE = prove
 (`!f:real^M->real^N.
        linear f
        ==> ((!x y. adjoint f x = adjoint f y ==> x = y) <=>
             (!y. ?x. f x = y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP MATRIX_WORKS o MATCH_MP
   ADJOINT_LINEAR) THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP MATRIX_WORKS) THEN
  ASM_REWRITE_TAC[GSYM FULL_RANK_INJECTIVE; GSYM FULL_RANK_SURJECTIVE] THEN
  ASM_SIMP_TAC[MATRIX_ADJOINT; RANK_TRANSP]);;

let ADJOINT_SURJECTIVE = prove
 (`!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. adjoint f x = y) <=> (!x y. f x = f y ==> x = y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [GSYM(MATCH_MP ADJOINT_ADJOINT th)]) THEN
  ASM_SIMP_TAC[ADJOINT_INJECTIVE; ADJOINT_LINEAR]);;

let ADJOINT_INJECTIVE_INJECTIVE = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x y. adjoint f x = adjoint f y ==> x = y) <=>
             (!x y. f x = f y ==> x = y))`,
  SIMP_TAC[ADJOINT_INJECTIVE] THEN
  MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE;
            LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

let ADJOINT_INJECTIVE_INJECTIVE_0 = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x. adjoint f x = vec 0 ==> x = vec 0) <=>
             (!x. f x = vec 0 ==> x = vec 0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ADJOINT_INJECTIVE_INJECTIVE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ADJOINT_LINEAR) THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_0]);;

let LINEAR_SINGULAR_INTO_HYPERPLANE = prove
 (`!f:real^N->real^N.
        linear f
        ==> (~(!x y. f(x) = f(y) ==> x = y) <=>
             ?a. ~(a = vec 0) /\ !x. a dot f(x) = &0)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
  ASM_SIMP_TAC[ADJOINT_WORKS; FORALL_DOT_EQ_0] THEN
  REWRITE_TAC[MESON[] `(?a. ~p a /\ q a) <=> ~(!a. q a ==> p a)`] THEN
  ASM_SIMP_TAC[ADJOINT_INJECTIVE_INJECTIVE_0; LINEAR_INJECTIVE_0]);;

let LINEAR_SINGULAR_IMAGE_HYPERPLANE = prove
 (`!f:real^N->real^N.
        linear f /\ ~(!x y. f(x) = f(y) ==> x = y)
        ==> ?a. ~(a = vec 0) /\ !s. IMAGE f s SUBSET {x | a dot x = &0}`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[LINEAR_SINGULAR_INTO_HYPERPLANE] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let LOWDIM_EXPAND_DIMENSION = prove
 (`!s:real^N->bool n.
        dim s <= n /\ n <= dimindex(:N)
        ==> ?t. dim(t) = n /\ span s SUBSET span t`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV) [LE_EXISTS] THEN
  SIMP_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  INDUCT_TAC THENL [MESON_TAC[ADD_CLAUSES; SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `s + SUC d <= n <=> s + d < n`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[LT_IMP_LE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `~(span t = (:real^N))` MP_TAC THENL
   [REWRITE_TAC[GSYM DIM_EQ_FULL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `(a:real^N) INSERT t` THEN ASM_REWRITE_TAC[DIM_INSERT; ADD1] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `span(t:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC[]);;

let LOWDIM_EXPAND_BASIS = prove
 (`!s:real^N->bool n.
        dim s <= n /\ n <= dimindex(:N)
        ==> ?b. b HAS_SIZE n /\ independent b /\ span s SUBSET span b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC o
    MATCH_MP LOWDIM_EXPAND_DIMENSION) THEN
  MP_TAC(ISPEC `t:real^N->bool` BASIS_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SPAN_SPAN; SUBSET_TRANS; SPAN_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Orthogonal bases, Gram-Schmidt process, and related theorems.             *)
(* ------------------------------------------------------------------------- *)

let SPAN_DELETE_0 = prove
 (`!s:real^N->bool. span(s DELETE vec 0) = span s`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[DELETE_SUBSET; SPAN_MONO] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `span((vec 0:real^N) INSERT (s DELETE vec 0))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
    SIMP_TAC[SUBSET; SPAN_BREAKDOWN_EQ; VECTOR_MUL_RZERO; VECTOR_SUB_RZERO]]);;

let SPAN_IMAGE_SCALE = prove
 (`!c s. FINITE s /\ (!x. x IN s ==> ~(c x = &0))
         ==> span (IMAGE (\x:real^N. c(x) % x) s) = span s`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; SPAN_BREAKDOWN_EQ; EXTENSION; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^N->bool`] THEN
  STRIP_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
  EXISTS_TAC `k / (c:real^N->real) x` THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL]);;

let PAIRWISE_ORTHOGONAL_INDEPENDENT = prove
 (`!s:real^N->bool.
        pairwise orthogonal s /\ ~(vec 0 IN s) ==> independent s`,
  REWRITE_TAC[pairwise; orthogonal] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[independent; dependent] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[SPAN_EXPLICIT; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
  REWRITE_TAC[SUBSET; IN_DELETE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:real^N. a dot x`) THEN
  ASM_SIMP_TAC[DOT_RSUM; DOT_RMUL; REAL_MUL_RZERO; SUM_0] THEN
  ASM_MESON_TAC[DOT_EQ_0]);;

let PAIRWISE_ORTHOGONAL_IMP_FINITE = prove
 (`!s:real^N->bool. pairwise orthogonal s ==> FINITE s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `independent (s DELETE (vec 0:real^N))` MP_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC PAIRWISE_MONO THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[SUBSET; IN_DELETE];
    DISCH_THEN(MP_TAC o MATCH_MP INDEPENDENT_IMP_FINITE) THEN
    REWRITE_TAC[FINITE_DELETE]]);;

let GRAM_SCHMIDT_STEP = prove
 (`!s a x.
        pairwise orthogonal s /\ x IN span s
        ==> orthogonal x (a - vsum s (\b:real^N. (b dot a) / (b dot b) % b))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ORTHOGONAL_SYM] ORTHOGONAL_TO_SPAN_EQ] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `x:real^N`] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
  REWRITE_TAC[orthogonal; DOT_RSUB] THEN ASM_SIMP_TAC[DOT_RSUM] THEN
  REWRITE_TAC[REAL_SUB_0; DOT_RMUL] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum s (\y:real^N. if y = x then y dot a else &0)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[SUM_DELTA; DOT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pairwise; orthogonal]) THEN
  ASM_CASES_TAC `x:real^N = y` THEN ASM_SIMP_TAC[DOT_LMUL; REAL_MUL_RZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; DOT_EQ_0; DOT_LZERO; REAL_MUL_RZERO]);;

let ORTHOGONAL_EXTENSION = prove
 (`!s t:real^N->bool.
        pairwise orthogonal s
        ==> ?u. pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)`,
  let lemma = prove
   (`!t s:real^N->bool.
        FINITE t /\ FINITE s /\ pairwise orthogonal s
        ==> ?u. pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)`,
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC `{}:real^N->bool` THEN
      ASM_REWRITE_TAC[UNION_EMPTY];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `t:real^N->bool`] THEN
    REWRITE_TAC[pairwise; orthogonal] THEN REPEAT STRIP_TAC THEN
    ABBREV_TAC `a' = a - vsum s (\b:real^N. (b dot a) / (b dot b) % b)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(a':real^N) INSERT s`) THEN
    ASM_REWRITE_TAC[FINITE_INSERT] THEN ANTS_TAC THENL
     [SUBGOAL_THEN `!x:real^N. x IN s ==> a' dot x = &0`
       (fun th -> REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[DOT_SYM; th]) THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "a'" THEN
      REWRITE_TAC[GSYM orthogonal] THEN ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
      MATCH_MP_TAC GRAM_SCHMIDT_STEP THEN
      ASM_SIMP_TAC[pairwise; orthogonal; SPAN_CLAUSES];
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(a':real^N) INSERT u` THEN
      ASM_REWRITE_TAC[SET_RULE `s UNION a INSERT u = a INSERT s UNION u`] THEN
      REWRITE_TAC[SET_RULE `(x INSERT s) UNION t = x INSERT (s UNION t)`] THEN
      MATCH_MP_TAC EQ_SPAN_INSERT_EQ THEN EXPAND_TAC "a'" THEN
      REWRITE_TAC[VECTOR_ARITH `a - x - a:real^N = --x`] THEN
      MATCH_MP_TAC SPAN_NEG THEN MATCH_MP_TAC SPAN_VSUM THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SPAN_MUL THEN ASM_SIMP_TAC[SPAN_SUPERSET; IN_UNION]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `span t:real^N->bool` BASIS_SUBSPACE_EXISTS) THEN
  REWRITE_TAC[SUBSPACE_SPAN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `s:real^N->bool`] lemma) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[HAS_SIZE; PAIRWISE_ORTHOGONAL_IMP_FINITE];
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SPAN_UNION]]);;

let ORTHOGONAL_EXTENSION_STRONG = prove
 (`!s t:real^N->bool.
        pairwise orthogonal s
        ==> ?u. DISJOINT u (vec 0 INSERT s) /\
                pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
    SPEC `t:real^N->bool` o MATCH_MP ORTHOGONAL_EXTENSION) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u DIFF ((vec 0:real^N) INSERT s)` THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        PAIRWISE_MONO)) THEN SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC BINOP_CONV [GSYM SPAN_DELETE_0] THEN
    AP_TERM_TAC THEN SET_TAC[]]);;

let ORTHONORMAL_EXTENSION = prove
 (`!s t:real^N->bool.
        pairwise orthogonal s /\ (!x. x IN s ==> norm x = &1)
        ==> ?u. DISJOINT u s /\
                pairwise orthogonal (s UNION u) /\
                (!x. x IN u ==> norm x = &1) /\
                span(s UNION u) = span(s UNION t)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
    SPEC `t:real^N->bool` o MATCH_MP ORTHOGONAL_EXTENSION_STRONG) THEN
  REWRITE_TAC[SET_RULE `DISJOINT u s <=> !x. x IN u ==> ~(x IN s)`] THEN
  REWRITE_TAC[IN_INSERT; DE_MORGAN_THM; pairwise] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. inv(norm x) % x) u` THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(x:real^N) = &1` THEN
    ASM_SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `inv(norm x) % x:real^N`]) THEN
    ASM_REWRITE_TAC[IN_UNION; VECTOR_MUL_EQ_0; REAL_SUB_0; REAL_INV_EQ_1;
      VECTOR_ARITH `x:real^N = a % x <=> (a - &1) % x = vec 0`] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL
     [ASM_MESON_TAC[VECTOR_MUL_RZERO];
      ASM_REWRITE_TAC[orthogonal; DOT_RMUL; REAL_ENTIRE; DOT_EQ_0] THEN
      ASM_REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0]];
    REWRITE_TAC[IN_UNION; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[orthogonal; DOT_LMUL; DOT_RMUL; REAL_ENTIRE; DOT_EQ_0;
                 REAL_INV_EQ_0; NORM_EQ_0] THEN
    REWRITE_TAC[GSYM orthogonal] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_UNION] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[NORM_MUL; REAL_MUL_LINV; NORM_EQ_0; REAL_ABS_INV;
                 REAL_ABS_NORM];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SPAN_EQ; UNION_SUBSET] THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; SPAN_SUPERSET; SPAN_MUL; IN_UNION] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x:real^N = norm(x) % inv(norm x) % x`
     (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
    THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
      MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN ASM_MESON_TAC[]]]);;

let VECTOR_IN_ORTHOGONAL_SPANNINGSET = prove
 (`!a. ?s. a IN s /\ pairwise orthogonal s /\ span s = (:real^N)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`{a:real^N}`; `(IMAGE basis (1..dimindex(:N))):real^N->bool`]
                 ORTHOGONAL_EXTENSION) THEN
  REWRITE_TAC[PAIRWISE_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{a:real^N} UNION u` THEN ASM_REWRITE_TAC[IN_UNION; IN_SING] THEN
  MATCH_MP_TAC(SET_RULE `!s. s = UNIV /\ s SUBSET t ==> t = UNIV`) THEN
  EXISTS_TAC `span {basis i:real^N | 1 <= i /\ i <= dimindex (:N)}` THEN
  CONJ_TAC THENL [REWRITE_TAC[SPAN_STDBASIS]; MATCH_MP_TAC SPAN_MONO] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; GSYM IN_NUMSEG] THEN SET_TAC[]);;

let VECTOR_IN_ORTHOGONAL_BASIS = prove
 (`!a. ~(a = vec 0)
       ==> ?s. a IN s /\ ~(vec 0 IN s) /\
               pairwise orthogonal s /\
               independent s /\
               s HAS_SIZE (dimindex(:N)) /\
               span s = (:real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:real^N` VECTOR_IN_ORTHOGONAL_SPANNINGSET) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s DELETE (vec 0:real^N)` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; IN_DELETE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_SIMP_TAC[IN_DELETE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SPAN_DELETE_0];
    DISCH_TAC THEN ASM_SIMP_TAC[BASIS_HAS_SIZE_UNIV]]);;

let VECTOR_IN_ORTHONORMAL_BASIS = prove
 (`!a. norm a = &1
       ==> ?s. a IN s /\
               pairwise orthogonal s /\
               (!x. x IN s ==> norm x = &1) /\
               independent s /\
               s HAS_SIZE (dimindex(:N)) /\
               span s = (:real^N)`,
  GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP VECTOR_IN_ORTHOGONAL_BASIS) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. inv(norm x) % x) s` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_MESON_TAC[ORTHOGONAL_CLAUSES];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_MESON_TAC[REAL_MUL_LINV; NORM_EQ_0];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[BASIS_HAS_SIZE_UNIV]] THEN
  UNDISCH_THEN `span s = (:real^N)` (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SPAN_IMAGE_SCALE THEN
  REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0] THEN
  ASM_MESON_TAC[HAS_SIZE]);;

let BESSEL_INEQUALITY = prove
 (`!s x:real^N.
        pairwise orthogonal s /\ (!x. x IN s ==> norm x = &1)
        ==> sum s (\e. (e dot x) pow 2) <= norm(x) pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
  MP_TAC(ISPEC `x - vsum s (\e. (e dot x) % e):real^N` DOT_POS_LE) THEN
  REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
   `(a - b:real^N) dot (a - b) = a dot a + b dot b - &2 * b dot a`] THEN
  ASM_SIMP_TAC[DOT_LSUM; REAL_POW_2; DOT_LMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `t = s ==> &0 <= x + t - &2 * s ==> s <= x`) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `e:real^N` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[DOT_RSUM] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum s (\k:real^N. if k = e then e dot x else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[SUM_DELTA]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[DOT_RMUL] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[REAL_RING `a * x = a <=> a = &0 \/ x = &1`] THEN
    DISJ2_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N`) THEN
    ASM_REWRITE_TAC[NORM_EQ_SQUARE] THEN REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise; orthogonal]) THEN
    ASM_SIMP_TAC[REAL_ENTIRE]]);;

(* ------------------------------------------------------------------------- *)
(* Analogous theorems for existence of orthonormal basis for a subspace.     *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_SPANNINGSET_SUBSPACE = prove
 (`!s:real^N->bool.
        subspace s
        ==> ?b. b SUBSET s /\ pairwise orthogonal b /\ span b = s`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL[`{}:real^N->bool`; `b:real^N->bool`] ORTHOGONAL_EXTENSION) THEN
  REWRITE_TAC[PAIRWISE_EMPTY; UNION_EMPTY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSPACE THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[SPAN_INC]]);;

let ORTHOGONAL_BASIS_SUBSPACE = prove
 (`!s:real^N->bool.
        subspace s
        ==> ?b. ~(vec 0 IN b) /\
                b SUBSET s /\
                pairwise orthogonal b /\
                independent b /\
                b HAS_SIZE (dim s) /\
                span b = s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_SPANNINGSET_SUBSPACE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b DELETE (vec 0:real^N)` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; IN_DELETE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_SIMP_TAC[IN_DELETE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SPAN_DELETE_0];
    DISCH_TAC THEN ASM_SIMP_TAC[BASIS_HAS_SIZE_DIM]]);;

let ORTHONORMAL_BASIS_SUBSPACE = prove
 (`!s:real^N->bool.
        subspace s
        ==> ?b. b SUBSET s /\
                pairwise orthogonal b /\
                (!x. x IN b ==> norm x = &1) /\
                independent b /\
                b HAS_SIZE (dim s) /\
                span b = s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_BASIS_SUBSPACE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. inv(norm x) % x) b` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[SPAN_MUL; SPAN_INC; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_MESON_TAC[ORTHOGONAL_CLAUSES];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_MESON_TAC[REAL_MUL_LINV; NORM_EQ_0];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[BASIS_HAS_SIZE_DIM]] THEN
  UNDISCH_THEN `span b = (s:real^N->bool)` (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SPAN_IMAGE_SCALE THEN
  REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0] THEN
  ASM_MESON_TAC[HAS_SIZE]);;

let ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN = prove
 (`!s t:real^N->bool.
        span s PSUBSET span t
        ==> ?x. ~(x = vec 0) /\ x IN span t /\
                (!y. y IN span s ==> orthogonal x y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `span s:real^N->bool` ORTHOGONAL_BASIS_SUBSPACE) THEN
  REWRITE_TAC[SUBSPACE_SPAN] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `{u:real^N}`] ORTHOGONAL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:real^N->bool` MP_TAC) THEN
  ASM_CASES_TAC `ns SUBSET (vec 0:real^N) INSERT b` THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(IN) (u:real^N)` o CONJUNCT2) THEN
    SIMP_TAC[SPAN_SUPERSET; IN_UNION; IN_SING] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    SUBGOAL_THEN `~(u IN span (b UNION {vec 0:real^N}))` MP_TAC THENL
     [ASM_REWRITE_TAC[SET_RULE `s UNION {a} = a INSERT s`; SPAN_INSERT_0];
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
      MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `~(s SUBSET t) ==> ?z. z IN s /\ ~(z IN t)`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_INSERT; DE_MORGAN_THM] THEN
  X_GEN_TAC `n:real^N` THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `n:real^N`) THEN ASM_REWRITE_TAC[IN_UNION] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN EXISTS_TAC `n:real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(n:real^N) IN span (b UNION ns)` MP_TAC THENL
     [MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN SPEC_TAC(`n:real^N`,`n:real^N`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN REWRITE_TAC[SUBSPACE_SPAN] THEN
      ASM_REWRITE_TAC[SET_RULE
       `s UNION {a} SUBSET t <=> s SUBSET t /\ a IN t`] THEN
      ASM_MESON_TAC[SPAN_INC; SUBSET_TRANS]];
    MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC[SET_RULE `(\y. orthogonal n y) = {y | orthogonal n y}`] THEN
    REWRITE_TAC[SUBSPACE_ORTHOGONAL_TO_VECTOR] THEN ASM SET_TAC[]]);;

let ORTHOGONAL_TO_SUBSPACE_EXISTS = prove
 (`!s:real^N->bool. dim s < dimindex(:N)
                    ==> ?x. ~(x = vec 0) /\ !y. y IN s ==> orthogonal x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(:real^N)`]
        ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN) THEN
  ANTS_TAC THENL [REWRITE_TAC[PSUBSET]; MESON_TAC[SPAN_SUPERSET]] THEN
  REWRITE_TAC[SPAN_UNIV; SUBSET_UNIV] THEN
  ASM_MESON_TAC[DIM_SPAN; DIM_UNIV; LT_REFL]);;

let ORTHOGONAL_TO_VECTOR_EXISTS = prove
 (`!x:real^N. 2 <= dimindex(:N) ==> ?y. ~(y = vec 0) /\ orthogonal x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{x:real^N}` ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
  SIMP_TAC[DIM_SING; IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; MESON_TAC[ORTHOGONAL_SYM]]);;

let SPAN_NOT_UNIV_ORTHOGONAL = prove
 (`!s. ~(span s = (:real^N))
         ==> ?a. ~(a = vec 0) /\ !x. x IN span s ==> a dot x = &0`,
  REWRITE_TAC[GSYM DIM_EQ_FULL; GSYM LE_ANTISYM; DIM_SUBSET_UNIV;
              NOT_LE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM orthogonal] THEN
  MATCH_MP_TAC ORTHOGONAL_TO_SUBSPACE_EXISTS THEN ASM_REWRITE_TAC[DIM_SPAN]);;

let SPAN_NOT_UNIV_SUBSET_HYPERPLANE = prove
 (`!s. ~(span s = (:real^N))
       ==> ?a. ~(a = vec 0) /\ span s SUBSET {x | a dot x = &0}`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; SPAN_NOT_UNIV_ORTHOGONAL]);;

let LOWDIM_SUBSET_HYPERPLANE = prove
 (`!s. dim s < dimindex(:N)
       ==> ?a:real^N. ~(a = vec 0) /\ span s SUBSET {x | a dot x = &0}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_NOT_UNIV_SUBSET_HYPERPLANE THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIM_SUBSET) THEN
  ASM_REWRITE_TAC[NOT_LE; DIM_SPAN; DIM_UNIV]);;

let VECTOR_EQ_DOT_SPAN = prove
 (`!b x y:real^N.
        (!v. v IN b ==> v dot x = v dot y) /\ x IN span b /\ y IN span b
        ==> x = y`,
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0; GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM DOT_RSUB; GSYM ORTHOGONAL_REFL; GSYM orthogonal] THEN
  MESON_TAC[ORTHOGONAL_TO_SPAN; SPAN_SUB; ORTHOGONAL_SYM]);;

let ORTHONORMAL_BASIS_EXPAND = prove
 (`!b x:real^N.
        pairwise orthogonal b /\ (!v. v IN b ==> norm v = &1) /\ x IN span b
   ==> vsum b (\v. (v dot x) % v) = x`,
  REWRITE_TAC[NORM_EQ_1] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_EQ_DOT_SPAN THEN EXISTS_TAC `b:real^N->bool` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pairwise; orthogonal]) THEN
  ASM_SIMP_TAC[SPAN_VSUM; SPAN_MUL; DOT_RSUM; DOT_RMUL; SPAN_SUPERSET] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `sum b (\w:real^N. if w = v then v dot x else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[SUM_DELTA]] THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_RID; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Decomposing a vector into parts in orthogonal subspaces.                  *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE = prove
 (`!s t x y x' y':real^N.
        (!a b. a IN s /\ b IN t ==> orthogonal a b) /\
        x IN span s /\ x' IN span s /\ y IN span t /\ y' IN span t /\
        x + y = x' + y'
        ==> x = x' /\ y = y'`,
  REWRITE_TAC[VECTOR_ARITH `x + y:real^N = x' + y' <=> x - x' = y' - y`] THEN
  ONCE_REWRITE_TAC[GSYM ORTHOGONAL_TO_SPANS_EQ] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[VECTOR_ARITH
   `x:real^N = x' /\ y:real^N = y' <=> x - x' = vec 0 /\ y' - y = vec 0`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM ORTHOGONAL_REFL] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  ASM_MESON_TAC[ORTHOGONAL_CLAUSES; ORTHOGONAL_SYM]);;

let ORTHOGONAL_SUBSPACE_DECOMP_EXISTS = prove
 (`!s x:real^N. ?y z. y IN span s /\ (!w. w IN span s ==> orthogonal z w) /\
                      x = y + z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `span s:real^N->bool` ORTHOGONAL_BASIS_SUBSPACE) THEN
  REWRITE_TAC[SUBSPACE_SPAN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `vsum t (\b:real^N. (b dot x) / (b dot b) % b)` THEN
  EXISTS_TAC `x - vsum t (\b:real^N. (b dot x) / (b dot b) % b)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_VSUM THEN
    ASM_SIMP_TAC[INDEPENDENT_IMP_FINITE; SPAN_CLAUSES];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
    MATCH_MP_TAC GRAM_SCHMIDT_STEP THEN ASM_SIMP_TAC[];
    VECTOR_ARITH_TAC]);;

let ORTHOGONAL_SUBSPACE_DECOMP = prove
 (`!s x. ?!(y,z). y IN span s /\
                  z IN {z:real^N | !x. x IN span s ==> orthogonal z x} /\
                  x = y + z`,
  REWRITE_TAC[EXISTS_UNIQUE_DEF; IN_ELIM_THM] THEN
  REWRITE_TAC[EXISTS_PAIRED_THM; FORALL_PAIRED_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; ORTHOGONAL_SUBSPACE_DECOMP_EXISTS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  MATCH_MP_TAC ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`s:real^N->bool`; `{z:real^N | !x. x IN span s ==> orthogonal z x}`] THEN
  ASM_SIMP_TAC[SPAN_CLAUSES; IN_ELIM_THM] THEN
  ASM_MESON_TAC[SPAN_CLAUSES; ORTHOGONAL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Existence of isometry between subspaces of same dimension.                *)
(* ------------------------------------------------------------------------- *)

let ISOMETRY_SUBSET_SUBSPACE = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s <= dim t
        ==> ?f. linear f /\ IMAGE f s SUBSET t /\
                (!x. x IN s ==> norm(f x) = norm(x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^N->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  MP_TAC(ISPEC `s:real^M->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^M->bool`; `c:real^N->bool`] CARD_LE_INJ) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; INJECTIVE_ON_ALT] THEN
  X_GEN_TAC `fb:real^M->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fb:real^M->real^N`; `b:real^M->bool`]
    LINEAR_INDEPENDENT_EXTEND) THEN
  ASM_REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM; INJECTIVE_ON_ALT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `span b:real^M->bool = s`)] THEN
    ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC[];
    UNDISCH_THEN `span b:real^M->bool = s` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SPAN_FINITE] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real^M`; `u:real^M->real`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LINEAR_VSUM] THEN
    REWRITE_TAC[o_DEF; NORM_EQ_SQUARE; NORM_POS_LE; GSYM NORM_POW_2] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[ORTHOGONAL_MUL] THEN ASM SET_TAC[];
      REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC[NORM_MUL] THEN
      MATCH_MP_TAC SUM_EQ THEN ASM SET_TAC[]]]);;

let ISOMETRIES_SUBSPACES = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f g. linear f /\ linear g /\
                  IMAGE f s = t /\ IMAGE g t = s /\
                  (!x. x IN s ==> norm(f x) = norm x) /\
                  (!y. y IN t ==> norm(g y) = norm y) /\
                  (!x. x IN s ==> g(f x) = x) /\
                  (!y. y IN t ==> f(g y) = y)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `n = dim(t:real^N->bool)` THEN
  MP_TAC(ISPEC `t:real^N->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  MP_TAC(ISPEC `s:real^M->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^M->bool`; `c:real^N->bool`] CARD_EQ_BIJECTIONS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`fb:real^M->real^N`; `gb:real^N->real^M`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`gb:real^N->real^M`; `c:real^N->bool`]
    LINEAR_INDEPENDENT_EXTEND) THEN
  MP_TAC(ISPECL [`fb:real^M->real^N`; `b:real^M->bool`]
    LINEAR_INDEPENDENT_EXTEND) THEN
  ASM_REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `span b:real^M->bool = s`)] THEN
    ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SYM(ASSUME `span b:real^M->bool = s`)] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    UNDISCH_THEN `span b:real^M->bool = s` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SPAN_FINITE] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real^M`; `u:real^M->real`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LINEAR_VSUM] THEN
    REWRITE_TAC[o_DEF; NORM_EQ_SQUARE; NORM_POS_LE; GSYM NORM_POW_2] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[ORTHOGONAL_MUL] THEN ASM SET_TAC[];
      REPEAT(DISCH_THEN SUBST1_TAC) THEN
      ASM_SIMP_TAC[NORM_MUL]];
    UNDISCH_THEN `span c:real^N->bool = t` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SPAN_FINITE] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `u:real^N->real`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LINEAR_VSUM] THEN
    REWRITE_TAC[o_DEF; NORM_EQ_SQUARE; NORM_POS_LE; GSYM NORM_POW_2] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[ORTHOGONAL_MUL] THEN ASM SET_TAC[];
      REPEAT(DISCH_THEN SUBST1_TAC) THEN
      ASM_SIMP_TAC[NORM_MUL]];
    REWRITE_TAC[SYM(ASSUME `span b:real^M->bool = s`)] THEN
    MATCH_MP_TAC SPAN_INDUCT THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; IN]; ALL_TAC] THEN
    REWRITE_TAC[subspace; IN] THEN ASM_MESON_TAC[linear; LINEAR_0];
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    MATCH_MP_TAC SPAN_INDUCT THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; IN]; ALL_TAC] THEN
    REWRITE_TAC[subspace; IN] THEN ASM_MESON_TAC[linear; LINEAR_0]]);;

let ISOMETRY_SUBSPACES = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f:real^M->real^N. linear f /\ IMAGE f s = t /\
                               (!x. x IN s ==> norm(f x) = norm(x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMETRIES_SUBSPACES) THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

let ISOMETRY_UNIV_SUBSPACE = prove
 (`!s. subspace s /\ dimindex(:M) = dim s
       ==> ?f:real^M->real^N.
                linear f /\ IMAGE f (:real^M) = s /\
                (!x. norm(f x) = norm(x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `s:real^N->bool`] ISOMETRY_SUBSPACES) THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; IN_UNIV; DIM_UNIV]);;

let ISOMETRY_UNIV_SUPERSET_SUBSPACE = prove
 (`!s. subspace s /\ dim s <= dimindex(:M) /\ dimindex(:M) <= dimindex(:N)
       ==> ?f:real^M->real^N.
                linear f /\ s SUBSET (IMAGE f (:real^M)) /\
                (!x. norm(f x) = norm(x))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOWDIM_EXPAND_DIMENSION) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(:real^M)`; `span t:real^N->bool`] ISOMETRY_SUBSPACES) THEN
  ASM_REWRITE_TAC[SUBSPACE_SPAN; SUBSPACE_UNIV; DIM_UNIV; DIM_SPAN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[IN_UNIV] THEN
  ASM_MESON_TAC[SUBSET; SPAN_INC]);;

let ISOMETRY_UNIV_UNIV = prove
 (`dimindex(:M) <= dimindex(:N)
   ==> ?f:real^M->real^N. linear f /\ (!x. norm(f x) = norm(x))`,
  DISCH_TAC THEN
  MP_TAC(ISPEC `{vec 0:real^N}`ISOMETRY_UNIV_SUPERSET_SUBSPACE) THEN
  ASM_REWRITE_TAC[SUBSPACE_TRIVIAL] THEN
  ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC(ARITH_RULE `x = 0 /\ 1 <= y ==> x <= y`) THEN
  ASM_REWRITE_TAC[DIM_EQ_0; DIMINDEX_GE_1] THEN SET_TAC[]);;

let SUBSPACE_ISOMORPHISM = prove
 (`!s t. subspace s /\ subspace t /\ dim(s) = dim(t)
         ==> ?f:real^M->real^N.
                linear f /\ (IMAGE f s = t) /\
                (!x y. x IN s /\ y IN s /\ f x = f y ==> (x = y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISOMETRY_SUBSPACES) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[LINEAR_INJECTIVE_0_SUBSPACE] THEN MESON_TAC[NORM_EQ_0]);;

let ISOMORPHISMS_UNIV_UNIV = prove
 (`dimindex(:M) = dimindex(:N)
   ==> ?f:real^M->real^N g.
            linear f /\ linear g /\
            (!x. norm(f x) = norm x) /\ (!y. norm(g y) = norm y) /\
            (!x. g(f x) = x) /\ (!y. f(g y) = y)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(\x. lambda i. x$i):real^M->real^N` THEN
  EXISTS_TAC `(\x. lambda i. x$i):real^N->real^M` THEN
  SIMP_TAC[vector_norm; dot; LAMBDA_BETA] THEN
  SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           LAMBDA_BETA] THEN
  FIRST_ASSUM SUBST1_TAC THEN SIMP_TAC[LAMBDA_BETA] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN SIMP_TAC[LAMBDA_BETA]);;

(* ------------------------------------------------------------------------- *)
(* Properties of special hyperplanes.                                        *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_HYPERPLANE = prove
 (`!a. subspace {x:real^N | a dot x = &0}`,
  SIMP_TAC[subspace; DOT_RADD; DOT_RMUL; IN_ELIM_THM; REAL_ADD_LID;
           REAL_MUL_RZERO; DOT_RZERO]);;

let SUBSPACE_SPECIAL_HYPERPLANE = prove
 (`!k. subspace {x:real^N | x$k = &0}`,
  SIMP_TAC[subspace; IN_ELIM_THM; VEC_COMPONENT;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let SPECIAL_HYPERPLANE_SPAN = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> {x:real^N | x$k = &0} =
           span(IMAGE basis ((1..dimindex(:N)) DELETE k))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SPAN_SUBSPACE THEN
  ASM_SIMP_TAC[SUBSPACE_SPECIAL_HYPERPLANE] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; IN_DELETE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    SIMP_TAC[SPAN_FINITE; FINITE_IMAGE; FINITE_DELETE; FINITE_NUMSEG] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `\v:real^N. x dot v` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_NUMSEG; IN_DELETE] THEN
      MESON_TAC[BASIS_INJ];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
      ASM_SIMP_TAC[VSUM_DELETE; FINITE_NUMSEG; IN_NUMSEG; DOT_BASIS] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO]]]);;

let DIM_SPECIAL_HYPERPLANE = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> dim {x:real^N | x$k = &0} = dimindex(:N) - 1`,
  SIMP_TAC[SPECIAL_HYPERPLANE_SPAN] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `IMAGE (basis:num->real^N) ((1..dimindex(:N)) DELETE k)` THEN
  REWRITE_TAC[SUBSET_REFL; SPAN_INC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INDEPENDENT_MONO THEN
    EXISTS_TAC `{basis i:real^N | 1 <= i /\ i <= dimindex(:N)}` THEN
    REWRITE_TAC[INDEPENDENT_STDBASIS; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_DELETE; IN_NUMSEG; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_NUMSEG; IN_DELETE] THEN
      MESON_TAC[BASIS_INJ];
      ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; FINITE_NUMSEG; CARD_DELETE;
                   FINITE_IMAGE; IN_NUMSEG; CARD_NUMSEG_1]]]);;

let LOWDIM_EQ_INTER_HYPERPLANE = prove
 (`!s t:real^N->bool.
        subspace s /\ subspace t /\ t SUBSET s /\ dim t + 1 = dim s
        ==> ?a. ~(a = vec 0) /\ {x | a dot x = &0} INTER s = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^N->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `s:real^N->bool`]
        ORTHONORMAL_EXTENSION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
  SUBGOAL_THEN `span(b UNION s):real^N->bool = s` SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `span(s:real^N->bool)` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM SET_TAC[]; ASM_MESON_TAC[SPAN_OF_SUBSPACE]];
    STRIP_TAC] THEN
  UNDISCH_TAC `dim(t:real^N->bool) + 1 = dim(s:real^N->bool)` THEN
  MAP_EVERY EXPAND_TAC ["s"; "t"] THEN REWRITE_TAC[DIM_SPAN] THEN
  SUBGOAL_THEN `~((vec 0:real^N) IN b UNION c)` MP_TAC THENL
   [ASM_MESON_TAC[IN_UNION; NORM_ARITH `~(norm(vec 0:real^N) = &1)`];
    ASM_SIMP_TAC[DIM_EQ_CARD; PAIRWISE_ORTHOGONAL_INDEPENDENT; IN_UNION;
                 DE_MORGAN_THM]] THEN
  SUBGOAL_THEN `FINITE(b UNION c:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[PAIRWISE_ORTHOGONAL_IMP_FINITE];
    ASM_SIMP_TAC[FINITE_UNION; CARD_UNION;
                 GSYM(ONCE_REWRITE_RULE[INTER_COMM] DISJOINT)]] THEN
  STRIP_TAC THEN STRIP_TAC THEN REWRITE_TAC[EQ_ADD_LCANCEL] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(HAS_SIZE_CONV `(c:real^N->bool) HAS_SIZE 1`) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:real^N` THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_SING]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `t SUBSET s /\
    (!x. x IN t ==> x IN h) /\
    (!x. x IN s /\ ~(x IN t) ==> ~(x IN h))
    ==> h INTER s = t`) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; GSYM orthogonal] THEN
    MATCH_MP_TAC ORTHOGONAL_TO_SPAN THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [SET_RULE `s UNION {a} = a INSERT s`]) THEN
    REWRITE_TAC[PAIRWISE_INSERT] THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[SPAN_BREAKDOWN_EQ; SET_RULE `s UNION {a} = a INSERT s`] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `c:real`] THEN
  ASM_CASES_TAC `c = &0` THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO; IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `a dot (x - c % a:real^N) = &0` MP_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[DOT_RSUB; DOT_RMUL]] THEN
  ASM_SIMP_TAC[REAL_SUB_0; REAL_ENTIRE; DOT_EQ_0]);;

let LOWDIM_EQ_HYPERPLANE = prove
 (`!s. dim s = dimindex(:N) - 1
       ==> ?a:real^N. ~(a = vec 0) /\ span s = {x | a dot x = &0}`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`(:real^N)`; `span s:real^N->bool`] LOWDIM_EQ_INTER_HYPERPLANE) THEN
  ASM_REWRITE_TAC[SUBSPACE_SPAN; SUBSPACE_UNIV; SUBSET_UNIV; INTER_UNIV] THEN
  ASM_SIMP_TAC[DIM_SPAN; SUB_ADD; DIMINDEX_GE_1; DIM_UNIV] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More theorems about dimensions of different subspaces.                    *)
(* ------------------------------------------------------------------------- *)

let DIM_IMAGE_KERNEL_GEN = prove
 (`!f:real^M->real^N s.
        linear f /\ subspace s
        ==> dim(IMAGE f s) + dim {x | x IN s /\  f x = vec 0} = dim(s)`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPEC `{x | x IN s /\ (f:real^M->real^N) x = vec 0}` BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^M->bool`; `s:real^M->bool`]
    MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `span(w:real^M->bool) = s`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th] THEN
              ASSUME_TAC th)
  THENL [ASM_SIMP_TAC[SPAN_SUBSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `subspace {x | x IN s /\ (f:real^M->real^N) x = vec 0}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
    ASM_SIMP_TAC[SUBSPACE_INTER; SUBSPACE_KERNEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x = vec 0} = span v`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_ANTISYM; SPAN_SUBSET_SUBSPACE; SUBSPACE_KERNEL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIM_SPAN; DIM_EQ_CARD] THEN
  SUBGOAL_THEN
   `!x. x IN span(w DIFF v) /\ (f:real^M->real^N) x = vec 0 ==> x = vec 0`
  (LABEL_TAC "*") THENL
   [MATCH_MP_TAC(SET_RULE
     `!t. s SUBSET t /\ (!x. x IN s /\ x IN t /\ P x ==> Q x)
          ==> (!x. x IN s /\ P x ==> Q x)`) THEN
    EXISTS_TAC `s:real^M->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SPAN_MONO; SUBSET_DIFF]; ALL_TAC] THEN
    ASM_SIMP_TAC[SPAN_FINITE; IN_ELIM_THM; IMP_CONJ; FINITE_DIFF;
                 INDEPENDENT_IMP_FINITE; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN X_GEN_TAC `u:real^M->real` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMP_IMP] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `y IN s /\ f y = a <=> y IN {x | x IN s /\ f x = a}`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SPAN_FINITE; INDEPENDENT_IMP_FINITE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `t:real^M->real`) THEN
    MP_TAC(ISPEC `w:real^M->bool` INDEPENDENT_EXPLICIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC
     `(\x. if x IN w DIFF v then --u x else t x):real^M->real`) THEN
    ASM_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[VSUM_CASES; INDEPENDENT_IMP_FINITE] THEN
    REWRITE_TAC[SET_RULE `{x | x IN w /\ x IN (w DIFF v)} = w DIFF v`] THEN
    SIMP_TAC[ASSUME `(v:real^M->bool) SUBSET w`; SET_RULE
     `v SUBSET w ==> {x | x IN w /\ ~(x IN (w DIFF v))} = v`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VSUM_NEG; VECTOR_ADD_LINV] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC VSUM_EQ_0 THEN MP_TAC th) THEN
    REWRITE_TAC[REAL_NEG_EQ_0; VECTOR_MUL_EQ_0; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN (w DIFF v) /\ y IN (w DIFF v) /\
                      (f:real^M->real^N) x = f y ==> x = y`
  ASSUME_TAC THENL
   [REMOVE_THEN "*" MP_TAC THEN
    ASM_SIMP_TAC[GSYM LINEAR_INJECTIVE_0_SUBSPACE; SUBSPACE_SPAN] THEN
    MP_TAC(ISPEC `w DIFF v:real^M->bool` SPAN_INC) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s = span(IMAGE f (w DIFF v))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC;
      ASM_MESON_TAC[SUBSPACE_LINEAR_IMAGE; SPAN_MONO; IMAGE_SUBSET;
                    SUBSET_TRANS; SUBSET_DIFF; SPAN_EQ_SELF]] THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN UNDISCH_TAC `span w:real^M->bool = s` THEN
    REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `x:real^M`) THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [IN_UNIV; SPAN_FINITE; INDEPENDENT_IMP_FINITE; IN_ELIM_THM;
      FINITE_IMAGE; FINITE_DIFF; ASSUME `independent(w:real^M->bool)`] THEN
    REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `u:real^M->real` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
    DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^M`) THEN
    EXISTS_TAC `(u:real^M->real) o (g:real^N->real^M)` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FINITE_DIFF; INDEPENDENT_IMP_FINITE; LINEAR_VSUM] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[o_DEF] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_EQ_SUPERSET THEN
    SIMP_TAC[SUBSET_DIFF; FINITE_DIFF; INDEPENDENT_IMP_FINITE;
             LINEAR_CMUL; IN_DIFF; TAUT `a /\ ~(a /\ ~b) <=> a /\ b`;
             ASSUME `independent(w:real^M->bool)`;
             ASSUME `linear(f:real^M->real^N)`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM SET_TAC[];
    SUBGOAL_THEN `independent(IMAGE (f:real^M->real^N) (w DIFF v))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
      ASM_SIMP_TAC[LINEAR_INJECTIVE_0_SUBSPACE; SUBSPACE_SPAN] THEN
      ASM_MESON_TAC[INDEPENDENT_MONO; SUBSET_DIFF];
      ASM_SIMP_TAC[DIM_SPAN; DIM_EQ_CARD] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o
        lhand o lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[FINITE_DIFF; CARD_DIFF; INDEPENDENT_IMP_FINITE] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUB_ADD THEN
      ASM_MESON_TAC[CARD_SUBSET; INDEPENDENT_IMP_FINITE]]]);;

let DIM_IMAGE_KERNEL = prove
 (`!f:real^M->real^N.
        linear f
        ==> dim(IMAGE f (:real^M)) + dim {x | f x = vec 0} = dimindex(:M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`] DIM_IMAGE_KERNEL_GEN) THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; IN_UNIV; DIM_UNIV]);;

let DIM_SUMS_INTER = prove
 (`!s t:real^N->bool.
    subspace s /\ subspace t
    ==> dim {x + y | x IN s /\ y IN t} + dim(s INTER t) = dim(s) + dim(t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s INTER t:real^N->bool` BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `s:real^N->bool`]
    MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `t:real^N->bool`]
    MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^N->bool) INTER d = b` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SUBSET_INTER] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN MP_TAC(ISPEC `c:real^N->bool` independent) THEN
    ASM_REWRITE_TAC[dependent; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN span b` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_INTER; SPAN_INC];
      MP_TAC(ISPECL [`b:real^N->bool`; `c DELETE (x:real^N)`] SPAN_MONO) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dim (s INTER t:real^N->bool) = CARD(b:real^N->bool) /\
    dim s = CARD c /\ dim t = CARD d /\
    dim {x + y:real^N | x IN s /\ y IN t} = CARD(c UNION d:real^N->bool)`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CARD_UNION_GEN; INDEPENDENT_IMP_FINITE] THEN
    MATCH_MP_TAC(ARITH_RULE `b:num <= c ==> (c + d) - b + b = c + d`) THEN
    ASM_SIMP_TAC[CARD_SUBSET; INDEPENDENT_IMP_FINITE]] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC DIM_UNIQUE THENL
   [EXISTS_TAC `b:real^N->bool`;
    EXISTS_TAC `c:real^N->bool`;
    EXISTS_TAC `d:real^N->bool`;
    EXISTS_TAC `c UNION d:real^N->bool`] THEN
  ASM_SIMP_TAC[HAS_SIZE; INDEPENDENT_IMP_FINITE; FINITE_UNION] THEN
  REWRITE_TAC[UNION_SUBSET; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; FORALL_IN_GSPEC] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
    ASM_SIMP_TAC[SUBSPACE_0; VECTOR_ADD_RID] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `x:real^N`] THEN
    ASM_SIMP_TAC[SUBSPACE_0; VECTOR_ADD_LID] THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL[`c:real^N->bool`; `c UNION d:real^N->bool`] SPAN_MONO);
      MP_TAC(ISPECL[`d:real^N->bool`; `c UNION d:real^N->bool`] SPAN_MONO)] THEN
    REWRITE_TAC[SUBSET_UNION] THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INDEPENDENT_EXPLICIT; FINITE_UNION; INDEPENDENT_IMP_FINITE] THEN
  X_GEN_TAC `a:real^N->real` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  ASM_SIMP_TAC[VSUM_UNION; SET_RULE `DISJOINT c (d DIFF c)`;
               INDEPENDENT_IMP_FINITE; FINITE_DIFF; FINITE_UNION] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(vsum (d DIFF c) (\v:real^N. a v % v)) IN span b`
  MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (VECTOR_ARITH
       `a + b = vec 0 ==> b = --a`)) THEN
      MATCH_MP_TAC SUBSPACE_NEG THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSPACE_VSUM THEN
    ASM_SIMP_TAC[FINITE_DIFF; INDEPENDENT_IMP_FINITE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSPACE_MUL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SPAN_FINITE; INDEPENDENT_IMP_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:real^N->real`) THEN
  MP_TAC(ISPEC `c:real^N->bool` INDEPENDENT_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o SPEC `(\x. if x IN b then a x + e x else a x):real^N->real`)) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  ONCE_REWRITE_TAC[COND_RATOR] THEN ASM_SIMP_TAC[VSUM_CASES] THEN
  REWRITE_TAC[VECTOR_ADD_RDISTRIB; GSYM DIFF] THEN
  ASM_SIMP_TAC[SET_RULE `b SUBSET c ==> {x | x IN c /\ x IN b} = b`] THEN
  ASM_SIMP_TAC[VSUM_ADD; INDEPENDENT_IMP_FINITE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(a + b) + c:real^N = (a + c) + b`] THEN
  ASM_SIMP_TAC[GSYM VSUM_UNION; FINITE_DIFF; INDEPENDENT_IMP_FINITE;
               SET_RULE `DISJOINT b (c DIFF b)`] THEN
  ASM_SIMP_TAC[SET_RULE `b SUBSET c ==> b UNION (c DIFF b) = c`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^N. v IN (c DIFF b) ==> a v = &0` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `d:real^N->bool` INDEPENDENT_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o SPEC `a:real^N->real`)) THEN
  SUBGOAL_THEN `d:real^N->bool = b UNION (d DIFF c)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_SIMP_TAC[VSUM_UNION; FINITE_DIFF; INDEPENDENT_IMP_FINITE;
               SET_RULE `c INTER d = b ==> DISJOINT b (d DIFF c)`] THEN
  SUBGOAL_THEN `vsum b (\x:real^N. a x % x) = vsum c (\x. a x % x)`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0] THEN ASM_MESON_TAC[]);;

let DIM_UNION_INTER = prove
 (`!s t:real^N->bool.
        subspace s /\ subspace t
        ==> dim(s UNION t) + dim(s INTER t) = dim s + dim t`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM DIM_SPAN] THEN
  MP_TAC(ISPECL [`span s:real^N->bool`; `span t:real^N->bool`]
        DIM_SUMS_INTER) THEN
  ASM_SIMP_TAC[SPAN_UNION; SUBSPACE_SPAN; SPAN_OF_SUBSPACE]);;

let DIM_KERNEL_COMPOSE = prove
 (`!f:real^M->real^N g:real^N->real^P.
        linear f /\ linear g
        ==> dim {x | (g o f) x = vec 0} <=
                dim {x | f(x) = vec 0} +
                dim {y | g(y) = vec 0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{x | (f:real^M->real^N) x = vec 0}` BASIS_EXISTS_FINITE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?c. FINITE c /\
        IMAGE f c SUBSET {y | g(y):real^P = vec 0} /\
        independent (IMAGE (f:real^M->real^N) c) /\
        IMAGE f (:real^M) INTER {y | g(y) = vec 0} SUBSET span(IMAGE f c) /\
        (!x y. x IN c /\ y IN c ==> (f x = f y <=> x = y)) /\
        (IMAGE f c) HAS_SIZE dim (IMAGE f (:real^M) INTER {y | g(y) = vec 0})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (f:real^M->real^N) (:real^M) INTER
                 {x | (g:real^N->real^P) x = vec 0}` BASIS_EXISTS_FINITE) THEN
    REWRITE_TAC[SUBSET_INTER; GSYM CONJ_ASSOC; EXISTS_FINITE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `c:real^M->bool`]
        IMAGE_INJECTIVE_IMAGE_OF_SUBSET) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `dim(span(b UNION c:real^M->bool))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIM_SUBSET THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; o_THM] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) x IN span(IMAGE f c)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE; IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
    SUBST1_TAC(VECTOR_ARITH `x:real^M = y + (x - y)`) THEN
    MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_UNION; SPAN_MONO; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!t. x IN t /\ t SUBSET s ==> x IN s`) THEN
    EXISTS_TAC `{x | (f:real^M->real^N) x = vec 0}` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[LINEAR_SUB; VECTOR_SUB_EQ];
      ASM_MESON_TAC[SUBSET_TRANS; SUBSET_UNION; SPAN_MONO]];
    REWRITE_TAC[DIM_SPAN] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(b UNION c:real^M->bool)` THEN
    ASM_SIMP_TAC[DIM_LE_CARD; FINITE_UNION; INDEPENDENT_IMP_FINITE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(b:real^M->bool) + CARD(c:real^M->bool)` THEN
    ASM_SIMP_TAC[CARD_UNION_LE] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM DIM_EQ_CARD; DIM_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `dim(IMAGE (f:real^M->real^N) c)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[DIM_EQ_CARD] THEN
      ASM_MESON_TAC[CARD_IMAGE_INJ; LE_REFL];
      ASM_SIMP_TAC[GSYM DIM_EQ_CARD; DIM_SUBSET]]]);;

let DIM_ORTHOGONAL_SUM = prove
 (`!s t:real^N->bool.
        (!x y. x IN s /\ y IN t ==> x dot y = &0)
        ==> dim(s UNION t) = dim(s) + dim(t)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  REWRITE_TAC[SPAN_UNION] THEN
  SIMP_TAC[GSYM DIM_SUMS_INTER; SUBSPACE_SPAN] THEN
  REWRITE_TAC[ARITH_RULE `x = x + y <=> y = 0`] THEN
  REWRITE_TAC[DIM_EQ_0; SUBSET; IN_INTER] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN span s ==> !y:real^N. y IN span t ==> x dot y = &0`
  MP_TAC THENL
   [MATCH_MP_TAC SPAN_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC SPAN_INDUCT THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
      SIMP_TAC[subspace; IN_ELIM_THM; DOT_RMUL; DOT_RADD; DOT_RZERO] THEN
      REAL_ARITH_TAC;
      SIMP_TAC[subspace; IN_ELIM_THM; DOT_LMUL; DOT_LADD; DOT_LZERO] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[IN_SING] THEN MESON_TAC[DOT_EQ_0]]);;

let DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS = prove
 (`!s t:real^N->bool.
        subspace s /\ subspace t /\ s SUBSET t
        ==> dim {y | y IN t /\ !x. x IN s ==> orthogonal x y} + dim s = dim t`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) DIM_ORTHOGONAL_SUM o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM; orthogonal] THEN MESON_TAC[DOT_SYM];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN REWRITE_TAC[SUBSPACE_SPAN] THEN
  REWRITE_TAC[SPAN_UNION; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
        ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP (VECTOR_ARITH
     `x:real^N = y + z ==> z = x - y`)) THEN
    MATCH_MP_TAC SUBSPACE_SUB THEN
    ASM_MESON_TAC[SUBSET; SPAN_EQ_SELF];
    ASM_MESON_TAC[SPAN_SUPERSET; ORTHOGONAL_SYM]]);;

let DIM_SPECIAL_SUBSPACE = prove
 (`!k. dim {x:real^N |
            !i. 1 <= i /\ i <= dimindex(:N) /\ i IN k ==> x$i = &0} =
       CARD((1..dimindex(:N)) DIFF k)`,
  GEN_TAC THEN MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `IMAGE (basis:num->real^N) ((1..dimindex(:N)) DIFF k)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    SIMP_TAC[BASIS_COMPONENT; IN_DIFF; IN_NUMSEG] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:real^N)$j = &0` THEN
    ASM_REWRITE_TAC[SPAN_0; VECTOR_MUL_LZERO] THEN
    MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `j:num` THEN
    REWRITE_TAC[IN_NUMSEG; IN_DIFF] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM;
      SET_RULE `~(a IN IMAGE f s) <=> (!x. x IN s ==> ~(f x = a))`] THEN
    SIMP_TAC[FORALL_IN_IMAGE; ORTHOGONAL_BASIS_BASIS; BASIS_INJ_EQ;
             IN_DIFF; IN_NUMSEG; BASIS_NONZERO];
    SIMP_TAC[HAS_SIZE; FINITE_IMAGE; FINITE_DIFF; FINITE_NUMSEG] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG; IMP_CONJ; RIGHT_FORALL_IMP_THM;
      SET_RULE `~(a IN IMAGE f s) <=> (!x. x IN s ==> ~(f x = a))`] THEN
    SIMP_TAC[FORALL_IN_IMAGE; ORTHOGONAL_BASIS_BASIS; BASIS_INJ_EQ;
             IN_DIFF; IN_NUMSEG; BASIS_NONZERO]]);;

(* ------------------------------------------------------------------------- *)
(* More injective/surjective versus dimension variants.                      *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INJECTIVE_IFF_DIM = prove
 (`!f:real^M->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) <=>
             dim(IMAGE f (:real^M)) = dimindex(:M))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` DIM_IMAGE_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (ARITH_RULE
    `x + y:num = m ==> (x = m <=> y = 0)`)) THEN
  REWRITE_TAC[DIM_EQ_0; SUBSET; IN_ELIM_THM; IN_SING] THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_0]);;

let LINEAR_SURJECTIVE_IFF_DIM = prove
 (`!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. f x = y) <=>
             dim(IMAGE f (:real^M)) = dimindex(:N))`,
  SIMP_TAC[DIM_EQ_FULL; SPAN_LINEAR_IMAGE; SPAN_UNIV] THEN SET_TAC[]);;

let LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN = prove
 (`!f:real^M->real^N.
      dimindex(:M) = dimindex(:N) /\ linear f
      ==> ((!y. ?x. f x = y) <=> (!x y. f x = f y ==> x = y))`,
  SIMP_TAC[LINEAR_INJECTIVE_IFF_DIM; LINEAR_SURJECTIVE_IFF_DIM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More about product spaces.                                                *)
(* ------------------------------------------------------------------------- *)

let PASTECART_AS_ORTHOGONAL_SUM = prove
 (`!x:real^M y:real^N.
        pastecart x y = pastecart x (vec 0) + pastecart (vec 0) y`,
  REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID]);;

let PCROSS_AS_ORTHOGONAL_SUM = prove
 (`!s:real^M->bool t:real^N->bool.
        s PCROSS t =
        {u + v | u IN IMAGE (\x. pastecart x (vec 0)) s /\
                 v IN IMAGE (\y. pastecart (vec 0) y) t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [PASTECART_AS_ORTHOGONAL_SUM] THEN
  SET_TAC[]);;

let DIM_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> dim(s PCROSS t) = dim s + dim t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PCROSS_AS_ORTHOGONAL_SUM] THEN
  W(MP_TAC o PART_MATCH (lhand o lhand o rand) DIM_SUMS_INTER o
        lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSPACE_LINEAR_IMAGE;
    MATCH_MP_TAC(ARITH_RULE `c = d /\ b = 0 ==> a + b = c ==> a = d`) THEN
    CONJ_TAC THENL
     [BINOP_TAC THEN MATCH_MP_TAC DIM_INJECTIVE_LINEAR_IMAGE THEN
      SIMP_TAC[PASTECART_INJ];
      REWRITE_TAC[DIM_EQ_0; SUBSET; IN_INTER; IN_IMAGE; IN_SING] THEN
      REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MESON_TAC[FSTCART_VEC; SNDCART_VEC]]] THEN
  ASM_REWRITE_TAC[linear; GSYM PASTECART_VEC] THEN
  REWRITE_TAC[PASTECART_ADD; GSYM PASTECART_CMUL; PASTECART_INJ] THEN
  VECTOR_ARITH_TAC);;

let SPAN_PCROSS_SUBSET = prove
 (`!s:real^M->bool t:real^N->bool.
        span(s PCROSS t) SUBSET (span s) PCROSS (span t)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
  SIMP_TAC[SUBSPACE_PCROSS; SUBSPACE_SPAN; PCROSS_MONO; SPAN_INC]);;

let SPAN_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ (vec 0 IN s \/ vec 0 IN t)
        ==> span(s PCROSS t) = (span s) PCROSS (span t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SPAN_PCROSS_SUBSET] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_PCROSS] THEN
  ONCE_REWRITE_TAC[PASTECART_AS_ORTHOGONAL_SUM] THEN
  SUBGOAL_THEN
   `(!x:real^M. x IN span s ==> pastecart x (vec 0) IN span(s PCROSS t)) /\
    (!y:real^N. y IN span t ==> pastecart (vec 0) y IN span(s PCROSS t))`
   (fun th -> ASM_MESON_TAC[th; SPAN_ADD]) THEN
  CONJ_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[IN_ELIM_THM] THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN
     ASM_SIMP_TAC[SPAN_SUPERSET; PASTECART_IN_PCROSS];
     REWRITE_TAC[subspace; IN_ELIM_THM; PASTECART_VEC; SPAN_0] THEN
     CONJ_TAC THEN REPEAT GEN_TAC THENL
      [DISCH_THEN(MP_TAC o MATCH_MP SPAN_ADD) THEN
       REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID];
       DISCH_THEN(MP_TAC o MATCH_MP SPAN_MUL) THEN
       SIMP_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO]]])
  THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    SUBGOAL_THEN
     `pastecart x (vec 0) =
      pastecart (x:real^M) (y:real^N) - pastecart (vec 0) y`
    SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_SUB; PASTECART_INJ] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC SPAN_SUB THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; PASTECART_IN_PCROSS]];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^M`) THEN
    SUBGOAL_THEN
     `pastecart (vec 0) y =
      pastecart (x:real^M) (y:real^N) - pastecart x (vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_SUB; PASTECART_INJ] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC SPAN_SUB THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; PASTECART_IN_PCROSS]]]);;

let DIM_PCROSS_STRONG = prove
 (`!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ (vec 0 IN s \/ vec 0 IN t)
        ==> dim(s PCROSS t) = dim s + dim t`,
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  SIMP_TAC[SPAN_PCROSS; DIM_PCROSS; SUBSPACE_SPAN]);;

let SPAN_SUMS = prove
 (`!s t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ vec 0 IN (s UNION t)
        ==> span {x + y | x IN s /\ y IN t} =
            {x + y | x IN span s /\ y IN span t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SPAN_UNION] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
  REWRITE_TAC[SUBSPACE_SPAN; SUBSET; FORALL_IN_GSPEC] THEN
  SIMP_TAC[SPAN_ADD; IN_UNION; SPAN_SUPERSET] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I [IN_UNION]) THENL
   [UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    SUBST1_TAC(VECTOR_ARITH `x:real^N = (x + y) - (vec 0 + y)`) THEN
    MATCH_MP_TAC SPAN_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    ASM SET_TAC[];
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[VECTOR_ADD_RID];
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[VECTOR_ADD_LID];
    UNDISCH_TAC `~(s:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    SUBST1_TAC(VECTOR_ARITH `x:real^N = (y + x) - (y + vec 0)`) THEN
    MATCH_MP_TAC SPAN_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* More about rank from the rank/nullspace formula.                          *)
(* ------------------------------------------------------------------------- *)

let RANK_NULLSPACE = prove
 (`!A:real^M^N. rank A + dim {x | A ** x = vec 0} = dimindex(:M)`,
  GEN_TAC THEN REWRITE_TAC[RANK_DIM_IM] THEN
  MATCH_MP_TAC DIM_IMAGE_KERNEL THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let RANK_SYLVESTER = prove
 (`!A:real^N^M B:real^P^N.
        rank(A) + rank(B) <= rank(A ** B) + dimindex(:N)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
    `!ia ib iab p:num.
        ra + ia = n /\
        rb + ib = p /\
        rab + iab = p /\
        iab <= ia + ib
        ==> ra + rb <= rab + n`) THEN
  MAP_EVERY EXISTS_TAC
   [`dim {x | (A:real^N^M) ** x = vec 0}`;
    `dim {x | (B:real^P^N) ** x = vec 0}`;
    `dim {x | ((A:real^N^M) ** (B:real^P^N)) ** x = vec 0}`;
    `dimindex(:P)`] THEN
  REWRITE_TAC[RANK_NULLSPACE] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] DIM_KERNEL_COMPOSE) THEN
  CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let RANK_GRAM = prove
 (`!A:real^M^N. rank(transp A ** A) = rank A`,
  GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
   `!n n' k. r + n:num = k /\ r' + n' = k /\ n = n' ==> r = r'`) THEN
  MAP_EVERY EXISTS_TAC
   [`dim {x | (transp A ** (A:real^M^N)) ** x = vec 0}`;
    `dim {x | (A:real^M^N) ** x = vec 0}`;
    `dimindex(:M)`] THEN
  REWRITE_TAC[RANK_NULLSPACE] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; GSYM MATRIX_VECTOR_MUL_ASSOC;
           MATRIX_VECTOR_MUL_RZERO] THEN
  X_GEN_TAC `x:real^M` THEN
  DISCH_THEN(MP_TAC o AP_TERM `(dot) (x:real^M)`) THEN
  ONCE_REWRITE_TAC[GSYM DOT_LMUL_MATRIX] THEN
  REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP; TRANSP_TRANSP; DOT_RZERO] THEN
  REWRITE_TAC[DOT_EQ_0]);;

let RANK_TRIANGLE = prove
 (`!A B:real^M^N. rank(A + B) <= rank(A) + rank(B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RANK_DIM_IM] THEN
  MP_TAC(ISPECL [`IMAGE (\x. (A:real^M^N) ** x) (:real^M)`;
                 `IMAGE (\x. (B:real^M^N) ** x) (:real^M)`]
                DIM_SUMS_INTER) THEN
  ASM_SIMP_TAC[SUBSPACE_LINEAR_IMAGE; SUBSPACE_UNIV;
               MATRIX_VECTOR_MUL_LINEAR] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`) THEN
  MATCH_MP_TAC DIM_SUBSET THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV;
              MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN MESON_TAC[]);;

let COVARIANCE_MATRIX_EQ_0 = prove
 (`!A:real^N^M. transp A ** A = mat 0 <=> A = mat 0`,
  REWRITE_TAC[GSYM RANK_EQ_0; RANK_GRAM]);;

let MATRIX_MUL_COVARIANCE_LCANCEL = prove
 (`!A:real^N^P B C:real^M^N.
        (transp A ** A) ** B = (transp A ** A) ** C <=> A ** B = A ** C`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM MATRIX_SUB_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM COVARIANCE_MATRIX_EQ_0] THEN
  MATCH_MP_TAC(MESON[MATRIX_MUL_RZERO]
   `(?C:real^M^N. C ** A = B) ==> A = mat 0 ==> B = mat 0`) THEN
  EXISTS_TAC `transp(B - C:real^M^N)` THEN
  REWRITE_TAC[TRANSP_MATRIX_SUB; MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]);;

let MATRIX_MUL_COVARIANCE_RCANCEL = prove
 (`!A:real^P^N B C:real^N^M.
        B ** (A ** transp A) = C ** (A ** transp A) <=> B ** A = C ** A`,
  ONCE_REWRITE_TAC[GSYM TRANSP_EQ] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[MATRIX_MUL_COVARIANCE_LCANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Inverse matrices. These are actually, in general, Moore-Penrose           *)
(* pseudoinverses, but collapse to the usual inverse in the invertible case. *)
(* The extra generality gives some cleaner theorems (e.g. MATRIX_INV_INV)    *)
(* and might have some other applications one day.                           *)
(* ------------------------------------------------------------------------- *)

let matrix_inv = new_definition
 `matrix_inv (A:real^M^N) =
    matrix(\y. @x. (!w. A ** w = vec 0 ==> orthogonal x w) /\
                   (!z. orthogonal (y - A ** x) (A ** z)))`;;

let MOORE_PENROSE_PSEUDOINVERSE,MOORE_PENROSE_PSEUDOINVERSE_UNIQUE =
  let lemma_existence = prove
   (`!f:real^M->real^N y.
          linear f
          ==> ?x. (!w. f w = vec 0 ==> orthogonal x w) /\
                  (!z. orthogonal (y - f x) (f z))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?u. !z. orthogonal (y - (f:real^M->real^N) u) (f z)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (f:real^M->real^N) UNIV`; `y:real^N`]
          ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
      ASM_SIMP_TAC[SPAN_OF_SUBSPACE; SUBSPACE_LINEAR_IMAGE; SUBSPACE_UNIV] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_UNIV] THEN
      MESON_TAC[VECTOR_ARITH `y:real^N = x + z <=> y - x = z`];
      MP_TAC(ISPECL [`{v | (f:real^M->real^N) v = vec 0}`; `u:real^M`]
          ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
      ASM_SIMP_TAC[SPAN_OF_SUBSPACE; SUBSPACE_KERNEL] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `w:real^M` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH `y:real^N = x + z <=> y - x = z`] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^M` STRIP_ASSUME_TAC) THEN
      EXPAND_TAC "w" THEN ASM_SIMP_TAC[LINEAR_SUB; VECTOR_SUB_RZERO]])
  and lemma_uniqueness = prove
   (`!A:real^M^N u v y.
        (!w. A ** w = vec 0 ==> orthogonal u w) /\
        (!z. orthogonal (y - A ** u) (A ** z)) /\
        (!w. A ** w = vec 0 ==> orthogonal v w) /\
        (!z. orthogonal (y - A ** v) (A ** z))
        ==> u = v`,
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC[GSYM ORTHOGONAL_REFL] THEN
    MATCH_MP_TAC(last(CONJUNCTS ORTHOGONAL_CLAUSES)) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM ORTHOGONAL_REFL] THEN
    (SUBGOAL_THEN
     `(A:real^M^N) ** (u - v:real^M) = (y - A ** v) - (y - A ** u)` MP_TAC
     THENL
      [SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN CONV_TAC VECTOR_ARITH;
       DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th])]) THEN
    ASM_MESON_TAC[ORTHOGONAL_CLAUSES]) in
  let MOORE_PENROSE_PSEUDOINVERSE = prove
   (`!A:real^M^N y.
           (!w. A ** w = vec 0 ==> orthogonal (matrix_inv A ** y) w) /\
           (!z. orthogonal (y - A ** (matrix_inv A ** y)) (A ** z))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[matrix_inv] THEN
    MP_TAC(ISPEC `\x:real^M. (A:real^M^N) ** x` lemma_existence) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN(MP_TAC o GEN `y:real^N` o SELECT_RULE o SPEC `y:real^N`) THEN
    ABBREV_TAC
     `f y = @x. (!w. (A:real^M^N) ** w = vec 0 ==> orthogonal x w) /\
                (!z. orthogonal (y - A ** x) (A ** z))` THEN
    REWRITE_TAC[FORALL_AND_THM; ETA_AX] THEN STRIP_TAC THEN
    SUBGOAL_THEN `linear(f:real^N->real^M)` ASSUME_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[MATRIX_WORKS]] THEN
    REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC lemma_uniqueness THEN EXISTS_TAC `A:real^M^N` THENL
     [EXISTS_TAC `x + y:real^N`; EXISTS_TAC `c % x:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ORTHOGONAL_CLAUSES; MATRIX_VECTOR_MUL_RMUL;
      GSYM VECTOR_SUB_LDISTRIB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
      VECTOR_ARITH `(x + y) - (u + v):real^N = (x - u) + (y - v)`]) in
  let MOORE_PENROSE_PSEUDOINVERSE_UNIQUE = prove
   (`!A:real^M^N x y.
           (!w. A ** w = vec 0 ==> orthogonal x w) /\
           (!z. orthogonal (y - A ** x) (A ** z))
           ==> matrix_inv A ** y = x`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma_uniqueness THEN
    EXISTS_TAC `A:real^M^N` THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[MOORE_PENROSE_PSEUDOINVERSE]) in
  MOORE_PENROSE_PSEUDOINVERSE,MOORE_PENROSE_PSEUDOINVERSE_UNIQUE;;

let MATRIX_INV_MUL_INNER = prove
 (`!A:real^M^N. A ** matrix_inv A ** A = A`,
  SIMP_TAC[MATRIX_EQ; MATRIX_MUL_ASSOC; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM ORTHOGONAL_REFL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  REWRITE_TAC[MOORE_PENROSE_PSEUDOINVERSE]);;

let SYMMETRIC_MATRIX_INV_RMUL = prove
 (`!A:real^M^N. transp(A ** matrix_inv A) = A ** matrix_inv A`,
  GEN_TAC THEN
  MP_TAC(ISPEC `\x:real^N. ((A:real^M^N) ** matrix_inv A) ** x`
    ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT) THEN
  SIMP_TAC[ADJOINT_MATRIX; ORTHOGONAL_PROJECTION_ALT; MATRIX_VECTOR_MUL_ASSOC;
           MATRIX_VECTOR_MUL_LINEAR; o_DEF; FUN_EQ_THM; GSYM MATRIX_EQ] THEN
  MATCH_MP_TAC(TAUT `p ==> (p <=> q /\ r) ==> q`) THEN
  ONCE_REWRITE_TAC[GSYM ORTHOGONAL_LNEG] THEN
  REWRITE_TAC[VECTOR_NEG_SUB; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[MOORE_PENROSE_PSEUDOINVERSE]);;

let MATRIX_INV_INV = prove
 (`!A:real^M^N. matrix_inv (matrix_inv A) = A`,
  REWRITE_TAC[MATRIX_EQ] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MOORE_PENROSE_PSEUDOINVERSE_UNIQUE THEN
  MP_TAC(ISPEC `A:real^M^N` MOORE_PENROSE_PSEUDOINVERSE) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `x:real^M`]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_RZERO; ORTHOGONAL_SYM;
                     MATRIX_VECTOR_MUL_RZERO];
    ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; VECTOR_SUB_EQ] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_MUL_ASSOC] THEN
    REWRITE_TAC[MATRIX_INV_MUL_INNER]]);;

let MATRIX_INV_EQ = prove
 (`!A B:real^M^N. matrix_inv A = matrix_inv B <=> A = B`,
  MESON_TAC[MATRIX_INV_INV]);;

let MATRIX_INV_MUL_OUTER = prove
 (`!A:real^M^N. matrix_inv A ** A ** matrix_inv A = matrix_inv A`,
  GEN_TAC THEN
  MP_TAC(ISPEC `matrix_inv(A:real^M^N)` MATRIX_INV_MUL_INNER) THEN
  REWRITE_TAC[MATRIX_INV_INV]);;

let SYMMETRIC_MATRIX_INV_LMUL = prove
 (`!A:real^M^N. transp(matrix_inv A ** A) = matrix_inv A ** A`,
  GEN_TAC THEN
  MP_TAC(ISPEC `matrix_inv(A:real^M^N)` SYMMETRIC_MATRIX_INV_RMUL) THEN
  REWRITE_TAC[MATRIX_INV_INV]);;

let MATRIX_INV_UNIQUE_STRONG = prove
 (`!A:real^M^N X.
        A ** X ** A = A /\ X ** A ** X = X /\
        transp(A ** X) = A ** X /\ transp(X ** A) = X ** A
        ==> matrix_inv A = X`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (ASSUME_TAC o ISPEC `A:real^M^N`)
   [MATRIX_INV_MUL_OUTER; SYMMETRIC_MATRIX_INV_RMUL; MATRIX_INV_MUL_INNER;
    SYMMETRIC_MATRIX_INV_LMUL] THEN
  ABBREV_TAC `Y = matrix_inv(A:real^M^N)` THEN
  POP_ASSUM(K ALL_TAC) THEN CONV_TAC SYM_CONV THEN
  SUBGOAL_THEN
   `(X:real^N^M) ** (A:real^M^N) ** X = Y ** A ** Y`
  MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  TRANS_TAC EQ_TRANS `(X:real^N^M) ** (A:real^M^N) ** (Y:real^N^M)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN TRANS_TAC EQ_TRANS
     `transp(X:real^N^M) ** transp(A ** (Y:real^N^M) ** A)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM MATRIX_TRANSP_MUL]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ONCE_REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS
     `transp(A ** (Y:real^N^M) ** A) ** transp(X:real^N^M)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM MATRIX_TRANSP_MUL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]]);;

let MATRIX_INV_TRANSP = prove
 (`!A:real^M^N. matrix_inv (transp A) = transp(matrix_inv A)`,
  GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
  REWRITE_TAC[TRANSP_EQ; GSYM MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[MATRIX_INV_MUL_INNER; MATRIX_INV_MUL_OUTER;
              SYMMETRIC_MATRIX_INV_RMUL; SYMMETRIC_MATRIX_INV_LMUL]);;

let TRANSP_MATRIX_INV = prove
 (`!A:real^M^N. transp(matrix_inv A) = matrix_inv(transp A)`,
  REWRITE_TAC[MATRIX_INV_TRANSP]);;

let SYMMETRIC_MATRIX_INV = prove
 (`!A:real^N^N. transp(matrix_inv A) = matrix_inv A <=> transp A = A`,
  REWRITE_TAC[TRANSP_MATRIX_INV; MATRIX_INV_EQ]);;

let MATRIX_INV_0 = prove
 (`matrix_inv(mat 0:real^M^N) = mat 0`,
  MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO; TRANSP_MAT]);;

let MATRIX_INV_EQ_0 = prove
 (`!A:real^M^N. matrix_inv A = mat 0 <=> A = mat 0`,
  MESON_TAC[MATRIX_INV_0; MATRIX_INV_INV]);;

let MATRIX_INV_CMUL = prove
 (`!c A:real^M^N. matrix_inv (c %% A) = inv(c) %% matrix_inv A`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; TRANSP_MATRIX_CMUL] THEN
  REWRITE_TAC[MATRIX_CMUL_ASSOC; MATRIX_INV_MUL_INNER; MATRIX_INV_MUL_OUTER;
              SYMMETRIC_MATRIX_INV_RMUL; SYMMETRIC_MATRIX_INV_LMUL] THEN
  ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[REAL_INV_0; MATRIX_CMUL_LZERO; REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; REAL_MUL_LID]);;

let MATRIX_INV = prove
 (`!A:real^N^M.
    invertible A ==> A ** matrix_inv A = mat 1 /\ matrix_inv A ** A = mat 1`,
  GEN_TAC THEN REWRITE_TAC[invertible] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^M^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(AP_TERM `\A:real^N^M. (B:real^M^N) ** A`
   (ISPEC `A:real^N^M` MATRIX_INV_MUL_INNER)) THEN
  MP_TAC(AP_TERM `\A:real^N^M. A ** (B:real^M^N)`
       (ISPEC `A:real^N^M` MATRIX_INV_MUL_INNER)) THEN
  ASM_REWRITE_TAC[MATRIX_MUL_ASSOC; MATRIX_MUL_LID] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID] THEN
  SIMP_TAC[MATRIX_MUL_LID]);;

let MATRIX_MUL_LCANCEL = prove
 (`!A:real^M^N B:real^P^M C.
        invertible A ==> (A ** B = A ** C <=> B = C)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `matrix_mul (matrix_inv(A:real^M^N)):real^P^N->real^P^M`) THEN
  ASM_SIMP_TAC[MATRIX_MUL_ASSOC; MATRIX_MUL_LID]);;

let MATRIX_MUL_RCANCEL = prove
 (`!A B:real^M^N C:real^P^M.
        invertible C ==> (A ** C = B ** C <=> A = B)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\A:real^P^N. A ** matrix_inv(C:real^P^M)`) THEN
  ASM_SIMP_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID]);;

let RANK_INVERTIBLE_RMUL = prove
 (`!A:real^M^N B:real^P^M. invertible B ==> rank(A ** B) = rank A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM; RANK_MUL_LE_LEFT] THEN
  TRANS_TAC LE_TRANS
    `rank(((A:real^M^N) ** (B:real^P^M)) ** matrix_inv B)` THEN
  REWRITE_TAC[RANK_MUL_LE_LEFT] THEN
  ASM_SIMP_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV] THEN
  REWRITE_TAC[LE_REFL; MATRIX_MUL_RID]);;

let RANK_INVERTIBLE_LMUL = prove
 (`!A:real^M^N B:real^P^M. invertible A ==> rank(A ** B) = rank B`,
  ONCE_REWRITE_TAC[GSYM RANK_TRANSP] THEN
  SIMP_TAC[MATRIX_TRANSP_MUL; RANK_INVERTIBLE_RMUL; INVERTIBLE_TRANSP]);;

let RANK_CMUL = prove
 (`!A:real^N^M c. rank(c %% A) = if c = &0 then 0 else rank A`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MATRIX_CMUL_LZERO; RANK_0] THEN
  GEN_REWRITE_TAC
   (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM MATRIX_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_LMUL] THEN
  MATCH_MP_TAC RANK_INVERTIBLE_LMUL THEN
  ASM_REWRITE_TAC[INVERTIBLE_CMUL; INVERTIBLE_I]);;

let RANK_NEG = prove
 (`!A:real^N^M. rank(--A) = rank A`,
  REWRITE_TAC[MATRIX_NEG_MINUS1; RANK_CMUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MATRIX_INV_UNIQUE = prove
 (`!A:real^N^M B. A ** B = mat 1 /\ B ** A = mat 1 ==> matrix_inv A = B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  ASM_REWRITE_TAC[TRANSP_MAT; MATRIX_MUL_RID]);;

let MATRIX_INV_I = prove
 (`matrix_inv(mat 1:real^N^N) = mat 1`,
  MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
  REWRITE_TAC[MATRIX_MUL_LID]);;

let INVERTIBLE_MATRIX_INV = prove
 (`!A:real^M^N. invertible(matrix_inv A) <=> invertible A`,
  MESON_TAC[MATRIX_INV_INV; MATRIX_INV; invertible]);;

let MATRIX_INV_UNIQUE_LEFT = prove
 (`!A:real^N^N B. A ** B = mat 1 ==> matrix_inv B = A`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
  ASM_MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE]);;

let MATRIX_INV_UNIQUE_RIGHT = prove
 (`!A:real^N^N B. A ** B = mat 1 ==> matrix_inv A = B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
  ASM_MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE]);;

let MATRIX_INV_COVARIANCE = prove
 (`!A:real^M^N.
     matrix_inv(transp A ** A) = matrix_inv(A) ** transp(matrix_inv A)`,
  GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MESON[MATRIX_MUL_ASSOC; MATRIX_TRANSP_MUL]
   `(A:real^M^N) ** transp B ** transp C ** (D:real^P^Q) =
    A ** transp(C ** B) ** D`] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_LMUL; SYMMETRIC_MATRIX_INV_RMUL] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV_MUL_INNER] THEN
  REWRITE_TAC[EQT_ELIM(REWRITE_CONV[MATRIX_MUL_ASSOC]
   `(A:real^M^N) ** B ** C ** (D:real^P^Q) = (A ** B ** C) ** D`)] THEN
  REWRITE_TAC[MATRIX_INV_MUL_OUTER] THEN
  MATCH_MP_TAC(MESON[] `y = x ==> x = y /\ y = x`) THEN
  ONCE_REWRITE_TAC[GSYM SYMMETRIC_MATRIX_INV_RMUL] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV_MUL_INNER] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_LMUL]);;

let COVARIANCE_MATRIX_INV = prove
 (`!A:real^M^N.
        transp(matrix_inv A) ** matrix_inv A = matrix_inv(A ** transp A)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_INV_EQ] THEN
  REWRITE_TAC[MATRIX_INV_INV; MATRIX_INV_COVARIANCE]);;

let NORMAL_MATRIX_INV = prove
 (`!A:real^N^N.
        transp(matrix_inv A) ** matrix_inv A =
        matrix_inv A ** transp(matrix_inv A) <=>
        transp A ** A = A ** transp A`,
  REWRITE_TAC[GSYM MATRIX_INV_COVARIANCE; COVARIANCE_MATRIX_INV] THEN
  REWRITE_TAC[MATRIX_INV_EQ] THEN MESON_TAC[]);;

let MATRIX_INV_COVARIANCE_RMUL = prove
 (`!A:real^M^N. matrix_inv(transp A ** A) ** transp A = matrix_inv A`,
  REWRITE_TAC[MATRIX_INV_COVARIANCE] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_RMUL; MATRIX_INV_MUL_OUTER]);;

let MATRIX_INV_COVARIANCE_LMUL = prove
 (`!A:real^M^N. transp(A) ** matrix_inv(A ** transp A) = matrix_inv A`,
  REWRITE_TAC[GSYM COVARIANCE_MATRIX_INV] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_LMUL; GSYM MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[MATRIX_INV_MUL_OUTER]);;

let RANK_CONJUGATE = prove
 (`!A:real^N^N U:real^M^N.
        invertible U ==> rank(matrix_inv U ** A ** U) = rank A`,
  SIMP_TAC[RANK_INVERTIBLE_RMUL; RANK_INVERTIBLE_LMUL;
           INVERTIBLE_MATRIX_INV]);;

let RANK_MATRIX_INV = prove
 (`!A:real^M^N. rank(matrix_inv A) = rank A`,
  GEN_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM MATRIX_INV_MUL_INNER] THEN
  REWRITE_TAC[MATRIX_INV_INV] THEN MATCH_MP_TAC(MESON[LE_TRANS]
   `rank(A ** B ** C) <= rank(B ** C) /\ rank(B ** C) <= rank B
    ==> rank(A ** B ** C) <= rank B`) THEN
  REWRITE_TAC[RANK_MUL_LE_RIGHT; RANK_MUL_LE_LEFT]);;

let RANK_MATRIX_INV_RMUL = prove
 (`!A:real^M^N. rank(A ** matrix_inv A) = rank A`,
  GEN_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  REWRITE_TAC[RANK_MUL_LE_LEFT] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM RANK_MATRIX_INV] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM MATRIX_INV_MUL_OUTER] THEN
  REWRITE_TAC[RANK_MUL_LE_RIGHT]);;

let RANK_MATRIX_INV_LMUL = prove
 (`!A:real^M^N. rank(matrix_inv A ** A) = rank A`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM RANK_TRANSP] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_MATRIX_INV; RANK_MATRIX_INV_RMUL]);;

let MATRIX_INV_MULTIPLE_TRANP_RIGHT = prove
 (`!A:real^M^N.
       matrix_inv A = matrix_inv A ** transp(matrix_inv A) ** transp A`,
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL; SYMMETRIC_MATRIX_INV_RMUL] THEN
  REWRITE_TAC[MATRIX_INV_MUL_OUTER]);;

let MATRIX_TRANSP_MULTIPLE_INV_RIGHT = prove
 (`!A:real^M^N. transp A = transp A ** A ** matrix_inv A`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM MATRIX_INV_MUL_INNER] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_RMUL] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC]);;

let MATRIX_INV_MULTIPLE_TRANP_LEFT = prove
 (`!A:real^M^N.
       matrix_inv A = transp A ** transp(matrix_inv A) ** matrix_inv A`,
  GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MATRIX_INV_MUL_OUTER] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_LMUL]);;

let MATRIX_TRANSP_MULTIPLE_INV_LEFT = prove
 (`!A:real^M^N. transp A = matrix_inv A ** A ** transp A`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM MATRIX_INV_MUL_INNER] THEN
  ONCE_REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_LMUL] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC]);;

let MATRIX_VECTOR_MUL_INV_EQ_0 = prove
 (`!A:real^M^N. matrix_inv A ** x = vec 0 <=> transp A ** x = vec 0`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ONCE_REWRITE_TAC[MATRIX_TRANSP_MULTIPLE_INV_RIGHT];
    ONCE_REWRITE_TAC[MATRIX_INV_MULTIPLE_TRANP_RIGHT]] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_RZERO]);;

let KERNEL_MATRIX_INV = prove
 (`!A:real^M^N.
        {x | matrix_inv A ** x = vec 0} = {x | transp A ** x = vec 0}`,
  REWRITE_TAC[MATRIX_VECTOR_MUL_INV_EQ_0]);;

let IMAGE_MATRIX_INV = prove
 (`!A:real^M^N.
        IMAGE (\x:real^N. matrix_inv A ** x) UNIV =
        IMAGE (\x. transp A ** x) UNIV`,
  GEN_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THENL
   [ONCE_REWRITE_TAC[MATRIX_INV_MULTIPLE_TRANP_LEFT];
    ONCE_REWRITE_TAC[MATRIX_TRANSP_MULTIPLE_INV_LEFT]] THEN
  REWRITE_TAC[IN_UNIV; IN_IMAGE; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  MESON_TAC[]);;

let COMMUTING_MATRIX_INV_COVARIANCE = prove
 (`!A:real^M^N.
        matrix_inv(transp A ** A) ** (transp A ** A) =
        (transp A ** A) ** matrix_inv(transp A ** A)`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM SYMMETRIC_MATRIX_INV_RMUL] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_MATRIX_INV; TRANSP_TRANSP]);;

let COMMUTING_MATRIX_INV_NORMAL = prove
 (`!A:real^N^N.
      transp A ** A = A ** transp A ==> matrix_inv A ** A = A ** matrix_inv A`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
   [GSYM MATRIX_INV_COVARIANCE_RMUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [GSYM MATRIX_INV_COVARIANCE_LMUL] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[COMMUTING_MATRIX_INV_COVARIANCE] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_ASSOC]);;

let MATRIX_MUL_INV_EQ_0 = prove
 (`!A:real^P^N B:real^N^M.
        matrix_inv A ** matrix_inv B = mat 0 <=> B ** A = mat 0`,
  let lemma = prove
   (`!A:real^P^N B:real^N^M.
        B ** A = mat 0 ==> matrix_inv A ** matrix_inv B = mat 0`,
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [MATRIX_INV_MULTIPLE_TRANP_RIGHT] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [MATRIX_INV_MULTIPLE_TRANP_LEFT] THEN
    ONCE_REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
     [GSYM MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO; TRANSP_MAT]) in
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  REWRITE_TAC[MATRIX_INV_INV]);;

let MATRIX_INV_IDEMPOTENT = prove
 (`!A:real^N^N. transp A = A /\ A ** A = A ==> matrix_inv A = A`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  ASM_REWRITE_TAC[MATRIX_TRANSP_MUL]);;

let IDEMPOTENT_MATRIX_MUL_LINV = prove
 (`!A:real^N^M.
        (matrix_inv A ** A) ** (matrix_inv A ** A) = matrix_inv A ** A`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV_MUL_OUTER]);;

let IDEMPOTENT_MATRIX_MUL_RINV = prove
 (`!A:real^N^M.
        (A ** matrix_inv A) ** (A ** matrix_inv A) = A ** matrix_inv A`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV_MUL_INNER]);;

let MATRIX_INV_MUL_LINV = prove
 (`!A:real^N^M. matrix_inv(matrix_inv A ** A) = matrix_inv A ** A`,
  GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_TRANSP_MUL; TRANSP_MATRIX_INV] THEN
  REWRITE_TAC[MATRIX_INV_MUL_INNER; MATRIX_INV_MUL_OUTER] THEN
  REWRITE_TAC[GSYM TRANSP_MATRIX_INV; GSYM MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_LMUL]);;

let MATRIX_INV_MUL_RINV = prove
 (`!A:real^N^M. matrix_inv(A ** matrix_inv A) = A ** matrix_inv A`,
  GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_TRANSP_MUL; TRANSP_MATRIX_INV] THEN
  REWRITE_TAC[MATRIX_INV_MUL_INNER; MATRIX_INV_MUL_OUTER] THEN
  REWRITE_TAC[GSYM TRANSP_MATRIX_INV; GSYM MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_INV_RMUL]);;

(* ------------------------------------------------------------------------- *)
(* Infinity norm.                                                            *)
(* ------------------------------------------------------------------------- *)

let infnorm = define
 `infnorm (x:real^N) = sup { abs(x$i) | 1 <= i /\ i <= dimindex(:N) }`;;

let NUMSEG_DIMINDEX_NONEMPTY = prove
 (`?i. i IN 1..dimindex(:N)`,
  REWRITE_TAC[MEMBER_NOT_EMPTY; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1]);;

let INFNORM_SET_IMAGE = prove
 (`{abs(x$i) | 1 <= i /\ i <= dimindex(:N)} =
   IMAGE (\i. abs(x$i)) (1..dimindex(:N))`,
  REWRITE_TAC[numseg] THEN SET_TAC[]);;

let INFNORM_SET_LEMMA = prove
 (`FINITE {abs((x:real^N)$i) | 1 <= i /\ i <= dimindex(:N)} /\
   ~({abs(x$i) | 1 <= i /\ i <= dimindex(:N)} = {})`,
  SIMP_TAC[INFNORM_SET_IMAGE; FINITE_NUMSEG; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1]);;

let INFNORM_POS_LE = prove
 (`!x. &0 <= infnorm x`,
  REWRITE_TAC[infnorm] THEN
  SIMP_TAC[REAL_LE_SUP_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[INFNORM_SET_IMAGE; NUMSEG_DIMINDEX_NONEMPTY;
              EXISTS_IN_IMAGE; REAL_ABS_POS]);;

let INFNORM_TRIANGLE = prove
 (`!x y. infnorm(x + y) <= infnorm x + infnorm y`,
  REWRITE_TAC[infnorm] THEN
  SIMP_TAC[REAL_SUP_LE_FINITE; INFNORM_SET_LEMMA] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_SUB_RADD] THEN
  SIMP_TAC[REAL_LE_SUP_FINITE; INFNORM_SET_LEMMA] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x - y <= z <=> x - z <= y`] THEN
  SIMP_TAC[REAL_LE_SUP_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[INFNORM_SET_IMAGE; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; GSYM IN_NUMSEG] THEN
  MESON_TAC[NUMSEG_DIMINDEX_NONEMPTY;
            REAL_ARITH `abs(x + y) - abs(x) <= abs(y)`]);;

let INFNORM_EQ_0 = prove
 (`!x. infnorm x = &0 <=> x = vec 0`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; INFNORM_POS_LE] THEN
  SIMP_TAC[infnorm; REAL_SUP_LE_FINITE; INFNORM_SET_LEMMA] THEN
  SIMP_TAC[FORALL_IN_IMAGE; INFNORM_SET_IMAGE; CART_EQ; VEC_COMPONENT] THEN
  REWRITE_TAC[IN_NUMSEG; REAL_ARITH `abs(x) <= &0 <=> x = &0`]);;

let INFNORM_0 = prove
 (`infnorm(vec 0) = &0`,
  REWRITE_TAC[INFNORM_EQ_0]);;

let INFNORM_NEG = prove
 (`!x. infnorm(--x) = infnorm x`,
  GEN_TAC THEN REWRITE_TAC[infnorm] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[REAL_ABS_NEG; VECTOR_NEG_COMPONENT]);;

let INFNORM_SUB = prove
 (`!x y. infnorm(x - y) = infnorm(y - x)`,
  MESON_TAC[INFNORM_NEG; VECTOR_NEG_SUB]);;

let REAL_ABS_SUB_INFNORM = prove
 (`abs(infnorm x - infnorm y) <= infnorm(x - y)`,
  MATCH_MP_TAC(REAL_ARITH
    `nx <= n + ny /\ ny <= n + nx ==> abs(nx - ny) <= n`) THEN
  MESON_TAC[INFNORM_SUB; VECTOR_SUB_ADD2; INFNORM_TRIANGLE; VECTOR_ADD_SYM]);;

let REAL_ABS_INFNORM = prove
 (`!x. abs(infnorm x) = infnorm x`,
  REWRITE_TAC[real_abs; INFNORM_POS_LE]);;

let COMPONENT_LE_INFNORM = prove
 (`!x:real^N i. 1 <= i /\ i <= dimindex (:N) ==> abs(x$i) <= infnorm x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[infnorm] THEN
  MP_TAC(SPEC `{ abs((x:real^N)$i) | 1 <= i /\ i <= dimindex(:N) }`
              SUP_FINITE) THEN
  REWRITE_TAC[INFNORM_SET_LEMMA] THEN
  SIMP_TAC[INFNORM_SET_IMAGE; FORALL_IN_IMAGE; IN_NUMSEG]);;

let INFNORM_MUL_LEMMA = prove
 (`!a x. infnorm(a % x) <= abs a * infnorm x`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [infnorm] THEN
  SIMP_TAC[REAL_SUP_LE_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; INFNORM_SET_IMAGE] THEN
  SIMP_TAC[REAL_ABS_MUL; VECTOR_MUL_COMPONENT; IN_NUMSEG] THEN
  SIMP_TAC[COMPONENT_LE_INFNORM; REAL_LE_LMUL; REAL_ABS_POS]);;

let INFNORM_MUL = prove
 (`!a x:real^N. infnorm(a % x) = abs a * infnorm x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INFNORM_0; REAL_ABS_0; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; INFNORM_MUL_LEMMA] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [GSYM VECTOR_MUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(a) * abs(inv a) * infnorm(a % x:real^N)` THEN
  ASM_SIMP_TAC[INFNORM_MUL_LEMMA; REAL_LE_LMUL; REAL_ABS_POS] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; GSYM REAL_ABS_MUL; REAL_MUL_RINV] THEN
  REAL_ARITH_TAC);;

let INFNORM_POS_LT = prove
 (`!x. &0 < infnorm x <=> ~(x = vec 0)`,
  MESON_TAC[REAL_LT_LE; INFNORM_POS_LE; INFNORM_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Prove that it differs only up to a bound from Euclidean norm.             *)
(* ------------------------------------------------------------------------- *)

let INFNORM_LE_NORM = prove
 (`!x. infnorm(x) <= norm(x)`,
  SIMP_TAC[infnorm; REAL_SUP_LE_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[COMPONENT_LE_NORM]);;

let NORM_LE_INFNORM = prove
 (`!x:real^N. norm(x) <= sqrt(&(dimindex(:N))) * infnorm(x)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o funpow 2 RAND_CONV)
   [GSYM CARD_NUMSEG_1] THEN
  REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  SIMP_TAC[DOT_POS_LE; SQRT_POS_LE; REAL_POS; REAL_LE_MUL; INFNORM_POS_LE;
           SQRT_POW_2; REAL_POW_MUL] THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_BOUND THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs(y)`) THEN
  SIMP_TAC[infnorm; REAL_LE_SUP_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Equality in Cauchy-Schwarz and triangle inequalities.                     *)
(* ------------------------------------------------------------------------- *)

let NORM_CAUCHY_SCHWARZ_EQ = prove
 (`!x:real^N y. x dot y = norm(x) * norm(y) <=> norm(x) % y = norm(y) % x`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  ASM_REWRITE_TAC[NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO;
    DOT_LZERO; DOT_RZERO; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THEN
  MP_TAC(ISPEC `norm(y:real^N) % x - norm(x:real^N) % y` DOT_EQ_0) THEN
  REWRITE_TAC[DOT_RSUB; DOT_LSUB; DOT_LMUL; DOT_RMUL; GSYM NORM_POW_2;
              REAL_POW_2; VECTOR_SUB_EQ] THEN
  REWRITE_TAC[DOT_SYM; REAL_ARITH
   `y * (y * x * x - x * d) - x * (y * d - x * y * y) =
    &2 * x * y * (x * y - d)`] THEN
  ASM_SIMP_TAC[REAL_ENTIRE; NORM_EQ_0; REAL_SUB_0; REAL_OF_NUM_EQ; ARITH] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let NORM_CAUCHY_SCHWARZ_ABS_EQ = prove
 (`!x:real^N y. abs(x dot y) = norm(x) * norm(y) <=>
                norm(x) % y = norm(y) % x \/ norm(x) % y = --norm(y) % x`,
  SIMP_TAC[REAL_ARITH `&0 <= a ==> (abs x = a <=> x = a \/ --x = a)`;
           REAL_LE_MUL; NORM_POS_LE; GSYM DOT_RNEG] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV) [GSYM NORM_NEG] THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_EQ] THEN REWRITE_TAC[NORM_NEG] THEN
  BINOP_TAC THEN VECTOR_ARITH_TAC);;

let NORM_TRIANGLE_EQ = prove
 (`!x y:real^N. norm(x + y) = norm(x) + norm(y) <=> norm(x) % y = norm(y) % x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NORM_CAUCHY_SCHWARZ_EQ] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `norm(x + y:real^N) pow 2 = (norm(x) + norm(y)) pow 2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_RING `x pow 2 = y pow 2 <=> x = y \/ x + y = &0`] THEN
    MAP_EVERY (MP_TAC o C ISPEC NORM_POS_LE)
     [`x + y:real^N`; `x:real^N`; `y:real^N`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; REAL_ARITH
     `(x + y) pow 2 = x pow 2 + y pow 2 + &2 * x * y`] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC]);;

let DIST_TRIANGLE_EQ = prove
 (`!x y z. dist(x,z) = dist(x,y) + dist(y,z) <=>
                norm (x - y) % (y - z) = norm (y - z) % (x - y)`,
  REWRITE_TAC[GSYM NORM_TRIANGLE_EQ] THEN NORM_ARITH_TAC);;

let NORM_CROSS_MULTIPLY = prove
 (`!a b x y:real^N.
        a % x = b % y /\ &0 < a /\ &0 < b
        ==> norm y % x = norm x % y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; VECTOR_MUL_RZERO] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. inv(a) % x`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
               NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Collinearity.                                                             *)
(* ------------------------------------------------------------------------- *)

let collinear = new_definition
 `collinear s <=> ?u. !x y. x IN s /\ y IN s ==> ?c. x - y = c % u`;;

let COLLINEAR_SUBSET = prove
 (`!s t. collinear t /\ s SUBSET t ==> collinear s`,
  REWRITE_TAC[collinear] THEN SET_TAC[]);;

let COLLINEAR_EMPTY = prove
 (`collinear {}`,
  REWRITE_TAC[collinear; NOT_IN_EMPTY]);;

let COLLINEAR_SING = prove
 (`!x. collinear {x}`,
  SIMP_TAC[collinear; IN_SING; VECTOR_SUB_REFL] THEN
  MESON_TAC[VECTOR_MUL_LZERO]);;

let COLLINEAR_2 = prove
 (`!x y:real^N. collinear {x,y}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[collinear; IN_INSERT; NOT_IN_EMPTY] THEN
  EXISTS_TAC `x - y:real^N` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `&0`; EXISTS_TAC `&1`; EXISTS_TAC `-- &1`; EXISTS_TAC `&0`] THEN
  VECTOR_ARITH_TAC);;

let COLLINEAR_SMALL = prove
 (`!s. FINITE s /\ CARD s <= 2 ==> collinear s`,
  REWRITE_TAC[ARITH_RULE `s <= 2 <=> s = 0 \/ s = 1 \/ s = 2`] THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; GSYM HAS_SIZE] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[COLLINEAR_EMPTY; COLLINEAR_SING; COLLINEAR_2]);;

let COLLINEAR_3 = prove
 (`!x y z. collinear {x,y,z} <=> collinear {vec 0,x - y,z - y}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[collinear; FORALL_IN_INSERT; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              NOT_IN_EMPTY] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MESON_TAC[VECTOR_ARITH `x - y = (x - y) - vec 0`;
            VECTOR_ARITH `y - x = vec 0 - (x - y)`;
            VECTOR_ARITH `x - z:real^N = (x - y) - (z - y)`]);;

let COLLINEAR_LEMMA = prove
 (`!x y:real^N. collinear {vec 0,x,y} <=>
                   x = vec 0 \/ y = vec 0 \/ ?c. y = c % x`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  TRY(ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SING; COLLINEAR_2] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[collinear] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N`
     (fun th -> MP_TAC(SPECL [`x:real^N`; `vec 0:real^N`] th) THEN
                MP_TAC(SPECL [`y:real^N`; `vec 0:real^N`] th))) THEN
    REWRITE_TAC[IN_INSERT; VECTOR_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` SUBST_ALL_TAC) THEN
    EXISTS_TAC `e / d` THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_EQ_0; DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL];
    STRIP_TAC THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `&0`; EXISTS_TAC `-- &1`; EXISTS_TAC `--c`;
      EXISTS_TAC `&1`; EXISTS_TAC `&0`; EXISTS_TAC `&1 - c`;
      EXISTS_TAC `c:real`; EXISTS_TAC `c - &1`; EXISTS_TAC `&0`] THEN
    VECTOR_ARITH_TAC]);;

let COLLINEAR_LEMMA_ALT = prove
 (`!x y. collinear {vec 0,x,y} <=> x = vec 0 \/ ?c. y = c % x`,
  REWRITE_TAC[COLLINEAR_LEMMA] THEN MESON_TAC[VECTOR_MUL_LZERO]);;

let NORM_CAUCHY_SCHWARZ_EQUAL = prove
 (`!x y:real^N. abs(x dot y) = norm(x) * norm(y) <=> collinear {vec 0,x,y}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS_EQ] THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  TRY(ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SING; COLLINEAR_2; NORM_0;
                      VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[COLLINEAR_LEMMA] THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM
       `(%) (inv(norm(x:real^N))):real^N->real^N`);
      FIRST_X_ASSUM(MP_TAC o AP_TERM
       `(%) (--inv(norm(x:real^N))):real^N->real^N`)] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LNEG] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; VECTOR_MUL_LNEG; VECTOR_MUL_LID;
                 VECTOR_ARITH `--x = --y <=> x:real^N = y`] THEN
    MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC(MESON[]
      `t = a \/ t = b ==> t % x = a % x \/ t % x = b % x`) THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG;
                REAL_ARITH `x * c = d * x <=> x * (c - d) = &0`] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; NORM_EQ_0] THEN REAL_ARITH_TAC]);;

let DOT_CAUCHY_SCHWARZ_EQUAL = prove
 (`!x y:real^N.
        (x dot y) pow 2 = (x dot x) * (y dot y) <=>
        collinear {vec 0,x,y}`,
  REWRITE_TAC[GSYM NORM_CAUCHY_SCHWARZ_EQUAL] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `&0 <= y /\ (u:real = v <=> x = abs y) ==> (u = v <=> x = y)`) THEN
  SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
  REWRITE_TAC[REAL_EQ_SQUARE_ABS] THEN REWRITE_TAC[REAL_POW_MUL; NORM_POW_2]);;

let COLLINEAR_3_EXPAND = prove
 (`!a b c:real^N. collinear{a,b,c} <=> a = c \/ ?u. b = u % a + (&1 - u) % c`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[COLLINEAR_LEMMA; VECTOR_SUB_EQ] THEN
  ASM_CASES_TAC `a:real^N = c` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `b:real^N = c` THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `u % c + (&1 - u) % c = c`] THENL
   [EXISTS_TAC `&0` THEN VECTOR_ARITH_TAC;
    AP_TERM_TAC THEN ABS_TAC THEN VECTOR_ARITH_TAC]);;

let COLLINEAR_TRIPLES = prove
 (`!s a b:real^N.
        ~(a = b)
        ==> (collinear(a INSERT b INSERT s) <=>
             !x. x IN s ==> collinear{a,b,x})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] COLLINEAR_SUBSET)) THEN
    ASM SET_TAC[];
    ONCE_REWRITE_TAC[SET_RULE `{a,b,x} = {a,x,b}`] THEN
    ASM_REWRITE_TAC[COLLINEAR_3_EXPAND] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x:real^N. x IN (a INSERT b INSERT s) ==> ?u. x = u % a + (&1 - u) % b`
    MP_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_INSERT] THEN CONJ_TAC THENL
       [EXISTS_TAC `&1` THEN VECTOR_ARITH_TAC;
        EXISTS_TAC `&0` THEN VECTOR_ARITH_TAC];
      POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
      REWRITE_TAC[collinear] THEN EXISTS_TAC `b - a:real^N` THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:real^N` th) THEN MP_TAC(SPEC
        `y:real^N` th)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH
       `(u % a + (&1 - u) % b) - (v % a + (&1 - v) % b):real^N =
        (v - u) % (b - a)`] THEN
      MESON_TAC[]]]);;

let COLLINEAR_4_3 = prove
 (`!a b c d:real^N.
        ~(a = b)
        ==> (collinear {a,b,c,d} <=> collinear{a,b,c} /\ collinear{a,b,d})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{c:real^N,d}`; `a:real^N`; `b:real^N`]
    COLLINEAR_TRIPLES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let COLLINEAR_3_TRANS = prove
 (`!a b c d:real^N.
        collinear{a,b,c} /\ collinear{b,c,d} /\ ~(b = c) ==> collinear{a,b,d}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COLLINEAR_SUBSET THEN
  EXISTS_TAC `{b:real^N,c,a,d}` THEN ASM_SIMP_TAC[COLLINEAR_4_3] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[INSERT_AC]);;

let ORTHOGONAL_TO_ORTHOGONAL_2D = prove
 (`!x y z:real^2.
     ~(x = vec 0) /\ orthogonal x y /\ orthogonal x z
     ==> collinear {vec 0,y,z}`,
  REWRITE_TAC[orthogonal; GSYM DOT_CAUCHY_SCHWARZ_EQUAL; GSYM DOT_EQ_0] THEN
  REWRITE_TAC[DOT_2] THEN CONV_TAC REAL_RING);;

let COLLINEAR_3_2D = prove
 (`!x y z:real^2. collinear{x,y,z} <=>
                  (z$1 - x$1) * (y$2 - x$2) = (y$1 - x$1) * (z$2 - x$2)`,
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
  REWRITE_TAC[DOT_2; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING);;

let COLLINEAR_3_DOT_MULTIPLES = prove
 (`!a b c:real^N.
        collinear {a,b,c} <=>
        ((b - a) dot (b - a)) % (c - a) = ((c - a) dot (b - a)) % (b - a)`,
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC; DOT_RZERO; VECTOR_MUL_LZERO;
                    VECTOR_SUB_REFL];
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL; GSYM DOT_EQ_0] THEN
    REWRITE_TAC[GSYM DOT_EQ_0; DOT_RSUB; DOT_LSUB; DOT_RMUL; DOT_LMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* Between-ness.                                                             *)
(* ------------------------------------------------------------------------- *)

let between = new_definition
 `between x (a,b) <=> dist(a,b) = dist(a,x) + dist(x,b)`;;

let BETWEEN_REFL = prove
 (`!a b. between a (a,b) /\ between b (a,b) /\ between a (a,a)`,
  REWRITE_TAC[between] THEN NORM_ARITH_TAC);;

let BETWEEN_REFL_EQ = prove
 (`!a x. between x (a,a) <=> x = a`,
  REWRITE_TAC[between] THEN NORM_ARITH_TAC);;

let BETWEEN_SYM = prove
 (`!a b x. between x (a,b) <=> between x (b,a)`,
  REWRITE_TAC[between] THEN NORM_ARITH_TAC);;

let BETWEEN_ANTISYM = prove
 (`!a b c. between a (b,c) /\ between b (a,c) ==> a = b`,
  REWRITE_TAC[between; DIST_SYM] THEN NORM_ARITH_TAC);;

let BETWEEN_TRANS = prove
 (`!a b c d. between a (b,c) /\ between d (a,c) ==> between d (b,c)`,
  REWRITE_TAC[between; DIST_SYM] THEN NORM_ARITH_TAC);;

let BETWEEN_TRANS_2 = prove
 (`!a b c d. between a (b,c) /\ between d (a,b) ==> between a (c,d)`,
  REWRITE_TAC[between; DIST_SYM] THEN NORM_ARITH_TAC);;

let BETWEEN_NORM = prove
 (`!a b x:real^N.
     between x (a,b) <=> norm(x - a) % (b - x) = norm(b - x) % (x - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[between; DIST_TRIANGLE_EQ] THEN
  REWRITE_TAC[NORM_SUB] THEN VECTOR_ARITH_TAC);;

let BETWEEN_DOT = prove
 (`!a b x:real^N.
     between x (a,b) <=> (x - a) dot (b - x) = norm(x - a) * norm(b - x)`,
  REWRITE_TAC[BETWEEN_NORM; NORM_CAUCHY_SCHWARZ_EQ]);;

let BETWEEN_EXISTS_EXTENSION = prove
 (`!a b x:real^N.
        between b (a,x) /\ ~(b = a) ==> ?d. &0 <= d /\ x = b + d % (b - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BETWEEN_NORM] THEN STRIP_TAC THEN
  EXISTS_TAC `norm(x - b:real^N) / norm(b - a)` THEN
  SIMP_TAC[REAL_LE_DIV; NORM_POS_LE] THEN FIRST_X_ASSUM
   (MP_TAC o AP_TERM `(%) (inv(norm(b - a:real^N))):real^N->real^N`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; NORM_EQ_0; VECTOR_SUB_EQ] THEN
  VECTOR_ARITH_TAC);;

let BETWEEN_IMP_COLLINEAR = prove
 (`!a b x:real^N. between x (a,b) ==> collinear {a,x,b}`,
  REPEAT GEN_TAC THEN MAP_EVERY
   (fun t -> ASM_CASES_TAC t THEN
             TRY(ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2] THEN NO_TAC))
   [`x:real^N = a`; `x:real^N = b`; `a:real^N = b`] THEN
  ONCE_REWRITE_TAC[COLLINEAR_3; BETWEEN_NORM] THEN
  DISCH_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  REPEAT DISJ2_TAC THEN EXISTS_TAC `--(norm(b - x:real^N) / norm(x - a))` THEN
  MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `norm(x - a:real^N)` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
  VECTOR_ARITH_TAC);;

let COLLINEAR_BETWEEN_CASES = prove
 (`!a b c:real^N.
        collinear {a,b,c} <=>
        between a (b,c) \/ between b (c,a) \/ between c (a,b)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_EXPAND] THEN
    ASM_CASES_TAC `c:real^N = a` THEN ASM_REWRITE_TAC[BETWEEN_REFL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[between; dist] THEN
    REWRITE_TAC[VECTOR_ARITH `(u % a + (&1 - u) % c) - c = --u % (c - a)`;
      VECTOR_ARITH `(u % a + (&1 - u) % c) - a = (&1 - u) % (c - a)`;
      VECTOR_ARITH `c - (u % a + (&1 - u) % c) = u % (c - a)`;
      VECTOR_ARITH `a - (u % a + (&1 - u) % c) = (u - &1) % (c - a)`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBST1_TAC(NORM_ARITH `norm(a - c:real^N) = norm(c - a)`) THEN
    REWRITE_TAC[REAL_ARITH `a * c + c = (a + &1) * c`; GSYM REAL_ADD_RDISTRIB;
                REAL_ARITH `c + a * c = (a + &1) * c`] THEN
    ASM_REWRITE_TAC[REAL_EQ_MUL_RCANCEL;
                    REAL_RING `n = x * n <=> n = &0 \/ x = &1`] THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN REAL_ARITH_TAC;
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (MP_TAC o MATCH_MP
      BETWEEN_IMP_COLLINEAR)) THEN
    REWRITE_TAC[INSERT_AC]]);;

let COLLINEAR_DIST_BETWEEN = prove
 (`!a b x. collinear {x,a,b} /\
           dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)
           ==> between x (a,b)`,
  SIMP_TAC[COLLINEAR_BETWEEN_CASES; between; DIST_SYM] THEN NORM_ARITH_TAC);;

let BETWEEN_COLLINEAR_DIST_EQ = prove
 (`!a b x:real^N.
        between x (a,b) <=>
        collinear {a, x, b} /\
        dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[BETWEEN_IMP_COLLINEAR] THEN REWRITE_TAC[between] THEN
    NORM_ARITH_TAC;
    MESON_TAC[COLLINEAR_DIST_BETWEEN; INSERT_AC]]);;

let COLLINEAR_1 = prove
 (`!s:real^1->bool. collinear s`,
  GEN_TAC THEN MATCH_MP_TAC COLLINEAR_SUBSET THEN
  EXISTS_TAC `(vec 0:real^1) INSERT (vec 1) INSERT s` THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) COLLINEAR_TRIPLES o snd) THEN
  REWRITE_TAC[VEC_EQ; ARITH_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COLLINEAR_BETWEEN_CASES] THEN
  REWRITE_TAC[between; DIST_REAL; GSYM drop; DROP_VEC; REAL_ABS_NUM] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Midpoint between two points.                                              *)
(* ------------------------------------------------------------------------- *)

let midpoint = new_definition
 `midpoint(a,b) = inv(&2) % (a + b)`;;

let MIDPOINT_REFL = prove
 (`!x. midpoint(x,x) = x`,
  REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC);;

let MIDPOINT_SYM = prove
 (`!a b. midpoint(a,b) = midpoint(b,a)`,
  REWRITE_TAC[midpoint; VECTOR_ADD_SYM]);;

let DIST_MIDPOINT = prove
 (`!a b. dist(a,midpoint(a,b)) = dist(a,b) / &2 /\
         dist(b,midpoint(a,b)) = dist(a,b) / &2 /\
         dist(midpoint(a,b),a) = dist(a,b) / &2 /\
         dist(midpoint(a,b),b) = dist(a,b) / &2`,
  REWRITE_TAC[midpoint] THEN NORM_ARITH_TAC);;

let MIDPOINT_EQ_ENDPOINT = prove
 (`!a b. (midpoint(a,b) = a <=> a = b) /\
         (midpoint(a,b) = b <=> a = b) /\
         (a = midpoint(a,b) <=> a = b) /\
         (b = midpoint(a,b) <=> a = b)`,
  REWRITE_TAC[midpoint] THEN NORM_ARITH_TAC);;

let BETWEEN_MIDPOINT = prove
 (`!a b. between (midpoint(a,b)) (a,b) /\ between (midpoint(a,b)) (b,a)`,
  REWRITE_TAC[between; midpoint] THEN NORM_ARITH_TAC);;

let MIDPOINT_LINEAR_IMAGE = prove
 (`!f a b. linear f ==> midpoint(f a,f b) = f(midpoint(a,b))`,
  SIMP_TAC[midpoint; LINEAR_ADD; LINEAR_CMUL]);;

let COLLINEAR_MIDPOINT = prove
 (`!a b. collinear{a,midpoint(a,b),b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_3_EXPAND; midpoint] THEN
  DISJ2_TAC THEN EXISTS_TAC `&1 / &2` THEN VECTOR_ARITH_TAC);;

let MIDPOINT_COLLINEAR = prove
 (`!a b c:real^N.
        ~(a = c)
        ==> (b = midpoint(a,c) <=> collinear{a,b,c} /\ dist(a,b) = dist(b,c))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (b ==> (a <=> c)) ==> (a <=> b /\ c)`) THEN
  SIMP_TAC[COLLINEAR_MIDPOINT] THEN ASM_REWRITE_TAC[COLLINEAR_3_EXPAND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[midpoint; dist] THEN
  REWRITE_TAC
   [VECTOR_ARITH `a - (u % a + (&1 - u) % c) = (&1 - u) % (a - c)`;
    VECTOR_ARITH `(u % a + (&1 - u) % c) - c = u % (a - c)`;
    VECTOR_ARITH `u % a + (&1 - u) % c = inv (&2) % (a + c) <=>
                  (u - &1 / &2) % (a - c) = vec 0`] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_EQ_MUL_RCANCEL; NORM_EQ_0; VECTOR_SUB_EQ;
               VECTOR_MUL_EQ_0] THEN
  REAL_ARITH_TAC);;

let MIDPOINT_BETWEEN = prove
 (`!a b c:real^N.
        b = midpoint (a,c) <=> between b (a,c) /\ dist (a,b) = dist (b,c)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = c` THENL
   [ASM_SIMP_TAC[BETWEEN_REFL_EQ; MIDPOINT_REFL; DIST_SYM]; ALL_TAC] THEN
  EQ_TAC THEN SIMP_TAC[BETWEEN_MIDPOINT; DIST_MIDPOINT] THEN
  ASM_MESON_TAC[MIDPOINT_COLLINEAR; BETWEEN_IMP_COLLINEAR]);;

(* ------------------------------------------------------------------------- *)
(* General "one way" lemma for properties preserved by injective map.        *)
(* ------------------------------------------------------------------------- *)

let WLOG_LINEAR_INJECTIVE_IMAGE_2 = prove
 (`!P Q. (!f s. P s /\ linear f ==> Q(IMAGE f s)) /\
         (!g t. Q t /\ linear g ==> P(IMAGE g t))
         ==> !f:real^M->real^N.
                linear f /\ (!x y. f x = f y ==> x = y)
                ==> !s. Q(IMAGE f s) <=> P s`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`g:real^N->real^M`; `IMAGE (f:real^M->real^N) s`]) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID]);;

let WLOG_LINEAR_INJECTIVE_IMAGE_2_ALT = prove
 (`!P Q f s. (!h u. P u /\ linear h ==> Q(IMAGE h u)) /\
             (!g t. Q t /\ linear g ==> P(IMAGE g t)) /\
             linear f /\ (!x y. f x = f y ==> x = y)
             ==> (Q(IMAGE f s) <=> P s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     WLOG_LINEAR_INJECTIVE_IMAGE_2) THEN
  ASM_REWRITE_TAC[]);;

let WLOG_LINEAR_INJECTIVE_IMAGE = prove
 (`!P. (!f s. P s /\ linear f ==> P(IMAGE f s))
       ==> !f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                              ==> !s. P(IMAGE f s) <=> P s`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WLOG_LINEAR_INJECTIVE_IMAGE_2 THEN
  ASM_REWRITE_TAC[]);;

let WLOG_LINEAR_INJECTIVE_IMAGE_ALT = prove
 (`!P f s. (!g t. P t /\ linear g ==> P(IMAGE g t)) /\
           linear f /\ (!x y. f x = f y ==> x = y)
           ==> (P(IMAGE f s) <=> P s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     WLOG_LINEAR_INJECTIVE_IMAGE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Inference rule to apply it conveniently.                                  *)
(*                                                                           *)
(*   |- !f s. P s /\ linear f ==> P(IMAGE f s)  [or /\ commuted]             *)
(* ---------------------------------------------------------------           *)
(*   |- !f s. linear f /\ (!x y. f x = f y ==> x = y)                        *)
(*            ==> (Q(IMAGE f s) <=> P s)                                     *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVARIANT_RULE th =
  let [f;s] = fst(strip_forall(concl th)) in
  let (rm,rn) = dest_fun_ty (type_of f) in
  let m = last(snd(dest_type rm)) and n = last(snd(dest_type rn)) in
  let th' = INST_TYPE [m,n; n,m] th in
  let th0 = CONJ th th' in
  let th1 = try MATCH_MP WLOG_LINEAR_INJECTIVE_IMAGE_2 th0
            with Failure _ ->
                MATCH_MP WLOG_LINEAR_INJECTIVE_IMAGE_2
            (GEN_REWRITE_RULE (BINOP_CONV o ONCE_DEPTH_CONV) [CONJ_SYM] th0) in
  GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_FORALL_THM] th1;;

(* ------------------------------------------------------------------------- *)
(* Immediate application.                                                    *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (subspace (IMAGE f s) <=> subspace s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE SUBSPACE_LINEAR_IMAGE));;

(* ------------------------------------------------------------------------- *)
(* Storage of useful "invariance under linear map / translation" theorems.   *)
(* ------------------------------------------------------------------------- *)

let invariant_under_linear = ref([]:thm list);;

let invariant_under_translation = ref([]:thm list);;

let scaling_theorems = ref([]:thm list);;

(* ------------------------------------------------------------------------- *)
(* Scaling theorems and derivation from linear invariance.                   *)
(* ------------------------------------------------------------------------- *)

let LINEAR_SCALING = prove
 (`!c. linear(\x:real^N. c % x)`,
  REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC);;

let INJECTIVE_SCALING = prove
 (`!c. (!x y:real^N. c % x = c % y ==> x = y) <=> ~(c = &0)`,
  GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
  ASM_CASES_TAC `c:real = &0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^N`; `vec 1:real^N`]) THEN
  REWRITE_TAC[VEC_EQ; ARITH]);;

let SURJECTIVE_SCALING = prove
 (`!c. (!y:real^N. ?x. c % x = y) <=> ~(c = &0)`,
  ASM_SIMP_TAC[LINEAR_SURJECTIVE_IFF_INJECTIVE; LINEAR_SCALING] THEN
  REWRITE_TAC[INJECTIVE_SCALING]);;

let SCALING_INVARIANT =
  let pths = (CONJUNCTS o UNDISCH o prove)
   (`&0 < c
     ==> linear(\x:real^N. c % x) /\
         (!x y:real^N. c % x = c % y ==> x = y) /\
         (!y:real^N. ?x. c % x = y)`,
    SIMP_TAC[REAL_LT_IMP_NZ; LINEAR_SCALING;
             INJECTIVE_SCALING; SURJECTIVE_SCALING])
  and sc_tm = `\x:real^N. c % x`
  and sa_tm = `&0:real < c`
  and c_tm = `c:real` in
  fun th ->
    let ith = BETA_RULE(ISPEC sc_tm th) in
    let avs,bod = strip_forall(concl ith) in
    let cjs = conjuncts(lhand bod) in
    let cths = map (fun t -> find(fun th -> aconv (concl th) t) pths) cjs in
    let oth = MP (SPECL avs ith) (end_itlist CONJ cths) in
    GEN c_tm (DISCH sa_tm (GENL avs oth));;

(* ------------------------------------------------------------------------- *)
(* Augmentation of the lists. The "add_linear_invariants" also updates       *)
(* the scaling theorems automatically, so only a few of those will need      *)
(* to be added explicitly.                                                   *)
(* ------------------------------------------------------------------------- *)

let add_scaling_theorems thl =
  (scaling_theorems := (!scaling_theorems) @ thl);;

let add_linear_invariants thl =
  ignore(mapfilter (fun th -> add_scaling_theorems[SCALING_INVARIANT th]) thl);
  (invariant_under_linear := (!invariant_under_linear) @ thl);;

let add_translation_invariants thl =
 (invariant_under_translation := (!invariant_under_translation) @ thl);;

(* ------------------------------------------------------------------------- *)
(* Start with some basic set equivalences.                                   *)
(* We give them all an injectivity hypothesis even if it's not necessary.    *)
(* For just the intersection theorem we add surjectivity (more manageable    *)
(* than assuming that the set isn't empty).                                  *)
(* ------------------------------------------------------------------------- *)

let th_sets = prove
 (`!f. (!x y. f x = f y ==> x = y)
       ==> (if p then f x else f y) = f(if p then x else y) /\
           (if p then IMAGE f s else IMAGE f t) =
           IMAGE f (if p then s else t) /\
           (f x) INSERT (IMAGE f s) = IMAGE f (x INSERT s) /\
           (IMAGE f s) DELETE (f x) = IMAGE f (s DELETE x) /\
           (IMAGE f s) INTER (IMAGE f t) = IMAGE f (s INTER t) /\
           (IMAGE f s) UNION (IMAGE f t) = IMAGE f (s UNION t) /\
           UNIONS(IMAGE (IMAGE f) u) = IMAGE f (UNIONS u) /\
           (IMAGE f s) DIFF (IMAGE f t) = IMAGE f (s DIFF t) /\
           (IMAGE f s (f x) <=> s x) /\
           ((f x) IN (IMAGE f s) <=> x IN s) /\
           ((f o xs) (n:num) = f(xs n)) /\
           ((f o pt) (tt:real^1) = f(pt tt)) /\
           (DISJOINT (IMAGE f s) (IMAGE f t) <=> DISJOINT s t) /\
           ((IMAGE f s) SUBSET (IMAGE f t) <=> s SUBSET t) /\
           ((IMAGE f s) PSUBSET (IMAGE f t) <=> s PSUBSET t) /\
           (IMAGE f s = IMAGE f t <=> s = t) /\
           ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n) /\
           (FINITE(IMAGE f s) <=> FINITE s) /\
           (INFINITE(IMAGE f s) <=> INFINITE s) /\
           (COUNTABLE(IMAGE f s) <=> COUNTABLE s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_UNIONS] THEN
  REWRITE_TAC[o_THM; MESON[IN] `IMAGE f s y <=> y IN IMAGE f s`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[INFINITE; TAUT `(~p <=> ~q) <=> (p <=> q)`] THEN
  REPLICATE_TAC 11 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[HAS_SIZE] THEN
  ASM_MESON_TAC[COUNTABLE_IMAGE_INJ_EQ;
                FINITE_IMAGE_INJ_EQ; CARD_IMAGE_INJ]) in
let f = `f:real^M->real^N`
and imf = `IMAGE (f:real^M->real^N)`
and a = `a:real^N`
and ima = `IMAGE (\x:real^N. a + x)`
and vth = VECTOR_ARITH `!x y. a + x:real^N = a + y ==> x = y` in
let th1 = UNDISCH(ISPEC f th_sets)
and th1' = UNDISCH
 (GEN_REWRITE_RULE LAND_CONV [INJECTIVE_IMAGE] (ISPEC imf th_sets))
and th2 = MATCH_MP th_sets vth
and th2' = MATCH_MP
  (BETA_RULE(GEN_REWRITE_RULE LAND_CONV [INJECTIVE_IMAGE] (ISPEC ima th_sets)))
  vth in
let fn a th = GENL (a::subtract (frees(concl th)) [a]) th in
add_linear_invariants(map (fn f o DISCH_ALL) (CONJUNCTS th1 @ CONJUNCTS th1')),
add_translation_invariants(map (fn a) (CONJUNCTS th2 @ CONJUNCTS th2'));;

let th_set = prove
 (`!f:A->B s. (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
              ==> INTERS (IMAGE (IMAGE f) s) = IMAGE f (INTERS s)`,
  REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]) in
let th_vec = prove
 (`!a:real^N s.
    INTERS (IMAGE (IMAGE (\x. a + x)) s) = IMAGE (\x. a + x) (INTERS s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC th_set THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = y <=> x = y - a`; EXISTS_REFL]) in
add_linear_invariants [th_set],add_translation_invariants[th_vec];;

(* ------------------------------------------------------------------------- *)
(* Now add arithmetical equivalences.                                        *)
(* ------------------------------------------------------------------------- *)

let SAME_NORM_SAME_DOT = prove
 (`!f:real^M->real^N g:real^M->real^P x y.
     linear f /\ linear g /\ (!x. norm(f x) = norm(g x))
     ==> (f x) dot (f y) = (g x) dot (g y)`,
  REWRITE_TAC[NORM_EQ] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x + y:real^M`) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th])) THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_RADD] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let PRESERVES_NORM_PRESERVES_DOT = prove
 (`!f:real^M->real^N x y.
     linear f /\ (!x. norm(f x) = norm x)
     ==> (f x) dot (f y) = x dot y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `\x:real^M. x`]
        SAME_NORM_SAME_DOT) THEN
  ASM_SIMP_TAC[LINEAR_ID]);;

let PRESEVES_NORM_PRESERVES_DIST = prove
 (`!f:real^M->real^N.
        linear f /\ (!x. norm(f x) = norm x)
        ==> !x y. dist(f x,f y) = dist(x,y)`,
  REWRITE_TAC[dist] THEN MESON_TAC[LINEAR_SUB]);;

let PRESERVES_NORM_INJECTIVE = prove
 (`!f:real^M->real^N.
     linear f /\ (!x. norm(f x) = norm x)
     ==> !x y. f x = f y ==> x = y`,
  SIMP_TAC[LINEAR_INJECTIVE_0; GSYM NORM_EQ_0]);;

let ORTHOGONAL_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N x y.
     linear f /\ (!x. norm(f x) = norm x)
     ==> (orthogonal (f x) (f y) <=> orthogonal x y)`,
  SIMP_TAC[orthogonal; PRESERVES_NORM_PRESERVES_DOT]);;

let NORMAL_MATRIX_IFF_SAME_NORM_TRANSP,NORMAL_MATRIX_IFF_SAME_DOT_TRANSP =
    (CONJ_PAIR o prove)
 (`(!A:real^N^N.
         transp A ** A = A ** transp A <=>
         !x. norm(transp A ** x) = norm(A ** x)) /\
   (!A:real^N^N.
         transp A ** A = A ** transp A <=>
         !x y. (transp A ** x) dot (transp A ** y) = (A ** x) dot (A ** y))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC
   (TAUT `(q <=> r) /\ (p <=> r) ==> (p <=> q) /\ (p <=> r)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THENL [ALL_TAC; SIMP_TAC[NORM_EQ]] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SAME_NORM_SAME_DOT THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
    GEN_REWRITE_TAC (RAND_CONV o funpow 2 BINDER_CONV o RAND_CONV)
     [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN REWRITE_TAC[GSYM DOT_LSUB] THEN
    REWRITE_TAC[FORALL_DOT_EQ_0; MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM MATRIX_EQ_0; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
    REWRITE_TAC[MATRIX_SUB_EQ] THEN MESON_TAC[]]);;

let NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT = prove
 (`!A x:real^N.
        transp A ** A = A ** transp A
        ==> (transp A ** x = vec 0 <=> A ** x = vec 0)`,
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MESON_TAC[NORMAL_MATRIX_IFF_SAME_NORM_TRANSP]);;

let NORMAL_MATRIX_KERNEL_TRANSP = prove
 (`!A:real^N^N.
        transp A ** A = A ** transp A
        ==> {x | transp A ** x = vec 0} = {x | A ** x = vec 0}`,
  SIMP_TAC[EXTENSION; IN_ELIM_THM; NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT]);;

add_linear_invariants
 [GSYM LINEAR_ADD;
  GSYM LINEAR_CMUL;
  GSYM LINEAR_SUB;
  GSYM LINEAR_NEG;
  MIDPOINT_LINEAR_IMAGE;
  MESON[] `!f:real^M->real^N x.
                (!x. norm(f x) = norm x) ==> norm(f x) = norm x`;
  PRESERVES_NORM_PRESERVES_DOT;
  MESON[dist; LINEAR_SUB]
    `!f:real^M->real^N x y.
        linear f /\ (!x. norm(f x) = norm x)
        ==> dist(f x,f y) = dist(x,y)`;
  MESON[] `!f:real^M->real^N x y.
                (!x y. f x = f y ==> x = y) ==> (f x = f y <=> x = y)`;
  SUBSPACE_LINEAR_IMAGE_EQ;
  ORTHOGONAL_LINEAR_IMAGE_EQ;
  SPAN_LINEAR_IMAGE;
  DEPENDENT_LINEAR_IMAGE_EQ;
  INDEPENDENT_LINEAR_IMAGE_EQ;
  DIM_INJECTIVE_LINEAR_IMAGE];;

add_translation_invariants
 [VECTOR_ARITH `!a x y. a + x:real^N = a + y <=> x = y`;
  NORM_ARITH `!a x y. dist(a + x,a + y) = dist(x,y)`;
  VECTOR_ARITH `!a x y. &1 / &2 % ((a + x) + (a + y)) = a + &1 / &2 % (x + y)`;
  VECTOR_ARITH `!a x y. inv(&2) % ((a + x) + (a + y)) = a + inv(&2) % (x + y)`;
  VECTOR_ARITH `!a x y. (a + x) - (a + y):real^N = x - y`;
  (EQT_ELIM o (REWRITE_CONV[midpoint] THENC(EQT_INTRO o NORM_ARITH)))
               `!a x y. midpoint(a + x,a + y) = a + midpoint(x,y)`;
  (EQT_ELIM o (REWRITE_CONV[between] THENC(EQT_INTRO o NORM_ARITH)))
               `!a x y z. between (a + x) (a + y,a + z) <=> between x (y,z)`];;

let th = prove
 (`!a s b c:real^N. (a + b) + c IN IMAGE (\x. a + x) s <=> (b + c) IN s`,
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH
    `(a + b) + c:real^N = a + x <=> x = b + c`] THEN
  MESON_TAC[]) in
add_translation_invariants [th];;

(* ------------------------------------------------------------------------- *)
(* A few for lists.                                                          *)
(* ------------------------------------------------------------------------- *)

let MEM_TRANSLATION = prove
 (`!a:real^N x l. MEM (a + x) (MAP (\x. a + x) l) <=> MEM x l`,
  REWRITE_TAC[MEM_MAP; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  MESON_TAC[]);;

add_translation_invariants [MEM_TRANSLATION];;

let MEM_LINEAR_IMAGE = prove
 (`!f:real^M->real^N x l.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (MEM (f x) (MAP f l) <=> MEM x l)`,
  REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]);;

add_linear_invariants [MEM_LINEAR_IMAGE];;

let LENGTH_TRANSLATION = prove
 (`!a:real^N l. LENGTH(MAP (\x. a + x) l) = LENGTH l`,
  REWRITE_TAC[LENGTH_MAP]) in
add_translation_invariants [LENGTH_TRANSLATION];;

let LENGTH_LINEAR_IMAGE = prove
 (`!f:real^M->real^N l. linear f ==> LENGTH(MAP f l) = LENGTH l`,
  REWRITE_TAC[LENGTH_MAP]) in
add_linear_invariants [LENGTH_LINEAR_IMAGE];;

let CONS_TRANSLATION = prove
 (`!a:real^N h t.
     CONS ((\x. a + x) h) (MAP (\x. a + x) t) = MAP (\x. a + x) (CONS h t)`,
  REWRITE_TAC[MAP]) in
add_translation_invariants [CONS_TRANSLATION];;

let CONS_LINEAR_IMAGE = prove
 (`!f:real^M->real^N h t.
     linear f ==> CONS (f h) (MAP f t) = MAP f (CONS h t)`,
  REWRITE_TAC[MAP]) in
add_linear_invariants [CONS_LINEAR_IMAGE];;

let APPEND_TRANSLATION = prove
 (`!a:real^N l1 l2.
     APPEND (MAP (\x. a + x) l1) (MAP (\x. a + x) l2) =
     MAP (\x. a + x) (APPEND l1 l2)`,
  REWRITE_TAC[MAP_APPEND]) in
add_translation_invariants [APPEND_TRANSLATION];;

let APPEND_LINEAR_IMAGE = prove
 (`!f:real^M->real^N l1 l2.
     linear f ==> APPEND (MAP f l1) (MAP f l2) = MAP f (APPEND l1 l2)`,
  REWRITE_TAC[MAP_APPEND]) in
add_linear_invariants [APPEND_LINEAR_IMAGE];;

let REVERSE_TRANSLATION = prove
 (`!a:real^N l. REVERSE(MAP (\x. a + x) l) = MAP (\x. a + x) (REVERSE l)`,
  REWRITE_TAC[MAP_REVERSE]) in
add_translation_invariants [REVERSE_TRANSLATION];;

let REVERSE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N l. linear f ==> REVERSE(MAP f l) = MAP f (REVERSE l)`,
  REWRITE_TAC[MAP_REVERSE]) in
add_linear_invariants [REVERSE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* A few scaling theorems that don't come from invariance theorems. Most are *)
(* artificially weak with 0 < c hypotheses, so we don't bind them to names.  *)
(* ------------------------------------------------------------------------- *)

let DOT_SCALING = prove
 (`!c. &0 < c ==> !x y. (c % x) dot (c % y) = c pow 2 * (x dot y)`,
  REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC) in
add_scaling_theorems [DOT_SCALING];;

let DIST_SCALING = prove
 (`!c. &0 < c ==> !x y. dist(c % x,c % y) = c * dist(x,y)`,
  SIMP_TAC[DIST_MUL; REAL_ARITH `&0 < c ==> abs c = c`]) in
add_scaling_theorems [DIST_SCALING];;

let ORTHOGONAL_SCALING = prove
 (`!c. &0 < c ==> !x y. orthogonal (c % x) (c % y) <=> orthogonal x y`,
  REWRITE_TAC[orthogonal; DOT_LMUL; DOT_RMUL] THEN CONV_TAC REAL_FIELD) in
add_scaling_theorems [ORTHOGONAL_SCALING];;

let NORM_SCALING = prove
 (`!c. &0 < c ==> !x. norm(c % x) = c * norm x`,
  SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < c ==> abs c = c`]) in
add_scaling_theorems [NORM_SCALING];;

add_scaling_theorems
  [REAL_ARITH `!c. &0 < c ==> !a b. a * c * b = c * a * b`;
   REAL_ARITH `!c. &0 < c ==> !a b. c * a + c * b = c * (a + b)`;
   REAL_ARITH `!c. &0 < c ==> !a b. c * a - c * b = c * (a - b)`;
   REAL_FIELD `!c. &0 < c ==> !a b. c * a = c * b <=> a = b`;
   MESON[REAL_LT_LMUL_EQ] `!c. &0 < c ==> !a b. c * a < c * b <=> a < b`;
   MESON[REAL_LE_LMUL_EQ] `!c. &0 < c ==> !a b. c * a <= c * b <=> a <= b`;
   MESON[REAL_LT_LMUL_EQ; real_gt]
     `!c. &0 < c ==> !a b. c * a > c * b <=> a > b`;
   MESON[REAL_LE_LMUL_EQ; real_ge]
     `!c. &0 < c ==> !a b. c * a >= c * b <=> a >= b`;
   MESON[REAL_POW_MUL]
    `!c. &0 < c ==> !a n. (c * a) pow n = c pow n * a pow n`;
   REAL_ARITH `!c. &0 < c ==> !a b n. a * c pow n * b = c pow n * a * b`;
   REAL_ARITH
    `!c. &0 < c ==> !a b n. c pow n * a + c pow n * b = c pow n * (a + b)`;
   REAL_ARITH
    `!c. &0 < c ==> !a b n. c pow n * a - c pow n * b = c pow n * (a - b)`;
   MESON[REAL_POW_LT; REAL_EQ_LCANCEL_IMP; REAL_LT_IMP_NZ]
    `!c. &0 < c ==> !a b n. c pow n * a = c pow n * b <=> a = b`;
   MESON[REAL_LT_LMUL_EQ; REAL_POW_LT]
     `!c. &0 < c ==> !a b n. c pow n * a < c pow n * b <=> a < b`;
   MESON[REAL_LE_LMUL_EQ; REAL_POW_LT]
     `!c. &0 < c ==> !a b n. c pow n * a <= c pow n * b <=> a <= b`;
   MESON[REAL_LT_LMUL_EQ; real_gt; REAL_POW_LT]
     `!c. &0 < c ==> !a b n. c pow n * a > c pow n * b <=> a > b`;
   MESON[REAL_LE_LMUL_EQ; real_ge; REAL_POW_LT]
     `!c. &0 < c ==> !a b n. c pow n * a >= c pow n * b <=> a >= b`];;

(* ------------------------------------------------------------------------- *)
(* Theorem deducing quantifier mappings from surjectivity.                   *)
(* ------------------------------------------------------------------------- *)

let QUANTIFY_SURJECTION_THM = prove
 (`!f:A->B.
        (!y. ?x. f x = y)
        ==> ((!P. (!x. P x) <=> (!x. P (f x))) /\
             (!P. (?x. P x) <=> (?x. P (f x))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE f s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE f s)))) /\
            (!P. {x | P x} = IMAGE f {x | P(f x)})`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SURJECTIVE_RIGHT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  SUBGOAL_THEN `!s. IMAGE (f:A->B) (IMAGE g s) = s` ASSUME_TAC THENL
   [ASM SET_TAC[]; CONJ_TAC THENL [ASM MESON_TAC[]; ASM SET_TAC[]]]);;

let QUANTIFY_SURJECTION_HIGHER_THM = prove
 (`!f:A->B.
        (!y. ?x. f x = y)
        ==> ((!P. (!x. P x) <=> (!x. P (f x))) /\
             (!P. (?x. P x) <=> (?x. P (f x))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE f s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE f s))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE (IMAGE f) s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE (IMAGE f) s))) /\
             (!P. (!g:real^1->B. P g) <=> (!g. P(f o g))) /\
             (!P. (?g:real^1->B. P g) <=> (?g. P(f o g))) /\
             (!P. (!g:num->B. P g) <=> (!g. P(f o g))) /\
             (!P. (?g:num->B. P g) <=> (?g. P(f o g))) /\
             (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
             (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
            ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
             (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
             (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))`,
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  ASM_REWRITE_TAC[GSYM SURJECTIVE_FORALL_THM; GSYM SURJECTIVE_EXISTS_THM;
            GSYM SURJECTIVE_IMAGE_THM; SURJECTIVE_IMAGE; SURJECTIVE_MAP] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM SKOLEM_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Apply such quantifier and set expansions once per level at depth.         *)
(* In the PARTIAL version, avoid expanding named variables in list.          *)
(* ------------------------------------------------------------------------- *)

let PARTIAL_EXPAND_QUANTS_CONV avoid th =
  let ath,sth = CONJ_PAIR th in
  let conv1 = GEN_REWRITE_CONV I [ath]
  and conv2 = GEN_REWRITE_CONV I [sth] in
  let conv1' tm =
    let th = conv1 tm in
    if mem (fst(dest_var(fst(dest_abs(rand tm))))) avoid
    then failwith "Not going to expand this variable" else th in
  let rec conv tm =
   ((conv1' THENC BINDER_CONV conv) ORELSEC
    (conv2 THENC
     RAND_CONV(RAND_CONV(ABS_CONV(BINDER_CONV(LAND_CONV conv))))) ORELSEC
    SUB_CONV conv) tm in
  conv;;

let EXPAND_QUANTS_CONV = PARTIAL_EXPAND_QUANTS_CONV [];;
