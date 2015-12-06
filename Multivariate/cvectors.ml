(* ========================================================================= *)
(* A library for vectors of complex numbers.                                 *)
(* Much inspired from HOL-Light real vector library <"vectors.ml">.          *)
(*                                                                           *)
(*            (c) Copyright, Sanaz Khan Afshar & Vincent Aravantinos 2011-13 *)
(*                           Hardware Verification Group,                    *)
(*                           Concordia University                            *)
(*                                                                           *)
(*                Contact:   <s_khanaf@encs.concordia.ca>                    *)
(*                           <vincent.aravantinos@fortiss.org>               *)
(*                                                                           *)
(* Acknowledgements:                                                         *)
(* - Harsh Singhal: n-dimensional dot product, utility theorems              *)
(*                                                                           *)
(* Updated for the latest version of HOL Light (JULY 2014)                   *)
(* ========================================================================= *)

needs "Multivariate/complexes.ml";;
needs "Multivariate/cross.ml";;

(* ========================================================================= *)
(* ADDITIONS TO THE BASE LIBRARY                                             *)
(* ========================================================================= *)

  (* ----------------------------------------------------------------------- *)
  (* Additional tacticals                                                    *)
  (* ----------------------------------------------------------------------- *)


let SINGLE f x = f [x];;

let distrib fs x = map (fun f -> f x) fs;;

let DISTRIB ttacs x = EVERY (distrib ttacs x);;

let REWRITE_TACS = MAP_EVERY (SINGLE REWRITE_TAC);;

let GCONJUNCTS thm = map GEN_ALL (CONJUNCTS (SPEC_ALL thm));;

  (* ----------------------------------------------------------------------- *)
  (* Additions to the vectors library                                        *)
  (* ----------------------------------------------------------------------- *)

let COMPONENT_LE_NORM_ALT = prove
  (`!x:real^N i. 1 <= i /\ i <= dimindex (:N) ==> x$i <= norm x`,
  MESON_TAC [REAL_ABS_LE;COMPONENT_LE_NORM;REAL_LE_TRANS]);;

  (* ----------------------------------------------------------------------- *)
  (* Additions to the library of complex numbers                             *)
  (* ----------------------------------------------------------------------- *)

(* Lemmas *)
let RE_IM_NORM = prove
  (`!x. Re x <= norm x /\ Im x <= norm x /\ abs(Re x) <= norm x
  /\ abs(Im x) <= norm x`,
  REWRITE_TAC[RE_DEF;IM_DEF] THEN GEN_TAC THEN REPEAT CONJ_TAC
  THEN ((MATCH_MP_TAC COMPONENT_LE_NORM_ALT
  THEN REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC) ORELSE SIMP_TAC [COMPONENT_LE_NORM]));;

let [RE_NORM;IM_NORM;ABS_RE_NORM;ABS_IM_NORM] = GCONJUNCTS RE_IM_NORM;;

let NORM_RE = prove
  (`!x. &0 <= norm x + Re x /\ &0 <= norm x - Re x`,
  GEN_TAC THEN MP_TAC (SPEC_ALL ABS_RE_NORM) THEN REAL_ARITH_TAC);;

let [NORM_RE_ADD;NORM_RE_SUB] = GCONJUNCTS NORM_RE;;

let NORM2_ADD_REAL = prove
  (`!x y.
    real x /\ real y ==> norm (x + ii * y) pow 2 = norm x pow 2 + norm y pow 2`,
  SIMP_TAC[real;complex_norm;RE_ADD;IM_ADD;RE_MUL_II;IM_MUL_II;REAL_NEG_0;
    REAL_ADD_LID;REAL_ADD_RID;REAL_POW_ZERO;ARITH_RULE `~(2=0)`;REAL_LE_POW_2;
    SQRT_POW_2;REAL_LE_ADD]);;

let COMPLEX_EQ_RCANCEL_IMP = GEN_ALL (MATCH_MP (MESON []
  `(p <=> r \/ q) ==> (p /\ ~r ==> q) `) (SPEC_ALL COMPLEX_EQ_MUL_RCANCEL));;

let COMPLEX_BALANCE_DIV_MUL = prove
  (`!x y z t. ~(z=Cx(&0)) ==> (x = y/z * t <=> x*z = y * t)`,
  REPEAT STRIP_TAC THEN POP_ASSUM (fun x ->
    ASSUME_TAC (REWRITE_RULE[x] (SPEC_ALL COMPLEX_EQ_MUL_RCANCEL))
    THEN ASSUME_TAC (REWRITE_RULE[x] (SPECL [`x:complex`;`z:complex`]
    COMPLEX_DIV_RMUL)))
  THEN SUBGOAL_THEN `x=y/z*t <=> x*z=(y/z*t)*z:complex` (SINGLE REWRITE_TAC)
  THENL [ASM_REWRITE_TAC[];
    REWRITE_TAC[SIMPLE_COMPLEX_ARITH `(y/z*t)*z=(y/z*z)*t:complex`]
  THEN ASM_REWRITE_TAC[]]);;

let CSQRT_MUL_LCX_LT = prove
  (`!x y. &0 < x ==> csqrt(Cx x * y) = Cx(sqrt x) * csqrt y`,
  REWRITE_TAC[csqrt;complex_mul;IM;RE;IM_CX;REAL_MUL_LZERO;REAL_ADD_RID;RE_CX;
    REAL_SUB_RZERO]
  THEN REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC
  THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)
  THEN ASM_SIMP_TAC[IM;RE;REAL_MUL_RZERO;SQRT_MUL]
  THENL [
    REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC[REAL_ENTIRE;REAL_MUL_POS_LE]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[SQRT_0;REAL_MUL_LZERO;REAL_MUL_RZERO];
    REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [REAL_ENTIRE]
    THEN MESON_TAC [REAL_LT_IMP_NZ];
    ASM_MESON_TAC [REAL_LE_MUL_EQ;REAL_ARITH `~(&0 <= y) = &0 > y`];
    SIMP_TAC [REAL_NEG_RMUL] THEN REPEAT (POP_ASSUM MP_TAC)
    THEN SIMP_TAC [REAL_ARITH `~(&0 <= y) = y < &0`]
    THEN SIMP_TAC [GSYM REAL_NEG_GT0] THEN MESON_TAC[REAL_LT_IMP_LE;SQRT_MUL];
    REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [REAL_ENTIRE]
    THEN MESON_TAC [REAL_LT_IMP_NZ];
    REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [REAL_ENTIRE]
    THEN SIMP_TAC [DE_MORGAN_THM];
    REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [REAL_ENTIRE]
    THEN SIMP_TAC [DE_MORGAN_THM]; ALL_TAC] THENL [
      SIMP_TAC [REAL_NEG_0;SQRT_0;REAL_MUL_RZERO];
      ASM_MESON_TAC[REAL_ARITH `~(x<y /\ ~(x <=y))`];
      ASM_MESON_TAC[REAL_ARITH `~(x<y /\ y<x)`];
      ALL_TAC]
    THEN REWRITE_TAC[GSYM (REWRITE_RULE[CX_DEF;complex_mul;RE;IM;
      REAL_MUL_LZERO;REAL_ADD_RID;REAL_SUB_RZERO] COMPLEX_CMUL)]
    THEN SIMP_TAC [NORM_MUL] THEN POP_ASSUM MP_TAC
    THEN ASM_SIMP_TAC [GSYM REAL_ABS_REFL] THEN DISCH_TAC
    THEN SIMP_TAC [REAL_ABS_MUL]
    THEN ASM_SIMP_TAC [GSYM REAL_ABS_REFL]
    THEN SIMP_TAC [GSYM REAL_ADD_LDISTRIB; GSYM REAL_SUB_LDISTRIB]
    THEN SUBGOAL_THEN `(x*Im y) / (x*abs(Im y)) = Im y / abs(Im y)` ASSUME_TAC
    THENL [
      SIMP_TAC [real_div] THEN SIMP_TAC [REAL_INV_MUL]
      THEN SIMP_TAC [GSYM REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_AC]
      THEN SUBGOAL_THEN `Im y * x * inv x * inv (abs(Im y)) =
        Im y * (x * inv x) * inv (abs (Im y)) ` ASSUME_TAC
        THENL [SIMP_TAC [REAL_MUL_AC]; ALL_TAC]
      THEN ASM_SIMP_TAC[REAL_MUL_RINV;REAL_LT_IMP_NZ]
      THEN SIMP_TAC [REAL_MUL_LID] THEN SIMP_TAC [REAL_MUL_AC];
      ALL_TAC]
    THEN ASM_SIMP_TAC[]
    THEN SUBGOAL_THEN `sqrt x * Im y / abs(Im y) * sqrt ((norm y-Re y) / &2) =
      Im y / abs (Im y) * sqrt x * sqrt ((norm y - Re y) / &2)` ASSUME_TAC
    THENL [SIMP_TAC [REAL_MUL_AC]; ALL_TAC] THEN ASM_SIMP_TAC[]
    THEN SUBGOAL_THEN `sqrt ((x * (norm y - Re y)) / &2) =
      sqrt (x * (norm y - Re y)) / sqrt (&2)` ASSUME_TAC
    THENL [
      SIMP_TAC[SQRT_DIV] THEN CONJ_TAC THENL [
        ASM_SIMP_TAC[REAL_LE_MUL_EQ;REAL_LT_IMP_LE] THEN SIMP_TAC[NORM_RE_SUB];
        REAL_ARITH_TAC];
      ALL_TAC]
    THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN `sqrt ((norm y - Re y) / &2) =
      sqrt (norm y - Re y) / sqrt (&2)` ASSUME_TAC
    THENL [
      SIMP_TAC[SQRT_DIV] THEN CONJ_TAC
      THENL [SIMP_TAC [NORM_RE_SUB]; REAL_ARITH_TAC];
      ALL_TAC ]
    THEN ASM_SIMP_TAC[]
    THEN SUBGOAL_THEN `sqrt ((x * (norm y + Re y)) / &2) =
      sqrt (x * (norm y + Re y)) / sqrt (&2)` ASSUME_TAC
    THENL [
      SIMP_TAC[SQRT_DIV] THEN CONJ_TAC
      THENL [
        ASM_SIMP_TAC [REAL_LE_MUL_EQ;REAL_LT_IMP_LE]
        THEN SIMP_TAC[NORM_RE_ADD];
        REAL_ARITH_TAC];
      ALL_TAC]
    THEN SUBGOAL_THEN `sqrt ((norm y + Re y) / &2) =
      sqrt (norm y + Re y) / sqrt (&2)` ASSUME_TAC
    THENL [
      SIMP_TAC[SQRT_DIV] THEN CONJ_TAC
      THENL [SIMP_TAC[NORM_RE_ADD]; REAL_ARITH_TAC];
      ALL_TAC]
    THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN `&0 <= x` ASSUME_TAC
    THENL [ ASM_SIMP_TAC [REAL_LT_IMP_LE]; ALL_TAC ]
    THEN SIMP_TAC[COMPLEX_EQ] THEN SIMP_TAC[RE;IM] THEN CONJ_TAC
    THENL [
      SUBGOAL_THEN `sqrt x * sqrt (norm y + Re y) / sqrt (&2) =
        (sqrt x * sqrt (norm y + Re y)) / sqrt (&2)` ASSUME_TAC
      THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN ASM_MESON_TAC [SQRT_MUL;NORM_RE_ADD];
      SUBGOAL_THEN `Im y/abs(Im y) * sqrt x * sqrt (norm y-Re y) / sqrt(&2) =
        Im y/abs (Im y) * (sqrt x * sqrt (norm y - Re y))/sqrt(&2)` ASSUME_TAC
      THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN ASM_MESON_TAC[SQRT_MUL;NORM_RE_SUB]]);;

let CSQRT_MUL_LCX = prove
  (`!x y. &0 <= x ==> csqrt(Cx x * y) = Cx(sqrt x) * csqrt y`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC
  THEN ASM_SIMP_TAC[CSQRT_MUL_LCX_LT] THEN EXPAND_TAC "x"
  THEN REWRITE_TAC[COMPLEX_MUL_LZERO;SQRT_0;CSQRT_0]);;

let REAL_ADD_POW_2 = prove
  (`!x y:real. (x+y) pow 2 = x pow 2 + y pow 2 + &2 * x * y`,
  REAL_ARITH_TAC);;

let COMPLEX_ADD_POW_2 = prove
  (`!x y:complex. (x+y) pow 2 = x pow 2 + y pow 2 + Cx(&2) * x * y`,
  REWRITE_TAC[COMPLEX_POW_2] THEN SIMPLE_COMPLEX_ARITH_TAC);;



(* ----------------------------------------------------------------------- *)
(* Additions to the topology library                                       *)
(* ----------------------------------------------------------------------- *)

 prioritize_vector ();;

(* Lemmas *)
let FINITE_INTER_ENUM = prove
  (`!s n. FINITE(s INTER (0..n))`,
  MESON_TAC[FINITE_INTER;FINITE_NUMSEG]);;

let NORM_PASTECART_GE1 = prove
  (`!x y. norm x <= norm (pastecart x y)`,
  MESON_TAC[FSTCART_PASTECART;NORM_FSTCART]);;

let NORM_PASTECART_GE2 = prove
  (`!x y. norm y <= norm (pastecart x y)`,
  MESON_TAC[SNDCART_PASTECART;NORM_SNDCART]);;

let LIM_PASTECART_EQ = prove
  (`!net a b f:A->real^M g:A->real^N. (f --> a) net /\ (g --> b) net
    <=> ((\x. pastecart (f x) (g x)) --> pastecart a b) net`,
  REWRITE_TAC[MESON[] `(a <=> b) <=> (a ==> b) /\ (b ==> a)`;LIM_PASTECART;LIM;
    MESON[]`(p\/q ==> (p \/ r) /\ (p \/ s)) <=> (~p /\ q ==> r /\ s)`;dist;
    PASTECART_SUB]
  THEN ASM_MESON_TAC[REAL_LET_TRANS;NORM_PASTECART_GE1;NORM_PASTECART_GE2]);;

let SUMS_PASTECART = prove
  (`!s f1:num->real^N f2:num->real^M l1 l2. (f1 sums l1) s /\ (f2 sums l2) s
    <=> ((\x. pastecart (f1 x) (f2 x)) sums (pastecart l1 l2)) s`,
  SIMP_TAC[sums;FINITE_INTER_ENUM;GSYM PASTECART_VSUM;LIM_PASTECART_EQ]);;

let LINEAR_SUMS = prove(
  `!s f l g. linear g ==> ((f sums l) s ==> ((g o f) sums (g l)) s)`,
  SIMP_TAC[sums;FINITE_INTER_ENUM;GSYM LINEAR_VSUM;
    REWRITE_RULE[o_DEF;CONTINUOUS_AT_SEQUENTIALLY] LINEAR_CONTINUOUS_AT]);;

  (* ----------------------------------------------------------------------- *)
  (* Embedding of reals in complex numbers                                   *)
  (* ----------------------------------------------------------------------- *)

let real_of_complex = new_definition `real_of_complex c = @r. c = Cx r`;;

let REAL_OF_COMPLEX = prove
  (`!c. real c ==> Cx(real_of_complex c) = c`,
  MESON_TAC[REAL;real_of_complex]);;

let REAL_OF_COMPLEX_RE = prove
  (`!c. real c ==> real_of_complex c = Re c`,
  MESON_TAC[RE_CX;REAL_OF_COMPLEX]);;

let REAL_OF_COMPLEX_CX = prove
  (`!r. real_of_complex (Cx r) = r`,
  SIMP_TAC[REAL_CX;REAL_OF_COMPLEX_RE;RE_CX]);;

let REAL_OF_COMPLEX_NORM = prove
  (`!c. real c ==> norm c = abs (real_of_complex c)`,
  MESON_TAC[REAL_NORM;REAL_OF_COMPLEX_RE]);;

let REAL_OF_COMPLEX_ADD = prove
  (`!x y. real x /\ real y
    ==> real_of_complex (x+y) = real_of_complex x + real_of_complex y`,
  MESON_TAC[REAL_ADD;REAL_OF_COMPLEX_RE;RE_ADD]);;

let REAL_MUL = prove
  (`!x y. real x /\ real y ==> real (x*y)`,
  REWRITE_TAC[real] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let REAL_OF_COMPLEX_MUL = prove(
  `!x y. real x /\ real y
    ==> real_of_complex (x*y) = real_of_complex x * real_of_complex y`,
  MESON_TAC[REAL_MUL;REAL_OF_COMPLEX;CX_MUL;REAL_OF_COMPLEX_CX]);;

let REAL_OF_COMPLEX_0 = prove(
  `!x. real x ==> (real_of_complex x = &0 <=> x = Cx(&0))`,
  REWRITE_TAC[REAL_EXISTS] THEN REPEAT STRIP_TAC
  THEN ASM_SIMP_TAC[REAL_OF_COMPLEX_CX;CX_INJ]);;

let REAL_COMPLEX_ADD_CNJ = prove(
  `!x. real(cnj x + x) /\ real(x + cnj x)`,
  REWRITE_TAC[COMPLEX_ADD_CNJ;REAL_CX]);;

(* TODO
 *let RE_EQ_NORM = prove(`!x. Re x = norm x <=> real x /\ &0 <= real_of_complex x`,
 *)

  (* ----------------------------------------------------------------------- *)
  (* Additions to the vectors library                                        *)
  (* ----------------------------------------------------------------------- *)

let vector_const = new_definition
  `vector_const (k:A) :A^N = lambda i. k`;;
let vector_map = new_definition
  `vector_map (f:A->B) (v:A^N) :B^N = lambda i. f(v$i)`;;
let vector_map2 = new_definition
  `vector_map2 (f:A->B->C) (v1:A^N) (v2:B^N) :C^N =
    lambda i. f (v1$i) (v2$i)`;;
let vector_map3 = new_definition
  `vector_map3 (f:A->B->C->D) (v1:A^N) (v2:B^N) (v3:C^N) :D^N =
    lambda i. f (v1$i) (v2$i) (v3$i)`;;

let FINITE_INDEX_INRANGE_2 = prove
 (`!i. ?k. 1 <= k /\ k <= dimindex(:N) /\ (!x:A^N. x$i = x$k)
  /\ (!x:B^N. x$i = x$k) /\ (!x:C^N. x$i = x$k) /\ (!x:D^N. x$i = x$k)`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]);;

let COMPONENT_TAC x =
  REPEAT GEN_TAC THEN CHOOSE_TAC (SPEC_ALL FINITE_INDEX_INRANGE_2)
  THEN ASM_SIMP_TAC[x;LAMBDA_BETA];;

let VECTOR_CONST_COMPONENT = prove
  (`!i k. ((vector_const k):A^N)$i = k`,
  COMPONENT_TAC vector_const);;
let VECTOR_MAP_COMPONENT = prove
  (`!i f:A->B v:A^N. (vector_map f v)$i = f (v$i)`,
  COMPONENT_TAC vector_map);;
let VECTOR_MAP2_COMPONENT = prove
  (`!i f:A->B->C v1:A^N v2. (vector_map2 f v1 v2)$i = f (v1$i) (v2$i)`,
  COMPONENT_TAC vector_map2);;
let VECTOR_MAP3_COMPONENT = prove(
  `!i f:A->B->C->D v1:A^N v2 v3. (vector_map3 f v1 v2 v3)$i =
    f (v1$i) (v2$i) (v3$i)`,
    COMPONENT_TAC vector_map3);;

let COMMON_TAC =
  REWRITE_TAC[vector_const;vector_map;vector_map2;vector_map3]
  THEN ONCE_REWRITE_TAC[CART_EQ] THEN SIMP_TAC[LAMBDA_BETA;o_DEF];;

let VECTOR_MAP_VECTOR_CONST = prove
  (`!f:A->B k. vector_map f ((vector_const k):A^N) = vector_const (f k)`,
  COMMON_TAC);;

let VECTOR_MAP_VECTOR_MAP = prove
  (`!f:A->B g:C->A v:C^N.
    vector_map f (vector_map g v) = vector_map (f o g) v`,
  COMMON_TAC);;

let VECTOR_MAP_VECTOR_MAP2 = prove
  (`!f:A->B g:C->D->A u v:D^N.
    vector_map f (vector_map2 g u v) = vector_map2 (\x y. f (g x y)) u v`,
  COMMON_TAC);;

let VECTOR_MAP2_LVECTOR_CONST = prove
  (`!f:A->B->C k v:B^N.
    vector_map2 f (vector_const k) v = vector_map (f k) v`,
  COMMON_TAC);;

let VECTOR_MAP2_RVECTOR_CONST = prove
  (`!f:A->B->C k v:A^N.
    vector_map2 f v (vector_const k) = vector_map (\x. f x k) v`,
  COMMON_TAC);;

let VECTOR_MAP2_LVECTOR_MAP = prove
  (`!f:A->B->C g:D->A v1 v2:B^N.
    vector_map2 f (vector_map g v1) v2 = vector_map2 (f o g) v1 v2`,
  COMMON_TAC);;

let VECTOR_MAP2_RVECTOR_MAP = prove
  (`!f:A->B->C g:D->B v1 v2:D^N.
    vector_map2 f v1 (vector_map g v2) = vector_map2 (\x y. f x (g y)) v1 v2`,
  COMMON_TAC);;

let VECTOR_MAP2_LVECTOR_MAP2 = prove
  (`!f:A->B->C g:D->E->A v1 v2 v3:B^N.
    vector_map2 f (vector_map2 g v1 v2) v3 =
      vector_map3 (\x y. f (g x y)) v1 v2 v3`,
  COMMON_TAC);;

let VECTOR_MAP2_RVECTOR_MAP2 = prove(
  `!f:A->B->C g:D->E->B v1 v2 v3:E^N.
    vector_map2 f v1 (vector_map2 g v2 v3) =
      vector_map3 (\x y z. f x (g y z)) v1 v2 v3`,
  COMMON_TAC);;

let VECTOR_MAP_SIMP_TAC = REWRITE_TAC[
    VECTOR_MAP_VECTOR_CONST;VECTOR_MAP2_LVECTOR_CONST;
    VECTOR_MAP2_RVECTOR_CONST;VECTOR_MAP_VECTOR_MAP;VECTOR_MAP2_RVECTOR_MAP;
    VECTOR_MAP2_LVECTOR_MAP;VECTOR_MAP2_RVECTOR_MAP2;VECTOR_MAP2_LVECTOR_MAP2;
    VECTOR_MAP_VECTOR_MAP2];;

let VECTOR_MAP_PROPERTY_TAC fs prop =
  REWRITE_TAC fs THEN VECTOR_MAP_SIMP_TAC THEN ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[VECTOR_MAP_COMPONENT;VECTOR_MAP2_COMPONENT;
    VECTOR_MAP3_COMPONENT;VECTOR_CONST_COMPONENT;o_DEF;prop];;

let VECTOR_MAP_PROPERTY thm f prop =
  prove(thm,VECTOR_MAP_PROPERTY_TAC f prop);;

let COMPLEX_VECTOR_MAP = prove
  (`!f:complex->complex g. f = vector_map g
    <=> !z. f z = complex (g (Re z), g (Im z))`,
  REWRITE_TAC[vector_map;FUN_EQ_THM;complex] THEN REPEAT (GEN_TAC ORELSE EQ_TAC)
  THEN ASM_SIMP_TAC[CART_EQ;DIMINDEX_2;FORALL_2;LAMBDA_BETA;VECTOR_2;RE_DEF;IM_DEF]);;

let COMPLEX_NEG_IS_A_MAP = prove
  (`(--):complex->complex = vector_map ((--):real->real)`,
  REWRITE_TAC[COMPLEX_VECTOR_MAP;complex_neg]);;

let VECTOR_NEG_IS_A_MAP = prove
  (`(--):real^N->real^N = vector_map ((--):real->real)`,
  REWRITE_TAC[FUN_EQ_THM;CART_EQ;VECTOR_NEG_COMPONENT;VECTOR_MAP_COMPONENT]);;

let VECTOR_MAP_VECTOR_MAP_ALT = prove
  (`!f:A^N->B^N g:C^N->A^N f' g'. f = vector_map f' /\ g = vector_map g' ==>
    f o g = vector_map (f' o g')`,
  SIMP_TAC[o_DEF;FUN_EQ_THM;VECTOR_MAP_VECTOR_MAP]);;

let COMPLEX_VECTOR_MAP2 = prove
  (`!f:complex->complex->complex g. f = vector_map2 g <=>
    !z1 z2. f z1 z2 = complex (g (Re z1) (Re z2), g (Im z1) (Im z2))`,
  REWRITE_TAC[vector_map2;FUN_EQ_THM;complex]
  THEN REPEAT (GEN_TAC ORELSE EQ_TAC)
  THEN ASM_SIMP_TAC[CART_EQ;DIMINDEX_2;FORALL_2;LAMBDA_BETA;VECTOR_2;RE_DEF;
    IM_DEF]);;

let VECTOR_MAP2_RVECTOR_MAP_ALT = prove(
  `!f:complex->complex->complex g:complex->complex f' g'.
    f = vector_map2 f' /\ g = vector_map g'
      ==> (\x y. f x (g y)) = vector_map2 (\x y. f' x (g' y))`,
  SIMP_TAC[FUN_EQ_THM;VECTOR_MAP2_RVECTOR_MAP]);;

let COMPLEX_ADD_IS_A_MAP = prove
  (`(+):complex->complex->complex = vector_map2 ((+):real->real->real)`,
  REWRITE_TAC[COMPLEX_VECTOR_MAP2;complex_add]);;

let VECTOR_ADD_IS_A_MAP = prove
  (`(+):real^N->real^N->real^N = vector_map2 ((+):real->real->real)`,
  REWRITE_TAC[FUN_EQ_THM;CART_EQ;VECTOR_ADD_COMPONENT;VECTOR_MAP2_COMPONENT]);;

let COMPLEX_SUB_IS_A_MAP = prove
  (`(-):complex->complex->complex = vector_map2 ((-):real->real->real)`,
  ONCE_REWRITE_TAC[prove(`(-) = \x y:complex. x-y`,REWRITE_TAC[FUN_EQ_THM])]
  THEN ONCE_REWRITE_TAC[prove(`(-) = \x y:real. x-y`,REWRITE_TAC[FUN_EQ_THM])]
  THEN REWRITE_TAC[complex_sub;real_sub]
  THEN MATCH_MP_TAC VECTOR_MAP2_RVECTOR_MAP_ALT
  THEN REWRITE_TAC[COMPLEX_NEG_IS_A_MAP;COMPLEX_ADD_IS_A_MAP]);;

let VECTOR_SUB_IS_A_MAP = prove
  (`(-):real^N->real^N->real^N = vector_map2 ((-):real->real->real)`,
  REWRITE_TAC[FUN_EQ_THM;CART_EQ;VECTOR_SUB_COMPONENT;VECTOR_MAP2_COMPONENT]);;

let COMMON_TAC x =
  SIMP_TAC[CART_EQ;pastecart;x;LAMBDA_BETA] THEN REPEAT STRIP_TAC
  THEN REPEAT COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[]
  THEN SUBGOAL_THEN `1<= i-dimindex(:N) /\ i-dimindex(:N) <= dimindex(:M)`
    ASSUME_TAC
  THEN ASM_SIMP_TAC[LAMBDA_BETA]
  THEN REPEAT (POP_ASSUM (MP_TAC o REWRITE_RULE[DIMINDEX_FINITE_SUM]))
  THEN ARITH_TAC;;

let PASTECART_VECTOR_MAP = prove
  (`!f:A->B x:A^N y:A^M.
    pastecart (vector_map f x) (vector_map f y) =
      vector_map f (pastecart x y)`,
    COMMON_TAC vector_map);;

let PASTECART_VECTOR_MAP2 = prove
  (`!f:A->B->C x1:A^N x2 y1:A^M y2.
    pastecart (vector_map2 f x1 x2) (vector_map2 f y1 y2)
      = vector_map2 f (pastecart x1 y1) (pastecart x2 y2)`,
  COMMON_TAC vector_map2);;

let vector_zip = new_definition
  `vector_zip (v1:A^N) (v2:B^N) : (A#B)^N = lambda i. (v1$i,v2$i)`;;

let VECTOR_ZIP_COMPONENT = prove
  (`!i v1:A^N v2:B^N. (vector_zip v1 v2)$i = (v1$i,v2$i)`,
  REPEAT GEN_TAC THEN CHOOSE_TAC (INST_TYPE [`:A#B`,`:C`] (SPEC_ALL
    FINITE_INDEX_INRANGE_2)) THEN ASM_SIMP_TAC[vector_zip;LAMBDA_BETA]);;

let vector_unzip = new_definition
  `vector_unzip (v:(A#B)^N):(A^N)#(B^N) = vector_map FST v,vector_map SND v`;;

let VECTOR_UNZIP_COMPONENT = prove
  (`!i v:(A#B)^N. (FST (vector_unzip v))$i = FST (v$i)
    /\ (SND (vector_unzip v))$i = SND (v$i)`,
  REWRITE_TAC[vector_unzip;VECTOR_MAP_COMPONENT]);;

let VECTOR_MAP2_AS_VECTOR_MAP = prove
  (`!f:A->B->C v1:A^N v2:B^N.
    vector_map2 f v1 v2 = vector_map (UNCURRY f) (vector_zip v1 v2)`,
  REWRITE_TAC[CART_EQ;VECTOR_MAP2_COMPONENT;VECTOR_MAP_COMPONENT;
    VECTOR_ZIP_COMPONENT;UNCURRY_DEF]);;



(* ========================================================================= *)
(* BASIC ARITHMETIC                                                          *)
(* ========================================================================= *)

make_overloadable "%" `:A-> B-> B`;;

let prioritize_cvector () =
  overload_interface("--",`(cvector_neg):complex^N->complex^N`);
  overload_interface("+",`(cvector_add):complex^N->complex^N->complex^N`);
  overload_interface("-",`(cvector_sub):complex^N->complex^N->complex^N`);
  overload_interface("%",`(cvector_mul):complex->complex^N->complex^N`);;

let cvector_zero = new_definition
  `cvector_zero:complex^N = vector_const (Cx(&0))`;;

let cvector_neg = new_definition
  `cvector_neg :complex^N->complex^N = vector_map (--)`;;

let cvector_add = new_definition
  `cvector_add :complex^N->complex^N->complex^N = vector_map2 (+)`;;

let cvector_sub = new_definition
  `cvector_sub :complex^N->complex^N->complex^N = vector_map2 (-)`;;

let cvector_mul = new_definition
  `(cvector_mul:complex->complex^N->complex^N) a = vector_map (( * ) a)`;;

overload_interface("%",`(%):real->real^N->real^N`);;
prioritize_cvector ();;

let CVECTOR_ZERO_COMPONENT = prove
  (`!i. (cvector_zero:complex^N)$i = Cx(&0)`,
  REWRITE_TAC[cvector_zero;VECTOR_CONST_COMPONENT]);;

let CVECTOR_NON_ZERO = prove
  (`!x:complex^N. ~(x=cvector_zero)
    <=> ?i. 1 <= i /\ i <= dimindex(:N) /\ ~(x$i = Cx(&0))`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [CART_EQ]
  THEN REWRITE_TAC[CVECTOR_ZERO_COMPONENT] THEN MESON_TAC[]);;

let CVECTOR_ADD_COMPONENT = prove
  (`!X Y:complex^N i. ((X + Y)$i = X$i + Y$i)`,
  REWRITE_TAC[cvector_add;VECTOR_MAP2_COMPONENT]);;

let CVECTOR_SUB_COMPONENT = prove
  (`!X:complex^N Y i. ((X - Y)$i = X$i - Y$i)`,
  REWRITE_TAC[cvector_sub;VECTOR_MAP2_COMPONENT]);;

let CVECTOR_NEG_COMPONENT = prove
  (`!X:complex^N i. ((--X)$i = --(X$i))`,
  REWRITE_TAC[cvector_neg;VECTOR_MAP_COMPONENT]);;

let CVECTOR_MUL_COMPONENT = prove
  (`!c:complex X:complex^N i. ((c % X)$i = c * X$i)`,
  REWRITE_TAC[cvector_mul;VECTOR_MAP_COMPONENT]);;

(* Simple generic tactic adapted from VECTOR_ARITH_TAC *)
let CVECTOR_ARITH_TAC =
  let RENAMED_LAMBDA_BETA th =
    if fst(dest_fun_ty(type_of(funpow 3 rand (concl th)))) = aty
    then INST_TYPE [aty,bty; bty,aty] LAMBDA_BETA else LAMBDA_BETA
  in
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_TAC ORELSE EQ_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN TRY EQ_TAC THEN
  TRY(MATCH_MP_TAC MONO_FORALL) THEN GEN_TAC THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`;
              TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`] THEN
  TRY(MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`)) THEN
  REWRITE_TAC[cvector_zero;cvector_add; cvector_sub; cvector_neg; cvector_mul; vector_map;vector_map2;vector_const] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP(RENAMED_LAMBDA_BETA th) th]) THEN
  SIMPLE_COMPLEX_ARITH_TAC;;

let CVECTOR_ARITH tm = prove(tm,CVECTOR_ARITH_TAC);;

(* ========================================================================= *)
(*  VECTOR SPACE AXIOMS AND ADDITIONAL BASIC RESULTS                         *)
(* ========================================================================= *)

let CVECTOR_MAP_PROPERTY thm =
  VECTOR_MAP_PROPERTY thm [cvector_zero;cvector_add;cvector_sub;cvector_neg;
    cvector_mul];;

let CVECTOR_ADD_SYM = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. x + y = y + x`
  COMPLEX_ADD_SYM;;

let CVECTOR_ADD_ASSOC = CVECTOR_MAP_PROPERTY
  `!x y z:complex^N. x + (y + z) = (x + y) + z`
  COMPLEX_ADD_ASSOC;;

let CVECTOR_ADD_ID = CVECTOR_MAP_PROPERTY
  `!x:complex^N. x + cvector_zero = x /\ cvector_zero + x = x`
  (CONJ COMPLEX_ADD_RID COMPLEX_ADD_LID);;

let [CVECTOR_ADD_RID;CVECTOR_ADD_LID] = GCONJUNCTS CVECTOR_ADD_ID;;

let CVECTOR_ADD_INV = CVECTOR_MAP_PROPERTY
  `!x:complex^N. x + -- x = cvector_zero /\ --x + x = cvector_zero`
  (CONJ COMPLEX_ADD_RINV COMPLEX_ADD_LINV);;

let CVECTOR_MUL_ASSOC = CVECTOR_MAP_PROPERTY
  `!a b x:complex^N. a % (b % x) = (a * b) % x`
  COMPLEX_MUL_ASSOC;;

let CVECTOR_SUB_LDISTRIB = CVECTOR_MAP_PROPERTY
  `!c x y:complex^N. c % (x - y) = c % x - c % y`
  COMPLEX_SUB_LDISTRIB;;

let CVECTOR_SCALAR_RDIST = CVECTOR_MAP_PROPERTY
  `!a b x:complex^N. (a + b) % x = a % x + b % x`
  COMPLEX_ADD_RDISTRIB;;

let CVECTOR_MUL_ID = CVECTOR_MAP_PROPERTY
  `!x:complex^N. Cx(&1) % x = x`
  COMPLEX_MUL_LID;;

let CVECTOR_SUB_REFL = CVECTOR_MAP_PROPERTY
  `!x:complex^N. x - x = cvector_zero`
  COMPLEX_SUB_REFL;;

let CVECTOR_SUB_RADD = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. x - (x + y) = --y`
  COMPLEX_ADD_SUB2;;

let CVECTOR_NEG_SUB = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. --(x - y) = y - x`
  COMPLEX_NEG_SUB;;

let CVECTOR_SUB_EQ = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. (x - y = cvector_zero) <=> (x = y)`
  COMPLEX_SUB_0;;

let CVECTOR_MUL_LZERO = CVECTOR_MAP_PROPERTY
  `!x. Cx(&0) % x = cvector_zero`
  COMPLEX_MUL_LZERO;;

let CVECTOR_SUB_ADD = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. (x - y) + y = x`
  COMPLEX_SUB_ADD;;

let CVECTOR_SUB_ADD2 = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. y + (x - y) = x`
  COMPLEX_SUB_ADD2;;

let CVECTOR_ADD_LDISTRIB = CVECTOR_MAP_PROPERTY
  `!c x y:complex^N. c % (x + y) = c % x + c % y`
  COMPLEX_ADD_LDISTRIB;;

let CVECTOR_ADD_RDISTRIB = CVECTOR_MAP_PROPERTY
  `!a b x:complex^N. (a + b) % x = a % x + b % x`
  COMPLEX_ADD_RDISTRIB;;

let CVECTOR_SUB_RDISTRIB = CVECTOR_MAP_PROPERTY
  `!a b x:complex^N. (a - b) % x = a % x - b % x`
  COMPLEX_SUB_RDISTRIB;;

let CVECTOR_ADD_SUB = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. (x + y:complex^N) - x = y`
  COMPLEX_ADD_SUB;;

let CVECTOR_EQ_ADDR = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. (x + y = x) <=> (y = cvector_zero)`
  COMPLEX_EQ_ADD_LCANCEL_0;;

let CVECTOR_SUB = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. x - y = x + --(y:complex^N)`
  complex_sub;;

let CVECTOR_SUB_RZERO = CVECTOR_MAP_PROPERTY
  `!x:complex^N. x - cvector_zero = x`
  COMPLEX_SUB_RZERO;;

let CVECTOR_MUL_RZERO = CVECTOR_MAP_PROPERTY
  `!c:complex. c % cvector_zero = cvector_zero`
  COMPLEX_MUL_RZERO;;

let CVECTOR_MUL_LZERO = CVECTOR_MAP_PROPERTY
  `!x:complex^N. Cx(&0) % x = cvector_zero`
  COMPLEX_MUL_LZERO;;

let CVECTOR_MUL_EQ_0 = prove
  (`!a:complex x:complex^N.
    (a % x = cvector_zero <=> a = Cx(&0) \/ x = cvector_zero)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [
    ASM_CASES_TAC `a=Cx(&0)` THENL [
      ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [CART_EQ]
      THEN ASM_REWRITE_TAC[CVECTOR_MUL_COMPONENT;CVECTOR_ZERO_COMPONENT;
        COMPLEX_ENTIRE]
      THEN GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [CART_EQ]
      THEN REWRITE_TAC[CVECTOR_ZERO_COMPONENT];
    ];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[CVECTOR_MUL_RZERO;CVECTOR_MUL_LZERO];
  ]);;

let CVECTOR_NEG_MINUS1 = CVECTOR_MAP_PROPERTY
  `!x:complex^N. --x = (--(Cx(&1))) % x`
  (GSYM COMPLEX_NEG_MINUS1);;

let CVECTOR_SUB_LZERO = CVECTOR_MAP_PROPERTY
  `!x:complex^N. cvector_zero - x = --x`
  COMPLEX_SUB_LZERO;;

let CVECTOR_NEG_NEG = CVECTOR_MAP_PROPERTY
  `!x:complex^N. --(--(x:complex^N)) = x`
  COMPLEX_NEG_NEG;;

let CVECTOR_MUL_LNEG = CVECTOR_MAP_PROPERTY
  `!c x:complex^N. --c % x = --(c % x)`
  COMPLEX_MUL_LNEG;;

let CVECTOR_MUL_RNEG = CVECTOR_MAP_PROPERTY
  `!c x:complex^N. c % --x = --(c % x)`
  COMPLEX_MUL_RNEG;;

let CVECTOR_NEG_0 = CVECTOR_MAP_PROPERTY
  `--cvector_zero = cvector_zero`
  COMPLEX_NEG_0;;

let CVECTOR_NEG_EQ_0 = CVECTOR_MAP_PROPERTY
  `!x:complex^N. --x = cvector_zero <=> x = cvector_zero`
  COMPLEX_NEG_EQ_0;;

let CVECTOR_ADD_AC = prove
  (`!x y z:complex^N.
    (x + y = y + x) /\ ((x + y) + z = x + y + z) /\ (x + y + z = y + x + z)`,
  MESON_TAC[CVECTOR_ADD_SYM;CVECTOR_ADD_ASSOC]);;

let CVECTOR_MUL_LCANCEL = prove
  (`!a x y:complex^N. a % x = a % y <=> a = Cx(&0) \/ x = y`,
  MESON_TAC[CVECTOR_MUL_EQ_0;CVECTOR_SUB_LDISTRIB;CVECTOR_SUB_EQ]);;

let CVECTOR_MUL_RCANCEL = prove
  (`!a b x:complex^N. a % x = b % x <=> a = b \/ x = cvector_zero`,
  MESON_TAC[CVECTOR_MUL_EQ_0;CVECTOR_SUB_RDISTRIB;COMPLEX_SUB_0;CVECTOR_SUB_EQ]);;


(* ========================================================================= *)
(* LINEARITY                                                                 *)
(* ========================================================================= *)

let clinear = new_definition
  `clinear (f:complex^M->complex^N)
    <=> (!x y. f(x + y) = f(x) + f(y)) /\ (!c x. f(c % x) = c % f(x))`;;

let COMMON_TAC additional_thms =
  SIMP_TAC[clinear] THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CART_EQ]
  THEN SIMP_TAC(CVECTOR_ADD_COMPONENT::CVECTOR_MUL_COMPONENT::additional_thms)
  THEN SIMPLE_COMPLEX_ARITH_TAC;;

let CLINEAR_COMPOSE_CMUL = prove
 (`!f:complex^M->complex^N c. clinear f ==> clinear (\x. c % f x)`,
 COMMON_TAC[]);;

let CLINEAR_COMPOSE_NEG = prove
 (`!f:complex^M->complex^N. clinear f ==> clinear (\x. --(f x))`,
 COMMON_TAC[CVECTOR_NEG_COMPONENT]);;

let CLINEAR_COMPOSE_ADD = prove
 (`!f:complex^M->complex^N g. clinear f /\ clinear g ==> clinear (\x. f x + g x)`,
 COMMON_TAC[]);;

let CLINEAR_COMPOSE_SUB = prove
 (`!f:complex^M->complex^N g. clinear f /\ clinear g ==> clinear (\x. f x - g x)`,
 COMMON_TAC[CVECTOR_SUB_COMPONENT]);;

let CLINEAR_COMPOSE = prove
 (`!f:complex^M->complex^N g. clinear f /\ clinear g ==> clinear (g o f)`,
 SIMP_TAC[clinear;o_THM]);;

let CLINEAR_ID = prove
 (`clinear (\x:complex^N. x)`,
 REWRITE_TAC[clinear]);;

let CLINEAR_I = prove
 (`clinear (I:complex^N->complex^N)`,
  REWRITE_TAC[I_DEF;CLINEAR_ID]);;

let CLINEAR_ZERO = prove
 (`clinear ((\x. cvector_zero):complex^M->complex^N)`,
 COMMON_TAC[CVECTOR_ZERO_COMPONENT]);;

let CLINEAR_NEGATION = prove
 (`clinear ((--):complex^N->complex^N)`,
 COMMON_TAC[CVECTOR_NEG_COMPONENT]);;

let CLINEAR_VMUL_COMPONENT = prove
 (`!f:complex^M->complex^N v:complex^P k.
     clinear f /\ 1 <= k /\ k <= dimindex(:N) ==> clinear (\x. (f x)$k % v)`,
 COMMON_TAC[]);;

let CLINEAR_0 = prove
 (`!f:complex^M->complex^N. clinear f ==> (f cvector_zero = cvector_zero)`,
  MESON_TAC[CVECTOR_MUL_LZERO;clinear]);;

let CLINEAR_CMUL = prove
 (`!f:complex^M->complex^N c x. clinear f ==> (f (c % x) = c % f x)`,
  SIMP_TAC[clinear]);;

let CLINEAR_NEG = prove
 (`!f:complex^M->complex^N x. clinear f ==> (f (--x) = --(f x))`,
  ONCE_REWRITE_TAC[CVECTOR_NEG_MINUS1] THEN SIMP_TAC[CLINEAR_CMUL]);;

let CLINEAR_ADD = prove
 (`!f:complex^M->complex^N x y. clinear f ==> (f (x + y) = f x + f y)`,
  SIMP_TAC[clinear]);;

let CLINEAR_SUB = prove
 (`!f:complex^M->complex^N x y. clinear f ==> (f(x - y) = f x - f y)`,
  SIMP_TAC[CVECTOR_SUB;CLINEAR_ADD;CLINEAR_NEG]);;

let CLINEAR_INJECTIVE_0 = prove
 (`!f:complex^M->complex^N.
  clinear f
   ==> ((!x y. f x = f y ==> x = y)
    <=> (!x. f x = cvector_zero ==> x = cvector_zero))`,
  ONCE_REWRITE_TAC[GSYM CVECTOR_SUB_EQ]
  THEN SIMP_TAC[CVECTOR_SUB_RZERO;GSYM CLINEAR_SUB]
  THEN MESON_TAC[CVECTOR_SUB_RZERO]);;



(* ========================================================================= *)
(* PASTING COMPLEX VECTORS                                                   *)
(* ========================================================================= *)

let CLINEAR_FSTCART_SNDCART = prove
  (`clinear fstcart /\ clinear sndcart`,
  SIMP_TAC[clinear;fstcart;sndcart;CART_EQ;LAMBDA_BETA;CVECTOR_ADD_COMPONENT;
    CVECTOR_MUL_COMPONENT; DIMINDEX_FINITE_SUM;
    ARITH_RULE `x <= a ==> x <= a + b:num`;
    ARITH_RULE `x <= b ==> x + a <= a + b:num`]);;

let FSTCART_CLINEAR = CONJUNCT1 CLINEAR_FSTCART_SNDCART;;
let SNDCART_CLINEAR = CONJUNCT2 CLINEAR_FSTCART_SNDCART;;

let FSTCART_SNDCART_CVECTOR_ZERO = prove
  (`fstcart cvector_zero = cvector_zero /\ sndcart cvector_zero = cvector_zero`,
  SIMP_TAC[CVECTOR_ZERO_COMPONENT;fstcart;sndcart;LAMBDA_BETA;CART_EQ;
    DIMINDEX_FINITE_SUM;ARITH_RULE `x <= a ==> x <= a + b:num`;
    ARITH_RULE `x <= b ==> x + a <= a + b:num`]);;

let FSTCART_CVECTOR_ZERO = CONJUNCT1 FSTCART_SNDCART_CVECTOR_ZERO;;
let SNDCART_CVECTOR_ZERO = CONJUNCT2 FSTCART_SNDCART_CVECTOR_ZERO;;

let FSTCART_SNDCART_CVECTOR_ADD = prove
 (`!x:complex^(M,N)finite_sum y.
  fstcart(x + y) = fstcart(x) + fstcart(y)
  /\ sndcart(x + y) = sndcart(x) + sndcart(y)`,
  REWRITE_TAC[REWRITE_RULE[clinear] CLINEAR_FSTCART_SNDCART]);;

let FSTCART_SNDCART_CVECTOR_MUL = prove
  (`!x:complex^(M,N)finite_sum c.
  fstcart(c % x) = c % fstcart(x) /\ sndcart(c % x) = c % sndcart(x)`,
  REWRITE_TAC[REWRITE_RULE[clinear] CLINEAR_FSTCART_SNDCART]);;

let PASTECART_TAC xs =
  REWRITE_TAC(PASTECART_EQ::FSTCART_PASTECART::SNDCART_PASTECART::xs);;

let PASTECART_CVECTOR_ZERO = prove
  (`pastecart (cvector_zero:complex^N) (cvector_zero:complex^M) = cvector_zero`,
  PASTECART_TAC[FSTCART_SNDCART_CVECTOR_ZERO]);;

let PASTECART_EQ_CVECTOR_ZERO = prove
  (`!x:complex^N y:complex^M.
    pastecart x y = cvector_zero <=> x = cvector_zero /\ y = cvector_zero`,
  PASTECART_TAC [FSTCART_SNDCART_CVECTOR_ZERO]);;

let PASTECART_CVECTOR_ADD = prove
  (`!x1 y2 x2:complex^N y2:complex^M.
  pastecart x1 y1 + pastecart x2 y2 = pastecart (x1 + x2) (y1 + y2)`,
  PASTECART_TAC [FSTCART_SNDCART_CVECTOR_ADD]);;

let PASTECART_CVECTOR_MUL = prove
  (`!x1 x2 c:complex.
  pastecart (c % x1) (c % y1) = c % pastecart x1 y1`, PASTECART_TAC [FSTCART_SNDCART_CVECTOR_MUL]);;


(* ========================================================================= *)
(* REAL AND IMAGINARY VECTORS                                                *)
(* ========================================================================= *)

let cvector_re = new_definition
  `cvector_re :complex^N -> real^N = vector_map Re`;;
let cvector_im = new_definition
  `cvector_im :complex^N -> real^N = vector_map Im`;;
let vector_to_cvector = new_definition
  `vector_to_cvector :real^N -> complex^N = vector_map Cx`;;

let CVECTOR_RE_COMPONENT = prove
  (`!x:complex^N i. (cvector_re x)$i = Re (x$i)`,
  REWRITE_TAC[cvector_re;VECTOR_MAP_COMPONENT]);;
let CVECTOR_IM_COMPONENT = prove
  (`!x:complex^N i. (cvector_im x)$i = Im (x$i)`,
  REWRITE_TAC[cvector_im;VECTOR_MAP_COMPONENT]);;
let VECTOR_TO_CVECTOR_COMPONENT = prove
  (`!x:real^N i. (vector_to_cvector x)$i = Cx(x$i)`,
  REWRITE_TAC[vector_to_cvector;VECTOR_MAP_COMPONENT]);;

let VECTOR_TO_CVECTOR_ZERO = prove
  (`vector_to_cvector (vec 0) = cvector_zero:complex^N`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_ZERO_COMPONENT;
    VEC_COMPONENT]);;

let VECTOR_TO_CVECTOR_ZERO_EQ = prove
  (`!x:real^N. vector_to_cvector x = cvector_zero <=> x = vec 0`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[VECTOR_TO_CVECTOR_ZERO]
  THEN ONCE_REWRITE_TAC[CART_EQ]
  THEN SIMP_TAC[VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_ZERO_COMPONENT;
    VEC_COMPONENT;CX_INJ]);;

let CVECTOR_ZERO_VEC0 = prove
  (`!x:complex^N. x = cvector_zero <=> cvector_re x = vec 0 /\ cvector_im x = vec 0`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_ZERO_COMPONENT;CVECTOR_RE_COMPONENT;
    CVECTOR_IM_COMPONENT;VEC_COMPONENT;COMPLEX_EQ;RE_CX;IM_CX]
  THEN MESON_TAC[]);;

let VECTOR_TO_CVECTOR_MUL = prove
  (`!a x:real^N. vector_to_cvector (a % x) = Cx a % vector_to_cvector x`,
  ONCE_REWRITE_TAC[CART_EQ] THEN REWRITE_TAC[VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_MUL_COMPONENT;VECTOR_MUL_COMPONENT;CX_MUL]);;

let CVECTOR_EQ = prove
  (`!x:complex^N y z.
    x = vector_to_cvector y + ii % vector_to_cvector z
    <=> cvector_re x = y /\ cvector_im x = z`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_ADD_COMPONENT;CVECTOR_MUL_COMPONENT;
    CVECTOR_RE_COMPONENT;CVECTOR_IM_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT]
  THEN REWRITE_TAC[COMPLEX_EQ;RE_CX;IM_CX;RE_ADD;IM_ADD;RE_MUL_II;REAL_NEG_0;
    REAL_ADD_RID;REAL_ADD_LID;IM_MUL_II] THEN MESON_TAC[]);;

let CVECTOR_RE_VECTOR_TO_CVECTOR = prove
  (`!x:real^N. cvector_re (vector_to_cvector x) = x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_RE_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;RE_CX]);;

let CVECTOR_IM_VECTOR_TO_CVECTOR = prove
  (`!x:real^N. cvector_im (vector_to_cvector x) = vec 0`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;IM_CX;
    VEC_COMPONENT]);;

let CVECTOR_IM_VECTOR_TO_CVECTOR_IM = prove
  (`!x:real^N. cvector_im (ii % vector_to_cvector x) = x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;IM_CX;
    VEC_COMPONENT;CVECTOR_MUL_COMPONENT;IM_MUL_II;RE_CX]);;

let VECTOR_TO_CVECTOR_CVECTOR_RE_IM = prove
  (`!x:complex^N.
    vector_to_cvector (cvector_re x) + ii % vector_to_cvector (cvector_im x)
      = x`,
  GEN_TAC THEN MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC[CVECTOR_EQ]);;

let CVECTOR_IM_VECTOR_TO_CVECTOR_RE_IM = prove
  (`!x y:real^N. cvector_im (vector_to_cvector x + ii % vector_to_cvector y) = y`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;CVECTOR_ADD_COMPONENT;
    CVECTOR_MUL_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;IM_ADD;IM_CX;IM_MUL_II;
    RE_CX;REAL_ADD_LID]);;

let CVECTOR_RE_VECTOR_TO_CVECTOR_RE_IM = prove
  (`!x y:real^N. cvector_re (vector_to_cvector x + ii % vector_to_cvector y)= x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_RE_COMPONENT;CVECTOR_ADD_COMPONENT;
    CVECTOR_MUL_COMPONENT;RE_ADD;VECTOR_TO_CVECTOR_COMPONENT;RE_CX;RE_MUL_CX;
    RE_II;REAL_MUL_LZERO;REAL_ADD_RID]);;

let CVECTOR_RE_ADD = prove
  (`!x y:complex^N. cvector_re (x+y) = cvector_re x + cvector_re y`,
  ONCE_REWRITE_TAC[CART_EQ] THEN REWRITE_TAC[CVECTOR_RE_COMPONENT;
    VECTOR_ADD_COMPONENT;CVECTOR_ADD_COMPONENT;RE_ADD]);;

let CVECTOR_IM_ADD = prove
  (`!x y:complex^N. cvector_im (x+y) = cvector_im x + cvector_im y`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;VECTOR_ADD_COMPONENT;
    CVECTOR_ADD_COMPONENT;IM_ADD]);;

let CVECTOR_RE_MUL = prove
  (`!a x:complex^N. cvector_re (Cx a % x) = a % cvector_re x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_RE_COMPONENT;VECTOR_MUL_COMPONENT;
    CVECTOR_MUL_COMPONENT;RE_MUL_CX]);;

let CVECTOR_IM_MUL = prove
  (`!a x:complex^N. cvector_im (Cx a % x) = a % cvector_im x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;VECTOR_MUL_COMPONENT;
    CVECTOR_MUL_COMPONENT;IM_MUL_CX]);;

let CVECTOR_RE_VECTOR_MAP = prove
  (`!f v:A^N. cvector_re (vector_map f v) = vector_map (Re o f) v`,
  REWRITE_TAC[cvector_re;VECTOR_MAP_VECTOR_MAP]);;

let CVECTOR_IM_VECTOR_MAP = prove
  (`!f v:A^N. cvector_im (vector_map f v) = vector_map (Im o f) v`,
  REWRITE_TAC[cvector_im;VECTOR_MAP_VECTOR_MAP]);;

let VECTOR_MAP_CVECTOR_RE = prove
  (`!f:real->A v:complex^N.
    vector_map f (cvector_re v) = vector_map (f o Re) v`,
  REWRITE_TAC[cvector_re;VECTOR_MAP_VECTOR_MAP]);;

let VECTOR_MAP_CVECTOR_IM = prove
  (`!f:real->A v:complex^N.
    vector_map f (cvector_im v) = vector_map (f o Im) v`,
  REWRITE_TAC[cvector_im;VECTOR_MAP_VECTOR_MAP]);;

let CVECTOR_RE_VECTOR_MAP2 = prove
  (`!f v1:A^N v2:B^N.
    cvector_re (vector_map2 f v1 v2) = vector_map2 (\x y. Re (f x y)) v1 v2`,
  REWRITE_TAC[cvector_re;VECTOR_MAP_VECTOR_MAP2]);;

let CVECTOR_IM_VECTOR_MAP2 = prove
  (`!f v1:A^N v2:B^N.
    cvector_im (vector_map2 f v1 v2) = vector_map2 (\x y. Im (f x y)) v1 v2`,
  REWRITE_TAC[cvector_im;VECTOR_MAP_VECTOR_MAP2]);;


(* ========================================================================= *)
(* FLATTENING COMPLEX VECTORS INTO REAL VECTORS                              *)
(*                                                                           *)
(* Note:                                                                     *)
(* Theoretically, the following could be defined more generally for matrices *)
(* instead of complex vectors, but this would require a "finite_prod" type   *)
(* constructor, which is not available right now, and which, at first sight, *)
(* would probably require dependent types.                                   *)
(* ========================================================================= *)

let cvector_flatten = new_definition
  `cvector_flatten (v:complex^N) :real^(N,N) finite_sum =
    pastecart (cvector_re v) (cvector_im v)`;;

let FLATTEN_RE_IM_COMPONENT = prove
  (`!v:complex^N i.
  1 <= i /\ i <= 2 * dimindex(:N)
    ==> (cvector_flatten v)$i =
      if i <= dimindex(:N)
      then (cvector_re v)$i
      else (cvector_im v)$(i-dimindex(:N))`,
  SIMP_TAC[MULT_2;GSYM DIMINDEX_FINITE_SUM;cvector_flatten;pastecart;
    LAMBDA_BETA]);;

let complex_vector = new_definition
  `complex_vector (v1,v2) :complex^N
    = vector_map2 (\x y. Cx x + ii * Cx y) v1 v2`;;

let COMPLEX_VECTOR_TRANSPOSE = prove(
  `!v1 v2:real^N.
  complex_vector (v1,v2) = vector_to_cvector v1 + ii % vector_to_cvector v2`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN SIMP_TAC[complex_vector;CVECTOR_ADD_COMPONENT;CVECTOR_MUL_COMPONENT;
    VECTOR_TO_CVECTOR_COMPONENT;VECTOR_MAP2_COMPONENT]);;

let cvector_unflatten = new_definition
  `cvector_unflatten (v:real^(N,N) finite_sum) :complex^N
    = complex_vector (fstcart v, sndcart v)`;;

let UNFLATTEN_FLATTEN = prove
  (`cvector_unflatten o cvector_flatten = I :complex^N -> complex^N`,
  REWRITE_TAC[FUN_EQ_THM;o_DEF;I_DEF;cvector_flatten;cvector_unflatten;
    FSTCART_PASTECART;SNDCART_PASTECART;COMPLEX_VECTOR_TRANSPOSE;
    VECTOR_TO_CVECTOR_CVECTOR_RE_IM]);;

let FLATTEN_UNFLATTEN = prove
  (`cvector_flatten o cvector_unflatten =
    I :real^(N,N) finite_sum -> real^(N,N) finite_sum`,
  REWRITE_TAC[FUN_EQ_THM;o_DEF;I_DEF;cvector_flatten;cvector_unflatten;
    PASTECART_FST_SND;COMPLEX_VECTOR_TRANSPOSE;
    CVECTOR_RE_VECTOR_TO_CVECTOR_RE_IM;CVECTOR_IM_VECTOR_TO_CVECTOR_RE_IM]);;

let FLATTEN_CLINEAR = prove
  (`!f:complex^N->complex^M.
    clinear f ==> linear (cvector_flatten o f o cvector_unflatten)`,
  REWRITE_TAC[clinear;linear;cvector_flatten;cvector_unflatten;o_DEF;
    FSTCART_ADD;SNDCART_ADD;PASTECART_ADD;complex_vector;GSYM PASTECART_CMUL]
  THEN REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE MK_COMB_TAC)
  THEN REWRITE_TAC(map GSYM [CVECTOR_RE_ADD;CVECTOR_IM_ADD;CVECTOR_RE_MUL;
    CVECTOR_IM_MUL])
  THEN AP_TERM_TAC THEN ASSUM_LIST (REWRITE_TAC o map GSYM)
  THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC[CART_EQ]
  THEN SIMP_TAC[VECTOR_MAP2_COMPONENT;VECTOR_ADD_COMPONENT;
    CVECTOR_ADD_COMPONENT;CX_ADD;VECTOR_MUL_COMPONENT;CVECTOR_MUL_COMPONENT;
    FSTCART_CMUL;SNDCART_CMUL;CX_MUL]
  THEN SIMPLE_COMPLEX_ARITH_TAC);;

let FLATTEN_MAP = prove
  (`!f g.
    f = vector_map g
      ==> !x:complex^N.
        cvector_flatten (vector_map f x) = vector_map g (cvector_flatten x)`,
  SIMP_TAC[cvector_flatten;CVECTOR_RE_VECTOR_MAP;CVECTOR_IM_VECTOR_MAP;
    GSYM PASTECART_VECTOR_MAP;VECTOR_MAP_CVECTOR_RE;VECTOR_MAP_CVECTOR_IM;
    o_DEF;IM_DEF;RE_DEF;VECTOR_MAP_COMPONENT]);;

let FLATTEN_NEG = prove
  (`!x:complex^N. cvector_flatten (--x) = --(cvector_flatten x)`,
  REWRITE_TAC[cvector_neg;MATCH_MP FLATTEN_MAP COMPLEX_NEG_IS_A_MAP]
  THEN REWRITE_TAC[VECTOR_NEG_IS_A_MAP]);;

let CVECTOR_NEG_ALT = prove
  (`!x:complex^N. --x = cvector_unflatten (--(cvector_flatten x))`,
  REWRITE_TAC[GSYM FLATTEN_NEG;
    REWRITE_RULE[o_DEF;FUN_EQ_THM;I_DEF] UNFLATTEN_FLATTEN]);;

let FLATTEN_MAP2 = prove(
  `!f g.
    f = vector_map2 g ==>
      !x y:complex^N.
        cvector_flatten (vector_map2 f x y) =
          vector_map2 g (cvector_flatten x) (cvector_flatten y)`,
  SIMP_TAC[cvector_flatten;CVECTOR_RE_VECTOR_MAP2;CVECTOR_IM_VECTOR_MAP2;
    CVECTOR_RE_VECTOR_MAP2;GSYM PASTECART_VECTOR_MAP2]
  THEN REWRITE_TAC[cvector_re;cvector_im;VECTOR_MAP2_LVECTOR_MAP;
    VECTOR_MAP2_RVECTOR_MAP]
  THEN REPEAT MK_COMB_TAC
  THEN REWRITE_TAC[FUN_EQ_THM;IM_DEF;RE_DEF;VECTOR_MAP2_COMPONENT;o_DEF]);;

let FLATTEN_ADD = prove
  (`!x y:complex^N.
    cvector_flatten (x+y) = cvector_flatten x + cvector_flatten y`,
  REWRITE_TAC[cvector_add;MATCH_MP FLATTEN_MAP2 COMPLEX_ADD_IS_A_MAP]
  THEN REWRITE_TAC[VECTOR_ADD_IS_A_MAP]);;

let CVECTOR_ADD_ALT = prove
  (`!x y:complex^N.
    x+y = cvector_unflatten (cvector_flatten x + cvector_flatten y)`,
  REWRITE_TAC[GSYM FLATTEN_ADD;
    REWRITE_RULE[o_DEF;FUN_EQ_THM;I_DEF] UNFLATTEN_FLATTEN]);;

let FLATTEN_SUB = prove
  (`!x y:complex^N. cvector_flatten (x-y) = cvector_flatten x - cvector_flatten y`,
  REWRITE_TAC[cvector_sub;MATCH_MP FLATTEN_MAP2 COMPLEX_SUB_IS_A_MAP]
  THEN REWRITE_TAC[VECTOR_SUB_IS_A_MAP]);;

let CVECTOR_SUB_ALT = prove
  (`!x y:complex^N. x-y = cvector_unflatten (cvector_flatten x - cvector_flatten y)`,
  REWRITE_TAC[GSYM FLATTEN_SUB;
    REWRITE_RULE[o_DEF;FUN_EQ_THM;I_DEF] UNFLATTEN_FLATTEN]);;


(* ========================================================================= *)
(* CONJUGATE VECTOR.                                                         *)
(* ========================================================================= *)

let cvector_cnj = new_definition
  `cvector_cnj : complex^N->complex^N = vector_map cnj`;;

let CVECTOR_MAP_PROPERTY thm =
  VECTOR_MAP_PROPERTY thm [cvector_zero;cvector_add;cvector_sub;cvector_neg;
  cvector_mul;cvector_cnj;cvector_re;cvector_im];;

let CVECTOR_CNJ_ADD = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. cvector_cnj (x+y) = cvector_cnj x + cvector_cnj y`
  CNJ_ADD;;

let CVECTOR_CNJ_SUB = CVECTOR_MAP_PROPERTY
  `!x y:complex^N. cvector_cnj (x-y) = cvector_cnj x - cvector_cnj y`
  CNJ_SUB;;

let CVECTOR_CNJ_NEG = CVECTOR_MAP_PROPERTY
  `!x:complex^N. cvector_cnj (--x) = --(cvector_cnj x)`
  CNJ_NEG;;

let CVECTOR_RE_CNJ = CVECTOR_MAP_PROPERTY
  `!x:complex^N. cvector_re (cvector_cnj x) = cvector_re x`
  RE_CNJ;;

let CVECTOR_IM_CNJ = prove
  (`!x:complex^N. cvector_im (cvector_cnj x) = --(cvector_im x)`,
  VECTOR_MAP_PROPERTY_TAC[cvector_im;cvector_cnj;VECTOR_NEG_IS_A_MAP] IM_CNJ);;

let CVECTOR_CNJ_CNJ = CVECTOR_MAP_PROPERTY
  `!x:complex^N. cvector_cnj (cvector_cnj x) = x`
  CNJ_CNJ;;


(* ========================================================================= *)
(* CROSS PRODUCTS IN COMPLEX^3.                                              *)
(* ========================================================================= *)

prioritize_vector();;

parse_as_infix("ccross",(20,"right"));;

let ccross = new_definition
  `((ccross):complex^3 -> complex^3 -> complex^3) x y = vector [
    x$2 * y$3 - x$3 * y$2;
    x$3 * y$1 - x$1 * y$3;
    x$1 * y$2 - x$2 * y$1
  ]`;;

let CCROSS_COMPONENT = prove
  (`!x y:complex^3.
  (x ccross y)$1 = x$2 * y$3 - x$3 * y$2
  /\ (x ccross y)$2 = x$3 * y$1 - x$1 * y$3
  /\ (x ccross y)$3 = x$1 * y$2 - x$2 * y$1`,
  REWRITE_TAC[ccross;VECTOR_3]);;

(* simple handy instantiation of CART_EQ for dimension 3*)
let CART_EQ3 = prove
  (`!x y:complex^3. x = y <=> x$1 = y$1 /\ x$2 = y$2 /\ x$3 = y$3`,
  GEN_REWRITE_TAC (PATH_CONV "rbrblr") [CART_EQ]
  THEN REWRITE_TAC[DIMINDEX_3;FORALL_3]);;

let CCROSS_TAC lemmas =
  REWRITE_TAC(CART_EQ3::CCROSS_COMPONENT::lemmas)
  THEN SIMPLE_COMPLEX_ARITH_TAC;;

let CCROSS_LZERO = prove
  (`!x:complex^3. cvector_zero ccross x = cvector_zero`,
  CCROSS_TAC[CVECTOR_ZERO_COMPONENT]);;

let CCROSS_RZERO = prove
  (`!x:complex^3. x ccross cvector_zero = cvector_zero`,
  CCROSS_TAC[CVECTOR_ZERO_COMPONENT]);;

let CCROSS_SKEW = prove
  (`!x y:complex^3. (x ccross y) = --(y ccross x)`,
  CCROSS_TAC[CVECTOR_NEG_COMPONENT]);;

let CCROSS_REFL = prove
  (`!x:complex^3. x ccross x = cvector_zero`,
  CCROSS_TAC[CVECTOR_ZERO_COMPONENT]);;

let CCROSS_LADD = prove
  (`!x y z:complex^3. (x + y) ccross z = (x ccross z) + (y ccross z)`,
  CCROSS_TAC[CVECTOR_ADD_COMPONENT]);;

let CCROSS_RADD = prove
  (`!x y z:complex^3. x ccross(y + z) = (x ccross y) + (x ccross z)`,
  CCROSS_TAC[CVECTOR_ADD_COMPONENT]);;

let CCROSS_LMUL = prove
  (`!c x y:complex^3. (c % x) ccross y = c % (x ccross y)`,
  CCROSS_TAC[CVECTOR_MUL_COMPONENT]);;

let CCROSS_RMUL = prove
  (`!c x y:complex^3. x ccross (c % y) = c % (x ccross y)`,
  CCROSS_TAC[CVECTOR_MUL_COMPONENT]);;

let CCROSS_LNEG = prove
  (`!x y:complex^3. (--x) ccross y = --(x ccross y)`,
  CCROSS_TAC[CVECTOR_NEG_COMPONENT]);;

let CCROSS_RNEG = prove
  (`!x y:complex^3. x ccross (--y) = --(x ccross y)`,
  CCROSS_TAC[CVECTOR_NEG_COMPONENT]);;

let CCROSS_JACOBI = prove
 (`!(x:complex^3) y z.
    x ccross (y ccross z) + y ccross (z ccross x) + z ccross (x ccross y) =
      cvector_zero`,
  REWRITE_TAC[CART_EQ3]
  THEN REWRITE_TAC[CVECTOR_ADD_COMPONENT;CCROSS_COMPONENT;
    CVECTOR_ZERO_COMPONENT] THEN SIMPLE_COMPLEX_ARITH_TAC);;


(* ========================================================================= *)
(* DOT PRODUCTS IN COMPLEX^N                                                 *)
(*                                                                           *)
(* Only difference with the real case:                                       *)
(* we take the conjugate of the 2nd argument                                 *)
(* ========================================================================= *)

prioritize_complex();;

parse_as_infix("cdot",(20,"right"));;

let cdot = new_definition
  `(cdot) (x:complex^N) (y:complex^N) =
    vsum (1..dimindex(:N)) (\i. x$i * cnj(y$i))`;;

(* The dot product is symmetric MODULO the conjugate *)
let CDOT_SYM = prove
  (`!x:complex^N y. x cdot y = cnj (y cdot x)`,
  REWRITE_TAC[cdot]
  THEN REWRITE_TAC[MATCH_MP (SPEC_ALL CNJ_VSUM) (SPEC `dimindex (:N)` (GEN_ALL
    (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[CNJ_MUL;CNJ_CNJ;COMPLEX_MUL_SYM]);;

let REAL_CDOT_SELF = prove
  (`!x:complex^N. real(x cdot x)`,
  REWRITE_TAC[REAL_CNJ;GSYM CDOT_SYM]);;

(* The following theorems are usual axioms of the hermitian dot product, they are proved later on.
 * let CDOT_SELF_POS = prove(`!x:complex^N. &0 <= real_of_complex (x cdot x)`, ...
 * let CDOT_EQ_0 = prove(`!x:complex^N. x cdot x = Cx(&0) <=> x = cvector_zero`
 *)

let CDOT_LADD = prove
  (`!x:complex^N y z. (x + y) cdot z = (x cdot z) + (y cdot z)`,
  REWRITE_TAC[cdot]
  THEN REWRITE_TAC[MATCH_MP (GSYM VSUM_ADD) (SPEC `dimindex (:N)` (GEN_ALL
    (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC
  THEN REWRITE_TAC[FUN_EQ_THM]
  THEN REWRITE_TAC[SPECL [`(x:real^2^N)$(x':num)`;`(y:real^2^N)$(x':num)`;
    `cnj ((z:real^2^N)$(x':num))`] (GSYM COMPLEX_ADD_RDISTRIB)]
  THEN REWRITE_TAC[CVECTOR_ADD_COMPONENT]);;

let CDOT_RADD = prove
  (`!x:complex^N y z. x cdot (y + z) = (x cdot y) + (x cdot z)`,
  REWRITE_TAC[cdot]
  THEN REWRITE_TAC[MATCH_MP (GSYM VSUM_ADD) (SPEC `dimindex (:N)` (GEN_ALL
    (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC
  THEN REWRITE_TAC[FUN_EQ_THM]
  THEN REWRITE_TAC[SPECL [`(x:real^2^N)$(x':num)`; `cnj((y:real^2^N)$(x':num))`;
  `cnj ((z:real^2^N)$(x':num))`] (GSYM COMPLEX_ADD_LDISTRIB)]
  THEN REWRITE_TAC[CNJ_ADD; CVECTOR_ADD_COMPONENT]);;

let CDOT_LSUB = prove
  (`!x:complex^N y z. (x - y) cdot z = (x cdot z) - (y cdot z)`,
  REWRITE_TAC[cdot]
  THEN REWRITE_TAC[MATCH_MP (GSYM VSUM_SUB) (SPEC `dimindex (:N)` (GEN_ALL
    (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC
  THEN REWRITE_TAC[FUN_EQ_THM]
  THEN REWRITE_TAC[SPECL [`(x:real^2^N)$(x':num)`; `(y:real^2^N)$(x':num)`;
    `cnj ((z:real^2^N)$(x':num))`] (GSYM COMPLEX_SUB_RDISTRIB)]
  THEN REWRITE_TAC[CVECTOR_SUB_COMPONENT]);;

let CDOT_RSUB = prove
  (`!x:complex^N y z. x cdot (y - z) = (x cdot y) - (x cdot z)`,
  REWRITE_TAC[cdot]
  THEN REWRITE_TAC[MATCH_MP (GSYM VSUM_SUB) (SPEC `dimindex (:N)` (GEN_ALL
    (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC
  THEN REWRITE_TAC[FUN_EQ_THM]
  THEN REWRITE_TAC[SPECL [`(x:real^2^N)$(x':num)`; `cnj((y:real^2^N)$(x':num))`;
    `cnj ((z:real^2^N)$(x':num))`] (GSYM COMPLEX_SUB_LDISTRIB)]
  THEN REWRITE_TAC[CNJ_SUB; CVECTOR_SUB_COMPONENT]);;

let CDOT_LMUL = prove
  (`!c:complex x:complex^N y. (c % x) cdot y = c * (x cdot y)`,
  REWRITE_TAC[cdot]
  THEN REWRITE_TAC[MATCH_MP (GSYM VSUM_COMPLEX_LMUL) (SPEC `dimindex (:N)`
    (GEN_ALL (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE]
    HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[CVECTOR_MUL_COMPONENT; GSYM COMPLEX_MUL_ASSOC]);;

let CDOT_RMUL = prove
  (`!c:complex x:complex^N x y. x cdot (c % y) = cnj c * (x cdot y)`,
  REWRITE_TAC[cdot]
  THEN REWRITE_TAC[MATCH_MP (GSYM VSUM_COMPLEX_LMUL) (SPEC `dimindex (:N)`
    (GEN_ALL (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE]
    HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[CVECTOR_MUL_COMPONENT; CNJ_MUL; COMPLEX_MUL_AC]);;

let CDOT_LNEG = prove
  (`!x:complex^N y. (--x) cdot y = --(x cdot y)`,
  REWRITE_TAC[cdot] THEN ONCE_REWRITE_TAC[COMPLEX_NEG_MINUS1]
  THEN REWRITE_TAC[MATCH_MP (GSYM VSUM_COMPLEX_LMUL) (SPEC `dimindex (:N)`
    (GEN_ALL (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE]
    HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[CVECTOR_NEG_COMPONENT] THEN ONCE_REWRITE_TAC[GSYM
    COMPLEX_NEG_MINUS1] THEN REWRITE_TAC[COMPLEX_NEG_LMUL]);;

let CDOT_RNEG = prove
  (`!x:complex^N y. x cdot (--y) = --(x cdot y)`,
  REWRITE_TAC[cdot] THEN ONCE_REWRITE_TAC[COMPLEX_NEG_MINUS1]
  THEN REWRITE_TAC[MATCH_MP (GSYM VSUM_COMPLEX_LMUL) (SPEC `dimindex (:N)`
    (GEN_ALL (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE]
    HAS_SIZE_NUMSEG_1)))))]
  THEN ONCE_REWRITE_TAC[GSYM COMPLEX_NEG_MINUS1]
  THEN REWRITE_TAC[CVECTOR_NEG_COMPONENT; CNJ_NEG; COMPLEX_NEG_RMUL]);;

let CDOT_LZERO = prove
  (`!x:complex^N. cvector_zero cdot x = Cx (&0)`,
  REWRITE_TAC[cdot] THEN REWRITE_TAC[CVECTOR_ZERO_COMPONENT]
  THEN REWRITE_TAC[COMPLEX_MUL_LZERO; GSYM COMPLEX_VEC_0; VSUM_0]);;

let CNJ_ZERO = prove(
  `cnj (Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[cnj;RE_CX;IM_CX;CX_DEF;REAL_NEG_0]);;

let CDOT_RZERO = prove(
  `!x:complex^N. x cdot cvector_zero = Cx (&0)`,
  REWRITE_TAC[cdot] THEN REWRITE_TAC[CVECTOR_ZERO_COMPONENT]
  THEN REWRITE_TAC[CNJ_ZERO]
  THEN REWRITE_TAC[COMPLEX_MUL_RZERO;GSYM COMPLEX_VEC_0;VSUM_0]);;

(* Cauchy Schwarz inequality: proved later on
 * let CDOT_CAUCHY_SCHWARZ = prove (`!x y:complex^N. norm (x cdot y) pow 2 <= cnorm2 x * cnorm2 y`,
 * let CDOT_CAUCHY_SCHWARZ_EQUAL = prove(`!x y:complex^N. norm (x cdot y) pow 2 = cnorm2 x * cnorm2 y <=> collinear_cvectors x y`,
*)

let CDOT3 = prove
  (`!x y:complex^3.
    x cdot y = (x$1 * cnj (y$1) + x$2 * cnj (y$2) + x$3 * cnj (y$3))`,
  REWRITE_TAC[cdot] THEN SIMP_TAC [DIMINDEX_3] THEN REWRITE_TAC[VSUM_3]);;

let ADD_CDOT_SYM = prove(
  `!x y:complex^N. x cdot y + y cdot x = Cx(&2 * Re(x cdot y))`,
  MESON_TAC[CDOT_SYM;COMPLEX_ADD_CNJ]);;


(* ========================================================================= *)
(* RELATION WITH REAL DOT AND CROSS PRODUCTS                                 *)
(* ========================================================================= *)

let CCROSS_LREAL = prove
  (`!r c.
    (vector_to_cvector r) ccross c =
      vector_to_cvector (r cross (cvector_re c))
      + ii % (vector_to_cvector (r cross (cvector_im c)))`,
  REWRITE_TAC[CART_EQ3;CVECTOR_ADD_COMPONENT;CVECTOR_MUL_COMPONENT;
    VECTOR_TO_CVECTOR_COMPONENT;CCROSS_COMPONENT;CROSS_COMPONENTS;
    CVECTOR_RE_COMPONENT;CVECTOR_IM_COMPONENT;complex_mul;RE_CX;IM_CX;CX_DEF;
    complex_sub;complex_neg;complex_add;RE;IM;RE_II;IM_II]
  THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ]
  THEN ARITH_TAC);;

let CCROSS_RREAL = prove
  (`!r c.
    c ccross (vector_to_cvector r) =
      vector_to_cvector ((cvector_re c) cross r)
      + ii % (vector_to_cvector ((cvector_im c) cross r))`,
  REWRITE_TAC[CART_EQ3;CVECTOR_ADD_COMPONENT;CVECTOR_MUL_COMPONENT;
    VECTOR_TO_CVECTOR_COMPONENT;CCROSS_COMPONENT;CROSS_COMPONENTS;
    CVECTOR_RE_COMPONENT;CVECTOR_IM_COMPONENT;complex_mul;RE_CX;IM_CX;CX_DEF;
    complex_sub;complex_neg;complex_add;RE;IM;RE_II;IM_II]
  THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ]
  THEN ARITH_TAC);;

let CDOT_LREAL = prove
  (`!r c.
    (vector_to_cvector r) cdot c =
      Cx (r dot (cvector_re c)) - ii * Cx (r dot (cvector_im c))`,
  REWRITE_TAC[cdot; dot; VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_RE_COMPONENT;
    CVECTOR_IM_COMPONENT] THEN REPEAT GEN_TAC
  THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [COMPLEX_EXPAND]
  THEN REWRITE_TAC[MATCH_MP RE_VSUM (SPEC `dimindex (:N)` (GEN_ALL (CONJUNCT1
    (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[MATCH_MP (IM_VSUM) (SPEC `dimindex (:N)` (GEN_ALL
    (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE]
      HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[RE_MUL_CX;RE_CNJ;IM_MUL_CX;IM_CNJ]
  THEN REWRITE_TAC[COMPLEX_POLY_NEG_CLAUSES] THEN REWRITE_TAC[COMPLEX_MUL_AC]
  THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM CX_MUL]
  THEN REWRITE_TAC[GSYM SUM_LMUL]
  THEN REWRITE_TAC[GSYM REAL_NEG_MINUS1;GSYM REAL_MUL_RNEG]);;

let CDOT_RREAL = prove
  (`!r c.
    c cdot (vector_to_cvector r) =
      Cx ((cvector_re c) dot r) + ii * Cx ((cvector_im c) dot r)`,
  REWRITE_TAC[cdot; dot; VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_RE_COMPONENT;
    CVECTOR_IM_COMPONENT]
  THEN REPEAT GEN_TAC
  THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [COMPLEX_EXPAND]
  THEN REWRITE_TAC[MATCH_MP RE_VSUM (SPEC `dimindex (:N)` (GEN_ALL (CONJUNCT1
    (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[MATCH_MP IM_VSUM (SPEC `dimindex (:N)` (GEN_ALL (CONJUNCT1
    (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[CNJ_CX]
  THEN REWRITE_TAC[RE_MUL_CX;RE_CNJ;IM_MUL_CX;IM_CNJ]);;


(* ========================================================================= *)
(* NORM, UNIT VECTORS.                                                       *)
(* ========================================================================= *)

let cnorm2 = new_definition
  `cnorm2 (v:complex^N) = real_of_complex (v cdot v)`;;

let CX_CNORM2 = prove
  (`!v:complex^N. Cx(cnorm2 v) = v cdot v`,
  SIMP_TAC[cnorm2;REAL_CDOT_SELF;REAL_OF_COMPLEX]);;

let CNORM2_CVECTOR_ZERO = prove
  (`cnorm2 (cvector_zero:complex^N) = &0`,
  REWRITE_TAC[cnorm2;CDOT_RZERO;REAL_OF_COMPLEX_CX]);;

let CNORM2_MODULUS = prove
  (`!x:complex^N. cnorm2 x = (vector_map norm x) dot (vector_map norm x)`,
  REWRITE_TAC[cnorm2;cdot;COMPLEX_MUL_CNJ;COMPLEX_POW_2;GSYM CX_MUL;
    VSUM_CX_NUMSEG;dot;VECTOR_MAP_COMPONENT;REAL_OF_COMPLEX_CX]);;

let CNORM2_EQ_0 = prove
  (`!x:complex^N. cnorm2 x = &0 <=> x = cvector_zero`,
  REWRITE_TAC[CNORM2_MODULUS;CX_INJ;DOT_EQ_0] THEN GEN_TAC
  THEN GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [CART_EQ]
  THEN REWRITE_TAC[VEC_COMPONENT;VECTOR_MAP_COMPONENT;COMPLEX_NORM_ZERO]
  THEN GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [CART_EQ]
  THEN REWRITE_TAC[CVECTOR_ZERO_COMPONENT]);;

let CDOT_EQ_0 = prove
  (`!x:complex^N. x cdot x = Cx(&0) <=> x = cvector_zero`,
  SIMP_TAC[TAUT `(p<=>q) <=> ((p==>q) /\ (q==>p))`;CDOT_LZERO]
  THEN GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (MESON[REAL_OF_COMPLEX_CX]
    `x = Cx y ==> real_of_complex x = y`))
  THEN REWRITE_TAC[GSYM cnorm2;CNORM2_EQ_0]);;

let CNORM2_POS = prove
  (`!x:complex^N. &0 <= cnorm2 x`, REWRITE_TAC[CNORM2_MODULUS;DOT_POS_LE]);;

let CDOT_SELF_POS = prove
  (`!x:complex^N. &0 <= real_of_complex (x cdot x)`,
  REWRITE_TAC[GSYM cnorm2;CNORM2_POS]);;

let CNORM2_MUL = prove
  (`!a x:complex^N. cnorm2 (a % x) = (norm a) pow 2 * cnorm2 x`,
  SIMP_TAC[cnorm2;CDOT_LMUL;CDOT_RMUL;
    SIMPLE_COMPLEX_ARITH `x * cnj x * y = (x * cnj x) * y`;COMPLEX_MUL_CNJ;
    REAL_OF_COMPLEX_CX;REAL_OF_COMPLEX_MUL;REAL_CX;REAL_CDOT_SELF;
    GSYM CX_POW]);;

let CNORM2_NORM2_2 = prove
  (`!x y:real^N.
    cnorm2 (vector_to_cvector x + ii % vector_to_cvector y) =
      norm x pow 2 + norm y pow 2`,
  REWRITE_TAC[cnorm2;vector_norm;cdot;CVECTOR_ADD_COMPONENT;
    CVECTOR_MUL_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;CNJ_ADD;CNJ_CX;CNJ_MUL;
    CNJ_II;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;
    SIMPLE_COMPLEX_ARITH
      `(x*x+x*(--ii)*y)+(ii*y)*x+(ii*y)*(--ii)*y = x*x-(ii*ii)*y*y`]
  THEN REWRITE_TAC[GSYM COMPLEX_POW_2;COMPLEX_POW_II_2;
    SIMPLE_COMPLEX_ARITH `x-(--Cx(&1))*y = x+y`]
  THEN SIMP_TAC[MESON[CARD_NUMSEG_1;HAS_SIZE_NUMSEG_1;FINITE_HAS_SIZE]
    `FINITE (1..dimindex(:N))`;VSUM_ADD;GSYM CX_POW;VSUM_CX;GSYM dot;
    REAL_POW_2;GSYM dot]
  THEN SIMP_TAC[GSYM CX_ADD;REAL_OF_COMPLEX_CX;GSYM REAL_POW_2;DOT_POS_LE;
    SQRT_POW_2]);;

let CNORM2_NORM2 = prove
  (`!v:complex^N.
    cnorm2 v = norm (cvector_re v) pow 2 + norm (cvector_im v) pow 2`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [GSYM
    VECTOR_TO_CVECTOR_CVECTOR_RE_IM] THEN REWRITE_TAC[CNORM2_NORM2_2]);;

let CNORM2_ALT = prove
  (`!x:complex^N. cnorm2 x = norm (x cdot x)`,
  SIMP_TAC[cnorm2;REAL_OF_COMPLEX_NORM;REAL_CDOT_SELF;EQ_SYM_EQ;REAL_ABS_REFL;
    REWRITE_RULE[cnorm2] CNORM2_POS]);;

let CNORM2_SUB = prove
  (`!x y:complex^N. cnorm2 (x-y) = cnorm2 (y-x)`,
  REWRITE_TAC[cnorm2;CDOT_LSUB;CDOT_RSUB] THEN REPEAT GEN_TAC THEN AP_TERM_TAC
  THEN SIMPLE_COMPLEX_ARITH_TAC);;

let CNORM2_VECTOR_TO_CVECTOR = prove
  (`!x:real^N. cnorm2 (vector_to_cvector x) = norm x pow 2`,
  REWRITE_TAC[CNORM2_ALT;CDOT_RREAL;CVECTOR_RE_VECTOR_TO_CVECTOR;
    CVECTOR_IM_VECTOR_TO_CVECTOR;DOT_LZERO;COMPLEX_MUL_RZERO;COMPLEX_ADD_RID;
    DOT_SQUARE_NORM;CX_POW;COMPLEX_NORM_POW;COMPLEX_NORM_CX;REAL_POW2_ABS]);;

let cnorm = new_definition
  `cnorm :complex^N->real = sqrt o cnorm2`;;

overload_interface ("norm",`cnorm:complex^N->real`);;

let CNORM_CVECTOR_ZERO = prove
  (`norm (cvector_zero:complex^N) = &0`,
  REWRITE_TAC[cnorm;CNORM2_CVECTOR_ZERO;o_DEF;SQRT_0]);;

let CNORM_POW_2 = prove
  (`!x:complex^N. norm x pow 2 = cnorm2 x`,
  SIMP_TAC[cnorm;o_DEF;SQRT_POW_2;CNORM2_POS]);;

let CNORM_NORM_2 = prove
  (`!x y:real^N.
    norm (vector_to_cvector x + ii % vector_to_cvector y) =
      sqrt(norm x pow 2 + norm y pow 2)`,
  REWRITE_TAC[cnorm;o_DEF;CNORM2_NORM2_2]);;

let CNORM_NORM = prove(
  `!v:complex^N.
    norm v = sqrt(norm (cvector_re v) pow 2 + norm (cvector_im v) pow 2)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [GSYM
    VECTOR_TO_CVECTOR_CVECTOR_RE_IM] THEN REWRITE_TAC[CNORM_NORM_2]);;

let CNORM_MUL = prove
  (`!a x:complex^N. norm (a % x) = norm a * norm x`,
  SIMP_TAC[cnorm;o_DEF;CNORM2_MUL;REAL_LE_POW_2;SQRT_MUL;CNORM2_POS;
    NORM_POS_LE;POW_2_SQRT]);;

let CNORM_EQ_0 = prove
  (`!x:complex^N. norm x = &0 <=> x = cvector_zero`,
  SIMP_TAC[cnorm;o_DEF;SQRT_EQ_0;CNORM2_POS;CNORM2_EQ_0]);;

let CNORM_POS = prove
  (`!x:complex^N. &0 <= norm x`,
  SIMP_TAC[cnorm;o_DEF;SQRT_POS_LE;CNORM2_POS]);;

let CNORM_SUB = prove
  (`!x y:complex^N. norm (x-y) = norm (y-x)`,
  REWRITE_TAC[cnorm;o_DEF;CNORM2_SUB]);;

let CNORM_VECTOR_TO_CVECTOR = prove
  (`!x:real^N. norm (vector_to_cvector x) = norm x`,
  SIMP_TAC[cnorm;o_DEF;CNORM2_VECTOR_TO_CVECTOR;POW_2_SQRT;NORM_POS_LE]);;

let CNORM_BASIS = prove
  (`!k. 1 <= k /\ k <= dimindex(:N)
    ==> norm (vector_to_cvector (basis k :real^N)) = &1`,
  SIMP_TAC[NORM_BASIS;CNORM_VECTOR_TO_CVECTOR]);;

let CNORM_BASIS_1 = prove
 (`norm(basis 1:real^N) = &1`,
  SIMP_TAC[NORM_BASIS_1;CNORM_VECTOR_TO_CVECTOR]);;

let CVECTOR_CHOOSE_SIZE = prove
  (`!c. &0 <= c ==> ?x:complex^N. norm(x) = c`,
  MESON_TAC[VECTOR_CHOOSE_SIZE;CNORM_VECTOR_TO_CVECTOR]);;

(* Triangle inequality. Proved later on using Cauchy Schwarz inequality.
 * let CNORM_TRIANGLE = prove(`!x y:complex^N. norm (x+y) <= norm x + norm y`, ...
 *)

let cunit = new_definition
  `cunit (X:complex^N) = inv(Cx(norm X))% X`;;

let CUNIT_CVECTOR_ZERO = prove
  (`cunit cvector_zero = cvector_zero:complex^N`,
  REWRITE_TAC[cunit;CNORM_CVECTOR_ZERO;COMPLEX_INV_0;CVECTOR_MUL_LZERO]);;

let CDOT_CUNIT_MUL_CUNIT = prove
  (`!x:complex^N. (cunit x cdot x) % cunit x = x`,
  GEN_TAC THEN ASM_CASES_TAC `x = cvector_zero:complex^N`
  THEN ASM_REWRITE_TAC[CUNIT_CVECTOR_ZERO;CDOT_LZERO;CVECTOR_MUL_LZERO]
  THEN SIMP_TAC[cunit;CVECTOR_MUL_ASSOC;CDOT_LMUL;
    SIMPLE_COMPLEX_ARITH `(x*y)*x=(x*x)*y`;GSYM COMPLEX_INV_MUL;GSYM CX_MUL;
    GSYM REAL_POW_2;cnorm;o_DEF;CNORM2_POS;SQRT_POW_2]
  THEN ASM_SIMP_TAC[cnorm2;REAL_OF_COMPLEX;REAL_CDOT_SELF;CDOT_EQ_0;
    CNORM2_CVECTOR_ZERO;CVECTOR_MUL_RZERO;CNORM2_EQ_0;COMPLEX_MUL_LINV;
    CVECTOR_MUL_ID]);;


(* ========================================================================= *)
(* COLLINEARITY                                                              *)
(* ========================================================================= *)

(* Definition of collinearity between complex vectors.
 * Note: This is different from collinearity between points (which is the one defined in HOL-Light library)
 *)
let collinear_cvectors = new_definition
  `collinear_cvectors x (y:complex^N) <=> ?a. y = a % x \/ x = a % y`;;

let COLLINEAR_CVECTORS_SYM = prove
  (`!x y:complex^N. collinear_cvectors x y <=> collinear_cvectors y x`,
  REWRITE_TAC[collinear_cvectors] THEN MESON_TAC[]);;

let COLLINEAR_CVECTORS_0 = prove
  (`!x:complex^N. collinear_cvectors x cvector_zero`,
  REWRITE_TAC[collinear_cvectors] THEN GEN_TAC THEN EXISTS_TAC `Cx(&0)`
  THEN REWRITE_TAC[CVECTOR_MUL_LZERO]);;

let NON_NULL_COLLINEARS = prove
  (`!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) /\ ~(y=cvector_zero)
      ==> ?a. ~(a=Cx(&0)) /\ y = a % x`,
  REWRITE_TAC[collinear_cvectors] THEN REPEAT STRIP_TAC THENL [
    ASM_MESON_TAC[CVECTOR_MUL_LZERO];
    SUBGOAL_THEN `~(a=Cx(&0))` ASSUME_TAC THENL [
      ASM_MESON_TAC[CVECTOR_MUL_LZERO];
      EXISTS_TAC `inv a :complex`
      THEN ASM_REWRITE_TAC[COMPLEX_INV_EQ_0;CVECTOR_MUL_ASSOC]
      THEN ASM_SIMP_TAC[COMPLEX_MUL_LINV;CVECTOR_MUL_ID]]]);;

let COLLINEAR_LNONNULL = prove(
  `!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) ==> ?a. y = a % x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y=cvector_zero:complex^N` THENL [
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `Cx(&0)`
    THEN ASM_MESON_TAC[CVECTOR_MUL_LZERO];
    ASM_MESON_TAC[NON_NULL_COLLINEARS] ]);;

let COLLINEAR_RNONNULL = prove(
  `!x y:complex^N.
    collinear_cvectors x y /\ ~(y=cvector_zero) ==> ?a. x = a % y`,
  MESON_TAC[COLLINEAR_LNONNULL;COLLINEAR_CVECTORS_SYM]);;

let COLLINEAR_RUNITREAL = prove(
  `!x y:real^N.
    collinear_cvectors x (vector_to_cvector y) /\ norm y = &1
      ==> x = (x cdot (vector_to_cvector y)) % vector_to_cvector y`,
  REPEAT STRIP_TAC
  THEN POP_ASSUM (DISTRIB [ASSUME_TAC; ASSUME_TAC o REWRITE_RULE[NORM_EQ_0;
    GSYM VECTOR_TO_CVECTOR_ZERO_EQ] o MATCH_MP
      (REAL_ARITH `!x. x= &1 ==> ~(x= &0)`)])
  THEN FIRST_X_ASSUM (fun x -> FIRST_X_ASSUM (fun y ->
    CHOOSE_THEN (SINGLE ONCE_REWRITE_TAC) (MATCH_MP COLLINEAR_RNONNULL
      (CONJ y x))))
  THEN REWRITE_TAC[CDOT_LMUL;CDOT_LREAL;CVECTOR_RE_VECTOR_TO_CVECTOR;
    CVECTOR_IM_VECTOR_TO_CVECTOR;DOT_RZERO;COMPLEX_MUL_RZERO;COMPLEX_SUB_RZERO]
  THEN POP_ASSUM ((fun x ->
    REWRITE_TAC[x;COMPLEX_MUL_RID]) o REWRITE_RULE[NORM_EQ_1]));;

let CCROSS_COLLINEAR_CVECTORS = prove
  (`!x y:complex^3. x ccross y = cvector_zero <=> collinear_cvectors x y`,
  REWRITE_TAC[ccross;collinear_cvectors;CART_EQ3;VECTOR_3;
    CVECTOR_ZERO_COMPONENT;COMPLEX_SUB_0;CVECTOR_MUL_COMPONENT]
  THEN REPEAT GEN_TAC THEN EQ_TAC
  THENL [
    REPEAT (POP_ASSUM MP_TAC) THEN ASM_CASES_TAC `(x:complex^3)$1 = Cx(&0)`
    THENL [
      ASM_CASES_TAC `(x:complex^3)$2 = Cx(&0)` THENL [
        ASM_CASES_TAC `(x:complex^3)$3 = Cx(&0)` THENL [
          REPEAT DISCH_TAC THEN EXISTS_TAC `Cx(&0)`
          THEN ASM_REWRITE_TAC[COMPLEX_POLY_CLAUSES];
          REPEAT STRIP_TAC THEN EXISTS_TAC `(y:complex^3)$3/(x:complex^3)$3`
          THEN ASM_SIMP_TAC[COMPLEX_BALANCE_DIV_MUL]
          THEN ASM_MESON_TAC[COMPLEX_MUL_AC];];
        REPEAT STRIP_TAC THEN EXISTS_TAC `(y:complex^3)$2/(x:complex^3)$2`
        THEN ASM_SIMP_TAC[COMPLEX_BALANCE_DIV_MUL]
        THEN ASM_MESON_TAC[COMPLEX_MUL_AC]; ];
      REPEAT STRIP_TAC THEN EXISTS_TAC `(y:complex^3)$1/(x:complex^3)$1`
      THEN ASM_SIMP_TAC[COMPLEX_BALANCE_DIV_MUL]
      THEN ASM_MESON_TAC[COMPLEX_MUL_AC];];
      SIMPLE_COMPLEX_ARITH_TAC ]);;

let CVECTOR_MUL_INV = prove
  (`!a x y:complex^N. ~(a = Cx(&0)) /\ x = a % y ==> y = inv a % x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CVECTOR_MUL_ASSOC;
    MESON[] `(p\/q) <=> (~p ==> q)`;COMPLEX_MUL_LINV;CVECTOR_MUL_ID]);;

let CVECTOR_MUL_INV2 = prove
  (`!a x y:complex^N. ~(x = cvector_zero) /\ x = a % y ==> y = inv a % x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a=Cx(&0)`
  THEN ASM_MESON_TAC[CVECTOR_MUL_LZERO;CVECTOR_MUL_INV]);;



let COLLINEAR_CVECTORS_VECTOR_TO_CVECTOR = prove(
  `!x y:real^N.
    collinear_cvectors (vector_to_cvector x) (vector_to_cvector y)
      <=> collinear {vec 0,x,y}`,
  REWRITE_TAC[COLLINEAR_LEMMA_ALT;collinear_cvectors]
  THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL [
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[CART_EQ]
    THEN REWRITE_TAC[CVECTOR_MUL_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;
      VECTOR_MUL_COMPONENT;COMPLEX_EQ;RE_CX;RE_MUL_CX]
    THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `Re a`
    THEN ASM_SIMP_TAC[];
    REWRITE_TAC[MESON[]`(p\/q) <=> (~p ==> q)`]
    THEN REWRITE_TAC[GSYM VECTOR_TO_CVECTOR_ZERO_EQ]
    THEN DISCH_TAC
    THEN SUBGOAL_TAC "" `vector_to_cvector (y:real^N) =
      inv a % vector_to_cvector x` [ASM_MESON_TAC[CVECTOR_MUL_INV2]]
    THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[CART_EQ]
    THEN REWRITE_TAC[CVECTOR_MUL_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;
      VECTOR_MUL_COMPONENT;COMPLEX_EQ;RE_CX;RE_MUL_CX]
    THEN REPEAT STRIP_TAC THEN EXISTS_TAC `Re(inv a)` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[VECTOR_TO_CVECTOR_ZERO;
      CVECTOR_MUL_LZERO];
    ASM_REWRITE_TAC[VECTOR_TO_CVECTOR_MUL] THEN EXISTS_TAC `Cx c`
    THEN REWRITE_TAC[];
  ]);;


(* ========================================================================= *)
(* ORTHOGONALITY                                                             *)
(* ========================================================================= *)

let corthogonal = new_definition
  `corthogonal (x:complex^N) y <=> x cdot y = Cx(&0)`;;

let CORTHOGONAL_SYM = prove(
  `!x y:complex^N. corthogonal x y <=> corthogonal y x`,
  MESON_TAC[corthogonal;CDOT_SYM;CNJ_ZERO]);;

let CORTHOGONAL_0 = prove(
  `!x:complex^N. corthogonal cvector_zero x /\ corthogonal x cvector_zero`,
  REWRITE_TAC[corthogonal;CDOT_LZERO;CDOT_RZERO]);;

let [CORTHOGONAL_LZERO;CORTHOGONAL_RZERO] = GCONJUNCTS CORTHOGONAL_0;;

let CORTHOGONAL_COLLINEAR_CVECTORS = prove
  (`!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) /\ ~(y=cvector_zero)
      ==> ~(corthogonal x y)`,
  REWRITE_TAC[collinear_cvectors;corthogonal] THEN REPEAT STRIP_TAC
  THEN POP_ASSUM MP_TAC
  THEN ASM_REWRITE_TAC[CDOT_RMUL;CDOT_LMUL;COMPLEX_ENTIRE;GSYM cnorm2;
    CDOT_EQ_0;CNJ_EQ_0]
  THEN ASM_MESON_TAC[CVECTOR_MUL_LZERO]);;

let CORTHOGONAL_MUL_CLAUSES = prove
  (`!x y a.
    (corthogonal x y ==> corthogonal x (a%y))
    /\ (corthogonal x y \/ a = Cx(&0) <=> corthogonal x (a%y))
    /\ (corthogonal x y ==> corthogonal (a%x) y)
    /\ (corthogonal x y \/ a = Cx(&0) <=> corthogonal (a%x) y)`,
  SIMP_TAC[corthogonal;CDOT_RMUL;CDOT_LMUL;COMPLEX_ENTIRE;CNJ_EQ_0]
  THEN MESON_TAC[]);;

let [CORTHOGONAL_RMUL;CORTHOGONAL_RMUL_EQ;CORTHOGONAL_LMUL;
  CORTHOGONAL_LMUL_EQ] = GCONJUNCTS CORTHOGONAL_MUL_CLAUSES;;

let CORTHOGONAL_LRMUL_CLAUSES = prove
  (`!x y a b.
    (corthogonal x y ==> corthogonal (a%x) (b%y))
    /\ (corthogonal x y \/ a = Cx(&0) \/ b = Cx(&0)
      <=> corthogonal (a%x) (b%y))`,
  MESON_TAC[CORTHOGONAL_MUL_CLAUSES]);;

let [CORTHOGONAL_LRMUL;CORTHOGONAL_LRMUL_EQ] =
  GCONJUNCTS CORTHOGONAL_LRMUL_CLAUSES;;

let CORTHOGONAL_REAL_CLAUSES = prove
  (`!r c.
    (corthogonal c (vector_to_cvector r)
      <=> orthogonal (cvector_re c) r /\ orthogonal (cvector_im c) r)
    /\ (corthogonal (vector_to_cvector r) c
      <=> orthogonal r (cvector_re c) /\ orthogonal r (cvector_im c))`,
  REWRITE_TAC[corthogonal;orthogonal;CDOT_LREAL;CDOT_RREAL;COMPLEX_SUB_0;
    COMPLEX_EQ;RE_CX;IM_CX;RE_SUB;IM_SUB;RE_ADD;IM_ADD]
  THEN REWRITE_TAC[RE_DEF;CX_DEF;IM_DEF;complex;complex_mul;VECTOR_2;ii]
  THEN CONV_TAC REAL_FIELD);;

let [CORTHOGONAL_RREAL;CORTHOGONAL_LREAL] =
  GCONJUNCTS CORTHOGONAL_REAL_CLAUSES;;

let CORTHOGONAL_UNIT = prove
  (`!x y:complex^N.
    (corthogonal x (cunit y) <=> corthogonal x y)
    /\ (corthogonal (cunit x) y <=> corthogonal x y)`,
  REWRITE_TAC[cunit;GSYM CORTHOGONAL_MUL_CLAUSES;COMPLEX_INV_EQ_0;CX_INJ;
    CNORM_EQ_0]
  THEN MESON_TAC[CORTHOGONAL_0]);;

let [CORTHOGONAL_RUNIT;CORTHOGONAL_LUNIT] = GCONJUNCTS CORTHOGONAL_UNIT;;

let CORTHOGONAL_PROJECTION = prove(
  `!x y:complex^N. corthogonal (x - (x cdot cunit y) % cunit y) y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `y=cvector_zero:complex^N`
  THEN ASM_REWRITE_TAC[corthogonal;CDOT_RZERO]
  THEN REWRITE_TAC[CDOT_LSUB;cunit;CVECTOR_MUL_ASSOC;GSYM cnorm2;CDOT_LMUL;
    CDOT_RMUL;REWRITE_RULE[REAL_CNJ] (MATCH_MP REAL_INV (SPEC_ALL REAL_CX))]
  THEN REWRITE_TAC[COMPLEX_MUL_AC;GSYM COMPLEX_INV_MUL;GSYM COMPLEX_POW_2;
    cnorm;o_DEF;CSQRT]
  THEN SIMP_TAC[CNORM2_POS;CX_SQRT;cnorm2;REAL_CDOT_SELF;REAL_OF_COMPLEX;CSQRT]
  THEN ASM_SIMP_TAC[CDOT_EQ_0;COMPLEX_MUL_RINV;COMPLEX_MUL_RID;
    COMPLEX_SUB_REFL]);;

let CDOT_PYTHAGOREAN = prove
  (`!x y:complex^N. corthogonal x y ==> cnorm2 (x+y) = cnorm2 x + cnorm2 y`,
  SIMP_TAC[corthogonal;cnorm2;CDOT_LADD;CDOT_RADD;COMPLEX_ADD_RID;
    COMPLEX_ADD_LID;REAL_OF_COMPLEX_ADD;REAL_CDOT_SELF;
    MESON[CDOT_SYM;CNJ_ZERO] `x cdot y = Cx (&0) ==> y cdot x = Cx(&0)`]);;

let CDOT_CAUCHY_SCHWARZ_POW_2 = prove
  (`!x y:complex^N. norm (x cdot y) pow 2 <= cnorm2 x * cnorm2 y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `y = cvector_zero:complex^N`
  THEN ASM_REWRITE_TAC[CNORM2_CVECTOR_ZERO;CDOT_RZERO;COMPLEX_NORM_0;
    REAL_POW_2;REAL_MUL_RZERO;REAL_OF_COMPLEX_CX;REAL_LE_REFL]
  THEN ONCE_REWRITE_TAC[MATCH_MP (MESON[CVECTOR_SUB_ADD]
    `(!x:complex^N y. p (x - f x y) y)
      ==> cnorm2 x * z = cnorm2 (x - f x y + f x y) * z`) CORTHOGONAL_PROJECTION]
  THEN MATCH_MP_TAC (GEN_ALL (MATCH_MP (MESON[] `(!x y. P x y ==> f x y = (g x y:real))
    ==> P x y /\ a <= g x y * b ==> a <= f x y * b`) CDOT_PYTHAGOREAN))
  THEN REWRITE_TAC[GSYM CORTHOGONAL_MUL_CLAUSES;CORTHOGONAL_RUNIT;
    CORTHOGONAL_PROJECTION]
  THEN SIMP_TAC[cnorm2;GSYM REAL_OF_COMPLEX_ADD;REAL_CDOT_SELF;REAL_ADD;
    GSYM REAL_OF_COMPLEX_MUL]
  THEN REWRITE_TACS[cunit;CDOT_RMUL;CVECTOR_MUL_ASSOC;REWRITE_RULE[REAL_CNJ]
    (MATCH_MP REAL_INV (SPEC_ALL REAL_CX));COMPLEX_MUL_AC;GSYM COMPLEX_INV_MUL;
    GSYM COMPLEX_POW_2;cnorm;o_DEF;CSQRT;COMPLEX_ADD_LDISTRIB;cnorm2;CDOT_RMUL;
    CNJ_MUL;CDOT_LMUL;GSYM cnorm2;
    REWRITE_RULE[REAL_CNJ] (MATCH_MP REAL_INV (SPEC_ALL REAL_CX))]
  THEN SIMP_TAC[CX_SQRT;CNORM2_POS;CSQRT;CX_CNORM2]
  THEN REWRITE_TAC[SIMPLE_COMPLEX_ARITH
    `x * ((y * inv x) * x) * (z * inv x') * inv x'
    = (y * z) * (x * inv x) * (x * inv x' * inv x'):complex`]
  THEN ASM_SIMP_TAC[CDOT_EQ_0;COMPLEX_MUL_RINV;COMPLEX_MUL_LID;COMPLEX_MUL_CNJ;
    GSYM COMPLEX_INV_MUL]
  THEN ONCE_REWRITE_TAC[
    GSYM (MATCH_MP REAL_OF_COMPLEX (SPEC_ALL REAL_CDOT_SELF))]
  THEN SIMP_TAC[GSYM cnorm2;GSYM CX_SQRT;CNORM2_POS;GSYM CX_MUL;
    GSYM COMPLEX_POW_2;GSYM CX_POW;SQRT_POW_2;GSYM CX_INV]
  THEN ASM_SIMP_TAC[REAL_MUL_RINV;CNORM2_EQ_0;REAL_MUL_RID;GSYM CX_ADD;
    REAL_OF_COMPLEX_CX;GSYM REAL_POW_2;REAL_LE_ADDL;REAL_LE_MUL;CNORM2_POS]);;

let CDOT_CAUCHY_SCHWARZ = prove
  (`!x y:complex^N. norm (x cdot y) <= norm x * norm y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC (REWRITE_RULE[REAL_LE_SQUARE_ABS]
    (REAL_ARITH `&0 <= x /\ &0 <= y /\ abs x <= abs y ==> x <= y`))
  THEN SIMP_TAC[NORM_POS_LE;CNORM_POS;REAL_LE_MUL;REAL_POW_MUL;CNORM_POW_2;
    CDOT_CAUCHY_SCHWARZ_POW_2]);;

let CDOT_CAUCHY_SCHWARZ_POW_2_EQUAL = prove
  (`!x y:complex^N.
    norm (x cdot y) pow 2 = cnorm2 x * cnorm2 y <=> collinear_cvectors x y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `y = cvector_zero:complex^N`
  THEN ASM_REWRITE_TAC[CNORM2_CVECTOR_ZERO;CDOT_RZERO;COMPLEX_NORM_0;
    REAL_POW_2;REAL_MUL_RZERO;REAL_OF_COMPLEX_CX;COLLINEAR_CVECTORS_0]
  THEN EQ_TAC THENL [
    ONCE_REWRITE_TAC[MATCH_MP (MESON[CVECTOR_SUB_ADD]
      `(!x:complex^N y. p (x - f x y) y) ==>
      cnorm2 x * z = cnorm2 (x - f x y + f x y) * z`) CORTHOGONAL_PROJECTION]
    THEN MATCH_MP_TAC (GEN_ALL (MATCH_MP (MESON[]
      `(!x y. P x y ==> g x y = (f x y:real)) ==>
        P x y /\ (a = f x y * z ==> R) ==> (a = g x y * z ==> R)`)
      CDOT_PYTHAGOREAN))
    THEN REWRITE_TAC[GSYM CORTHOGONAL_MUL_CLAUSES;CORTHOGONAL_RUNIT;
      CORTHOGONAL_PROJECTION]
    THEN SIMP_TAC[cnorm2;GSYM REAL_OF_COMPLEX_ADD;REAL_CDOT_SELF;REAL_ADD;
      GSYM REAL_OF_COMPLEX_MUL]
    THEN REWRITE_TACS[cunit;CDOT_RMUL;CVECTOR_MUL_ASSOC;REWRITE_RULE[REAL_CNJ]
      (MATCH_MP REAL_INV (SPEC_ALL REAL_CX));COMPLEX_MUL_AC;
      GSYM COMPLEX_INV_MUL;GSYM COMPLEX_POW_2;cnorm;o_DEF;CSQRT;
      COMPLEX_ADD_LDISTRIB;cnorm2;CDOT_RMUL;CNJ_MUL;CDOT_LMUL;GSYM cnorm2;
      REWRITE_RULE[REAL_CNJ] (MATCH_MP REAL_INV (SPEC_ALL REAL_CX))]
    THEN SIMP_TAC[CX_SQRT;CNORM2_POS;CSQRT;CX_CNORM2]
    THEN REWRITE_TAC[SIMPLE_COMPLEX_ARITH
      `x * ((y * inv x) * x) * (z * inv x') * inv x' =
        (y * z) * (x * inv x) * (x * inv x' * inv x'):complex`]
    THEN ONCE_REWRITE_TAC[GSYM (MATCH_MP REAL_OF_COMPLEX
      (SPEC_ALL REAL_CDOT_SELF))]
    THEN SIMP_TAC[GSYM cnorm2;GSYM CX_SQRT;CNORM2_POS;GSYM CX_MUL;
      GSYM COMPLEX_POW_2;GSYM CX_POW;SQRT_POW_2;GSYM CX_INV;REAL_POW_INV]
    THEN ASM_SIMP_TAC[REAL_MUL_RINV;CNORM2_EQ_0;REAL_MUL_RID;GSYM CX_ADD;
      REAL_OF_COMPLEX_CX;GSYM REAL_POW_2;REAL_LE_ADDL;REAL_LE_MUL;CNORM2_POS;
      GSYM CX_POW;REAL_POW_ONE;COMPLEX_MUL_RID;COMPLEX_MUL_CNJ;
      REAL_ARITH `x = y + x <=> y = &0`;REAL_ENTIRE;CNORM2_EQ_0;
      CVECTOR_SUB_EQ;collinear_cvectors]
    THEN MESON_TAC[];
    REWRITE_TAC[collinear_cvectors] THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[cnorm2;CDOT_LMUL;CDOT_RMUL;COMPLEX_NORM_MUL;
      COMPLEX_MUL_ASSOC]
    THEN SIMP_TAC[COMPLEX_MUL_CNJ;GSYM cnorm2;COMPLEX_NORM_CNJ;GSYM CX_POW;
      REAL_OF_COMPLEX_MUL;REAL_CX;REAL_CDOT_SELF;REAL_OF_COMPLEX_CX;
      GSYM CNORM2_ALT]
    THEN SIMPLE_COMPLEX_ARITH_TAC
  ]);;

let CDOT_CAUCHY_SCHWARZ_EQUAL = prove
  (`!x y:complex^N.
  norm (x cdot y) = norm x * norm y <=> collinear_cvectors x y`,
  ONCE_REWRITE_TAC[REWRITE_RULE[REAL_EQ_SQUARE_ABS] (REAL_ARITH
    `x=y <=> abs x = abs y /\ (&0 <= x /\ &0 <= y \/ x < &0 /\ y < &0)`)]
  THEN SIMP_TAC[NORM_POS_LE;CNORM_POS;REAL_LE_MUL;REAL_POW_MUL;CNORM_POW_2;
    CDOT_CAUCHY_SCHWARZ_POW_2_EQUAL]);;

let CNORM_TRIANGLE = prove
  (`!x y:complex^N. norm (x+y) <= norm x + norm y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC (REWRITE_RULE[REAL_LE_SQUARE_ABS]
    (REAL_ARITH `abs x <= abs y /\ &0 <= x /\ &0 <= y ==> x <= y`))
  THEN SIMP_TAC[CNORM_POS;REAL_LE_ADD;REAL_ADD_POW_2;CNORM_POW_2;cnorm2;
    CDOT_LADD;CDOT_RADD;SIMPLE_COMPLEX_ARITH `(x+y)+z+t = x+(y+z)+t:complex`;
    ADD_CDOT_SYM;REAL_OF_COMPLEX_ADD;REAL_CDOT_SELF;REAL_CX;REAL_ADD;
    REAL_OF_COMPLEX_CX;REAL_ARITH `x+ &2*y+z<=x+z+ &2*t <=> y<=t:real`]
  THEN MESON_TAC[CDOT_CAUCHY_SCHWARZ;RE_NORM;REAL_LE_TRANS]);;

let REAL_ABS_SUB_CNORM = prove
  (`!x y:complex^N. abs (norm x - norm y) <= norm (x-y)`,
  let lemma =
    REWRITE_RULE[CVECTOR_SUB_ADD2;REAL_ARITH `x<=y+z <=> x-y<=z:real`]
      (SPECL [`x:complex^N`;`y-x:complex^N`] CNORM_TRIANGLE)
  in
  REPEAT GEN_TAC
  THEN MATCH_MP_TAC (MATCH_MP (MESON[]
    `(!x y. P x y <=> Q x y) ==> Q x y ==> P x y`) REAL_ABS_BOUNDS)
  THEN ONCE_REWRITE_TAC[REAL_ARITH `--x <= y <=>  --y <= x`]
  THEN REWRITE_TAC[REAL_NEG_SUB]
  THEN REWRITE_TAC[lemma;ONCE_REWRITE_RULE[CNORM_SUB] lemma]);;

(* ========================================================================= *)
(* VSUM                                                                      *)
(* ========================================================================= *)

let cvsum = new_definition
  `(cvsum:(A->bool)->(A->complex^N)->complex^N) s f = lambda i. vsum s (\x. (f x)$i)`;;


(* ========================================================================= *)
(* INFINITE SUM                                                              *)
(* ========================================================================= *)

let csummable = new_definition
  `csummable (s:num->bool) (f:num->complex^N)
    <=> summable s (cvector_re o f) /\ summable s (cvector_im o f)`;;

let cinfsum = new_definition
  `cinfsum (s:num->bool) (f:num->complex^N) :complex^N
    = vector_to_cvector (infsum s (\x. cvector_re (f x)))
      + ii % vector_to_cvector (infsum s (\x.cvector_im (f x)))`;;

let CSUMMABLE_FLATTEN_CVECTOR = prove
  (`!s (f:num->complex^N). csummable s f <=> summable s (cvector_flatten o f)`,
  REWRITE_TAC[csummable;summable;cvector_flatten;o_DEF]
  THEN REPEAT (STRIP_TAC ORELSE EQ_TAC)
  THENL [
    EXISTS_TAC `pastecart (l:real^N) (l':real^N)`
    THEN ASM_SIMP_TAC[GSYM SUMS_PASTECART];
    EXISTS_TAC `fstcart (l:real^(N,N) finite_sum)`
    THEN MATCH_MP_TAC (GEN_ALL (MATCH_MP (TAUT `(p /\ q <=> r) ==> (r ==> p)`)
      (INST_TYPE [`:N`,`:M`] (SPEC_ALL SUMS_PASTECART))))
    THEN EXISTS_TAC `(cvector_im o f) :num->real^N`
    THEN EXISTS_TAC `sndcart (l:real^(N,N) finite_sum)`
    THEN ASM_REWRITE_TAC[ETA_AX;o_DEF;PASTECART_FST_SND];
    EXISTS_TAC `sndcart (l:real^(N,N) finite_sum)`
    THEN MATCH_MP_TAC (GEN_ALL (MATCH_MP (TAUT `(p /\ q <=> r) ==> (r ==> q)`)
      (INST_TYPE [`:N`,`:M`] (SPEC_ALL SUMS_PASTECART))))
    THEN EXISTS_TAC `(cvector_re o f) :num->real^N`
    THEN EXISTS_TAC `fstcart (l:real^(N,N) finite_sum)`
    THEN ASM_REWRITE_TAC[ETA_AX;o_DEF;PASTECART_FST_SND];
  ]);;

let FLATTEN_CINFSUM = prove
  (`!s f.
    csummable s f ==>
      ((cinfsum s f):complex^N) =
        cvector_unflatten (infsum s (cvector_flatten o f))`,
  SIMP_TAC[cinfsum;cvector_unflatten;COMPLEX_VECTOR_TRANSPOSE;LINEAR_FSTCART;
    LINEAR_SNDCART;CSUMMABLE_FLATTEN_CVECTOR;GSYM INFSUM_LINEAR;o_DEF;
    cvector_flatten;FSTCART_PASTECART;SNDCART_PASTECART]);;

let CSUMMABLE_LINEAR = prove
  (`!f h:complex^N->complex^M s.
    csummable s f /\ clinear h ==> csummable s (h o f)`,
  REWRITE_TAC[CSUMMABLE_FLATTEN_CVECTOR] THEN REPEAT STRIP_TAC
  THEN POP_ASSUM (ASSUME_TAC o MATCH_MP FLATTEN_CLINEAR)
  THEN SUBGOAL_THEN
    `cvector_flatten o (h:complex^N -> complex^M) o (f:num -> complex^N) =
    \n. (cvector_flatten o h o cvector_unflatten) (cvector_flatten (f n))`
    (SINGLE REWRITE_TAC)
  THENL [
    REWRITE_TAC[o_DEF;FUN_EQ_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC
    THEN REWRITE_TAC[REWRITE_RULE[o_DEF;I_DEF;FUN_EQ_THM] UNFLATTEN_FLATTEN];
    MATCH_MP_TAC SUMMABLE_LINEAR THEN ASM_SIMP_TAC[GSYM o_DEF]
  ]);;

let CINFSUM_LINEAR = prove
  (`!f (h:complex^M->complex^N) s.
    csummable s f /\ clinear h ==> cinfsum s (h o f) = h (cinfsum s f)`,
  REPEAT GEN_TAC
  THEN DISCH_THEN (fun x -> MP_TAC (CONJ (MATCH_MP CSUMMABLE_LINEAR x) x))
  THEN SIMP_TAC[FLATTEN_CINFSUM;CSUMMABLE_FLATTEN_CVECTOR]
  THEN REPEAT STRIP_TAC THEN POP_ASSUM (ASSUME_TAC o MATCH_MP FLATTEN_CLINEAR)
  THEN SUBGOAL_THEN
    `cvector_flatten o (h:complex^M->complex^N) o (f:num->complex^M) =
    \n. (cvector_flatten o h o cvector_unflatten) ((cvector_flatten o f) n)`
    (SINGLE REWRITE_TAC)
  THENL [
    REWRITE_TAC[o_DEF;FUN_EQ_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC
    THEN REWRITE_TAC[REWRITE_RULE[o_DEF;I_DEF;FUN_EQ_THM] UNFLATTEN_FLATTEN];
    FIRST_ASSUM (fun x -> FIRST_ASSUM (fun y -> REWRITE_TAC[MATCH_MP
      (MATCH_MP (REWRITE_RULE[IMP_CONJ] INFSUM_LINEAR) x) y]))
    THEN REWRITE_TAC[o_DEF;REWRITE_RULE[o_DEF;I_DEF;FUN_EQ_THM]
      UNFLATTEN_FLATTEN]
  ]);;
