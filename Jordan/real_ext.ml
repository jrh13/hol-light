



(* ------------------------------------------------------------------ *)
(*   Theorems that construct and propagate equality and inequality    *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Propagation of =EQUAL=  *)
(* ------------------------------------------------------------------ *)

unambiguous_interface();;
prioritize_num();;

let REAL_MUL_LTIMES = prove (`!x a b. (x*.a = x*.b) ==> (~(x=(&.0))) ==> (a =b)`,
   MESON_TAC[REAL_EQ_MUL_LCANCEL]);;

let REAL_MUL_RTIMES = prove (`!x a b. (a*.x = b*.x) ==> (~(x=(&.0))) ==> (a =b)`,
   MESON_TAC[REAL_EQ_MUL_RCANCEL]);;

let REAL_PROP_EQ_LMUL = REAL_MUL_LTIMES;;
let REAL_PROP_EQ_RMUL = REAL_MUL_RTIMES;;

let REAL_PROP_EQ_LMUL_' = REAL_EQ_MUL_LCANCEL (* |- !x y z. (x * y = x * z) = (x = &0) \/ (y = z) *);;
let REAL_PROP_EQ_RMUL_' = REAL_EQ_MUL_LCANCEL (* |- !x y z. (x * z = y * z) = (x = y) \/ (z = &0) *);;
(* see also minor variations REAL_LT_LMUL_EQ, REAL_LT_RMUL_EQ *)

let REAL_PROP_EQ_SQRT = SQRT_INJ;; (* |- !x y. &0 <= x /\ &0 <= y ==> ((sqrt x = sqrt y) = x = y) *)

(* ------------------------------------------------------------------ *)
(* Construction of <=. *)
(* ------------------------------------------------------------------ *)
let REAL_MK_LE_SQUARE = REAL_LE_SQUARE_POW ;; (*  |- !x. &0 <= x pow 2 *)

(* ------------------------------------------------------------------ *)
(* Propagation of <=. *)
(* ------------------------------------------------------------------ *)

let REAL_MUL_LTIMES_LE = prove (`!x a b. (x*.a <=. x*.b) ==> (&.0 < x) ==> (a <=. b)`,
   MESON_TAC[REAL_LE_LMUL_EQ]);;
  (* virtually identical to REAL_LE_LCANCEL_IMP, REAL_LE_LMUL_EQ *)

let REAL_MUL_RTIMES_LE = prove (`!x a b. (a*.x <=. b*.x) ==> (&.0 < x) ==> (a <=. b)`,
   MESON_TAC[REAL_LE_RMUL_EQ]);;
  (* virtually identical to REAL_LE_RCANCEL_IMP, REAL_LE_RMUL_EQ *)

let REAL_PROP_LE_LCANCEL = REAL_MUL_LTIMES_LE;;
let REAL_PROP_LE_RCANCEL = REAL_MUL_RTIMES_LE;;
let REAL_PROP_LE_LMUL = REAL_LE_LMUL (* |- !x y z. &0 <= x /\ y <= z ==> x * y <= x * z *);;
let REAL_PROP_LE_RMUL = REAL_LE_RMUL (* |- !x y z. x <= y /\ &0 <= z ==> x * z <= y * z *);;
let REAL_PROP_LE_LRMUL = REAL_LE_MUL2;; (* |- !w x y z. &0 <= w /\ w <= x /\ &0 <= y /\ y <= z ==> w * y <= x * z *)
let REAL_PROP_LE_POW = POW_LE;; (* |- !n x y. &0 <= x /\ x <= y ==> x pow n <= y pow n *)
let REAL_PROP_LE_SQRT = SQRT_MONO_LE_EQ;; (* |- !x y. &0 <= x /\ &0 <= y ==> (sqrt x <= sqrt y = x <= y) *)

(* ------------------------------------------------------------------ *)
(* Construction of LT *)
(* ------------------------------------------------------------------ *)

let REAL_MK_LT_SQUARE  = REAL_LT_SQUARE;; (* |- !x. &0 < x * x = ~(x = &0) *)

(* ------------------------------------------------------------------ *)
(* Propagation of LT *)
(* ------------------------------------------------------------------ *)

let REAL_PROP_LT_LCANCEL = REAL_LT_LCANCEL_IMP (* |- !x y z. &0 < x /\ x * y < x * z ==> y < z *);;
let REAL_PROP_LT_RCANCEL = REAL_LT_RCANCEL_IMP (* |- !x y z. &0 < z /\ x * z < y * z ==> x < y *);;
let REAL_PROP_LT_LMUL = REAL_LT_LMUL (* |- !x y z. &0 < x /\ y < z ==> x * y < x * z *);;
let REAL_PROP_LT_RMUL = REAL_LT_RMUL (* |- !x y z. x < y /\ &0 < z ==> x * z < y * z *);;
(* minor variation REAL_LT_LMUL_IMP, REAL_LT_RMUL_IMP *)

let REAL_PROP_LT_LRMUL= REAL_LT_MUL2;; (* |- !w x y z. &0 <= w /\ w < x /\ &0 <= y /\ y < z ==> w * y < x * z *)
let REAL_PROP_LT_SQRT = SQRT_MONO_LT_EQ;; (* |- !x y. &0 <= x /\ &0 <= y ==> (sqrt x < sqrt y = x < y) *)

(* ------------------------------------------------------------------ *)
(* Constructors of Non-negative *)
(* ------------------------------------------------------------------ *)

let REAL_MK_NN_SQUARE = REAL_LE_SQUARE;; (* |- !x. &0 <= x * x *)
let REAL_MK_NN_ABS = ABS_POS;; (* |- !x. &0 <= abs x *)

(* ------------------------------------------------------------------ *)
(* Propagation of Non-negative *)
(* ------------------------------------------------------------------ *)

let REAL_PROP_NN_POS = prove(`! x y. x<. y ==> x <= y`,MESON_TAC[REAL_LT_LE]);;
let REAL_PROP_NN_ADD2 = REAL_LE_ADD (* |- !x y. &0 <= x /\ &0 <= y ==> &0 <= x + y *);;
let REAL_PROP_NN_DOUBLE = REAL_LE_DOUBLE (* |- !x. &0 <= x + x <=> &0 <= x *);;
let REAL_PROP_NN_RCANCEL= prove(`!x y. &.0 <. x /\ (&.0) <=. y*.x ==> ((&.0) <=. y)`,
  MESON_TAC[REAL_PROP_LE_RCANCEL;REAL_MUL_LZERO]);;
let REAL_PROP_NN_LCANCEL= prove(`!x y. &.0 <. x /\ (&.0) <=. x*.y ==> ((&.0) <=. y)`,
  MESON_TAC[REAL_PROP_LE_LCANCEL;REAL_MUL_RZERO]);;
let REAL_PROP_NN_MUL2 = REAL_LE_MUL (* |- !x y. &0 <= x /\ &0 <= y ==> &0 <= x * y *);;
let REAL_PROP_NN_POW = REAL_POW_LE (* |- !x n. &0 <= x ==> &0 <= x pow n *);;
let REAL_PROP_NN_SQUARE = REAL_LE_POW_2;; (* |- !x. &0 <= x pow 2 *)
let REAL_PROP_NN_SQRT = SQRT_POS_LE;; (* |- !x. &0 <= x ==> &0 <= sqrt x *)
let REAL_PROP_NN_INV = REAL_LE_INV_EQ (* |- !x. &0 <= inv x = &0 <= x *);;
let REAL_PROP_NN_SIN = SIN_POS_PI_LE;; (* |- !x. &0 <= x /\ x <= pi ==> &0 <= sin x *)
let REAL_PROP_NN_ATN = ATN_POS_LE;; (* |- &0 <= atn x = &0 <= x *)


(* ------------------------------------------------------------------ *)
(* Constructor of POS *)
(* ------------------------------------------------------------------ *)

let REAL_MK_POS_ABS = REAL_ABS_NZ (* |- !x. ~(x = &0) = &0 < abs x *);;
let REAL_MK_POS_EXP = REAL_EXP_POS_LT;; (* |- !x. &0 < exp x *)
let REAL_MK_POS_LN = LN_POS_LT;; (* |- !x. &1 < x ==> &0 < ln x *)
let REAL_MK_POS_PI = PI_POS;; (* |- &0 < pi *)


(* ------------------------------------------------------------------ *)
(* Propagation of POS *)
(* ------------------------------------------------------------------ *)

let REAL_PROP_POS_ADD2 = REAL_LT_ADD (* |- !x y. &0 < x /\ &0 < y ==> &0 < x + y *);;
let REAL_PROP_POS_LADD = REAL_LET_ADD (* |- !x y. &0 <= x /\ &0 < y ==> &0 < x + y *);;
let REAL_PROP_POS_RADD = REAL_LTE_ADD (* |- !x y. &0 < x /\ &0 <= y ==> &0 < x + y *);;
let REAL_PROP_POS_LMUL = REAL_LT_LMUL_0;; (* |- !x y. &0 < x ==> (&0 < x * y = &0 < y) *)
let REAL_PROP_POS_RMUL = REAL_LT_RMUL_0;; (* |- !x y. &0 < y ==> (&0 < x * y = &0 < x) *)
let REAL_PROP_POS_MUL2 = REAL_LT_MUL (* |- !x y. &0 < x /\ &0 < y ==> &0 < x * y *);;
let REAL_PROP_POS_SQRT = SQRT_POS_LT;; (* |- !x. &0 < x ==> &0 < sqrt x *)
let REAL_PROP_POS_POW =  REAL_POW_LT (*  |- !x n. &0 < x ==> &0 < x pow n *);;
let REAL_PROP_POS_INV = REAL_LT_INV (* |- !x. &0 < x ==> &0 < inv x *);;
let REAL_PROP_POS_SIN = SIN_POS_PI;; (*  |- !x. &0 < x /\ x < pi ==> &0 < sin x *)
let REAL_PROP_POS_TAN = TAN_POS_PI2;; (* |- !x. &0 < x /\ x < pi / &2 ==> &0 < tan x *)
let REAL_PROP_POS_ATN = ATN_POS_LT;; (* |- &0 < atn x = &0 < x *)

(* ------------------------------------------------------------------ *)
(* Construction of NZ *)
(* ------------------------------------------------------------------ *)

(* renamed from REAL_MK_NZ_OF_POS *)
let REAL_MK_NZ_POS = REAL_LT_IMP_NZ (* |- !x. &0 < x ==> ~(x = &0) *);;
let REAL_MK_NZ_EXP = REAL_EXP_NZ;; (*  |- !x. ~(exp x = &0) *)

(* ------------------------------------------------------------------ *)
(* Propagation of NZ *)
(* ------------------------------------------------------------------ *)

(* renamed from REAL_ABS_NZ, moved from float.ml *)
let REAL_PROP_NZ_ABS =  prove(`!x. (~(x = (&.0))) ==> (~(abs(x) = (&.0)))`,
    REWRITE_TAC[ABS_ZERO]);;
let REAL_PROP_NZ_POW = REAL_POW_NZ (*  |- !x n. ~(x = &0) ==> ~(x pow n = &0) *);;
let REAL_PROP_NZ_INV = REAL_INV_NZ;; (* |- !x. ~(x = &0) ==> ~(inv x = &0) *)


(* ------------------------------------------------------------------ *)
(* Propagation of ZERO *)
(* ------------------------------------------------------------------ *)

let REAL_PROP_ZERO_ABS = REAL_ABS_ZERO (* |- !x. (abs x = &0) = x = &0); *);;
let REAL_PROP_ZERO_NEG = REAL_NEG_EQ_0 ;; (*  |- !x. (--x = &0) = x = &0 *)
let REAL_PROP_ZERO_INV = REAL_INV_EQ_0 (* |- !x. (inv x = &0) = x = &0 *);;
let REAL_PROP_ZERO_NEG = REAL_NEG_EQ0;; (* |- !x. (--x = &0) = x = &0 *)
let REAL_PROP_ZERO_SUMSQ = REAL_SUMSQ;; (* |- !x y. (x * x + y * y = &0) = (x = &0) /\ (y = &0) *)
let REAL_PROP_ZERO_POW = REAL_POW_EQ_0;; (* |- !x n. (x pow n = &0) = (x = &0) /\ ~(n = 0) *)
let REAL_PROP_ZERO_SQRT = SQRT_EQ_0;; (* |- !x. &0 <= x ==> (x / sqrt x = sqrt x) *)

(* ------------------------------------------------------------------ *)
(* Special values of functions *)
(* ------------------------------------------------------------------ *)

let REAL_SV_LADD_0 = REAL_ADD_LID (* |- !x. &0 + x = x); *);;
let REAL_SV_INV_0 = REAL_INV_0 (*  |- inv (&0) = &0 *);;
let REAL_SV_RMUL_0 = REAL_MUL_RZERO (* |- !x. x * &0 = &0 *);;
let REAL_SV_LMUL_0 = REAL_MUL_LZERO (* |- !x. &0 * x = &0 *);;
let REAL_SV_NEG_0 = REAL_NEG_0 (*  |- -- &0 = &0 *);;
let REAL_SV_ABS_0 = REAL_ABS_0 (* |- abs (&0) = &0 *);;
let REAL_SV_EXP_0 = REAL_EXP_0;; (* |- exp (&0) = &1 *)
let REAL_SV_LN_1 = LN_1;; (* |- ln (&1) = &0 *)
let REAL_SV_SQRT_0 = SQRT_0;; (* |- sqrt (&0) = &0 *)
let REAL_SV_TAN_0 = TAN_0;; (*  |- tan (&0) = &0 *)
let REAL_SV_TAN_PI = TAN_PI;; (* |- tan pi = &0 *)

(* ------------------------------------------------------------------ *)
(* A tactic that multiplies a real on the left *)
(* ------------------------------------------------------------------ *)

(**
#g `a:real = b:real`;;
#e (REAL_LMUL_TAC `c:real`);;
it : goalstack = 2 subgoals (2 total)
`~(c = &0)`

`c * a = c * b`

 0 [`~(c = &0)`]
#
**)
(* ------------------------------------------------------------------ *)



let REAL_LMUL_TAC t =
  let REAL_MUL_LTIMES =
        prove ((`!x a b.
        (((~(x=(&0)) ==> (x*a = x*b)) /\ ~(x=(&0))) ==>  (a = b))`),
                MESON_TAC[REAL_EQ_MUL_LCANCEL]) in
   (MATCH_MP_TAC (SPEC t REAL_MUL_LTIMES))
   THEN CONJ_TAC
   THENL [DISCH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------ *)
(* Right multiply by a real *)
(* ------------------------------------------------------------------ *)

let REAL_RMUL_TAC t =
  let REAL_MUL_RTIMES =
        prove (`!x a b.
                ((~(x=(&0))==>(a*x = b*x)) /\ ~(x=(&0))) ==>  (a = b)`,
                MESON_TAC[REAL_EQ_MUL_RCANCEL]) in
   (MATCH_MP_TAC (SPEC t REAL_MUL_RTIMES))
   THEN CONJ_TAC
   THENL [DISCH_TAC; ALL_TAC];;


pop_priority();;
