(* ---------------------------------------------------------------------- *)
(*  Num                                                                   *)
(* ---------------------------------------------------------------------- *)

let NUM_REWRITES = ref [
LT_TRANS;
LET_TRANS;
LTE_TRANS;
LE_TRANS;
GT;
GE;
PRE;
ARITH_RULE `x + 0 = x`;
ARITH_RULE `0 + x = x`;
ARITH_RULE `1 * x = x`;
ARITH_RULE `x * 1 = x`;
];;

let NUM_SIMP_TAC = REWRITE_TAC !NUM_REWRITES;; 

let extend_num_rewrites l = 
  NUM_REWRITES := !NUM_REWRITES @ l;;

(* ---------------------------------------------------------------------- *)
(*  Real                                                                  *)
(* ---------------------------------------------------------------------- *)

(*
search [`(pow)`;rp] 
*)

let REAL_REWRITES = ref [
REAL_MUL_LID;
REAL_MUL_RID;
REAL_MUL_RZERO;
REAL_MUL_LZERO;
REAL_LT_TRANS;
REAL_LET_TRANS;
REAL_LTE_TRANS;
REAL_LE_TRANS;
REAL_LE_MUL;
REAL_NOT_LT;
REAL_LT_REFL;
REAL_LE_REFL;
REAL_ADD_RID;
REAL_ADD_LID;
REAL_ADD_LDISTRIB;
REAL_ADD_RDISTRIB;
REAL_NEG_0;
REAL_NEG_MUL2;
REAL_OF_NUM_LT;
REAL_MAX_MAX;
real_pow;
REAL_ARITH `x - &0 = x`;
REAL_NOT_LT;
REAL_NOT_LE;
REAL_INV_INV;
REAL_INV_MUL;
real_gt;
real_ge;
REAL_POW_1;
ARITH_RULE `-- &1 * x = -- x`;
ARITH_RULE `-- &1 * -- &1 = &1`;
ARITH_RULE `-- (-- x * y) = x * y`;
ARITH_RULE `x - x = &0`;
REAL_POW_ONE;
REAL_NEG_NEG;
];;

let REAL_ELIM = ref [
REAL_LT_INV;
REAL_ADD_SYM;
REAL_ADD_ASSOC;
REAL_MUL_SYM;
REAL_MUL_ASSOC;
REAL_LT_LE;
REAL_LE_LT;
real_div;
];;

let REAL_SIMP_TAC = REWRITE_TAC (
  !REAL_REWRITES
);; 

let REAL_SOLVE_TAC = ASM_MESON_TAC (!REAL_REWRITES @ !REAL_ELIM);;

let extend_real_rewrites l = 
  REAL_REWRITES := !REAL_REWRITES @ l;;

let BASIC_REWRITES = ref (!REAL_REWRITES @ !NUM_REWRITES);;
