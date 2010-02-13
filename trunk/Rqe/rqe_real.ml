(* ---------------------------------------------------------------------- *)
(*  Reals                                                                 *)
(* ---------------------------------------------------------------------- *)
let real_ty = `:real`;;
let rx = `x:real`;;
let ry = `y:real`;;
let rz = `z:real`;;
let rzero = `&0`;;
let req = `(=):real->real->bool`;;
let rneq = `(<>):real->real->bool`;;
let rlt = `(<):real->real->bool`;;
let rgt = `(>):real->real->bool`;;
let rle = `(<=):real->real->bool`;;
let rge = `(>=):real->real->bool`;;
let rm = `( * ):real->real->real`;;
let rs = `(-):real->real->real`;;
let rn = `(--):real->real`;;
let rd = `(/):real->real->real`;;
let rp = `(+):real->real->real`;;
let rzero = `&0`;;
let rone = `&1`;;
let rlast = `LAST:(real) list -> real`;;
let rappend = `APPEND:(real) list -> real list -> real list`;;
let mk_rlist l = mk_list (l,real_ty);;

let diffl_tm = `(diffl)`;;
let dest_diffl tm =
  try
    let l,var = dest_comb tm in
    let dp,p' = dest_comb l in
    let d,p = dest_comb dp in
    if not (d = diffl_tm) then failwith "dest_diffl: not a diffl" else
    let _,bod = dest_abs p in
      bod,p'
  with _ -> failwith "dest_diffl";;

let dest_mult =
  try
    dest_binop rm
  with _ -> failwith "dest_mult";;

let mk_mult = mk_binop rm;;

let pow_tm = `(pow)`;;
let dest_pow =
  try
    dest_binop pow_tm
  with _ -> failwith "dest_pow";;

let mk_plus = mk_binop rp;;
let mk_negative = curry mk_comb rn;;

let dest_plus =
  try
    dest_binop rp
  with _ -> failwith "dest_plus";;

let REAL_DENSE = prove(
  `!x y. x < y ==> ?z. x < z /\ z < y`,
(* {{{ Proof *)
  REPEAT STRIP_TAC THEN
  CLAIM `&0 < y - x` THENL
  [REWRITE_TAC[REAL_LT_SUB_LADD;REAL_ADD_LID] THEN
     POP_ASSUM MATCH_ACCEPT_TAC;
   DISCH_THEN (ASSUME_TAC o (MATCH_MP REAL_DOWN)) THEN
     POP_ASSUM MP_TAC THEN STRIP_TAC THEN
     EXISTS_TAC `e + x` THEN
     STRIP_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[GSYM REAL_ADD_RID])) THEN
      MATCH_MP_TAC REAL_LET_ADD2 THEN
      STRIP_TAC THENL
      [MATCH_ACCEPT_TAC REAL_LE_REFL;
       FIRST_ASSUM MATCH_ACCEPT_TAC];
      MATCH_EQ_MP_TAC ((GEN `y:real` (GEN `z:real` (ISPECL [`y:real`;`z:real`;`-- x`] REAL_LT_RADD)))) THEN
      REWRITE_TAC[GSYM REAL_ADD_ASSOC;REAL_ADD_RINV;REAL_ADD_RID] THEN
      REWRITE_TAC[GSYM real_sub] THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC]]);;
(* }}} *)

let REAL_LT_EXISTS = prove(
  `!x. ?y. x < y`,
(* {{{ Proof *)
  GEN_TAC THEN
  EXISTS_TAC `x + &1` THEN
  REAL_ARITH_TAC);;
(* }}} *)

let REAL_GT_EXISTS = prove(
  `!x. ?y. y < x`,
(* {{{ Proof *)
  GEN_TAC THEN
  EXISTS_TAC `x - &1` THEN
  REAL_ARITH_TAC);;
(* }}} *)

let REAL_DIV_DISTRIB_L = prove_by_refinement(
  `!x y z. x / (y * z) = (x / y) * (&1 / z)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_div;REAL_INV_MUL];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let REAL_DIV_DISTRIB_R = prove_by_refinement(
  `!x y z. x / (y * z) = (&1 / y) * (x / z)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_div;REAL_INV_MUL];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let REAL_DIV_DISTRIB_2 = prove_by_refinement(
  `!x y z. (x * w) / (y * z) = (x / y) * (w / z)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_div;REAL_INV_MUL];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let REAL_DIV_ADD_DISTRIB = prove_by_refinement(
  `!x y z. (x + y) / z = (x / z) + (y / z)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_div;REAL_INV_MUL];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let DIV_ID = prove_by_refinement(
 `!x. ~(x = &0) ==> (x / x = &1)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  REWRITE_TAC[real_div];
  ASM_MESON_TAC[REAL_MUL_LINV;REAL_MUL_SYM];
]);;

(* }}} *)

let POS_POW = prove_by_refinement(
 `!c x. &0 < c /\ &0 < x ==> &0 < c * x pow k`,
(* {{{ Proof *)

[
  MESON_TAC[REAL_POW_LT;REAL_LT_MUL]
]);;

(* }}} *)

let POS_NAT_POW = prove_by_refinement(
 `!c n. 0 < n /\ &0 < c ==> &0 < c * &n pow k`,
(* {{{ Proof *)

[
  MESON_TAC[REAL_POW_LT;REAL_LT_MUL;REAL_LT;]
]);;

(* }}} *)

let REAL_NUM_LE_0 = prove_by_refinement(
  `!n. &0 <= (&n)`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  REAL_ARITH_TAC;
  REWRITE_TAC[REAL];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let REAL_ARCH_SIMPLE_LT = prove_by_refinement(
  `!x. ?n. x < &n`,
(* {{{ Proof *)
[
  STRIP_TAC;
  CHOOSE_THEN ASSUME_TAC (ISPEC `x:real` REAL_ARCH_SIMPLE);
  EXISTS_TAC `SUC n`;
  REWRITE_TAC[REAL];
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let BINOMIAL_LEMMA_LT = prove_by_refinement(
   `!x y. &0 < x /\ &0 < y
           ==> !n. 0 < n ==> x pow n + y pow n <= (x + y) pow n`,
(* {{{ Proof *)

[
  REPEAT GEN_TAC;
  STRIP_TAC;
  INDUCT_TAC;
  ARITH_TAC;
  REWRITE_TAC[real_pow];
  STRIP_TAC;
  CASES_ON `n = 0`;
  ASM_REWRITE_TAC[real_pow;REAL_MUL_RID;REAL_LE_REFL];
  CLAIM `0 < n`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> ASSUME_TAC (MATCH_MP y x)));
  MATCH_MP_TAC REAL_LE_TRANS;
  EXISTS_TAC `(x + y) * (x pow n + y pow n)`;
  STRIP_TAC;
  REWRITE_TAC[REAL_ADD_RDISTRIB];
  MATCH_MP_TAC REAL_LE_ADD2;
  CONJ_TAC;
  MATCH_MP_TAC REAL_LE_LMUL;
  STRIP_TAC;
  FIRST_ASSUM (fun x -> MP_TAC x THEN ARITH_TAC);
  MATCH_MP_TAC (REAL_ARITH `&0 <= y ==> x <= x + y`);
  MATCH_MP_TAC REAL_POW_LE;
  FIRST_ASSUM (fun x -> MP_TAC x THEN ARITH_TAC);
  REWRITE_TAC[REAL_ADD_LDISTRIB];
  MATCH_MP_TAC (REAL_ARITH `&0 <= y ==> x <= y + x`);
  MATCH_MP_TAC REAL_LE_MUL;
  CONJ_TAC;
  FIRST_ASSUM (fun x -> MP_TAC x THEN REAL_ARITH_TAC);
  MATCH_MP_TAC (REAL_ARITH `x < y ==> x <= y`);
  MATCH_MP_TAC REAL_POW_LT;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  MATCH_MP_TAC REAL_LE_LMUL;
  CONJ_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;

(* }}} *)

let BINOMIAL_LEMMA = prove_by_refinement(
   `!x y. &0 <= x /\ &0 <= y
           ==> !n. 0 < n ==> x pow n + y pow n <= (x + y) pow n`,
(* {{{ Proof *)

[
  REPEAT GEN_TAC;
  STRIP_TAC;
  CASES_ON `(x = &0) \/ (y = &0)`;
  POP_ASSUM DISJ_CASES_TAC;
  ASM_REWRITE_TAC[real_pow;REAL_ADD_LID;POW_0];
  REPEAT STRIP_TAC;
  CLAIM `n = SUC (PRE n)`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ONCE_ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[POW_0;REAL_ADD_LID;real_pow;REAL_LE_REFL];
  REPEAT STRIP_TAC;
  CLAIM `n = SUC (PRE n)`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ONCE_ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[POW_0;REAL_ADD_LID;REAL_ADD_RID;real_pow;REAL_LE_REFL];
  POP_ASSUM MP_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC;
  MATCH_MP_TAC BINOMIAL_LEMMA_LT;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;

(* }}} *)

let NEG_ABS = prove_by_refinement(
  `!x. -- (abs x) <= &0`,
(* {{{ Proof *)
[
  REAL_ARITH_TAC;
]);;
(* }}} *)

let REAL_MUL_LT = prove_by_refinement(
  `!x y. x * y < &0 <=> (x < &0 /\ &0 < y) \/ (&0 < x /\ y < &0)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  EQ_TAC;
  REPEAT STRIP_TAC;
  CCONTR_TAC;
  REWRITE_ASSUMS ([REAL_NOT_LT;DE_MORGAN_THM;] @ !REAL_REWRITES);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `x = &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  DISCH_THEN (REWRITE_ASSUMS o list);
  REWRITE_ASSUMS !REAL_REWRITES;
  ASM_MESON_TAC !REAL_REWRITES;
  CLAIM `&0 * &0 <= x * y`;
  MATCH_MP_TAC REAL_LE_MUL2;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REAL_SIMP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `&0 * &0 <= --x * --y`;
  MATCH_MP_TAC REAL_LE_MUL2;
  REAL_SIMP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REAL_SIMP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `y = &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  DISCH_THEN (REWRITE_ASSUMS o list);
  REWRITE_ASSUMS !REAL_REWRITES;
  ASM_REWRITE_TAC[];
  EVERY_ASSUM MP_TAC THEN ARITH_TAC;
  (* save *)
  REPEAT STRIP_TAC;
  CLAIM `&0 < --x`;
  EVERY_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 * &0 < --x * y`;
  MATCH_MP_TAC REAL_LT_MUL2;
  REAL_SIMP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REAL_SIMP_TAC;
  REWRITE_TAC[REAL_ARITH `--y * x = --(y * x)`];
  REAL_ARITH_TAC;
  CLAIM `&0 < --y`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 * &0 < x * --y`;
  MATCH_MP_TAC REAL_LT_MUL2;
  REAL_SIMP_TAC;
  ASM_REWRITE_TAC[];
  REAL_SIMP_TAC;
  REWRITE_TAC[REAL_ARITH `x * --y = --(x * y)`];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let REAL_MUL_GT = prove_by_refinement(
  `!x y. &0 < x * y <=> (x < &0 /\ y < &0) \/ (&0 < x /\ &0 < y)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  EQ_TAC;
  REPEAT STRIP_TAC;
  ONCE_REWRITE_ASSUMS[ARITH_RULE `x < y <=> -- y < -- x`];
  REWRITE_ASSUMS[GSYM REAL_MUL_RNEG];
  REWRITE_ASSUMS[REAL_ARITH `-- &0 = &0`; REAL_MUL_LT];
  POP_ASSUM MP_TAC THEN REPEAT STRIP_TAC;
  DISJ1_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REPEAT STRIP_TAC;
  ONCE_REWRITE_TAC [ARITH_RULE `x * y = --x * --y`];
  ONCE_REWRITE_TAC [ARITH_RULE `&0 = &0 * &0`];
  MATCH_MP_TAC REAL_LT_MUL2;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  ONCE_REWRITE_TAC [ARITH_RULE `&0 = &0 * &0`];
  MATCH_MP_TAC REAL_LT_MUL2;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let REAL_DIV_INV = prove_by_refinement(
  `!y z. &0 < y /\ y < z ==> &1 / z < &1 / y`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[real_div];
  REAL_SIMP_TAC;
  MATCH_MP_TAC REAL_LT_INV2;
  ASM_MESON_TAC[];
]);;
(* }}} *)

let REAL_DIV_DENOM_LT = prove_by_refinement(
  `!x y z. &0 < x /\ &0 < y /\ y < z ==> x / z < x / y`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP;
  EXISTS_TAC `inv x`;
  REPEAT STRIP_TAC;
  REAL_SOLVE_TAC;
  REWRITE_TAC[real_div];
  ASM_SIMP_TAC[REAL_LT_IMP_NZ;REAL_MUL_ASSOC;REAL_MUL_LINV;];
  REAL_SIMP_TAC;
  MATCH_MP_TAC (REWRITE_RULE [REAL_MUL_LID;real_div] REAL_DIV_INV);
  ASM_MESON_TAC[];
]);;
(* }}} *)

let REAL_DIV_DENOM_LE = prove_by_refinement(
  `!x y z. &0 <= x /\ &0 < y /\ y <= z ==> x / z <= x / y`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CASES_ON `x = &0`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[real_div;REAL_MUL_LZERO;REAL_LE_REFL];
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP;
  EXISTS_TAC `inv x`;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC REAL_LT_INV;
  ASM_MESON_TAC[REAL_LT_LE];
  REWRITE_TAC[real_div];
  ASM_SIMP_TAC[REAL_LT_IMP_NZ;REAL_MUL_ASSOC;REAL_MUL_LINV;];
  REAL_SIMP_TAC;
  MATCH_MP_TAC REAL_LE_INV2;
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let REAL_NEG_DIV = prove_by_refinement(
  `!x y. -- x / -- y = x / y`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_div];
  REWRITE_TAC[REAL_INV_NEG];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let REAL_GT_IMP_NZ = prove(
  `!x. x < &0 ==> ~(x = &0)`,
(* {{{ Proof *)
 REAL_ARITH_TAC);;
(* }}} *)

let REAL_NEG_NZ = prove(
  `!x. x < &0 ==> ~(x = &0)`,
(* {{{ Proof *)
  REAL_ARITH_TAC);;
(* }}} *)

let PARITY_POW_LT = prove_by_refinement(
  `!a n. a < &0 ==> (EVEN n ==> a pow n > &0) /\ (ODD n ==> a pow n < &0)`,
(* {{{ Proof *)

[
  STRIP_TAC;
  INDUCT_TAC;
  REWRITE_TAC[EVEN;ODD;real_pow];
  REAL_ARITH_TAC;
  DISCH_THEN (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  REWRITE_TAC[EVEN;ODD;real_pow;NOT_EVEN;NOT_ODD];
  DISJ_CASES_TAC (ISPEC `n:num` EVEN_OR_ODD);
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[real_gt;REAL_MUL_GT];
  ASM_MESON_TAC[EVEN_AND_ODD];
  ASM_REWRITE_TAC[real_gt;REAL_MUL_LT];
  ASM_MESON_TAC[real_gt];
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[real_gt;REAL_MUL_LT;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[];
  ASM_MESON_TAC[EVEN_AND_ODD];
]);;

(* }}} *)

let EVEN_ODD_POW = prove_by_refinement(
  `!a n.  a <> &0 ==>
          (EVEN n ==> a pow n > &0) /\
          (ODD n ==> a < &0 ==> a pow n < &0) /\
          (ODD n ==> a > &0 ==> a pow n > &0)`,
(* {{{ Proof *)
[
  REWRITE_TAC[NEQ];
  REPEAT_N 2 STRIP_TAC;
  CLAIM `a < &0 \/ a > &0 \/ (a = &0)`;
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[PARITY_POW_LT];
  ASM_MESON_TAC[PARITY_POW_LT];
  ASM_MESON_TAC[REAL_POW_LT;real_gt];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_POW_LT;real_gt];
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  ASM_MESON_TAC[REAL_POW_LT;real_gt];
  ASM_REWRITE_TAC[];
]);;
(* }}} *)
