(* ========================================================================= *)
(* The type "real^2" regarded as the complex numbers.                        *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

new_type_abbrev("complex",`:real^2`);;

let prioritize_complex() =
  overload_interface("--",`vector_neg:complex->complex`);
  overload_interface("+",`vector_add:complex->complex->complex`);
  overload_interface("-",`vector_sub:complex->complex->complex`);
  overload_interface("*",`complex_mul:complex->complex->complex`);
  overload_interface("/",`complex_div:complex->complex->complex`);
  overload_interface("pow",`complex_pow:complex->num->complex`);
  overload_interface("inv",`complex_inv:complex->complex`);;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Real and imaginary parts of a number.                                     *)
(* ------------------------------------------------------------------------- *)

let RE_DEF = new_definition
  `Re(z:complex) = z$1`;;

let IM_DEF = new_definition
  `Im(z:complex) = z$2`;;

(* ------------------------------------------------------------------------- *)
(* Real injection and imaginary unit.                                        *)
(* ------------------------------------------------------------------------- *)

let complex = new_definition
 `complex(x,y) = vector[x;y]:complex`;;

let CX_DEF = new_definition
 `Cx(a) = complex(a,&0)`;;

let ii = new_definition
  `ii = complex(&0,&1)`;;

(* ------------------------------------------------------------------------- *)
(* Complex multiplication.                                                   *)
(* ------------------------------------------------------------------------- *)

let complex_mul = new_definition
  `w * z = complex(Re(w) * Re(z) - Im(w) * Im(z),
                   Re(w) * Im(z) + Im(w) * Re(z))`;;

let complex_inv = new_definition
  `inv(z) = complex(Re(z) / (Re(z) pow 2 + Im(z) pow 2),
                    --(Im(z)) / (Re(z) pow 2 + Im(z) pow 2))`;;

let complex_div = new_definition
  `w / z = w * inv(z)`;;

let complex_pow = define
  `(x pow 0 = Cx(&1)) /\
   (!n. x pow (SUC n) = x * x pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Various handy rewrites.                                                   *)
(* ------------------------------------------------------------------------- *)

let RE = prove
 (`(Re(complex(x,y)) = x)`,
  REWRITE_TAC[RE_DEF; complex; VECTOR_2]);;

let IM = prove
 (`Im(complex(x,y)) = y`,
  REWRITE_TAC[IM_DEF; complex; VECTOR_2]);;

let COMPLEX_EQ = prove
 (`!w z. (w = z) <=> (Re(w) = Re(z)) /\ (Im(w) = Im(z))`,
  SIMP_TAC[CART_EQ; FORALL_2; DIMINDEX_2; RE_DEF; IM_DEF]);;

let COMPLEX = prove
 (`!z. complex(Re(z),Im(z)) = z`,
  REWRITE_TAC[COMPLEX_EQ; RE; IM]);;

let COMPLEX_EQ_0 = prove
 (`z = Cx(&0) <=> Re(z) pow 2 + Im(z) pow 2 = &0`,
  REWRITE_TAC[COMPLEX_EQ; CX_DEF; RE; IM] THEN
  EQ_TAC THEN SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `!x y:real. x + y = &0 ==> &0 <= x /\ &0 <= y ==> x = &0 /\ y = &0`)) THEN
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE; REAL_ENTIRE]);;

let FORALL_COMPLEX = prove
 (`(!z. P z) <=> (!x y. P(complex(x,y)))`,
  MESON_TAC[COMPLEX]);;

let EXISTS_COMPLEX = prove
 (`(?z. P z) <=> (?x y. P(complex(x,y)))`,
  MESON_TAC[COMPLEX]);;

(* ------------------------------------------------------------------------- *)
(* Pseudo-definitions of other general vector concepts over R^2.             *)
(* ------------------------------------------------------------------------- *)

let complex_neg = prove
 (`--z = complex(--(Re(z)),--(Im(z)))`,
  REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN REWRITE_TAC[RE_DEF; IM_DEF] THEN
  SIMP_TAC[VECTOR_NEG_COMPONENT; DIMINDEX_2; ARITH]);;

let complex_add = prove
 (`w + z = complex(Re(w) + Re(z),Im(w) + Im(z))`,
  REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN REWRITE_TAC[RE_DEF; IM_DEF] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; DIMINDEX_2; ARITH]);;

let complex_sub = VECTOR_ARITH `(w:complex) - z = w + --z`;;

let complex_norm = prove
 (`norm(z) = sqrt(Re(z) pow 2 + Im(z) pow 2)`,
  REWRITE_TAC[vector_norm; dot; RE_DEF; IM_DEF; SUM_2; DIMINDEX_2] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let COMPLEX_SQNORM = prove
 (`norm(z) pow 2 = Re(z) pow 2 + Im(z) pow 2`,
  REWRITE_TAC[NORM_POW_2; dot; RE_DEF; IM_DEF; SUM_2; DIMINDEX_2] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Crude tactic to automate very simple algebraic equivalences.              *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_COMPLEX_ARITH_TAC =
  REWRITE_TAC[COMPLEX_EQ; RE; IM; CX_DEF;
              complex_add; complex_neg; complex_sub; complex_mul;
              complex_inv; complex_div] THEN
  CONV_TAC REAL_FIELD;;

let SIMPLE_COMPLEX_ARITH tm = prove(tm,SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Basic algebraic properties that can be proved automatically by this.      *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_ADD_SYM = prove
 (`!x y. x + y = y + x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_ASSOC = prove
 (`!x y z. x + y + z = (x + y) + z`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_LID = prove
 (`!x. Cx(&0) + x = x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_LINV = prove
 (`!x. --x + x = Cx(&0)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_SYM = prove
 (`!x y. x * y = y * x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_ASSOC = prove
 (`!x y z. x * y * z = (x * y) * z`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_LID = prove
 (`!x. Cx(&1) * x = x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_LDISTRIB = prove
 (`!x y z. x * (y + z) = x * y + x * z`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_AC = prove
 (`(m + n = n + m) /\ ((m + n) + p = m + n + p) /\ (m + n + p = n + m + p)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_AC = prove
 (`(m * n = n * m) /\ ((m * n) * p = m * n * p) /\ (m * n * p = n * m * p)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_RID = prove
 (`!x. x + Cx(&0) = x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_RID = prove
 (`!x. x * Cx(&1) = x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_RINV = prove
 (`!x. x + --x = Cx(&0)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_RDISTRIB = prove
 (`!x y z. (x + y) * z = x * z + y * z`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_EQ_ADD_LCANCEL = prove
 (`!x y z. (x + y = x + z) <=> (y = z)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_EQ_ADD_RCANCEL = prove
 (`!x y z. (x + z = y + z) <=> (x = y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_RZERO = prove
 (`!x. x * Cx(&0) = Cx(&0)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_LZERO = prove
 (`!x. Cx(&0) * x = Cx(&0)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_NEG = prove
 (`!x. --(--x) = x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_RNEG = prove
 (`!x y. x * --y = --(x * y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_LNEG = prove
 (`!x y. --x * y = --(x * y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_ADD = prove
 (`!x y. --(x + y) = --x + --y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_0 = prove
 (`--Cx(&0) = Cx(&0)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_EQ_ADD_LCANCEL_0 = prove
 (`!x y. (x + y = x) <=> (y = Cx(&0))`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_EQ_ADD_RCANCEL_0 = prove
 (`!x y. (x + y = y) <=> (x = Cx(&0))`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_LNEG_UNIQ = prove
 (`!x y. (x + y = Cx(&0)) <=> (x = --y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_RNEG_UNIQ = prove
 (`!x y. (x + y = Cx(&0)) <=> (y = --x)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_LMUL = prove
 (`!x y. --(x * y) = --x * y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_RMUL = prove
 (`!x y. --(x * y) = x * --y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_MUL2 = prove
 (`!x y. --x * --y = x * y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_ADD = prove
 (`!x y. x - y + y = x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_ADD2 = prove
 (`!x y. y + x - y = x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_REFL = prove
 (`!x. x - x = Cx(&0)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_0 = prove
 (`!x y. (x - y = Cx(&0)) <=> (x = y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_EQ_0 = prove
 (`!x. (--x = Cx(&0)) <=> (x = Cx(&0))`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_SUB = prove
 (`!x y. --(x - y) = y - x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_SUB = prove
 (`!x y. (x + y) - x = y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_EQ = prove
 (`!x y. (--x = y) <=> (x = --y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NEG_MINUS1 = prove
 (`!x. --x = --Cx(&1) * x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_SUB = prove
 (`!x y. x - y - x = --y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD2_SUB2 = prove
 (`!a b c d. (a + b) - (c + d) = a - c + b - d`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_LZERO = prove
 (`!x. Cx(&0) - x = --x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_RZERO = prove
 (`!x. x - Cx(&0) = x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_LNEG = prove
 (`!x y. --x - y = --(x + y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_RNEG = prove
 (`!x y. x - --y = x + y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_NEG2 = prove
 (`!x y. --x - --y = y - x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_TRIANGLE = prove
 (`!a b c. a - b + b - c = a - c`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_EQ_SUB_LADD = prove
 (`!x y z. (x = y - z) <=> (x + z = y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_EQ_SUB_RADD = prove
 (`!x y z. (x - y = z) <=> (x = z + y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_SUB2 = prove
 (`!x y. x - (x - y) = y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ADD_SUB2 = prove
 (`!x y. x - (x + y) = --y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_DIFFSQ = prove
 (`!x y. (x + y) * (x - y) = x * x - y * y`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_EQ_NEG2 = prove
 (`!x y. (--x = --y) <=> (x = y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_LDISTRIB = prove
 (`!x y z. x * (y - z) = x * y - x * z`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_SUB_RDISTRIB = prove
 (`!x y z. (x - y) * z = x * z - y * z`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_2 = prove
 (`!x. Cx(&2) * x = x + x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sometimes here we need to tweak non-zeroness assertions.                  *)
(* ------------------------------------------------------------------------- *)

let II_NZ = prove
 (`~(ii = Cx(&0))`,
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_LINV = prove
 (`!z. ~(z = Cx(&0)) ==> (inv(z) * z = Cx(&1))`,
  REWRITE_TAC[COMPLEX_EQ_0] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_ENTIRE = prove
 (`!x y. (x * y = Cx(&0)) <=> (x = Cx(&0)) \/ (y = Cx(&0))`,
  REWRITE_TAC[COMPLEX_EQ_0] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_MUL_RINV = prove
 (`!z. ~(z = Cx(&0)) ==> (z * inv(z) = Cx(&1))`,
  REWRITE_TAC[COMPLEX_EQ_0] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_DIV_REFL = prove
 (`!x. ~(x = Cx(&0)) ==> (x / x = Cx(&1))`,
  REWRITE_TAC[COMPLEX_EQ_0] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_VEC_0 = prove
 (`vec 0 = Cx(&0)`,
  SIMP_TAC[CART_EQ; VEC_COMPONENT; CX_DEF; complex;
           DIMINDEX_2; FORALL_2; VECTOR_2]);;

let COMPLEX_CMUL = prove
 (`!c x. c % x = Cx(c) * x`,
  SIMP_TAC[CART_EQ; VECTOR_MUL_COMPONENT; CX_DEF; complex;
           complex_mul; DIMINDEX_2; FORALL_2; IM_DEF; RE_DEF; VECTOR_2] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Homomorphic embedding properties for Cx mapping.                          *)
(* ------------------------------------------------------------------------- *)

let CX_INJ = prove
 (`!x y. (Cx(x) = Cx(y)) <=> (x = y)`,
  REWRITE_TAC[CX_DEF; COMPLEX_EQ; RE; IM]);;

let CX_NEG = prove
 (`!x. Cx(--x) = --(Cx(x))`,
  REWRITE_TAC[CX_DEF; complex_neg; RE; IM; REAL_NEG_0]);;

let CX_ADD = prove
 (`!x y. Cx(x + y) = Cx(x) + Cx(y)`,
  REWRITE_TAC[CX_DEF; complex_add; RE; IM; REAL_ADD_LID]);;

let CX_SUB = prove
 (`!x y. Cx(x - y) = Cx(x) - Cx(y)`,
  REWRITE_TAC[complex_sub; real_sub; CX_ADD; CX_NEG]);;

let CX_INV = prove
 (`!x. Cx(inv x) = inv(Cx x)`,
  GEN_TAC THEN REWRITE_TAC[CX_DEF; complex_inv; RE; IM; COMPLEX_EQ] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let CX_MUL = prove
 (`!x y. Cx(x * y) = Cx(x) * Cx(y)`,
  REWRITE_TAC[CX_DEF; complex_mul; RE; IM; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_RID]);;

let CX_POW = prove
 (`!x n. Cx(x pow n) = Cx(x) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; real_pow; CX_MUL]);;

let CX_DIV = prove
 (`!x y. Cx(x / y) = Cx(x) / Cx(y)`,
  REWRITE_TAC[complex_div; real_div; CX_MUL; CX_INV]);;

let CX_ABS = prove
 (`!x. Cx(abs x) = Cx(norm(Cx(x)))`,
  REWRITE_TAC[CX_DEF; complex_norm; COMPLEX_EQ; RE; IM] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

let COMPLEX_NORM_CX = prove
 (`!x. norm(Cx(x)) = abs(x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_ABS]);;

let DIST_CX = prove
 (`!x y. dist(Cx x,Cx y) = abs(x - y)`,
  REWRITE_TAC[dist; GSYM CX_SUB; COMPLEX_NORM_CX]);;

(* ------------------------------------------------------------------------- *)
(* Some "linear" things hold for Re and Im too.                              *)
(* ------------------------------------------------------------------------- *)

let RE_CX = prove
 (`!x. Re(Cx x) = x`,
  REWRITE_TAC[RE; CX_DEF]);;

let RE_NEG = prove
 (`!x. Re(--x) = --Re(x)`,
  REWRITE_TAC[complex_neg; RE]);;

let RE_ADD = prove
 (`!x y. Re(x + y) = Re(x) + Re(y)`,
  REWRITE_TAC[complex_add; RE]);;

let RE_SUB = prove
 (`!x y. Re(x - y) = Re(x) - Re(y)`,
  REWRITE_TAC[complex_sub; real_sub; RE_ADD; RE_NEG]);;

let IM_CX = prove
 (`!x. Im(Cx x) = &0`,
  REWRITE_TAC[IM; CX_DEF]);;

let IM_NEG = prove
 (`!x. Im(--x) = --Im(x)`,
  REWRITE_TAC[complex_neg; IM]);;

let IM_ADD = prove
 (`!x y. Im(x + y) = Im(x) + Im(y)`,
  REWRITE_TAC[complex_add; IM]);;

let IM_SUB = prove
 (`!x y. Im(x - y) = Im(x) - Im(y)`,
  REWRITE_TAC[complex_sub; real_sub; IM_ADD; IM_NEG]);;

(* ------------------------------------------------------------------------- *)
(* An "expansion" theorem into the traditional notation.                     *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_EXPAND = prove
 (`!z. z = Cx(Re z) + ii * Cx(Im z)`,
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_TRAD = prove
 (`!x y. complex(x,y) = Cx(x) + ii * Cx(y)`,
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Real and complex parts of ii and multiples.                               *)
(* ------------------------------------------------------------------------- *)

let RE_II = prove
 (`Re ii = &0`,
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let IM_II = prove
 (`Im ii = &1`,
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let RE_MUL_II = prove
 (`!z. Re(z * ii) = --(Im z) /\ Re(ii * z) = --(Im z)`,
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let IM_MUL_II = prove
 (`!z. Im(z * ii) = Re z /\ Im(ii * z) = Re z`,
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_NORM_II = prove
 (`norm ii = &1`,
  REWRITE_TAC[complex_norm; RE_II; IM_II] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_1]);;

(* ------------------------------------------------------------------------- *)
(* Limited "multiplicative" theorems for Re and Im.                          *)
(* ------------------------------------------------------------------------- *)

let RE_CMUL = prove
 (`!a z. Re(a % z) = a * Re z`,
  SIMP_TAC[RE_DEF; VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH]);;

let IM_CMUL = prove
 (`!a z. Im(a % z) = a * Im z`,
  SIMP_TAC[IM_DEF; VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH]);;

let RE_MUL_CX = prove
 (`!x z. Re(Cx(x) * z) = x * Re z /\
         Re(z * Cx(x)) = Re z * x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let IM_MUL_CX = prove
 (`!x z. Im(Cx(x) * z) = x * Im z /\
         Im(z * Cx(x)) = Im z * x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let RE_DIV_CX = prove
 (`!z x. Re(z / Cx(x)) = Re(z) / x`,
  REWRITE_TAC[complex_div; real_div; GSYM CX_INV; RE_MUL_CX]);;

let IM_DIV_CX = prove
 (`!z x. Im(z / Cx(x)) = Im(z) / x`,
  REWRITE_TAC[complex_div; real_div; GSYM CX_INV; IM_MUL_CX]);;

(* ------------------------------------------------------------------------- *)
(* Syntax constructors etc. for complex constants.                           *)
(* ------------------------------------------------------------------------- *)

let is_complex_const =
  let cx_tm = `Cx` in
  fun tm ->
    is_comb tm &
    let l,r = dest_comb tm in l = cx_tm & is_ratconst r;;

let dest_complex_const =
  let cx_tm = `Cx` in
  fun tm ->
    let l,r = dest_comb tm in
    if l = cx_tm then rat_of_term r
    else failwith "dest_complex_const";;

let mk_complex_const =
  let cx_tm = `Cx` in
  fun r ->
    mk_comb(cx_tm,term_of_rat r);;

(* ------------------------------------------------------------------------- *)
(* Conversions for arithmetic on complex constants.                          *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RAT_EQ_CONV =
  GEN_REWRITE_CONV I [CX_INJ] THENC REAL_RAT_EQ_CONV;;

let COMPLEX_RAT_MUL_CONV =
  GEN_REWRITE_CONV I [GSYM CX_MUL] THENC RAND_CONV REAL_RAT_MUL_CONV;;

let COMPLEX_RAT_ADD_CONV =
  GEN_REWRITE_CONV I [GSYM CX_ADD] THENC RAND_CONV REAL_RAT_ADD_CONV;;

let COMPLEX_RAT_POW_CONV =
  let x_tm = `x:real`
  and n_tm = `n:num` in
  let pth = SYM(SPECL [x_tm; n_tm] CX_POW) in
  fun tm ->
    let lop,r = dest_comb tm in
    let op,bod = dest_comb lop in
    let th1 = INST [rand bod,x_tm; r,n_tm] pth in
    let tm1,tm2 = dest_comb(concl th1) in
    if rand tm1 <> tm then failwith "COMPLEX_RAT_POW_CONV" else
    let tm3,tm4 = dest_comb tm2 in
    TRANS th1 (AP_TERM tm3 (REAL_RAT_REDUCE_CONV tm4));;

(* ------------------------------------------------------------------------- *)
(* Complex polynomial normalizer.                                            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLY_CLAUSES = prove
 (`(!x y z. x + (y + z) = (x + y) + z) /\
   (!x y. x + y = y + x) /\
   (!x. Cx(&0) + x = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x y. x * y = y * x) /\
   (!x. Cx(&1) * x = x) /\
   (!x. Cx(&0) * x = Cx(&0)) /\
   (!x y z. x * (y + z) = x * y + x * z) /\
   (!x. x pow 0 = Cx(&1)) /\
   (!x n. x pow (SUC n) = x * x pow n)`,
  REWRITE_TAC[complex_pow] THEN SIMPLE_COMPLEX_ARITH_TAC)
and COMPLEX_POLY_NEG_CLAUSES = prove
 (`(!x. --x = Cx(-- &1) * x) /\
   (!x y. x - y = x + Cx(-- &1) * y)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_POLY_NEG_CONV,COMPLEX_POLY_ADD_CONV,COMPLEX_POLY_SUB_CONV,
    COMPLEX_POLY_MUL_CONV,COMPLEX_POLY_POW_CONV,COMPLEX_POLY_CONV =
  SEMIRING_NORMALIZERS_CONV COMPLEX_POLY_CLAUSES COMPLEX_POLY_NEG_CLAUSES
   (is_complex_const,
    COMPLEX_RAT_ADD_CONV,COMPLEX_RAT_MUL_CONV,COMPLEX_RAT_POW_CONV)
   (<);;

(* ------------------------------------------------------------------------- *)
(* Extend it to handle "inv" and division, by constants after normalization. *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RAT_INV_CONV =
  REWR_CONV(GSYM CX_INV) THENC RAND_CONV REAL_RAT_INV_CONV;;

let COMPLEX_POLY_CONV =
  let neg_tm = `(--):complex->complex`
  and inv_tm = `inv:complex->complex`
  and add_tm = `(+):complex->complex->complex`
  and sub_tm = `(-):complex->complex->complex`
  and mul_tm = `(*):complex->complex->complex`
  and div_tm = `(/):complex->complex->complex`
  and pow_tm = `(pow):complex->num->complex`
  and div_conv = REWR_CONV complex_div in
  let rec COMPLEX_POLY_CONV tm =
    if not(is_comb tm) or is_ratconst tm then REFL tm else
    let lop,r = dest_comb tm in
    if lop = neg_tm then
      let th1 = AP_TERM lop (COMPLEX_POLY_CONV r) in
      TRANS th1 (COMPLEX_POLY_NEG_CONV (rand(concl th1)))
    else if lop = inv_tm then
      let th1 = AP_TERM lop (COMPLEX_POLY_CONV r) in
      TRANS th1 (TRY_CONV COMPLEX_RAT_INV_CONV (rand(concl th1)))
    else if not(is_comb lop) then REFL tm else
    let op,l = dest_comb lop in
    if op = pow_tm then
      let th1 = AP_THM (AP_TERM op (COMPLEX_POLY_CONV l)) r in
      TRANS th1 (TRY_CONV COMPLEX_POLY_POW_CONV (rand(concl th1)))
    else if op = add_tm or op = mul_tm or op = sub_tm then
      let th1 = MK_COMB(AP_TERM op (COMPLEX_POLY_CONV l),
                        COMPLEX_POLY_CONV r) in
      let fn = if op = add_tm then COMPLEX_POLY_ADD_CONV
               else if op = mul_tm then COMPLEX_POLY_MUL_CONV
               else COMPLEX_POLY_SUB_CONV in
      TRANS th1 (fn (rand(concl th1)))
    else if op = div_tm then
      let th1 = div_conv tm in
      TRANS th1 (COMPLEX_POLY_CONV (rand(concl th1)))
    else REFL tm in
  COMPLEX_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Complex number version of usual ring procedure.                           *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RING,complex_ideal_cofactors =
  let COMPLEX_INTEGRAL = prove
   (`(!x. Cx(&0) * x = Cx(&0)) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))`,
    REWRITE_TAC[COMPLEX_ENTIRE; SIMPLE_COMPLEX_ARITH
     `(w * y + x * z = w * z + x * y) <=>
      (w - x) * (y - z) = Cx(&0)`] THEN
    SIMPLE_COMPLEX_ARITH_TAC)
  and COMPLEX_RABINOWITSCH = prove
   (`!x y:complex. ~(x = y) <=> ?z. (x - y) * z = Cx(&1)`,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM COMPLEX_SUB_0] THEN
    MESON_TAC[COMPLEX_MUL_RINV; COMPLEX_MUL_LZERO;
              SIMPLE_COMPLEX_ARITH `~(Cx(&1) = Cx(&0))`])
  and COMPLEX_IIII = prove
   (`ii * ii + Cx(&1) = Cx(&0)`,
    REWRITE_TAC[ii; CX_DEF; complex_mul; complex_add; RE; IM] THEN
    AP_TERM_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC) in
  let ring,ideal =
    RING_AND_IDEAL_CONV
        (dest_complex_const,mk_complex_const,COMPLEX_RAT_EQ_CONV,
         `(--):complex->complex`,`(+):complex->complex->complex`,
         `(-):complex->complex->complex`,`(inv):complex->complex`,
         `(*):complex->complex->complex`,`(/):complex->complex->complex`,
         `(pow):complex->num->complex`,
         COMPLEX_INTEGRAL,COMPLEX_RABINOWITSCH,COMPLEX_POLY_CONV)
  and ii_tm = `ii` and iiii_tm = concl COMPLEX_IIII in
  (fun tm -> if free_in ii_tm tm then
             MP (ring (mk_imp(iiii_tm,tm))) COMPLEX_IIII
             else ring tm),
  ideal;;

(* ------------------------------------------------------------------------- *)
(* Most basic properties of inverses.                                        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_INV_0 = prove
 (`inv(Cx(&0)) = Cx(&0)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_INV_1 = prove
 (`inv(Cx(&1)) = Cx(&1)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_INV_MUL = prove
 (`!w z. inv(w * z) = inv(w) * inv(z)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`w = Cx(&0)`; `z = Cx(&0)`] THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[complex_mul; complex_inv; RE; IM; COMPLEX_EQ; CX_DEF] THEN
  REWRITE_TAC[GSYM REAL_SOS_EQ_0] THEN CONV_TAC REAL_FIELD);;

let COMPLEX_POW_INV = prove
 (`!x n. (inv x) pow n = inv(x pow n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; COMPLEX_INV_1; COMPLEX_INV_MUL]);;

let COMPLEX_INV_INV = prove
 (`!x:complex. inv(inv x) = x`,
  GEN_TAC THEN ASM_CASES_TAC `x = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0] THEN
  POP_ASSUM MP_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t COMPLEX_MUL_RINV))
   [`x:complex`; `inv(x):complex`] THEN
  CONV_TAC COMPLEX_RING);;

let COMPLEX_INV_DIV = prove
 (`!w z:complex. inv(w / z) = z / w`,
  REWRITE_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_INV_INV] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let COMPLEX_EQ_INV2 = prove
 (`!w x:complex. inv w = inv z <=> w = z`,
  MESON_TAC[COMPLEX_INV_INV]);;

let SGN_RE_COMPLEX_INV = prove
 (`!z. real_sgn(Re(inv z)) = real_sgn(Re z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0] THEN
  REWRITE_TAC[RE; complex_inv; REAL_SGN_DIV] THEN
  SUBGOAL_THEN `real_sgn (Re z pow 2 + Im z pow 2) = &1`
   (fun th -> REWRITE_TAC[REAL_DIV_1; th]) THEN
  REWRITE_TAC[REAL_SGN_EQ; real_gt; GSYM COMPLEX_SQNORM] THEN
  ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT; COMPLEX_VEC_0]);;

let RE_COMPLEX_INV_GT_0 = prove
 (`!z. &0 < Re(inv z) <=> &0 < Re z`,
  REWRITE_TAC[GSYM real_gt; GSYM REAL_SGN_EQ; SGN_RE_COMPLEX_INV]);;

let RE_COMPLEX_INV_GE_0 = prove
 (`!z. &0 <= Re(inv z) <=> &0 <= Re z`,
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_SGN_EQ; SGN_RE_COMPLEX_INV]);;

(* ------------------------------------------------------------------------- *)
(* And also field procedure.                                                 *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_EQ_MUL_LCANCEL = prove
 (`!x y z. (x * y = x * z) <=> (x = Cx(&0)) \/ (y = z)`,
  CONV_TAC COMPLEX_RING);;

let COMPLEX_EQ_MUL_RCANCEL = prove
 (`!x y z. (x * z = y * z) <=> (x = y) \/ (z = Cx(&0))`,
  CONV_TAC COMPLEX_RING);;

let COMPLEX_FIELD =
  let prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PURE_REWRITE_CONV[FORALL_SIMP; EXISTS_SIMP; complex_div;
               COMPLEX_INV_INV; COMPLEX_INV_MUL; GSYM COMPLEX_POW_INV] THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV `(/\)` CONDS_CELIM_CONV THENC
    PRENEX_CONV
  and setup_conv = NNF_CONV THENC WEAK_CNF_CONV THENC CONJ_CANON_CONV
  and is_inv =
    let inv_tm = `inv:complex->complex`
    and is_div = is_binop `(/):complex->complex->complex` in
    fun tm -> (is_div tm or (is_comb tm & rator tm = inv_tm)) &
              not(is_ratconst(rand tm)) in
  let BASIC_COMPLEX_FIELD tm =
    let is_freeinv t = is_inv t & free_in t tm in
    let itms = setify(map rand (find_terms is_freeinv tm)) in
    let hyps = map (fun t -> SPEC t COMPLEX_MUL_RINV) itms in
    let tm' = itlist (fun th t -> mk_imp(concl th,t)) hyps tm in
    let th1 = setup_conv tm' in
    let cjs = conjuncts(rand(concl th1)) in
    let ths = map COMPLEX_RING cjs in
    let th2 = EQ_MP (SYM th1) (end_itlist CONJ ths) in
    rev_itlist (C MP) hyps th2 in
  fun tm ->
    let th0 = prenex_conv tm in
    let tm0 = rand(concl th0) in
    let avs,bod = strip_forall tm0 in
    let th1 = setup_conv bod in
    let ths = map BASIC_COMPLEX_FIELD (conjuncts(rand(concl th1))) in
    EQ_MP (SYM th0) (GENL avs (EQ_MP (SYM th1) (end_itlist CONJ ths)));;

(* ------------------------------------------------------------------------- *)
(* More trivial lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DIV_1 = prove
 (`!z. z / Cx(&1) = z`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIV_LMUL = prove
 (`!x y. ~(y = Cx(&0)) ==> y * x / y = x`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIV_RMUL = prove
 (`!x y. ~(y = Cx(&0)) ==> x / y * y = x`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_INV_EQ_0 = prove
 (`!x. inv x = Cx(&0) <=> x = Cx(&0)`,
  GEN_TAC THEN ASM_CASES_TAC `x = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0] THEN POP_ASSUM MP_TAC THEN
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_INV_NEG = prove
 (`!x:complex. inv(--x) = --(inv x)`,
  GEN_TAC THEN ASM_CASES_TAC `x = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0; COMPLEX_NEG_0] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

let COMPLEX_NEG_INV = prove
 (`!x:complex. --(inv x) = inv(--x)`,
  REWRITE_TAC[COMPLEX_INV_NEG]);;

let COMPLEX_INV_EQ_1 = prove
 (`!x. inv x = Cx(&1) <=> x = Cx(&1)`,
  GEN_TAC THEN ASM_CASES_TAC `x = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0] THEN POP_ASSUM MP_TAC THEN
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIV_EQ_0 = prove
 (`!w z. w / z = Cx(&0) <=> w = Cx(&0) \/ z = Cx(&0)`,
  REWRITE_TAC[complex_div; COMPLEX_INV_EQ_0; COMPLEX_ENTIRE]);;

(* ------------------------------------------------------------------------- *)
(* Powers.                                                                   *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POW_ADD = prove
 (`!x m n. x pow (m + n) = x pow m * x pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; complex_pow;
                  COMPLEX_MUL_LID; COMPLEX_MUL_ASSOC]);;

let COMPLEX_POW_POW = prove
 (`!x m n. (x pow m) pow n = x pow (m * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; MULT_CLAUSES; COMPLEX_POW_ADD]);;

let COMPLEX_POW_1 = prove
 (`!x. x pow 1 = x`,
  REWRITE_TAC[num_CONV `1`] THEN REWRITE_TAC[complex_pow; COMPLEX_MUL_RID]);;

let COMPLEX_POW_2 = prove
 (`!x. x pow 2 = x * x`,
  REWRITE_TAC[num_CONV `2`] THEN REWRITE_TAC[complex_pow; COMPLEX_POW_1]);;

let COMPLEX_POW_NEG = prove
 (`!x n. (--x) pow n = if EVEN n then x pow n else --(x pow n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; EVEN] THEN
  ASM_CASES_TAC `EVEN n` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RNEG; COMPLEX_MUL_LNEG; COMPLEX_NEG_NEG]);;

let COMPLEX_POW_ONE = prove
 (`!n. Cx(&1) pow n = Cx(&1)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[complex_pow; COMPLEX_MUL_LID]);;

let COMPLEX_POW_MUL = prove
 (`!x y n. (x * y) pow n = (x pow n) * (y pow n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; COMPLEX_MUL_LID; COMPLEX_MUL_AC]);;

let COMPLEX_POW_DIV = prove
 (`!x y n. (x / y) pow n = (x pow n) / (y pow n)`,
  REWRITE_TAC[complex_div; COMPLEX_POW_MUL; COMPLEX_POW_INV]);;

let COMPLEX_POW_II_2 = prove
 (`ii pow 2 = --Cx(&1)`,
  REWRITE_TAC[ii; COMPLEX_POW_2; complex_mul; CX_DEF; RE; IM; complex_neg] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let COMPLEX_POW_EQ_0 = prove
 (`!x n. (x pow n = Cx(&0)) <=> (x = Cx(&0)) /\ ~(n = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_SUC; complex_pow; COMPLEX_ENTIRE] THENL
   [SIMPLE_COMPLEX_ARITH_TAC; CONV_TAC TAUT]);;

let COMPLEX_POW_ZERO = prove
 (`!n. Cx(&0) pow n = if n = 0 then Cx(&1) else Cx(&0)`,
  INDUCT_TAC THEN REWRITE_TAC[complex_pow; COMPLEX_MUL_LZERO; NOT_SUC]);;

let COMPLEX_INV_II = prove
 (`inv ii = --ii`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIV_POW = prove
 (`!x:complex n k:num.
      ~(x= Cx(&0)) /\ k <= n /\ ~(k = 0)
      ==> x pow (n - k) = x pow n / x pow k`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `x:complex pow (n - k) * x pow k =
  x pow n / x pow k * x pow k` (fun th-> ASM_MESON_TAC
  [th;COMPLEX_POW_EQ_0;COMPLEX_EQ_MUL_RCANCEL])
  THEN ASM_SIMP_TAC[GSYM COMPLEX_POW_ADD;SUB_ADD] THEN
  MP_TAC (MESON [COMPLEX_POW_EQ_0;ASSUME `~(k = 0)`; ASSUME `~(x = Cx(&0))`]
  `~(x pow k = Cx(&0))`) THEN ASM_SIMP_TAC[COMPLEX_DIV_RMUL]);;

let COMPLEX_DIV_POW2 = prove
 (`!z m n. ~(z = Cx(&0))
           ==> z pow m / z pow n =
               if n <= m then z pow (m - n) else inv(z pow (n - m))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[COMPLEX_POW_EQ_0; COMPLEX_FIELD
    `~(b = Cx(&0)) /\ ~(c = Cx(&0))
     ==> (a / b = inv c <=> a * c = b)`] THEN
  ASM_SIMP_TAC[COMPLEX_POW_EQ_0; COMPLEX_FIELD
   `~(b = Cx(&0)) ==> (a / b = c <=> b * c = a)`] THEN
  REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Norms (aka "moduli").                                                     *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_NORM_ZERO = prove
 (`!z. (norm z = &0) <=> (z = Cx(&0))`,
  REWRITE_TAC[NORM_EQ_0; COMPLEX_VEC_0]);;

let COMPLEX_NORM_NUM = prove
 (`!n. norm(Cx(&n)) = &n`,
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM]);;

let COMPLEX_NORM_0 = prove
 (`norm(Cx(&0)) = &0`,
  MESON_TAC[COMPLEX_NORM_ZERO]);;

let COMPLEX_NORM_NZ = prove
 (`!z. &0 < norm(z) <=> ~(z = Cx(&0))`,
  REWRITE_TAC[NORM_POS_LT; COMPLEX_VEC_0]);;

let COMPLEX_NORM_MUL = prove
 (`!w z. norm(w * z) = norm(w) * norm(z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_norm; complex_mul; RE; IM] THEN
  SIMP_TAC[GSYM SQRT_MUL; REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let COMPLEX_NORM_POW = prove
 (`!z n. norm(z pow n) = norm(z) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; real_pow; COMPLEX_NORM_NUM; COMPLEX_NORM_MUL]);;

let COMPLEX_NORM_INV = prove
 (`!z. norm(inv z) = inv(norm z)`,
  GEN_TAC THEN REWRITE_TAC[complex_norm; complex_inv; RE; IM] THEN
  REWRITE_TAC[REAL_POW_2; real_div] THEN
  REWRITE_TAC[REAL_ARITH `(r * d) * r * d + (--i * d) * --i * d =
                          (r * r + i * i) * d * d:real`] THEN
  ASM_CASES_TAC `Re z * Re z + Im z * Im z = &0` THENL
   [ASM_REWRITE_TAC[REAL_INV_0; SQRT_0; REAL_MUL_LZERO]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
  SIMP_TAC[GSYM SQRT_MUL; REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LE_ADD;
           REAL_LE_SQUARE] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `a * a * b * b:real = (a * b) * (a * b)`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID; SQRT_1]);;

let COMPLEX_NORM_DIV = prove
 (`!w z. norm(w / z) = norm(w) / norm(z)`,
  REWRITE_TAC[complex_div; real_div; COMPLEX_NORM_INV; COMPLEX_NORM_MUL]);;

let COMPLEX_NORM_TRIANGLE_SUB = prove
 (`!w z. norm(w) <= norm(w + z) + norm(z)`,
  MESON_TAC[NORM_TRIANGLE; NORM_NEG; COMPLEX_ADD_ASSOC;
            COMPLEX_ADD_RINV; COMPLEX_ADD_RID]);;

let COMPLEX_NORM_ABS_NORM = prove
 (`!w z. abs(norm w - norm z) <= norm(w - z)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `a - b <= x /\ b - a <= x ==> abs(a - b) <= x:real`) THEN
  MESON_TAC[COMPLEX_NEG_SUB; NORM_NEG; REAL_LE_SUB_RADD; complex_sub;
            COMPLEX_NORM_TRIANGLE_SUB]);;

let COMPLEX_POW_EQ_1 = prove
 (`!z n. z pow n = Cx(&1) ==> norm(z) = &1 \/ n = 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  SIMP_TAC[COMPLEX_NORM_POW; COMPLEX_NORM_CX; REAL_POW_EQ_1; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_ABS_NORM] THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Complex conjugate.                                                        *)
(* ------------------------------------------------------------------------- *)

let cnj = new_definition
  `cnj(z) = complex(Re(z),--(Im(z)))`;;

(* ------------------------------------------------------------------------- *)
(* Conjugation is an automorphism.                                           *)
(* ------------------------------------------------------------------------- *)

let CNJ_INJ = prove
 (`!w z. (cnj(w) = cnj(z)) <=> (w = z)`,
  REWRITE_TAC[cnj; COMPLEX_EQ; RE; IM; REAL_EQ_NEG2]);;

let CNJ_CNJ = prove
 (`!z. cnj(cnj z) = z`,
  REWRITE_TAC[cnj; COMPLEX_EQ; RE; IM; REAL_NEG_NEG]);;

let CNJ_CX = prove
 (`!x. cnj(Cx x) = Cx x`,
  REWRITE_TAC[cnj; COMPLEX_EQ; CX_DEF; REAL_NEG_0; RE; IM]);;

let COMPLEX_NORM_CNJ = prove
 (`!z. norm(cnj z) = norm(z)`,
  REWRITE_TAC[complex_norm; cnj; REAL_POW_2] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; RE; IM; REAL_NEG_NEG]);;

let CNJ_NEG = prove
 (`!z. cnj(--z) = --(cnj z)`,
  REWRITE_TAC[cnj; complex_neg; COMPLEX_EQ; RE; IM]);;

let CNJ_INV = prove
 (`!z. cnj(inv z) = inv(cnj z)`,
  REWRITE_TAC[cnj; complex_inv; COMPLEX_EQ; RE; IM] THEN
  REWRITE_TAC[real_div; REAL_NEG_NEG; REAL_POW_2;
              REAL_MUL_LNEG; REAL_MUL_RNEG]);;

let CNJ_ADD = prove
 (`!w z. cnj(w + z) = cnj(w) + cnj(z)`,
  REWRITE_TAC[cnj; complex_add; COMPLEX_EQ; RE; IM] THEN
  REWRITE_TAC[REAL_NEG_ADD; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

let CNJ_SUB = prove
 (`!w z. cnj(w - z) = cnj(w) - cnj(z)`,
  REWRITE_TAC[complex_sub; CNJ_ADD; CNJ_NEG]);;

let CNJ_MUL = prove
 (`!w z. cnj(w * z) = cnj(w) * cnj(z)`,
  REWRITE_TAC[cnj; complex_mul; COMPLEX_EQ; RE; IM] THEN
  REWRITE_TAC[REAL_NEG_ADD; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

let CNJ_DIV = prove
 (`!w z. cnj(w / z) = cnj(w) / cnj(z)`,
  REWRITE_TAC[complex_div; CNJ_MUL; CNJ_INV]);;

let CNJ_POW = prove
 (`!z n. cnj(z pow n) = cnj(z) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; CNJ_MUL; CNJ_CX]);;

let RE_CNJ = prove
 (`!z. Re(cnj z) = Re z`,
  REWRITE_TAC[cnj; RE]);;

let IM_CNJ = prove
 (`!z. Im(cnj z) = --Im z`,
  REWRITE_TAC[cnj; IM]);;

let CNJ_EQ_CX = prove
 (`!x z. cnj z = Cx x <=> z = Cx x`,
  REWRITE_TAC[COMPLEX_EQ; RE_CNJ; IM_CNJ; RE_CX; IM_CX] THEN
  CONV_TAC REAL_RING);;

let CNJ_EQ_0 = prove
 (`!z. cnj z = Cx(&0) <=> z = Cx(&0)`,
  REWRITE_TAC[CNJ_EQ_CX]);;

let COMPLEX_ADD_CNJ = prove
 (`(!z. z + cnj z = Cx(&2 * Re z)) /\ (!z. cnj z + z = Cx(&2 * Re z))`,
  REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX; RE_ADD; IM_ADD; RE_CNJ; IM_CNJ] THEN
  REAL_ARITH_TAC);;

let CNJ_II = prove
 (`cnj ii = --ii`,
  REWRITE_TAC[cnj; ii; RE; IM; complex_neg; REAL_NEG_0]);;

let CX_RE_CNJ = prove
 (`!z. Cx(Re z) = (z + cnj z) / Cx(&2)`,
  REWRITE_TAC[COMPLEX_EQ; RE_DIV_CX; IM_DIV_CX; RE_CX; IM_CX] THEN
  REWRITE_TAC[RE_ADD; IM_ADD; RE_CNJ; IM_CNJ] THEN REAL_ARITH_TAC);;

let CX_IM_CNJ = prove
 (`!z. Cx(Im z) = --ii * (z - cnj z) / Cx(&2)`,
  REWRITE_TAC[COMPLEX_EQ; RE_DIV_CX; IM_DIV_CX; RE_CX; IM_CX;
              COMPLEX_MUL_LNEG; RE_NEG; IM_NEG; RE_MUL_II; IM_MUL_II] THEN
  REWRITE_TAC[RE_SUB; IM_SUB; RE_CNJ; IM_CNJ] THEN REAL_ARITH_TAC);;

let FORALL_CNJ = prove
 (`(!z. P(cnj z)) <=> (!z. P z)`,
  MESON_TAC[CNJ_CNJ]);;

let EXISTS_CNJ = prove
 (`(?z. P(cnj z)) <=> (?z. P z)`,
  MESON_TAC[CNJ_CNJ]);;

(* ------------------------------------------------------------------------- *)
(* Slightly ad hoc theorems relating multiplication, inverse and conjugation *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_NORM_POW_2 = prove
 (`!z. Cx(norm z) pow 2 = z * cnj z`,
  GEN_TAC THEN REWRITE_TAC [GSYM CX_POW; COMPLEX_SQNORM] THEN
  REWRITE_TAC [cnj; complex_mul; CX_DEF; RE; IM; COMPLEX_EQ] THEN
  CONV_TAC REAL_RING);;

let COMPLEX_MUL_CNJ = prove
 (`!z. cnj z * z = Cx(norm(z)) pow 2 /\ z * cnj z = Cx(norm(z)) pow 2`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[cnj; complex_mul; RE; IM; GSYM CX_POW; COMPLEX_SQNORM] THEN
  REWRITE_TAC[CX_DEF] THEN AP_TERM_TAC THEN BINOP_TAC THEN
  CONV_TAC REAL_RING);;

let COMPLEX_INV_CNJ = prove
 (`!z. inv z = cnj z / Cx(norm z) pow 2`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[CNJ_CX; complex_div; COMPLEX_INV_0; COMPLEX_MUL_LZERO];
    MATCH_MP_TAC(COMPLEX_FIELD
     `x * y = z /\ ~(x = Cx(&0)) /\ ~(z = Cx(&0)) ==> inv x = y / z`) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; CX_INJ; REAL_POW_EQ_0] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_ZERO; ARITH]]);;

let COMPLEX_DIV_CNJ = prove
 (`!a b. a / b = (a * cnj b) / Cx(norm b) pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [COMPLEX_INV_CNJ] THEN
  REWRITE_TAC[complex_div]);;

let RE_COMPLEX_DIV_EQ_0 = prove
 (`!a b. Re(a / b) = &0 <=> Re(a * cnj b) = &0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN
  REWRITE_TAC[complex_div; GSYM CX_POW; GSYM CX_INV] THEN
  REWRITE_TAC[RE_MUL_CX; REAL_INV_EQ_0; REAL_POW_EQ_0; ARITH;
              REAL_ENTIRE; COMPLEX_NORM_ZERO] THEN
  ASM_CASES_TAC `b = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CNJ_CX; COMPLEX_MUL_RZERO; RE_CX]);;

let IM_COMPLEX_DIV_EQ_0 = prove
 (`!a b. Im(a / b) = &0 <=> Im(a * cnj b) = &0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN
  REWRITE_TAC[complex_div; GSYM CX_POW; GSYM CX_INV] THEN
  REWRITE_TAC[IM_MUL_CX; REAL_INV_EQ_0; REAL_POW_EQ_0; ARITH;
              REAL_ENTIRE; COMPLEX_NORM_ZERO] THEN
  ASM_CASES_TAC `b = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CNJ_CX; COMPLEX_MUL_RZERO; IM_CX]);;

let RE_COMPLEX_DIV_GT_0 = prove
 (`!a b. &0 < Re(a / b) <=> &0 < Re(a * cnj b)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN
  REWRITE_TAC[complex_div; GSYM CX_POW; GSYM CX_INV] THEN
  REWRITE_TAC[RE_MUL_CX; REAL_INV_EQ_0; REAL_POW_EQ_0; ARITH;
              REAL_ENTIRE; COMPLEX_NORM_ZERO] THEN
  ASM_CASES_TAC `b = Cx(&0)` THEN
  ASM_REWRITE_TAC[CNJ_CX; COMPLEX_MUL_RZERO; RE_CX; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_ARITH `&0 < a * x <=> &0 * x < a * x`] THEN
  ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_INV_EQ; REAL_POW_LT; ARITH;
               COMPLEX_NORM_NZ]);;

let IM_COMPLEX_DIV_GT_0 = prove
 (`!a b. &0 < Im(a / b) <=> &0 < Im(a * cnj b)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN
  REWRITE_TAC[complex_div; GSYM CX_POW; GSYM CX_INV] THEN
  REWRITE_TAC[IM_MUL_CX; REAL_INV_EQ_0; REAL_POW_EQ_0; ARITH;
              REAL_ENTIRE; COMPLEX_NORM_ZERO] THEN
  ASM_CASES_TAC `b = Cx(&0)` THEN
  ASM_REWRITE_TAC[CNJ_CX; COMPLEX_MUL_RZERO; IM_CX; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_ARITH `&0 < a * x <=> &0 * x < a * x`] THEN
  ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_INV_EQ; REAL_POW_LT; ARITH;
               COMPLEX_NORM_NZ]);;

let RE_COMPLEX_DIV_GE_0 = prove
 (`!a b. &0 <= Re(a / b) <=> &0 <= Re(a * cnj b)`,
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> &0 < x \/ x = &0`] THEN
  REWRITE_TAC[RE_COMPLEX_DIV_GT_0; RE_COMPLEX_DIV_EQ_0]);;

let IM_COMPLEX_DIV_GE_0 = prove
 (`!a b. &0 <= Im(a / b) <=> &0 <= Im(a * cnj b)`,
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> &0 < x \/ x = &0`] THEN
  REWRITE_TAC[IM_COMPLEX_DIV_GT_0; IM_COMPLEX_DIV_EQ_0]);;

let RE_COMPLEX_DIV_LE_0 = prove
 (`!a b. Re(a / b) <= &0 <=> Re(a * cnj b) <= &0`,
  REWRITE_TAC[GSYM REAL_NOT_LT; RE_COMPLEX_DIV_GT_0]);;

let IM_COMPLEX_DIV_LE_0 = prove
 (`!a b. Im(a / b) <= &0 <=> Im(a * cnj b) <= &0`,
  REWRITE_TAC[GSYM REAL_NOT_LT; IM_COMPLEX_DIV_GT_0]);;

let RE_COMPLEX_DIV_LT_0 = prove
 (`!a b. Re(a / b) < &0 <=> Re(a * cnj b) < &0`,
  REWRITE_TAC[GSYM REAL_NOT_LE; RE_COMPLEX_DIV_GE_0]);;

let IM_COMPLEX_DIV_LT_0 = prove
 (`!a b. Im(a / b) < &0 <=> Im(a * cnj b) < &0`,
  REWRITE_TAC[GSYM REAL_NOT_LE; IM_COMPLEX_DIV_GE_0]);;

let IM_COMPLEX_INV_GE_0 = prove
 (`!z. &0 <= Im(inv z) <=> Im(z) <= &0`,
  GEN_TAC THEN MP_TAC(ISPECL [`Cx(&1)`; `z:complex`] IM_COMPLEX_DIV_GE_0) THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LID; IM_CNJ] THEN REAL_ARITH_TAC);;

let IM_COMPLEX_INV_LE_0 = prove
 (`!z. Im(inv z) <= &0 <=> &0 <= Im(z)`,
  MESON_TAC[IM_COMPLEX_INV_GE_0; COMPLEX_INV_INV]);;

let IM_COMPLEX_INV_GT_0 = prove
 (`!z. &0 < Im(inv z) <=> Im(z) < &0`,
  REWRITE_TAC[REAL_ARITH `&0 < a <=> ~(a <= &0)`; IM_COMPLEX_INV_LE_0] THEN
  REAL_ARITH_TAC);;

let IM_COMPLEX_INV_LT_0 = prove
 (`!z. Im(inv z) < &0 <=> &0 < Im(z)`,
  REWRITE_TAC[REAL_ARITH `a < &0 <=> ~(&0 <= a)`; IM_COMPLEX_INV_GE_0] THEN
  REAL_ARITH_TAC);;

let IM_COMPLEX_INV_EQ_0 = prove
 (`!z. Im(inv z) = &0 <=> Im(z) = &0`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; IM_COMPLEX_INV_LE_0; IM_COMPLEX_INV_GE_0] THEN
  REAL_ARITH_TAC);;

let REAL_SGN_RE_COMPLEX_DIV = prove
 (`!w z. real_sgn(Re(w / z)) = real_sgn(Re(w * cnj z))`,
  REWRITE_TAC[real_sgn; RE_COMPLEX_DIV_GT_0; RE_COMPLEX_DIV_GE_0;
              REAL_ARITH `x < &0 <=> ~(&0 <= x)`]);;

let REAL_SGN_IM_COMPLEX_DIV = prove
 (`!w z. real_sgn(Im(w / z)) = real_sgn(Im(w * cnj z))`,
  REWRITE_TAC[real_sgn; IM_COMPLEX_DIV_GT_0; IM_COMPLEX_DIV_GE_0;
              REAL_ARITH `x < &0 <=> ~(&0 <= x)`]);;

(* ------------------------------------------------------------------------- *)
(* Norm versus components for complex numbers.                               *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_NORM_GE_RE_IM = prove
 (`!z. abs(Re(z)) <= norm(z) /\ abs(Im(z)) <= norm(z)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
  REWRITE_TAC[complex_norm] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_ADDL; REAL_POW_2; REAL_LE_SQUARE]);;

let COMPLEX_NORM_LE_RE_IM = prove
 (`!z. norm(z) <= abs(Re z) + abs(Im z)`,
  GEN_TAC THEN MP_TAC(ISPEC `z:complex` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; RE_DEF; IM_DEF]);;

let COMPLEX_L1_LE_NORM = prove
 (`!z. sqrt(&2) / &2 * (abs(Re z) + abs(Im z)) <= norm z`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `sqrt(&2)` THEN
  SIMP_TAC[REAL_ARITH `x * x / &2 * y = (x pow 2) / &2 * y`;
           SQRT_POW_2; REAL_POS; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
  MP_TAC(ISPEC `z:complex` L1_LE_NORM) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; RE_DEF; IM_DEF] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Complex square roots.                                                     *)
(* ------------------------------------------------------------------------- *)

let csqrt = new_definition
  `csqrt(z) = if Im(z) = &0 then
                if &0 <= Re(z) then complex(sqrt(Re(z)),&0)
                else complex(&0,sqrt(--Re(z)))
              else complex(sqrt((norm(z) + Re(z)) / &2),
                           (Im(z) / abs(Im(z))) *
                           sqrt((norm(z) - Re(z)) / &2))`;;


let CSQRT = prove
 (`!z. csqrt(z) pow 2 = z`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_POW_2; csqrt] THEN COND_CASES_TAC THENL
   [COND_CASES_TAC THEN
    ASM_REWRITE_TAC[CX_DEF; complex_mul; RE; IM; REAL_MUL_RZERO; REAL_MUL_LZERO;
      REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_ADD_LID; COMPLEX_EQ] THEN
    REWRITE_TAC[REAL_NEG_EQ; GSYM REAL_POW_2] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_ARITH `~(&0 <= x) ==> &0 <= --x`];
    ALL_TAC] THEN
  REWRITE_TAC[complex_mul; RE; IM] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(s * s - (i * s') * (i * s') = s * s - (i * i) * (s' * s')) /\
    (s * i * s' + (i * s')* s = &2 * i * s * s')`] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN
  SUBGOAL_THEN `&0 <= norm(z) + Re(z) /\ &0 <= norm(z) - Re(z)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; GSYM SQRT_MUL; SQRT_POW_2] THEN
  REWRITE_TAC[COMPLEX_EQ; RE; IM] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_DIV; REAL_POW2_ABS;
                 REAL_POW_EQ_0; REAL_DIV_REFL] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_ARITH `(m + r) - (m - r) = r * &2`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `(a * b) * a' * b = (a * a') * (b * b:real)`] THEN
  REWRITE_TAC[REAL_DIFFSQ] THEN
  REWRITE_TAC[complex_norm; GSYM REAL_POW_2] THEN
  SIMP_TAC[SQRT_POW_2; REAL_LE_ADD;
           REWRITE_RULE[GSYM REAL_POW_2] REAL_LE_SQUARE] THEN
  REWRITE_TAC[REAL_ADD_SUB; GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[POW_2_SQRT_ABS] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `&2 * (i * a') * a * h = i * (&2 * h) * a * a'`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LID; GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_ABS_ZERO; REAL_MUL_RID]);;

let CX_SQRT = prove
 (`!x. &0 <= x ==> Cx(sqrt x) = csqrt(Cx x)`,
  SIMP_TAC[csqrt; IM_CX; RE_CX; COMPLEX_EQ; RE; IM]);;

let CSQRT_CX = prove
 (`!x. &0 <= x ==> csqrt(Cx x) = Cx(sqrt x)`,
  SIMP_TAC[CX_SQRT]);;

let CSQRT_0 = prove
 (`csqrt(Cx(&0)) = Cx(&0)`,
  SIMP_TAC[CSQRT_CX; REAL_POS; SQRT_0]);;

let CSQRT_1 = prove
 (`csqrt(Cx(&1)) = Cx(&1)`,
  SIMP_TAC[CSQRT_CX; REAL_POS; SQRT_1]);;

let CSQRT_PRINCIPAL = prove
 (`!z. &0 < Re(csqrt(z)) \/ Re(csqrt(z)) = &0 /\ &0 <= Im(csqrt(z))`,
  GEN_TAC THEN REWRITE_TAC[csqrt] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[RE; IM]) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SQRT_POS_LE) THEN REAL_ARITH_TAC;
    DISJ2_TAC THEN REWRITE_TAC[real_ge] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    DISJ1_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
    MATCH_MP_TAC(REAL_ARITH `abs(y) < x ==> &0 < (x + y) / &2`) THEN
    REWRITE_TAC[complex_norm] THEN REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE; REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    ASM_REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE]]);;

let RE_CSQRT = prove
 (`!z. &0 <= Re(csqrt z)`,
  MP_TAC CSQRT_PRINCIPAL THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let CSQRT_UNIQUE = prove
 (`!s z. s pow 2 = z /\ (&0 < Re s \/ Re s = &0 /\ &0 <= Im s)
         ==> csqrt z = s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MP_TAC(SPEC `(s:complex) pow 2` CSQRT) THEN
  SIMP_TAC[COMPLEX_RING `a pow 2 = b pow 2 <=> a = b \/ a = --b:complex`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[COMPLEX_RING `--z = z <=> z = Cx(&0)`] THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `Re`) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[RE_NEG; IM_NEG; COMPLEX_EQ; RE_CX; IM_CX] THEN
  MP_TAC(SPEC `(s:complex) pow 2` CSQRT_PRINCIPAL) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let POW_2_CSQRT = prove
 (`!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im(z) ==> csqrt(z pow 2) = z`,
  MESON_TAC[CSQRT_UNIQUE]);;

let CSQRT_EQ_0 = prove
 (`!z. csqrt z = Cx(&0) <=> z = Cx(&0)`,
  GEN_TAC THEN MP_TAC (SPEC `z:complex` CSQRT) THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* A few more complex-specific cases of vector notions.                      *)
(* ------------------------------------------------------------------------- *)

let DOT_COMPLEX_MUL_CNJ = prove
 (`!w z. w dot z = Re(w * cnj z)`,
  REWRITE_TAC[cnj; complex_mul; RE; IM] THEN
  REWRITE_TAC[DOT_2; RE_DEF; IM_DEF] THEN REAL_ARITH_TAC);;

let DOT_CNJ = prove
 (`!w z. cnj w dot cnj z = w dot z`,
  REWRITE_TAC[DOT_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[cnj; RE; IM] THEN REAL_ARITH_TAC);;

let LINEAR_COMPLEX_MUL = prove
 (`!c. linear (\x. c * x)`,
   REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING);;

let BILINEAR_COMPLEX_MUL = prove
 (`bilinear( * )`,
  REWRITE_TAC[bilinear; linear; COMPLEX_CMUL] THEN  CONV_TAC COMPLEX_RING);;

let LINEAR_CNJ = prove
 (`linear cnj`,
  REWRITE_TAC[linear; COMPLEX_CMUL; CNJ_ADD; CNJ_MUL; CNJ_CX]);;

let ORTHOGONAL_TRANSFORMATION_CNJ = prove
 (`orthogonal_transformation cnj`,
  REWRITE_TAC[orthogonal_transformation; LINEAR_CNJ; DOT_CNJ]);;

let LINEAR_COMPLEX_LMUL = prove
 (`!f:real^N->complex c. linear f ==> linear (\x. c * f x)`,
  SIMP_TAC[linear; COMPLEX_CMUL] THEN
  REPEAT STRIP_TAC THEN CONV_TAC COMPLEX_RING);;

let LINEAR_COMPLEX_RMUL = prove
 (`!f:real^N->complex c. linear f ==> linear (\x. f x * c)`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN REWRITE_TAC[LINEAR_COMPLEX_LMUL]);;

let COMPLEX_CAUCHY_SCHWARZ_EQ = prove
 (`!w z. (w dot z) pow 2 + ((ii * w) dot z) pow 2 =
          norm(w) pow 2 * norm(z) pow 2`,
  REWRITE_TAC[NORM_POW_2; DOT_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; complex_mul; RE; IM] THEN REAL_ARITH_TAC);;

let COMPLEX_BASIS = prove
 (`basis 1 = Cx(&1) /\ basis 2 = ii`,
  SIMP_TAC[CART_EQ; FORALL_2; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CX; IM_CX] THEN
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_LINEAR = prove
 (`!f:complex->complex.
        (?c. f = \z. c * z) <=>
        linear f /\
        (matrix f)$1$1 = (matrix f)$2$2 /\
        (matrix f)$1$2 = --((matrix f)$2$1)`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[LINEAR_COMPLEX_MUL] THEN
    SIMP_TAC[matrix; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[COMPLEX_BASIS; GSYM RE_DEF; GSYM IM_DEF; ii] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    STRIP_TAC THEN
    EXISTS_TAC `complex(matrix(f:complex->complex)$1$1,matrix f$2$1)` THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC LAND_CONV [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; DIMINDEX_2; SUM_2; ARITH;
                 FORALL_2; FUN_EQ_THM; LAMBDA_BETA] THEN
    REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; IM; RE; complex_mul] THEN
    REAL_ARITH_TAC]);;

let COMPLEX_LINEAR_ALT = prove
 (`!f:complex->complex.
        (?c. f = \z. c * z) <=> linear f /\ f(ii) = ii * f(Cx(&1))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LINEAR_COMPLEX_MUL] THENL
   [SIMPLE_COMPLEX_ARITH_TAC; ASM_REWRITE_TAC[COMPLEX_LINEAR]] THEN
  FIRST_ASSUM(MP_TAC o SYM) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
  REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_MUL_II; IM_MUL_II] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_COMPONENT; IM_DEF; RE_DEF] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH; DOT_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; CX_DEF; RE; IM; RE_II; IM_II] THEN
  REAL_ARITH_TAC);;

let ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL = prove                               
 (`!c. orthogonal_transformation(\z. c * z) <=> norm c = &1`,                   
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; LINEAR_COMPLEX_MUL] THEN              
  GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN                              
  REWRITE_TAC[REAL_RING `c * v:real = v <=> c = &1 \/ v = &0`] THEN            
  ASM_CASES_TAC `norm(c:complex) = &1` THEN ASM_REWRITE_TAC[] THEN             
  DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN    
  REAL_ARITH_TAC);;                                                            

let COMPLEX_ORTHOGONAL_ROTATION = prove                                         
 (`!f:complex->complex.                                                        
        orthogonal_transformation f /\ det(matrix f) = &1 <=>                  
        ?c. norm c = &1 /\ f = \z. c * z`,                                     
  GEN_TAC THEN TRANS_TAC EQ_TRANS                                              
   `(!z. norm(f z) = norm z) /\ (?c. f = \z:complex. c * z)` THEN               
  CONJ_TAC THENL                                                               
   [REWRITE_TAC[COMPLEX_LINEAR] THEN                                           
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> (q /\ p) /\ r`] THEN            
    REWRITE_TAC[GSYM ORTHOGONAL_TRANSFORMATION] THEN                       
    REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX] THEN                      
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN AP_TERM_TAC THEN                         
    REWRITE_TAC[ORTHOGONAL_MATRIX_2; DET_2] THEN CONV_TAC REAL_RING;           
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN                                     
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN                       
    X_GEN_TAC `c:complex` THEN REWRITE_TAC[] THEN                              
    ASM_CASES_TAC `f:complex->complex = \z. c * z` THEN                        
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL] THEN                                     
    REWRITE_TAC[REAL_RING `c * v:real = v <=> c = &1 \/ v = &0`] THEN          
    ASM_CASES_TAC `norm(c:complex) = &1` THEN ASM_REWRITE_TAC[] THEN           
    DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN  
    REAL_ARITH_TAC]);;                                                          
                                                                               
let COMPLEX_ORTHOGONAL_ROTOINVERSION = prove                                   
 (`!f:complex->complex.                                                        
        orthogonal_transformation f /\ det(matrix f) = -- &1 <=>               
        ?c. norm c = &1 /\ f = \z. c * cnj z`,                                 
  GEN_TAC THEN                                                                 
  SUBGOAL_THEN                                                             
   `!c. (f = \z. c * cnj z) = (f o cnj = \z. c * z)`                           
   (fun th -> REWRITE_TAC[th])                                                 
  THENL                                                                        
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[CNJ_CNJ; CNJ_MUL];
    REWRITE_TAC[GSYM COMPLEX_ORTHOGONAL_ROTATION]] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `(f:complex->complex) = (f o cnj) o cnj` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; CNJ_CNJ];
      POP_ASSUM MP_TAC THEN
      SPEC_TAC(`(f:complex->complex) o cnj`,`f:complex->complex`) THEN
      REPEAT STRIP_TAC]] THEN
  ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE; MATRIX_COMPOSE; DET_MUL;
    ORTHOGONAL_TRANSFORMATION_CNJ; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
  SIMP_TAC[DET_2; MATRIX_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[COMPLEX_BASIS; CNJ_II; CNJ_CX] THEN
  REWRITE_TAC[GSYM IM_DEF; GSYM RE_DEF; IM; RE; CX_DEF; ii; complex_neg] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let COMPLEX_ORTHOGONAL_TRANSFORMATION = prove
 (`!f:complex->complex.
        orthogonal_transformation f <=>
        ?c. norm c = &1 /\ ((f = \z. c * z) \/ (f = \z. c * cnj z))`,
  GEN_TAC THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; EXISTS_OR_THM] THEN
  REWRITE_TAC[GSYM COMPLEX_ORTHOGONAL_ROTATION;
              GSYM COMPLEX_ORTHOGONAL_ROTOINVERSION] THEN
  MESON_TAC[DET_ORTHOGONAL_MATRIX; ORTHOGONAL_TRANSFORMATION_MATRIX]);;
(* ------------------------------------------------------------------------- *)
(* Complex-specific theorems about sums.                                     *)
(* ------------------------------------------------------------------------- *)

let RE_VSUM = prove
 (`!f s. FINITE s ==> Re(vsum s f) = sum s (\x. Re(f x))`,
  SIMP_TAC[RE_DEF; VSUM_COMPONENT; DIMINDEX_2; ARITH]);;

let IM_VSUM = prove
 (`!f s. FINITE s ==> Im(vsum s f) = sum s (\x. Im(f x))`,
  SIMP_TAC[IM_DEF; VSUM_COMPONENT; DIMINDEX_2; ARITH]);;

let VSUM_COMPLEX_LMUL = prove
 (`!c f s. FINITE(s) ==> vsum s (\x. c * f x) = c * vsum s f`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let VSUM_COMPLEX_RMUL = prove
 (`!c f s. FINITE(s) ==> vsum s (\x. f x * c) = vsum s f * c`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN REWRITE_TAC[VSUM_COMPLEX_LMUL]);;

let VSUM_CX = prove
 (`!f:A->real s. vsum s (\a. Cx(f a)) = Cx(sum s f)`,
  SIMP_TAC[CART_EQ; VSUM_COMPONENT] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[IM_CX; SUM_0; RE_CX; ETA_AX]);;

let CNJ_VSUM = prove
 (`!f s. FINITE s ==> cnj(vsum s f) = vsum s (\x. cnj(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; CNJ_ADD; CNJ_CX; COMPLEX_VEC_0]);;

let VSUM_CX_NUMSEG = prove
 (`!f m n. vsum (m..n) (\a. Cx(f a)) = Cx(sum (m..n) f)`,
  SIMP_TAC[VSUM_CX; FINITE_NUMSEG]);;

let COMPLEX_SUB_POW = prove
 (`!x y n.
        1 <= n ==> x pow n - y pow n =
                   (x - y) * vsum(0..n-1) (\i. x pow i * y pow (n - 1 - i))`,
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_RING
   `(x - y) * (a * b):complex = (x * a) * b - a * (y * b)`] THEN
  SIMP_TAC[GSYM complex_pow; ADD1; ARITH_RULE
    `1 <= n /\ x <= n - 1
     ==> n - 1 - x = n - (x + 1) /\ SUC(n - 1 - x) = n - x`] THEN
  REWRITE_TAC[VSUM_DIFFS_ALT; LE_0] THEN
  SIMP_TAC[SUB_0; SUB_ADD; SUB_REFL;
           complex_pow; COMPLEX_MUL_LID; COMPLEX_MUL_RID]);;

let COMPLEX_SUB_POW_R1 = prove
 (`!x n. 1 <= n
         ==> x pow n - Cx(&1) = (x - Cx(&1)) * vsum(0..n-1) (\i. x pow i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`x:complex`; `Cx(&1)`] o
    MATCH_MP COMPLEX_SUB_POW) THEN
  REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_RID]);;

let COMPLEX_SUB_POW_L1 = prove
 (`!x n. 1 <= n
         ==> Cx(&1) - x pow n = (Cx(&1) - x) * vsum(0..n-1) (\i. x pow i)`,
  ONCE_REWRITE_TAC[GSYM COMPLEX_NEG_SUB] THEN
  SIMP_TAC[COMPLEX_SUB_POW_R1] THEN REWRITE_TAC[COMPLEX_MUL_LNEG]);;

(* ------------------------------------------------------------------------- *)
(* The complex numbers that are real (zero imaginary part).                  *)
(* ------------------------------------------------------------------------- *)

let real = new_definition
 `real z <=> Im z = &0`;;

let REAL = prove
 (`!z. real z <=> Cx(Re z) = z`,
  REWRITE_TAC[COMPLEX_EQ; real; CX_DEF; RE; IM] THEN REAL_ARITH_TAC);;

let REAL_CNJ = prove
 (`!z. real z <=> cnj z = z`,
  REWRITE_TAC[real; cnj; COMPLEX_EQ; RE; IM] THEN REAL_ARITH_TAC);;

let REAL_IMP_CNJ = prove
 (`!z. real z ==> cnj z = z`,
  REWRITE_TAC[REAL_CNJ]);;

let REAL_EXISTS = prove
 (`!z. real z <=> ?x. z = Cx x`,
  MESON_TAC[REAL; real; IM_CX]);;

let FORALL_REAL = prove
 (`(!z. real z ==> P z) <=> (!x. P(Cx x))`,
  MESON_TAC[REAL_EXISTS]);;

let EXISTS_REAL = prove
 (`(?z. real z /\ P z) <=> (?x. P(Cx x))`,
  MESON_TAC[REAL_EXISTS]);;

let REAL_CX = prove
 (`!x. real(Cx x)`,
  REWRITE_TAC[REAL_CNJ; CNJ_CX]);;

let REAL_MUL_CX = prove
 (`!x z. real(Cx x * z) <=> x = &0 \/ real z`,
  REWRITE_TAC[real; IM_MUL_CX; REAL_ENTIRE]);;

let REAL_ADD = prove
 (`!w z. real w /\ real z ==> real(w + z)`,
  SIMP_TAC[REAL_CNJ; CNJ_ADD]);;

let REAL_NEG = prove
 (`!z. real z ==> real(--z)`,
  SIMP_TAC[REAL_CNJ; CNJ_NEG]);;

let REAL_SUB = prove
 (`!w z. real w /\ real z ==> real(w - z)`,
  SIMP_TAC[REAL_CNJ; CNJ_SUB]);;

let REAL_MUL = prove
 (`!w z. real w /\ real z ==> real(w * z)`,
  SIMP_TAC[REAL_CNJ; CNJ_MUL]);;

let REAL_POW = prove
 (`!z n. real z ==> real(z pow n)`,
  SIMP_TAC[REAL_CNJ; CNJ_POW]);;

let REAL_INV = prove
 (`!z. real z ==> real(inv z)`,
  SIMP_TAC[REAL_CNJ; CNJ_INV]);;

let REAL_INV_EQ = prove
 (`!z. real(inv z) = real z`,
  MESON_TAC[REAL_INV; COMPLEX_INV_INV]);;

let REAL_DIV = prove
 (`!w z. real w /\ real z ==> real(w / z)`,
  SIMP_TAC[REAL_CNJ; CNJ_DIV]);;

let REAL_VSUM = prove
 (`!f s. FINITE s /\ (!a. a IN s ==> real(f a)) ==> real(vsum s f)`,
  SIMP_TAC[CNJ_VSUM; REAL_CNJ]);;

let REAL_MUL_CNJ = prove
 (`(!z. real(z * cnj z)) /\ (!z. real(cnj z * z))`,
  REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; REAL_CX]);;

let REAL_SEGMENT = prove
 (`!a b x. x IN segment[a,b] /\ real a /\ real b ==> real x`,
  SIMP_TAC[segment; IN_ELIM_THM; real; COMPLEX_EQ; LEFT_AND_EXISTS_THM;
           LEFT_IMP_EXISTS_THM; IM_ADD; IM_CMUL] THEN
  REAL_ARITH_TAC);;

let IN_SEGMENT_CX = prove
 (`!a b x. Cx(x) IN segment[Cx(a),Cx(b)] <=>
                a <= x /\ x <= b \/ b <= x /\ x <= a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[segment; IN_ELIM_THM] THEN
  REWRITE_TAC[COMPLEX_CMUL; GSYM CX_ADD; CX_INJ; GSYM CX_MUL] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[REAL_ARITH `(&1 - u) * b + u * b = b`] THEN
    ASM_CASES_TAC `x:real = b` THEN ASM_REWRITE_TAC[REAL_LE_ANTISYM] THEN
    EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[REAL_ARITH `a <= (&1 - u) * a + u * b <=> &0 <= u * (b - a)`;
      REAL_ARITH `b <= (&1 - u) * a + u * b <=> &0 <= (&1 - u) * (a - b)`;
      REAL_ARITH `(&1 - u) * a + u * b <= a <=> &0 <= u * (a - b)`;
      REAL_ARITH `(&1 - u) * a + u * b <= b <=> &0 <= (&1 - u) * (b - a)`] THEN
    DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b <= a`) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXISTS_TAC `(x - a:real) / (b - a)`];
    SUBGOAL_THEN `&0 < a - b` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXISTS_TAC `(a - x:real) / (a - b)`]] THEN
  (CONJ_TAC THENL
    [ALL_TAC; UNDISCH_TAC `~(a:real = b)` THEN CONV_TAC REAL_FIELD]) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let IN_SEGMENT_CX_GEN = prove
 (`!a b x.
        x IN segment[Cx a,Cx b] <=>
        Im(x) = &0 /\ (a <= Re x /\ Re x <= b \/ b <= Re x /\ Re x <= a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM real] THEN
  ASM_CASES_TAC `real x` THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o REWRITE_RULE[REAL]) THEN
    REWRITE_TAC[IN_SEGMENT_CX; REAL_CX; RE_CX] THEN REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_SEGMENT; REAL_CX]]);;

let RE_POS_SEGMENT = prove
 (`!a b x. x IN segment[a,b] /\ &0 < Re a /\ &0 < Re b ==> &0 < Re x`,
  SIMP_TAC[segment; IN_ELIM_THM; real; COMPLEX_EQ; LEFT_AND_EXISTS_THM;
           LEFT_IMP_EXISTS_THM; RE_ADD; RE_CMUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
    `&0 <= x /\ &0 <= y /\ ~(x = &0 /\ y = &0) ==> &0 < x + y`) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_LT_IMP_LE; REAL_ENTIRE] THEN
  ASM_REAL_ARITH_TAC);;

let CONVEX_REAL = prove
 (`convex real`,
  REWRITE_TAC[convex; IN; COMPLEX_CMUL] THEN
  SIMP_TAC[REAL_ADD; REAL_MUL; REAL_CX]);;

let IMAGE_CX = prove
 (`!s. IMAGE Cx s = {z | real z /\ Re(z) IN s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[RE_CX; REAL]);;

let SUBSPACE_REAL = prove
 (`subspace real`,
  REWRITE_TAC[subspace] THEN
  SIMP_TAC[COMPLEX_CMUL; COMPLEX_VEC_0; IN; REAL_CX; REAL_ADD; REAL_MUL]);;

let DIM_REAL = prove
 (`dim real = 1`,
  ONCE_REWRITE_TAC[SET_RULE `real = {x | real x}`] THEN
  SIMP_TAC[real; IM_DEF; DIM_SPECIAL_HYPERPLANE; DIMINDEX_2; ARITH]);;

let INTERIOR_REAL = prove
 (`interior real = {}`,
  MATCH_MP_TAC EMPTY_INTERIOR_LOWDIM THEN
  REWRITE_TAC[DIM_REAL; DIMINDEX_2; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Useful bound-type theorems for real quantities.                           *)
(* ------------------------------------------------------------------------- *)

let REAL_NORM = prove
 (`!z. real z ==> norm(z) = abs(Re z)`,
  SIMP_TAC[real; complex_norm] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[POW_2_SQRT_ABS; REAL_ADD_RID]);;

let REAL_NORM_POS = prove
 (`!z. real z /\ &0 <= Re z ==> norm(z) = Re(z)`,
  SIMP_TAC[REAL_NORM] THEN REAL_ARITH_TAC);;

let COMPLEX_NORM_VSUM_SUM_RE = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> real(f x) /\ &0 <= Re(f x))
         ==> norm(vsum s f) = sum s (\x. Re(f x))`,
  SIMP_TAC[GSYM RE_VSUM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_NORM_POS THEN
  ASM_SIMP_TAC[REAL_VSUM; RE_VSUM; SUM_POS_LE]);;

let COMPLEX_NORM_VSUM_BOUND = prove
 (`!s f:A->complex g:A->complex.
        FINITE s /\ (!x. x IN s ==> real(g x) /\ norm(f x) <= Re(g x))
        ==> norm(vsum s f) <= norm(vsum s g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x. norm((f:A->complex) x))` THEN
  ASM_SIMP_TAC[VSUM_NORM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x. Re((g:A->complex) x))` THEN
  ASM_SIMP_TAC[SUM_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `x:real = y ==> y <= x`) THEN
  MATCH_MP_TAC COMPLEX_NORM_VSUM_SUM_RE THEN
  ASM_MESON_TAC[REAL_LE_TRANS; NORM_POS_LE]);;

let COMPLEX_NORM_VSUM_BOUND_SUBSET = prove
 (`!f:A->complex g:A->complex s t.
        FINITE s /\ t SUBSET s /\
        (!x. x IN s ==> real(g x) /\ norm(f x) <= Re(g x))
        ==> norm(vsum t f) <= norm(vsum s g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vsum t (g:A->complex))` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COMPLEX_NORM_VSUM_BOUND; SUBSET; FINITE_SUBSET];ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vsum t (g:A->complex)) = sum t (\x. Re(g x)) /\
    norm(vsum s g) = sum s (\x. Re(g x))`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPLEX_NORM_VSUM_SUM_RE;
    MATCH_MP_TAC SUM_SUBSET THEN REWRITE_TAC[IN_DIFF]] THEN
  ASM_MESON_TAC[REAL_LE_TRANS; NORM_POS_LE; FINITE_SUBSET; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Geometric progression.                                                    *)
(* ------------------------------------------------------------------------- *)

let VSUM_GP_BASIC = prove
 (`!x n. (Cx(&1) - x) * vsum(0..n) (\i. x pow i) = Cx(&1) - x pow (SUC n)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[complex_pow; COMPLEX_MUL_RID; LE_0] THEN
  ASM_REWRITE_TAC[COMPLEX_ADD_LDISTRIB; complex_pow] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let VSUM_GP_MULTIPLIED = prove
 (`!x m n. m <= n
           ==> ((Cx(&1) - x) * vsum(m..n) (\i. x pow i) =
                x pow m - x pow (SUC n))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VSUM_OFFSET_0; COMPLEX_POW_ADD; FINITE_NUMSEG;
               COMPLEX_MUL_ASSOC; VSUM_GP_BASIC; VSUM_COMPLEX_RMUL] THEN
  REWRITE_TAC[COMPLEX_SUB_RDISTRIB; GSYM COMPLEX_POW_ADD; COMPLEX_MUL_LID] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> (SUC(n - m) + m = SUC n)`]);;

let VSUM_GP = prove
 (`!x m n.
        vsum(m..n) (\i. x pow i) =
                if n < m then Cx(&0)
                else if x = Cx(&1) then Cx(&((n + 1) - m))
                else (x pow m - x pow (SUC n)) / (Cx(&1) - x)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `n < m \/ ~(n < m) /\ m <= n:num`) THEN
  ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; COMPLEX_VEC_0] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_POW_ONE; VSUM_CONST_NUMSEG; COMPLEX_MUL_RID];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `~(z = Cx(&1)) /\ (Cx(&1) - z) * x = y ==> x = y / (Cx(&1) - z)`) THEN
  ASM_SIMP_TAC[COMPLEX_DIV_LMUL; COMPLEX_SUB_0; VSUM_GP_MULTIPLIED]);;

let VSUM_GP_OFFSET = prove
 (`!x m n. vsum(m..m+n) (\i. x pow i) =
                if x = Cx(&1) then Cx(&n) + Cx(&1)
                else x pow m * (Cx(&1) - x pow (SUC n)) / (Cx(&1) - x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VSUM_GP; ARITH_RULE `~(m + n < m:num)`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; GSYM CX_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[complex_div; complex_pow; COMPLEX_POW_ADD] THEN
    SIMPLE_COMPLEX_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Basics about polynomial functions: extremal behaviour and root counts.    *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_SUB_POLYFUN = prove
 (`!a x y n.
   1 <= n
   ==> vsum(0..n) (\i. a i * x pow i) - vsum(0..n) (\i. a i * y pow i) =
       (x - y) *
       vsum(0..n-1) (\j. vsum(j+1..n) (\i. a i * y pow (i - j - 1)) * x pow j)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VSUM_SUB_NUMSEG; GSYM COMPLEX_SUB_LDISTRIB] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP VSUM_CLAUSES_LEFT (SPEC_ALL LE_0)] THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; complex_pow; COMPLEX_MUL_RZERO;
      COMPLEX_ADD_LID] THEN
  SIMP_TAC[COMPLEX_SUB_POW; ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `a * x * s:complex = x * a * s`] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG;
           VSUM_VSUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
  REPEAT(EXISTS_TAC `\(x:num,y:num). (y,x)`) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `a - b - c:num = a - (b + c)`; ADD_SYM] THEN
  REWRITE_TAC[COMPLEX_MUL_AC] THEN ARITH_TAC);;

let COMPLEX_SUB_POLYFUN_ALT = prove
 (`!a x y n.
    1 <= n
    ==> vsum(0..n) (\i. a i * x pow i) - vsum(0..n) (\i. a i * y pow i) =
        (x - y) *
        vsum(0..n-1) (\j. vsum(0..n-j-1) (\k. a(j+k+1) * y pow k) * x pow j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_SUB_POLYFUN] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC
   [`\i. i - (j + 1)`; `\k. j + k + 1`] THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  TRY(BINOP_TAC THEN AP_TERM_TAC) THEN ASM_ARITH_TAC);;

let COMPLEX_POLYFUN_LINEAR_FACTOR = prove
 (`!a c n. ?b. !z. vsum(0..n) (\i. c(i) * z pow i) =
                   (z - a) * vsum(0..n-1) (\i. b(i) * z pow i) +
                    vsum(0..n) (\i. c(i) * a pow i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_EQ_SUB_RADD] THEN
  ASM_CASES_TAC `n = 0` THENL
   [EXISTS_TAC `\i:num. Cx(&0)` THEN
    ASM_SIMP_TAC[VSUM_SING; NUMSEG_SING; complex_pow; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; GSYM COMPLEX_VEC_0; VSUM_0] THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO];
    ASM_SIMP_TAC[COMPLEX_SUB_POLYFUN; LE_1] THEN
    EXISTS_TAC `\j. vsum (j + 1..n) (\i. c i * a pow (i - j - 1))` THEN
    REWRITE_TAC[]]);;

let COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT = prove
 (`!a c n. vsum(0..n) (\i. c(i) * a pow i) = Cx(&0)
           ==> ?b. !z. vsum(0..n) (\i. c(i) * z pow i) =
                      (z - a) * vsum(0..n-1) (\i. b(i) * z pow i)`,
  MESON_TAC[COMPLEX_POLYFUN_LINEAR_FACTOR; COMPLEX_ADD_RID]);;

let COMPLEX_POLYFUN_EXTREMAL_LEMMA = prove
 (`!c n e. &0 < e
           ==> ?M. !z. M <= norm(z)
                       ==> norm(vsum(0..n) (\i. c(i) * z pow i))
                               <= e * norm(z) pow (n + 1)`,
  GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; complex_pow; REAL_POW_1; COMPLEX_MUL_RID] THEN
    EXISTS_TAC `norm(c 0:complex) / e` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (REAL_ARITH `&0 < &1 / &2`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  EXISTS_TAC `max M ((&1 / &2 + norm(c(n+1):complex)) / e)` THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[REAL_MAX_LE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `a + norm(y) <= b ==> norm(x) <= a ==> norm(x + y) <= b`) THEN
  SIMP_TAC[ADD1; COMPLEX_NORM_MUL; COMPLEX_NORM_POW;
           GSYM REAL_ADD_RDISTRIB; ARITH_RULE `(n + 1) + 1 = 1 + n + 1`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_POW_ADD] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_POW_LE; NORM_POS_LE; REAL_POW_1]);;

let COMPLEX_POLYFUN_EXTREMAL = prove
 (`!c n. (!k. k IN 1..n ==> c(k) = Cx(&0)) \/
         !B. eventually (\z. norm(vsum(0..n) (\i. c(i) * z pow i)) >= B)
                        at_infinity`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[NUMSEG_CLAUSES; ARITH; NOT_IN_EMPTY] THEN
  MP_TAC(ARITH_RULE `0 <= n`) THEN SIMP_TAC[GSYM NUMSEG_RREC] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_CASES_TAC `c(n:num) = Cx(&0)` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM NUMSEG_RREC; LE_1] THEN
    SIMP_TAC[IN_INSERT; VSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID; COND_ID] THEN
    ASM_MESON_TAC[];
    DISJ2_TAC THEN MP_TAC(ISPECL
      [`c:num->complex`; `n - 1`; `norm(c(n:num):complex) / &2`]
      COMPLEX_POLYFUN_EXTREMAL_LEMMA) THEN ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_NZ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    SIMP_TAC[IN_INSERT; VSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> ~(n <= n - 1)`] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN X_GEN_TAC `B:real` THEN
    REWRITE_TAC[EVENTUALLY_AT_INFINITY] THEN EXISTS_TAC
     `max M (max (&1) ((abs B + &1) / (norm(c(n:num):complex) / &2)))` THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_ge; REAL_MAX_LE] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
     `abs b + &1 <= norm(y) - a ==> norm(x) <= a ==> b <= norm(y + x)`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
    REWRITE_TAC[REAL_ARITH `c * x - c / &2 * x = x * c / &2`] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; COMPLEX_NORM_NZ; REAL_LT_DIV;
                 REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(z:complex) pow 1` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_POW_1]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_SIMP_TAC[LE_1]]);;

let COMPLEX_POLYFUN_ROOTBOUND = prove
 (`!n c. ~(!i. i IN 0..n ==> c(i) = Cx(&0))
         ==> FINITE {z | vsum(0..n) (\i. c(i) * z pow i) = Cx(&0)} /\
             CARD {z | vsum(0..n) (\i. c(i) * z pow i) = Cx(&0)} <= n`,
  REWRITE_TAC[TAUT `~a ==> b <=> a \/ b`] THEN INDUCT_TAC THEN GEN_TAC THENL
   [SIMP_TAC[NUMSEG_SING; VSUM_SING; IN_SING; complex_pow] THEN
    ASM_CASES_TAC `c 0 = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_MUL_RID] THEN
    REWRITE_TAC[EMPTY_GSPEC; FINITE_RULES; CARD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `{z | vsum(0..SUC n) (\i. c(i) * z pow i) = Cx(&0)} = {}` THEN
  ASM_REWRITE_TAC[FINITE_RULES; CARD_CLAUSES; LE_0] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:complex` MP_TAC o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT) THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num->complex`) THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_SUB_0; SUC_SUB1; SET_RULE
   `{z | z = a \/ P z} = a INSERT {z | P z}`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:num->complex`) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THENL
   [DISJ1_TAC; ASM_ARITH_TAC] THEN
  MP_TAC(SPECL [`c:num->complex`; `SUC n`] COMPLEX_POLYFUN_EXTREMAL) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
  ASM_SIMP_TAC[SUC_SUB1; COMPLEX_MUL_LZERO] THEN
  SIMP_TAC[COMPLEX_POW_ZERO; COND_RAND; COMPLEX_MUL_RZERO] THEN
  ASM_SIMP_TAC[VSUM_0; GSYM COMPLEX_VEC_0; VSUM_DELTA; IN_NUMSEG; LE_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO; COMPLEX_NORM_NUM] THEN
  REWRITE_TAC[COMPLEX_MUL_RID; real_ge; EVENTUALLY_AT_INFINITY] THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[LE_1]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM] THEN X_GEN_TAC `b:real` THEN
  MP_TAC(SPEC `b:real` (INST_TYPE [`:2`,`:N`] VECTOR_CHOOSE_SIZE)) THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TOTAL; REAL_LE_TRANS]);;

let COMPLEX_POLYFUN_FINITE_ROOTS = prove
 (`!n c. FINITE {x | vsum(0..n) (\i. c i * x pow i) = Cx(&0)} <=>
         ?i. i IN 0..n /\ ~(c i = Cx(&0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAUT `a /\ ~b <=> ~(a ==> b)`] THEN
  REWRITE_TAC[GSYM NOT_FORALL_THM] THEN EQ_TAC THEN
  SIMP_TAC[COMPLEX_POLYFUN_ROOTBOUND] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[COMPLEX_MUL_LZERO] THEN SIMP_TAC[GSYM COMPLEX_VEC_0; VSUM_0] THEN
  REWRITE_TAC[SET_RULE `{x | T} = (:complex)`; GSYM INFINITE;
              EUCLIDEAN_SPACE_INFINITE]);;

let COMPLEX_POLYFUN_EQ_0 = prove
 (`!n c. (!z. vsum(0..n) (\i. c i * z pow i) = Cx(&0)) <=>
         (!i. i IN 0..n ==> c i = Cx(&0))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_THEN(MP_TAC o MATCH_MP
     COMPLEX_POLYFUN_ROOTBOUND) THEN
    ASM_REWRITE_TAC[EUCLIDEAN_SPACE_INFINITE; GSYM INFINITE; DE_MORGAN_THM;
                    SET_RULE `{x | T} = (:complex)`];
    ASM_SIMP_TAC[IN_NUMSEG; LE_0; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0]]);;

let COMPLEX_POLYFUN_EQ_CONST = prove
 (`!n c k. (!z. vsum(0..n) (\i. c i * z pow i) = k) <=>
           c 0 = k /\ (!i. i IN 1..n ==> c i = Cx(&0))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `!x. vsum(0..n) (\i. (if i = 0 then c 0 - k else c i) * x pow i) =
        Cx(&0)` THEN
  CONJ_TAC THENL
   [SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; complex_pow; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[COMPLEX_RING `(c - k) + s = Cx(&0) <=> c + s = k`] THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH];
    REWRITE_TAC[COMPLEX_POLYFUN_EQ_0; IN_NUMSEG; LE_0] THEN
    GEN_REWRITE_TAC LAND_CONV [MESON[]
     `(!n. P n) <=> P 0 /\ (!n. ~(n = 0) ==> P n)`] THEN
    SIMP_TAC[LE_0; COMPLEX_SUB_0] THEN MESON_TAC[LE_1]]);;

(* ------------------------------------------------------------------------- *)
(* Complex products.                                                         *)
(* ------------------------------------------------------------------------- *)

let cproduct = new_definition
  `cproduct = iterate (( * ):complex->complex->complex)`;;

let NEUTRAL_COMPLEX_MUL = prove
 (`neutral(( * ):complex->complex->complex) = Cx(&1)`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_RID]);;

let MONOIDAL_COMPLEX_MUL = prove
 (`monoidal(( * ):complex->complex->complex)`,
  REWRITE_TAC[monoidal; NEUTRAL_COMPLEX_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let CPRODUCT_CLAUSES = prove
 (`(!f. cproduct {} f = Cx(&1)) /\
   (!x f s. FINITE(s)
            ==> (cproduct (x INSERT s) f =
                 if x IN s then cproduct s f else f(x) * cproduct s f))`,
  REWRITE_TAC[cproduct; GSYM NEUTRAL_COMPLEX_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_COMPLEX_MUL]);;

let CPRODUCT_EQ_0 = prove
 (`!f s. FINITE s ==> (cproduct s f = Cx(&0) <=> ?x. x IN s /\ f(x) = Cx(&0))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; COMPLEX_ENTIRE; IN_INSERT; CX_INJ; REAL_OF_NUM_EQ;
           ARITH; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let CPRODUCT_INV = prove
 (`!f s. FINITE s ==> cproduct s (\x. inv(f x)) = inv(cproduct s f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; COMPLEX_INV_1; COMPLEX_INV_MUL]);;

let CPRODUCT_MUL = prove
 (`!f g s. FINITE s
           ==> cproduct s (\x. f x * g x) = cproduct s f * cproduct s g`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; COMPLEX_MUL_AC; COMPLEX_MUL_LID]);;

let CPRODUCT_EQ_1 = prove
 (`!f s. (!x:A. x IN s ==> (f(x) = Cx(&1))) ==> (cproduct s f = Cx(&1))`,
  REWRITE_TAC[cproduct; GSYM NEUTRAL_COMPLEX_MUL] THEN
  SIMP_TAC[ITERATE_EQ_NEUTRAL; MONOIDAL_COMPLEX_MUL]);;

let CPRODUCT_1 = prove
 (`!s. cproduct s (\n. Cx(&1)) = Cx(&1)`,
  SIMP_TAC[CPRODUCT_EQ_1]);;

let CPRODUCT_POW = prove
 (`!f s n. FINITE s
           ==> cproduct s (\x. f x pow n) = (cproduct s f) pow n`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[complex_pow; CPRODUCT_MUL; CPRODUCT_1]);;

let NORM_CPRODUCT = prove
 (`!f s. FINITE s ==> norm(cproduct s f) = product s (\x. norm(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; COMPLEX_NORM_CX; REAL_ABS_NUM;
           CPRODUCT_MUL; PRODUCT_CLAUSES; COMPLEX_NORM_MUL]);;

let CPRODUCT_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> cproduct s f = cproduct s g`,
  REWRITE_TAC[cproduct] THEN MATCH_MP_TAC ITERATE_EQ THEN
  REWRITE_TAC[MONOIDAL_COMPLEX_MUL]);;

let CPRODUCT_SING = prove
 (`!f x. cproduct {x} f = f(x)`,
  SIMP_TAC[CPRODUCT_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; COMPLEX_MUL_RID]);;

let CPRODUCT_CLAUSES_NUMSEG = prove
 (`(!m. cproduct(m..0) f = if m = 0 then f(0) else Cx(&1)) /\
   (!m n. cproduct(m..SUC n) f = if m <= SUC n then cproduct(m..n) f * f(SUC n)
                                 else cproduct(m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[CPRODUCT_SING; CPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; COMPLEX_MUL_AC]);;

let CPRODUCT_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> cproduct(m..n) f = cproduct(m..n-1) f * (f n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; CPRODUCT_CLAUSES_NUMSEG; SUC_SUB1]);;

let CPRODUCT_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> cproduct(m..n) f = f m * cproduct(m + 1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; CPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let CPRODUCT_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ f x = f y ==> (x = y))
           ==> (cproduct (IMAGE f s) g = cproduct s (g o f))`,
  REWRITE_TAC[cproduct; GSYM NEUTRAL_COMPLEX_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_COMPLEX_MUL]);;

let CPRODUCT_OFFSET = prove
 (`!f m p. cproduct(m+p..n+p) f = cproduct(m..n) (\i. f(i + p))`,
  SIMP_TAC[NUMSEG_OFFSET_IMAGE; CPRODUCT_IMAGE;
           EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF]);;

let CPRODUCT_CONST = prove
 (`!c s. FINITE s ==> cproduct s (\x. c) = c pow (CARD s)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; CARD_CLAUSES; complex_pow]);;

let CPRODUCT_CONST_NUMSEG = prove
 (`!c m n. cproduct (m..n) (\x. c) = c pow ((n + 1) - m)`,
  SIMP_TAC[CPRODUCT_CONST; CARD_NUMSEG; FINITE_NUMSEG]);;

let CPRODUCT_PAIR = prove
 (`!f m n. cproduct(2*m..2*n+1) f = cproduct(m..n) (\i. f(2*i) * f(2*i+1))`,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_COMPLEX_MUL) THEN
  REWRITE_TAC[cproduct; NEUTRAL_COMPLEX_MUL]);;

let CPRODUCT_REFLECT = prove
 (`!x m n. cproduct(m..n) x =
           if n < m then Cx(&1) else cproduct(0..n-m) (\i. x(n - i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cproduct] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP ITERATE_REFLECT MONOIDAL_COMPLEX_MUL] THEN
  REWRITE_TAC[NEUTRAL_COMPLEX_MUL]);;

let CNJ_CPRODUCT = prove
 (`!f s. FINITE s ==> cnj(cproduct s f) = cproduct s (\i. cnj(f i))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; CNJ_MUL; CNJ_CX]);;

let CX_PRODUCT = prove
 (`!f s. FINITE s ==> Cx(product s f) = cproduct s (\i. Cx(f i))`,
  GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; PRODUCT_CLAUSES; GSYM CX_MUL]);;

let th = prove
 (`(!f g s.   (!x. x IN s ==> f(x) = g(x))
              ==> cproduct s (\i. f(i)) = cproduct s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> cproduct(a..b) (\i. f(i)) = cproduct(a..b) g) /\
   (!f g p.   (!x. p x ==> f x = g x)
              ==> cproduct {y | p y} (\i. f(i)) = cproduct {y | p y} g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
  extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;
