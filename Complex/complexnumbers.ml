(* ========================================================================= *)
(* Basic definitions and properties of complex numbers.                      *)
(* ========================================================================= *)

needs "Library/transc.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Definition of complex number type.                                        *)
(* ------------------------------------------------------------------------- *)

let complex_tybij_raw =
  new_type_definition "complex" ("complex","coords")
   (prove(`?x:real#real. T`,REWRITE_TAC[]));;

let complex_tybij = REWRITE_RULE [] complex_tybij_raw;;

(* ------------------------------------------------------------------------- *)
(* Real and imaginary parts of a number.                                     *)
(* ------------------------------------------------------------------------- *)

let RE_DEF = new_definition
  `Re(z) = FST(coords(z))`;;

let IM_DEF = new_definition
  `Im(z) = SND(coords(z))`;;

(* ------------------------------------------------------------------------- *)
(* Set up overloading.                                                       *)
(* ------------------------------------------------------------------------- *)

do_list overload_interface
 ["+",`complex_add:complex->complex->complex`;
  "-",`complex_sub:complex->complex->complex`;
  "*",`complex_mul:complex->complex->complex`;
  "/",`complex_div:complex->complex->complex`;
  "--",`complex_neg:complex->complex`;
  "pow",`complex_pow:complex->num->complex`;
  "inv",`complex_inv:complex->complex`];;

let prioritize_complex() = prioritize_overload(mk_type("complex",[]));;

(* ------------------------------------------------------------------------- *)
(* Complex absolute value (modulus).                                         *)
(* ------------------------------------------------------------------------- *)

make_overloadable "norm" `:A->real`;;
overload_interface("norm",`complex_norm:complex->real`);;

let complex_norm = new_definition
  `norm(z) = sqrt(Re(z) pow 2 + Im(z) pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Imaginary unit (too inconvenient to use "i"!)                             *)
(* ------------------------------------------------------------------------- *)

let ii = new_definition
  `ii = complex(&0,&1)`;;

(* ------------------------------------------------------------------------- *)
(* Injection from reals.                                                     *)
(* ------------------------------------------------------------------------- *)

let CX_DEF = new_definition
  `Cx(a) = complex(a,&0)`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations.                                                    *)
(* ------------------------------------------------------------------------- *)

let complex_neg = new_definition
  `--z = complex(--(Re(z)),--(Im(z)))`;;

let complex_add = new_definition
  `w + z = complex(Re(w) + Re(z),Im(w) + Im(z))`;;

let complex_sub = new_definition
  `w - z = w + --z`;;

let complex_mul = new_definition
  `w * z = complex(Re(w) * Re(z) - Im(w) * Im(z),
                   Re(w) * Im(z) + Im(w) * Re(z))`;;

let complex_inv = new_definition
  `inv(z) = complex(Re(z) / (Re(z) pow 2 + Im(z) pow 2),
                    --(Im(z)) / (Re(z) pow 2 + Im(z) pow 2))`;;

let complex_div = new_definition
  `w / z = w * inv(z)`;;

let complex_pow = new_recursive_definition num_RECURSION
  `(x pow 0 = Cx(&1)) /\
   (!n. x pow (SUC n) = x * x pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Various handy rewrites.                                                   *)
(* ------------------------------------------------------------------------- *)

let RE = prove
 (`(Re(complex(x,y)) = x)`,
  REWRITE_TAC[RE_DEF; complex_tybij]);;

let IM = prove
 (`Im(complex(x,y)) = y`,
  REWRITE_TAC[IM_DEF; complex_tybij]);;

let COMPLEX = prove
 (`complex(Re(z),Im(z)) = z`,
  REWRITE_TAC[IM_DEF; RE_DEF; complex_tybij]);;

let COMPLEX_EQ = prove
 (`!w z. (w = z) <=> (Re(w) = Re(z)) /\ (Im(w) = Im(z))`,
  REWRITE_TAC[RE_DEF; IM_DEF; GSYM PAIR_EQ] THEN MESON_TAC[complex_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Crude tactic to automate very simple algebraic equivalences.              *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_COMPLEX_ARITH_TAC =
  REWRITE_TAC[COMPLEX_EQ; RE; IM; CX_DEF;
              complex_add; complex_neg; complex_sub; complex_mul] THEN
  REAL_ARITH_TAC;;

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
 (`!x. &2 * x = x + x`,
  SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Homomorphic embedding properties for Cx mapping.                          *)
(* ------------------------------------------------------------------------- *)

let CX_INJ = prove
 (`!x y. (Cx(x) = Cx(y)) <=> (x = y)`,
  REWRITE_TAC[CX_DEF; COMPLEX_EQ; RE; IM]);;

let CX_NEG = prove
 (`!x. Cx(--x) = --(Cx(x))`,
  REWRITE_TAC[CX_DEF; complex_neg; RE; IM; REAL_NEG_0]);;

let CX_INV = prove
 (`!x. Cx(inv x) = inv(Cx x)`,
  GEN_TAC THEN
  REWRITE_TAC[CX_DEF; complex_inv; RE; IM] THEN
  REWRITE_TAC[real_div; REAL_NEG_0; REAL_MUL_LZERO] THEN
  REWRITE_TAC[COMPLEX_EQ; REAL_POW_2; REAL_MUL_RZERO; RE; IM] THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_INV_MUL] THEN
  ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_INV_0; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[REAL_MUL_RINV]);;

let CX_ADD = prove
 (`!x y. Cx(x + y) = Cx(x) + Cx(y)`,
  REWRITE_TAC[CX_DEF; complex_add; RE; IM; REAL_ADD_LID]);;

let CX_SUB = prove
 (`!x y. Cx(x - y) = Cx(x) - Cx(y)`,
  REWRITE_TAC[complex_sub; real_sub; CX_ADD; CX_NEG]);;

let CX_MUL = prove
 (`!x y. Cx(x * y) = Cx(x) * Cx(y)`,
  REWRITE_TAC[CX_DEF; complex_mul; RE; IM; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_RID]);;

let CX_DIV = prove
 (`!x y. Cx(x / y) = Cx(x) / Cx(y)`,
  REWRITE_TAC[complex_div; real_div; CX_MUL; CX_INV]);;

let CX_POW = prove
 (`!x n. Cx(x pow n) = Cx(x) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; real_pow; CX_MUL]);;

let CX_ABS = prove
 (`!x. Cx(abs x) = Cx(norm(Cx(x)))`,
  REWRITE_TAC[CX_DEF; complex_norm; COMPLEX_EQ; RE; IM] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

let COMPLEX_NORM_CX = prove
 (`!x. norm(Cx(x)) = abs(x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_ABS]);;

(* ------------------------------------------------------------------------- *)
(* A convenient lemma that we need a few times below.                        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_ENTIRE = prove
 (`!x y. (x * y = Cx(&0)) <=> (x = Cx(&0)) \/ (y = Cx(&0))`,
  REWRITE_TAC[COMPLEX_EQ; complex_mul; RE; IM; CX_DEF; GSYM REAL_SOS_EQ_0] THEN
  CONV_TAC REAL_RING);;

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

let COMPLEX_POW_II_2 = prove
 (`ii pow 2 = --Cx(&1)`,
  REWRITE_TAC[ii; COMPLEX_POW_2; complex_mul; CX_DEF; RE; IM; complex_neg] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let COMPLEX_POW_EQ_0 = prove
 (`!x n. (x pow n = Cx(&0)) <=> (x = Cx(&0)) /\ ~(n = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_SUC; complex_pow; COMPLEX_ENTIRE] THENL
   [SIMPLE_COMPLEX_ARITH_TAC; CONV_TAC TAUT]);;

(* ------------------------------------------------------------------------- *)
(* Norms (aka "moduli").                                                     *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_NORM_CX = prove
 (`!x. norm(Cx x) = abs(x)`,
  GEN_TAC THEN REWRITE_TAC[complex_norm; CX_DEF; RE; IM] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

let COMPLEX_NORM_POS = prove
 (`!z. &0 <= norm(z)`,
  SIMP_TAC[complex_norm; SQRT_POS_LE; REAL_POW_2;
           REAL_LE_SQUARE; REAL_LE_ADD]);;

let COMPLEX_ABS_NORM = prove
 (`!z. abs(norm z) = norm z`,
  REWRITE_TAC[real_abs; COMPLEX_NORM_POS]);;

let COMPLEX_NORM_ZERO = prove
 (`!z. (norm z = &0) <=> (z = Cx(&0))`,
  GEN_TAC THEN REWRITE_TAC[complex_norm] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM SQRT_0] THEN
  SIMP_TAC[REAL_POW_2; REAL_LE_SQUARE; REAL_LE_ADD; REAL_POS; SQRT_INJ] THEN
  REWRITE_TAC[COMPLEX_EQ; RE; IM; CX_DEF] THEN
  SIMP_TAC[REAL_LE_SQUARE; REAL_ARITH
   `&0 <= x /\ &0 <= y ==> ((x + y = &0) <=> (x = &0) /\ (y = &0))`] THEN
  REWRITE_TAC[REAL_ENTIRE]);;

let COMPLEX_NORM_NUM = prove
 (`norm(Cx(&n)) = &n`,
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM]);;

let COMPLEX_NORM_0 = prove
 (`norm(Cx(&0)) = &0`,
  MESON_TAC[COMPLEX_NORM_ZERO]);;

let COMPLEX_NORM_NZ = prove
 (`!z. &0 < norm(z) <=> ~(z = Cx(&0))`,
  MESON_TAC[COMPLEX_NORM_ZERO; COMPLEX_ABS_NORM; REAL_ABS_NZ]);;

let COMPLEX_NORM_NEG = prove
 (`!z. norm(--z) = norm(z)`,
  REWRITE_TAC[complex_neg; complex_norm; REAL_POW_2; RE; IM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let COMPLEX_NORM_MUL = prove
 (`!w z. norm(w * z) = norm(w) * norm(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[complex_norm; complex_mul; RE; IM] THEN
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

let COMPLEX_NORM_TRIANGLE = prove
 (`!w z. norm(w + z) <= norm(w) + norm(z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_norm; complex_add; RE; IM] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ abs(x) <= abs(y) ==> x <= y`) THEN
  SIMP_TAC[SQRT_POS_LE; REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE;
           REAL_LE_SQUARE_ABS; SQRT_POW_2] THEN
  GEN_REWRITE_TAC RAND_CONV[REAL_ARITH
    `(a + b) * (a + b) = a * a + b * b + &2 * a * b`] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN
  SIMP_TAC[SQRT_POW_2; REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE] THEN
  REWRITE_TAC[REAL_ARITH
   `(rw + rz) * (rw + rz) + (iw + iz) * (iw + iz) <=
    (rw * rw + iw * iw) + (rz * rz + iz * iz) + &2 * other <=>
    rw * rz + iw * iz <= other`] THEN
  SIMP_TAC[GSYM SQRT_MUL; REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ abs(x) <= abs(y) ==> x <= y`) THEN
  SIMP_TAC[SQRT_POS_LE; REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE;
           REAL_LE_SQUARE_ABS; SQRT_POW_2; REAL_LE_MUL] THEN
  REWRITE_TAC[REAL_ARITH
   `(rw * rz + iw * iz) * (rw * rz + iw * iz) <=
    (rw * rw + iw * iw) * (rz * rz + iz * iz) <=>
    &0 <= (rw * iz - rz * iw) * (rw * iz - rz * iw)`] THEN
  REWRITE_TAC[REAL_LE_SQUARE]);;

let COMPLEX_NORM_TRIANGLE_SUB = prove
 (`!w z. norm(w) <= norm(w + z) + norm(z)`,
  MESON_TAC[COMPLEX_NORM_TRIANGLE; COMPLEX_NORM_NEG; COMPLEX_ADD_ASSOC;
            COMPLEX_ADD_RINV; COMPLEX_ADD_RID]);;

let COMPLEX_NORM_ABS_NORM = prove
 (`!w z. abs(norm w - norm z) <= norm(w - z)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `a - b <= x /\ b - a <= x ==> abs(a - b) <= x:real`) THEN
  MESON_TAC[COMPLEX_NEG_SUB; COMPLEX_NORM_NEG; REAL_LE_SUB_RADD; complex_sub;
            COMPLEX_NORM_TRIANGLE_SUB]);;

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

(* ------------------------------------------------------------------------- *)
(* Conversion of (complex-type) rational constant to ML rational number.     *)
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
(* Conversions to perform operations if coefficients are rational constants. *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RAT_MUL_CONV =
  GEN_REWRITE_CONV I [GSYM CX_MUL] THENC RAND_CONV REAL_RAT_MUL_CONV;;

let COMPLEX_RAT_ADD_CONV =
  GEN_REWRITE_CONV I [GSYM CX_ADD] THENC RAND_CONV REAL_RAT_ADD_CONV;;

let COMPLEX_RAT_EQ_CONV =
  GEN_REWRITE_CONV I [CX_INJ] THENC REAL_RAT_EQ_CONV;;

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
(* Instantiate polynomial normalizer.                                        *)
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

let COMPLEX_RAT_INV_CONV =
  GEN_REWRITE_CONV I [GSYM CX_INV] THENC RAND_CONV REAL_RAT_INV_CONV;;

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
    if not(is_comb tm) or is_complex_const tm then REFL tm else
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

let COMPLEX_MUL_LINV = prove
 (`!z. ~(z = Cx(&0)) ==> (inv(z) * z = Cx(&1))`,
  REWRITE_TAC[complex_mul; complex_inv; RE; IM; COMPLEX_EQ; CX_DEF] THEN
  REWRITE_TAC[GSYM REAL_SOS_EQ_0] THEN CONV_TAC REAL_FIELD);;

let COMPLEX_MUL_RINV = prove
 (`!z. ~(z = Cx(&0)) ==> (z * inv(z) = Cx(&1))`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN REWRITE_TAC[COMPLEX_MUL_LINV]);;

let COMPLEX_RING,complex_ideal_cofactors =
  let ring_pow_tm = `(pow):complex->num->complex`
  and COMPLEX_INTEGRAL = prove
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
  and init = ALL_CONV in
  let pure,ideal =
    RING_AND_IDEAL_CONV
        (dest_complex_const,mk_complex_const,COMPLEX_RAT_EQ_CONV,
         `(--):complex->complex`,`(+):complex->complex->complex`,
         `(-):complex->complex->complex`,`(inv):complex->complex`,
         `(*):complex->complex->complex`,`(/):complex->complex->complex`,
         `(pow):complex->num->complex`,
         COMPLEX_INTEGRAL,COMPLEX_RABINOWITSCH,COMPLEX_POLY_CONV) in
  (fun tm -> let th = init tm in EQ_MP (SYM th) (pure(rand(concl th)))),
  ideal;;

(* ------------------------------------------------------------------------- *)
(* Most basic properties of inverses.                                        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_INV_0 = prove
 (`inv(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[complex_inv; CX_DEF; RE; IM; real_div; REAL_MUL_LZERO;
              REAL_NEG_0]);;

let COMPLEX_INV_MUL = prove
 (`!w z. inv(w * z) = inv(w) * inv(z)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`w = Cx(&0)`; `z = Cx(&0)`] THEN
  ASM_REWRITE_TAC[COMPLEX_INV_0; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[complex_mul; complex_inv; RE; IM; COMPLEX_EQ; CX_DEF] THEN
  REWRITE_TAC[GSYM REAL_SOS_EQ_0] THEN CONV_TAC REAL_FIELD);;

let COMPLEX_INV_1 = prove
 (`inv(Cx(&1)) = Cx(&1)`,
  REWRITE_TAC[complex_inv; CX_DEF; RE; IM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_DIV_1]);;

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

(* ------------------------------------------------------------------------- *)
(* And also field procedure.                                                 *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_FIELD =
  let prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PURE_REWRITE_CONV[FORALL_SIMP; EXISTS_SIMP; complex_div;
                      COMPLEX_INV_INV; COMPLEX_INV_MUL; GSYM REAL_POW_INV] THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV `(/\)` CONDS_CELIM_CONV THENC
    PRENEX_CONV
  and setup_conv = NNF_CONV THENC WEAK_CNF_CONV THENC CONJ_CANON_CONV
  and is_inv =
    let inv_tm = `inv:complex->complex`
    and is_div = is_binop `(/):complex->complex->complex` in
    fun tm -> (is_div tm or (is_comb tm & rator tm = inv_tm)) &
              not(is_complex_const(rand tm))
  and lemma_inv = MESON[COMPLEX_MUL_RINV]
    `!x. x = Cx(&0) \/ x * inv(x) = Cx(&1)`
  and dcases = MATCH_MP(TAUT `(p \/ q) /\ (r \/ s) ==> (p \/ r) \/ q /\ s`) in
  let cases_rule th1 th2 = dcases (CONJ th1 th2) in
  let BASIC_COMPLEX_FIELD tm =
    let is_freeinv t = is_inv t & free_in t tm in
    let itms = setify(map rand (find_terms is_freeinv tm)) in
    let dth = if itms = [] then TRUTH
              else end_itlist cases_rule (map (C SPEC lemma_inv) itms) in
    let tm' = mk_imp(concl dth,tm) in
    let th1 = setup_conv tm' in
    let ths = map COMPLEX_RING (conjuncts(rand(concl th1))) in
    let th2 = EQ_MP (SYM th1) (end_itlist CONJ ths) in
    MP (EQ_MP (SYM th1) (end_itlist CONJ ths)) dth in
  fun tm ->
    let th0 = prenex_conv tm in
    let tm0 = rand(concl th0) in
    let avs,bod = strip_forall tm0 in
    let th1 = setup_conv bod in
    let ths = map BASIC_COMPLEX_FIELD (conjuncts(rand(concl th1))) in
    EQ_MP (SYM th0) (GENL avs (EQ_MP (SYM th1) (end_itlist CONJ ths)));;

(* ------------------------------------------------------------------------- *)
(* Properties of inverses, divisions are now mostly automatic.               *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POW_DIV = prove
 (`!x y n. (x / y) pow n = (x pow n) / (y pow n)`,
  REWRITE_TAC[complex_div; COMPLEX_POW_MUL; COMPLEX_POW_INV]);;

let COMPLEX_DIV_REFL = prove
 (`!x. ~(x = Cx(&0)) ==> (x / x = Cx(&1))`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_EQ_MUL_LCANCEL = prove
 (`!x y z. (x * y = x * z) <=> (x = Cx(&0)) \/ (y = z)`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_EQ_MUL_RCANCEL = prove
 (`!x y z. (x * z = y * z) <=> (x = y) \/ (z = Cx(&0))`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_MUL_RINV_UNIQ = prove
 (`!w z. w * z = Cx(&1) ==> inv w = z`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_MUL_LINV_UNIQ = prove
 (`!w z. w * z = Cx(&1) ==> inv z = w`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIV_LMUL = prove
 (`!w z. ~(z = Cx(&0)) ==> z * w / z = w`,
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIV_RMUL = prove
 (`!w z. ~(z = Cx(&0)) ==> w / z * z = w`,
  CONV_TAC COMPLEX_FIELD);;
