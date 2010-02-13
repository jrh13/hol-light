(* ========================================================================= *)
(* Complex transcendental functions.                                         *)
(* ========================================================================= *)

needs "Library/transc.ml";;
needs "Library/floor.ml";;
needs "Complex/complexnumbers.ml";;

unparse_as_infix "exp";;
remove_interface "exp";;

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

let COMPLEX_NORM_GE_RE_IM = prove
 (`!z. abs(Re(z)) <= norm(z) /\ abs(Im(z)) <= norm(z)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
  REWRITE_TAC[complex_norm] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_ADDL; REAL_POW_2; REAL_LE_SQUARE]);;

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

(* ------------------------------------------------------------------------- *)
(* Complex exponential.                                                      *)
(* ------------------------------------------------------------------------- *)

let cexp = new_definition
 `cexp z = Cx(exp(Re z)) * complex(cos(Im z),sin(Im z))`;;

let CX_CEXP = prove
 (`!x. Cx(exp x) = cexp(Cx x)`,
  REWRITE_TAC[cexp; CX_DEF; RE; IM; SIN_0; COS_0] THEN
  REWRITE_TAC[GSYM CX_DEF; GSYM CX_MUL; REAL_MUL_RID]);;

let CEXP_0 = prove
 (`cexp(Cx(&0)) = Cx(&1)`,
  REWRITE_TAC[GSYM CX_CEXP; REAL_EXP_0]);;

let CEXP_ADD = prove
 (`!w z. cexp(w + z) = cexp(w) * cexp(z)`,
  REWRITE_TAC[COMPLEX_EQ; cexp; complex_mul; complex_add; RE; IM; CX_DEF] THEN
  REWRITE_TAC[REAL_EXP_ADD; SIN_ADD; COS_ADD] THEN CONV_TAC REAL_RING);;

let CEXP_MUL = prove
 (`!n z. cexp(Cx(&n) * z) = cexp(z) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[complex_pow] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; CEXP_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; COMPLEX_ADD_RDISTRIB; CX_ADD] THEN
  ASM_REWRITE_TAC[CEXP_ADD; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let CEXP_NONZERO = prove
 (`!z. ~(cexp z = Cx(&0))`,
  GEN_TAC THEN REWRITE_TAC[cexp; COMPLEX_ENTIRE; CX_INJ; REAL_EXP_NZ] THEN
  REWRITE_TAC[CX_DEF; RE; IM; COMPLEX_EQ] THEN
  MP_TAC(SPEC `Im z` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let CEXP_NEG_LMUL = prove
 (`!z. cexp(--z) * cexp(z) = Cx(&1)`,
  REWRITE_TAC[GSYM CEXP_ADD; COMPLEX_ADD_LINV; CEXP_0]);;

let CEXP_NEG_RMUL = prove
 (`!z. cexp(z) * cexp(--z) = Cx(&1)`,
  REWRITE_TAC[GSYM CEXP_ADD; COMPLEX_ADD_RINV; CEXP_0]);;

let CEXP_NEG = prove
 (`!z. cexp(--z) = inv(cexp z)`,
  MESON_TAC[CEXP_NEG_LMUL; COMPLEX_MUL_LINV_UNIQ]);;

let CEXP_SUB = prove
 (`!w z. cexp(w - z) = cexp(w) / cexp(z)`,
  REWRITE_TAC[complex_sub; complex_div; CEXP_NEG; CEXP_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Complex trig functions.                                                   *)
(* ------------------------------------------------------------------------- *)

let ccos = new_definition
  `ccos z = (cexp(ii * z) + cexp(--ii * z)) / Cx(&2)`;;

let csin = new_definition
  `csin z = (cexp(ii * z) - cexp(--ii * z)) / (Cx(&2) * ii)`;;

let CX_CSIN,CX_CCOS = (CONJ_PAIR o prove)
 (`(!x. Cx(sin x) = csin(Cx x)) /\ (!x. Cx(cos x) = ccos(Cx x))`,
  REWRITE_TAC[csin; ccos; cexp; CX_DEF; ii; RE; IM; complex_mul; complex_add;
              REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_SUB_RZERO;
              REAL_MUL_LID; complex_neg; REAL_EXP_0; REAL_ADD_LID;
              REAL_MUL_LNEG; REAL_NEG_0; REAL_ADD_RID; complex_sub;
              SIN_NEG; COS_NEG; GSYM REAL_MUL_2; GSYM real_sub;
              complex_div; REAL_SUB_REFL; complex_inv; REAL_SUB_RNEG] THEN
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let CSIN_0 = prove
 (`csin(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[GSYM CX_CSIN; SIN_0]);;

let CCOS_0 = prove
 (`ccos(Cx(&0)) = Cx(&1)`,
  REWRITE_TAC[GSYM CX_CCOS; COS_0]);;

let CSIN_CIRCLE = prove
 (`!z. csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[csin; ccos] THEN
  MP_TAC(SPEC `ii * z` CEXP_NEG_LMUL) THEN
  MP_TAC COMPLEX_POW_II_2 THEN REWRITE_TAC[COMPLEX_MUL_LNEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_ADD = prove
 (`!w z. csin(w + z) = csin(w) * ccos(z) + ccos(w) * csin(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[csin; ccos; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_FIELD);;

let CCOS_ADD = prove
 (`!w z. ccos(w + z) = ccos(w) * ccos(z) - csin(w) * csin(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[csin; ccos; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_FIELD);;

let CSIN_NEG = prove
 (`!z. csin(--z) = --(csin(z))`,
  REWRITE_TAC[csin; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG] THEN
  GEN_TAC THEN MP_TAC COMPLEX_POW_II_2 THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_NEG = prove
 (`!z. ccos(--z) = ccos(z)`,
  REWRITE_TAC[ccos; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG] THEN
  GEN_TAC THEN MP_TAC COMPLEX_POW_II_2 THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_DOUBLE = prove
 (`!z. csin(Cx(&2) * z) = Cx(&2) * csin(z) * ccos(z)`,
  REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CSIN_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let CCOS_DOUBLE = prove
 (`!z. ccos(Cx(&2) * z) = (ccos(z) pow 2) - (csin(z) pow 2)`,
  REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CCOS_ADD] THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Euler and de Moivre formulas.                                             *)
(* ------------------------------------------------------------------------- *)

let CEXP_EULER = prove
 (`!z. cexp(ii * z) = ccos(z) + ii * csin(z)`,
  REWRITE_TAC[ccos; csin] THEN MP_TAC COMPLEX_POW_II_2 THEN
  CONV_TAC COMPLEX_FIELD);;

let DEMOIVRE = prove
 (`!z n. (ccos z + ii * csin z) pow n =
         ccos(Cx(&n) * z) + ii * csin(Cx(&n) * z)`,
  REWRITE_TAC[GSYM CEXP_EULER; GSYM CEXP_MUL] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let EXISTS_COMPLEX = prove
 (`!P. (?z. P (Re z) (Im z)) <=> ?x y. P x y`,
  MESON_TAC[RE; IM; COMPLEX]);;

let COMPLEX_UNIMODULAR_POLAR = prove
 (`!z. (norm z = &1) ==> ?x. z = complex(cos(x),sin(x))`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM `2` o AP_TERM `(pow):real->num->real`) THEN
  REWRITE_TAC[complex_norm] THEN
  SIMP_TAC[REAL_POW_2; REWRITE_RULE[REAL_POW_2] SQRT_POW_2;
           REAL_LE_SQUARE; REAL_LE_ADD] THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:real` o MATCH_MP CIRCLE_SINCOS) THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM]);;

let SIN_INTEGER_2PI = prove
 (`!n. integer n ==> sin((&2 * pi) * n) = &0`,
  REWRITE_TAC[integer; REAL_ARITH `abs(x) = &n <=> x = &n \/ x = -- &n`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RNEG; SIN_NEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; SIN_DOUBLE] THEN
  REWRITE_TAC[REAL_ARITH `pi * &n = &n * pi`; SIN_NPI] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_NEG_0]);;

let COS_INTEGER_2PI = prove
 (`!n. integer n ==> cos((&2 * pi) * n) = &1`,
  REWRITE_TAC[integer; REAL_ARITH `abs(x) = &n <=> x = &n \/ x = -- &n`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RNEG; COS_NEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; COS_DOUBLE] THEN
  REWRITE_TAC[REAL_ARITH `pi * &n = &n * pi`; SIN_NPI; COS_NPI] THEN
  REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[GSYM REAL_POW_POW; REAL_POW_2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_SUB_RZERO]);;

let SINCOS_PRINCIPAL_VALUE = prove
 (`!x. ?y. (--pi < y /\ y <= pi) /\ (sin(y) = sin(x) /\ cos(y) = cos(x))`,
  GEN_TAC THEN EXISTS_TAC `pi - (&2 * pi) * frac((pi - x) / (&2 * pi))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[REAL_ARITH `--p < p - x <=> x < (&2 * p) * &1`;
             REAL_ARITH `p - x <= p <=> (&2 * p) * &0 <= x`;
             REAL_LT_LMUL_EQ; REAL_LE_LMUL_EQ; REAL_LT_MUL;
             PI_POS; REAL_OF_NUM_LT; ARITH; FLOOR_FRAC];
   REWRITE_TAC[FRAC_FLOOR; REAL_SUB_LDISTRIB] THEN
   SIMP_TAC[REAL_DIV_LMUL; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH; REAL_LT_IMP_NZ;
    PI_POS; REAL_ARITH `a - (a - b - c):real = b + c`; SIN_ADD; COS_ADD] THEN
   SIMP_TAC[FLOOR_FRAC; SIN_INTEGER_2PI; COS_INTEGER_2PI] THEN
   CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* Complex logarithms (the conventional principal value).                    *)
(* ------------------------------------------------------------------------- *)

let clog = new_definition
 `clog z = @w. cexp(w) = z /\ --pi < Im(w) /\ Im(w) <= pi`;;

let CLOG_WORKS = prove
 (`!z. ~(z = Cx(&0))
       ==> cexp(clog z) = z /\ --pi < Im(clog z) /\ Im(clog z) <= pi`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[clog] THEN CONV_TAC SELECT_CONV THEN
  REWRITE_TAC[cexp; EXISTS_COMPLEX] THEN
  EXISTS_TAC `ln(norm(z:complex))` THEN
  SUBGOAL_THEN `exp(ln(norm(z:complex))) = norm(z)` SUBST1_TAC THENL
   [ASM_MESON_TAC[REAL_EXP_LN; COMPLEX_NORM_NZ]; ALL_TAC] THEN
  MP_TAC(SPEC `z / Cx(norm z)` COMPLEX_UNIMODULAR_POLAR) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[COMPLEX_ABS_NORM; REAL_DIV_REFL; COMPLEX_NORM_ZERO];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `x:real` SINCOS_PRINCIPAL_VALUE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CX_INJ; COMPLEX_DIV_LMUL; COMPLEX_NORM_ZERO]);;

let CEXP_CLOG = prove
 (`!z. ~(z = Cx(&0)) ==> cexp(clog z) = z`,
  SIMP_TAC[CLOG_WORKS]);;

(* ------------------------------------------------------------------------- *)
(* Unwinding number.                                                         *)
(* ------------------------------------------------------------------------- *)

let unwinding = new_definition
 `unwinding(z) = (z - clog(cexp z)) / (Cx(&2 * pi) * ii)`;;

let COMPLEX_II_NZ = prove
 (`~(ii = Cx(&0))`,
  MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING);;

let UNWINDING_2PI = prove
 (`Cx(&2 * pi) * ii * unwinding(z) = z - clog(cexp z)`,
  REWRITE_TAC[unwinding; COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC COMPLEX_DIV_LMUL THEN
  REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; COMPLEX_II_NZ] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An example of how to get nice identities with unwinding number.           *)
(* ------------------------------------------------------------------------- *)

let CLOG_MUL = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
               clog(w) + clog(z) -
               Cx(&2 * pi) * ii * unwinding(clog w + clog z)`,
  REWRITE_TAC[UNWINDING_2PI;
    COMPLEX_RING `w + z - ((w + z) - c) = c:complex`] THEN
  ASM_SIMP_TAC[CEXP_ADD; CEXP_CLOG]);;
