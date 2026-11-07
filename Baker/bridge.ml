(* ========================================================================= *)
(* Bridge between algebraic_number and explicit integer polynomials.         *)
(*                                                                           *)
(* Purpose: algebraic_number of 100/transcendence.ml (root of a nonzero      *)
(* ring_polynomial over ZinC_ring, evaluated with poly_eval) means being a   *)
(* root of an explicit integer polynomial vsum(0..d) (\i. Cx(a i) * z pow i) *)
(* with real integer coefficients a : num->real and a d <> 0; variants with  *)
(* exact degree d >= 1 and a height bound H >= 1. Closure of the algebraic   *)
(* numbers under the field operations, powers, vsum and inverses (the        *)
(* library has algebraic_number_add, _mul and _neg in curried form;          *)
(* ALGEBRAIC_NUMBER_ADD, _MUL and _NEG restate them for their users).        *)
(*                                                                           *)
(* Main results: ALGEBRAIC_NUMBER_EXPLICIT (the characterization),           *)
(*   ALGEBRAIC_NUMBER_IMP_EXPLICIT, EXPLICIT_IMP_ALGEBRAIC_NUMBER,           *)
(*   ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT_1, EXPLICIT_POLY_EXACT_DEGREE;         *)
(*   ALGEBRAIC_NUMBER_CX_INTEGER, _CX_NUM, _CX_SQRT (square roots of natural *)
(*   numbers), _ADD, _SUB, _MUL, _NEG, _POW, _VSUM, _INV, _DIV.              *)
(*                                                                           *)
(* Uses: 100/transcendence.ml (algebraic_number, ZinC, algebraic_number_add, *)
(* algebraic_number_mul, algebraic_number_neg, algebraic_number_sum,         *)
(* ALGEBRAIC_OVER_QINC_COMPLEX), Library/fieldtheory.ml (ALGEBRAIC_OVER_DIV) *)
(* and Baker/lemmas.ml (COMPLEX_POLYFUN_POLY).                               *)
(* ========================================================================= *)

needs "Baker/lemmas.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Integers inside the complex numbers.                                      *)
(* ------------------------------------------------------------------------- *)

let CX_IN_ZINC = prove
 (`!x. Cx x IN ZinC <=> integer x`,
  REWRITE_TAC[ZinC; IN_ELIM_THM; CX_INJ] THEN
  MESON_TAC[int_tybij; INTEGER_REAL_OF_INT]);;

let ZINC_CX_RE = prove
 (`!z. z IN ZinC ==> integer(Re z) /\ Cx(Re z) = z`,
  REWRITE_TAC[ZinC; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RE_CX; INTEGER_REAL_OF_INT]);;

(* ------------------------------------------------------------------------- *)
(* From algebraic_number to an explicit integer polynomial of exact degree   *)
(* d >= 1, with coefficients vanishing beyond d.                             *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_NUMBER_IMP_EXPLICIT = prove
 (`!z. algebraic_number z
       ==> ?d a. 1 <= d /\ (!i. integer(a i)) /\ (!i. d < i ==> a i = &0) /\
                 ~(a d = &0) /\
                 vsum(0..d) (\i. Cx(a i) * z pow i) = Cx(&0)`,
  GEN_TAC THEN REWRITE_TAC[algebraic_number] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->complex` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = poly_deg ZinC_ring (p:(1->num)->complex)` THEN
  SUBGOAL_THEN `poly_deg complex_ring (p:(1->num)->complex) = d`
  ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    REWRITE_TAC[poly_deg; ZinC_ring_clauses; COMPLEX_RING_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. coeff i (p:(1->num)->complex) IN ZinC` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`ZinC_ring`; `p:(1->num)->complex`; `i:num`]
      COEFF_IN_CARRIER_ALT) THEN
    ASM_REWRITE_TAC[ZinC_ring_clauses];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(coeff d (p:(1->num)->complex) = Cx(&0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ZinC_ring`; `p:(1->num)->complex`] POLY_TOP_EQ_0) THEN
    ASM_REWRITE_TAC[ZinC_ring_clauses];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. d < i ==> coeff i (p:(1->num)->complex) = Cx(&0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ZinC_ring`; `p:(1->num)->complex`; `i:num`]
      COEFF_NONZERO_LE_DEG) THEN
    ASM_REWRITE_TAC[ZinC_ring_clauses] THEN
    ASM_MESON_TAC[NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(0..d) (\i. coeff i (p:(1->num)->complex) * z pow i) = Cx(&0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:(1->num)->complex`; `z:complex`; `d:num`]
      poly_eval_vsum) THEN
    ASM_SIMP_TAC[poly_complex_if_poly_ZinC; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `vsum(0..0) (\i. coeff i (p:(1->num)->complex) * z pow i) = Cx(&0)` THEN
    ASM_REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. Cx(Re(coeff i (p:(1->num)->complex))) = coeff i p /\
                    integer(Re(coeff i p))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ZINC_CX_RE]; ALL_TAC] THEN
  EXISTS_TAC `d:num` THEN
  EXISTS_TAC `\i. Re(coeff i (p:(1->num)->complex))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[RE_CX];
    ASM_REWRITE_TAC[GSYM CX_INJ]]);;

(* ------------------------------------------------------------------------- *)
(* Conversely, a root of an explicit integer polynomial with nonzero top     *)
(* coefficient is an algebraic number (the polynomial of                     *)
(* COMPLEX_POLYFUN_POLY has coefficients in ZinC).                           *)
(* ------------------------------------------------------------------------- *)

let EXPLICIT_IMP_ALGEBRAIC_NUMBER = prove
 (`!z d a. (!i. integer(a i)) /\ ~(a d = &0) /\
           vsum(0..d) (\i. Cx(a i) * z pow i) = Cx(&0)
           ==> algebraic_number z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[algebraic_number] THEN
  MP_TAC(SPECL [`d:num`; `\i. Cx((a:num->real) i)`] COMPLEX_POLYFUN_POLY) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:(1->num)->complex` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_POLYNOMIAL_COEFF_BOUND THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[RING_POWERSERIES_COEFF; ZinC_ring_clauses] THEN
    CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[CX_IN_ZINC; ZinC_0];
    DISCH_THEN(MP_TAC o AP_TERM `coeff d:((1->num)->complex)->complex`) THEN
    ASM_REWRITE_TAC[COEFF_POLY_0; ZinC_ring_clauses; LE_REFL; CX_INJ]]);;

(* ------------------------------------------------------------------------- *)
(* The explicit characterization.                                            *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_NUMBER_EXPLICIT = prove
 (`!z. algebraic_number z <=>
       ?d a. (!i. integer(a i)) /\ ~(a d = &0) /\
             vsum(0..d) (\i. Cx(a i) * z pow i) = Cx(&0)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP ALGEBRAIC_NUMBER_IMP_EXPLICIT) THEN
    MESON_TAC[];
    MESON_TAC[EXPLICIT_IMP_ALGEBRAIC_NUMBER]]);;

(* ------------------------------------------------------------------------- *)
(* Explicit degree d >= 1 and a uniform bound H for all coefficients.        *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT = prove
 (`!z. algebraic_number z
       ==> ?d a H. 1 <= d /\ (!i. integer(a i) /\ abs(a i) <= H) /\
                   ~(a d = &0) /\
                   vsum(0..d) (\i. Cx(a i) * z pow i) = Cx(&0)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ALGEBRAIC_NUMBER_IMP_EXPLICIT) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:num`; `a:num->real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`d:num`; `a:num->real`; `sum(0..d) (\i. abs((a:num->real) i))`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i <= d` THENL
   [MP_TAC(ISPECL [`\i. abs((a:num->real) i)`;
                   `sum(0..d) (\i. abs((a:num->real) i))`; `0..d`]
      SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_ABS_POS; REAL_LE_REFL; IN_NUMSEG] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[LE_0];
    SUBGOAL_THEN `(a:num->real) i = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_0] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[REAL_ABS_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Passing from degree <= d (not all coefficients zero) to the exact degree: *)
(* cut at the largest index with a nonzero coefficient.                      *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT_1 = prove
 (`!z. algebraic_number z
       ==> ?d a H. 1 <= d /\ &1 <= H /\ (!i. integer(a i) /\ abs(a i) <= H) /\
                   ~(a d = &0) /\
                   vsum(0..d) (\i. Cx(a i) * z pow i) = Cx(&0)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:num`; `a:num->real`; `H:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`d:num`; `a:num->real`; `max (&1) H`] THEN
  ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  ASM_REWRITE_TAC[]);;

let COMPLEX_POLYFUN_EXACT_DEGREE = prove
 (`!c d. ~(!i. i <= d ==> c i = Cx(&0))
         ==> ?d'. d' <= d /\ ~(c d' = Cx(&0)) /\
                  (!i. d' < i /\ i <= d ==> c i = Cx(&0)) /\
                  !z. vsum(0..d') (\i. c i * z pow i) =
                      vsum(0..d) (\i. c i * z pow i)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?m. (m <= d /\ ~((c:num->complex) m = Cx(&0))) /\
        (!x. x <= d /\ ~(c x = Cx(&0)) ==> x <= m)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(BETA_RULE(ISPEC
      `\i. i <= d /\ ~((c:num->complex) i = Cx(&0))` num_MAX))] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. m < i /\ i <= d ==> (c:num->complex) i = Cx(&0)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
  EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:complex` THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
  ASM_REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; LE_0; COMPLEX_VEC_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:num->complex) j = Cx(&0)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[COMPLEX_MUL_LZERO]]);;

let EXPLICIT_POLY_EXACT_DEGREE = prove
 (`!z d a B. (!i. integer(a i) /\ abs(a i) <= B) /\
             ~(!i. i <= d ==> a i = &0) /\
             vsum(0..d) (\i. Cx(a i) * z pow i) = Cx(&0)
             ==> ?d'. d' <= d /\ ~(a d' = &0) /\
                      vsum(0..d') (\i. Cx(a i) * z pow i) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i. Cx((a:num->real) i)`; `d:num`]
    COMPLEX_POLYFUN_EXACT_DEGREE) THEN
  ASM_REWRITE_TAC[CX_INJ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closure properties. The library has algebraic_number_add, _mul, _neg      *)
(* (curried), _ZinC, _QinC and _sum (over ring_sum); here the first ones in  *)
(* conjunctive form, plus subtraction, powers, vsum, quotients (from         *)
(* ALGEBRAIC_OVER_DIV of Library/fieldtheory.ml) and inverses.               *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_NUMBER_CX_INTEGER = prove
 (`!x. integer x ==> algebraic_number(Cx x)`,
  MESON_TAC[algebraic_number_ZinC; CX_IN_ZINC]);;

let ALGEBRAIC_NUMBER_CX_NUM = prove
 (`!n. algebraic_number(Cx(&n))`,
  MESON_TAC[algebraic_number_ZinC; num_in_ZinC]);;

let ALGEBRAIC_NUMBER_CX_SQRT = prove
 (`!n. algebraic_number(Cx(sqrt(&n)))`,
  GEN_TAC THEN MATCH_MP_TAC EXPLICIT_IMP_ALGEBRAIC_NUMBER THEN
  MAP_EVERY EXISTS_TAC
   [`2`; `\i. if i = 0 then --(&n) else if i = 1 then &0 else &1`] THEN
  REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED];
    CONV_TAC REAL_RAT_REDUCE_CONV;
    SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
    REWRITE_TAC[ARITH; VSUM_2] THEN
    REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
    SIMP_TAC[SQRT_POW_2; REAL_POS; real_pow; REAL_POW_1] THEN
    REAL_ARITH_TAC]);;

let ALGEBRAIC_NUMBER_ADD = prove
 (`!y z. algebraic_number y /\ algebraic_number z
         ==> algebraic_number(y + z)`,
  MESON_TAC[algebraic_number_add]);;

let ALGEBRAIC_NUMBER_MUL = prove
 (`!y z. algebraic_number y /\ algebraic_number z
         ==> algebraic_number(y * z)`,
  MESON_TAC[algebraic_number_mul]);;

let ALGEBRAIC_NUMBER_SUB = prove
 (`!y z. algebraic_number y /\ algebraic_number z
         ==> algebraic_number(y - z)`,
  REWRITE_TAC[complex_sub] THEN
  MESON_TAC[algebraic_number_add; algebraic_number_neg]);;

let ALGEBRAIC_NUMBER_POW = prove
 (`!z n. algebraic_number z ==> algebraic_number(z pow n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[complex_pow; ALGEBRAIC_NUMBER_CX_NUM; ALGEBRAIC_NUMBER_MUL]);;

let ALGEBRAIC_NUMBER_VSUM = prove
 (`!f:A->complex s.
        FINITE s /\ (!x. x IN s ==> algebraic_number(f x))
        ==> algebraic_number(vsum s f)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM COMPLEX_RING_SUM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] algebraic_number_sum) THEN
  ASM_REWRITE_TAC[]);;

let ALGEBRAIC_NUMBER_DIV = prove
 (`!y z. algebraic_number y /\ algebraic_number z
         ==> algebraic_number(y / z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`I:complex->complex`; `QinC_ring`; `complex_ring`;
                 `y:complex`; `z:complex`] ALGEBRAIC_OVER_DIV) THEN
  ASM_REWRITE_TAC[FIELD_EXTENSION_QINC_COMPLEX; ALGEBRAIC_OVER_QINC_COMPLEX;
                  complex_field_clauses]);;

let ALGEBRAIC_NUMBER_INV = prove
 (`!z. algebraic_number z ==> algebraic_number(inv z)`,
  MESON_TAC[ALGEBRAIC_NUMBER_DIV; ALGEBRAIC_NUMBER_CX_NUM;
            COMPLEX_FIELD `inv z = Cx(&1) / z`]);;
