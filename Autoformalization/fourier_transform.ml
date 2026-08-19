(* ========================================================================= *)
(* The Fourier transform on R (Fremlin, Measure Theory vol 2, sections       *)
(* 283-284).                                                                 *)
(*                                                                           *)
(* NORMALIZATION (Fremlin 283Ba): symmetric, so the transform is an L^2      *)
(* isometry (Plancherel constant 1):                                         *)
(*   (fourier f)(y) = (1 / sqrt(2*pi)) * INT_R e^{-i y x} f(x) dx.           *)
(* f : real->complex (= real^1->real^2); the spatial variable ranges over R  *)
(* via drop of a real^1 integration variable.  The normalizing constant is   *)
(* written  Cx(&1) / Cx(sqrt(&2 * pi))  (division kept at the COMPLEX level) *)
(* so COMPLEX_FIELD / SIMPLE_COMPLEX_ARITH can normalize it as an atom --    *)
(* Cx(&1 / sqrt(&2 * pi)) instead jams those tactics on the sqrt inside Cx.  *)
(* ========================================================================= *)

needs "100/fourier.ml";;

let fourier = new_definition
 `fourier (f:real->complex) (y:real) =
    (Cx(&1) / Cx(sqrt(&2 * pi))) *
    integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))`;;

(* The transform kernel at frequency y.                                      *)
let fourier_kernel = new_definition
 `fourier_kernel (y:real) (x:real) = cexp(--(ii * Cx y * Cx x))`;;

(* ========================================================================= *)
(* SECTION 1. Basic properties of the Fourier transform.                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 283C(a,b): linearity.  Under integrability of the transform integrand at
   y *)
(* (automatic for the L^1 / Schwartz functions we apply it to).              *)
(* ------------------------------------------------------------------------- *)

let FOURIER_LMUL = prove
 (`!f c y.
        (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))
        integrable_on (:real^1)
        ==> fourier (\x. c * f x) y = c * fourier f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  SUBGOAL_THEN
   `integral (:real^1)
             (\x. cexp(--(ii * Cx y * Cx(drop x))) * (c * f(drop x))) =
    c * integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))`
   (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN
     `(\x. cexp(--(ii * Cx y * Cx(drop x))) * (c * f(drop x))) =
      (\x. c * (cexp(--(ii * Cx y * Cx(drop x))) * f(drop x)))`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_COMPLEX_LMUL];
    ALL_TAC] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let FOURIER_ADD = prove
 (`!f g y.
        (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))
        integrable_on (:real^1) /\
        (\x. cexp(--(ii * Cx y * Cx(drop x))) * g(drop x))
        integrable_on (:real^1)
        ==> fourier (\x. f x + g x) y = fourier f y + fourier g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  SUBGOAL_THEN
   `integral (:real^1)
             (\x. cexp(--(ii * Cx y * Cx(drop x))) * (f(drop x) + g(drop x))) =
    integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x)) +
    integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * g(drop x))`
   (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN
     `(\x. cexp(--(ii * Cx y * Cx(drop x))) * (f(drop x) + g(drop x))) =
      (\x. (cexp(--(ii * Cx y * Cx(drop x))) * f(drop x)) +
           (cexp(--(ii * Cx y * Cx(drop x))) * g(drop x)))`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD]; ALL_TAC] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

(* The Fourier transform of the zero function is zero.                       *)
let FOURIER_0 = prove
 (`!y. fourier (\x. Cx(&0)) y = Cx(&0)`,
  GEN_TAC THEN REWRITE_TAC[fourier] THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; GSYM COMPLEX_VEC_0; INTEGRAL_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Translation-invariance of the integral over R, at the real->complex level *)
(* (reusable for the change-of-variables in the shift/dilation rules).       *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_TRANSLATION_R = prove
 (`!G:real->complex c.
     integral (:real^1) (\x. G(c + drop x)) =
     integral (:real^1) (\x. G(drop x))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. (G:real->complex)(drop x)`; `(:real^1)`; `lift c`]
    INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN
  SUBGOAL_THEN `IMAGE (\x:real^1. lift c + x) (:real^1) = (:real^1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[TRANSLATION_UNIV]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* 283C(c): the SHIFT rule.  If h(x) = f(x + c) then h^(y) = e^{icy} f^(y).  *)
(* Change of variables x |-> x - c inside the integral, then pull the        *)
(* constant e^{icy} out.                                                     *)
(* ------------------------------------------------------------------------- *)

let FOURIER_SHIFT = prove
 (`!f c y.
        (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))
        integrable_on (:real^1)
   ==> fourier (\x. f(x + c)) y = cexp(ii * Cx c * Cx y) * fourier f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x + c)) =
    cexp(ii * Cx c * Cx y) *
    integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))`
   (fun th -> REWRITE_TAC[th]) THENL [ALL_TAC; SIMPLE_COMPLEX_ARITH_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x + c)) =
    integral (:real^1)
      (\x. (\u. cexp(--(ii * Cx y * Cx(u - c))) * (f:real->complex)
                u)(c + drop x))`
   SUBST1_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `!c x:real. (c + x) - c = x`; REAL_ADD_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_TRANSLATION_R] THEN
  SUBGOAL_THEN
   `!x:real^1. cexp(--(ii * Cx y * Cx(drop x - c))) * f(drop x) =
               cexp(ii * Cx c * Cx y) *
               (cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `cexp(--(ii * Cx y * Cx(drop x - c))) =
                  cexp(ii * Cx c * Cx y) *
                  cexp(--(ii * Cx y * Cx(drop x)))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM CEXP_ADD] THEN AP_TERM_TAC THEN REWRITE_TAC[CX_SUB] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      SIMPLE_COMPLEX_ARITH_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 283C(d): the MODULATION rule.  If h(x) = e^{icx} f(x) then
   h^(y)=f^(y - c). *)
(* No change of variables -- just combine the two exponentials.              *)
(* ------------------------------------------------------------------------- *)

let FOURIER_MODULATION = prove
 (`!f c y. fourier (\x. cexp(ii * Cx c * Cx x) * f x) y = fourier f (y - c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fourier] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM CEXP_ADD] THEN AP_TERM_TAC THEN REWRITE_TAC[CX_SUB] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The transform kernel has modulus 1 (real frequency/position), hence the   *)
(* fundamental L^1 -> L^infinity bound:  |f^(y)| <= (1/sqrt(2 pi)) ||f||_1.  *)
(* This is the Riemann-Lebesgue-adjacent boundedness (283B): the transform
   of  *)
(* an integrable function is bounded.                                        *)
(* ------------------------------------------------------------------------- *)

let FOURIER_KERNEL_NORM = prove
 (`!y x. norm(cexp(--(ii * Cx y * Cx x))) = &1`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `--(ii * Cx y * Cx x) = ii * Cx(--(y * x))` SUBST1_TAC THENL
   [REWRITE_TAC[CX_NEG; CX_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_CEXP_II]);;

let FOURIER_BOUND = prove
 (`!f y.
        (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))
        integrable_on (:real^1) /\
        (\x. lift(norm(f(drop x)))) integrable_on (:real^1)
   ==> norm(fourier f y) <=
       (&1 / sqrt(&2 * pi)) *
       drop(integral (:real^1) (\x. lift(norm(f(drop x)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `norm(Cx(&1) / Cx(sqrt(&2 * pi))) = &1 / sqrt(&2 * pi)`
    SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN MP_TAC PI_POS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[LIFT_DROP; COMPLEX_NORM_MUL; FOURIER_KERNEL_NORM; REAL_MUL_LID;
              REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Reflection.  Whole-line reflection of the R->complex integral (reusable), *)
(* and the transform reflection rule  (\x. f(--x))^(y) = f^(--y).            *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_REFLECT_R = prove
 (`!G:real->complex.
     integral (:real^1) (\x. G(--(drop x))) =
     integral (:real^1) (\x. G(drop x))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. (G:real->complex)(drop x)`; `(:real^1)`]
    INTEGRAL_REFLECT_GEN) THEN
  REWRITE_TAC[DROP_NEG] THEN
  SUBGOAL_THEN `IMAGE (--) (:real^1) = (:real^1)` SUBST1_TAC THENL
   [REWRITE_TAC[REFLECT_UNIV]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let FOURIER_REFLECT = prove
 (`!f y. fourier (\x. f(--x)) y = fourier f (--y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fourier] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(--drop x)) =
    integral (:real^1)
      (\x. (\u. cexp(ii * Cx y * Cx u) * (f:real->complex) u)(--(drop x)))`
   SUBST1_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[] THEN
    REWRITE_TAC[CX_NEG] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_REFLECT_R] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CX_NEG] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 283C(e): the DILATION rule.  For c > 0, if h(x) = f(cx) then              *)
(* h^(y) = (1/c) f^(y/c).  Uses the whole-line integral stretch.             *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_STRETCH_R = prove
 (`!G:real->complex c. &0 < c /\ (\x. G(drop x)) integrable_on (:real^1)
   ==> integral (:real^1) (\x. G(c * drop x)) =
       (&1 / c) % integral (:real^1) (\x. G(drop x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. (G:real->complex)(drop x)`;
                 `integral (:real^1) (\x:real^1. (G:real->complex)(drop x))`;
                 `(:real^1)`; `c:real`; `vec 0:real^1`]
                HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; VECTOR_MUL_RZERO; VECTOR_ADD_RID;
               VECTOR_NEG_0] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^1. inv c % x) (:real^1) = (:real^1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `z:real^1` THEN
    EXISTS_TAC `c % z:real^1` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                 VECTOR_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_1; REAL_POW_1] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
  REWRITE_TAC[DROP_CMUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[real_div; REAL_MUL_LID]);;

let FOURIER_DILATION = prove
 (`!f c y.
        &0 < c /\
        (\x. cexp(--(ii * Cx (y/c) * Cx(drop x))) * f(drop x))
        integrable_on (:real^1)
   ==> fourier (\x. f(c * x)) y = Cx(&1 / c) * fourier f (y / c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(c * drop x)) =
    integral (:real^1)
      (\x. (\u. cexp(--(ii * Cx (y/c) * Cx u)) * (f:real->complex)
                u)(c * drop x))`
   SUBST1_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_MUL] THEN
    SUBGOAL_THEN `Cx(y / c) * Cx c = Cx y`
      (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
     [REWRITE_TAC[GSYM CX_MUL] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_STRETCH_R] THEN
  REWRITE_TAC[COMPLEX_CMUL] THEN
  SPEC_TAC(`integral (:real^1)
                     (\x. cexp(--(ii * Cx (y/c) * Cx(drop x))) *
                          (f:real->complex)(drop x))`,
           `z:complex`) THEN
  GEN_TAC THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* CONTINUITY of the Fourier transform (283D-adjacent): for f in L^1, f^ is  *)
(* continuous.  Proved via dominated convergence -- for any y_k -> y the     *)
(* transform integrands are dominated by |f| and converge pointwise, so the  *)
(* integrals converge.  Stated in sequential form.                           *)
(* First two auxiliary limits: the kernel argument, and the kernel value.    *)
(* ------------------------------------------------------------------------- *)

let FOURIER_KARG_LIM = prove
 (`!x:real yy y. (yy ---> y) sequentially
   ==> ((\k. --(ii * Cx (yy k) * Cx x)) --> --(ii * Cx y * Cx x))
       sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NEG THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `ii * Cx a * Cx x = (ii * Cx x) * Cx a`] THEN
  MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REALLIM_COMPLEX]) THEN
  REWRITE_TAC[o_DEF]);;

let FOURIER_KVAL_LIM = prove
 (`!x:real yy y. (yy ---> y) sequentially
   ==> ((\k. cexp(--(ii * Cx (yy k) * Cx x))) -->
        cexp(--(ii * Cx y * Cx x))) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cexp`; `--(ii * Cx y * Cx x)`]
    CONTINUOUS_AT_SEQUENTIALLY) THEN
  REWRITE_TAC[CONTINUOUS_AT_CEXP] THEN
  DISCH_THEN(MP_TAC o SPEC `\k. --(ii * Cx ((yy:num->real) k) * Cx x)`) THEN
  ASM_SIMP_TAC[FOURIER_KARG_LIM; o_DEF]);;

(* The integral part is sequentially continuous in the frequency (DCT).      *)
let FOURIER_INTEGRAL_CONTINUOUS = prove
 (`!f y. (!y'. (\x. cexp(--(ii * Cx y' * Cx(drop x))) * f(drop x))
               integrable_on (:real^1)) /\
         (\x. lift(norm(f(drop x)))) integrable_on (:real^1)
   ==> !yy. (yy ---> y) sequentially
       ==> ((\k. integral (:real^1)
                          (\x. cexp(--(ii * Cx (yy k) * Cx(drop x))) *
                               f(drop x)))
            --> integral (:real^1)
                         (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x)))
           sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\k x. cexp(--(ii * Cx ((yy:num->real) k) * Cx(drop x))) *
           (f:real->complex)(drop x)`;
    `\x. cexp(--(ii * Cx y * Cx(drop x))) * (f:real->complex)(drop x)`;
    `\x. lift(norm((f:real->complex)(drop x)))`;
    `(:real^1)`] DOMINATED_CONVERGENCE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[LIFT_DROP; COMPLEX_NORM_MUL] THEN
      SUBGOAL_THEN
        `norm(cexp(--(ii * Cx (yy(k:num)) * Cx(drop(x:real^1))))) = &1`
        SUBST1_TAC THENL
       [SUBGOAL_THEN `--(ii * Cx (yy(k:num)) * Cx(drop(x:real^1))) =
                      ii * Cx(--(yy k * drop x))`
          SUBST1_TAC THENL
         [REWRITE_TAC[CX_NEG; CX_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_LE_REFL];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `a * b = b * a`] THEN
      MATCH_MP_TAC LIM_COMPLEX_LMUL THEN ASM_SIMP_TAC[FOURIER_KVAL_LIM]];
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th)) THEN REWRITE_TAC[]]);;

let FOURIER_CONTINUOUS_SEQ = prove
 (`!f y. (!y'. (\x. cexp(--(ii * Cx y' * Cx(drop x))) * f(drop x))
               integrable_on (:real^1)) /\
         (\x. lift(norm(f(drop x)))) integrable_on (:real^1)
   ==> !yy. (yy ---> y) sequentially
       ==> ((\k. fourier f (yy k)) --> fourier f y) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `yy:num->real` THEN
  DISCH_TAC THEN
  REWRITE_TAC[fourier] THEN MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
  MP_TAC(ISPECL [`f:real->complex`; `y:real`] FOURIER_INTEGRAL_CONTINUOUS) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The elementary oscillatory integral  INT_{-a}^a e^{iby} dy = 2 sin(ab)/b  *)
(* (b =/= 0, a >= 0), the kernel of the Fubini step in the inversion theorem *)
(* 283H.  Antiderivative e^{iby}/(ib); vector FTC along the reals.           *)
(* ------------------------------------------------------------------------- *)

(* d/dy [ e^{iby}/(ib) ] = e^{iby}  (real->complex chain rule).              *)
let CEXP_IB_VECTOR_DERIV = prove
 (`!b y. ~(b = &0)
     ==> ((\y. cexp(ii * Cx b * Cx(drop y)) / (ii * Cx b))
          has_vector_derivative
          cexp(ii * Cx b * Cx(drop y))) (at y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
  SUBGOAL_THEN `~(ii * Cx b = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  COMPLEX_DIFF_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

(* (P + iQ)/(iw) - (P - iQ)/(iw) = 2 Q/w  (the endpoint combination).        *)
let COMPLEX_FRAC_COMBINE = prove
 (`!P Q w. ~(w = Cx(&0))
     ==> (P + ii * Q) / (ii * w) - (P + ii * (--Q)) / (ii * w) =
         Cx(&2) * Q / w`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_SUB_RDISTRIB] THEN
  SUBGOAL_THEN `(P + ii * Q) - (P + ii * --Q) = ii * (Cx(&2) * Q)`
    SUBST1_TAC THENL
   [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
  SUBGOAL_THEN `ii * Cx(&2) * Q * inv ii = Cx(&2) * Q` SUBST1_TAC THENL
   [MP_TAC II_NZ THEN CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC II_NZ THEN CONV_TAC COMPLEX_FIELD);;

(* The endpoint value  e^{iab}/(ib) - e^{-iab}/(ib) = 2 sin(ab)/b.           *)
let CEXP_ENDPOINT_ID = prove
 (`!a b. ~(b = &0)
     ==> cexp(ii * Cx b * Cx a) / (ii * Cx b) -
         cexp(ii * Cx b * Cx(--a)) / (ii * Cx b) =
         Cx(&2 * sin(a * b) / b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ii * Cx b * Cx a = ii * Cx(a * b) /\
                ii * Cx b * Cx(--a) = ii * Cx(--(a * b))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[CX_NEG; CX_MUL] THEN CONJ_TAC THEN SIMPLE_COMPLEX_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS] THEN
  REWRITE_TAC[SIN_NEG; COS_NEG] THEN
  MP_TAC(ISPECL [`Cx(cos(a*b))`; `Cx(sin(a*b))`; `Cx b`]
    COMPLEX_FRAC_COMBINE) THEN
  ANTS_TAC THENL [REWRITE_TAC[CX_INJ] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CX_NEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM CX_DIV; GSYM CX_MUL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* INT_{[-a,a]} e^{iby} dy = 2 sin(ab)/b.                                    *)
let CEXP_INTERVAL_INTEGRAL = prove
 (`!a b. &0 <= a /\ ~(b = &0)
     ==> integral (interval[lift(--a), lift a])
                  (\y. cexp(ii * Cx b * Cx(drop y))) =
         Cx(&2 * sin(a * b) / b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL
    [`\y. cexp(ii * Cx b * Cx(drop y)) / (ii * Cx b)`;
     `\y. cexp(ii * Cx b * Cx(drop y))`;
     `lift(--a)`; `lift a`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[LIFT_DROP; DROP_NEG] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      ASM_SIMP_TAC[CEXP_IB_VECTOR_DERIV]];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; DROP_NEG] THEN
  ASM_SIMP_TAC[CEXP_ENDPOINT_ID]);;


(* ========================================================================= *)
(* SECTION 2. Dirichlet sine integral and inversion foundations              *)
(* (Fremlin 283D-283J).                                                      *)
(* Underpins Fourier INVERSION and thence the Schwartz theory (284) and      *)
(* Plancherel.                                                               *)
(* (Uses DIRICHLET_KERNEL* / RIEMANN_LEBESGUE* from 100/fourier.ml, and      *)
(* REAL_SECOND_MEAN_VALUE_THEOREM = Fremlin 224J.)                           *)
(*                                                                           *)
(* Foundation: the "sinc" function (sin x / x extended by 1 at 0) is smooth/ *)
(* continuous, so its running integral F(a) = INT_0^a sin/x is well-behaved. *)
(* Fremlin 283D: F(a) -> pi/2 as a -> +inf, and |INT_a^b sin(cx)/x| <= K     *)
(* uniformly (the two facts the inversion theorem 283F consumes).            *)
(* ========================================================================= *)

let sinc = new_definition
 `sinc x = if x = &0 then &1 else sin x / x`;;


(* sinc is continuous everywhere (the singularity at 0 is removable).        *)
let SINC_CONTINUOUS = prove
 (`!x. sinc real_continuous atreal x`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN
    SUBGOAL_THEN `sinc(&0) = &1` SUBST1_TAC THENL
     [REWRITE_TAC[sinc]; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\x. sin x / x` THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[sinc] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REALLIM_SIN_OVER_X]];
    MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\x. sin x / x` THEN EXISTS_TAC `abs x` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x':real` THEN DISCH_TAC THEN REWRITE_TAC[sinc] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN
      REWRITE_TAC[REAL_CONTINUOUS_AT_SIN; REAL_CONTINUOUS_AT_ID] THEN
      ASM_REWRITE_TAC[]]]);;

(* sinc is continuous on every interval, hence integrable there.             *)
let SINC_CONTINUOUS_ON = prove
 (`!s. sinc real_continuous_on s`,
  GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  REWRITE_TAC[SINC_CONTINUOUS]);;

let SINC_INTEGRABLE = prove
 (`!a b. sinc real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC[SINC_CONTINUOUS_ON]);;

(* t |-> sinc(c t) is continuous (composition), hence integrable on any      *)
(* interval.                                                                 *)
let SINC_STRETCH_INTEGRABLE = prove
 (`!c a b. (\t. sinc(c * t)) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  SUBGOAL_THEN `(\t. sinc(c * t)) = sinc o (\t. c * t)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN
  REWRITE_TAC[SINC_CONTINUOUS] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_AT_ID]);;

(* Hence sin(c t)/t is integrable on any interval, for c > 0 (= c sinc(c     *)
(* t)).                                                                      *)
let SIN_STRETCH_OVER_X_INTEGRABLE = prove
 (`!c a b. &0 < c ==> (\t. sin(c * t) / t) real_integrable_on
   real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC [`\t. c * sinc(c * t)`; `{&0}`] THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_SING] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[sinc] THEN COND_CASES_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[REAL_ENTIRE] THEN
    TRY(ASM_REAL_ARITH_TAC) THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_FIELD
      `~(c = &0) /\ ~(x = &0) ==> sin (c * x) / x = c * sin (c * x) / (c * x)`)
        THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
      REWRITE_TAC[SINC_STRETCH_INTEGRABLE]]);;

(* ------------------------------------------------------------------------- *)
(* 283D(b): the uniform bound |INT_a^b sin(cx)/x| <= K.  Core estimate here: *)
(* for 0 < a <= b,  |INT_a^b sin x/x dx| <= 2/a + 2/b, via the second mean   *)
(* value theorem (Fremlin 224J) with the decreasing weight 1/x.              *)
(* ------------------------------------------------------------------------- *)

let SIN_MVT = prove
 (`!a b. &0 < a /\ a <= b
   ==> ?c. c IN real_interval[a,b] /\
           real_integral (real_interval[a,b]) (\x. --(inv x) * sin x) =
           --(inv a) * real_integral (real_interval[a,c]) sin +
           --(inv b) * real_integral (real_interval[c,b]) sin`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sin`; `\x:real. --(inv x)`; `a:real`; `b:real`]
    REAL_SECOND_MEAN_VALUE_THEOREM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_INTERVAL_NE_EMPTY] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_SIN];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_NEG2] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_REAL_INTERVAL])) THEN
        ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c:real` THEN
    ASM_REWRITE_TAC[]]);;

let REAL_INTEGRAL_SIN = prove
 (`!a c. a <= c ==> real_integral (real_interval[a,c]) sin = cos a - cos c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`\x. --(cos x)`; `sin`; `a:real`; `c:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
      REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `--cos c - --cos a = cos a - cos c`]]);;

let SIN_OVER_X_INTEGRABLE = prove
 (`!a b. &0 < a ==> (\x. sin x / x) real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN
  REWRITE_TAC[REAL_CONTINUOUS_AT_SIN; REAL_CONTINUOUS_AT_ID] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_REAL_ARITH_TAC);;

let NEG_INV_SIN_INTEGRAL = prove
 (`!a b. &0 < a
   ==> real_integral (real_interval[a,b]) (\x. --(inv x) * sin x) =
       --(real_integral (real_interval[a,b]) (\x. sin x / x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. --(inv x) * sin x) = (\x. --(sin x / x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[real_div] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_NEG THEN MATCH_MP_TAC SIN_OVER_X_INTEGRABLE THEN
    ASM_REWRITE_TAC[]);;

let ABS_MUL_BOUND = prove
 (`!i d:real. &0 < i /\ abs d <= &2 ==> abs(i * d) <= &2 * i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs i * &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    SUBGOAL_THEN `abs i = i` SUBST1_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC]);;

let SIN_OVER_X_BOUND = prove
 (`!a b. &0 < a /\ a <= b
   ==> abs(real_integral (real_interval[a,b]) (\x. sin x / x)) <= &2 * inv a +
     &2 * inv b`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:real`;`b:real`] SIN_MVT) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] NEG_INV_SIN_INTEGRAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:real`; `c:real`] REAL_INTEGRAL_SIN) THEN ANTS_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`c:real`; `b:real`] REAL_INTEGRAL_SIN) THEN ANTS_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `real_integral (real_interval[a,b]) (\x. sin x / x) =
                inv a * (cos a - cos c) + inv b * (cos c - cos b)` SUBST1_TAC
                  THENL
   [REPEAT(FIRST_X_ASSUM(fun th -> if is_eq(concl th) then MP_TAC th else
     ALL_TAC)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv a /\ &0 < inv b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `a:real` COS_BOUNDS) THEN MP_TAC(SPEC `b:real` COS_BOUNDS) THEN
  MP_TAC(SPEC `c:real` COS_BOUNDS) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs u <= &2 * inv a /\ abs v <= &2 * inv b ==> abs(u + v) <= &2 * inv a +
     &2 * inv b`) THEN
  CONJ_TAC THEN MATCH_MP_TAC ABS_MUL_BOUND THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 283D(a): the VALUE.  lim_{a->inf} INT_{-a}^a sin x/x dx = pi (so the      *)
(* one-sided limit is pi/2).  On the critical path to 283I inversion (hence  *)
(* 284C Schwartz inversion and 284O Plancherel).                             *)
(*                                                                           *)
(* Route (avoids Fremlin's abstract gamma-existence Cauchy step): prove the  *)
(* two-sided running integral G(a) = INT_{-a}^a sin/x -> pi directly at      *)
(* posinfinity, anchoring the value on the subsequence a = pi(n+1/2) via the *)
(* Dirichlet kernel, and controlling the tail with SIN_OVER_X_BOUND.         *)
(* ------------------------------------------------------------------------- *)

(* sin x / x is integrable on EVERY interval (unconditional: = sinc off      *)
(* {0}).                                                                     *)
let SIN_OVER_X_INTEGRABLE_UNIV = prove
 (`!a b. (\x. sin x / x) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`sinc`; `\x. sin x / x`; `{&0}`; `real_interval[a:real,b]`]
    REAL_INTEGRABLE_SPIKE) THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING; SINC_INTEGRABLE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_DIFF; IN_SING; sinc] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[]);;

(* Change of variables x = c t (c > 0): stretch [--p,p] by c.                *)
let SIN_OVER_X_STRETCH_IMAGE = prove
 (`!c p. &0 < c /\ &0 <= p
     ==> IMAGE (\x. inv c * x) (real_interval[--(c*p),c*p]) =
       real_interval[--p,p]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ &0 <= c * p` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN
     ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_STRETCH_REAL_INTERVAL] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[REAL_INTERVAL_EQ_EMPTY]) THEN
     ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv c` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(c = &0) ==> inv c * (c * p) = p`;
               REAL_FIELD `~(c = &0) ==> inv c * --(c * p) = --p`]);;

(* INT_{-c p}^{c p} sin x/x dx = INT_{-p}^p sin(c t)/t dt, for c > 0, p >=   *)
(* 0. Stretch x = c t via HAS_REAL_INTEGRAL_STRETCH gives sin(ct)/(ct);      *)
(* scale by c (LMUL) and repair the integrand at 0 (SPIKE) to reach          *)
(* sin(ct)/t.                                                                *)
let SIN_OVER_X_SUBST = prove
 (`!c p. &0 < c /\ &0 <= p
     ==> real_integral (real_interval[--(c*p), c*p]) (\x. sin x / x) =
         real_integral (real_interval[--p,p]) (\t. sin(c * t) / t)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`\x. sin x / x`;
                 `real_integral (real_interval[--(c*p),c*p]) (\x. sin x / x)`;
                 `--(c*p):real`; `c*p:real`;
                   `c:real`] HAS_REAL_INTEGRAL_STRETCH) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL; REAL_LT_IMP_NZ;
    SIN_OVER_X_INTEGRABLE_UNIV;
               SIN_OVER_X_STRETCH_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `c * inv(abs c) *
     real_integral (real_interval[--(c*p),c*p]) (\x. sin x / x) =
     real_integral (real_interval[--(c*p),c*p]) (\x. sin x / x)`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `inv(abs c) = inv c` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC [`\x. c * sin (c * x) / (c * x)`; `{&0}`] THEN
  ASM_REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
  REWRITE_TAC[IN_DIFF; IN_SING] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(c = &0) /\ ~(x = &0) ==> sin (c * x) / x = c * sin (c * x) / (c * x)`)
     THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Dirichlet-kernel comparison function phi(t) = 1/t - 1/(2 sin(t/2)),   *)
(* extended by 0 at t = 0.  Near 0 the two singular terms cancel; the point  *)
(* is that phi is BOUNDED and MEASURABLE on [--pi,pi], hence abs-integrable. *)
(* This is what lets Riemann-Lebesgue kill INT sin((n+1/2)t) phi(t) dt.      *)
(* The Taylor estimates SIN_SUB_X_BOUND, SIN_OVER_X_SUB1_BOUND,              *)
(* SIN_LOWER_BOUND_HALF and INV_SIN_SUB_INV_BOUND are provided by            *)
(* 100/fourier.ml (loaded above).                                            *)
(* ------------------------------------------------------------------------- *)

(* abs(sin u) = sin|u|  when |u| <= pi  (sin is odd and >= 0 on [0,pi]).     *)
let ABS_SIN_EQ = prove
 (`!u. abs u <= pi ==> abs(sin u) = sin(abs u)`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `&0 <= u` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= u ==> abs u = u`] THEN
    REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SIN_POS_PI_LE THEN
      ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= u) ==> abs u = --u`; SIN_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH `s <= &0 ==> abs s = --s`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --(sin u) ==> sin u <= &0`) THEN
    REWRITE_TAC[GSYM SIN_NEG] THEN MATCH_MP_TAC SIN_POS_PI_LE THEN
      ASM_REAL_ARITH_TAC]);;

(* Away from 0:  sin(1/2) <= |sin(t/2)|  when 1 <= |t| <= pi.                *)
let SIN_HALF_LOWER_BOUND = prove
 (`!t. &1 <= abs t /\ abs t <= pi ==> sin(&1 / &2) <= abs(sin(t / &2))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(sin(t / &2)) = sin(abs(t / &2))` SUBST1_TAC THENL
   [MATCH_MP_TAC ABS_SIN_EQ THEN MP_TAC PI_APPROX_32 THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC SIN_MONO_LE THEN MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC);;

(* phi(t) = 1/t - 1/(2 sin(t/2)) is MEASURABLE on [--pi,pi]:  each term is
   1/g   *)
(* with g continuous and vanishing only on a countable (negligible) set.     *)
let DIRICHLET_PHI_MEASURABLE = prove
 (`(\t. inv t - inv(&2 * sin(t / &2))) real_measurable_on
   real_interval[--pi,pi]`,
  MATCH_MP_TAC REAL_MEASURABLE_ON_SUB THEN CONJ_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV) [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
  MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
  SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
           REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
           REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
             REAL_CLOSED_UNIV] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
    MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
      MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `IMAGE (\n. &2 * n * pi) integer` THEN CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_IMAGE THEN
       REWRITE_TAC[COUNTABLE_INTEGER]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:real` THEN
    ASM_CASES_TAC `sin(x / &2) = &0` THENL
     [ALL_TAC; ASM_REWRITE_TAC[REAL_ENTIRE] THEN
       CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    DISCH_TAC THEN MP_TAC(SPEC `x / &2` SIN_EQ_0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `n:real` THEN ASM_REWRITE_TAC[IN] THEN ASM_REAL_ARITH_TAC]);;

(* phi is BOUNDED on [--pi,pi]:  |phi(t)| <= 2 + 2/sin(1/2).  Near 0 the     *)
(* singular terms cancel (INV_SIN_SUB_INV_BOUND); away from 0 both are
   bounded.  *)
let DIRICHLET_PHI_BOUND = prove
 (`!t. t IN real_interval[--pi,pi]
       ==> abs(inv t - inv(&2 * sin(t / &2))) <= &2 + &2 * inv(sin(&1 / &2))`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &2 * inv(sin(&1 / &2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SIN_POS_PI_LE THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&0) - inv(&2 * sin(&0 / &2)) = &0` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO; SIN_0; REAL_MUL_RZERO;
       REAL_INV_0] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `abs t <= &1` THENL
   [SUBGOAL_THEN `~(sin(t / &2) = &0)` ASSUME_TAC THENL
     [MP_TAC(SPEC `t / &2` SIN_EQ_0_PI) THEN MP_TAC PI_APPROX_32 THEN
       ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(t = &0) /\ ~(sin(t / &2) = &0)
      ==> inv t - inv(&2 * sin(t / &2)) =
          --(&1 / &2) * (inv(sin(t / &2)) - inv(t / &2))`] THEN
    MP_TAC(SPEC `t / &2` INV_SIN_SUB_INV_BOUND) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `sin(&1 / &2) <= abs(sin(t / &2))` ASSUME_TAC THENL
     [MATCH_MP_TAC SIN_HALF_LOWER_BOUND THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sin(&1 / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_APPROX_32 THEN
       REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(inv t) <= &1` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
       ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
      `abs(inv(&2 * sin(t / &2))) <= inv(sin(&1 / &2))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_INV; REAL_ABS_MUL; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * sin(&1 / &2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* Hence phi is absolutely integrable on [--pi,pi] (bounded x measurable).   *)
let DIRICHLET_PHI_ABSINT = prove
 (`(\t. inv t - inv(&2 * sin(t / &2))) absolutely_real_integrable_on
   real_interval[--pi,pi]`,
  SUBGOAL_THEN
   `(\t. (inv t - inv(&2 * sin(t / &2))) * &1) absolutely_real_integrable_on
    real_interval[--pi,pi]`
   MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    REWRITE_TAC[DIRICHLET_PHI_MEASURABLE;
      ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN
    EXISTS_TAC `&2 + &2 * inv(sin(&1 / &2)) + &1` THEN CONJ_TAC THENL
     [MP_TAC(SPEC `&0` DIRICHLET_PHI_BOUND) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
       [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` DIRICHLET_PHI_BOUND) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_RID]]);;

(* The two summands of sin((n+1/2)t)/t = sin(...) phi + sin(...)/(2          *)
(* sin(t/2)) are each integrable on [--pi,pi].                               *)
let DIRICHLET_SINPHI_INTEGRABLE = prove
 (`!n. (\t. sin((&n + &1 / &2) * t) * (inv t - inv(&2 * sin(t / &2))))
       real_integrable_on real_interval[--pi,pi]`,
  GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  REWRITE_TAC[DIRICHLET_PHI_ABSINT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL] THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[SIN_BOUND]]);;

let DIRICHLET_SININV_INTEGRABLE = prove
 (`!n. (\t. sin((&n + &1 / &2) * t) / (&2 * sin(t / &2)))
       real_integrable_on real_interval[--pi,pi]`,
  GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC [`dirichlet_kernel n`; `{&0}`] THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_SING] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[dirichlet_kernel];
    MP_TAC(SPEC `n:num` HAS_REAL_INTEGRAL_DIRICHLET_KERNEL) THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* The Dirichlet-kernel integral value in sin/(2 sin) form:  = pi for all n. *)
let DIRICHLET_SININV_VALUE = prove
 (`!n. real_integral (real_interval[--pi,pi])
         (\t. sin((&n + &1 / &2) * t) / (&2 * sin(t / &2))) = pi`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real. &1`; `n:num`; `real_interval[--pi,pi]`]
    REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[ETA_AX; HAS_REAL_INTEGRAL_DIRICHLET_KERNEL]);;

(* ------------------------------------------------------------------------- *)
(* The sequential Dirichlet limit:  INT_{-pi}^pi sin((n+1/2)t)/t dt -> pi.   *)
(* Split sin((n+1/2)t)/t = sin(...) phi(t) + sin(...)/(2 sin(t/2)); the
   first  *)
(* integral -> 0 by Riemann-Lebesgue (phi abs-integrable), the second = pi.  *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_SINE_LIMIT_SEQ = prove
 (`((\n. real_integral (real_interval[--pi,pi])
                       (\t. sin((&n + &1 / &2) * t) / t))
    ---> pi) sequentially`,
  SUBGOAL_THEN
   `!n. real_integral (real_interval[--pi,pi])
                      (\t. sin((&n + &1 / &2) * t) / t) =
        real_integral (real_interval[--pi,pi])
          (\t. sin((&n + &1 / &2) * t) * (inv t - inv(&2 * sin(t / &2)))) + pi`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `real_integral (real_interval[--pi,pi])
                    (\t. sin((&n + &1 / &2) * t) / t) =
      real_integral (real_interval[--pi,pi])
        (\t. sin((&n + &1 / &2) * t) * (inv t - inv(&2 * sin(t / &2))) +
             sin((&n + &1 / &2) * t) / (&2 * sin(t / &2)))`
     SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[real_div;
                  REAL_ARITH `!s a b:real. s * (a - b) + s * b = s * a`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_ADD; DIRICHLET_SINPHI_INTEGRABLE;
                 DIRICHLET_SININV_INTEGRABLE] THEN
    REWRITE_TAC[DIRICHLET_SININV_VALUE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
    `\n. real_integral (real_interval[--pi,pi])
          (\t. sin((&n + &1 / &2) * t) * (inv t - inv(&2 * sin(t / &2))))`;
    `\n:num. pi`; `&0`; `pi`] REALLIM_ADD) THEN
  REWRITE_TAC[REALLIM_CONST; REAL_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
  REWRITE_TAC[DIRICHLET_PHI_ABSINT]);;

(* ------------------------------------------------------------------------- *)
(* Upgrade the sequential limit to the continuous one at +infinity.  Two     *)
(* facts: sin x/x is EVEN so G(a) = INT_{-a}^a = 2 INT_0^a; and G on the     *)
(* samples a = (n+1/2)pi equals the sin((n+1/2)t)/t integral
   (SIN_OVER_X_SUBST *)
(* with c = n+1/2), which -> pi.  The tail bound SIN_OVER_X_BOUND fills in.  *)
(* ------------------------------------------------------------------------- *)

(* sin x/x is even:  INT_{-a}^0 sin x/x = INT_0^a sin x/x.                   *)
let SIN_OVER_X_REFLECT_HALF = prove
 (`!a. real_integral (real_interval[--a,&0]) (\x. sin x / x) =
       real_integral (real_interval[&0,a]) (\x. sin x / x)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\x. sin x / x`; `&0:real`; `a:real`]
    REAL_INTEGRAL_REFLECT) THEN
  REWRITE_TAC[REAL_NEG_0; SIN_NEG; real_div; REAL_INV_NEG; REAL_NEG_MUL2] THEN
  REWRITE_TAC[GSYM real_div] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* Hence the two-sided integral is twice the one-sided:  G(a) = 2 INT_0^a.   *)
let SIN_OVER_X_TWO_SIDED = prove
 (`!a. &0 <= a
       ==> real_integral (real_interval[--a,a]) (\x. sin x / x) =
           &2 * real_integral (real_interval[&0,a]) (\x. sin x / x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. sin x / x`; `--a:real`; `a:real`; `&0:real`]
    REAL_INTEGRAL_COMBINE) THEN
  ASM_SIMP_TAC[SIN_OVER_X_INTEGRABLE_UNIV;
               REAL_ARITH `&0 <= a ==> --a <= &0`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SIN_OVER_X_REFLECT_HALF] THEN
  REAL_ARITH_TAC);;

(* The samples:  INT_{-(n+1/2)pi}^{(n+1/2)pi} sin x/x =
   INT_{-pi}^pi sin((n+1/2)t)/t. *)
let SIN_OVER_X_SAMPLE = prove
 (`!n. real_integral
         (real_interval[--((&n + &1 / &2) * pi), (&n + &1 / &2) * pi])
         (\x. sin x / x) =
       real_integral (real_interval[--pi,pi])
                     (\t. sin((&n + &1 / &2) * t) / t)`,
  GEN_TAC THEN MATCH_MP_TAC SIN_OVER_X_SUBST THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 / &2` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[REAL_LE_ADDL; REAL_POS]];
    MP_TAC PI_POS THEN REAL_ARITH_TAC]);;

(* Hence G on the samples tends to pi.                                       *)
let SIN_OVER_X_SAMPLE_LIMIT = prove
 (`((\n. real_integral
           (real_interval[--((&n + &1 / &2) * pi), (&n + &1 / &2) * pi])
           (\x. sin x / x)) ---> pi) sequentially`,
  REWRITE_TAC[SIN_OVER_X_SAMPLE; DIRICHLET_SINE_LIMIT_SEQ]);;

(* Tail control:  0 < b <= a ==> |G(a) - G(b)| <= 8/b  (G(a) = INT_{-a}^a).  *)
(* Both endpoints share the small lower endpoint b, so the difference is a   *)
(* single tail INT_b^a bounded by SIN_OVER_X_BOUND -- no nearest-sample
   needed.  *)
let SIN_OVER_X_TAIL_DIFF = prove
 (`!a b. &0 < b /\ b <= a
   ==> abs(real_integral (real_interval[--a,a]) (\x. sin x / x) -
           real_integral (real_interval[--b,b]) (\x. sin x / x)) <= &8 / b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= a /\ &0 <= b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SIN_OVER_X_TWO_SIDED] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,a]) (\x. sin x / x) -
    real_integral (real_interval[&0,b]) (\x. sin x / x) =
    real_integral (real_interval[b,a]) (\x. sin x / x)`
   (fun th ->
        ONCE_REWRITE_TAC[REAL_ARITH `&2 * x - &2 * y = &2 * (x - y)`] THEN
        REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`\x. sin x / x`; `&0:real`; `a:real`; `b:real`]
      REAL_INTEGRAL_COMBINE) THEN
    ASM_SIMP_TAC[SIN_OVER_X_INTEGRABLE_UNIV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  MP_TAC(SPECL [`b:real`; `a:real`] SIN_OVER_X_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv a <= inv b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&8 / b = &2 * (&2 * inv b + &2 * inv b)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 283D(a), first form:  lim_{a->+inf} INT_{-a}^a sin x/x dx = pi.           *)
(* Anchor at a fixed sample b = (N+1/2)pi with N large enough that both      *)
(* |G(b) - pi| < e/2 (sequential limit) and 8/b < e/2 (b >= 16/e); then for  *)
(* every a >= b, |G(a) - pi| <= |G(a) - G(b)| + |G(b) - pi| <= 8/b + e/2
   < e.  *)
(* ------------------------------------------------------------------------- *)

let SIN_OVER_X_LIMIT_POSINF = prove
 (`((\a. real_integral (real_interval[--a,a]) (\x. sin x / x)) ---> pi)
   at_posinfinity`,
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN
  MP_TAC SIN_OVER_X_SAMPLE_LIMIT THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC) THEN
  MP_TAC(SPEC `&16 / e` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
  EXISTS_TAC `(&(N1 + N2) + &1 / &2) * pi` THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
  ABBREV_TAC `b = (&(N1 + N2) + &1 / &2) * pi` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MP_TAC PI_POS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `b:real`] SIN_OVER_X_TAIL_DIFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&16 / e <= b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(N1+N2) + &1 / &2` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [REAL_ARITH_TAC; MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 / b <= e / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&16 <= b * e` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Corollary (Fremlin 283D(a) as stated):  lim_{a->+inf} INT_0^a sin x/x =
   pi/2. *)
let SIN_OVER_X_LIMIT_POSINF_HALF = prove
 (`((\a. real_integral (real_interval[&0,a]) (\x. sin x / x)) ---> pi / &2)
   at_posinfinity`,
  MP_TAC SIN_OVER_X_LIMIT_POSINF THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `e:real` THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` ASSUME_TAC) THEN
  EXISTS_TAC `abs B + &1` THEN X_GEN_TAC `a:real` THEN
  REWRITE_TAC[real_ge] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SIN_OVER_X_TWO_SIDED] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The frequency-scaled Dirichlet limit needed by 283E:                      *)
(*   lim_{a->inf} INT_{-a}^a sin(b x)/x dx = pi (b>0), -pi (b<0), 0 (b=0).   *)
(* For b>0, substitute u = b x (SIN_OVER_X_SUBST) so the integral becomes
   the  *)
(* plain one over [-ba, ba] with ba -> +inf.  b<0 is the odd reflection; b=0 *)
(* trivial.                                                                  *)
(* ------------------------------------------------------------------------- *)

let SIN_BX_OVER_X_LIMIT_POS = prove
 (`!b. &0 < b
   ==> ((\a. real_integral (real_interval[--a,a]) (\t. sin(b * t) / t)) --->
        pi)
       at_posinfinity`,
  REPEAT STRIP_TAC THEN
  MP_TAC SIN_OVER_X_LIMIT_POSINF THEN REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` ASSUME_TAC) THEN
  EXISTS_TAC `(abs B + &1) / b` THEN X_GEN_TAC `a:real` THEN
  REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(abs B + &1) / b` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real) * a >= B` ASSUME_TAC THENL
   [REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs B + &1` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MP_TAC(ISPECL [`(abs B + &1) / b`; `a:real`; `b:real`] REAL_LE_RMUL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[REAL_MUL_SYM]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[--a,a]) (\t. sin(b * t) / t) =
    real_integral (real_interval[--(b * a), b * a]) (\x. sin x / x)`
   SUBST1_TAC THENL
   [MP_TAC(SPECL [`b:real`; `a:real`] SIN_OVER_X_SUBST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `forall x. x >= B
      ==> abs (real_integral (real_interval [--x,x]) (\x. sin x / x) - pi)
          < e` THEN
  DISCH_THEN(MP_TAC o SPEC `(b:real) * a`) THEN ASM_REWRITE_TAC[]);;

(* Pointwise reflection: for b<0, INT sin(bt)/t = -INT sin(-b t)/t (-b>0).   *)
let SIN_BX_OVER_X_REFLECT = prove
 (`!b a. b < &0
     ==> real_integral (real_interval[--a,a]) (\t. sin(b * t) / t) =
         --(real_integral (real_interval[--a,a]) (\t. sin(--b * t) / t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. sin(--b * t) / t`; `real_interval[--a,a]`]
    REAL_INTEGRAL_NEG) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SIN_STRETCH_OVER_X_INTEGRABLE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_LNEG; SIN_NEG; real_div] THEN REAL_ARITH_TAC);;

(* sin(bx)/x is odd in b, giving the full sign-cased limit that 283E         *)
(* consumes.                                                                 *)
let SIN_BX_OVER_X_LIMIT = prove
 (`!b. ((\a. real_integral (real_interval[--a,a]) (\t. sin(b * t) / t)) --->
        (if &0 < b then pi else if b < &0 then --pi else &0)) at_posinfinity`,
  GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `&0 < b \/ b < &0 \/ b = &0`) THENL
   [ASM_SIMP_TAC[SIN_BX_OVER_X_LIMIT_POS];
    ASM_SIMP_TAC[REAL_ARITH `b < &0 ==> ~(&0 < b)`; SIN_BX_OVER_X_REFLECT] THEN
    MATCH_MP_TAC REALLIM_NEG THEN MATCH_MP_TAC SIN_BX_OVER_X_LIMIT_POS THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    REWRITE_TAC[REAL_MUL_LZERO; SIN_0; real_div; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_INTEGRAL_0; REALLIM_CONST]]);;

(* ========================================================================= *)
(* SECTION 3. Riemann-Lebesgue lemma on the whole real line                  *)
(* (Fremlin 283Cg / 282E).                                                   *)
(*   INT_R h(u) sin(a u) du -> 0  as a -> +inf,  for h in L^1(R).            *)
(* This ingredient of the pointwise Fourier inversion theorem 283I is not    *)
(* already in HOL Light: the base library's Riemann-Lebesgue lemma is         *)
(* PERIODIC (100/fourier.ml, on [-pi,pi], via Bessel/orthonormal systems) and *)
(* does not transfer to the line.                                            *)
(*                                                                           *)
(* Route: L^1 density by continuous bounded functions, the                   *)
(* |INT h sin(au)| <= INT|h| transfer, and the                               *)
(* half-period translation trick, which needs L^1-continuity of translation. *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Whole-line translation invariance of the real integral (foundational).    *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_INTEGRAL_TRANSLATION_UNIV = prove
 (`!H c i. ((\u. H(u + c)) has_real_integral i) (:real) <=>
           (H has_real_integral i) (:real)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral; IMAGE_LIFT_UNIV] THEN
  SUBGOAL_THEN `lift o (\u. H(u + c)) o drop =
                (\x. (lift o H o drop)(lift c + x))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
    REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[HAS_INTEGRAL_TRANSLATION] THEN
  REWRITE_TAC[TRANSLATION_UNIV]);;

let REAL_INTEGRABLE_TRANSLATION_UNIV = prove
 (`!H c. (\u. H(u + c)) real_integrable_on (:real) <=>
         H real_integrable_on (:real)`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_TRANSLATION_UNIV]);;

let REAL_INTEGRAL_TRANSLATION_UNIV = prove
 (`!H c. real_integral (:real) (\u. H(u + c)) = real_integral (:real) H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_TRANSLATION_UNIV]);;

let ABSOLUTELY_REAL_INTEGRABLE_TRANSLATION_UNIV = prove
 (`!H c. (\u. H(u + c)) absolutely_real_integrable_on (:real) <=>
         H absolutely_real_integrable_on (:real)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; IMAGE_LIFT_UNIV] THEN
  SUBGOAL_THEN `lift o (\u. H(u + c)) o drop =
                (\x. (lift o H o drop)(lift c + x))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
    REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_TRANSLATION] THEN
  REWRITE_TAC[TRANSLATION_UNIV]);;

(* The abs-difference of an L^1 function and its translate is integrable.    *)
let ABS_DIFF_TRANSLATION_INTEGRABLE = prove
 (`!H c. H absolutely_real_integrable_on (:real)
     ==> (\u. abs(H(u + c) - H u)) real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ABS THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
  ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_TRANSLATION_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* L^1-CONTINUITY OF TRANSLATION (the analytic heart):  for H in L^1(R),     *)
(*   INT_R |H(u+c) - H(u)| du -> 0  as c -> 0.                               *)
(* Bridged from the vector CONTINUOUS_ON_ABSOLUTELY_INTEGRABLE_TRANSLATION_  *)
(* NORM (measure.ml) via the lift/drop <-> real_integral dictionary.         *)
(* ------------------------------------------------------------------------- *)

let REAL_TRANSLATION_CONTINUITY = prove
 (`!H. H absolutely_real_integrable_on (:real)
   ==> ((\c. real_integral (:real) (\u. abs(H(u + c) - H u))) ---> &0)
       (atreal(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o
    REWRITE_RULE[ABSOLUTELY_REAL_INTEGRABLE_ON; IMAGE_LIFT_UNIV]) THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP CONTINUOUS_ON_ABSOLUTELY_INTEGRABLE_TRANSLATION_NORM) THEN
  REWRITE_TAC[o_THM; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT] THEN
  REWRITE_TAC[REALLIM_ATREAL_AT; LIFT_NUM; TENDSTO_REAL; o_DEF] THEN
  SUBGOAL_THEN
   `(\a. integral (:real^1) (\x. lift(abs(H(drop(a + x)) - H(drop x))))) =
    (\x. lift(real_integral (:real) (\u. abs(H(u + drop x) - H u))))`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:real^1` THEN
  MP_TAC(SPECL [`H:real->real`; `drop(a:real^1)`]
    ABS_DIFF_TRANSLATION_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL th]) THEN
  REWRITE_TAC[IMAGE_LIFT_UNIV; LIFT_DROP] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[LIFT_DROP; DROP_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Assembling Riemann-Lebesgue via the half-period translation trick.        *)
(* H in L^1(R) => H(.) sin(a.) is absolutely integrable; the half-period     *)
(* identity  INT H(u)sin(au) = -INT H(u-pi/a)sin(au); hence 2 INT H sin(au)
   =  *)
(* INT (H(u)-H(u-pi/a)) sin(au), which is O(INT|H(u)-H(u-pi/a)|) -> 0.       *)
(* ------------------------------------------------------------------------- *)

(* H in L^1 => H(.) sin(a.) absolutely integrable (bounded x L^1).           *)
let FOURIER_SIN_ABSINT = prove
 (`!H a. H absolutely_real_integrable_on (:real)
     ==> (\u. H u * sin(a * u)) absolutely_real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    REWRITE_TAC[REAL_CLOSED_UNIV] THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[SIN_BOUND]]);;

(* sin(x - pi) = -sin x.                                                     *)
let SIN_SUB_PI = prove
 (`!x. sin(x - pi) = --sin x`,
  GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `x - pi = --pi + x`; SIN_ADD; SIN_NEG; COS_NEG;
              SIN_PI; COS_PI] THEN REAL_ARITH_TAC);;

(* The half-period identity.                                                 *)
let FOURIER_SIN_HALF_PERIOD = prove
 (`!H a. ~(a = &0) /\ H absolutely_real_integrable_on (:real)
     ==> real_integral (:real) (\u. H u * sin(a * u)) =
         --(real_integral (:real) (\u. H(u - pi / a) * sin(a * u)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\u. H(u) * sin(a * u)`; `--(pi / a)`]
    REAL_INTEGRAL_TRANSLATION_UNIV) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(\u. H (u + --(pi / a)) * sin (a * (u + --(pi / a)))) =
    (\u. --(H(u - pi / a) * sin(a * u)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real` THEN
    REWRITE_TAC[REAL_ARITH `u + --(pi / a) = u - pi / a`] THEN
    SUBGOAL_THEN `a * (u - pi / a) = (a * u) - pi` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
      SUBGOAL_THEN `a * (pi / a) = pi` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[SIN_SUB_PI; REAL_MUL_RNEG]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_NEG THEN
  ONCE_REWRITE_TAC[REAL_ARITH `u - pi / a = u + (--(pi / a))`] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC FOURIER_SIN_ABSINT THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_TRANSLATION_UNIV] THEN
  ASM_REWRITE_TAC[]);;

(* 2 INT H sin(au) = INT (H(u) - H(u-pi/a)) sin(au)  (from the half-period
   id). *)
let FOURIER_SIN_DOUBLE = prove
 (`!H a. ~(a = &0) /\ H absolutely_real_integrable_on (:real)
   ==> &2 * real_integral (:real) (\u. H u * sin(a * u)) =
       real_integral (:real) (\u. (H u - H(u - pi / a)) * sin(a * u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`H:real->real`; `a:real`] FOURIER_SIN_HALF_PERIOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `real_integral (:real) (\u. (H u - H(u - pi / a)) * sin(a * u)) =
    real_integral (:real) (\u. H u * sin(a * u)) -
    real_integral (:real) (\u. H(u - pi / a) * sin(a * u))`
   SUBST1_TAC THENL
   [REWRITE_TAC[REAL_SUB_RDISTRIB] THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THENL
     [MATCH_MP_TAC FOURIER_SIN_ABSINT THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `u - pi / a = u + --(pi / a)`] THEN
      MATCH_MP_TAC FOURIER_SIN_ABSINT THEN
      ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_TRANSLATION_UNIV]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* |INT (H(u)-H(u-pi/a)) sin(au)| <= INT |H(u)-H(u-pi/a)|  (|sin| <= 1).     *)
let FOURIER_SIN_DIFF_BOUND = prove
 (`!H a. H absolutely_real_integrable_on (:real)
   ==> abs(real_integral (:real) (\u. (H u - H(u - pi / a)) * sin(a * u))) <=
       real_integral (:real) (\u. abs(H u - H(u - pi / a)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
  SUBGOAL_THEN
   `(\u. H u - H(u - pi / a)) absolutely_real_integrable_on (:real)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `u - pi / a = u + --(pi / a)`] THEN
    ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_TRANSLATION_UNIV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC FOURIER_SIN_ABSINT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS; SIN_BOUND]]);;

(* ------------------------------------------------------------------------- *)
(* THE RIEMANN-LEBESGUE LEMMA on the real line (Fremlin 283Cg / 282E):       *)
(*   INT_R H(u) sin(a u) du -> 0  as a -> +inf,  for H in L^1(R).            *)
(* eps-B: translation-continuity gives delta for eps; take B = pi/delta + 1; *)
(* for a >= B, pi/a < delta, so 2|INT H sin(au)| = |INT (H(u)-H(u-pi/a))sin| *)
(* <= INT|H(u)-H(u-pi/a)| = INT|H(u-pi/a)-H(u)| < eps, whence |INT| < eps.   *)
(* ------------------------------------------------------------------------- *)

let RIEMANN_LEBESGUE_RLINE = prove
 (`!H. H absolutely_real_integrable_on (:real)
   ==> ((\a. real_integral (:real) (\u. H u * sin(a * u))) ---> &0)
       at_posinfinity`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_TRANSLATION_CONTINUITY) THEN
  REWRITE_TAC[REALLIM_ATREAL] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `pi / d + &1` THEN X_GEN_TAC `a:real` THEN
  REWRITE_TAC[real_ge] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN
    SUBGOAL_THEN `&0 < pi / d` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[PI_POS];
      ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `pi / a < d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `d * (pi / d + &1)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--(pi / a)`) THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `&0 < pi / a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < p ==> abs p = p`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`H:real->real`; `a:real`] FOURIER_SIN_DOUBLE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`H:real->real`; `a:real`] FOURIER_SIN_DIFF_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `real_integral (:real) (\u. abs(H u - H(u - pi / a))) =
    real_integral (:real) (\u. abs(H (u + --(pi / a)) - H u))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `u + --(pi / a) = u - pi / a`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* SECTION 4. Pointwise Fourier inversion (Fremlin 283H -> 283I -> 283J).    *)
(*   283H:  (1/sqrt(2pi)) INT_{-a}^a e^{ixy} fhat(y) dy                      *)
(*            = (1/pi) INT_R (sin a u / u) f(x-u) du (Fubini + 283D value)   *)
(*   283I:  if f is integrable over R and differentiable at x, the limit of  *)
(*          the above as a -> inf is f(x)  (Riemann-Lebesgue + 283Da).       *)
(*   283J:  if in addition fhat is integrable, f = (fhat) check.             *)
(* Uses the Riemann-Lebesgue lemma and the Dirichlet-integral facts (283I).  *)
(*                                                                           *)
(* 283H is a 2D Fubini over the strip [-a,a] x R; the inner integral is the  *)
(* oscillatory CEXP_INTERVAL_INTEGRAL.  Bookkeeping is at                    *)
(* real^(1,1)finite_sum                                                      *)
(* via pastecart (fstcart = frequency y in [-a,a], sndcart = space t).       *)
(* ========================================================================= *)

(* The frequency strip [-a,a] x R is lebesgue-measurable in R^2.             *)
let STRIP_MEASURABLE = prove
 (`!a. lebesgue_measurable
        {z:real^(1,1)finite_sum | drop(fstcart z) IN real_interval[--a,a]}`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `{z:real^(1,1)finite_sum | drop(fstcart z) IN real_interval[--a,a]} =
    (interval[lift(--a), lift a]) PCROSS (:real^1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM; PASTECART_IN_PCROSS;
               FSTCART_PASTECART; IN_UNIV; IN_INTERVAL_1;
               IN_REAL_INTERVAL; LIFT_DROP];
    REWRITE_TAC[LEBESGUE_MEASURABLE_PCROSS; LEBESGUE_MEASURABLE_INTERVAL;
                LEBESGUE_MEASURABLE_UNIV]]);;

(* The two exponential factors of the 283H integrand are continuous on R^2.  *)
let CEXP_FST_CONTINUOUS = prove
 (`!x. (\z:real^(1,1)finite_sum. cexp(ii * Cx x * Cx(drop(fstcart z))))
       continuous_on (:real^(1,1)finite_sum)`,
  GEN_TAC THEN SUBGOAL_THEN
   `(\z:real^(1,1)finite_sum. cexp(ii * Cx x * Cx(drop(fstcart z)))) =
    cexp o (\z. (ii * Cx x) * Cx(drop(fstcart z)))`
   SUBST1_TAC THENL [REWRITE_TAC[o_DEF; COMPLEX_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART]);;

let CEXP_FSTSND_CONTINUOUS = prove
 (`(\z:real^(1,1)finite_sum.
        cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))))
   continuous_on (:real^(1,1)finite_sum)`,
  SUBGOAL_THEN
   `(\z:real^(1,1)finite_sum.
        cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z))))) =
    cexp o (\z. --(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z))))`
   SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

(* The 283H strip integrand is measurable on R^2, given f measurable on R.   *)
let STRIP_INTEGRAND_MEASURABLE = prove
 (`!(f:real->complex) a x.
     (\z. f(drop z)) measurable_on (:real^1)
     ==> (\z:real^(1,1)finite_sum.
            if drop(fstcart z) IN real_interval[--a,a]
            then cexp(ii * Cx x * Cx(drop(fstcart z))) *
                 cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
                 f(drop(sndcart z))
            else vec 0) measurable_on (:real^(1,1)finite_sum)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_CASES THEN
  REWRITE_TAC[STRIP_MEASURABLE; MEASURABLE_ON_0] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    REWRITE_TAC[CEXP_FST_CONTINUOUS];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    REWRITE_TAC[CEXP_FSTSND_CONTINUOUS];
    MP_TAC(INST_TYPE [`:1`,`:M`; `:1`,`:N`]
             (ISPEC `\z. (f:real->complex)(drop z)`
                    MEASURABLE_ON_COMPOSE_SNDCART)) THEN
    ASM_REWRITE_TAC[o_DEF; ETA_AX]]);;

(* The strip integrand has modulus |f(t)| (both exponential factors have     *)
(* modulus 1).                                                               *)
let STRIP_INTEGRAND_NORM = prove
 (`!x y t (f:real->complex).
     norm(cexp(ii * Cx x * Cx y) * cexp(--(ii * Cx y * Cx t)) * f t) =
     norm(f t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN
   `norm(cexp(ii * Cx x * Cx y)) = &1 /\
    norm(cexp(--(ii * Cx y * Cx t))) = &1`
   (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `ii * Cx x * Cx y = ii * Cx(x * y)` SUBST1_TAC THENL
     [REWRITE_TAC[CX_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC;
      REWRITE_TAC[NORM_CEXP_II]];
    REWRITE_TAC[FOURIER_KERNEL_NORM]]);;

(* The modulation integrand y |-> e^{-i d y} f(y) is absolutely integrable   *)
(* (bounded modulus-1 factor x an L^1 function).  This is the nonzero
   t-slice of  *)
(* the 283H strip integrand at a fixed frequency d, up to a constant factor. *)
let FOURIER_MODULATION_ABSINT = prove
 (`!(f:real->complex) d.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> (\y. cexp(--(ii * Cx d * Cx(drop y))) * f(drop y))
         absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`;
                 `\y:real^1. cexp(--(ii * Cx d * Cx(drop y)))`;
                 `\y:real^1. (f:real->complex)(drop y)`; `(:real^1)`]
    ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    SUBGOAL_THEN `(\y:real^1. cexp(--(ii * Cx d * Cx(drop y)))) =
                  cexp o (\y. --((ii * Cx d) * Cx(drop y)))`
     SUBST1_TAC THENL [REWRITE_TAC[o_DEF; COMPLEX_MUL_ASSOC]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
    REWRITE_TAC[CONTINUOUS_ON_ID];
    REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
    X_GEN_TAC `y:real^1` THEN
    SUBGOAL_THEN `--(ii * Cx d * Cx(drop y)) = ii * Cx(--(d * drop y))`
     SUBST1_TAC THENL
     [REWRITE_TAC[CX_NEG; CX_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_CEXP_II] THEN REAL_ARITH_TAC]);;

(* Every t-slice of the 283H strip integrand (at a fixed frequency x0) is    *)
(* absolutely integrable: the vec-0 slices trivially, the others = a         *)
(* constant times a modulation integrand.                                    *)
let STRIP_SLICE_ABSINT = prove
 (`!(f:real->complex) a x x0.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> (\y. if drop(fstcart(pastecart (x0:real^1) y)) IN real_interval[--a,a]
              then cexp(ii * Cx x * Cx(drop(fstcart(pastecart x0 y)))) *
                   cexp(--(ii * Cx(drop(fstcart(pastecart x0 y))) *
                            Cx(drop(sndcart(pastecart x0 y))))) *
                   f(drop(sndcart(pastecart x0 y)))
              else vec 0) absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_CASES_TAC `drop(x0:real^1) IN real_interval[--a,a]` THEN
  ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_0] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL THEN
  ASM_SIMP_TAC[FOURIER_MODULATION_ABSINT]);;

(* The inner (t-)integral of |G| is a step function of the frequency x0:     *)
(*   INT_t |G(pastecart x0 y)| = if drop x0 IN [-a,a] then INT_R |f| else 0. *)
let STRIP_INNER_NORM_INTEGRAL = prove
 (`!(f:real->complex) a x x0.
     integral (:real^1) (\y. lift(norm(
         if drop(fstcart(pastecart (x0:real^1) y)) IN real_interval[--a,a]
         then cexp(ii * Cx x * Cx(drop(fstcart(pastecart x0 y)))) *
              cexp(--(ii * Cx(drop(fstcart(pastecart x0 y))) *
                       Cx(drop(sndcart(pastecart x0 y))))) *
              f(drop(sndcart(pastecart x0 y)))
         else vec 0))) =
     (if drop x0 IN real_interval[--a,a]
      then integral (:real^1) (\y. lift(norm(f(drop y)))) else vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NORM_0; LIFT_NUM; INTEGRAL_0] THEN
  REWRITE_TAC[STRIP_INTEGRAND_NORM]);;

(* A constant restricted to the frequency strip is integrable over R.        *)
let STRIP_STEP_INTEGRABLE = prove
 (`!a (C:real^1).
        (\x0:real^1. if drop x0 IN real_interval[--a,a] then C else vec 0)
        integrable_on (:real^1)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]
   `(if drop x0 IN real_interval[--a,a] then (C:real^1) else vec 0) =
    (if x0 IN interval[lift(--a), lift a] then C else vec 0)`] THEN
  REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_CONST]);;

(* The 283H strip integrand G is absolutely integrable over R^2, via FUBINI_ *)
(* TONELLI: it is measurable, all t-slices are absolutely integrable (so the *)
(* bad- slice set is empty), and the iterated norm-integral is the step      *)
(* function 1_[-a,a](x0) INT_R |f|, which is integrable.                     *)
let STRIP_INTEGRAND_ABSINT = prove
 (`!(f:real->complex) a w.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> (\z:real^(1,1)finite_sum.
            if drop(fstcart z) IN real_interval[--a,a]
            then cexp(ii * Cx w * Cx(drop(fstcart z))) *
                 cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
                 f(drop(sndcart z))
            else vec 0) absolutely_integrable_on (:real^(1,1)finite_sum)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `\z:real^(1,1)finite_sum.
       if drop(fstcart z) IN real_interval[--a,a]
       then cexp(ii * Cx w * Cx(drop(fstcart z))) *
            cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
            f(drop(sndcart z))
       else vec 0` (INST_TYPE [`:1`,`:M`; `:1`,`:N`] FUBINI_TONELLI)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC STRIP_INTEGRAND_MEASURABLE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                 INTEGRABLE_IMP_MEASURABLE]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{x | ~((\y. (if drop(fstcart(pastecart (x:real^1) y)) IN
                       real_interval[--a,a]
                   then cexp(ii * Cx w * Cx(drop(fstcart(pastecart x y)))) *
                        cexp(--(ii * Cx(drop(fstcart(pastecart x y))) *
                                 Cx(drop(sndcart(pastecart x y))))) *
                        f(drop(sndcart(pastecart x y)))
                   else vec 0)) absolutely_integrable_on (:real^1))} = {}`
     (fun th -> REWRITE_TAC[th; NEGLIGIBLE_EMPTY]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[STRIP_SLICE_ABSINT];
    ASM_REWRITE_TAC[STRIP_INNER_NORM_INTEGRAL; STRIP_STEP_INTEGRABLE]]);;

(* Fubini's theorem for the strip integrand: swap the order of the frequency
   (x)  *)
(* and space (y=t) integrations.  This is the heart of 283H.                 *)
let STRIP_FUBINI_SWAP = prove
 (`!(f:real->complex) a w.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> integral (:real^1)
           (\x. integral (:real^1) (\y.
              if drop(fstcart(pastecart (x:real^1) y)) IN real_interval[--a,a]
              then cexp(ii * Cx w * Cx(drop(fstcart(pastecart x y)))) *
                   cexp(--(ii * Cx(drop(fstcart(pastecart x y))) *
                            Cx(drop(sndcart(pastecart x y))))) *
                   f(drop(sndcart(pastecart x y)))
              else vec 0)) =
         integral (:real^1)
           (\y. integral (:real^1) (\x.
              if drop(fstcart(pastecart (x:real^1) y)) IN real_interval[--a,a]
              then cexp(ii * Cx w * Cx(drop(fstcart(pastecart x y)))) *
                   cexp(--(ii * Cx(drop(fstcart(pastecart x y))) *
                            Cx(drop(sndcart(pastecart x y))))) *
                   f(drop(sndcart(pastecart x y)))
              else vec 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `\z:real^(1,1)finite_sum.
       if drop(fstcart z) IN real_interval[--a,a]
       then cexp(ii * Cx w * Cx(drop(fstcart z))) *
            cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
            f(drop(sndcart z))
       else vec 0`
      (INST_TYPE [`:1`,`:M`; `:1`,`:N`] FUBINI_INTEGRAL_SWAP)) THEN
  ASM_SIMP_TAC[STRIP_INTEGRAND_ABSINT]);;

(* ------------------------------------------------------------------------- *)
(* Evaluating the two iterated integrals.                                    *)
(* ------------------------------------------------------------------------- *)

(* LHS inner (t-)integral reproduces the (unnormalized) Fourier transform.   *)
let LHS_INNER = prove
 (`!(f:real->complex) x0.
     integral (:real^1)
       (\y. cexp(--(ii * Cx(drop x0) * Cx(drop y))) * f(drop y)) =
     Cx(sqrt(&2 * pi)) * fourier f (drop x0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fourier] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  SUBGOAL_THEN `Cx(sqrt(&2 * pi)) * Cx(&1) / Cx(sqrt(&2 * pi)) = Cx(&1)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(COMPLEX_FIELD `~(z = Cx(&0)) ==> z * Cx(&1)/z = Cx(&1)`) THEN
    REWRITE_TAC[CX_INJ] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    REWRITE_TAC[COMPLEX_MUL_LID]]);;

(* Combine the two exponentials of the RHS inner integrand.                  *)
let CEXP_COMBINE = prove
 (`!w t x. cexp(ii * Cx w * Cx x) * cexp(--(ii * Cx x * Cx t)) =
           cexp(ii * Cx(w - t) * Cx x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CEXP_ADD] THEN AP_TERM_TAC THEN
  REWRITE_TAC[CX_SUB] THEN SIMPLE_COMPLEX_ARITH_TAC);;

(* The frequency-restricted single exponential is integrable and integrates  *)
(* to the Dirichlet-kernel value (CEXP_INTERVAL_INTEGRAL over the strip      *)
(* [-a,a]).                                                                  *)
let CEXP_RESTRICT_INTEGRABLE = prove
 (`!a b. (\x:real^1. if drop x IN real_interval[--a,a]
                     then cexp(ii * Cx b * Cx(drop x)) else vec 0)
         integrable_on (:real^1)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\x:real^1. if drop x IN real_interval[--a,a]
                then cexp(ii * Cx b * Cx(drop x)) else vec 0) =
    (\x. if x IN interval[lift(--a), lift a]
         then cexp(ii * Cx b * Cx(drop x)) else vec 0)`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  SUBGOAL_THEN `(\x:real^1. cexp(ii * Cx b * Cx(drop x))) =
                cexp o (\x. (ii * Cx b) * Cx(drop x))`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF; COMPLEX_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN REWRITE_TAC[CONTINUOUS_ON_ID]);;

let CEXP_RESTRICT_INTEGRAL = prove
 (`!a b. &0 <= a /\ ~(b = &0)
   ==> integral (:real^1) (\x. if drop x IN real_interval[--a,a]
                               then cexp(ii * Cx b * Cx(drop x)) else vec 0) =
       Cx(&2 * sin(a * b) / b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^1. if drop x IN real_interval[--a,a]
                then cexp(ii * Cx b * Cx(drop x)) else vec 0) =
    (\x. if x IN interval[lift(--a), lift a]
         then cexp(ii * Cx b * Cx(drop x)) else vec 0)`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
  ASM_SIMP_TAC[CEXP_INTERVAL_INTEGRAL]);;

(* RHS inner (frequency-)integral = f(t) * 2 sin((w-t)a)/(w-t)  (w =/= t).   *)
let RHS_INNER = prove
 (`!(f:real->complex) a w t y. &0 <= a /\ ~(w - t = &0)
   ==> integral (:real^1)
         (\x. if drop(fstcart(pastecart (x:real^1) (y:real^1))) IN
                 real_interval[--a,a]
              then cexp(ii * Cx w * Cx(drop(fstcart(pastecart x y)))) *
                   cexp(--(ii * Cx(drop(fstcart(pastecart x y))) * Cx t)) * f t
              else vec 0) =
       Cx(&2 * sin((w - t) * a) / (w - t)) * f t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FSTCART_PASTECART] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[CEXP_COMBINE] THEN
  SUBGOAL_THEN
   `!x. (if drop x IN real_interval[--a,a]
         then cexp(ii * Cx(w - t) * Cx(drop x)) * f t else vec 0) =
        (if drop x IN real_interval[--a,a]
         then cexp(ii * Cx(w - t) * Cx(drop x)) else vec 0) *
        (f:real->complex) t`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_COMPLEX_RMUL; CEXP_RESTRICT_INTEGRABLE] THEN
  ASM_SIMP_TAC[CEXP_RESTRICT_INTEGRAL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

(* LHS outer integrand: after the inner t-integral, the frequency integrand
   is    *)
(*   1_[-a,a](x) * e^{iwx} sqrt(2pi) fhat(x).                                *)
let LHS_OUTER_INTEGRAND = prove
 (`!(f:real->complex) a w x.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> integral (:real^1)
           (\y. if drop(fstcart(pastecart (x:real^1) (y:real^1))) IN
                   real_interval[--a,a]
                then cexp(ii * Cx w * Cx(drop(fstcart(pastecart x y)))) *
                     cexp(--(ii * Cx(drop(fstcart(pastecart x y))) *
                              Cx(drop(sndcart(pastecart x y))))) *
                     f(drop(sndcart(pastecart x y)))
                else vec 0) =
         (if drop x IN real_interval[--a,a]
          then cexp(ii * Cx w * Cx(drop x)) * Cx(sqrt(&2 * pi)) *
               fourier f (drop x)
          else vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INTEGRAL_0] THEN
  MP_TAC(ISPECL [`\y:real^1. cexp(--(ii * Cx(drop(x:real^1)) * Cx(drop y))) *
                             (f:real->complex)(drop y)`;
                 `(:real^1)`; `cexp(ii * Cx w * Cx(drop(x:real^1)))`]
    INTEGRAL_COMPLEX_LMUL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC FOURIER_MODULATION_ABSINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LHS_INNER] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM th]) THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC]);;

(* LHS of the Fubini swap, fully evaluated: the frequency integral over      *)
(* [-a,a] of e^{iwy} sqrt(2pi) fhat(y).                                      *)
let LHS_SIDE = prove
 (`!(f:real->complex) a w.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> integral (:real^1)
           (\x. integral (:real^1) (\y.
              if drop(fstcart(pastecart (x:real^1) y)) IN real_interval[--a,a]
              then cexp(ii * Cx w * Cx(drop(fstcart(pastecart x y)))) *
                   cexp(--(ii * Cx(drop(fstcart(pastecart x y))) *
                            Cx(drop(sndcart(pastecart x y))))) *
                   f(drop(sndcart(pastecart x y)))
              else vec 0)) =
         integral (interval[lift(--a), lift a])
           (\y. cexp(ii * Cx w * Cx(drop y)) * Cx(sqrt(&2 * pi)) *
                fourier f (drop y))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LHS_OUTER_INTEGRAND] THEN
  SUBGOAL_THEN
   `(\x. if drop x IN real_interval[--a,a]
         then cexp(ii * Cx w * Cx(drop x)) * Cx(sqrt(&2 * pi)) *
              fourier f (drop x)
         else vec 0) =
    (\x:real^1. if x IN interval[lift(--a),lift a]
         then cexp(ii * Cx w * Cx(drop x)) * Cx(sqrt(&2 * pi)) *
              fourier f (drop x)
         else vec 0)`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]);;

(* RHS of the Fubini swap, fully evaluated (via a spike at the single point  *)
(* t=w): the space integral of 2 sin((w-t)a)/(w-t) f(t).                     *)
let RHS_SIDE = prove
 (`!(f:real->complex) a w.
     &0 <= a
     ==> integral (:real^1)
           (\y. integral (:real^1) (\x.
              if drop(fstcart(pastecart (x:real^1) y)) IN real_interval[--a,a]
              then cexp(ii * Cx w * Cx(drop(fstcart(pastecart x y)))) *
                   cexp(--(ii * Cx(drop(fstcart(pastecart x y))) *
                            Cx(drop(sndcart(pastecart x y))))) *
                   f(drop(sndcart(pastecart x y)))
              else vec 0)) =
         integral (:real^1)
           (\y. Cx(&2 * sin((w - drop y) * a) / (w - drop y)) * f(drop y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{lift w}` THEN REWRITE_TAC[NEGLIGIBLE_SING] THEN
  X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN
  DISCH_TAC THEN
  REWRITE_TAC[SNDCART_PASTECART] THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`f:real->complex`; `a:real`; `w:real`; `drop(y:real^1)`;
                 `y:real^1`] RHS_INNER) THEN
  REWRITE_TAC[SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_0] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(y = lift w)` THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LIFT_DROP] THEN ASM_REWRITE_TAC[];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 283H (Fremlin), clean intermediate form.  For a >= 0 and f in L^1(R):     *)
(*   sqrt(2pi) INT_{-a}^a e^{iwy} fhat(y) dy =
     INT_R (2 sin((w-t)a)/(w-t)) f(t) dt.*)
(* Chains the two evaluated sides through the Fubini swap.  (The Fremlin
   form  *)
(* (1/sqrt2pi)INT e^{iwy}fhat = (1/pi)INT sin.../(w-t) f follows by dividing
   by *)
(* 2 sqrt(2pi); the sin((w-t)a)/(w-t) kernel is exactly the sinc kernel that *)
(* 283I feeds to Riemann-Lebesgue + 283Da.)                                  *)
let FOURIER_283H_RAW = prove
 (`!(f:real->complex) a w.
     &0 <= a /\ (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> integral (interval[lift(--a), lift a])
           (\y. cexp(ii * Cx w * Cx(drop y)) * Cx(sqrt(&2 * pi)) *
                fourier f (drop y)) =
         integral (:real^1)
           (\y. Cx(&2 * sin((w - drop y) * a) / (w - drop y)) * f(drop y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->complex`; `a:real`; `w:real`] LHS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`f:real->complex`; `a:real`; `w:real`] RHS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC STRIP_FUBINI_SWAP THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The complex-valued Riemann-Lebesgue lemma on R (for 283I): the real RL    *)
(* applied to the real and imaginary parts.  INT_R Cx(sin(a u)) H(u) -->
   vec 0.*)
(* ------------------------------------------------------------------------- *)

(* Cx(sin(a * drop u)) is continuous on R^1 (needed for measurability).      *)
let CX_SIN_STRETCH_CONTINUOUS = prove
 (`!a. (\u:real^1. Cx(sin(a * drop u))) continuous_on (:real^1)`,
  GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN
  SUBGOAL_THEN `(\u:real^1. lift(sin(a * drop u))) =
                lift o (\t. sin(a * t)) o drop`
   SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV) [GSYM IMAGE_LIFT_UNIV] THEN
  REWRITE_TAC[GSYM REAL_CONTINUOUS_ON] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
  REAL_DIFFERENTIABLE_TAC);;

(* Cx(sin(a u)) H(u) is integrable (bounded x L^1).                          *)
let CX_SIN_H_INTEGRABLE = prove
 (`!(H:real->complex) a. (\z. H(drop z)) absolutely_integrable_on (:real^1)
   ==> (\u. Cx(sin(a * drop u)) * H(drop u)) integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`;
                 `\u:real^1. Cx(sin(a * drop u))`;
                 `\u:real^1. (H:real->complex)(drop u)`; `(:real^1)`]
    ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    REWRITE_TAC[CX_SIN_STRETCH_CONTINUOUS];
    REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN GEN_TAC THEN
    MP_TAC(SPEC `a * drop(x:real^1)` SIN_BOUND) THEN REAL_ARITH_TAC]);;

(* The real and imaginary parts of an L^1 complex function are real-L^1.     *)
(* GEN_REWRITE_RULE I [ABSOLUTELY_INTEGRABLE_COMPONENTWISE] applies the iff
   at    *)
(* precisely the TOP LEVEL of the chosen hypothesis, turning the complex L^1 *)
(* fact into its two lifted components.  (A plain REWRITE_RULE would loop --
   the  *)
(* iff's RHS re-matches its LHS pattern; and ONCE_REWRITE_RULE, which
   descends,   *)
(* would silently no-op if FIRST_X_ASSUM grabbed a non-matching hypothesis.
   The   *)
(* top-level `I` conversion instead fails there, so FIRST_X_ASSUM
   backtracks.)    *)
let RE_H_ABSINT = prove
 (`!(H:real->complex). (\z. H(drop z)) absolutely_integrable_on (:real^1)
   ==> (\u. Re(H u)) absolutely_real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [ABSOLUTELY_INTEGRABLE_COMPONENTWISE]) THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2] THEN STRIP_TAC THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; IMAGE_LIFT_UNIV; o_DEF;
              RE_DEF] THEN
  ASM_REWRITE_TAC[]);;

let IM_H_ABSINT = prove
 (`!(H:real->complex). (\z. H(drop z)) absolutely_integrable_on (:real^1)
   ==> (\u. Im(H u)) absolutely_real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [ABSOLUTELY_INTEGRABLE_COMPONENTWISE]) THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2] THEN STRIP_TAC THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; IMAGE_LIFT_UNIV; o_DEF;
              IM_DEF] THEN
  ASM_REWRITE_TAC[]);;

(* The two real components of INT_R Cx(sin(a u)) H(u) du are the real        *)
(* integrals of Re(H) sin and Im(H) sin -- the bridge from the complex       *)
(* integral to the real RL (INTEGRAL_COMPONENT + REAL_INTEGRAL +             *)
(* RE_MUL_CX/IM_MUL_CX).                                                     *)
let RE_COMPONENT_BRIDGE = prove
 (`!(H:real->complex) a. (\z. H(drop z)) absolutely_integrable_on (:real^1)
   ==> (integral (:real^1) (\u. Cx(sin(a * drop u)) * H(drop u)))$1 =
       real_integral (:real) (\u. Re(H u) * sin(a * u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\u. Re((H:real->complex) u) * sin(a * u)) real_integrable_on (:real)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC FOURIER_SIN_ABSINT THEN ASM_SIMP_TAC[RE_H_ABSINT];
    ALL_TAC] THEN
  MP_TAC(INST [`(:real^1)`,`s:real^1->bool`; `1`,`k:num`]
    (ISPEC `\u. Cx(sin(a * drop u)) * (H:real->complex)(drop u)`
           INTEGRAL_COMPONENT)) THEN
  ASM_SIMP_TAC[CX_SIN_H_INTEGRABLE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM RE_DEF; RE_MUL_CX] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL] THEN
  REWRITE_TAC[IMAGE_LIFT_UNIV; o_DEF; LIFT_DROP] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_SYM]);;

let IM_COMPONENT_BRIDGE = prove
 (`!(H:real->complex) a. (\z. H(drop z)) absolutely_integrable_on (:real^1)
   ==> (integral (:real^1) (\u. Cx(sin(a * drop u)) * H(drop u)))$2 =
       real_integral (:real) (\u. Im(H u) * sin(a * u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\u. Im((H:real->complex) u) * sin(a * u)) real_integrable_on (:real)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC FOURIER_SIN_ABSINT THEN
      ASM_SIMP_TAC[IM_H_ABSINT]; ALL_TAC] THEN
  MP_TAC(INST [`(:real^1)`,`s:real^1->bool`; `2`,`k:num`]
    (ISPEC `\u. Cx(sin(a * drop u)) * (H:real->complex)(drop u)`
      INTEGRAL_COMPONENT)) THEN
  ASM_SIMP_TAC[CX_SIN_H_INTEGRABLE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM IM_DEF; IM_MUL_CX] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL] THEN
  REWRITE_TAC[IMAGE_LIFT_UNIV; o_DEF; LIFT_DROP] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_SYM]);;

(* The complex-valued Riemann-Lebesgue lemma on R: INT_R Cx(sin(a u)) H(u)   *)
(* du                                                                        *)
(* --> vec 0 at +inf, for complex H in L^1(R). Componentwise from the real   *)
(* RL.                                                                       *)
let RIEMANN_LEBESGUE_RLINE_COMPLEX = prove
 (`!(H:real->complex).
     (\z. H(drop z)) absolutely_integrable_on (:real^1)
     ==> ((\a. integral (:real^1) (\u. Cx(sin(a * drop u)) * H(drop u))) -->
       vec 0)
         at_posinfinity`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_COMPONENTWISE_REAL] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; GSYM tendsto_real_def; VEC_COMPONENT] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RE_COMPONENT_BRIDGE] THEN
    MATCH_MP_TAC RIEMANN_LEBESGUE_RLINE THEN ASM_SIMP_TAC[RE_H_ABSINT];
    ASM_SIMP_TAC[IM_COMPONENT_BRIDGE] THEN
    MATCH_MP_TAC RIEMANN_LEBESGUE_RLINE THEN ASM_SIMP_TAC[IM_H_ABSINT]]);;

(* ------------------------------------------------------------------------- *)
(* 283I ingredients.  The truncation g(u) = f(x) for |u|<=1, 0 otherwise     *)
(* contributes  INT_{-1}^1 sin(a u)/u du * f(x); the sinc factor's limit is  *)
(* pi (from 283Da via the x = a t substitution SIN_OVER_X_SUBST).            *)
(* (Uses SIN_OVER_X_SUBST / SIN_OVER_X_LIMIT_POSINF, proved above.)          *)
(* ------------------------------------------------------------------------- *)

let GPART_LIMIT = prove
 (`((\a. real_integral (real_interval[--(&1),&1]) (\u. sin(a * u) / u)) --->
   pi)
   at_posinfinity`,
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\a. real_integral (real_interval[--a,a]) (\x. sin x / x)` THEN
  REWRITE_TAC[SIN_OVER_X_LIMIT_POSINF] THEN
  REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN EXISTS_TAC `&1` THEN
  X_GEN_TAC `a:real` THEN REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:real`; `&1`] SIN_OVER_X_SUBST) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* u |-> f(x - u) is L^1 when f is (reflection m=-1 + translation c = lift   *)
(* x, via                                                                    *)
(* ABSOLUTELY_INTEGRABLE_AFFINITY). Used for the L^1 tail of the 283I        *)
(* integrand.                                                                *)
let F_REFLECT_TRANSLATE_ABSINT = prove
 (`!(f:real->complex) x. (\z. f(drop z)) absolutely_integrable_on (:real^1)
   ==> (\z. f(x - drop z)) absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^1. (f:real->complex)(drop z)`; `(:real^1)`; `--(&1)`;
    `lift x`]
    ABSOLUTELY_INTEGRABLE_AFFINITY) THEN
  ASM_REWRITE_TAC[REAL_ARITH `~(--(&1) = &0)`] THEN
  SUBGOAL_THEN
    `IMAGE (\z:real^1. inv(--(&1)) % z + --(inv(--(&1)) % lift x)) (:real^1) =
    (:real^1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `z:real^1` THEN
    EXISTS_TAC `--z + lift x:real^1` THEN
    REWRITE_TAC[REAL_INV_NEG; REAL_INV_1] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* Scalar quotient bound (the arithmetic heart of the 283I near-0 estimate): *)
(* if n <= K v and v > 0 then 2 (1/v) n <= 2 K.  Applied with v = |u|, n =   *)
(* norm(f(x-u)-f x) to bound the difference-quotient integrand near u = 0.   *)
let SCALAR_QUOTIENT_BOUND = prove
 (`!v n K:real. &0 < v /\ n <= K * v ==> &2 * inv v * n <= &2 * K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * K = &2 * inv v * (K * v)` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(v = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ]);;

(* The singular factor Cx(2/u) is measurable on R^1: 2 inv(drop z) is real-  *)
(* measurable (inv of the identity, zeros = {0} negligible), then compose    *)
(* with                                                                      *)
(* the continuous Cx(drop .).  (Part of the 283I integrand's measurability.) *)
let CX_2INV_MEASURABLE = prove
 (`(\z:real^1. Cx(&2 * inv(drop z))) measurable_on (:real^1)`,
  SUBGOAL_THEN
    `(\z:real^1. Cx(&2 * inv(drop z))) = (\w. Cx(drop w)) o (\z. lift(&2 *
    inv(drop z)))`
   SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^1. lift(&2 * inv(drop z))) = lift o (\u. &2 * inv u) o drop`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_LIFT_UNIV; GSYM real_measurable_on] THEN
    MATCH_MP_TAC REAL_MEASURABLE_ON_LMUL THEN
    MP_TAC(ISPEC `\x:real. x` REAL_MEASURABLE_ON_INV) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SING_GSPEC; REAL_NEGLIGIBLE_SING] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN REWRITE_TAC[CONTINUOUS_ON_ID]]);;

(* The truncation window {u : |u| <= 1} is (the lift of) a bounded interval, *)
(* hence lebesgue-measurable -- needed for measurability of the              *)
(* g-truncation.                                                             *)
let TRUNC_WINDOW_MEASURABLE = prove
 (`lebesgue_measurable {z:real^1 | abs(drop z) <= &1}`,
  SUBGOAL_THEN
    `{z:real^1 | abs(drop z) <= &1} = interval[lift(--(&1)), lift(&1)]`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL]]);;

(* The 283I integrand H(u) = 2/u (f(x-u) - g(u)) is measurable on R^1, where *)
(* g(u) = f(x) for |u| <= 1 and 0 otherwise. Product of the measurable       *)
(* factors                                                                   *)
(* Cx(2/u) and (f(x-u) - g(u)) (affine-of-f minus a two-case function).      *)
let H283I_MEASURABLE = prove
 (`!(f:real->complex) x. (\z. f(drop z)) absolutely_integrable_on (:real^1)
   ==> (\z. Cx(&2 * inv(drop z)) *
            (f(x - drop z) - (if abs(drop z) <= &1 then f x else vec 0)))
       measurable_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN
  REWRITE_TAC[CX_2INV_MEASURABLE] THEN
  MATCH_MP_TAC MEASURABLE_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    ASM_SIMP_TAC[F_REFLECT_TRANSLATE_ABSINT];
    MATCH_MP_TAC MEASURABLE_ON_CASES THEN
    REWRITE_TAC[MEASURABLE_ON_CONST; MEASURABLE_ON_0;
      TRUNC_WINDOW_MEASURABLE]]);;

(* A constant on a symmetric window is integrable over R (extend by 0).      *)
let CONST_WINDOW_INTEGRABLE = prove
 (`!c r. (\z:real^1. lift(c * (if abs(drop z) <= r then &1 else &0)))
   integrable_on (:real^1)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\z:real^1. lift(c * (if abs(drop z) <= r then &1 else &0))) =
    (\z. if z IN interval[lift(--r), lift r] then lift c else vec 0)`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; LIFT_NUM] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_CONST]);;

(* The dominating function for the 283I integrand H is integrable: a sum of  *)
(* a box (near 0), (2/d) |f(x-u)| (an L^1 translate/reflect of f), and a     *)
(* box.                                                                      *)
let DOMINATOR_INTEGRABLE = prove
 (`!(f:real->complex) x K d. (\z. f(drop z)) absolutely_integrable_on (:real^1)
   ==> (\z:real^1. lift(&2 * K * (if abs(drop z) <= d then &1 else &0)) +
                   lift(&2 / d * norm(f(x - drop z))) +
                   lift(&2 / d * norm(f x) * (if abs(drop z) <= &1 then &1 else
                     &0)))
       integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
     REWRITE_TAC[CONST_WINDOW_INTEGRABLE]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
    ASM_SIMP_TAC[F_REFLECT_TRANSLATE_ABSINT];
    ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      REWRITE_TAC[CONST_WINDOW_INTEGRABLE]]);;

(* norm of the singular-factor product:  |Cx(2/u) w| = 2 (1/|u|) |w|.        *)
let NORM_CX_2INV_MUL = prove
 (`!u (w:complex). norm(Cx(&2 * inv u) * w) = &2 * inv(abs u) * norm w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_INV] THEN
    REWRITE_TAC[REAL_MUL_ASSOC]);;

(* The three terms of the dominator are nonnegative (handles the u = 0       *)
(* case).                                                                    *)
let NEAR_REGION_BOUND = prove
 (`!(f:real->complex) x K d u.
     &0 < d /\ d <= &1 /\ &0 <= K /\ ~(u = &0) /\ abs u <= d /\
     (!v. abs v <= d ==> norm(f(x - v) - f x) <= K * abs v)
     ==> &2 * inv(abs u) * norm(f(x - u) - (if abs u <= &1 then f x else vec
       0))
         <= &2 * K * (if abs u <= d then &1 else &0) +
            &2 / d * norm(f(x - u)) +
            &2 / d * norm(f x) * (if abs u <= &1 then &1 else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs u <= &1` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * K` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`abs u`; `norm((f:real->complex)(x - u) - f x)`; `K:real`]
      SCALAR_QUOTIENT_BOUND) THEN
    ASM_SIMP_TAC[GSYM REAL_ABS_NZ] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
    MATCH_MP_TAC(REAL_ARITH `&0 <= t2 /\ &0 <= t3 ==> &2 * K <= &2 * K + t2 +
      t3`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS; NORM_POS_LE]]);;

(* Far region abs u > delta: norm H <= (2/abs u)(norm f(x-u) + norm g(u)) <= *)
(* (2/delta) norm f(x-u) + (2/delta) norm(f x) on the unit window (inv       *)
(* monotone + triangle inequality).                                          *)
let FAR_REGION_BOUND = prove
 (`!(f:real->complex) x K d u.
     &0 < d /\ ~(u = &0) /\ ~(abs u <= d)
     ==> &2 * inv(abs u) * norm(f(x - u) - (if abs u <= &1 then f x else vec
       0))
         <= &2 * K * (if abs u <= d then &1 else &0) +
            &2 / d * norm(f(x - u)) +
            &2 / d * norm(f x) * (if abs u <= &1 then &1 else &0)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
  ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * inv(abs u)) *
              (norm((f:real->complex)(x - u)) + norm(if abs u <= &1 then f x
                else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
       REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ; REAL_ABS_POS];
      NORM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * inv(abs u) <= &2 / d` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
     REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / d * (norm((f:real->complex)(x - u)) + norm(if abs u <= &1
    then f x else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    REWRITE_TAC[REAL_LE_REFL] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RID; NORM_0; REAL_MUL_RZERO; REAL_LE_REFL]]);;

(* Combining the regions: the pointwise domination norm(H(u)) <= drop D(u).  *)
let H283I_POINTWISE_BOUND = prove
 (`!(f:real->complex) x K d u.
     &0 < d /\ d <= &1 /\ &0 <= K /\
     (!v. abs v <= d ==> norm(f(x - v) - f x) <= K * abs v)
     ==> norm(Cx(&2 * inv u) * (f(x - u) - (if abs u <= &1 then f x else vec
       0)))
         <= &2 * K * (if abs u <= d then &1 else &0) +
            &2 / d * norm(f(x - u)) +
            &2 / d * norm(f x) * (if abs u <= &1 then &1 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_CX_2INV_MUL] THEN
  ASM_CASES_TAC `u = &0` THENL
   [ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_INV_0; REAL_MUL_LZERO;
     REAL_MUL_RZERO] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; NORM_POS_LE; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `abs u <= d` THENL
   [MP_TAC(ISPECL [`f:real->complex`; `x:real`; `K:real`; `d:real`;
     `u:real`] NEAR_REGION_BOUND) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`f:real->complex`; `x:real`; `K:real`; `d:real`;
      `u:real`] FAR_REGION_BOUND) THEN
    ASM_SIMP_TAC[]]);;

(* The 283I integrand H(u) = (2/u)(f(x-u) - g(u)) is absolutely integrable   *)
(* on R                                                                      *)
(* (measurable + dominated by the integrable D). This is the L^1-ness that   *)
(* lets                                                                      *)
(* Riemann-Lebesgue kill the "difference" part of the inversion integral.    *)
let H283I_ABSINT = prove
 (`!(f:real->complex) x K d.
     &0 < d /\ d <= &1 /\ &0 <= K /\
     (!v. abs v <= d ==> norm(f(x - v) - f x) <= K * abs v) /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> (\z. Cx(&2 * inv(drop z)) *
              (f(x - drop z) - (if abs(drop z) <= &1 then f x else vec 0)))
         absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC
   `\z:real^1. lift(&2 * K * (if abs(drop z) <= d then &1 else &0)) +
               lift(&2 / d * norm((f:real->complex)(x - drop z))) +
               lift(&2 / d * norm(f x) * (if abs(drop z) <= &1 then &1 else
                 &0))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[H283I_MEASURABLE];
    ASM_SIMP_TAC[DOMINATOR_INTEGRABLE];
    GEN_TAC THEN REWRITE_TAC[IN_UNIV] THEN
    REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN BETA_TAC THEN
    MATCH_MP_TAC H283I_POINTWISE_BOUND THEN ASM_REWRITE_TAC[]]);;

(* The Riemann-Lebesgue "difference" part of the 283I integral vanishes:     *)
(* INT_R sin(a u)/u (f(x-u) - g(u)) du --> 0, since (f(x-u)-g(u))/u is L^1.  *)
let RLPART_LIMIT = prove
 (`!(f:real->complex) x K d.
     &0 < d /\ d <= &1 /\ &0 <= K /\
     (!v. abs v <= d ==> norm(f(x - v) - f x) <= K * abs v) /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> ((\a. integral (:real^1)
                (\u. Cx(sin(a * drop u)) *
                     (Cx(&2 * inv(drop u)) *
                      (f(x - drop u) - (if abs(drop u) <= &1 then f x else vec
                        0)))))
          --> vec 0) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\u. Cx(&2 * inv u) *
                    ((f:real->complex)(x - u) - (if abs u <= &1 then f x else
                      vec 0))`
    RIEMANN_LEBESGUE_RLINE_COMPLEX) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`f:real->complex`; `x:real`; `K:real`;
    `d:real`] H283I_ABSINT) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Assembly bricks for 283I: change of variable t = x - u in the 283H RHS,   *)
(* the pointwise integrand split, and a Cx / real_integral bridge.           *)
(* ------------------------------------------------------------------------- *)

(* Change of variable u |-> c - u on the whole real line: reflect +          *)
(* translate.                                                                *)
let SUBST_REFLECT_INTEGRAL_UNIV = prove
 (`!(H:real^1->real^N) c.
     integral (:real^1) (\u. H(c - u)) = integral (:real^1) H`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. (H:real^1->real^N)(c + x)`; `(:real^1)`]
    INTEGRAL_REFLECT_GEN) THEN
  REWRITE_TAC[REFLECT_UNIV] THEN BETA_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(c:real^1) + --x = c - x`] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:real^1->real^N`; `(:real^1)`; `c:real^1`]
    INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[TRANSLATION_UNIV] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* The 283H RHS integral, after t = x - u: the sinc kernel becomes sin(a     *)
(* u)/u.                                                                     *)
let SUBSTITUTED_RHS = prove
 (`!(f:real->complex) x a.
     integral (:real^1)
       (\y. Cx (&2 * sin ((x - drop y) * a) / (x - drop y)) * f (drop y)) =
     integral (:real^1)
       (\u. Cx (&2 * sin (a * drop u) / drop u) * f (x - drop u))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
    [`\y. Cx (&2 * sin ((x - drop y) * a) / (x - drop y)) *
          (f:real->complex) (drop y)`;
     `lift x`] SUBST_REFLECT_INTEGRAL_UNIV) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
  AP_TERM_TAC THEN ABS_TAC THEN BETA_TAC THEN
  REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN
  REWRITE_TAC[REAL_ARITH `(x:real) - (x - u) = u`; REAL_MUL_SYM]);;

(* Split the substituted integrand into the L^1 "difference" part (feeds     *)
(* Riemann-Lebesgue) and the singular "g" part (feeds the Dirichlet limit).  *)
let INTEGRAND_SPLIT_283I = prove
 (`!(f:real->complex) x a u:real^1.
     Cx (&2 * sin (a * drop u) / drop u) * f (x - drop u) =
     Cx (sin (a * drop u)) *
       (Cx (&2 * inv (drop u)) *
        (f (x - drop u) - (if abs (drop u) <= &1 then f x else vec 0))) +
     Cx (sin (a * drop u)) *
       (Cx (&2 * inv (drop u)) *
        (if abs (drop u) <= &1 then f x else vec 0))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_ADD_LDISTRIB; GSYM COMPLEX_ADD_ASSOC] THEN
  REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB] THEN
  REWRITE_TAC[COMPLEX_SUB_ADD] THEN
  REWRITE_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[real_div; CX_MUL; COMPLEX_MUL_AC]);;

(* Integral of Cx of a real function = Cx of the real integral (a linear     *)
(* map).                                                                     *)
let CX_REAL_INTEGRAL_BRIDGE = prove
 (`!(g:real->real) s.
     g real_integrable_on s
     ==> integral (IMAGE lift s) (\u. Cx(g(drop u))) =
         Cx(real_integral s g)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INTEGRABLE_INTEGRAL) THEN
  REWRITE_TAC[has_real_integral] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`lift o (g:real->real) o drop`; `lift(real_integral s (g:real->real))`;
     `IMAGE lift s`;
       `(\z. Cx(drop z)):real^1->complex`] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL;
     CX_MUL];
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REFL_TAC]);;

(* Cx of a real-integrable function is (vector) integrable on the lifted     *)
(* set.                                                                      *)
let INTEGRABLE_CX_DROP_COMPOSE = prove
 (`!(g:real->real) s.
     g real_integrable_on s
     ==> (\u. Cx(g(drop u))) integrable_on (IMAGE lift s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[real_integrable_on]) THEN
  REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real`) THEN
  MP_TAC(ISPECL
    [`lift o (g:real->real) o drop`; `(\z. Cx(drop z)):real^1->complex`;
     `IMAGE lift s`] INTEGRABLE_LINEAR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift(y:real)` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL;
                  COMPLEX_CMUL; CX_MUL]];
    REWRITE_TAC[o_DEF; LIFT_DROP]]);;

(* Two small helpers for the g-part value.                                   *)
let COMPLEX_MUL_COND_VEC0 = prove
 (`!A B c P:bool. A * (B * (if P then c else vec 0)) =
                  (if P then A * (B * c) else vec 0)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO]);;

let GPART_INTEGRAND_REWRITE = prove
 (`!(fx:complex) a u:real^1.
     Cx (sin (a * drop u)) * (Cx (&2 * inv (drop u)) * fx) =
     fx * Cx(&2 * sin (a * drop u) / drop u)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_div; CX_MUL; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

(* The singular "g" part of the 283I integral: it equals f x times the       *)
(* Dirichlet integral over [-1,1] (scaled by 2), which tends to 2 pi f x.    *)
let GPART_VALUE = prove
 (`!(f:real->complex) x a.
     &0 < a
     ==> integral (:real^1)
           (\u. Cx (sin (a * drop u)) *
                (Cx (&2 * inv (drop u)) *
                 (if abs (drop u) <= &1 then f x else vec 0))) =
         f x *
         Cx(real_integral (real_interval[-- &1,&1]) (\u. &2 * sin(a * u) /
           u))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_COND_VEC0] THEN
  SUBGOAL_THEN
   `!u:real^1. abs(drop u) <= &1 <=> u IN interval[lift(-- &1),lift(&1)]`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV; GPART_INTEGRAND_REWRITE] THEN
  SUBGOAL_THEN
   `(\u:real. &2 * sin(a * u) / u) real_integrable_on real_interval[-- &1,&1]`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
    ASM_SIMP_TAC[SIN_STRETCH_OVER_X_INTEGRABLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real. &2 * sin(a * u) / u`; `real_interval[-- &1,&1]`]
    CX_REAL_INTEGRAL_BRIDGE) THEN
  ASM_REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN BETA_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC INTEGRABLE_CX_DROP_COMPOSE THEN ASM_REWRITE_TAC[]);;

(* Unconditional integrability of the stretched sinc sin(c u)/u on any       *)
(* interval (the c > 0 case is SIN_STRETCH_OVER_X_INTEGRABLE; c < 0 by       *)
(* oddness, c = 0 trivially).                                                *)
let SIN_STRETCH_OVER_X_INTEGRABLE_ALL = prove
 (`!a b c:real. (\u. sin(c * u) / u) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `c = &0 \/ &0 < c \/ &0 < --c`) THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; SIN_0; real_div; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_INTEGRABLE_0];
    POP_ASSUM STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SIN_STRETCH_OVER_X_INTEGRABLE];
      SUBGOAL_THEN
       `(\u. sin(c * u) / u) = (\u. --(sin(--c * u) / u))`
       (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
        REWRITE_TAC[REAL_MUL_LNEG; SIN_NEG] THEN
        REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_NEG];
        MATCH_MP_TAC REAL_INTEGRABLE_NEG THEN
        ASM_SIMP_TAC[SIN_STRETCH_OVER_X_INTEGRABLE]]]]);;

(* The g-part of the 283I integral tends to f x times 2 pi (the Dirichlet    *)
(* limit GPART_LIMIT gives pi over [-1,1]; the factor 2 from the kernel      *)
(* doubles it).                                                              *)
let GPART_LIMIT_FULL = prove
 (`!(f:real->complex) x.
     ((\a. integral (:real^1)
             (\u. Cx (sin (a * drop u)) *
                  (Cx (&2 * inv (drop u)) *
                   (if abs (drop u) <= &1 then f x else vec 0))))
      --> f x * Cx(&2 * pi)) at_posinfinity`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\a. (f:real->complex) x *
        Cx(real_integral (real_interval[-- &1,&1]) (\u. &2 * sin(a * u) / u))`
          THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN
    EXISTS_TAC `&1` THEN X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC GPART_VALUE THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `!a. real_integral (real_interval[-- &1,&1]) (\u. &2 * sin(a * u) / u) =
          &2 * real_integral (real_interval[-- &1,&1]) (\u. sin(a * u) / u)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
      REWRITE_TAC[SIN_STRETCH_OVER_X_INTEGRABLE_ALL];
      ALL_TAC] THEN
    REWRITE_TAC[CX_MUL; COMPLEX_MUL_ASSOC] THEN
    MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
    MP_TAC(REWRITE_RULE[REALLIM_COMPLEX; o_DEF] GPART_LIMIT) THEN
    REWRITE_TAC[]]);;

(* The g-part integrand is integrable on the whole line (needed to split the *)
(* substituted integral into RL-part + g-part via INTEGRAL_ADD).             *)
let GPART_INTEGRABLE = prove
 (`!(f:real->complex) x a.
     (\u. Cx (sin (a * drop u)) *
          (Cx (&2 * inv (drop u)) *
           (if abs (drop u) <= &1 then f x else vec 0))) integrable_on
             (:real^1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_COND_VEC0] THEN
  SUBGOAL_THEN
   `!u:real^1. abs(drop u) <= &1 <=> u IN interval[lift(-- &1),lift(&1)]`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; GPART_INTEGRAND_REWRITE] THEN
  MATCH_MP_TAC INTEGRABLE_COMPLEX_LMUL THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC INTEGRABLE_CX_DROP_COMPOSE THEN
  MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
  REWRITE_TAC[SIN_STRETCH_OVER_X_INTEGRABLE_ALL]);;

(* 283I crux: after t = x - u, the whole inversion integral tends to 2 pi f  *)
(* x. Split the integrand (INTEGRAND_SPLIT_283I) into the L^1 "difference"   *)
(* part (--> 0 by Riemann-Lebesgue, RLPART_LIMIT) and the singular "g" part  *)
(* (--> 2 pi f x, GPART_LIMIT_FULL); add the two limits.                     *)
let SUBST_INTEGRAL_LIMIT = prove
 (`!(f:real->complex) x K d.
     &0 < d /\ d <= &1 /\ &0 <= K /\
     (!v. abs v <= d ==> norm(f(x - v) - f x) <= K * abs v) /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> ((\a. integral (:real^1)
                (\u. Cx (&2 * sin (a * drop u) / drop u) * f (x - drop u)))
          --> f x * Cx(&2 * pi)) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INTEGRAND_SPLIT_283I] THEN
  SUBGOAL_THEN
   `!a. integral (:real^1)
         (\u. Cx (sin (a * drop u)) *
              (Cx (&2 * inv (drop u)) *
               (f (x - drop u) - (if abs (drop u) <= &1 then f x else vec 0)))
                 +
              Cx (sin (a * drop u)) *
              (Cx (&2 * inv (drop u)) *
               (if abs (drop u) <= &1 then f x else vec 0))) =
        integral (:real^1)
          (\u. Cx (sin (a * drop u)) *
               (Cx (&2 * inv (drop u)) *
                (f (x - drop u) - (if abs (drop u) <= &1 then f x else vec
                  0)))) +
        integral (:real^1)
          (\u. Cx (sin (a * drop u)) *
               (Cx (&2 * inv (drop u)) *
                (if abs (drop u) <= &1 then f x else vec 0)))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_ADD THEN
    REWRITE_TAC[GPART_INTEGRABLE] THEN
    MP_TAC(ISPECL
      [`\u. Cx (&2 * inv u) *
            ((f:real->complex)(x - u) - (if abs u <= &1 then f x else vec 0))`;
       `a:real`] CX_SIN_H_INTEGRABLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`f:real->complex`; `x:real`; `K:real`;
      `d:real`] H283I_ABSINT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
  MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real->complex`; `x:real`; `K:real`;
     `d:real`] RLPART_LIMIT) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GPART_LIMIT_FULL]]);;

(* ------------------------------------------------------------------------- *)
(* Fremlin 283I (raw form): if f is L^1 on the line and Lipschitz at x, then *)
(* INT_{-a}^a e^{ixy} sqrt(2 pi) fhat(y) dy --> 2 pi f x as a --> +inf.      *)
(* Chain FOURIER_283H_RAW (Fubini identity), SUBSTITUTED_RHS (t = x - u),    *)
(* and                                                                       *)
(* SUBST_INTEGRAL_LIMIT (the split limit).                                   *)
(* ------------------------------------------------------------------------- *)
let FOURIER_283I_RAW = prove
 (`!(f:real->complex) x K d.
     &0 < d /\ d <= &1 /\ &0 <= K /\
     (!v. abs v <= d ==> norm(f(x - v) - f x) <= K * abs v) /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> ((\a. integral (interval[lift(--a),lift a])
                (\y. cexp(ii * Cx x * Cx(drop y)) * Cx(sqrt(&2 * pi)) *
                     fourier f (drop y)))
          --> f x * Cx(&2 * pi)) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\a. integral (:real^1)
          (\u. Cx (&2 * sin (a * drop u) / drop u) * (f:real->complex) (x -
            drop u))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN
    EXISTS_TAC `&0` THEN X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real->complex`; `a:real`;
      `x:real`] FOURIER_283H_RAW) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `a >= &0 ==> &0 <= a`];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUBSTITUTED_RHS]];
    MP_TAC(ISPECL [`f:real->complex`; `x:real`; `K:real`; `d:real`]
      SUBST_INTEGRAL_LIMIT) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Normalisation of 283I to the standard inversion form.  First: fhat is     *)
(* continuous on the line (from sequential continuity                        *)
(* FOURIER_CONTINUOUS_SEQ),                                                  *)
(* hence the modulated integrand e^{ixy} fhat(y) is integrable on [-a,a].    *)
(* ------------------------------------------------------------------------- *)
let FOURIER_CONTINUOUS_ON = prove
 (`!(f:real->complex).
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> (\z. fourier f (drop z)) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
  MAP_EVERY X_GEN_TAC [`xx:num->real^1`; `aa:real^1`] THEN STRIP_TAC THEN
  REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`f:real->complex`; `drop aa`] FOURIER_CONTINUOUS_SEQ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      ASM_SIMP_TAC[FOURIER_MODULATION_ABSINT];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
      REWRITE_TAC[o_DEF]];
    DISCH_THEN(MP_TAC o ISPEC `\k:num. drop(xx k)`) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM o_DEF; GSYM REAL_TENDSTO] THEN
    FIRST_X_ASSUM ACCEPT_TAC]);;

(* The modulated fhat integrand e^{ixy} fhat(y) is integrable on [-a,a]      *)
(* (continuous fhat times continuous exponential, on a compact interval).    *)
let FOURIER_MODULATED_INTEGRABLE = prove
 (`!(f:real->complex) x a.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> (\y. cexp(ii * Cx x * Cx(drop y)) * fourier f (drop y))
         integrable_on interval[lift(--a),lift a]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MP_TAC(ISPECL [`\y:real^1. y`; `interval[lift(--a),lift a]`]
        CONTINUOUS_ON_CX_DROP) THEN
      REWRITE_TAC[CONTINUOUS_ON_ID];
      REWRITE_TAC[CONTINUOUS_ON_CEXP; CONTINUOUS_ON_ID]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[FOURIER_CONTINUOUS_ON; SUBSET_UNIV]]);;

(* Constants for normalising sqrt(2 pi).                                     *)
let SQRT_2PI_POS = prove
 (`&0 < sqrt(&2 * pi)`,
  MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let CX_INV_2PI_SQRT = prove
 (`Cx(inv(&2 * pi)) * Cx(sqrt(&2 * pi)) = Cx(inv(sqrt(&2 * pi)))`,
  REWRITE_TAC[GSYM CX_MUL] THEN AP_TERM_TAC THEN
  MP_TAC SQRT_2PI_POS THEN MP_TAC(SPEC `&2 * pi` SQRT_POW_2) THEN
  MP_TAC PI_POS THEN CONV_TAC REAL_FIELD);;

let CX_INV_2PI_CANCEL = prove
 (`!fx. Cx(inv(&2 * pi)) * (fx * Cx(&2 * pi)) = fx`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_RING `ic * (fx * tp) = (ic * tp) * fx`] THEN
  REWRITE_TAC[GSYM CX_MUL] THEN
  SUBGOAL_THEN `inv(&2 * pi) * (&2 * pi) = &1` SUBST1_TAC THENL
   [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[COMPLEX_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* Fremlin 283I (standard normalised form): the pointwise Fourier inversion. *)
(* If f is L^1 on the line and Lipschitz at x, then                          *)
(* (1 / sqrt(2 pi)) INT_{-a}^a e^{ixy} fhat(y) dy --> f x as a --> +inf.     *)
(* Obtained from FOURIER_283I_RAW by pulling out sqrt(2 pi) (the integrand   *)
(* is                                                                        *)
(* integrable, FOURIER_MODULATED_INTEGRABLE) and rescaling the limit.        *)
(* ------------------------------------------------------------------------- *)
let FOURIER_283I = prove
 (`!(f:real->complex) x K d.
     &0 < d /\ d <= &1 /\ &0 <= K /\
     (!v. abs v <= d ==> norm(f(x - v) - f x) <= K * abs v) /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> ((\a. Cx(inv(sqrt(&2 * pi))) *
               integral (interval[lift(--a),lift a])
                 (\y. cexp(ii * Cx x * Cx(drop y)) * fourier f (drop y)))
          --> f x) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->complex`; `x:real`; `K:real`;
    `d:real`] FOURIER_283I_RAW) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a. integral (interval[lift(--a),lift a])
          (\y. cexp(ii * Cx x * Cx(drop y)) * Cx(sqrt(&2 * pi)) *
               (fourier:(real->complex)->real->complex) f (drop y)) =
        Cx(sqrt(&2 * pi)) *
        integral (interval[lift(--a),lift a])
          (\y. cexp(ii * Cx x * Cx(drop y)) * fourier f (drop y))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV)
      [SIMPLE_COMPLEX_ARITH `cexp e * Cx s * ff = Cx s * (cexp e * ff)`] THEN
    MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
    ASM_SIMP_TAC[FOURIER_MODULATED_INTEGRABLE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o ISPEC `Cx(inv(&2 * pi))` o MATCH_MP LIM_COMPLEX_LMUL)
    THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; CX_INV_2PI_SQRT] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; CX_INV_2PI_CANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Fremlin 283J: when fhat is itself integrable, the truncation limit of     *)
(* 283I                                                                      *)
(* collapses to the genuine full-line inverse-transform integral, which then *)
(* equals f x.  I.e. f = (fhat)check at any Lipschitz point.                 *)
(* ------------------------------------------------------------------------- *)

(* Symmetric truncations of an integrable function converge to its integral: *)
(* INT_{[-a,a]} g --> INT_R g  as a --> +inf.  From HAS_INTEGRAL_ALT (the    *)
(* improper integral as a ball-limit); ball(0,B) SUBSET [-a,a] once a >= B.  *)
let SYMMETRIC_INTERVAL_LIMIT = prove
 (`!(g:real^1->complex).
     g integrable_on (:real^1)
     ==> ((\a. integral (interval[lift(--a),lift a]) g) --> integral (:real^1)
       g)
         at_posinfinity`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_ALT] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; dist; real_ge] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`lift(--a)`; `lift a`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BALL_1; SUBSET_INTERVAL_1] THEN
    REWRITE_TAC[LIFT_DROP; DROP_ADD; DROP_SUB; LIFT_NEG; DROP_VEC;
      LIFT_NUM] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[ETA_AX]]);;

(* When fhat is L^1, e^{ixy} fhat(y) is integrable on the whole line         *)
(* (bounded modulation of an L^1 function -- reuse FOURIER_MODULATION_ABSINT *)
(* at d = -x).                                                               *)
let FOURIER_INV_MODULATED_INTEGRABLE = prove
 (`!(f:real->complex) x.
     (\z. fourier f (drop z)) absolutely_integrable_on (:real^1)
     ==> (\y. cexp(ii * Cx x * Cx(drop y)) * fourier f (drop y))
         integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_EQ THEN
  EXISTS_TAC
   `\y. cexp(--(ii * Cx(--x) * Cx(drop y))) *
        (fourier:(real->complex)->real->complex) f (drop y)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`fourier (f:real->complex)`; `--x:real`]
      FOURIER_MODULATION_ABSINT) THEN
    ASM_REWRITE_TAC[]]);;

(* Fremlin 283J proper: (1/sqrt(2pi)) INT_R e^{ixy} fhat(y) dy = f x. The    *)
(* 283I truncation limit and the full-line integral (via SYMMETRIC_INTERVAL_ *)
(* LIMIT, scaled) are two limits of the same sequence, so LIM_UNIQUE.        *)
let FOURIER_283J = prove
 (`!(f:real->complex) x K d.
     &0 < d /\ d <= &1 /\ &0 <= K /\
     (!v. abs v <= d ==> norm(f(x - v) - f x) <= K * abs v) /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. fourier f (drop z)) absolutely_integrable_on (:real^1)
     ==> Cx(inv(sqrt(&2 * pi))) *
         integral (:real^1)
           (\y. cexp(ii * Cx x * Cx(drop y)) * fourier f (drop y)) =
         f x`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `at_posinfinity` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\a. Cx(inv(sqrt(&2 * pi))) *
        integral (interval[lift(--a),lift a])
          (\y. cexp(ii * Cx x * Cx(drop y)) *
               (fourier:(real->complex)->real->complex) f (drop y))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_AT_POSINFINITY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
    MATCH_MP_TAC SYMMETRIC_INTERVAL_LIMIT THEN
    MATCH_MP_TAC FOURIER_INV_MODULATED_INTEGRABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FOURIER_283I THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `d:real`] THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* SECTION 5. Fourier-transform calculus (Fremlin 283C(f-i), 283K).          *)
(*                                                                           *)
(* Provides the derivative/multiplication duality for the transform:         *)
(*   283Cf  fhat continuous              (already FOURIER_CONTINUOUS_ON)     *)
(*   283Cg  fhat(y) --> 0 as |y| --> inf                                     *)
(*   283Ch  d/dy fhat(y) = -i/sqrt(2pi) INT e^{-iyx} x f(x) dx               *)
(*   283Ci  transform of a derivative: (f')hat(y) = iy fhat(y)               *)
(*   283K   f, f', f'' integrable  ==>  fhat integrable                      *)
(* These feed the Schwartz-function theory of 284 (284C inversion, 284O      *)
(* Plancherel), which 286 needs.                                             *)
(* ========================================================================= *)

(* Transport a (vector/real) derivative across an equal derivative value:    *)
(* rewrite the derivative in the conclusion to a convenient equal form.      *)
(* (Replaces a MESON[] `d = e ==> ...` idiom repeated throughout the file.)  *)
let VDERIV_EQ = prove
 (`!(f:real^1->real^N) d e net.
     d = e ==> (f has_vector_derivative d) net ==> (f has_vector_derivative e)
       net`,
  MESON_TAC[]);;

let RDERIV_EQ = prove
 (`!(f:real->real) d e net.
     d = e ==> (f has_real_derivative d) net ==> (f has_real_derivative e)
       net`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* An integrable function on the line that has a limit at +infinity must     *)
(* have                                                                      *)
(* limit zero (otherwise the tail integral of its norm would diverge).       *)
(* ------------------------------------------------------------------------- *)

(* Arithmetic helper: keeps the product (N-B)*P atomic (P = |L|/2), avoiding *)
(* the a*b/c reassociation that defeats REAL_ARITH.                          *)
let TAIL_ARITH_HELPER = prove
 (`!M N B P:real. &0 <= M /\ &0 < P /\ (&2 * M) / P < N - B
     ==> M < (N - B) * P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * M < (N - B) * P` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ]; ASM_REAL_ARITH_TAC]);;

let INTEGRABLE_TENDSTO_POSINFINITY_ZERO = prove
 (`!(f:real->complex) L.
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (f --> L) at_posinfinity
     ==> L = vec 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < n) /\ &0 <= n ==> n = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_AT_POSINFINITY]) THEN
  DISCH_THEN(MP_TAC o SPEC `norm(L:complex) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_ge; dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \z:real^1. lift(norm((f:real->complex)(drop z)))` THEN
  SUBGOAL_THEN `(g:real^1->real^1) integrable_on (:real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  ABBREV_TAC `M = drop(integral (:real^1) (g:real^1->real^1))` THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(L:complex) / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * M) / (norm(L:complex) / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* choose N with (N - B)*(|L|/2) > M                                       *)
  MP_TAC(SPEC `B + (&2 * M) / (norm(L:complex) / &2) + &1` REAL_ARCH_SIMPLE)
    THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  ABBREV_TAC `N = &n:real` THEN
  (* the tail lower bound: content[B,N]*(|L|/2) <= INT_{[B,N]} g <= M        *)
  SUBGOAL_THEN `B <= N` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (interval[lift B,lift N]) (g:real^1->real^1)) <= M`
   ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^1)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[LIFT_DROP; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(N - B) * (norm(L:complex) / &2) <=
    drop(integral (interval[lift B,lift N]) (g:real^1->real^1))`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^1. lift(norm(L:complex) / &2)`; `g:real^1->real^1`;
                   `interval[lift B,lift N]`] INTEGRAL_DROP_LE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[INTEGRABLE_CONST];
        MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `(:real^1)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
        X_GEN_TAC `z:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
        STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC(NORM_ARITH
         `norm(fz - L) < norm L / &2 ==> norm L / &2 <= norm fz`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[INTEGRAL_CONST; LIFT_DROP] THEN
      ASM_SIMP_TAC[CONTENT_1; LIFT_DROP; DROP_CMUL] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* combine: (N-B)*(|L|/2) <= INT <= M, but N chosen so M < (N-B)*(|L|/2)   *)
  SUBGOAL_THEN `M < (N - B) * (norm(L:complex) / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC TAIL_ARITH_HELPER THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Derivative of the Fourier kernel x |-> e^{-iyx} in x: it is -iy e^{-iyx}. *)
(* ------------------------------------------------------------------------- *)
let CEXP_KERNEL_VECTOR_DERIV = prove
 (`!y a:real^1.
     ((\z. cexp(--(ii * Cx y * Cx(drop z)))) has_vector_derivative
      (--(ii * Cx y) * cexp(--(ii * Cx y * Cx(drop a))))) (at a)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
  COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

(* A function differentiable everywhere on the line (as a real^1->complex    *)
(* map via drop) is continuous there.                                        *)
let FF_CONTINUOUS_ON = prove
 (`!(ff:real->complex) (ffp:real->complex).
     (!x. ((\z. ff(drop z)) has_vector_derivative (ffp x)) (at(lift x)))
     ==> (\z. ff(drop z)) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
  EXISTS_TAC `(ffp:real->complex)(drop x)` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop(x:real^1)`) THEN
  REWRITE_TAC[LIFT_DROP]);;

(* Hence e^{-iyx} ff(x) is integrable on any bounded interval (continuous on *)
(* a compact set).                                                           *)
let KERNEL_TIMES_FF_INTEGRABLE = prove
 (`!(ff:real->complex) (ffp:real->complex) y a.
     (!x. ((\z. ff(drop z)) has_vector_derivative (ffp x)) (at(lift x)))
     ==> (\z. cexp(--(ii * Cx y * Cx(drop z))) * ff(drop z))
         integrable_on interval[lift(--a),lift a]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MP_TAC(ISPECL [`\z:real^1. z`; `interval[lift(--a),lift a]`]
        CONTINUOUS_ON_CX_DROP) THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      REWRITE_TAC[CONTINUOUS_ON_CEXP; CONTINUOUS_ON_ID]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC FF_CONTINUOUS_ON THEN EXISTS_TAC `ffp:real->complex` THEN
    ASM_REWRITE_TAC[]]);;

(* Abstract rearrangement (kept away from COMPLEX_RING's concrete-atom       *)
(* lookup, which trips on the integral/cexp subterms).                       *)
let COMPLEX_COMBINE_SUB = prove
 (`!A B C D:complex. A = B - C /\ A = D ==> C = B + --D`,
  CONV_TAC COMPLEX_RING);;

(* Pull the constant -iy out of INT((-iy k) ff) = -iy INT(k ff). Bound       *)
(* variable                                                                  *)
(* z chosen to match the target integrals so the atoms coincide for          *)
(* COMPLEX_RING.                                                             *)
let KERNEL_LMUL_INTEGRAL = prove
 (`!(ff:real->complex) (ffp:real->complex) y a.
     (!x. ((\z. ff(drop z)) has_vector_derivative (ffp x)) (at(lift x)))
     ==> integral (interval[lift(--a),lift a])
          (\z. (--(ii * Cx y) * cexp(--(ii * Cx y * Cx(drop z)))) * ff(drop z))
            =
         --(ii * Cx y) * integral (interval[lift(--a),lift a])
          (\z. cexp(--(ii * Cx y * Cx(drop z))) * ff(drop z))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
  MATCH_MP_TAC KERNEL_TIMES_FF_INTEGRABLE THEN
  EXISTS_TAC `ffp:real->complex` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Finite-interval integration by parts for the Fourier kernel: for ff       *)
(* differentiable with derivative ffp (both viewed via drop), and            *)
(* e^{-iyx}ffp                                                               *)
(* integrable on [-a,a],                                                     *)
(*   INT_{-a}^a e^{-iyx} ffp(x) dx =                                         *)
(*     (e^{-iya}ff(a) - e^{iya}ff(-a)) + iy INT_{-a}^a e^{-iyx} ff(x) dx.    *)
(* ------------------------------------------------------------------------- *)
let FOURIER_IBP_FINITE = prove
 (`!(ff:real->complex) (ffp:real->complex) y a.
     &0 <= a /\
     (!x. ((\z. ff(drop z)) has_vector_derivative (ffp x)) (at(lift x))) /\
     (\z. cexp(--(ii * Cx y * Cx(drop z))) * ffp(drop z))
        integrable_on interval[lift(--a),lift a]
     ==> integral (interval[lift(--a),lift a])
           (\z. cexp(--(ii * Cx y * Cx(drop z))) * ffp(drop z)) =
         (cexp(--(ii * Cx y * Cx a)) * ff a -
          cexp(--(ii * Cx y * Cx(--a))) * ff(--a)) +
         (ii * Cx y) *
         integral (interval[lift(--a),lift a])
           (\z. cexp(--(ii * Cx y * Cx(drop z))) * ff(drop z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`( * ):complex->complex->complex`;
    `\z:real^1. cexp(--(ii * Cx y * Cx(drop z)))`;
    `\z:real^1. (ff:real->complex)(drop z)`;
    `\z:real^1. --(ii * Cx y) * cexp(--(ii * Cx y * Cx(drop z)))`;
    `\z:real^1. (ffp:real->complex)(drop z)`;
    `lift(--a)`; `lift a`;
    `(cexp(--(ii * Cx y * Cx a)) * ff a -
      cexp(--(ii * Cx y * Cx(--a))) * ff(--a)) -
     integral (interval[lift(--a),lift a])
       (\z. cexp(--(ii * Cx y * Cx(drop z))) * ffp(drop z))`]
   INTEGRATION_BY_PARTS_SIMPLE) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL; LIFT_DROP] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
        REWRITE_TAC[CEXP_KERNEL_VECTOR_DERIV];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `drop(x:real^1)`) THEN
        REWRITE_TAC[LIFT_DROP]];
      REWRITE_TAC[COMPLEX_RING `b - (b - z) = z`] THEN
      ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]];
    ALL_TAC] THEN
  (* Endgame: INTEGRAL_UNIQUE gives INT((-iy k) ff) = boundary - INT(k ffp); *)
  (* KERNEL_LMUL_INTEGRAL rewrites that LHS to -iy INT(k ff); COMPLEX_RING   *)
  (* closes.                                                                 *)
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[] o
             MATCH_MP INTEGRAL_UNIQUE o REWRITE_RULE[]) THEN
  MP_TAC(ISPECL [`ff:real->complex`; `ffp:real->complex`; `y:real`; `a:real`]
    KERNEL_LMUL_INTEGRAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  (* Combine INT((-iy k) ff) = boundary - INT(k ffp) with = -iy INT(k ff)    *)
  (* via the abstract rearrangement, then simplify --(-iy X) = iy X.         *)
  FIRST_X_ASSUM(fun eq2 -> FIRST_X_ASSUM(fun eq1 ->
    MP_TAC(MATCH_MP COMPLEX_COMBINE_SUB (CONJ eq1 eq2)))) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* The two boundary terms e^{-iya}ff(a) and e^{iya}ff(-a) vanish as a-->+inf *)
(* (kernel modulus 1, ff --> 0 at each end).                                 *)
(* ------------------------------------------------------------------------- *)
let BOUNDARY_TERM_POS = prove
 (`!(ff:real->complex) y.
     (ff --> vec 0) at_posinfinity
     ==> ((\a. cexp(--(ii * Cx y * Cx a)) * ff a) --> vec 0) at_posinfinity`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL_BOUNDED THEN
  EXISTS_TAC `&1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN BETA_TAC THEN
    DISJ1_TAC THEN REWRITE_TAC[FOURIER_KERNEL_NORM; REAL_LE_REFL];
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0]]);;

let BOUNDARY_TERM_NEG = prove
 (`!(ff:real->complex) y.
     ((\a. ff(--a)) --> vec 0) at_posinfinity
     ==> ((\a. cexp(--(ii * Cx y * Cx(--a))) * ff(--a)) --> vec 0)
       at_posinfinity`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL_BOUNDED THEN
  EXISTS_TAC `&1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN BETA_TAC THEN
    DISJ1_TAC THEN REWRITE_TAC[FOURIER_KERNEL_NORM; REAL_LE_REFL];
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0]]);;

(* ------------------------------------------------------------------------- *)
(* Fremlin 283Ci (raw form): the transform of a derivative.  For ff          *)
(* differentiable with derivative ffp (both L^1 after modulation), ff --> 0  *)
(* at both ends,                                                             *)
(*   INT_R e^{-iyx} ffp(x) dx = iy INT_R e^{-iyx} ff(x) dx.                  *)
(* Take a --> +inf in FOURIER_IBP_FINITE: LHS and the INT(k ff) both         *)
(* converge                                                                  *)
(* (SYMMETRIC_INTERVAL_LIMIT), the boundary term vanishes (BOUNDARY_TERM     *)
(* lemmas).                                                                  *)
(* ------------------------------------------------------------------------- *)
let FOURIER_283CI_RAW = prove
 (`!(ff:real->complex) (ffp:real->complex) y.
     (!x. ((\z. ff(drop z)) has_vector_derivative (ffp x)) (at(lift x))) /\
     (ff --> vec 0) at_posinfinity /\
     ((\a. ff(--a)) --> vec 0) at_posinfinity /\
     (\z. cexp(--(ii * Cx y * Cx(drop z))) * ffp(drop z))
        absolutely_integrable_on (:real^1) /\
     (\z. cexp(--(ii * Cx y * Cx(drop z))) * ff(drop z))
        absolutely_integrable_on (:real^1)
     ==> integral (:real^1) (\z. cexp(--(ii * Cx y * Cx(drop z))) * ffp(drop
       z)) =
         (ii * Cx y) *
         integral (:real^1) (\z. cexp(--(ii * Cx y * Cx(drop z))) * ff(drop
           z))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `at_posinfinity` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\a. integral (interval[lift(--a),lift a])
          (\z. cexp(--(ii * Cx y * Cx(drop z))) * (ffp:real->complex)(drop z))`
            THEN
  REWRITE_TAC[TRIVIAL_LIMIT_AT_POSINFINITY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SYMMETRIC_INTERVAL_LIMIT THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`at_posinfinity`;
    `\a. (cexp(--(ii * Cx y * Cx a)) * (ff:real->complex) a -
          cexp(--(ii * Cx y * Cx(--a))) * ff(--a)) +
         (ii * Cx y) *
         integral (interval[lift(--a),lift a])
           (\z. cexp(--(ii * Cx y * Cx(drop z))) * ff(drop z))`;
    `\a. integral (interval[lift(--a),lift a])
           (\z. cexp(--(ii * Cx y * Cx(drop z))) * (ffp:real->complex)(drop
             z))`;
    `(ii * Cx y) *
     integral (:real^1) (\z. cexp(--(ii * Cx y * Cx(drop z))) *
       (ff:real->complex)(drop z))`]
   LIM_TRANSFORM_EVENTUALLY) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN EXISTS_TAC `&0` THEN
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FOURIER_IBP_FINITE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^1)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
     [SUBST1_TAC(VECTOR_ARITH `vec 0:complex = vec 0 - vec 0`) THEN
      MATCH_MP_TAC LIM_SUB THEN
      ASM_SIMP_TAC[BOUNDARY_TERM_POS; BOUNDARY_TERM_NEG];
      MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
      MATCH_MP_TAC SYMMETRIC_INTERVAL_LIMIT THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Fremlin 283Ci, normalised: (f')hat(y) = iy fhat(y).  The 1/sqrt(2pi)      *)
(* normalising constant is a commuting factor (MUL_SWAP3 keeps it away from  *)
(* COMPLEX_RING's concrete-atom lookup).                                     *)
(* ------------------------------------------------------------------------- *)
let MUL_SWAP3 = prove
 (`!c e w:complex. c * (e * w) = e * (c * w)`, CONV_TAC COMPLEX_RING);;

let FOURIER_283CI = prove
 (`!(ff:real->complex) (ffp:real->complex) y.
     (!x. ((\z. ff(drop z)) has_vector_derivative (ffp x)) (at(lift x))) /\
     (ff --> vec 0) at_posinfinity /\
     ((\a. ff(--a)) --> vec 0) at_posinfinity /\
     (\z. cexp(--(ii * Cx y * Cx(drop z))) * ffp(drop z))
        absolutely_integrable_on (:real^1) /\
     (\z. cexp(--(ii * Cx y * Cx(drop z))) * ff(drop z))
        absolutely_integrable_on (:real^1)
     ==> fourier ffp y = (ii * Cx y) * fourier ff y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  MP_TAC(ISPECL [`ff:real->complex`; `ffp:real->complex`; `y:real`]
    FOURIER_283CI_RAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MUL_SWAP3]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary for 283K: 1/(1+y^2) is integrable over the whole line, with     *)
(* INT_{-a}^a = 2 atn a; this is the dominator for fhat.                     *)
(* ------------------------------------------------------------------------- *)
let INV_SQ_INTERVAL_INTEGRAL = prove
 (`!a. &0 <= a
       ==> real_integral (real_interval[--a,a]) (\y. inv(&1 + y pow 2)) = &2 *
         atn a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `&2 * atn a = atn a - atn(--a)` SUBST1_TAC THENL
   [REWRITE_TAC[ATN_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ATN]]);;

let INV_SQ_REAL_INTEGRABLE = prove
 (`(\y. inv(&1 + y pow 2)) real_integrable_on (:real)`,
  MP_TAC(ISPECL
   [`\k y. if abs y <= &k then inv(&1 + y pow 2) else &0`;
    `\y. inv(&1 + y pow 2)`; `(:real)`]
   REAL_MONOTONE_CONVERGENCE_INCREASING) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `(\y. if abs y <= &k then inv(&1 + y pow 2) else &0) =
      (\y. if y IN real_interval[-- &k, &k] then inv(&1 + y pow 2) else &0)`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN GEN_TAC THEN
      REWRITE_TAC[REAL_ARITH `abs y <= k <=> --k <= y /\ y <= k`];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      X_GEN_TAC `w:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= inv(&1 + x pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `abs x` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs x <= &n` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N:real` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    REWRITE_TAC[real_bounded; FORALL_IN_GSPEC] THEN
    EXISTS_TAC `pi` THEN X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN
     `real_integral (:real) (\y. if abs y <= &k then inv(&1 + y pow 2) else &0)
       =
      &2 * atn(&k)`
     SUBST1_TAC THENL
     [SUBGOAL_THEN
       `(\y. if abs y <= &k then inv(&1 + y pow 2) else &0) =
        (\y. if y IN real_interval[-- &k, &k] then inv(&1 + y pow 2) else &0)`
       SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; IN_REAL_INTERVAL] THEN GEN_TAC THEN
        REWRITE_TAC[REAL_ARITH `abs y <= k <=> --k <= y /\ y <= k`];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV] THEN
      MATCH_MP_TAC INV_SQ_INTERVAL_INTEGRAL THEN REWRITE_TAC[REAL_POS];
      MP_TAC(SPEC `&k:real` ATN_BOUND) THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* 283K: if f, f', f'' are integrable (with f, f' vanishing at +-inf and     *)
(* f differentiable with derivative f', f' with derivative f''), then fhat   *)
(* is                                                                        *)
(* integrable. Iterating 283Ci gives (f'')hat(y) = -y^2 fhat(y); with fhat   *)
(* and                                                                       *)
(* (f'')hat bounded (FOURIER_BOUND_UNIFORM) this yields |fhat(y)| <=         *)
(* 2K/(1+y^2),                                                               *)
(* an integrable dominator.                                                  *)
(* ------------------------------------------------------------------------- *)

(* (iy)^2 = -y^2 as a complex scalar (Cx(y^2) opaque to COMPLEX_RING unless  *)
(* rewritten to (Cx y) pow 2 first).                                         *)
let II_CX_SQ = prove
 (`!y. (ii * Cx y) * (ii * Cx y) = --(Cx(y pow 2))`,
  GEN_TAC THEN
  SUBGOAL_THEN `(ii * Cx y) * (ii * Cx y) = (ii * ii) * Cx(y pow 2)`
   SUBST1_TAC THENL
   [REWRITE_TAC[CX_POW] THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[GSYM COMPLEX_POW_2; COMPLEX_POW_II_2] THEN
    CONV_TAC COMPLEX_RING]);;

(* |w| <= K and |-y^2 w| <= K  ==>  |w| <= 2K/(1+y^2).                       *)
let FHAT_DOMINATION_BOUND = prove
 (`!(w:complex) y K.
     norm w <= K /\ norm(--(Cx(y pow 2)) * w) <= K
     ==> norm w <= (&2 * K) * inv(&1 + y pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(--(Cx(y pow 2)) * w) = y pow 2 * norm w` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; NORM_NEG; COMPLEX_NORM_CX] THEN
    MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + y pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM real_div] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
  ASM_REAL_ARITH_TAC);;

(* fhat is uniformly bounded when f is L^1.                                  *)
let FOURIER_BOUND_UNIFORM = prove
 (`!(f:real->complex).
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> ?K. !y. norm(fourier f y) <= K`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `&1 / sqrt(&2 * pi) *
              drop(integral (:real^1) (\x. lift(norm((f:real->complex)(drop
                x)))))` THEN
  GEN_TAC THEN MATCH_MP_TAC FOURIER_BOUND THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    ASM_SIMP_TAC[FOURIER_MODULATION_ABSINT];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    REWRITE_TAC[o_DEF]]);;

(* The K/(1+y^2) dominator, as a vector function integrable on the whole     *)
(* line.                                                                     *)
let DOMINATOR_SQ_INTEGRABLE = prove
 (`!K. (\z:real^1. lift((&2 * K) * inv(&1 + drop z pow 2))) integrable_on
   (:real^1)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\y. (&2 * K) * inv(&1 + y pow 2)) real_integrable_on (:real)`
   MP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN REWRITE_TAC[INV_SQ_REAL_INTEGRABLE];
    REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_UNIV; o_DEF; LIFT_DROP]]);;

(* Fremlin 283K proper: f, f', f'' integrable (with f, f' differentiable and *)
(* vanishing at +-inf) ==> fhat integrable. The dominating bound |fhat(y)|   *)
(* <=                                                                        *)
(* 2K/(1+y^2) comes from (f'')hat(y) = -y^2 fhat(y) (283Ci twice) and        *)
(* boundedness.                                                              *)
let FOURIER_283K = prove
 (`!(f:real->complex) (f':real->complex) (f'':real->complex).
     (!x. ((\z. f(drop z)) has_vector_derivative (f' x)) (at(lift x))) /\
     (!x. ((\z. f'(drop z)) has_vector_derivative (f'' x)) (at(lift x))) /\
     (f --> vec 0) at_posinfinity /\ ((\a. f(--a)) --> vec 0) at_posinfinity /\
     (f' --> vec 0) at_posinfinity /\ ((\a. f'(--a)) --> vec 0) at_posinfinity
       /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. f'(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. f''(drop z)) absolutely_integrable_on (:real^1)
     ==> (\z. fourier f (drop z)) absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!(g:real->complex) y.
        (\z. g(drop z)) absolutely_integrable_on (:real^1)
        ==> (\z. cexp(--(ii * Cx y * Cx(drop z))) * g(drop z))
            absolutely_integrable_on (:real^1)`
   (LABEL_TAC "MOD") THENL
   [REPEAT STRIP_TAC THEN
     ASM_SIMP_TAC[FOURIER_MODULATION_ABSINT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. fourier f'' y = --(Cx(y pow 2)) * fourier f y`
   (LABEL_TAC "REL") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `fourier f' y = (ii * Cx y) * fourier f y /\
      fourier f'' y = (ii * Cx y) * fourier f' y`
     (fun th -> REWRITE_TAC[CONJUNCT2 th; CONJUNCT1 th] THEN
                REWRITE_TAC[COMPLEX_MUL_ASSOC; II_CX_SQ]) THEN
    CONJ_TAC THEN MATCH_MP_TAC FOURIER_283CI THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `f:real->complex` FOURIER_BOUND_UNIFORM) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K1:real`) THEN
  MP_TAC(ISPEC `f'':real->complex` FOURIER_BOUND_UNIFORM) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K2:real`) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\z:real^1. lift((&2 * (abs K1 + abs K2)) * inv(&1 + drop z pow
    2))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    ASM_SIMP_TAC[FOURIER_CONTINUOUS_ON];
    REWRITE_TAC[DOMINATOR_SQ_INTEGRABLE];
    X_GEN_TAC `z:real^1` THEN REWRITE_TAC[IN_UNIV; LIFT_DROP] THEN
    MATCH_MP_TAC FHAT_DOMINATION_BOUND THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      USE_THEN "REL" (MP_TAC o SPEC `drop(z:real^1)`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K2:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;


(* ========================================================================= *)
(* SECTION 6. Schwartz (rapidly decreasing) test functions                   *)
(* (Fremlin 284A-284C).                                                      *)
(*                                                                           *)
(* A Schwartz function h:R->C is smooth with                                *)
(* sup_x |x|^k |h^(m)(x)| < inf for all k,m.                                *)
(* We encode smoothness by an explicit derivative sequence d (d 0 = h,       *)
(* d(SUC n) the vector derivative of d n via drop) and the decay bounds.     *)
(*                                                                           *)
(* The initial consequences establish integrability, decay, and inversion;  *)
(* later sections develop the smooth bump and differentiation machinery used *)
(* for density, Plancherel, and closure under the Fourier transform.         *)
(* ========================================================================= *)

let schwartz = new_definition
 `schwartz (h:real->complex) <=>
    ?d:num->real->complex.
        d 0 = h /\
        (!n x. ((\z. d n (drop z)) has_vector_derivative (d (SUC n) x))
          (at(lift x))) /\
        (!k m. ?B. !x. abs(x) pow k * norm(d m x) <= B)`;;

(* Core domination: the k=0 and k=2 decay bounds give |g x| <=               *)
(* (B0+B2)/(1+x^2).                                                          *)
let SCHWARTZ_DECAY_DOMINATION = prove
 (`!(g:real->complex) B0 B2 x.
     (!x. abs(x) pow 0 * norm(g x) <= B0) /\
     (!x. abs(x) pow 2 * norm(g x) <= B2)
     ==> norm(g x) <= (B0 + B2) * inv(&1 + x pow 2)`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real`)) THEN
  REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_POW2_ABS] THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN REAL_ARITH_TAC);;

(* 284Bc, integrability half: a Schwartz function is (absolutely)            *)
(* integrable. From the k=0 and k=2 decay bounds |h(x)| <= (B0+B2)/(1+x^2),  *)
(* dominated by the integrable 1/(1+x^2); h is measurable (continuous, being *)
(* differentiable).                                                          *)
let SCHWARTZ_ABSINT = prove
 (`!(h:real->complex). schwartz h
     ==> (\z. h(drop z)) absolutely_integrable_on (:real^1)`,
  REWRITE_TAC[schwartz] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B0:real` o SPECL [`0`; `0`]) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B2:real` o SPECL [`2`; `0`]) THEN
  EXISTS_TAC
   `\z:real^1. lift((&2 * (abs B0 + abs B2)) * inv(&1 + drop z pow 2))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC FF_CONTINUOUS_ON THEN
    EXISTS_TAC `(d:num->real->complex)(SUC 0)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[DOMINATOR_SQ_INTEGRABLE];
    X_GEN_TAC `z:real^1` THEN REWRITE_TAC[IN_UNIV; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(abs B0 + abs B2) * inv(&1 + drop z pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCHWARTZ_DECAY_DOMINATION THEN
      CONJ_TAC THEN X_GEN_TAC `x:real` THENL
       [MP_TAC(SPEC `x:real` (ASSUME
          `!x. abs(x) pow 0 * norm((d:num->real->complex) 0 x) <= B0`)) THEN
        REAL_ARITH_TAC;
        MP_TAC(SPEC `x:real` (ASSUME
          `!x. abs(x) pow 2 * norm((d:num->real->complex) 0 x) <= B2`)) THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV THEN MP_TAC(SPEC `drop z` REAL_LE_POW_2) THEN
        REAL_ARITH_TAC]]]);;

(* A Schwartz function is globally Lipschitz (its derivative d 1 is bounded, *)
(* so                                                                        *)
(* VECTOR_DIFFERENTIABLE_BOUND / the mean value inequality applies). This    *)
(* supplies                                                                  *)
(* the Lipschitz-at-x hypothesis of 283J.                                    *)
let SCHWARTZ_LIPSCHITZ = prove
 (`!(h:real->complex). schwartz h
     ==> ?K. &0 <= K /\ !u w. norm(h u - h w) <= K * abs(u - w)`,
  REWRITE_TAC[schwartz] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o SPECL [`0`; `SUC 0`]) THEN
  EXISTS_TAC `abs B` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `w:real`] THEN
  MP_TAC(ISPECL [`\z:real^1. (d:num->real->complex) 0 (drop z)`;
                 `\z:real^1. (d:num->real->complex) (SUC 0) (drop z)`;
                 `(:real^1)`; `abs B`] VECTOR_DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `drop x`]) THEN
      REWRITE_TAC[LIFT_DROP];
      GEN_TAC THEN
      MP_TAC(SPEC `drop x` (ASSUME
        `!x. abs(x) pow 0 * norm((d:num->real->complex)(SUC 0) x) <= B`)) THEN
      REWRITE_TAC[real_pow; REAL_MUL_LID] THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`lift u`; `lift w`]) THEN
    REWRITE_TAC[IN_UNIV; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT]]);;

(* Arithmetic core of the tail estimate: x*n <= B and x >= (|B|+1)/e force n *)
(* < e.                                                                      *)
let SCHWARTZ_TAIL_ARITH = prove
 (`!x e B n:real. &0 < e /\ &0 < x /\ &0 <= n /\ x * n <= B /\ (abs B + &1) / e
   <= x
                 ==> n < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs B + &1 <= x * e` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`abs B + &1`; `x:real`; `e:real`] REAL_LE_LDIV_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x * n < x * e` MP_TAC THENL
   [MP_TAC(SPEC `B:real` (REAL_ARITH `!B:real. B <= abs B`)) THEN
    UNDISCH_TAC `x * n <= B` THEN UNDISCH_TAC `abs B + &1 <= x * e` THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]);;

(* A Schwartz function (and its reflection) vanish at +infinity: the k=1     *)
(* bound                                                                     *)
(* |x| |h(x)| <= B gives |h(x)| <= B/|x| --> 0. Feeds 283K's vanishing       *)
(* hypotheses.                                                               *)
let SCHWARTZ_TENDSTO_POS = prove
 (`!(h:real->complex). schwartz h ==> (h --> vec 0) at_posinfinity`,
  REWRITE_TAC[schwartz] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o SPECL [`SUC 0`; `0`]) THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; dist; real_ge] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(abs B + &1) / e` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC SCHWARTZ_TAIL_ARITH THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `B:real`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(abs B + &1) / e` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; REAL_POW_1] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`]);;

let SCHWARTZ_TENDSTO_NEG = prove
 (`!(h:real->complex). schwartz h ==> ((\a. h(--a)) --> vec 0) at_posinfinity`,
  REWRITE_TAC[schwartz] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o SPECL [`SUC 0`; `0`]) THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; dist; real_ge] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(abs B + &1) / e` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC SCHWARTZ_TAIL_ARITH THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `B:real`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(abs B + &1) / e` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--x:real`) THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; REAL_POW_1; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`]);;

(* Shifting a Schwartz witness: the derivative d 1 is itself Schwartz.       *)
let SCHWARTZ_SHIFT = prove
 (`!(d:num->real->complex).
     (!n x. ((\z. d n (drop z)) has_vector_derivative (d (SUC n) x)) (at(lift
       x))) /\
     (!k m. ?B. !x. abs(x) pow k * norm(d m x) <= B)
     ==> schwartz (d 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schwartz] THEN
  EXISTS_TAC `\n. (d:num->real->complex)(SUC n)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `SUC 0 = 1`];
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`k:num`; `SUC m`] th)) THEN
    REWRITE_TAC[]]);;

(* fhat of a Schwartz function is integrable (Fremlin 283K applied to        *)
(* h,h',h'').                                                                *)
let SCHWARTZ_FHAT_ABSINT = prove
 (`!(h:real->complex). schwartz h
     ==> (\z. fourier h (drop z)) absolutely_integrable_on (:real^1)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC o
              REWRITE_RULE[schwartz]) THEN
  FIRST_X_ASSUM(fun th -> SUBST_ALL_TAC(SYM th)) THEN
  MATCH_MP_TAC FOURIER_283K THEN
  MAP_EVERY EXISTS_TAC
   [`(d:num->real->complex)(SUC 0)`; `(d:num->real->complex)(SUC(SUC 0))`] THEN
  (* d(SUC 0) and d(SUC(SUC 0)) are Schwartz (shift twice); the derivative   *)
  (* goals then match the witness chain directly, and                        *)
  (* vanishing/integrability follow.                                         *)
  SUBGOAL_THEN `schwartz ((d:num->real->complex) (SUC 0))` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN
    MATCH_MP_TAC SCHWARTZ_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `schwartz ((d:num->real->complex) (SUC(SUC 0)))` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `SUC(SUC 0) = 2`] THEN
    SUBGOAL_THEN `(d:num->real->complex) 2 = (\n. d(SUC n)) 1` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `SUC 1 = 2`];
      MATCH_MP_TAC SCHWARTZ_SHIFT THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`SUC n`; `x:real`] th)) THEN
        REWRITE_TAC[];
        REPEAT GEN_TAC THEN
        FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`k:num`; `SUC m`] th)) THEN
        REWRITE_TAC[]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SCHWARTZ_TENDSTO_POS THEN ASM_REWRITE_TAC[] THEN
    NO_TAC) THEN
  TRY(MATCH_MP_TAC SCHWARTZ_TENDSTO_NEG THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SCHWARTZ_ABSINT THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* Fremlin 284C (inversion half): for a Schwartz function h, the inverse     *)
(* Fourier transform recovers h everywhere:                                  *)
(*   (1/sqrt(2 pi)) INT_R e^{ixy} hhat(y) dy = h x.                          *)
(* Direct from 283J: h is L^1 (SCHWARTZ_ABSINT), globally Lipschitz          *)
(* (SCHWARTZ_LIPSCHITZ, giving the Lipschitz-at-x bound with d = 1), and     *)
(* hhat                                                                      *)
(* is L^1 (SCHWARTZ_FHAT_ABSINT).                                            *)
(* ------------------------------------------------------------------------- *)
let FOURIER_284C_INVERSION = prove
 (`!(h:real->complex) x. schwartz h
     ==> Cx(inv(sqrt(&2 * pi))) *
         integral (:real^1) (\y. cexp(ii * Cx x * Cx(drop y)) * fourier h (drop
           y)) =
         h x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN
    `K:real` STRIP_ASSUME_TAC o MATCH_MP SCHWARTZ_LIPSCHITZ) THEN
  MATCH_MP_TAC FOURIER_283J THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `&1`] THEN
  ASM_SIMP_TAC[SCHWARTZ_ABSINT; SCHWARTZ_FHAT_ABSINT; REAL_LE_REFL;
    REAL_LT_01] THEN
  X_GEN_TAC `v:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x - v:real`; `x:real`]) THEN
  REWRITE_TAC[REAL_ARITH `abs((x - v) - x) = abs v`]);;

(* ------------------------------------------------------------------------- *)
(* Fremlin 283O prep: the 2D integrand f(x) e^{-ixy} g(y) is absolutely      *)
(* integrable on the plane (product of two L^1 functions times a             *)
(* unit-modulus                                                              *)
(* kernel).  This is the Fubini input for the multiplication formula         *)
(* INT f*ghat = INT fhat*g.                                                  *)
(* ------------------------------------------------------------------------- *)

(* In R^1, scalar*vector commutes as a % v = drop v % lift a (use ONCE only  *)
(* -- it re-matches its own RHS).                                            *)
let CMUL_LIFT_SWAP = prove
 (`!a:real. !v:real^1. a % v = drop v % lift a`,
  REWRITE_TAC[CART_EQ; VECTOR_MUL_COMPONENT; LIFT_COMPONENT; drop;
    DIMINDEX_1] THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `i = 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[LIFT_COMPONENT; drop] THEN
   REAL_ARITH_TAC);;

let FOURIER_283O_2D_ABSINT = prove
 (`!(f:real->complex) (g:real->complex).
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. g(drop z)) absolutely_integrable_on (:real^1)
     ==> (\z:real^(1,1)finite_sum.
            f(drop(fstcart z)) *
            cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
            g(drop(sndcart z))) absolutely_integrable_on
              (:real^(1,1)finite_sum)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\x:real^1. lift(norm((g:real->complex)(drop x))))
     integrable_on (:real^1)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    UNDISCH_TAC `(\z. (g:real->complex)(drop z)) absolutely_integrable_on
      (:real^1)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
      REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:real^1. lift(norm((f:real->complex)(drop x))))
     integrable_on (:real^1)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    UNDISCH_TAC `(\z. (f:real->complex)(drop z)) absolutely_integrable_on
      (:real^1)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
      REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `\z:real^(1,1)finite_sum. f(drop(fstcart z)) *
       cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
         g(drop(sndcart z))`
   (INST_TYPE [`:1`,`:M`; `:1`,`:N`] FUBINI_TONELLI)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [MP_TAC(INST_TYPE [`:1`,`:M`; `:1`,`:N`; `:2`,`:P`]
        (ISPEC `\w:real^1. (f:real->complex)(drop w)`
          MEASURABLE_ON_COMPOSE_FSTCART)) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
        INTEGRABLE_IMP_MEASURABLE];
      MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
        REWRITE_TAC[CEXP_FSTSND_CONTINUOUS];
        MP_TAC(INST_TYPE [`:1`,`:M`; `:1`,`:N`; `:2`,`:P`]
          (ISPEC `\w:real^1. (g:real->complex)(drop w)`
            MEASURABLE_ON_COMPOSE_SNDCART)) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
          INTEGRABLE_IMP_MEASURABLE]]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{x:real^1 | ~((\y. f(drop x) *
                     cexp(--(ii * Cx(drop x) * Cx(drop y))) * g(drop y))
                    absolutely_integrable_on (:real^1))} = {}`
     (fun th -> REWRITE_TAC[th; NEGLIGIBLE_EMPTY]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^1` THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL THEN
    ASM_SIMP_TAC[FOURIER_MODULATION_ABSINT];
    SUBGOAL_THEN
     `!x:real^1. integral (:real^1)
          (\y. lift(norm(f(drop x) *
                        cexp(--(ii * Cx(drop x) * Cx(drop y))) * g(drop y)))) =
          norm(f(drop x)) % integral (:real^1) (\y. lift(norm(g(drop y))))`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
       REWRITE_TAC[COMPLEX_NORM_MUL; FOURIER_KERNEL_NORM; REAL_MUL_LID] THEN
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
        ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[CMUL_LIFT_SWAP] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Fremlin 283O: the multiplication formula INT f*ghat = INT fhat*g, the     *)
(* Parseval-type identity leading into Plancherel (284O).  Both sides equal  *)
(* (1/sqrt(2pi)) of the plane integral of f(x) e^{-ixy} g(y), computed by    *)
(* Fubini in the two orders (FOURIER_283O_2D_ABSINT justifies the swap).     *)
(* ------------------------------------------------------------------------- *)

(* Inner integral: INT_y e^{-ixy} g(y) dy = sqrt(2pi) * ghat(x).             *)
let INNER_INT_FOURIER = prove
 (`!(g:real->complex) x.
     integral (:real^1) (\y. cexp(--(ii * Cx x * Cx(drop y))) * g(drop y)) =
     Cx(sqrt(&2 * pi)) * fourier g x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fourier] THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  SUBGOAL_THEN
    `Cx(sqrt(&2 * pi)) * Cx(&1) / Cx(sqrt(&2 * pi)) = Cx(&1)` SUBST1_TAC THENL
   [MP_TAC SQRT_2PI_POS THEN SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; COMPLEX_FIELD
      `~(s = Cx(&0)) ==> s * Cx(&1) / s = Cx(&1)`];
    REWRITE_TAC[COMPLEX_MUL_LID]]);;

let INNER_LMUL = prove
 (`!(g:real->complex) c x.
     (\z. g(drop z)) absolutely_integrable_on (:real^1)
     ==> integral (:real^1) (\y. c * cexp(--(ii * Cx x * Cx(drop y))) * g(drop
       y)) =
         c * Cx(sqrt(&2 * pi)) * fourier g x`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_COMPLEX_LMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
               FOURIER_MODULATION_ABSINT] THEN
  REWRITE_TAC[INNER_INT_FOURIER; COMPLEX_MUL_ASSOC]);;

(* f * ghat is L^1 (ghat continuous and bounded, f L^1).                     *)
let FHAT_TIMES_L1_ABSINT = prove
 (`!(f:real->complex) (g:real->complex).
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. g(drop z)) absolutely_integrable_on (:real^1)
     ==> (\z. f(drop z) * fourier g (drop z)) absolutely_integrable_on
       (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`( * ):complex->complex->complex`;
    `\z:real^1. fourier g (drop z)`;
    `\z:real^1. (f:real->complex)(drop z)`;
    `(:real^1)`] ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
       ASM_SIMP_TAC[FOURIER_CONTINUOUS_ON];
      REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
      FIRST_ASSUM(X_CHOOSE_TAC `K:real` o MATCH_MP FOURIER_BOUND_UNIFORM) THEN
      EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN ASM_REWRITE_TAC[]]);;

let FOURIER_283O_DIR1 = prove
 (`!(f:real->complex) (g:real->complex).
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. g(drop z)) absolutely_integrable_on (:real^1)
     ==> integral (:real^(1,1)finite_sum)
           (\z. f(drop(fstcart z)) *
                cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
                g(drop(sndcart z))) =
         Cx(sqrt(&2 * pi)) *
         integral (:real^1) (\z. f(drop z) * fourier g (drop z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `\z:real^(1,1)finite_sum. f(drop(fstcart z)) *
       cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
         g(drop(sndcart z))`
   (INST_TYPE [`:1`,`:M`; `:1`,`:N`] FUBINI_INTEGRAL)) THEN
  ASM_SIMP_TAC[FOURIER_283O_2D_ABSINT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_SIMP_TAC[INNER_LMUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `(f * s) * gh = s * (f * gh)`] THEN
  MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  ASM_SIMP_TAC[FHAT_TIMES_L1_ABSINT]);;

let FOURIER_283O_DIR2 = prove
 (`!(f:real->complex) (g:real->complex).
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. g(drop z)) absolutely_integrable_on (:real^1)
     ==> integral (:real^(1,1)finite_sum)
           (\z. f(drop(fstcart z)) *
                cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
                g(drop(sndcart z))) =
         Cx(sqrt(&2 * pi)) *
         integral (:real^1) (\z. g(drop z) * fourier f (drop z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `\z:real^(1,1)finite_sum. f(drop(fstcart z)) *
       cexp(--(ii * Cx(drop(fstcart z)) * Cx(drop(sndcart z)))) *
         g(drop(sndcart z))`
   (INST_TYPE [`:1`,`:M`; `:1`,`:N`] FUBINI_INTEGRAL_ALT)) THEN
  ASM_SIMP_TAC[FOURIER_283O_2D_ABSINT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SUBGOAL_THEN
   `!y:real^1. integral (:real^1)
        (\x. f(drop x) * cexp(--(ii * Cx(drop x) * Cx(drop y))) * g(drop y)) =
        integral (:real^1)
        (\x. g(drop y) * cexp(--(ii * Cx(drop y) * Cx(drop x))) * f(drop x))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    SUBGOAL_THEN `ii * Cx(drop x) * Cx(drop y) = ii * Cx(drop y) * Cx(drop x)`
     SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INNER_LMUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `(g * s) * fh = s * (g * fh)`] THEN
  MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  ASM_SIMP_TAC[FHAT_TIMES_L1_ABSINT]);;

let FOURIER_283O = prove
 (`!(f:real->complex) (g:real->complex).
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. g(drop z)) absolutely_integrable_on (:real^1)
     ==> integral (:real^1) (\z. f(drop z) * fourier g (drop z)) =
         integral (:real^1) (\z. fourier f (drop z) * g(drop z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->complex`; `g:real->complex`] FOURIER_283O_DIR1) THEN
  MP_TAC(ISPECL [`f:real->complex`; `g:real->complex`] FOURIER_283O_DIR2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN
  SUBGOAL_THEN `~(Cx(sqrt(&2 * pi)) = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN MP_TAC SQRT_2PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_EQ_MUL_LCANCEL] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Analytic core for 283Ch (differentiating fhat): the Fourier kernel is     *)
(* 1-Lipschitz in its frequency, |e^{ia} - e^{ib}| <= |a - b|.  With a = -xy *)
(* this bounds the difference quotient of e^{-ixy} by |x|, giving the |x     *)
(* f(x)|                                                                     *)
(* dominator for dominated convergence.                                      *)
(* ------------------------------------------------------------------------- *)
let CEXP_II_DIFF_BOUND = prove
 (`!a b:real. norm(cexp(ii * Cx a) - cexp(ii * Cx b)) <= abs(a - b)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `cexp(ii * Cx a) - cexp(ii * Cx b) =
    cexp(ii * Cx b) * (cexp(ii * Cx(a - b)) - Cx(&1))`
   SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_LDISTRIB; GSYM CEXP_ADD; COMPLEX_MUL_RID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_SUB] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_LID;
    DIST_CEXP_II_1] THEN
  MP_TAC(SPEC `(a - b) / &2` REAL_ABS_SIN_BOUND_LE) THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* SECTION 7. Smooth-bump infrastructure toward Fremlin 284N.                *)
(* Foundation layer: polynomial-times-decaying-exponential limits, which     *)
(* drive the C^inf smoothness of the standard bump phi(x) = exp(-1/x)        *)
(* (x > 0, else 0) -- its m-th derivative has the form poly(1/x) exp(-1/x),  *)
(* whose limit at 0+ is controlled by t^k exp(-t) -> 0 as t -> +inf.         *)
(*                                                                           *)
(* Uses only the HOL Light analysis library.                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The real exponential series, as a real_sums statement (bridged from the   *)
(* complex Taylor series CEXP_CONVERGES).                                    *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_SERIES = prove
 (`!x. ((\n. x pow n / &(FACT n)) real_sums exp x) (from 0)`,
  GEN_TAC THEN REWRITE_TAC[REAL_SUMS_COMPLEX; o_DEF] THEN
  MP_TAC(SPEC `Cx x` CEXP_CONVERGES) THEN
  REWRITE_TAC[GSYM CX_EXP] THEN REWRITE_TAC[CX_DIV; CX_POW; CX_EXP]);;

(* ------------------------------------------------------------------------- *)
(* Every single Taylor term is dominated by exp x for x >= 0 (a nonnegative  *)
(* term of a convergent nonnegative series is at most the sum).              *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_MONOMIAL_LE = prove
 (`!x k. &0 <= x ==> x pow k / &(FACT k) <= exp x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. x pow n / &(FACT n)`; `from 0`; `{k:num}`]
    REAL_PARTIAL_SUMS_LE_INFSUM_GEN) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SING_SUBSET; IN_FROM; SUM_SING] THEN
  REWRITE_TAC[LE_0] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
      REWRITE_TAC[real_summable] THEN EXISTS_TAC `exp x` THEN
      REWRITE_TAC[REAL_EXP_SERIES]];
    MATCH_MP_TAC(REAL_ARITH `s = e ==> t <= s ==> t <= e`) THEN
    MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN REWRITE_TAC[REAL_EXP_SERIES]]);;

(* ------------------------------------------------------------------------- *)
(* inv x -> 0 as x -> +inf (the elementary reciprocal decay).                *)
(* ------------------------------------------------------------------------- *)

let REALLIM_INV_AT_POSINFINITY = prove
 (`((\x. inv x) ---> &0) at_posinfinity`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_INV; LIM_INV_X]);;

(* ------------------------------------------------------------------------- *)
(* Abstract arithmetic reshaping used by the comparison bound:               *)
(*   p*x <= e*f, with x,e > 0  ==>  p*inv e <= f*inv x.                      *)
(* ------------------------------------------------------------------------- *)

let DECAY_ARITH = prove
 (`!p x e f. &0 < x /\ &0 < e /\ p * x <= e * f ==> p * inv e <= f * inv x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(e = &0) /\ ~(x = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `e * x:real` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(e = &0) /\ ~(x = &0) ==>
     (p * inv e) * (e * x) = p * x /\ (f * inv x) * (e * x) = e * f`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial-over-exponential decay: x^n / exp x -> 0 as x -> +inf.         *)
(* Comparison with (n+1)! * inv x, using x^(n+1)/(n+1)! <= exp x.            *)
(* ------------------------------------------------------------------------- *)

let POW_OVER_EXP_LIMIT = prove
 (`!n. ((\x. x pow n / exp x) ---> &0) at_posinfinity`,
  GEN_TAC THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\x. &(FACT(n+1)) * inv x` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN EXISTS_TAC `&1` THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < exp x` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; real_abs; REAL_LT_IMP_LE; REAL_EXP_POS_LE;
                 REAL_POW_LE] THEN
    MATCH_MP_TAC DECAY_ARITH THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`x:real`; `n+1`] REAL_EXP_MONOMIAL_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    SUBGOAL_THEN `&0 < &(FACT(n+1))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
    REWRITE_TAC[GSYM REAL_MUL_LZERO] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    MP_TAC REALLIM_INV_AT_POSINFINITY THEN REWRITE_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Composed form: t^n exp(--t) -> 0 as t -> +inf.  This is the exact input   *)
(* for the bump: with t = 1/x, the m-th derivative of exp(-1/x) is           *)
(* poly(1/x) exp(-1/x), and poly(t) exp(-t) -> 0 gives the C^inf gluing at 0.*)
(* ------------------------------------------------------------------------- *)

let POW_TIMES_EXP_NEG_LIMIT = prove
 (`!n. ((\t. t pow n * exp(--t)) ---> &0) at_posinfinity`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` POW_OVER_EXP_LIMIT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN REWRITE_TAC[REAL_EXP_NEG; real_div]);;

(* ------------------------------------------------------------------------- *)
(* MASTER BOUND for the bump: exp(-1/t) <= N! t^N for every N and t > 0.     *)
(* Directly from REAL_EXP_MONOMIAL_LE at x = 1/t: (1/t)^N/N! <= exp(1/t), so *)
(* exp(-1/t) = 1/exp(1/t) <= N! t^N.  This single family of inequalities     *)
(* squeezes ALL the junction limits at 0 (continuity of phi and every        *)
(* derivative phi^(m) = P_m(1/x) exp(-1/x), which -> 0 since bounded by a    *)
(* polynomial in 1/t times exp(-1/t) <= (that poly) * N! t^N -> 0).          *)
(* ------------------------------------------------------------------------- *)

let PHI_MASTER_BOUND = prove
 (`!N t. &0 < t ==> exp(--(inv t)) <= &(FACT N) * t pow N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inv t:real`; `N:num`] REAL_EXP_MONOMIAL_LE) THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_EXP_NEG; REAL_POW_INV; real_div] THEN
  SUBGOAL_THEN `&0 < exp(inv t)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t pow N /\ &0 < &(FACT N)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; FACT_LT]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv(exp(inv t)) <= &(FACT N) * t pow N` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(inv(t pow N) * inv(&(FACT N)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
    REWRITE_TAC[REAL_INV_MUL; REAL_INV_INV] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
    REWRITE_TAC[REAL_MUL_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial growth bound (t >= 1): for a real^1 polynomial p there are     *)
(* C >= 0 and N with |p(lift t)| <= C t^N.  Proved by induction on the       *)
(* polynomial structure (coordinate/constant/sum/product); the sum and       *)
(* product steps are factored out as separate lemmas.                        *)
(* ------------------------------------------------------------------------- *)

let POLY_GROWTH_SUMCASE = prove
 (`!(f:real^1->real) g C1 N1 C2 N2.
     &0 <= C1 /\ (!t. &1 <= t ==> abs(f(lift t)) <= C1 * t pow N1) /\
     &0 <= C2 /\ (!t. &1 <= t ==> abs(g(lift t)) <= C2 * t pow N2)
     ==> ?C N. &0 <= C /\
               !t. &1 <= t ==> abs(f(lift t) + g(lift t)) <= C * t pow N`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`C1 + C2:real`; `MAX N1 N2`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(f(lift t):real) <= C1 * t pow (MAX N1 N2) /\
                abs(g(lift t):real) <= C2 * t pow (MAX N1 N2)`
   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `(C1:real) * t pow N1`; EXISTS_TAC `(C2:real) * t pow N2`] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let POLY_GROWTH_MULCASE = prove
 (`!(f:real^1->real) g C1 N1 C2 N2.
     &0 <= C1 /\ (!t. &1 <= t ==> abs(f(lift t)) <= C1 * t pow N1) /\
     &0 <= C2 /\ (!t. &1 <= t ==> abs(g(lift t)) <= C2 * t pow N2)
     ==> ?C N. &0 <= C /\
               !t. &1 <= t ==> abs(f(lift t) * g(lift t)) <= C * t pow N`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`C1 * C2:real`; `N1 + N2:num`] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_POW_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C1 * t pow N1) * (C2 * t pow N2):real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS];
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN REAL_ARITH_TAC]);;

let POLY_GROWTH_BOUND = prove
 (`!p:real^1->real. real_polynomial_function p
     ==> ?C N. &0 <= C /\ !t. &1 <= t ==> abs(p(lift t)) <= C * t pow N`,
  MATCH_MP_TAC real_polynomial_function_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP] THEN
    MAP_EVERY EXISTS_TAC [`&1`; `1`] THEN
    REWRITE_TAC[REAL_POS; REAL_POW_1; REAL_MUL_LID] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:real` THEN MAP_EVERY EXISTS_TAC [`abs c`; `0`] THEN
    REWRITE_TAC[REAL_ABS_POS; real_pow; REAL_MUL_RID; REAL_LE_REFL];
    MAP_EVERY X_GEN_TAC [`f:real^1->real`; `g:real^1->real`] THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `C1:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `C2:real` (X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC POLY_GROWTH_SUMCASE THEN
    MAP_EVERY EXISTS_TAC [`C1:real`; `N1:num`; `C2:real`; `N2:num`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`f:real^1->real`; `g:real^1->real`] THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `C1:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `C2:real` (X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC POLY_GROWTH_MULCASE THEN
    MAP_EVERY EXISTS_TAC [`C1:real`; `N1:num`; `C2:real`; `N2:num`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* THE bump payoff at the level of decay: any polynomial times exp(--t)      *)
(* tends to 0 at +inf.  This controls poly(1/x) exp(-1/x) -> 0 as x -> 0+.   *)
(* ------------------------------------------------------------------------- *)

let POLY_TIMES_EXP_NEG_DECAY = prove
 (`!p:real^1->real. real_polynomial_function p
     ==> ((\t. p(lift t) * exp(--t)) ---> &0) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP POLY_GROWTH_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN
    `N:num` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\t. C * (t pow N * exp(--t))` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN EXISTS_TAC `&1` THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(exp(--t)) = exp(--t)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL; REAL_EXP_POS_LE]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[]; REWRITE_TAC[REAL_EXP_POS_LE]];
    REWRITE_TAC[GSYM REAL_MUL_LZERO] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    REWRITE_TAC[POW_TIMES_EXP_NEG_LIMIT]]);;

(* ------------------------------------------------------------------------- *)
(* Decoupling "smooth compactly-supported ==> Schwartz".  This is the clean  *)
(* reusable lemma that reduces 284N to merely BUILDING a smooth bump: once   *)
(* we                                                                        *)
(* have a derivative chain all supported in a compact interval [-R,R], the   *)
(* Schwartz decay bounds |x|^k |d m x| <= B are automatic.                   *)
(* ------------------------------------------------------------------------- *)

(* A nonnegative continuous function that vanishes off [-R,R] is bounded.    *)
let BOUNDED_SUPPORT_CONT = prove
 (`!g:real->real R.
     &0 <= R /\ g real_continuous_on real_interval[--R,R] /\
     (!x. abs(x) > R ==> g x = &0) /\ (!x. &0 <= g x)
     ==> ?B. !x. g x <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `real_interval[--R,R]`]
    REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max (g(x0:real)) (&0)` THEN X_GEN_TAC `x:real` THEN
  ASM_CASES_TAC `abs(x) > R` THENL
   [ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* The norm of a term in a has_vector_derivative chain is real-continuous.   *)
let NORM_CONT_BRIDGE = prove
 (`!(dm:real->complex) dm1 s.
     (!x. ((\z. dm(drop z)) has_vector_derivative (dm1 x)) (at(lift x)))
     ==> (\x. norm(dm x)) real_continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`at(lift x)`; `\z. (dm:real->complex)(drop z)`]
    CONTINUOUS_LIFT_NORM_COMPOSE) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE];
    REWRITE_TAC[LIFT_DROP]]);;

(* MAIN: a derivative chain (d n) with d n differentiable-via-drop and every *)
(* d m supported in [-R,R] gives schwartz(d 0).                              *)
let COMPACT_SUPPORT_SMOOTH_IMP_SCHWARTZ = prove
 (`!d:num->real->complex. !R.
     &0 <= R /\
     (!n x. ((\z. d n(drop z)) has_vector_derivative (d(SUC n) x))(at(lift x)))
       /\
     (!m x. abs(x) > R ==> d m x = Cx(&0))
     ==> schwartz (d 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schwartz] THEN
  EXISTS_TAC `d:num->real->complex` THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN
  MATCH_MP_TAC BOUNDED_SUPPORT_CONT THEN EXISTS_TAC `R:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real. abs x`; `k:num`; `real_interval[--R,R]`]
        REAL_CONTINUOUS_ON_POW) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`\x:real. x`; `real_interval[--R,R]`]
        REAL_CONTINUOUS_ON_ABS) THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC NORM_CONT_BRIDGE THEN
      EXISTS_TAC `(d:num->real->complex)(SUC m)` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(d:num->real->complex) m x = Cx(&0)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; REWRITE_TAC[COMPLEX_NORM_0; REAL_MUL_RZERO]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_POW_LE; REAL_ABS_POS; NORM_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Differential calculus of the bump phi(x) = exp(-1/x) on x > 0.            *)
(* Its m-th derivative is P_m(1/x) exp(-1/x) with P_m a real polynomial,     *)
(* obeying the recurrence P_{m+1}(u) = u^2 (P_m(u) - P_m'(u)).               *)
(* ------------------------------------------------------------------------- *)


(* d/dx P(1/x) = -inv(x^2) P'(1/x)  (chain rule through inv).                *)
let BUMP_FACTOR1 = prove
 (`!(P:real->real) P1 x.
     &0 < x /\ (!y. (P has_real_derivative P1 y) (atreal y))
     ==> ((\x. P(inv x)) has_real_derivative (--(inv(x pow 2)) * P1(inv x)))
         (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `((P:real->real) o inv has_real_derivative (P1(inv x) * (--(inv(x pow 2)))))
    (atreal x)`
   MP_TAC THENL
   [MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real. x`; `&1`;
       `x:real`] HAS_REAL_DERIVATIVE_INV_ATREAL) THEN
      ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; ETA_AX] THEN
      MATCH_MP_TAC RDERIV_EQ THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_LNEG] THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_INV_POW];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC RDERIV_EQ THEN
    REWRITE_TAC[REAL_MUL_SYM]]);;

(* d/dx exp(-1/x) = exp(-1/x) inv(x^2).                                      *)
let BUMP_FACTOR2 = prove
 (`!x. &0 < x
     ==> ((\x. exp(--(inv x))) has_real_derivative (exp(--(inv x)) * inv(x pow
       2)))
         (atreal x)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

(* The derivative recurrence: d/dx [P(1/x) exp(-1/x)]                        *)
(*   = inv(x^2) (P(1/x) - P'(1/x)) exp(-1/x)  on x > 0.                      *)
let BUMP_DERIV_STEP = prove
 (`!(P:real->real) P1 x.
     &0 < x /\ (!y. (P has_real_derivative P1 y) (atreal y))
     ==> ((\x. P(inv x) * exp(--(inv x))) has_real_derivative
          (inv(x pow 2) * (P(inv x) - P1(inv x)) * exp(--(inv x))))
         (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. (P:real->real)(inv x) * exp(--(inv x))) has_real_derivative
     ((P(inv x)) * (exp(--(inv x)) * inv(x pow 2)) +
      (--(inv(x pow 2)) * P1(inv x)) * exp(--(inv x)))) (atreal x)`
   MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`P:real->real`; `P1:real->real`;
       `x:real`] BUMP_FACTOR1) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `x:real` BUMP_FACTOR2) THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC RDERIV_EQ THEN
    POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD]);;

(* Bridge from a real derivative to the Cx-valued vector derivative in the   *)
(* exact shape the schwartz / COMPACT_SUPPORT_SMOOTH_IMP_SCHWARTZ chain      *)
(* wants: (g has_real_derivative g')(atreal x) lifts to (\z. Cx(g(drop z)))  *)
(* has_vector_derivative (Cx g') (at(lift x)).                               *)
let CX_VECTOR_DERIV_BRIDGE = prove
 (`!g:real->real. !g' x.
     (g has_real_derivative g') (atreal x)
     ==> ((\z. Cx(g(drop z))) has_vector_derivative (Cx g')) (at(lift x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[HAS_REAL_VECTOR_DERIVATIVE_AT]) THEN
  REWRITE_TAC[has_vector_derivative] THEN
  DISCH_THEN(MP_TAC o ISPEC `Cx(&1)` o MATCH_MP HAS_DERIVATIVE_VMUL_DROP) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; DROP_CMUL; COMPLEX_CMUL; COMPLEX_MUL_RID] THEN
  REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
  MATCH_MP_TAC(MESON[] `f = g /\ a = b
     ==> (f has_derivative a) net ==> (g has_derivative b) net`) THEN
  CONJ_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID; GSYM CX_MUL] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The junction limit: for any polynomial Q, Q(1/x) exp(-1/x) -> 0 as x->0+. *)
(* This is the analytic heart of gluing phi at 0 (continuity and every       *)
(* derivative limit reduce to this via the recurrence).                      *)
(* ------------------------------------------------------------------------- *)

(* Regroup helper (abstract, so REAL_RING applies to plain vars).            *)
let REGROUP = prove
 (`!c a ff b x:real. a * b = x ==> (c * a) * (ff * b) = (c * ff) * x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(REAL_RING `!c a ff b:real. (c * a) * (ff * b) = (c * ff) * (a * b)`)
    THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* The pointwise squeeze bound on 0 < x < 1: |Q(1/x) exp(-1/x)| <= C(K+1)!   *)
(* x.                                                                        *)
let JUNCTION_ARITH = prove
 (`!(Q:real->real) C K x.
     &0 <= C /\ (!t. &1 <= t ==> abs((\z:real^1. Q(drop z))(lift t)) <= C * t
       pow K) /\
     &0 < x /\ x < &1 /\ &1 <= inv x
     ==> abs(Q(inv x) * exp(--(inv x))) <= (C * &(FACT(K+1))) * x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(x:real)` o check(fun th -> is_forall(concl
    th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(exp(--(inv x))) = exp(--(inv x))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL; REAL_EXP_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C * inv x pow K) * exp(--(inv x))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
     ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K+1`; `x:real`] PHI_MASTER_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS `(C * inv x pow K) * (&(FACT(K+1)) * x pow (K+1))`
    THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
    MATCH_MP_TAC REGROUP THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_INV] THEN
    MATCH_MP_TAC(REAL_FIELD `~(x = &0) ==> inv(x pow K) * (x pow K * x) = x`)
      THEN
    ASM_REAL_ARITH_TAC]);;

(* Linear limit helper: (\x. c x) -> 0 as x -> 0 within any set.             *)
let LIN_LIMIT_0 = prove
 (`!c s. ((\x:real. c * x) ---> &0) (atreal(&0) within s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(REWRITE_RULE[]
    (ISPECL [`atreal(&0) within s`; `\x:real. x`;
      `c:real`] REALLIM_NULL_LMUL)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
  REWRITE_TAC[REALLIM_ATREAL_ID]);;

let JUNCTION_LIMIT = prove
 (`!Q:real->real. real_polynomial_function (\z:real^1. Q(drop z))
     ==> ((\x. Q(inv x) * exp(--(inv x))) ---> &0)
         (atreal(&0) within {x | &0 < x})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP POLY_GROWTH_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN
    `K:num` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\x:real. (C * &(FACT(K+1))) * x` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`Q:real->real`; `C:real`; `K:num`;
      `x:real`] JUNCTION_ARITH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN ACCEPT_TAC];
    REWRITE_TAC[LIN_LIMIT_0]]);;

(* ------------------------------------------------------------------------- *)
(* The bump-generating function phi(x) = exp(-1/x) for x > 0, else 0, and    *)
(* the                                                                       *)
(* predicate bumpP characterising the members of its derivative chain: each  *)
(* is Cx(Q(1/x) exp(-1/x)) on x>0 and Cx 0 on x<=0 for some real polynomial  *)
(* Q.                                                                        *)
(* ------------------------------------------------------------------------- *)

let cphi = new_definition
 `cphi (x:real) = if &0 < x then Cx(exp(--(inv x))) else Cx(&0)`;;

let bumpP = new_definition
 `bumpP (f:real->complex) <=>
    ?Q:real->real. real_polynomial_function (\z:real^1. Q(drop z)) /\
                   (!x. &0 < x ==> f x = Cx(Q(inv x) * exp(--(inv x)))) /\
                   (!x. x <= &0 ==> f x = Cx(&0))`;;

(* Derivative-chain glue at a point: vector-derivative on two sets covering  *)
(* the line gives the derivative at the point.                               *)
let HAS_VDERIV_GLUE = prove
 (`!f:real^1->real^N f' a s t.
     (f has_vector_derivative f') (at a within s) /\
     (f has_vector_derivative f') (at a within t) /\
     s UNION t = (:real^1)
     ==> (f has_vector_derivative f') (at a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  REWRITE_TAC[has_derivative_within; has_derivative_at] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIM_UNION_UNIV THEN
  MAP_EVERY EXISTS_TAC [`s:real^1->bool`; `t:real^1->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* Left half-line: on {drop z <= 0}, a bumpP function is identically 0, so   *)
(* its derivative there is 0.                                                *)
let JUNCTION_LEFT = prove
 (`!f:real->complex. bumpP f
     ==> ((\z. f(drop z)) has_vector_derivative (Cx(&0)))
         (at(lift(&0)) within {z | drop z <= &0})`,
  REWRITE_TAC[bumpP] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`\z:real^1. vec 0:complex`; `&1`] THEN
  REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; LIFT_DROP; DROP_VEC] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    X_GEN_TAC `z:real^1` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN ASM_MESON_TAC[];
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]]);;

(* Right half-line derivative at 0.  The difference quotient inv(drop y) %   *)
(* f(drop y) equals Cx((1/x) Q(1/x) exp(-1/x)) = Cx(R(1/x) exp(-1/x)) with   *)
(* R(u)=u Q(u), which -> 0 by JUNCTION_LIMIT.                                *)

(* drop is a real polynomial function (as a real^1->real map).               *)
let RPF_DROP = prove
 (`real_polynomial_function (drop:real^1->real)`,
  SUBGOAL_THEN `drop = \z:real^1. z$1` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; drop]; ALL_TAC] THEN
  SIMP_TAC[real_polynomial_function_RULES; DIMINDEX_1; LE_REFL]);;

(* {drop z >= 0} minus the origin is exactly the (lifted) open right         *)
(* half-line.                                                                *)
let HALFLINE_DELETE = prove
 (`{z:real^1 | &0 <= drop z} DELETE lift(&0) = IMAGE lift {x | &0 < x}`,
  REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `z:real^1` THEN
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `drop z` THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC]);;

(* On the right half-line the transformed quotient agrees with               *)
(* Cx(R(1/x)e^..).                                                           *)
let JUNCTION_RIGHT_AGREE = prove
 (`!(f:real->complex) Q x'.
     (!x. &0 < x ==> f x = Cx(Q(inv x) * exp(--(inv x)))) /\
     x' IN {z | &0 <= drop z} /\ &0 < dist(x',lift(&0)) /\ dist(x',lift(&0)) <
       &1
     ==> Cx (inv (drop x') * Q (inv (drop x')) * exp (--inv (drop x'))) =
         inv (drop (x' - lift (&0))) % f (drop x')`,
  REWRITE_TAC[IN_ELIM_THM; DIST_REAL; GSYM drop; LIFT_DROP; DROP_VEC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < drop x'` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[DROP_SUB; LIFT_DROP; DROP_VEC; REAL_SUB_RZERO] THEN
  REWRITE_TAC[COMPLEX_CMUL; GSYM CX_MUL; REAL_MUL_ASSOC]);;

(* The transformed quotient -> Cx 0 (JUNCTION_LIMIT on R(u)=u Q(u), bridged  *)
(* complex<->real via REALLIM_COMPLEX and net-lifted via                     *)
(* LIM_WITHINREAL_WITHIN; the closed half-line reduces to the open one by    *)
(* LIM_WITHIN_DELETE).                                                       *)
let JUNCTION_RIGHT_LIMIT = prove
 (`!Q:real->real. real_polynomial_function (\z:real^1. Q(drop z))
     ==> ((\y. Cx(inv(drop y) * Q(inv(drop y)) * exp(--(inv(drop y))))) -->
       Cx(&0))
         (at(lift(&0)) within {z | &0 <= drop z})`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM LIM_WITHIN_DELETE] THEN
  REWRITE_TAC[HALFLINE_DELETE] THEN
  MP_TAC(ISPEC `\u:real. u * Q u` JUNCTION_LIMIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_MUL THEN
    ASM_REWRITE_TAC[RPF_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; REALLIM_WITHINREAL_WITHIN;
              LIM_WITHINREAL_WITHIN] THEN
  REWRITE_TAC[o_DEF; REAL_MUL_ASSOC]);;

let JUNCTION_RIGHT = prove
 (`!f:real->complex. bumpP f
     ==> ((\z. f(drop z)) has_vector_derivative (Cx(&0)))
         (at(lift(&0)) within {z | &0 <= drop z})`,
  REWRITE_TAC[bumpP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_WITHIN_1D] THEN
  REWRITE_TAC[LIFT_DROP; DROP_VEC; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `(f:real->complex)(&0) = Cx(&0)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_SUB_RZERO] THEN
  MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
  EXISTS_TAC `\y:real^1. Cx(inv(drop y) * (Q(inv(drop y)) * exp(--(inv(drop
    y)))))` THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC JUNCTION_RIGHT_AGREE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC JUNCTION_RIGHT_LIMIT THEN ASM_REWRITE_TAC[]]);;

(* phi and every derivative-chain member is differentiable at 0 with deriv   *)
(* 0.                                                                        *)
let JUNCTION_DIFF = prove
 (`!f:real->complex. bumpP f
     ==> ((\z. f(drop z)) has_vector_derivative (Cx(&0))) (at(lift(&0)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_VDERIV_GLUE THEN
  MAP_EVERY EXISTS_TAC [`{z:real^1 | drop z <= &0}`;
    `{z:real^1 | &0 <= drop z}`] THEN
  ASM_SIMP_TAC[JUNCTION_LEFT; JUNCTION_RIGHT] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The derivative chain: assembling the pieces.  On x>0 the derivative is    *)
(* the next bump-polynomial form; on x<0 it is 0; at x=0 it is 0 (JUNCTION_  *)
(* DIFF).  This gives the inductive step BUMP_STEP for building the whole    *)
(* chain of derivatives.                                                     *)
(* ------------------------------------------------------------------------- *)

(* x>0 derivative of the raw form Cx(Q(1/.)e^{-1/.}).                        *)
let BUMP_DERIV_POS_CORE = prove
 (`!(Q:real->real) Q1 x.
     (!y. (Q has_real_derivative Q1 y) (atreal y)) /\ &0 < x
     ==> ((\z. Cx(Q(inv(drop z)) * exp(--(inv(drop z))))) has_vector_derivative
          (Cx(inv(x pow 2) * (Q(inv x) - Q1(inv x)) * exp(--(inv x)))))
         (at(lift x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w. Q(inv w) * exp(--(inv w))`;
                 `inv(x pow 2) * (Q(inv x) - Q1(inv x)) * exp(--(inv x))`;
                   `x:real`]
    CX_VECTOR_DERIV_BRIDGE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`Q:real->real`; `Q1:real->real`;
    `x:real`] BUMP_DERIV_STEP) THEN
  ASM_REWRITE_TAC[]);;

(* x>0 derivative of f (transformed to the raw form near x).                 *)
let BUMP_DERIV_POS = prove
 (`!(f:real->complex) Q Q1 x.
     (!x. &0 < x ==> f x = Cx(Q(inv x) * exp(--(inv x)))) /\
     (!y. (Q has_real_derivative Q1 y) (atreal y)) /\ &0 < x
     ==> ((\z. f(drop z)) has_vector_derivative
          (Cx(inv(x pow 2) * (Q(inv x) - Q1(inv x)) * exp(--(inv x)))))
         (at(lift x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\z. Cx(Q(inv(drop z)) * exp(--(inv(drop z))))` THEN
  EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC BUMP_DERIV_POS_CORE THEN ASM_REWRITE_TAC[]]);;

(* x<0 derivative of f (identically 0 near x).                               *)
let BUMP_DERIV_NEG = prove
 (`!(f:real->complex) x.
     (!y. y <= &0 ==> f y = Cx(&0)) /\ x < &0
     ==> ((\z. f(drop z)) has_vector_derivative (Cx(&0))) (at(lift x))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\z:real^1. vec 0:complex` THEN
  EXISTS_TAC `--x:real` THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Full-line derivative into the next bump member (the if-form).             *)
let BUMP_DERIV_ALL = prove
 (`!(f:real->complex) Q Q1 x.
     (!x. &0 < x ==> f x = Cx(Q(inv x) * exp(--(inv x)))) /\
     (!x. x <= &0 ==> f x = Cx(&0)) /\
     (!y. (Q has_real_derivative Q1 y) (atreal y)) /\
     real_polynomial_function (\z:real^1. Q(drop z))
     ==> ((\z. f(drop z)) has_vector_derivative
          (if &0 < x
           then Cx((inv x pow 2 * (Q(inv x) - Q1(inv x))) * exp(--(inv x)))
           else Cx(&0)))
         (at(lift x))`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `x < &0 \/ x = &0 \/ &0 < x`) THENL
   [SUBGOAL_THEN `~(&0 < x)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC BUMP_DERIV_NEG THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_REFL] THEN
      MATCH_MP_TAC JUNCTION_DIFF THEN REWRITE_TAC[bumpP] THEN
      EXISTS_TAC `Q:real->real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(Cx((inv x pow 2 * (Q(inv x) - Q1(inv x))) * exp(--(inv x)))):complex =
        Cx(inv(x pow 2) * (Q(inv x) - Q1(inv x)) * exp(--(inv x)))`
      SUBST1_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[REAL_INV_POW] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC BUMP_DERIV_POS THEN ASM_REWRITE_TAC[]]]]);;

(* THE inductive step: a bumpP function has a bumpP derivative-successor.    *)
let BUMP_STEP = prove
 (`!f:real->complex. bumpP f
     ==> ?g. bumpP g /\
             (!x. ((\z. f(drop z)) has_vector_derivative (g x)) (at(lift x)))`,
  REWRITE_TAC[bumpP] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_POLY_DERIVATIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q1c:real^1->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Q1 = \u:real. (Q1c:real^1->real)(lift u)` THEN
  SUBGOAL_THEN `!y. ((Q:real->real) has_real_derivative (Q1 y)) (atreal y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real` THEN EXPAND_TAC "Q1" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check(fun th -> is_forall(concl
      th))) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `real_polynomial_function (\z:real^1. Q1 (drop z))` ASSUME_TAC THENL
   [EXPAND_TAC "Q1" THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `\x. if &0 < x
        then Cx((inv x pow 2 * (Q(inv x) - Q1(inv x))) * exp(--(inv x)))
        else Cx(&0)` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `\u:real. u pow 2 * (Q u - Q1 u)` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_POW THEN REWRITE_TAC[RPF_DROP];
        MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_SUB THEN ASM_REWRITE_TAC[]];
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    GEN_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BUMP_DERIV_ALL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The full C^inf-ness of phi: cphi is a bumpP function (base case), and a   *)
(* whole derivative chain d exists with d 0 = cphi and (d n)' = d(SUC n).    *)
(* ------------------------------------------------------------------------- *)

let BUMPP_CPHI = prove
 (`bumpP cphi`,
  REWRITE_TAC[bumpP; cphi] THEN EXISTS_TAC `\u:real. &1` THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[real_polynomial_function_RULES];
    GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let BUMP_CHAIN = prove
 (`?d:num->real->complex.
     d 0 = cphi /\
     (!n. bumpP (d n)) /\
     (!n x. ((\z. d n (drop z)) has_vector_derivative (d(SUC n) x)) (at(lift
       x)))`,
  MP_TAC(ISPECL
   [`\(n:num) (f:real->complex). bumpP f`;
    `\(n:num) (f:real->complex) (g:real->complex).
        !x. ((\z. f(drop z)) has_vector_derivative (g x)) (at(lift x))`;
    `cphi`] DEPENDENT_CHOICE_FIXED) THEN
  REWRITE_TAC[BUMPP_CPHI] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC BUMP_STEP THEN ACCEPT_TAC th);
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Toward a compactly-supported bump psi = phi(1+.) phi(1-.): the product    *)
(* derivative infrastructure (single product rule + VSUM derivative), for    *)
(* the                                                                       *)
(* Leibniz chain of the product of two smooth (chained) functions.           *)
(* ------------------------------------------------------------------------- *)

(* Product rule for two complex chains at a point.                           *)
let CMUL_DERIV = prove
 (`!(a:real->complex) b a' b' x.
     ((\z. a(drop z)) has_vector_derivative a') (at(lift x)) /\
     ((\z. b(drop z)) has_vector_derivative b') (at(lift x))
     ==> ((\z. a(drop z) * b(drop z)) has_vector_derivative
          (a(x) * b' + a' * b(x))) (at(lift x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`( * ):complex->complex->complex`; `\z. (a:real->complex)(drop z)`;
    `\z. (b:real->complex)(drop z)`; `a':complex`; `b':complex`; `lift x`]
   HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL; LIFT_DROP] THEN ASM_REWRITE_TAC[]);;

(* Vector derivative of a finite sum of complex chains.                      *)
let HAS_VDERIV_VSUM = prove
 (`!s. FINITE s ==> !(f:num->real^1->complex) f' x.
     (!i. i IN s ==> ((f i) has_vector_derivative (f' i)) (at x))
     ==> ((\z. vsum s (\i. f i z)) has_vector_derivative (vsum s f')) (at x)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_VECTOR_DERIVATIVE_CONST];
    MAP_EVERY X_GEN_TAC [`a:num`; `t:num->bool`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`f:num->real^1->complex`; `f':num->complex`;
      `x:real^1`] THEN
    DISCH_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INSERT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]]]);;

(* ------------------------------------------------------------------------- *)
(* Binomial / vsum algebra for the Leibniz rule: shift, Pascal peel, and the *)
(* key Pascal-combination identity                                           *)
(*   sum_{0..n} binom(n,k) B k + sum_{0..n} binom(n,k) B(SUC k)              *)
(*     = sum_{0..SUC n} binom(SUC n,k) B k.                                  *)
(* ------------------------------------------------------------------------- *)

let VSUM_SHIFT_SUC = prove
 (`!(g:num->complex) n. vsum(0..n)(\k. g(SUC k)) = vsum(1..SUC n) g`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[VSUM_CLAUSES_NUMSEG; LE_0;
    ARITH_RULE `1 <= SUC n`; ARITH_RULE `1 <= SUC(SUC n)`] THEN
  REWRITE_TAC[ARITH] THEN VECTOR_ARITH_TAC);;

let PEEL_PASCAL = prove
 (`!(C:num->complex) n.
     vsum(0..SUC n)(\k. Cx(&(binom(SUC n,k))) * C k) =
     C 0 + vsum(0..n)(\k. Cx(&(binom(n,SUC k)) + &(binom(n,k))) * C(SUC k))`,
  REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[VSUM_CLAUSES_LEFT; ARITH_RULE `0 <= SUC n`] THEN
  REWRITE_TAC[ADD_CLAUSES; binom; COMPLEX_MUL_LID] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\k. Cx(&(binom(SUC n,k))) * (C:num->complex) k`; `n:num`]
    VSUM_SHIFT_SUC) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[binom; GSYM CX_ADD; GSYM REAL_OF_NUM_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC);;

let PEEL_N = prove
 (`!(B:num->complex) n.
     vsum(0..n)(\k. Cx(&(binom(n,k))) * B k) =
     B 0 + vsum(0..n)(\k. Cx(&(binom(n,SUC k))) * B(SUC k))`,
  REPEAT GEN_TAC THEN
  MP_TAC(REWRITE_RULE[](ISPECL [`\k. Cx(&(binom(n,k))) * (B:num->complex) k`;
    `n:num`]
    VSUM_SHIFT_SUC)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
  GEN_REWRITE_TAC (LAND_CONV)
   [MATCH_MP VSUM_CLAUSES_LEFT (ARITH_RULE `0 <= n:num`)] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; ADD_CLAUSES] THEN
  SUBGOAL_THEN `binom(n,SUC n) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC BINOM_LT THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[binom; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; COMPLEX_ADD_RID] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC n`]);;

let PASCAL_VSUM = prove
 (`!(B:num->complex) n.
     vsum(0..n)(\k. Cx(&(binom(n,k))) * B k) +
     vsum(0..n)(\k. Cx(&(binom(n,k))) * B (SUC k)) =
     vsum(0..SUC n)(\k. Cx(&(binom(SUC n,k))) * B k)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [PEEL_PASCAL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [PEEL_N] THEN
  SUBGOAL_THEN
   `vsum(0..n)(\k. Cx(&(binom(n,SUC k)) + &(binom(n,k))) * (B:num->complex)(SUC
     k)) =
    vsum(0..n)(\k. Cx(&(binom(n,SUC k))) * B(SUC k)) +
    vsum(0..n)(\k. Cx(&(binom(n,k))) * B(SUC k))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VSUM_ADD_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD; COMPLEX_ADD_RDISTRIB];
    REWRITE_TAC[COMPLEX_ADD_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Leibniz rule: the product of two functions each carrying a full           *)
(* derivative                                                                *)
(* chain again carries one, with n-th derivative the binomial sum.  This is  *)
(* Fremlin 284Bb (Schwartz closed under product), used to build the          *)
(* compactly-supported bump psi = phi(1+.) phi(1-.).                         *)
(* ------------------------------------------------------------------------- *)

(* A constant times a chain scales the derivative.                           *)
let CONST_CHAIN_DERIV = prove
 (`!c (a:real->complex) a' x.
     ((\z. a(drop z)) has_vector_derivative a') (at(lift x))
     ==> ((\z. c * a(drop z)) has_vector_derivative (c * a')) (at(lift x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\u:real. c:complex`; `a:real->complex`; `Cx(&0)`;
    `a':complex`;
    `x:real`] CMUL_DERIV) THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID]);;

(* SUC(n-k) = SUC n - k inside the sum (valid for k <= n).                   *)
let SUM1EQ = prove
 (`!(A:num->num->complex) n.
     vsum(0..n)(\k. Cx(&(binom(n,k))) * A k (SUC(n-k))) =
     vsum(0..n)(\k. Cx(&(binom(n,k))) * A k (SUC n - k))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `i <= n ==> SUC(n - i) = SUC n - i`]);;

(* Derivative of a single Leibniz term.                                      *)
let LEIB_TERM = prove
 (`!(d:num->real->complex) e n k x.
     (!m y. ((\z. d m(drop z)) has_vector_derivative (d(SUC m) y))(at(lift y)))
       /\
     (!m y. ((\z. e m(drop z)) has_vector_derivative (e(SUC m) y))(at(lift y)))
     ==> ((\z. Cx(&(binom(n,k))) * d k (drop z) * e (n-k)(drop z))
          has_vector_derivative
          (Cx(&(binom(n,k))) * (d k x * e(SUC(n-k)) x + d(SUC k) x * e(n-k)
            x)))
         (at(lift x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONST_CHAIN_DERIV THEN
  MP_TAC(ISPECL [`(d:num->real->complex) k`; `(e:num->real->complex)(n-k)`;
    `(d:num->real->complex)(SUC k) x`; `(e:num->real->complex)(SUC(n-k)) x`;
      `x:real`]
    CMUL_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VDERIV_EQ THEN
  CONV_TAC COMPLEX_RING);;

(* The derivative-sum equals the SUC n Leibniz sum (SUM1EQ + PASCAL_VSUM).   *)
let LEIB_VALEQ = prove
 (`!(d:num->real->complex) e n x.
     vsum(0..n)(\k. Cx(&(binom(n,k))) *
                    (d k x * e(SUC(n-k)) x + d(SUC k) x * e(n-k) x)) =
     vsum(0..SUC n)(\k. Cx(&(binom(SUC n,k))) * d k x * e (SUC n-k) x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_ADD_LDISTRIB; VSUM_ADD_NUMSEG] THEN
  MP_TAC(REWRITE_RULE[](ISPEC `\k j. (d:num->real->complex) k x *
    (e:num->real->complex) j x` SUM1EQ)) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SPEC `n:num` th]) THEN
  MP_TAC(ISPEC `\k. (d:num->real->complex) k x * (e:num->real->complex) (SUC n
    - k) x`
    PASCAL_VSUM) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `a = a' /\ b = b' /\ c = c'
     ==> (a' + b' = c') ==> (a + b = c)`) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  REPEAT AP_TERM_TAC THEN TRY AP_THM_TAC THEN TRY AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* The Leibniz derivative step: (n-sum)' = (SUC n)-sum.                      *)
let LEIBNIZ_DERIV = prove
 (`!(d:num->real->complex) e n x.
     (!m y. ((\z. d m(drop z)) has_vector_derivative (d(SUC m) y))(at(lift y)))
       /\
     (!m y. ((\z. e m(drop z)) has_vector_derivative (e(SUC m) y))(at(lift y)))
     ==> ((\z. vsum(0..n)(\k. Cx(&(binom(n,k))) * d k (drop z) * e (n-k)(drop
       z)))
          has_vector_derivative
          (vsum(0..SUC n)(\k. Cx(&(binom(SUC n,k))) * d k x * e (SUC n-k) x)))
         (at(lift x))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM LEIB_VALEQ] THEN
  MP_TAC(ISPEC `0..n` HAS_VDERIV_VSUM) THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  DISCH_THEN(MP_TAC o ISPECL
   [`\k z. Cx(&(binom(n,k))) * (d:num->real->complex) k (drop z) * e (n-k)(drop
     z)`;
    `\k. Cx(&(binom(n,k))) * ((d:num->real->complex) k x * e(SUC(n-k)) x +
                              d(SUC k) x * e(n-k) x)`;
    `lift x`]) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LEIB_TERM THEN ASM_REWRITE_TAC[]);;

(* Product of two chains carries a chain.                                    *)
let LEIBNIZ_CHAIN = prove
 (`!(d:num->real->complex) e.
     (!m y. ((\z. d m(drop z)) has_vector_derivative (d(SUC m) y))(at(lift y)))
       /\
     (!m y. ((\z. e m(drop z)) has_vector_derivative (e(SUC m) y))(at(lift y)))
     ==> ?p:num->real->complex.
           (!x. p 0 x = d 0 x * e 0 x) /\
           (!n y. ((\z. p n(drop z)) has_vector_derivative (p(SUC n)
             y))(at(lift y)))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\n x. vsum(0..n)(\k. Cx(&(binom(n,k))) * (d:num->real->complex) k
    x * e (n-k) x)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; SUB_0; binom; COMPLEX_MUL_LID];
    REPEAT GEN_TAC THEN MATCH_MP_TAC LEIBNIZ_DERIV THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Affine reparametrisation of a chain: composing a chain d with x |-> c+s*x *)
(* yields the chain n |-> Cx s pow n * d n (c + s*x).  Used to build chains  *)
(* for cphi(1+x) (c=1,s=1) and cphi(1-x) (c=1,s=-1).                         *)
(* ------------------------------------------------------------------------- *)

let AFFINE_DERIV = prove
 (`!c s x. ((\z:real^1. lift(c + s * drop z)) has_vector_derivative (lift s))
   (at(lift x))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `(\z:real^1. lift(c + s * drop z)) = (\z:real^1. lift c + s % z)`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_ADD; LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `(lift s):real^1 = vec 0 + s % vec 1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_VEC; DROP_CMUL; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID]]);;

let AFFINE_CHAIN_STEP = prove
 (`!(g:real->complex) g' c s x.
     ((\z. g(drop z)) has_vector_derivative g') (at(lift(c + s * x)))
     ==> ((\z. g(c + s * drop z)) has_vector_derivative (s % g')) (at(lift
       x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^1. lift(c + s * drop z)`;
    `\w:real^1. (g:real->complex)(drop w)`;
    `lift s`; `g':complex`; `lift x`] VECTOR_DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; DROP_CMUL] THEN
  ASM_REWRITE_TAC[AFFINE_DERIV; LIFT_DROP]);;

let AFFINE_CHAIN = prove
 (`!(d:num->real->complex) c s.
     (!m y. ((\z. d m(drop z)) has_vector_derivative (d(SUC m) y))(at(lift y)))
     ==> (!m y. ((\z. (\n x. Cx s pow n * d n (c + s * x)) m (drop z))
                 has_vector_derivative
                 ((\n x. Cx s pow n * d n (c + s * x)) (SUC m) y))(at(lift
                   y)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\w. Cx s pow m * (d:num->real->complex) m w`;
    `Cx s pow m * (d:num->real->complex)(SUC m)(c + s * y)`; `c:real`;
      `s:real`; `y:real`]
    AFFINE_CHAIN_STEP) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CONST_CHAIN_DERIV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC VDERIV_EQ THEN
    REWRITE_TAC[COMPLEX_CMUL; complex_pow] THEN CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* The compactly-supported bump psi(x) = cphi(1+x) cphi(1-x) and its         *)
(* Schwartz-ness.  psi is supported in [-1,1], C^inf (Leibniz product of two *)
(* affine reparametrisations of the phi chain), hence Schwartz -- the first  *)
(* concrete compactly-supported Schwartz function.                           *)
(* ------------------------------------------------------------------------- *)

let PSI_CHAIN = prove
 (`?p:num->real->complex.
     (!x. p 0 x = cphi(&1 + x) * cphi(&1 - x)) /\
     (!n y. ((\z. p n(drop z)) has_vector_derivative (p(SUC n) y))(at(lift
       y)))`,
  MP_TAC BUMP_CHAIN THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d:num->real->complex`; `&1`; `&1`] AFFINE_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`d:num->real->complex`; `&1`; `-- &1`] AFFINE_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\n x. Cx(&1) pow n * (d:num->real->complex) n (&1 + &1 * x)`;
                 `\n x. Cx(-- &1) pow n * (d:num->real->complex) n (&1 + -- &1
                   * x)`]
    LEIBNIZ_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:num->real->complex` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[complex_pow; COMPLEX_MUL_LID] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_ARITH `&1 + -- &1 * x = &1 - x`]);;

(* If a chain's base vanishes off [-R,R], the whole chain does (a derivative *)
(* of a locally-zero function is zero; VECTOR_DERIVATIVE_UNIQUE_AT).         *)
let CHAIN_SUPPORT = prove
 (`!(p:num->real->complex) R.
     &0 <= R /\ (!x. R < abs x ==> p 0 x = Cx(&0)) /\
     (!n y. ((\z. p n(drop z)) has_vector_derivative (p(SUC n) y))(at(lift y)))
     ==> !n x. R < abs x ==> p n x = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\z. (p:num->real->complex) n (drop z)`; `lift x`;
    `(p:num->real->complex)(SUC n) x`; `Cx(&0)`]
   VECTOR_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\z:real^1. vec 0:complex` THEN EXISTS_TAC `abs x - R` THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let SCHWARTZ_PSI = prove
 (`schwartz (\x. cphi(&1 + x) * cphi(&1 - x))`,
  MP_TAC PSI_CHAIN THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(\x. cphi(&1 + x) * cphi(&1 - x)) = (p:num->real->complex) 0`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_SUPPORT_SMOOTH_IMP_SCHWARTZ THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_POS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_gt] THEN
  MP_TAC(ISPECL [`p:num->real->complex`; `&1`] CHAIN_SUPPORT) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[cphi] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* SECTION 8. Differentiation under the integral sign (Fremlin 123D).        *)
(*                                                                           *)
(* This supplies a differentiation-under-the-integral result not otherwise   *)
(* available in the required form. It is built via the sequential Dominated  *)
(* Theorem on difference quotients:                                          *)
(*   d/dy INT F(y,x) dx = INT dF/dy(y,x) dx                                  *)
(* when dF/dy is dominated by an integrable function uniformly in y.         *)
(*                                                                           *)
(* This unlocks Fremlin 283Ch (transform of x f(x)) and thence 284C-Schwartz *)
(* (fhat is a rapidly decreasing test function) and Plancherel-on-Schwartz.  *)
(*                                                                           *)
(* Uses only the HOL Light analysis library.                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Pointwise convergence of the difference quotient, from the derivative at  *)
(* y0 and any sequence yy -> lift y0 avoiding lift y0.                       *)
(* ------------------------------------------------------------------------- *)

let DQ_PTWISE = prove
 (`!(g:real->complex) g' y0 yy.
     ((\z. g(drop z)) has_vector_derivative g') (at(lift y0)) /\
     (!n. ~(yy n = lift y0)) /\ (yy --> lift y0) sequentially
     ==> ((\n. inv(drop(yy n) - y0) % (g(drop(yy n)) - g y0)) --> g')
       sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `yy:num->real^1` o
    REWRITE_RULE[LIM_AT_SEQUENTIALLY; HAS_VECTOR_DERIVATIVE_AT_1D]) THEN
  ASM_REWRITE_TAC[o_DEF; DROP_SUB; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Increment bound from a globally bounded derivative (mean value).          *)
(* ------------------------------------------------------------------------- *)

let INCR_BOUND = prove
 (`!(g:real->complex) g' B a b.
     (!y. ((\z. g(drop z)) has_vector_derivative (g' y)) (at(lift y))) /\
     (!y. norm(g' y) <= B)
     ==> norm(g a - g b) <= B * abs(a - b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. (g:real->complex)(drop z)`;
    `\z. (g':real->complex)(drop z)`;
    `(:real^1)`; `B:real`] VECTOR_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `w:real^1` THEN
       MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o ISPECL [`lift a`; `lift b`]) THEN
    REWRITE_TAC[LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT]]);;

(* ------------------------------------------------------------------------- *)
(* Domination of the difference quotient by the dominator dm.                *)
(* ------------------------------------------------------------------------- *)

let DQ_DOMINATED = prove
 (`!(ff:real->real->complex) gg dm y0 (yy:num->real^1) n (x:real).
     (!y (x:real). ((\z. ff (drop z) x) has_vector_derivative (gg y x))
       (at(lift y))) /\
     (!y (x:real). norm(gg y x) <= dm x) /\ ~(yy n = lift y0)
     ==> norm(inv(drop(yy n) - y0) % (ff (drop(yy n)) x - ff y0 x)) <= dm x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(drop(yy(n:num)) - y0 = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((yy:num->real^1) n = lift y0)` THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (ff:real->real->complex) t x`;
    `\y. (gg:real->real->complex) y x`;
    `(dm:real->real)(x:real)`; `drop(yy(n:num))`; `y0:real`] INCR_BOUND) THEN
  ANTS_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(abs(drop(yy(n:num)) - y0)) * ((dm:real->real) x *
    abs(drop(yy(n:num)) - y0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
     ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_ABS_POS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ASM_SIMP_TAC[REAL_FIELD `~(d = &0) ==> inv(abs d) * (dmx * abs d) =
      dmx`]]);;

(* ------------------------------------------------------------------------- *)
(* The difference quotient of two integrals is the integral of the           *)
(* difference                                                                *)
(* quotient (linearity).                                                     *)
(* ------------------------------------------------------------------------- *)

let DQ_INTEGRAL = prove
 (`!(ff:real->real->complex) a b c.
     (\x:real^1. ff a (drop x)) absolutely_integrable_on (:real^1) /\
     (\x:real^1. ff b (drop x)) absolutely_integrable_on (:real^1)
     ==> c % (integral (:real^1) (\x. ff a (drop x)) -
              integral (:real^1) (\x. ff b (drop x))) =
         integral (:real^1) (\x. c % (ff a (drop x) - ff b (drop x)))`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]) THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
               INTEGRAL_CMUL; INTEGRABLE_SUB; INTEGRAL_SUB]);;

(* ------------------------------------------------------------------------- *)
(* The Dominated Convergence engine: the difference quotients of integrals   *)
(* converge to the integral of the derivative, along any sequence yy->lift   *)
(* y0.                                                                       *)
(* ------------------------------------------------------------------------- *)

let DCT_PART = prove
 (`!(ff:real->real->complex) gg dm y0 (yy:num->real^1).
     (!y (x:real). ((\z. ff (drop z) x) has_vector_derivative (gg y x))
       (at(lift y))) /\
     (!y. (\x:real^1. ff y (drop x)) absolutely_integrable_on (:real^1)) /\
     (\x:real^1. gg y0 (drop x)) absolutely_integrable_on (:real^1) /\
     (!y (x:real). norm(gg y x) <= dm x) /\
     (\x:real^1. lift(dm(drop x))) absolutely_integrable_on (:real^1) /\
     (!n. ~(yy n = lift y0)) /\ (yy --> lift y0) sequentially
     ==> ((\n. integral (:real^1)
                 (\x. inv(drop(yy n) - y0) % (ff (drop(yy n)) (drop x) - ff y0
                   (drop x))))
          --> integral (:real^1) (\x. gg y0 (drop x))) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n x:real^1. inv(drop(yy(n:num)) - y0) % (ff (drop(yy n)) (drop x) - ff y0
     (drop x)):complex`;
    `\x:real^1. (gg:real->real->complex) y0 (drop x)`;
    `\x:real^1. lift(dm(drop x))`; `(:real^1)`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
       MATCH_MP_TAC INTEGRABLE_SUB THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DQ_DOMINATED THEN
      EXISTS_TAC `gg:real->real->complex` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      MP_TAC(BETA_RULE(ISPECL [`\t. (ff:real->real->complex) t (drop x)`;
        `(gg:real->real->complex) y0 (drop x)`; `y0:real`;
          `yy:num->real^1`] DQ_PTWISE)) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* DIFFERENTIATION UNDER THE INTEGRAL SIGN (Fremlin 123D).                   *)
(* If for each x the parameter-map t |-> ff t x is differentiable with       *)
(* derivative gg y x, all ff y and gg y0 are integrable, and |gg y x| <= dm  *)
(* x                                                                         *)
(* with dm integrable (a uniform-in-y dominator), then                       *)
(*   d/dy INT ff(y,x) dx |_{y0} = INT gg(y0,x) dx.                           *)
(* ------------------------------------------------------------------------- *)

let DIFF_UNDER_INTEGRAL = prove
 (`!(ff:real->real->complex) gg dm y0.
     (!y (x:real). ((\z. ff (drop z) x) has_vector_derivative (gg y x))
       (at(lift y))) /\
     (!y. (\x:real^1. ff y (drop x)) absolutely_integrable_on (:real^1)) /\
     (\x:real^1. gg y0 (drop x)) absolutely_integrable_on (:real^1) /\
     (!y (x:real). norm(gg y x) <= dm x) /\
     (\x:real^1. lift(dm(drop x))) absolutely_integrable_on (:real^1)
     ==> ((\z. integral (:real^1) (\x. ff (drop z) (drop x)))
       has_vector_derivative
          (integral (:real^1) (\x. gg y0 (drop x)))) (at(lift y0))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_AT_1D] THEN
  REWRITE_TAC[LIM_AT_SEQUENTIALLY] THEN
  X_GEN_TAC `yy:num->real^1` THEN STRIP_TAC THEN REWRITE_TAC[o_DEF] THEN
  SUBGOAL_THEN
   `!n. inv(drop(yy(n:num) - lift y0)) %
        (integral (:real^1) (\x. ff (drop(yy n)) (drop x)) -
         integral (:real^1) (\x. ff (drop(lift y0)) (drop x))) =
        integral (:real^1) (\x. inv(drop(yy n) - y0) %
                                (ff (drop(yy n)) (drop x) - ff y0 (drop x)))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN
    MATCH_MP_TAC DQ_INTEGRAL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DCT_PART THEN
    EXISTS_TAC `dm:real->real` THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* SECTION 9. Fremlin 283Ch: differentiating the transform.                  *)
(*   (fourier f)'(y) = -i * fourier (x |-> x f(x)) (y)                       *)
(* whenever f and x f(x) are (absolutely) integrable.  This is the first     *)
(* application of DIFF_UNDER_INTEGRAL (proved above), and the key input      *)
(* to 284C (fhat is a rapidly decreasing test function).                     *)
(* ========================================================================= *)

(* Derivative of the kernel x |-> e^{-iyx} in the FREQUENCY y: it is -ix     *)
(* e^..                                                                      *)
let KERNEL_DERIV_Y = prove
 (`!(x:real) a:real^1.
     ((\z. cexp(--(ii * Cx(drop z) * Cx x))) has_vector_derivative
      (--(ii * Cx x) * cexp(--(ii * Cx(drop a) * Cx x)))) (at a)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
  COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

(* Parametric (in y) derivative of the full integrand e^{-iyx} f(x).         *)
let FFY_DERIV = prove
 (`!(f:real->complex) (x:real) y.
     ((\z. cexp(--(ii * Cx(drop z) * Cx x)) * f x) has_vector_derivative
      (--(ii * Cx x) * cexp(--(ii * Cx y * Cx x)) * f x)) (at(lift y))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`( * ):complex->complex->complex`;
    `\z. cexp(--(ii * Cx(drop z) * Cx x))`; `\z:real^1. (f:real->complex) x`;
    `--(ii * Cx x) * cexp(--(ii * Cx y * Cx x))`; `Cx(&0)`; `lift y`]
   HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL; LIFT_DROP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`x:real`; `lift y`] KERNEL_DERIV_Y) THEN
       REWRITE_TAC[LIFT_DROP];
      REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_VECTOR_DERIVATIVE_CONST]];
    MATCH_MP_TAC VDERIV_EQ THEN
    CONV_TAC COMPLEX_RING]);;

(* |d/dy integrand| = |x f(x)| (kernel has unit modulus), the DCT dominator. *)
let GG_DOM = prove
 (`!(f:real->complex) (x:real) y.
     norm(--(ii * Cx x) * cexp(--(ii * Cx y * Cx x)) * f x) <= norm(Cx x * f
       x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_NEG; COMPLEX_NORM_II;
              COMPLEX_NORM_CX; FOURIER_KERNEL_NORM] THEN REAL_ARITH_TAC);;

(* The derivative integrand -ix e^{-iyx} f(x) is absolutely integrable       *)
(* (modulation of x f(x)).                                                   *)
let GGY0_ABSINT = prove
 (`!(f:real->complex) y0.
     (\x:real^1. Cx(drop x) * f(drop x)) absolutely_integrable_on (:real^1)
     ==> (\x:real^1. --(ii * Cx(drop x)) * cexp(--(ii * Cx y0 * Cx(drop x))) *
       f(drop x))
         absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. Cx t * (f:real->complex) t`;
    `y0:real`] FOURIER_MODULATION_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `--ii` o MATCH_MP
    ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL) THEN
  MATCH_MP_TAC(MESON[] `f = g ==> f absolutely_integrable_on s ==> g
    absolutely_integrable_on s`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC COMPLEX_RING);;

(* 283Ch (unnormalised): derivative of the inner Fourier integral in y.      *)
let FOURIER_283CH_RAW = prove
 (`!(f:real->complex) y0.
     (!y. (\x:real^1. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))
       absolutely_integrable_on (:real^1)) /\
     (\x:real^1. Cx(drop x) * f(drop x)) absolutely_integrable_on (:real^1)
     ==> ((\z. integral (:real^1) (\x. cexp(--(ii * Cx(drop z) * Cx(drop x))) *
       f(drop x)))
          has_vector_derivative
          (integral (:real^1) (\x. --(ii * Cx(drop x)) * cexp(--(ii * Cx y0 *
            Cx(drop x))) * f(drop x))))
         (at(lift y0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\y x. cexp(--(ii * Cx y * Cx x)) * (f:real->complex) x`;
    `\y x. --(ii * Cx x) * cexp(--(ii * Cx y * Cx x)) * (f:real->complex) x`;
    `\x. norm(Cx x * (f:real->complex) x)`;
      `y0:real`] DIFF_UNDER_INTEGRAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[FFY_DERIV];
      ASM_REWRITE_TAC[]; MATCH_MP_TAC GGY0_ABSINT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GG_DOM];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]]);;

(* Reshape the derivative integral into -i * fourier(x f).                   *)
let CH_RESHAPE = prove
 (`!(f:real->complex) y0.
     (\x:real^1. Cx(drop x) * f(drop x)) absolutely_integrable_on (:real^1)
     ==> Cx(&1) / Cx(sqrt(&2 * pi)) *
         integral (:real^1) (\x. --(ii * Cx(drop x)) * cexp(--(ii * Cx y0 *
           Cx(drop x))) * f(drop x)) =
         --ii * fourier (\x. Cx x * f x) y0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\x. --(ii * Cx(drop x)) * cexp(--(ii * Cx y0 * Cx(drop
     x))) * f(drop x)) =
    --ii * integral (:real^1) (\x. cexp(--(ii * Cx y0 * Cx(drop x))) * (Cx(drop
      x) * f(drop x)))`
   SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_COMPLEX_LMUL o rand o snd)
     THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`\t. Cx t * (f:real->complex) t`;
       `y0:real`] FOURIER_MODULATION_ABSINT) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTEGRAL_EQ THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING];
    CONV_TAC COMPLEX_RING]);;

(* 283Ch (Fremlin form): (fourier f)'(y0) = -i * fourier(x |-> x f(x))(y0).  *)
let FOURIER_283CH = prove
 (`!(f:real->complex) y0.
     (!y. (\x:real^1. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x))
       absolutely_integrable_on (:real^1)) /\
     (\x:real^1. Cx(drop x) * f(drop x)) absolutely_integrable_on (:real^1)
     ==> ((\z. fourier f (drop z)) has_vector_derivative
          (--ii * fourier (\x. Cx x * f x) y0)) (at(lift y0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `--ii * fourier (\x. Cx x * (f:real->complex) x) y0 =
    Cx(&1) / Cx(sqrt(&2 * pi)) *
    integral (:real^1) (\x. --(ii * Cx(drop x)) * cexp(--(ii * Cx y0 * Cx(drop
      x))) * f(drop x))`
   SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CH_RESHAPE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[fourier] THEN MATCH_MP_TAC CONST_CHAIN_DERIV THEN
    MATCH_MP_TAC FOURIER_283CH_RAW THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Conjugate of the transform = inverse transform of the conjugate:          *)
(*   cnj(fourier f y) = (1/sqrt2pi) INT e^{+iyx} cnj(f x) dx.                *)
(* The bridge for Plancherel-on-Schwartz (284O(a)(i)): g-bar =               *)
(* (f-bar)-check.                                                            *)
(* ------------------------------------------------------------------------- *)

let CNJ_FOURIER = prove
 (`!(f:real->complex) y.
     (\x:real^1. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x)) integrable_on
       (:real^1)
     ==> cnj(fourier f y) =
         Cx(&1)/Cx(sqrt(&2*pi)) *
         integral (:real^1) (\x. cexp(ii * Cx y * Cx(drop x)) * cnj(f(drop
           x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  REWRITE_TAC[CNJ_MUL; CNJ_DIV; CNJ_CX] THEN BINOP_TAC THENL
   [REWRITE_TAC[];
    MP_TAC(ISPECL [`\x. cexp(--(ii * Cx y * Cx(drop x))) *
      (f:real->complex)(drop x)`;
                   `(:real^1)`; `cnj`] INTEGRAL_LINEAR) THEN
    ASM_REWRITE_TAC[LINEAR_CNJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[o_DEF; CNJ_MUL; CNJ_CEXP] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CNJ_NEG; CNJ_MUL; CNJ_II; CNJ_CX] THEN
      SIMPLE_COMPLEX_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The inverse Fourier transform is the forward transform at the negated     *)
(* frequency: (1/sqrt2pi) INT e^{+iyx} f(x) dx = fourier f (-y).             *)
(* ------------------------------------------------------------------------- *)

let FOURIER_INV_NEG = prove
 (`!(f:real->complex) y. fourier f (--y) =
     Cx(&1)/Cx(sqrt(&2*pi)) * integral (:real^1) (\x. cexp(ii * Cx y * Cx(drop
       x)) * f(drop x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fourier] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CX_NEG] THEN SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Plancherel on Schwartz functions (Fremlin 284O(a)(i)):                    *)
(*   INT fhat * conj(fhat) = INT f * conj(f),  i.e. ||fhat||_2 = ||f||_2.    *)
(* Via the multiplication formula 283O applied to (fhat, x |-> conj(f(-x))), *)
(* the conjugate/reflection bridges, and the double-transform reflection.    *)
(* ------------------------------------------------------------------------- *)

(* fourier(x |-> conj(f(-x)))(z) = conj(fourier f z) (modulated f            *)
(* integrable).                                                              *)
let FOURIER_CNJ_REFLECT = prove
 (`!(f:real->complex) z.
     (\x:real^1. cexp(--(ii * Cx z * Cx(drop x))) * f(drop x)) integrable_on
       (:real^1)
     ==> fourier (\x. cnj(f(--x))) z = cnj(fourier f z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. cnj((f:real->complex) x)`;
    `z:real`] FOURIER_REFLECT) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`f:real->complex`; `z:real`] CNJ_FOURIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM FOURIER_INV_NEG]);;

(* Double transform is reflection: fourier(fourier h)(-z) = h z (Schwartz    *)
(* h).                                                                       *)
let DOUBLE_TRANSFORM = prove
 (`!(h:real->complex) z. schwartz h ==> fourier (fourier h) (--z) = h z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fourier(h:real->complex)`; `z:real`] FOURIER_INV_NEG) THEN
  REWRITE_TAC[GSYM CX_INV; complex_div; COMPLEX_MUL_LID] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`h:real->complex`; `z:real`] FOURIER_284C_INVERSION) THEN
  ASM_REWRITE_TAC[]);;

(* conj(f(-.)) is absolutely integrable when f is.                           *)
let CNJ_REFLECT_ABSINT = prove
 (`!(h:real->complex). (\z:real^1. h(drop z)) absolutely_integrable_on
   (:real^1)
     ==> (\z:real^1. cnj(h(--(drop z)))) absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\z:real^1. cnj(h(--(drop z)))) = cnj o (\z:real^1. h(drop(--z)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_NEG]; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN REWRITE_TAC[LINEAR_CNJ] THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_REFLECT_GEN] THEN
  SUBGOAL_THEN `IMAGE (--) (:real^1) = (:real^1)` SUBST1_TAC THENL
   [REWRITE_TAC[REFLECT_UNIV]; ASM_REWRITE_TAC[]]);;

(* Modulated integrand is integrable when f is absolutely integrable.        *)
let MODINT = prove
 (`!(h:real->complex) z. (\x:real^1. h(drop x)) absolutely_integrable_on
   (:real^1)
     ==> (\x:real^1. cexp(--(ii * Cx z * Cx(drop x))) * h(drop x))
       integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC FOURIER_MODULATION_ABSINT THEN ASM_REWRITE_TAC[]);;

let PARSEVAL_SCHWARTZ = prove
 (`!(h:real->complex). schwartz h
     ==> integral (:real^1) (\z. fourier h (drop z) * cnj(fourier h (drop z)))
       =
         integral (:real^1) (\z. h(drop z) * cnj(h(drop z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHWARTZ_ABSINT) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHWARTZ_FHAT_ABSINT) THEN
  MP_TAC(ISPECL [`fourier(h:real->complex)`;
    `\x. cnj((h:real->complex)(--x))`] FOURIER_283O) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CNJ_REFLECT_ABSINT THEN
     ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\z. fourier h (drop z) * fourier (\x.
     cnj((h:real->complex)(--x))) (drop z)) =
    integral (:real^1) (\z. fourier h (drop z) * cnj(fourier h (drop z)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC FOURIER_CNJ_REFLECT THEN MATCH_MP_TAC MODINT THEN
      ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\z. fourier (fourier h) (drop z) *
     cnj((h:real->complex)(--(drop z)))) =
    integral (:real^1) (\z. h(--(drop z)) * cnj(h(--(drop z))))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_NEG_NEG] THEN
      ASM_SIMP_TAC[DOUBLE_TRANSFORM; REAL_NEG_NEG];
    MP_TAC(ISPEC `\t. (h:real->complex) t * cnj(h t)` INTEGRAL_REFLECT_R) THEN
    REWRITE_TAC[]]);;


(* ========================================================================= *)
(* SECTION 10. Density of Schwartz functions in L^2 (Fremlin 284N).          *)
(*                                                                           *)
(* The proof uses a                                                          *)
(* convolution-free route that reuses the compactly-supported Schwartz bump  *)
(* SCHWARTZ_PSI (proved above):                                              *)
(*                                                                           *)
(*   Brick 1  LSPACE_APPROXIMATE_COMPACT_SUPPORT                             *)
(*            compactly-supported functions are L^p dense (general p, any    *)
(*            dimension), by dominated convergence on the ball truncations.  *)
(*   Brick 2  a smooth plateau eta (=1 on [-R,R], supported in [-R-2,R+2])   *)
(*            built from a smooth ramp Theta(t) = (1/I) INT_{-2}^{t} psi.    *)
(*   Brick 3  284N: truncate (brick 1) -> polynomial-approximate on the      *)
(* bounded support (LSPACE_APPROXIMATE_VECTOR_POLYNOMIAL_FUNCTION)           *)
(*            -> multiply by the plateau to get a compactly-supported smooth *)
(*            (hence Schwartz) approximant.                                  *)
(* ========================================================================= *)

(* The L^p norm of a difference is symmetric in its two arguments.           *)
let LNORM_SUB_SYM = prove
 (`!s p (a:real^M->real^N) b.
     lnorm s p (\x. a x - b x) = lnorm s p (\x. b x - a x)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LNORM_NEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Brick 1: compactly-supported functions are dense in L^p.                  *)
(* ------------------------------------------------------------------------- *)

(* The truncation of an L^p function to a measurable set stays in L^p.       *)
let TRUNC_IN_LSPACE = prove
 (`!(f:real^M->real^N) t p.
     &0 < p /\ f IN lspace (:real^M) p /\ lebesgue_measurable t
     ==> (\x. if x IN t then f x else vec 0) IN lspace (:real^M) p`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_RESTRICT THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `(\x:real^M. lift (norm (if x IN t then (f:real^M->real^N) x else vec 0)
       rpow p)) =
      (\x. if x IN t then lift(norm(f x) rpow p) else vec 0)`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[NORM_0] THEN
      ASM_SIMP_TAC[RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM];
      REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `i = 1` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[DIMINDEX_1; LE_ANTISYM]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM drop; LIFT_DROP; RPOW_POS_LE; NORM_POS_LE]]]);;

(* Dominated convergence: the ball-truncations converge to f in              *)
(* L^p-seminorm.                                                             *)
let TRUNC_LNORM_LIM = prove
 (`!(f:real^M->real^N) p.
     &0 < p /\ f IN lspace (:real^M) p
     ==> ((\n. lnorm (:real^M) p
              (\x. f x - (if x IN ball(vec 0,&n) then f x else vec 0))) --->
                &0)
         sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\n. lnorm (:real^M) p
         (\x. (f:real^M->real^N) x - (if x IN ball(vec 0,&n) then f x else vec
           0))) =
    (\n. lnorm (:real^M) p
         (\x. (if x IN ball(vec 0,&n) then f x else vec 0) - f x))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[LNORM_SUB_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n:num. \x:real^M. if x IN ball(vec 0,&n) then (f:real^M->real^N) x else
     vec 0`;
    `f:real^M->real^N`; `f:real^M->real^N`; `(:real^M)`; `p:real`;
      `{}:real^M->bool`]
   LSPACE_DOMINATED_CONVERGENCE) THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC TRUNC_IN_LSPACE THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL];
      REPEAT GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC LIM_EVENTUALLY THEN
        REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      MP_TAC(ISPEC `norm(x:real^M)` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_BALL_0] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `norm(x:real^M) < &n` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N:real` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    SIMP_TAC[]]);;

(* Brick 1: compactly-supported L^p approximation (Fremlin's tail step).     *)
let LSPACE_APPROXIMATE_COMPACT_SUPPORT = prove
 (`!(f:real^M->real^N) p e.
     &0 < p /\ f IN lspace (:real^M) p /\ &0 < e
     ==> ?g R. g IN lspace (:real^M) p /\
               (!x. R < norm x ==> g x = vec 0) /\
               lnorm (:real^M) p (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `p:real`] TRUNC_LNORM_LIM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  EXISTS_TAC `\x:real^M. if x IN ball(vec 0,&N) then (f:real^M->real^N) x else
    vec 0` THEN
  EXISTS_TAC `&N:real` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TRUNC_IN_LSPACE THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `&0 <= lnorm (:real^M) p
          (\x. (f:real^M->real^N) x - (if x IN ball(vec 0,&N) then f x else vec
            0))`
     MP_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; TRUNC_IN_LSPACE; LEBESGUE_MEASURABLE_BALL];
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Brick 2: a smooth plateau.  The building block is the real bump           *)
(*   rpsi(x) = rphi(1+x) * rphi(1-x),   rphi(x) = exp(-1/x) [x>0], 0 [x<=0], *)
(* i.e. the real form of the SCHWARTZ_PSI bump: nonnegative, continuous,     *)
(* supported in [-1,1], with strictly positive total integral.               *)
(* ------------------------------------------------------------------------- *)

let rphi = new_definition
  `rphi (x:real) = if &0 < x then exp(--(inv x)) else &0`;;

let rpsi = new_definition
  `rpsi (x:real) = rphi(&1 + x) * rphi(&1 - x)`;;

(* Bridge to the complex bump cphi (defined above).                          *)
let CPHI_RPHI = prove
 (`!x. cphi x = Cx(rphi x)`,
  GEN_TAC THEN REWRITE_TAC[cphi; rphi] THEN COND_CASES_TAC THEN
    REWRITE_TAC[]);;

let CPSI_RPSI = prove
 (`!x. cphi(&1 + x) * cphi(&1 - x) = Cx(rpsi x)`,
  GEN_TAC THEN REWRITE_TAC[CPHI_RPHI; rpsi; GSYM CX_MUL]);;

let RPSI_POS = prove
 (`!x. &0 <= rpsi x`,
  GEN_TAC THEN REWRITE_TAC[rpsi; rphi] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE]);;

let RPSI_SUPPORT = prove
 (`!x. &1 < abs x ==> rpsi x = &0`,
  GEN_TAC THEN REWRITE_TAC[rpsi; rphi] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC);;

(* Continuity of rpsi: p 0 of PSI_CHAIN is differentiable and equals Cx o    *)
(* rpsi.                                                                     *)
let CX_RPSI_CONT = prove
 (`(\z:real^1. Cx(rpsi(drop z))) continuous_on (:real^1)`,
  X_CHOOSE_THEN `p:num->real->complex` STRIP_ASSUME_TAC PSI_CHAIN THEN
  SUBGOAL_THEN
    `(\z:real^1. Cx(rpsi(drop z))) = (\z. (p:num->real->complex) 0 (drop z))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     ASM_REWRITE_TAC[CPSI_RPSI]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `x:real^1` THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `\h. drop h % (p:num->real->complex) 1 (drop x)` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `drop(x:real^1)`]) THEN
  REWRITE_TAC[LIFT_DROP; has_vector_derivative; ARITH_RULE `SUC 0 = 1`]);;

let RPSI_REAL_CONT = prove
 (`rpsi real_continuous_on (:real)`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_UNIV] THEN
  MP_TAC CX_RPSI_CONT THEN REWRITE_TAC[CONTINUOUS_ON; o_DEF] THEN
  REWRITE_TAC[LIM_CX_LIFT]);;

let RPSI_REAL_INT = prove
 (`rpsi real_integrable_on (:real)`,
  MATCH_MP_TAC REAL_INTEGRABLE_ON_SUPERSET THEN
  EXISTS_TAC `real_interval[-- &1, &1]` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_TAC THEN MATCH_MP_TAC RPSI_SUPPORT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[SUBSET_UNIV; RPSI_REAL_CONT]]);;

let RPSI_INT_HALF = prove
 (`rpsi real_integrable_on real_interval[-- &1 / &2, &1 / &2]`,
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
  REWRITE_TAC[SUBSET_UNIV; RPSI_REAL_CONT]);;

(* rpsi >= exp(-4) on [-1/2,1/2]: both factors exp(-1/(1 +- x)) >= exp(-2).  *)
let RPSI_LOWER = prove
 (`!x. x IN real_interval[-- &1 / &2, &1 / &2] ==> exp(-- &4) <= rpsi x`,
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[rpsi; rphi] THEN
  SUBGOAL_THEN `&0 < &1 + x /\ &0 < &1 - x` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exp(-- &4) = exp(-- &2) * exp(-- &2)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    CONJ_TAC THEN
  SUBGOAL_THEN `&2 = inv(&1 / &2)` SUBST1_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);;

(* The normalising constant I = INT rpsi is strictly positive.               *)
let IPSI_POS = prove
 (`&0 < real_integral (:real) rpsi`,
  SUBGOAL_THEN
   `exp(-- &4) <= real_integral (real_interval[-- &1 / &2, &1 / &2]) rpsi /\
    real_integral (real_interval[-- &1 / &2, &1 / &2]) rpsi <=
    real_integral (:real) rpsi`
   MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `real_integral (real_interval[-- &1 / &2, &1 / &2]) (\x.
        exp(-- &4))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `-- &1 / &2 <= &1 / &2`] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRAL_LE THEN
        ASM_SIMP_TAC[REAL_INTEGRABLE_CONST; RPSI_INT_HALF; RPSI_LOWER]];
      MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
      REWRITE_TAC[SUBSET_UNIV; RPSI_POS; RPSI_REAL_INT; RPSI_INT_HALF]];
    MP_TAC(SPEC `-- &4` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC]);;

(* rpsi vanishes on (-inf,-1] (rphi(1+x)=0 there); needed at the endpoint    *)
(* -1.                                                                       *)
let RPSI_ZERO_LEFT = prove
 (`!x. x <= -- &1 ==> rpsi x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rpsi; rphi] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The smooth ramp  rtheta(t) = (1/I) INT_{[-2,t]} rpsi,  I = INT rpsi.      *)
(* It is 0 on (-inf,-1], climbs to 1 on [1,inf), stays in [0,1], and is      *)
(* everywhere differentiable with rtheta' = (1/I) rpsi (FTC for t > -2;      *)
(* locally constant 0 for t < -1; the two ranges cover R since -2 < -1).     *)
(* ------------------------------------------------------------------------- *)

let rtheta = new_definition
  `rtheta (t:real) = inv(real_integral (:real) rpsi) *
                     real_integral (real_interval[-- &2, t]) rpsi`;;

let RTHETA_LAM = prove
 (`rtheta = \t. inv(real_integral (:real) rpsi) * real_integral
   (real_interval[-- &2, t]) rpsi`,
  REWRITE_TAC[FUN_EQ_THM; rtheta]);;

let RTHETA_INT_HALF = prove
 (`!t. rpsi real_integrable_on real_interval[-- &2, t]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
  REWRITE_TAC[SUBSET_UNIV; RPSI_REAL_CONT]);;

(* rtheta vanishes on (-inf,-1]: the integrand rpsi is 0 throughout [-2,t].  *)
let RTHETA_ZERO = prove
 (`!t. t <= -- &1 ==> rtheta t = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rtheta] THEN
  SUBGOAL_THEN
    `real_integral (real_interval[-- &2, t]) rpsi = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ_0 THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC RPSI_ZERO_LEFT THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_RZERO]]);;

(* Derivative for t > -2 via the fundamental theorem of calculus.            *)
let RTHETA_DERIV_POS = prove
 (`!t. -- &2 < t
       ==> (rtheta has_real_derivative (inv(real_integral (:real) rpsi) * rpsi
         t))
           (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RTHETA_LAM] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MP_TAC(ISPECL
    [`\u. real_integral (real_interval [-- &2,u]) rpsi`; `rpsi t`;
     `t:real`; `real_interval(-- &2, t + &1)`]
    HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `real_interval[-- &2, t + &1]` THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`rpsi`; `-- &2`;
     `t + &1`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
      REWRITE_TAC[SUBSET_UNIV; RPSI_REAL_CONT];
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* Derivative for t < -1: rtheta is locally constant 0 there.                *)
let RTHETA_DERIV_NEG = prove
 (`!t. t < -- &1
       ==> (rtheta has_real_derivative (inv(real_integral (:real) rpsi) * rpsi
         t))
           (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv(real_integral (:real) rpsi) * rpsi t = &0` SUBST1_TAC THENL
   [SUBGOAL_THEN `rpsi t = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC RPSI_ZERO_LEFT THEN
       ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_RZERO]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\t:real. &0`; `-- &1 - t`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RTHETA_ZERO THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]]);;

(* rtheta is everywhere differentiable with derivative (1/I) rpsi.           *)
let RTHETA_DERIV = prove
 (`!t. (rtheta has_real_derivative (inv(real_integral (:real) rpsi) * rpsi t))
       (atreal t)`,
  GEN_TAC THEN DISJ_CASES_TAC(REAL_ARITH `t < -- &1 \/ -- &2 < t`) THENL
   [MATCH_MP_TAC RTHETA_DERIV_NEG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RTHETA_DERIV_POS THEN ASM_REWRITE_TAC[]]);;

let RTHETA_ONE = prove
 (`!t. &1 <= t ==> rtheta t = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rtheta] THEN
  SUBGOAL_THEN
    `real_integral (real_interval[-- &2, t]) rpsi = real_integral (:real) rpsi`
   SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_ON_SUPERSET THEN
    EXISTS_TAC `real_interval[-- &2, t]` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_TAC THEN MATCH_MP_TAC RPSI_SUPPORT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN REWRITE_TAC[RTHETA_INT_HALF]];
    MATCH_MP_TAC REAL_MUL_LINV THEN MP_TAC IPSI_POS THEN REAL_ARITH_TAC]);;

let RTHETA_BOUNDS = prove
 (`!t. &0 <= rtheta t /\ rtheta t <= &1`,
  GEN_TAC THEN REWRITE_TAC[rtheta] THEN
  SUBGOAL_THEN `&0 < real_integral (:real) rpsi` ASSUME_TAC THENL
   [REWRITE_TAC[IPSI_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_integral (real_interval[-- &2, t]) rpsi /\
                real_integral (real_interval[-- &2, t]) rpsi <= real_integral
                  (:real) rpsi`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_POS THEN
       REWRITE_TAC[RTHETA_INT_HALF; RPSI_POS];
      MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
      REWRITE_TAC[SUBSET_UNIV; RPSI_POS; RPSI_REAL_INT; RTHETA_INT_HALF]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    SUBGOAL_THEN
     `inv(real_integral (:real) rpsi) * real_integral (real_interval[-- &2, t])
       rpsi <=
      inv(real_integral (:real) rpsi) * real_integral (:real) rpsi`
     MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
       ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]]]);;

(* The complex ramp Cx o rtheta carries a full smooth derivative chain: its  *)
(* first derivative is (1/I) times the SCHWARTZ_PSI chain p, so every higher *)
(* derivative is a constant multiple of a p-derivative.                      *)
let RTHETA_CHAIN = prove
 (`?d:num->real->complex.
     d 0 = (\x. Cx(rtheta x)) /\
     (!n y. ((\z. d n(drop z)) has_vector_derivative (d(SUC n) y))(at(lift
       y)))`,
  X_CHOOSE_THEN `p:num->real->complex` STRIP_ASSUME_TAC PSI_CHAIN THEN
  EXISTS_TAC
   `\n. if n = 0 then (\x. Cx(rtheta x))
        else (\x. Cx(inv(real_integral (:real) rpsi)) *
          (p:num->real->complex)(n - 1) x)` THEN
  CONJ_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN X_GEN_TAC `y:real` THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; ARITH] THENL
   [REWRITE_TAC[CPSI_RPSI; GSYM CX_MUL] THEN
    MATCH_MP_TAC CX_VECTOR_DERIV_BRIDGE THEN REWRITE_TAC[RTHETA_DERIV];
    SUBGOAL_THEN `p n = (p:num->real->complex)(SUC(n - 1))` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONST_CHAIN_DERIV THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The plateau  eta R x = rtheta(x+R+1) * rtheta(R+1-x):  = 1 on [-R,R],     *)
(* supported in [-R-2,R+2], with values in [0,1] and a full smooth chain.    *)
(* ------------------------------------------------------------------------- *)

let eta = new_definition
  `eta (R:real) (x:real) = rtheta(x + (R + &1)) * rtheta((R + &1) - x)`;;

let ETA_SUPPORT = prove
 (`!R x. &0 <= R /\ R + &2 < abs x ==> eta R x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eta] THEN
  DISJ_CASES_TAC(REAL_ARITH `x < &0 \/ &0 <= x`) THENL
   [SUBGOAL_THEN `rtheta(x + (R + &1)) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC RTHETA_ZERO THEN
       ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_LZERO]];
    SUBGOAL_THEN `rtheta((R + &1) - x) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC RTHETA_ZERO THEN
       ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_RZERO]]]);;

let ETA_ONE = prove
 (`!R x. abs x <= R ==> eta R x = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eta] THEN
  SUBGOAL_THEN `rtheta(x + (R + &1)) = &1 /\ rtheta((R + &1) - x) = &1`
   (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
  CONJ_TAC THEN MATCH_MP_TAC RTHETA_ONE THEN ASM_REAL_ARITH_TAC);;

let ETA_BOUNDS = prove
 (`!R x. &0 <= eta R x /\ eta R x <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eta] THEN
  MP_TAC(SPEC `x + (R + &1)` RTHETA_BOUNDS) THEN
  MP_TAC(SPEC `(R + &1) - x` RTHETA_BOUNDS) THEN
  STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rtheta(x + (R + &1)) * &1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC]]);;

(* Smooth chain for Cx o eta R, from PLATEAU_CHAIN = LEIBNIZ of two affine   *)
(* copies of the ramp chain.                                                 *)
let PLATEAU_CHAIN = prove
 (`!R. ?q:num->real->complex.
        q 0 = (\x. Cx(rtheta(x + (R + &1))) * Cx(rtheta((R + &1) - x))) /\
        (!n y. ((\z. q n(drop z)) has_vector_derivative (q(SUC n) y))(at(lift
          y)))`,
  GEN_TAC THEN X_CHOOSE_THEN
    `d:num->real->complex` STRIP_ASSUME_TAC RTHETA_CHAIN THEN
  MP_TAC(ISPECL [`d:num->real->complex`; `R + &1`; `&1`] AFFINE_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`d:num->real->complex`; `R + &1`; `-- &1`] AFFINE_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`\n x. Cx(&1) pow n * (d:num->real->complex) n ((R + &1) + &1 * x)`;
     `\n x. Cx(-- &1) pow n * (d:num->real->complex) n ((R + &1) + -- &1 * x)`]
    LEIBNIZ_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->real->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:num->real->complex` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
  ASM_REWRITE_TAC[complex_pow; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `(R + &1) + &1 * x = x + R + &1`;
              REAL_ARITH `(R + &1) + -- &1 * x = (R + &1) - x`]);;

let ETA_CHAIN = prove
 (`!R. ?q:num->real->complex.
        q 0 = (\x. Cx(eta R x)) /\
        (!n y. ((\z. q n(drop z)) has_vector_derivative (q(SUC n) y))(at(lift
          y)))`,
  GEN_TAC THEN X_CHOOSE_THEN `q:num->real->complex` STRIP_ASSUME_TAC
   (SPEC `R:real` PLATEAU_CHAIN) THEN
  EXISTS_TAC `q:num->real->complex` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; eta; CX_MUL]);;

(* Any vector polynomial function, viewed as real->complex, carries a chain  *)
(* (its derivatives are again vector polynomials).                           *)
let POLY_CHAIN = prove
 (`!P:real^1->real^2. vector_polynomial_function P
     ==> ?e:num->real->complex.
           e 0 = (\x. P(lift x)) /\
           (!n y. ((\z. e n(drop z)) has_vector_derivative (e(SUC n)
             y))(at(lift y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\(n:num) (Q:real^1->real^2). vector_polynomial_function Q`;
    `\(n:num) (Q:real^1->real^2) (Q':real^1->real^2).
        !x. (Q has_vector_derivative (Q' x)) (at x)`;
    `P:real^1->real^2`] DEPENDENT_CHOICE_FIXED) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP
      HAS_VECTOR_DERIVATIVE_VECTOR_POLYNOMIAL_FUNCTION) THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:num->real^1->real^2` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `\n:num. \x:real. (f:num->real^1->real^2) n (lift x)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      ASM_REWRITE_TAC[]]);;

(* The plateau times any polynomial is Schwartz (smooth product chain via    *)
(* LEIBNIZ_CHAIN, compact support inherited from the plateau).  This is the  *)
(* bridge from the polynomial L^2-approximant to a Schwartz approximant.     *)
let ETAP_SCHWARTZ = prove
 (`!R (P:real^1->real^2). &0 <= R /\ vector_polynomial_function P
     ==> schwartz (\x. Cx(eta R x) * P(lift x))`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN
    `q:num->real->complex` STRIP_ASSUME_TAC (SPEC `R:real` ETA_CHAIN) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `en:num->real->complex` STRIP_ASSUME_TAC o
    MATCH_MP POLY_CHAIN) THEN
  MP_TAC(ISPECL [`q:num->real->complex`;
    `en:num->real->complex`] LEIBNIZ_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->real->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `(\x. Cx (eta R x) * P(lift x)) = (s:num->real->complex) 0`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_SUPPORT_SMOOTH_IMP_SCHWARTZ THEN
  EXISTS_TAC `R + &2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_gt] THEN MATCH_MP_TAC CHAIN_SUPPORT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eta R x = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC ETA_SUPPORT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CX_MUL; COMPLEX_MUL_LZERO; CX_INJ]]]);;

(* ------------------------------------------------------------------------- *)
(* Brick 3: Schwartz functions are dense in L^2 (Fremlin 284N).              *)
(* Supporting facts: a Schwartz function is continuous, bounded, and in L^2. *)
(* ------------------------------------------------------------------------- *)

let SCHWARTZ_CONT = prove
 (`!h:real->complex. schwartz h ==> (\z:real^1. h(drop z)) continuous_on
   (:real^1)`,
  REWRITE_TAC[schwartz] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `x:real^1` THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `\h'. drop h' % (d:num->real->complex) 1 (drop x)` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `drop(x:real^1)`]) THEN
  ASM_REWRITE_TAC[LIFT_DROP; has_vector_derivative;
    ARITH_RULE `SUC 0 = 1`] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[]);;

let SCHWARTZ_BOUNDED = prove
 (`!h:real->complex. schwartz h ==> ?B. !x. norm(h x) <= B`,
  REWRITE_TAC[schwartz] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `0`]) THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  X_GEN_TAC `x:real` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
  ASM_REWRITE_TAC[real_pow; REAL_MUL_LID]);;

(* A Schwartz function is square-integrable: |h|^2 <= B|h| with |h| in L^1.  *)
let SCHWARTZ_L2 = prove
 (`!h:real->complex. schwartz h ==> (\z:real^1. h(drop z)) IN lspace (:real^1)
   (&2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHWARTZ_CONT) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o MATCH_MP SCHWARTZ_BOUNDED) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHWARTZ_ABSINT) THEN
  SUBGOAL_THEN `(\z:real^1. (h:real->complex)(drop z)) measurable_on (:real^1)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\z:real^1. B % lift(norm((h:real->complex)(drop z)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_RPOW THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    REWRITE_TAC[o_DEF] THEN REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP; REAL_ABS_RPOW;
      REAL_ABS_NORM] THEN
    REWRITE_TAC[RPOW_POW] THEN
    SUBGOAL_THEN
      `norm((h:real->complex)(drop z)) pow 2 =
       norm(h(drop z)) * norm(h(drop z))`
     SUBST1_TAC THENL [REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;

(* Glue: the L^2 seminorm over all of R equals that over a set s whenever    *)
(* the function vanishes off s (needs p>0, so &0 rpow p = &0).               *)
let LNORM_SUPPORTED = prove
 (`!(phi:real^1->real^2) s p.
     &0 < p /\ (!x. ~(x IN s) ==> phi x = vec 0)
     ==> lnorm (:real^1) p phi = lnorm s p phi`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnorm] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. lift(norm((phi:real^1->real^2) x) rpow p)`;
    `s:real^1->bool`]
        INTEGRAL_RESTRICT_UNIV) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[NORM_0; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM]);;

(* ------------------------------------------------------------------------- *)
(* 284N: Schwartz functions are dense in L^2 (Fremlin 284N).                 *)
(* Assembly of the three bricks:                                             *)
(*  (1) truncate f to a compactly-supported g   (LSPACE_APPROXIMATE_COMPACT_ *)
(*      SUPPORT), with ||f-g||_2 < e/2, g supported in |x|<=R;               *)
(*  (2) approximate g by a polynomial P on the bounded set                   *)
(*      s = interval[-(|R|+2), |R|+2]           (LSPACE_APPROXIMATE_VECTOR_  *)
(*      POLYNOMIAL_FUNCTION), with ||g-P||_{2,s} < e/2;                      *)
(*  (3) the Schwartz approximant is eta_(|R|) * P (ETAP_SCHWARTZ).  Since    *)
(*      eta = 1 where g <> 0 we have g = eta*g, so f - eta*P = (f-g) +       *)
(*      eta*(g-P); the second term is supported in s (LNORM_SUPPORTED) and   *)
(*      dominated pointwise by g-P (|eta|<=1, LNORM_MONO).                   *)
let LSPACE_APPROXIMATE_SCHWARTZ = prove
 (`!f:real^1->real^2. f IN lspace (:real^1) (&2)
     ==> !e. &0 < e
             ==> ?h. schwartz h /\
                     lnorm (:real^1) (&2) (\x. f x - (\z. h(drop z)) x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^2`; `&2`; `e / &2`]
        LSPACE_APPROXIMATE_COMPACT_SUPPORT) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_ARITH `&0 < &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2`
    (X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `s = interval[lift(--(abs R + &2)), lift(abs R + &2)]` THEN
  SUBGOAL_THEN
   `bounded s /\ measurable s /\ lebesgue_measurable(s:real^1->bool)`
   STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    REWRITE_TAC[BOUNDED_INTERVAL; MEASURABLE_INTERVAL;
      LEBESGUE_MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^2`; `s:real^1->bool`; `&2`; `e / &2`]
        LSPACE_APPROXIMATE_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF; REAL_ARITH `&1 <= &2`] THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^1->real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. Cx(eta (abs R) x) * (P:real^1->real^2)(lift x)` THEN
    CONJ_TAC THENL
   [MATCH_MP_TAC ETAP_SCHWARTZ THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN
    `!x:real^1. Cx(eta (abs R) (drop x)) * (g:real^1->real^2) x = g x`
   ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN
    ASM_CASES_TAC `norm(x:real^1) <= abs R` THENL
     [SUBGOAL_THEN `eta (abs R) (drop x) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC ETA_ONE THEN
        POP_ASSUM MP_TAC THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
          REAL_ARITH_TAC;
        REWRITE_TAC[COMPLEX_MUL_LID]];
      SUBGOAL_THEN `(g:real^1->real^2) x = vec 0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. Cx(eta (abs R) (drop x)) * (P:real^1->real^2) x) IN lspace
     (:real^1) (&2)`
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x:real^1. Cx(eta (abs R) (drop x)) * (P:real^1->real^2) x) =
      (\z:real^1. (\x. Cx(eta (abs R) x) * P(lift x))(drop z))`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP];
      MATCH_MP_TAC SCHWARTZ_L2 THEN MATCH_MP_TAC ETAP_SCHWARTZ THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `lnorm (:real^1) (&2) (\x. f x - (g:real^1->real^2) x) +
              lnorm (:real^1) (&2) (\x. (g:real^1->real^2) x -
                                        Cx(eta (abs R) (drop x)) * P x)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x. f x - Cx(eta (abs R) (drop x)) * (P:real^1->real^2) x) =
      (\x. (\x. f x - g x) x + (\x. g x - Cx(eta (abs R) (drop x)) * P x) x)`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LNORM_TRIANGLE THEN
    REWRITE_TAC[REAL_ARITH `&1 <= &2`; REAL_ARITH `&0 <= &2`] THEN
    CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_REWRITE_TAC[REAL_ARITH `&0 <= &2`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a < e / &2 /\ b <= e / &2 ==> a + b < e`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. (g:real^1->real^2) x - Cx(eta (abs R) (drop x)) * P x) =
    (\x. Cx(eta (abs R) (drop x)) * ((g:real^1->real^2) x - P x))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB] THEN ASM_REWRITE_TAC[] THEN
      VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm (:real^1) (&2) (\x. Cx(eta (abs R) (drop x)) * ((g:real^1->real^2) x
     - P x)) =
    lnorm s (&2) (\x. Cx(eta (abs R) (drop x)) * ((g:real^1->real^2) x - P x))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC LNORM_SUPPORTED THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
    X_GEN_TAC `x:real^1` THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN DISCH_TAC THEN
    SUBGOAL_THEN `eta (abs R) (drop x) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC ETA_SUPPORT THEN
       REWRITE_TAC[REAL_ABS_POS; NORM_REAL; GSYM drop] THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm s (&2) (\x. (g:real^1->real^2) x - P x)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^1->bool` THEN
  REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY; REAL_ARITH `&0 <= &2`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN
     `(\x:real^1. Cx(eta (abs R) (drop x)) * ((g:real^1->real^2) x - P x)) =
      (\x. g x - Cx(eta (abs R) (drop x)) * P x)`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
      REWRITE_TAC[COMPLEX_SUB_LDISTRIB] THEN ASM_REWRITE_TAC[] THEN
        VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_ARITH `&0 <= &2`];
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_ARITH `&0 <= &2`] THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MP_TAC(SPECL [`abs R`; `drop x`] ETA_BOUNDS) THEN REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* SECTION 11. Plancherel's theorem on L^2 (Fremlin 284O(a)).                *)
(*                                                                           *)
(* Every square-integrable f has a Fourier transform represented by some     *)
(* square-integrable g with ||g||_2 = ||f||_2. The transform is defined as   *)
(* the L^2 limit of                                                          *)
(* the classical transforms of a Schwartz approximating sequence (284N),     *)
(* which is Cauchy by Plancherel-on-Schwartz (PARSEVAL_SCHWARTZ) and hence   *)
(* convergent by completeness of L^2 (RIESZ_FISCHER).                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Schwartz functions form a linear space (closed under +, -, negation):     *)
(* the two derivative chains add termwise and the rapid-decay bounds add.    *)
(* ------------------------------------------------------------------------- *)

let SCHWARTZ_ADD = prove
 (`!h1 h2:real->complex. schwartz h1 /\ schwartz h2 ==> schwartz (\x. h1 x + h2
   x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schwartz] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e:num->real->complex` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\n:num. \x:real. (d:num->real->complex) n x +
    (e:num->real->complex) n x` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM];
    REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
      ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `m:num`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `m:num`]) THEN
    DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN
      DISCH_THEN(X_CHOOSE_TAC `B2:real`) THEN
    EXISTS_TAC `B1 + B2:real` THEN X_GEN_TAC `x:real` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs x pow k * norm((d:num->real->complex) m x) +
                abs x pow k * norm((e:num->real->complex) m x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
        CONV_TAC NORM_ARITH];
      MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[]]]);;

let SCHWARTZ_NEG = prove
 (`!h:real->complex. schwartz h ==> schwartz (\x. --(h x))`,
  GEN_TAC THEN REWRITE_TAC[schwartz] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n:num. \x:real. --((d:num->real->complex) n x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM];
    REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_NEG THEN
      ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `m:num`]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
      REWRITE_TAC[NORM_NEG]]);;

let SCHWARTZ_SUB = prove
 (`!h1 h2:real->complex. schwartz h1 /\ schwartz h2 ==> schwartz (\x. h1 x - h2
   x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `(\x. h1 x - h2 x) = (\x:real. h1 x + (\x. --(h2 x)) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING;
    MATCH_MP_TAC SCHWARTZ_ADD THEN ASM_SIMP_TAC[SCHWARTZ_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* The Fourier transform of a Schwartz function is square-integrable: it is  *)
(* uniformly bounded (FOURIER_BOUND_UNIFORM, from f in L^1) and in L^1       *)
(* (SCHWARTZ_FHAT_ABSINT), so |fhat|^2 <= K|fhat| is integrable. (Avoids the *)
(* full 284C fact that fhat is itself Schwartz.)                             *)
(* ------------------------------------------------------------------------- *)

let SCHWARTZ_FOURIER_L2 = prove
 (`!f:real->complex. schwartz f ==> (\z. fourier f (drop z)) IN lspace
   (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHWARTZ_ABSINT) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `K:real` o MATCH_MP FOURIER_BOUND_UNIFORM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHWARTZ_FHAT_ABSINT) THEN
  SUBGOAL_THEN
    `(\z:real^1. fourier f (drop z)) measurable_on (:real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC FOURIER_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\z:real^1. K % lift(norm(fourier f (drop z)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_RPOW THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    REWRITE_TAC[o_DEF] THEN REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; DROP_CMUL; LIFT_DROP; REAL_ABS_RPOW;
      REAL_ABS_NORM] THEN
    REWRITE_TAC[RPOW_POW] THEN
    SUBGOAL_THEN `norm(fourier f (drop z)) pow 2 =
                  norm(fourier f (drop z)) * norm(fourier f (drop z))`
     SUBST1_TAC THENL [REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Plancherel-on-Schwartz in lnorm form: ||fhat||_2 = ||f||_2. Since         *)
(* lproduct s f f = Cx((lnorm s 2 f) pow 2) (LPRODUCT_SELF_LNORM), this is   *)
(* PARSEVAL_SCHWARTZ (lproduct fhat fhat = lproduct f f) with the two        *)
(* nonnegative L^2 seminorms cancelled.                                      *)
(* ------------------------------------------------------------------------- *)

let PLANCHEREL_LNORM_SCHWARTZ = prove
 (`!h:real->complex. schwartz h
     ==> lnorm (:real^1) (&2) (\z. fourier h (drop z)) =
         lnorm (:real^1) (&2) (\z. h (drop z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z:real^1. (h:real->complex) (drop z)) IN lspace (:real^1) (&2) /\
    (\z:real^1. fourier (h:real->complex) (drop z)) IN lspace (:real^1) (&2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCHWARTZ_L2; SCHWARTZ_FOURIER_L2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[LNORM_POS_LE; ARITH] THEN
  REWRITE_TAC[GSYM CX_INJ] THEN
  ASM_SIMP_TAC[GSYM LPRODUCT_SELF_LNORM] THEN
  REWRITE_TAC[lproduct] THEN
  MATCH_MP_TAC PARSEVAL_SCHWARTZ THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Linearity of the transform on Schwartz functions (both integrands exist). *)
(* ------------------------------------------------------------------------- *)

let SCHWARTZ_MOD_INT = prove
 (`!h:real->complex y. schwartz h
     ==> (\x. cexp(--(ii * Cx y * Cx(drop x))) * h(drop x)) integrable_on
       (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC FOURIER_MODULATION_ABSINT THEN MATCH_MP_TAC SCHWARTZ_ABSINT THEN
  ASM_REWRITE_TAC[]);;

let FOURIER_SUB_SCHWARTZ = prove
 (`!h1 h2:real->complex. schwartz h1 /\ schwartz h2
     ==> !y. fourier (\x. h1 x - h2 x) y = fourier h1 y - fourier h2 y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
    `(\x. h1 x - h2 x) = (\x:real. h1 x + (\x. --Cx(&1) * h2 x) x)` SUBST1_TAC
    THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) FOURIER_ADD o lhs o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SCHWARTZ_MOD_INT THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(\x. cexp(--(ii * Cx y * Cx(drop x))) * (\x. --Cx(&1) * h2 x)(drop x))
         =
        (\x. --Cx(&1) * (\x. cexp(--(ii * Cx y * Cx(drop x))) * h2(drop x)) x)`
       SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC COMPLEX_RING;
        MATCH_MP_TAC INTEGRABLE_COMPLEX_LMUL THEN
        MATCH_MP_TAC SCHWARTZ_MOD_INT THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
    `fourier (\x. --Cx(&1) * h2 x) y = --Cx(&1) * fourier h2 y`
    SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) FOURIER_LMUL o lhs o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SCHWARTZ_MOD_INT THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* 284O(a): Plancherel on all of L^2. Every f in L^2 has a Fourier transform *)
(* represented by g in L^2 with ||g||_2 = ||f||_2. g is the L^2 limit of the *)
(* classical transforms of a Schwartz approximating sequence (284N); the     *)
(* transformed sequence is Cauchy by the Schwartz isometry (PLANCHEREL_DIFF) *)
(* and converges by completeness (RIESZ_FISCHER); norms pass to the limit.   *)
(* ------------------------------------------------------------------------- *)

(* Difference triangle and reverse triangle for the L^2 seminorm.            *)
let LNORM_TRIANGLE_SUB = prove
 (`!s (a:real^M->real^N) b c.
        a IN lspace s (&2) /\ b IN lspace s (&2) /\ c IN lspace s (&2)
        ==> lnorm s (&2) (\x. a x - c x) <=
            lnorm s (&2) (\x. a x - b x) + lnorm s (&2) (\x. b x - c x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (a:real^M->real^N) x - c x) =
                (\x. (\x. a x - b x) x + (\x. b x - c x) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC LNORM_TRIANGLE THEN REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN
    CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_REWRITE_TAC[REAL_ARITH `&0 <= &2`]]);;

let LNORM_REV = prove
 (`!s (a:real^M->real^N) b.
        a IN lspace s (&2) /\ b IN lspace s (&2)
        ==> abs(lnorm s (&2) a - lnorm s (&2) b) <= lnorm s (&2) (\x. a x - b
          x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `lnorm s (&2) (a:real^M->real^N) <= lnorm s (&2) b + lnorm s (&2) (\x. a x
    - b x) /\
                lnorm s (&2) (b:real^M->real^N) <= lnorm s (&2) a + lnorm s
                  (&2) (\x. a x - b x)`
   MP_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^M->bool`; `&2`; `b:real^M->real^N`;
       `\x. (a:real^M->real^N) x - b x`]
        LNORM_TRIANGLE) THEN
      ASM_SIMP_TAC[REAL_ARITH `&1 <= &2`; LSPACE_SUB;
        REAL_ARITH `&0 <= &2`] THEN
      MATCH_MP_TAC(REAL_ARITH `l = m ==> m <= r ==> l <= r`) THEN
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
      MP_TAC(ISPECL [`s:real^M->bool`; `&2`; `a:real^M->real^N`;
        `\x. (b:real^M->real^N) x - a x`]
        LNORM_TRIANGLE) THEN
      ASM_SIMP_TAC[REAL_ARITH `&1 <= &2`; LSPACE_SUB;
        REAL_ARITH `&0 <= &2`] THEN
      SUBGOAL_THEN `lnorm s (&2) (\x. (b:real^M->real^N) x - a x) =
                    lnorm s (&2) (\x. a x - b x)` SUBST1_TAC THENL
       [REWRITE_TAC[LNORM_SUB_SYM]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `l = m ==> m <= r ==> l <= r`) THEN
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* Isometry on differences of Schwartz functions.                            *)
let PLANCHEREL_DIFF = prove
 (`!a b:real->complex. schwartz a /\ schwartz b
     ==> lnorm (:real^1) (&2) (\z. fourier a (drop z) - fourier b (drop z)) =
         lnorm (:real^1) (&2) (\z. a (drop z) - b (drop z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real->complex`;
    `b:real->complex`] FOURIER_SUB_SCHWARTZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. fourier a (drop z) - fourier b (drop z)) =
    (\z. fourier (\x. a x - b x) (drop z))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `\x. (a:real->complex) x - b x` PLANCHEREL_LNORM_SCHWARTZ)
      THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SCHWARTZ_SUB THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]]);;

(* A Schwartz sequence approximating f in L^2 at rate inv(n+1).              *)
let SCHWARTZ_SEQ = prove
 (`!f:real^1->real^2. f IN lspace (:real^1) (&2)
     ==> ?fn:num->real->complex.
           (!n. schwartz (fn n)) /\
           (!n. lnorm (:real^1) (&2) (\z. f z - fn n (drop z)) < inv(&n +
             &1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LSPACE_APPROXIMATE_SCHWARTZ) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ] THEN
  SIMP_TAC[REAL_ARITH `&0 <= &n ==> &0 < &n + &1`; REAL_POS] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `fn:num->real->complex` THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let ABS_EPS_EQ = prove
 (`!a b:real. (!e. &0 < e ==> abs(a - b) < e) ==> a = b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(a - b)) ==> a = b`) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `abs(a - b:real)`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* If gn ---> g in L^2 norm and ||gn n|| ---> c, then ||g|| = c.             *)
(* The L^2 norm is continuous along L^2-convergent sequences (reverse        *)
(* triangle inequality LNORM_REV), so its limit is unique.                   *)
(* ------------------------------------------------------------------------- *)

let L2LIM_NORM = prove
 (`!(gn:num->real^1->complex) g c.
     (!n. gn n IN lspace (:real^1) (&2)) /\ g IN lspace (:real^1) (&2) /\
     (!e. &0 < e ==> ?N. !n. n >= N
          ==> lnorm (:real^1) (&2) (\x. gn n x - g x) < e) /\
     ((\n. lnorm (:real^1) (&2) (gn n)) ---> c) sequentially
     ==> lnorm (:real^1) (&2) g = c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\n. lnorm (:real^1) (&2) ((gn:num->real^1->complex) n))
     ---> lnorm (:real^1) (&2) (g:real^1->complex)) sequentially`
   ASSUME_TAC THENL
   [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lnorm (:real^1) (&2) (\x. (gn:num->real^1->complex) n x - g x)`
      THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^1)`; `(gn:num->real^1->complex) n`;
       `g:real^1->complex`]
        LNORM_REV) THEN ASM_REWRITE_TAC[REAL_ABS_SUB];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`sequentially`;
    `\n. lnorm (:real^1) (&2) ((gn:num->real^1->complex) n)`;
    `lnorm (:real^1) (&2) (g:real^1->complex)`; `c:real`] REALLIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 284O(b): bilinear Parseval on Schwartz functions.                         *)
(*   <f, g> = <fhat, ghat>,  i.e.  INT f * cnj g = INT fhat * cnj ghat.      *)
(* Generalises PARSEVAL_SCHWARTZ (the f = g diagonal) by the same route:     *)
(* the multiplication formula 283O on (fhat, x |-> cnj(g(-x))), the          *)
(* conjugate                                                                 *)
(* -reflection bridge, and the double-transform reflection.  Gives the       *)
(* orthogonality of transforms with disjoint frequency support.             *)
(* ------------------------------------------------------------------------- *)

let PARSEVAL_SCHWARTZ_BILINEAR = prove
 (`!(f:real->complex) (g:real->complex). schwartz f /\ schwartz g
     ==> integral (:real^1) (\z. f(drop z) * cnj(g(drop z))) =
         integral (:real^1) (\z. fourier f (drop z) * cnj(fourier g (drop
           z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHWARTZ_ABSINT o
    check(fun th -> concl th = `schwartz(g:real->complex)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHWARTZ_FHAT_ABSINT o
    check(fun th -> concl th = `schwartz(f:real->complex)`)) THEN
  MP_TAC(ISPECL [`fourier(f:real->complex)`;
    `\x. cnj((g:real->complex)(--x))`] FOURIER_283O) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CNJ_REFLECT_ABSINT THEN
     ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\z. fourier f (drop z) * fourier (\x.
     cnj((g:real->complex)(--x))) (drop z)) =
    integral (:real^1) (\z. fourier f (drop z) * cnj(fourier g (drop z)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC FOURIER_CNJ_REFLECT THEN MATCH_MP_TAC MODINT THEN
      ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\z. fourier (fourier f) (drop z) * (\x.
     cnj((g:real->complex)(--x))) (drop z)) =
    integral (:real^1) (\z. f(--(drop z)) * cnj(g(--(drop z))))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_NEG_NEG] THEN
      ASM_SIMP_TAC[DOUBLE_TRANSFORM; REAL_NEG_NEG];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPEC `\t. (f:real->complex) t * cnj(g t)` INTEGRAL_REFLECT_R) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;


(* ========================================================================= *)
(* SECTION 12. Schwartz calculus continued (Fremlin 284C).                   *)
(*                                                                           *)
(* Schwartz functions are closed under                                      *)
(* differentiation (SCHWARTZ_DERIV), multiplication by x (SCHWARTZ_MUL_X),   *)
(* affine reparametrisation and modulation (SCHWARTZ_AFFINE / _CMUL /        *)
(* _MODULATE / _MODAFFINE), and -- the payoff -- under the Fourier transform *)
(* itself (SCHWARTZ_FOURIER, Fremlin 284C).  Also the L^2 Fourier            *)
(* representative FOURIER_L2_REP and bilinear-Parseval orthogonality of      *)
(* disjoint-frequency-support transforms.                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Schwartz closure under differentiation (via chain-shift).                 *)
(* ------------------------------------------------------------------------- *)

(* Every function in a Schwartz derivative-chain is itself Schwartz.         *)
let SCHWARTZ_CHAIN_ALL = prove
 (`!h:real->complex. schwartz h
     ==> ?d. d 0 = h /\ (!n. schwartz (d n)) /\
             (!n x. ((\z. d n(drop z)) has_vector_derivative d(SUC n)
               x)(at(lift x)))`,
  GEN_TAC THEN REWRITE_TAC[schwartz] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:num->real->complex` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN
  EXISTS_TAC `\j. (d:num->real->complex)(n + j)` THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ADD_SUC] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `n + m:num`]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[]]);;

let SCHWARTZ_DERIV = prove
 (`!h h':real->complex.
     schwartz h /\ (!x. ((\z. h(drop z)) has_vector_derivative h' x)(at(lift
       x)))
     ==> schwartz h'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC o
    MATCH_MP SCHWARTZ_CHAIN_ALL) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
    `!x. ((\z. (d:num->real->complex) 0 (drop z)) has_vector_derivative d 1
    x)(at(lift x))`
   ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `x:real`]) THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`]; ALL_TAC] THEN
  SUBGOAL_THEN `h' = (d:num->real->complex) 1` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [`\z. (d:num->real->complex) 0 (drop z)`;
      `lift x`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The smooth plateau psi0 = rtheta(11-60x) rtheta(11+60x):                  *)
(*   = 1 on [-1/6,1/6], supported in [-1/5,1/5], values in [0,1], even.      *)
(* ------------------------------------------------------------------------- *)

let MULX_DERIV_STEP = prove
 (`!(a:real->complex) a' x.
     ((\z. a(drop z)) has_vector_derivative a') (at(lift x))
     ==> ((\z. Cx(drop z) * a(drop z)) has_vector_derivative
          (a x + Cx x * a')) (at(lift x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`( * ):complex->complex->complex`;
    `\z:real^1. Cx(drop z)`; `\z:real^1. (a:real->complex)(drop z)`;
    `Cx(&1)`; `a':complex`; `lift x`]
   HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL; LIFT_DROP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\t:real. t`; `&1`; `x:real`] CX_VECTOR_DERIV_BRIDGE) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; ETA_AX] THEN REWRITE_TAC[LIFT_DROP];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC VDERIV_EQ THEN
    CONV_TAC COMPLEX_RING]);;

(* Schwartz closed under multiplication by x: the chain for x*h is           *)
(*   e m x = x (d m x) + m (d(m-1) x)   (d = h's chain);  e 0 = x h.         *)
(* MULX_CHAIN_DERIV gives its derivative relation, and the decay bounds add. *)
let CMUL_PRED_DERIV = prove
 (`!(d:num->real->complex) m x.
     ~(m = 0) /\
     (!n x. ((\z. d n(drop z)) has_vector_derivative d(SUC n) x)(at(lift x)))
     ==> ((\z. Cx(&m) * d(m-1)(drop z)) has_vector_derivative Cx(&m) * d m
       x)(at(lift x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d:num->real->complex) m = d(SUC(m-1))` ASSUME_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONST_CHAIN_DERIV THEN
  ASM_REWRITE_TAC[]);;

let MULX_CHAIN_DERIV = prove
 (`!(d:num->real->complex).
     (!n x. ((\z. d n(drop z)) has_vector_derivative d(SUC n) x)(at(lift x)))
     ==> !m x. ((\z. Cx(drop z) * d m (drop z) + Cx(&m) * d(m-1)(drop z))
                has_vector_derivative
                (Cx x * d(SUC m) x + Cx(&(SUC m)) * d((SUC m)-1) x))(at(lift
                  x))`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN X_GEN_TAC `x:real` THEN
  REWRITE_TAC[SUC_SUB1] THEN
  SUBGOAL_THEN
   `Cx x * d(SUC m) x + Cx(&(SUC m)) * (d:num->real->complex) m x =
    ((d:num->real->complex) m x + Cx x * d(SUC m) x) + Cx(&m) * d m x`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD] THEN
     CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC MULX_DERIV_STEP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_VECTOR_DERIVATIVE_CONST];
    MATCH_MP_TAC CMUL_PRED_DERIV THEN ASM_REWRITE_TAC[]]);;

let SCHWARTZ_MUL_X = prove
 (`!h:real->complex. schwartz h ==> schwartz (\x. Cx x * h x)`,
  GEN_TAC THEN REWRITE_TAC[schwartz] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\m. \x. Cx x * (d:num->real->complex) m x + Cx(&m) * d(m-1) x`
    THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MULX_CHAIN_DERIV THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN
    FIRST_ASSUM(X_CHOOSE_TAC `B1:real` o SPECL [`SUC k`; `m:num`]) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `B2:real` o SPECL [`k:num`; `m - 1`]) THEN
    EXISTS_TAC `B1 + &m * B2:real` THEN X_GEN_TAC `x:real` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs x pow k * (abs x * norm((d:num->real->complex) m x) +
                               &m * norm(d(m-1) x))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`abs x pow k`;
        `norm(Cx x * (d:num->real->complex) m x + Cx(&m) * d(m-1) x)`;
        `abs x * norm((d:num->real->complex) m x) + &m * norm(d(m-1) x)`]
        REAL_LE_LMUL) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm(Cx x * (d:num->real->complex) m x) + norm(Cx(&m) *
          d(m-1) x)` THEN
        REWRITE_TAC[NORM_TRIANGLE; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
          REAL_ABS_NUM;
                    REAL_LE_REFL]];
      REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
        CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs x pow (SUC k) * norm((d:num->real->complex) m x)` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[real_pow] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
           CONV_TAC REAL_RING;
          ASM_REWRITE_TAC[]];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&m * (abs x pow k * norm((d:num->real->complex)(m-1) x))`
          THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Toward 284C, smoothness half: fourier g has a smooth derivative chain     *)
(* when                                                                      *)
(* g is Schwartz.  d/dy (fourier g) = -i fourier(x g) (283Ch, all conditions *)
(* automatic for Schwartz), iterated: (fourier g)^(m) = (-i)^m fourier(x^m   *)
(* g).                                                                       *)
(* ------------------------------------------------------------------------- *)

let FOURIER_SCHWARTZ_DERIV = prove
 (`!g:real->complex y0. schwartz g
     ==> ((\z. fourier g (drop z)) has_vector_derivative
          (--ii * fourier (\x. Cx x * g x) y0)) (at(lift y0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FOURIER_283CH THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FOURIER_MODULATION_ABSINT THEN
    MATCH_MP_TAC SCHWARTZ_ABSINT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `g:real->complex` SCHWARTZ_MUL_X) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SCHWARTZ_ABSINT) THEN REWRITE_TAC[]]);;

(* Transform of the derivative (the dual of FOURIER_SCHWARTZ_DERIV): for a   *)
(* Schwartz h with derivative h', (h')^(y) = iy . h^(y). All the side        *)
(* conditions of FOURIER_283CI are discharged from schwartz-ness (h' is      *)
(* again                                                                     *)
(* Schwartz by SCHWARTZ_DERIV; decay by SCHWARTZ_TENDSTO_*; modulated        *)
(* integrability by FOURIER_MODULATION_ABSINT o SCHWARTZ_ABSINT).            *)
let FOURIER_SCHWARTZ_DIFF = prove
 (`!(h:real->complex) h' y. schwartz h /\
     (!x. ((\z. h(drop z)) has_vector_derivative (h' x)) (at(lift x)))
     ==> fourier h' y = (ii * Cx y) * fourier h y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FOURIER_283CI THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `schwartz (h':real->complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHWARTZ_DERIV THEN EXISTS_TAC `h:real->complex` THEN
     ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCHWARTZ_TENDSTO_POS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCHWARTZ_TENDSTO_NEG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FOURIER_MODULATION_ABSINT THEN
      MATCH_MP_TAC SCHWARTZ_ABSINT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FOURIER_MODULATION_ABSINT THEN
      MATCH_MP_TAC SCHWARTZ_ABSINT THEN ASM_REWRITE_TAC[]]);;

(* The Schwartz sequence gg n = x^n g (all Schwartz).                        *)
let XPOW_SCHWARTZ_SEQ = prove
 (`!g:real->complex. schwartz g
     ==> ?gg. gg 0 = g /\ (!n. schwartz(gg n)) /\
              (!n. gg(SUC n) = (\t. Cx t * gg n t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\(n:num) (f:real->complex). schwartz f`;
    `\(n:num) (f:real->complex) (f':real->complex). f' = (\t. Cx t * f t)`;
    `g:real->complex`] DEPENDENT_CHOICE_FIXED) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `f:real->complex` THEN DISCH_TAC THEN
    EXISTS_TAC `\t. Cx t * (f:real->complex) t` THEN
    ASM_SIMP_TAC[SCHWARTZ_MUL_X];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `gg:num->real->complex` THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* fourier g has a full smooth chain (each term (-i)^n fourier(x^n g)).      *)
let FOURIER_SCHWARTZ_CHAIN = prove
 (`!g:real->complex. schwartz g
     ==> ?D. D 0 = (\y. fourier g y) /\
             (!n y. ((\z. D n (drop z)) has_vector_derivative D(SUC n)
               y)(at(lift y)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gg:num->real->complex` STRIP_ASSUME_TAC o
    MATCH_MP XPOW_SCHWARTZ_SEQ) THEN
  EXISTS_TAC `\n. \y. (--ii) pow n * fourier ((gg:num->real->complex) n) y`
    THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[complex_pow; COMPLEX_MUL_LID] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `(--ii) pow SUC n * fourier ((gg:num->real->complex)(SUC n)) y =
      (--ii) pow n * (--ii * fourier (\t. Cx t * gg n t) y)`
     SUBST1_TAC THENL
     [ASM_REWRITE_TAC[complex_pow] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    MATCH_MP_TAC CONST_CHAIN_DERIV THEN
    MP_TAC(ISPECL [`(gg:num->real->complex) n`;
      `y:real`] FOURIER_SCHWARTZ_DERIV) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Toward 284C, decay half: a Schwartz function vanishes at infinity         *)
(* (needed to apply 283Ci -- differentiation under the transform).           *)
(* ------------------------------------------------------------------------- *)

let INV_ABS_LIM = prove
 (`((\x:real. inv(abs x)) ---> &0) at_posinfinity`,
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN
  EXISTS_TAC `inv e + &1:real` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < x /\ inv e < x` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `e:real` REAL_LT_INV) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_SUB_RZERO;
    REAL_ABS_INV] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_INV]);;

let BINV_LIFT_LIM = prove
 (`!B. ((\x. lift(B * inv(abs x))) --> vec 0) at_posinfinity`,
  GEN_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  SUBST1_TAC(VECTOR_ARITH `vec 0:real^1 = B % vec 0`) THEN
  MATCH_MP_TAC LIM_CMUL THEN
  MP_TAC INV_ABS_LIM THEN REWRITE_TAC[REAL_TENDSTO] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; DROP_VEC]);;

let SCHWARTZ_VANISH = prove
 (`!h:real->complex. schwartz h ==> (h --> vec 0) at_posinfinity`,
  GEN_TAC THEN REWRITE_TAC[schwartz] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o SPECL [`1`; `0`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_1]) THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\x. B * inv(abs x)` THEN REWRITE_TAC[BINV_LIFT_LIM] THEN
  REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN EXISTS_TAC `&1` THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC);;

(* Schwartz closed under reflection; reflected vanishing; the                *)
(* y-multiplication                                                          *)
(* identity iy fourier(h) = fourier(h') (283Ci for Schwartz, all conditions  *)
(* automatic). Iterating this brings down y^k, bounding |y|^k norm(fourier   *)
(* h).                                                                       *)
let SCHWARTZ_REFLECT = prove
 (`!h:real->complex. schwartz h ==> schwartz (\x. h(--x))`,
  GEN_TAC THEN REWRITE_TAC[schwartz] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n:num. \x. Cx(-- &1) pow n * (d:num->real->complex) n (&0 + --
    &1 * x)` THEN
  REWRITE_TAC[complex_pow; COMPLEX_MUL_LID] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `&0 + -- &1 * x = --x`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM complex_pow] THEN
    MP_TAC(ISPECL [`d:num->real->complex`; `&0`; `-- &1`] AFFINE_CHAIN) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN
    REWRITE_TAC[REAL_ARITH `&0 + -- &1 * x = --x`] THEN
    FIRST_ASSUM(X_CHOOSE_TAC `B:real` o SPECL [`k:num`; `m:num`]) THEN
    EXISTS_TAC `B:real` THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `abs x = abs(--x)`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--x:real`) THEN REWRITE_TAC[REAL_ABS_NEG]]);;

let SCHWARTZ_VANISH_NEG = prove
 (`!h:real->complex. schwartz h ==> ((\a. h(--a)) --> vec 0) at_posinfinity`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. (h:real->complex)(--x)` SCHWARTZ_VANISH) THEN
  ASM_SIMP_TAC[SCHWARTZ_REFLECT]);;

let SCHWARTZ_MOD_ABSINT = prove
 (`!h:real->complex y. schwartz h
     ==> (\x. cexp(--(ii * Cx y * Cx(drop x))) * h(drop x))
       absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FOURIER_MODULATION_ABSINT THEN
  MATCH_MP_TAC SCHWARTZ_ABSINT THEN ASM_REWRITE_TAC[]);;

(* y-uniform form (one hp = h' for all y).                                   *)
let FOURIER_SCHWARTZ_YMUL_U = prove
 (`!h:real->complex. schwartz h
     ==> ?hp. schwartz hp /\ !y. fourier hp y = (ii * Cx y) * fourier h y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC o
    MATCH_MP SCHWARTZ_CHAIN_ALL) THEN
  EXISTS_TAC `(d:num->real->complex) 1` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:real` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `(d:num->real->complex) 0 = h` then
                            SUBST1_TAC(SYM th) else NO_TAC) THEN
  MATCH_MP_TAC FOURIER_283CI THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `x:real`]) THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`];
    MATCH_MP_TAC SCHWARTZ_VANISH THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCHWARTZ_VANISH_NEG THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCHWARTZ_MOD_ABSINT THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCHWARTZ_MOD_ABSINT THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[]]);;

(* Decay: |y|^k norm(fourier h y) is bounded, for every k (iterate the       *)
(* y-multiplication identity; base case = FOURIER_BOUND_UNIFORM).            *)
let FOURIER_SCHWARTZ_YPOW_BOUND = prove
 (`!k. !h:real->complex. schwartz h
       ==> ?B. !y. abs y pow k * norm(fourier h y) <= B`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SCHWARTZ_ABSINT) THEN
    DISCH_THEN(MP_TAC o MATCH_MP FOURIER_BOUND_UNIFORM) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `hp:real->complex` STRIP_ASSUME_TAC o
      MATCH_MP FOURIER_SCHWARTZ_YMUL_U) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `hp:real->complex`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real` THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= B ==> a <= B`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC]);;

(* Fremlin 284C(a): the Fourier transform of a Schwartz function is          *)
(* Schwartz.                                                                 *)
let SCHWARTZ_FOURIER = prove
 (`!g:real->complex. schwartz g ==> schwartz (fourier g)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gg:num->real->complex` STRIP_ASSUME_TAC o
    MATCH_MP XPOW_SCHWARTZ_SEQ) THEN
  REWRITE_TAC[schwartz] THEN
  EXISTS_TAC `\n. \y. (--ii) pow n * fourier ((gg:num->real->complex) n) y`
    THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[complex_pow; COMPLEX_MUL_LID; FUN_EQ_THM] THEN
     ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `(--ii) pow SUC n * fourier ((gg:num->real->complex)(SUC n)) x =
      (--ii) pow n * (--ii * fourier (\t. Cx t * gg n t) x)`
     SUBST1_TAC THENL
     [ASM_REWRITE_TAC[complex_pow] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    MATCH_MP_TAC CONST_CHAIN_DERIV THEN
    MP_TAC(ISPECL [`(gg:num->real->complex) n`;
      `x:real`] FOURIER_SCHWARTZ_DERIV) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN
    MP_TAC(ISPECL [`k:num`;
      `(gg:num->real->complex) m`] FOURIER_SCHWARTZ_YPOW_BOUND) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `B:real` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; NORM_NEG;
      COMPLEX_NORM_II] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* Fremlin 284O(a): every square-integrable f has a Fourier transform        *)
(* REPRESENTED by a square-integrable g (in the tempered/distributional      *)
(* sense                                                                     *)
(* of 284H: INT g*h = INT f*fourier h for every Schwartz h), with            *)
(* ||g||_2 = ||f||_2. The "represents" relation (not just the norm identity) *)
(* is what lets one identify g's own Fourier transform with f (284Ib).       *)
(*                                                                           *)
(* Proof (Fremlin's): fn Schwartz with ||f-fn||->0 (SCHWARTZ_SEQ); the       *)
(* transforms gn = fourier(fn) are L^2-Cauchy (PLANCHEREL_DIFF) so converge  *)
(* to some g (RIESZ_FISCHER) with ||g||=lim||gn||=lim||fn||=||f||            *)
(* (L2LIM_NORM).                                                             *)
(* For the represents clause, INT gn*h = INT fn*fourier h for each n (283O), *)
(* and both sides converge (LPRODUCT_L2LIM: gn->g and fn->f in L^2, h and    *)
(* fourier h being fixed L^2 functions), so INT g*h = INT f*fourier h.       *)
(* ------------------------------------------------------------------------- *)

let FOURIER_L2_REP = prove
 (`!f:real^1->complex. f IN lspace (:real^1) (&2)
     ==> ?g:real^1->complex. g IN lspace (:real^1) (&2) /\
             lnorm (:real^1) (&2) g = lnorm (:real^1) (&2) f /\
             (!h. schwartz h
                  ==> integral (:real^1) (\z. g z * h(drop z)) =
                      integral (:real^1) (\z. f z * fourier h (drop z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `fn:num->real->complex` STRIP_ASSUME_TAC o
    MATCH_MP SCHWARTZ_SEQ) THEN
  ABBREV_TAC `gn = \n. \z:real^1. fourier ((fn:num->real->complex) n) (drop z)`
    THEN
  SUBGOAL_THEN
    `!n. (gn:num->real^1->complex) n IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SCHWARTZ_FOURIER_L2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!n. (\z:real^1. (fn:num->real->complex) n (drop z))
         IN lspace (:real^1) (&2)`
   ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SCHWARTZ_L2 THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* fn ---> f mode (from SCHWARTZ_SEQ inv-bound)                            *)
  SUBGOAL_THEN
   `!e. &0 < e ==> ?N. !n. n >= N
        ==> lnorm (:real^1) (&2) (\z. (fn:num->real->complex) n (drop z) - f z)
          < e`
   (LABEL_TAC "FNCONV") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `lnorm (:real^1) (&2) (\z. (fn:num->real->complex) n (drop z) - f z) =
                  lnorm (:real^1) (&2) (\z. f z - fn n (drop z))` SUBST1_TAC
                    THENL
     [REWRITE_TAC[LNORM_SUB_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE[GE; GSYM REAL_OF_NUM_LE]) THEN
          ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* gn Cauchy in L2 (via PLANCHEREL_DIFF)                                   *)
  SUBGOAL_THEN
   `!m n. lnorm (:real^1) (&2) (\z. (gn:num->real^1->complex) m z - gn n z) =
          lnorm (:real^1) (&2) (\z. (fn:num->real->complex) m (drop z) - fn n
            (drop z))`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PLANCHEREL_DIFF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e ==> ?N. !m n. m >= N /\ n >= N
        ==> lnorm (:real^1) (&2) (\z. (gn:num->real^1->complex) m z - gn n z) <
          e`
   ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lnorm (:real^1) (&2) (\z. (fn:num->real->complex) m (drop z) -
      f z) +
                lnorm (:real^1) (&2) (\z. f z - fn n (drop z))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_TRIANGLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e / &2 + e / &2` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `lnorm (:real^1) (&2) (\z. (fn:num->real->complex) m (drop z) - f z) =
                    lnorm (:real^1) (&2) (\z. f z - fn m (drop z))` SUBST1_TAC
                      THENL
       [REWRITE_TAC[LNORM_SUB_SYM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&m + &1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&N)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
          RULE_ASSUM_TAC(REWRITE_RULE[GE; GSYM REAL_OF_NUM_LE]) THEN
          ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&N)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
          RULE_ASSUM_TAC(REWRITE_RULE[GE; GSYM REAL_OF_NUM_LE]) THEN
          ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gn:num->real^1->complex`; `&2`;
    `(:real^1)`] RIESZ_FISCHER) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RCONV"))) THEN
  EXISTS_TAC `g:real^1->complex` THEN ASM_REWRITE_TAC[] THEN
  (* per-index Plancherel norm ||gn n|| = ||fn n||                           *)
  SUBGOAL_THEN
   `!n. lnorm (:real^1) (&2) ((gn:num->real^1->complex) n) =
        lnorm (:real^1) (&2) (\z. (fn:num->real->complex) n (drop z))`
   (LABEL_TAC "PNORM") THENL
   [GEN_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PLANCHEREL_LNORM_SCHWARTZ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* ||fn n|| ---> ||f|| (from FNCONV via L2LIM_NORM), hence ||gn n|| --->   *)
  (* ||f||                                                                   *)
  SUBGOAL_THEN
   `((\n. lnorm (:real^1) (&2) ((gn:num->real^1->complex) n))
     ---> lnorm (:real^1) (&2) (f:real^1->complex)) sequentially`
   (LABEL_TAC "GNORMLIM") THENL
   [SUBGOAL_THEN
     `(\n. lnorm (:real^1) (&2) ((gn:num->real^1->complex) n)) =
      (\n. lnorm (:real^1) (&2) (\z. (fn:num->real->complex) n (drop z)))`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      USE_THEN "PNORM" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "FNCONV" (MP_TAC o SPEC `e:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lnorm (:real^1) (&2)
      (\z. (\z:real^1. (fn:num->real->complex) n (drop z)) z - f z)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^1)`;
       `\z:real^1. (fn:num->real->complex) n (drop z)`;
        `f:real^1->complex`] LNORM_REV) THEN ASM_REWRITE_TAC[REAL_ABS_SUB];
      REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GE]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* NORM EQUALITY via L2LIM_NORM                                          *)
    MATCH_MP_TAC L2LIM_NORM THEN
    EXISTS_TAC `gn:num->real^1->complex` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "RCONV" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* THE REPRESENTS PROPERTY                                                 *)
  X_GEN_TAC `h:real->complex` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. integral (:real^1) (\z. (gn:num->real^1->complex) n z *
    h(drop z))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [(* LHS: int gn*h ---> int g*h, via gn ---> g                             *)
    SUBGOAL_THEN
      `(\z:real^1. cnj(h(drop z))) IN lspace (:real^1) (&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC LSPACE_CNJ THEN MATCH_MP_TAC SCHWARTZ_L2 THEN
      ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!a:real^1->complex. integral (:real^1) (\z. a z * h(drop z)) =
                          lproduct (:real^1) a (\z. cnj(h(drop z)))`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[lproduct; CNJ_CNJ]; ALL_TAC] THEN
    MATCH_MP_TAC LPRODUCT_L2LIM THEN ASM_REWRITE_TAC[ETA_AX] THEN
    USE_THEN "RCONV" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* the sequence int gn*h EQUALS int fn*fhat (per n), which ---> int f*fhat *)
  SUBGOAL_THEN
   `!n. integral (:real^1) (\z. (gn:num->real^1->complex) n z * h(drop z)) =
        integral (:real^1) (\z. (fn:num->real->complex) n (drop z) * fourier h
          (drop z))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "gn" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(fn:num->real->complex) n`;
      `h:real->complex`] FOURIER_283O) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SCHWARTZ_ABSINT THEN ASM_REWRITE_TAC[ETA_AX];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC];
    ALL_TAC] THEN
  (* RHS: int fn*fhat ---> int f*fhat, via fn ---> f, with fixed fourier h   *)
  (* (Schwartz)                                                              *)
  SUBGOAL_THEN `schwartz (fourier h)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHWARTZ_FOURIER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\z:real^1. cnj(fourier h (drop z))) IN lspace (:real^1) (&2)` ASSUME_TAC
    THENL
   [MATCH_MP_TAC LSPACE_CNJ THEN MATCH_MP_TAC SCHWARTZ_L2 THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\n. integral (:real^1) (\z. (fn:num->real->complex) n (drop z) * fourier h
     (drop z))) =
    (\n. lproduct (:real^1) (\z. (fn:num->real->complex) n (drop z))
                            (\z. cnj(fourier h (drop z))))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[lproduct; CNJ_CNJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\z. f z * fourier h (drop z)) =
    lproduct (:real^1) (f:real^1->complex) (\z. cnj(fourier h (drop z)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[lproduct; CNJ_CNJ]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n. \z:real^1. (fn:num->real->complex) n (drop z)`;
    `f:real^1->complex`; `\z:real^1. cnj(fourier h (drop z))`;
    `(:real^1)`] LPRODUCT_L2LIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  USE_THEN "FNCONV" (fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* Change-of-variable helpers: an invertible affine map is a bijection of R, *)
(* so integral/integrability transfer under dilation and shift.              *)
(* ------------------------------------------------------------------------- *)

let AFFINE_IMAGE_UNIV = prove
 (`!c:real b:real^1. ~(c = &0)
     ==> IMAGE (\x. inv c % x + --(inv c % b)) (:real^1) = (:real^1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `x:real^1` THEN EXISTS_TAC `c % x + b:real^1` THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

(* Dilation change-of-variables on the whole line (from                      *)
(* HAS_INTEGRAL_AFFINITY): INT ff(c x + b) = (1/|c|) INT ff, and ff(c.+b)    *)
(* stays integrable.                                                         *)
let INTEGRAL_DILATE_UNIV = prove
 (`!(ff:real^1->real^N) c b. ~(c = &0) /\ ff integrable_on (:real^1)
     ==> integral (:real^1) (\x. ff(c % x + b)) = inv(abs c) % integral
       (:real^1) ff`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ff:real^1->real^N`; `integral (:real^1) (ff:real^1->real^N)`;
                 `(:real^1)`; `c:real`; `b:real^1`] HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[INTEGRABLE_INTEGRAL; AFFINE_IMAGE_UNIV; DIMINDEX_1;
    REAL_POW_1] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REFL_TAC);;

let INTEGRABLE_DILATE_UNIV = prove
 (`!(ff:real^1->real^N) c b. ~(c = &0) /\ ff integrable_on (:real^1)
     ==> (\x. ff(c % x + b)) integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ff:real^1->real^N`; `integral (:real^1) (ff:real^1->real^N)`;
                 `(:real^1)`; `c:real`; `b:real^1`] HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[INTEGRABLE_INTEGRAL; AFFINE_IMAGE_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN REWRITE_TAC[]);;

(* Polynomial-moment bounds for an affine reparametrisation, feeding         *)
(* SCHWARTZ_AFFINE: |x|^k is dominated by a constant times max(1,|x|)^k,     *)
(* which expands through (c + s x) by the binomial-type bound below.         *)
let MAXPOW_LE = prove
 (`!C t k. &0 <= C /\ &0 <= t ==> (max C t) pow k <= C pow k + t pow k`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `t <= C \/ C <= t`) THENL
   [ASM_SIMP_TAC[REAL_ARITH `t <= C ==> max C t = C`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_ARITH `C <= t ==> max C t = t`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> y <= x + y`) THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]]);;

let POW_ADD_2BOUND = prove
 (`!C t k. &0 <= C /\ &0 <= t
     ==> (C + t) pow k <= &2 pow k * (C pow k + t pow k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * max C t) pow k` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_MUL] THEN
    MP_TAC(SPECL [`C:real`; `t:real`; `k:num`] MAXPOW_LE) THEN
      ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`&2 pow k`; `(max C t) pow k`; `(C:real) pow k + t pow k`]
       REAL_LE_LMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      REWRITE_TAC[]]]);;

let AFFINE_XPOW_BOUND = prove
 (`!s c k x. ~(s = &0)
     ==> abs x pow k <= inv(abs s pow k) * (&2 pow k * (abs(c + s * x) pow k +
       abs c pow k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs x = inv(abs s) * abs((c + s * x) - c)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_INV; GSYM REAL_ABS_MUL] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(s = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; GSYM REAL_POW_INV] THEN
  MP_TAC(ISPECL [`inv(abs s) pow k`; `abs((c + s * x) - c) pow k`;
                 `&2 pow k * (abs(c + s * x) pow k + abs c pow k)`]
                   REAL_LE_LMUL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(abs(c + s * x) + abs c) pow k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
         REAL_ARITH_TAC;
        MATCH_MP_TAC POW_ADD_2BOUND THEN REWRITE_TAC[REAL_ABS_POS]]];
    REWRITE_TAC[]]);;

let AFFINE_WEIGHT_BOUND = prove
 (`!s c k x N B0 Bk.
     ~(s = &0) /\ &0 <= N /\
     abs(c + s * x) pow k * N <= Bk /\ N <= B0
     ==> abs x pow k * N <=
         inv(abs s pow k) * (&2 pow k * (Bk + abs c pow k * B0))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(inv(abs s pow k) * (&2 pow k * (abs(c + s * x) pow k + abs c pow
    k))) * N` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`abs x pow k`;
      `inv(abs s pow k) * (&2 pow k * (abs(c + s * x) pow k + abs c pow k))`;
        `N:real`]
      REAL_LE_RMUL) THEN
    ASM_SIMP_TAC[AFFINE_XPOW_BOUND];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MP_TAC(ISPECL [`inv(abs s pow k)`;
      `&2 pow k * (abs(c + s * x) pow k + abs c pow k) * N`;
      `&2 pow k * (Bk + abs c pow k * B0)`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
        REWRITE_TAC[REAL_ABS_POS];
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
        MP_TAC(ISPECL [`&2 pow k`;
          `(abs(c + s * x) pow k + abs c pow k) * N`; `Bk + abs c pow k * B0`]
          REAL_LE_LMUL) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
            REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
            MP_TAC(ISPECL [`abs c pow k`; `N:real`;
              `B0:real`] REAL_LE_LMUL) THEN
            ASM_SIMP_TAC[REAL_POW_LE; REAL_ABS_POS]];
          REWRITE_TAC[]]];
      REWRITE_TAC[]]]);;

let SCHWARTZ_AFFINE = prove
 (`!phi:real->complex s c. schwartz phi /\ ~(s = &0)
     ==> schwartz (\x. phi(c + s * x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schwartz] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `\n:num. \x. Cx s pow n * (d:num->real->complex) n (c + s * x)`
    THEN
  REWRITE_TAC[complex_pow; COMPLEX_MUL_LID] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`d:num->real->complex`; `c:real`;
      `s:real`] AFFINE_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[complex_pow];
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN
    FIRST_ASSUM(X_CHOOSE_TAC `B0:real` o SPECL [`0`; `m:num`]) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `Bk:real` o SPECL [`k:num`; `m:num`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real_pow; REAL_MUL_LID]) THEN
    EXISTS_TAC `abs s pow m * (inv(abs s pow k) * (&2 pow k * (Bk + abs c pow k
      * B0)))` THEN
    X_GEN_TAC `x:real` THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[REAL_ARITH `ak * (asm * n):real = asm * (ak * n)`] THEN
    MP_TAC(ISPECL [`abs s pow m`;
      `abs x pow k * norm((d:num->real->complex) m (c + s * x))`;
                   `inv(abs s pow k) * (&2 pow k * (Bk + abs c pow k * B0))`]
                     REAL_LE_LMUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC AFFINE_WEIGHT_BOUND THEN ASM_REWRITE_TAC[NORM_POS_LE]];
      MATCH_MP_TAC(REAL_ARITH `x = y ==> a <= x ==> a <= y`) THEN
      REWRITE_TAC[REAL_MUL_AC]]]);;

(* ------------------------------------------------------------------------- *)
(* Schwartz closed under multiplication by a complex constant. Trivial: same *)
(* chain scaled by c, decay bounds scaled by norm c.                         *)
(* ------------------------------------------------------------------------- *)

let SCHWARTZ_CMUL = prove
 (`!(h:real->complex) c. schwartz h ==> schwartz (\x. c * h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schwartz] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n x. c * (d:num->real->complex) n x` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM];
    REPEAT GEN_TAC THEN MATCH_MP_TAC CONST_CHAIN_DERIV THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `B:real` o SPECL [`k:num`; `m:num`]) THEN
    EXISTS_TAC `norm(c:complex) * B` THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `!a b cc:real. a * b * cc = b * (a *
      cc)`] THEN
    MP_TAC(ISPECL [`norm(c:complex)`;
      `abs x pow k * norm((d:num->real->complex) m x)`;
        `B:real`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [REWRITE_TAC[NORM_POS_LE]; ASM_REWRITE_TAC[]];
      DISCH_THEN ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Inversion in "psi = fhat o reflect" form:  for Schwartz phi,              *)
(*   fourier (\x. fourier phi (--x)) y = phi y.                              *)
(* This is DOUBLE_TRANSFORM (fourier(fourier h)(--z) = h z) composed with    *)
(* FOURIER_REFLECT (fourier(\x. f(--x)) y = fourier f (--y)).                *)
(* ------------------------------------------------------------------------- *)

let PHI_IS_FOURIER = prove
 (`!phi:real->complex. schwartz phi
     ==> (!y. fourier (\x. fourier phi (--x)) y = phi y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fourier(phi:real->complex)`; `y:real`] FOURIER_REFLECT) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`phi:real->complex`; `y:real`] DOUBLE_TRANSFORM) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Schwartz closed under modulation:  phi |-> e^{i b x} phi(x).  Proved via  *)
(* Fourier duality (NOT a Leibniz decay bound): with psi = \x. fourier       *)
(* phi(-x),                                                                  *)
(* one has fourier psi = phi (PHI_IS_FOURIER) and                            *)
(*   e^{i b x} phi(x) = fourier (\u. psi(u + b)) (x)   (FOURIER_SHIFT),      *)
(* and psi(.+b) is Schwartz (SCHWARTZ_AFFINE), hence so is its transform     *)
(* (SCHWARTZ_FOURIER = 284C).  Reuses everything; non-circular.              *)
(* ------------------------------------------------------------------------- *)

let SCHWARTZ_MODULATE = prove
 (`!phi:real->complex b. schwartz phi
     ==> schwartz (\x. cexp(ii * Cx b * Cx x) * phi x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `psi = \x. fourier (phi:real->complex) (--x)` THEN
  SUBGOAL_THEN `schwartz (psi:real->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN MATCH_MP_TAC SCHWARTZ_REFLECT THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SCHWARTZ_FOURIER THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. fourier (psi:real->complex) x = phi x` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN ASM_SIMP_TAC[PHI_IS_FOURIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. cexp(ii * Cx b * Cx x) * (phi:real->complex) x) = fourier (\u. psi(u +
     b))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
    MP_TAC(ISPECL [`psi:real->complex`; `b:real`; `x:real`] FOURIER_SHIFT) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC SCHWARTZ_MOD_ABSINT THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SCHWARTZ_FOURIER THEN
    SUBGOAL_THEN
      `(\u. (psi:real->complex)(u + b)) = (\u. psi(b + &1 * u))`
      SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
       REAL_ARITH_TAC;
      MATCH_MP_TAC SCHWARTZ_AFFINE THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Closure under a modulated affine reparametrisation:                       *)
(* x |-> e^{i b x} phi(mJ (x - a)) is Schwartz (mJ <> 0).                    *)
(* Peel e^{i b x} (SCHWARTZ_MODULATE), then the affine reparam               *)
(* mJ*(x-a) = --(mJ*a) + mJ*x (SCHWARTZ_AFFINE).                             *)
(* ------------------------------------------------------------------------- *)

let SCHWARTZ_MODAFFINE = prove
 (`!(phi:real->complex) mJ a b. schwartz phi /\ ~(mJ = &0)
     ==> schwartz (\x. cexp(ii * Cx b * Cx x) * phi(mJ * (x - a)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHWARTZ_MODULATE THEN
  SUBGOAL_THEN
    `(\x. (phi:real->complex)(mJ * (x - a))) = (\x. phi(--(mJ * a) + mJ * x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SCHWARTZ_AFFINE THEN ASM_REWRITE_TAC[]]);;

(* Arithmetic identity for dilation scale factors: sqrt m / m = 1 / sqrt m.  *)
let SQRT_SCALE_ID = prove
 (`!mJ. &0 < mJ ==> sqrt mJ * (&1 / mJ) = &1 / sqrt mJ`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(sqrt mJ = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mJ = sqrt mJ * sqrt mJ` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `mJ = sqrt mJ * sqrt mJ` THEN
  UNDISCH_TAC `~(sqrt mJ = &0)` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Two Schwartz functions whose Fourier transforms have disjoint support are *)
(* orthogonal:  if at every u one of fhat u, ghat u vanishes, then           *)
(* INT f cnj(g) = 0.  Immediate from bilinear Parseval (284Ob), since the    *)
(* transform-side integrand fhat cnj(ghat) is identically 0.                 *)
(* ------------------------------------------------------------------------- *)

let SCHWARTZ_ORTHO_DISJOINT_FHAT = prove
 (`!(f:real->complex) (g:real->complex). schwartz f /\ schwartz g /\
     (!u. fourier f u = Cx(&0) \/ fourier g u = Cx(&0))
     ==> integral (:real^1) (\z. f(drop z) * cnj(g(drop z))) = Cx(&0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PARSEVAL_SCHWARTZ_BILINEAR] THEN
  SUBGOAL_THEN
   `(\z. fourier (f:real->complex) (drop z) * cnj(fourier (g:real->complex)
     (drop z))) =
    (\z:real^1. Cx(&0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^1` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop z`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; CNJ_CX; COMPLEX_MUL_RZERO];
    REWRITE_TAC[COMPLEX_VEC_0] THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; INTEGRAL_0]]);;



(* ========================================================================= *)
(* SECTION 13. Real-line convolution and the convolution theorem:            *)
(*             (f * g)^ = sqrt(2pi) . f^ . g^; convolution of Schwartz       *)
(*             functions is continuous / Lipschitz / L^1 / Schwartz.         *)
(*                                                                           *)
(* Builds the convolution operator, the convolution theorem (Fremlin 283M),  *)
(* and continuity of a convolution (255K), in the symmetric normalization    *)
(* used throughout this file.                                                *)
(* ========================================================================= *)

(* Convolution operator (real-line, R->complex), symmetric-normalization     *)
(* tower.                                                                    *)
let convol = new_definition
 `convol (f:real->complex) (g:real->complex) (x:real) =
    integral (:real^1) (\t. f(x - drop t) * g(drop t))`;;

(* For Schwartz f,g the convolution integrand at x is absolutely integrable: *)
(* t |-> f(x-t) is Schwartz (SCHWARTZ_AFFINE, s=-1), hence                   *)
(* bounded+measurable, and g is L^1 (SCHWARTZ_ABSINT); bounded x L^1 is      *)
(* absolutely integrable.                                                    *)
let CONVOL_INTEGRAND_ABSINT = prove
 (`!(f:real->complex) g x. schwartz f /\ schwartz g
     ==> (\t. f(x - drop t) * g(drop t)) absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`;
                 `\t:real^1. (f:real->complex)(x - drop t)`;
                 `\t:real^1. (g:real->complex)(drop t)`; `(:real^1)`]
    ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [(* t |-> f(x - drop t) measurable                                        *)
    SUBGOAL_THEN `schwartz (\u. (f:real->complex)(x - u))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`f:real->complex`; `-- &1:real`;
       `x:real`] SCHWARTZ_AFFINE) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `x + -- &1 * u = x - u`] THEN
      REWRITE_TAC[REAL_ARITH `~(-- &1 = &0)`]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MP_TAC(MATCH_MP SCHWARTZ_CONT (ASSUME `schwartz (\u. (f:real->complex)(x -
      u))`)) THEN
    REWRITE_TAC[];
    (* bounded image of t |-> f(x - drop t)                                  *)
    SUBGOAL_THEN
      `?B. !u. norm((f:real->complex)(x - u)) <= B` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`f:real->complex`; `-- &1:real`;
       `x:real`] SCHWARTZ_AFFINE) THEN
      ASM_REWRITE_TAC[REAL_ARITH `~(-- &1 = &0)`] THEN
      REWRITE_TAC[REAL_ARITH `x + -- &1 * u = x - u`] THEN DISCH_TAC THEN
      MP_TAC(MATCH_MP SCHWARTZ_BOUNDED (ASSUME `schwartz (\u.
        (f:real->complex)(x - u))`)) THEN
      REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `B:real` THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_UNIV] THEN ASM_REWRITE_TAC[];
    (* g(drop t) absolutely integrable                                       *)
    MP_TAC(MATCH_MP SCHWARTZ_ABSINT (ASSUME `schwartz (g:real->complex)`)) THEN
    REWRITE_TAC[]]);;

(* The convolution integrand is integrable (from absolutely integrable).     *)
let CONVOL_INTEGRAND_INTEGRABLE = prove
 (`!(f:real->complex) g x. schwartz f /\ schwartz g
     ==> (\t. f(x - drop t) * g(drop t)) integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC CONVOL_INTEGRAND_ABSINT THEN ASM_REWRITE_TAC[]);;

(* The convolution norm is bounded by the integral of the pointwise product  *)
(* of norms, by the triangle inequality for vector integrals.                *)
let CONVOL_NORM_BOUND = prove
 (`!(f:real->complex) g x. schwartz f /\ schwartz g
     ==> norm(convol f g x)
         <= drop(integral (:real^1) (\t. lift(norm(f(x - drop t)) * norm(g(drop
           t)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[convol] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONVOL_INTEGRAND_INTEGRABLE THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`f:real->complex`; `g:real->complex`;
      `x:real`] CONVOL_INTEGRAND_ABSINT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
    REWRITE_TAC[o_DEF; COMPLEX_NORM_MUL];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP; COMPLEX_NORM_MUL; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The 2D transform integrand (x,t) |-> e^{-iyx} f(x-t) g(t) is measurable   *)
(* on R^2. All factors are continuous, so the product is continuous. This    *)
(* supplies the measurability needed for the convolution theorem's Fubini    *)
(* interchange.                                                              *)
(* ------------------------------------------------------------------------- *)
let IMAGE_ADD_LEFT_UNIV = prove
 (`!a:real^N. IMAGE (\x. a + x) (:real^N) = (:real^N)`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `y:real^N` THEN EXISTS_TAC `y - a:real^N` THEN VECTOR_ARITH_TAC);;

let INTEGRAL_NORM_TRANSLATION_UNIV = prove
 (`!(f:real^1->complex) a.
     integral (:real^1) (\x. lift(norm(f(a + x)))) =
     integral (:real^1) (\x. lift(norm(f x)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. lift(norm((f:real^1->complex) x))`; `(:real^1)`;
    `a:real^1`]
    INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[IMAGE_ADD_LEFT_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 283M brick 3: the x-slice of the transform integrand is absolutely        *)
(* integrable (fixed t). \x. e^{-iyx} f(x-t) g(t) = (bounded e^{-iyx} g(t))  *)
(* x                                                                         *)
(* (L^1 f(x-t)); f(.-t) is Schwartz (SCHWARTZ_AFFINE) hence L^1 (SCHWARTZ_   *)
(* ABSINT).  This is the a.e.-slice-absint hypothesis of FUBINI for the      *)
(* convolution theorem swap.                                                 *)
(* ------------------------------------------------------------------------- *)
let FOURIER_MODULATE_ABSINT = prove
 (`!(f:real->complex) w. schwartz f
     ==> (\u. cexp(--(ii * Cx w * Cx(drop u))) * f(drop u))
       absolutely_integrable_on (:real^1)`,
  MATCH_ACCEPT_TAC SCHWARTZ_MOD_ABSINT);;


(* Abstract complex rearrangement (a b = c ==> (a p)(b q) = c (p q)), for    *)
(* the modulated-product regroup in CONV283M_INNER (COMPLEX_RING chokes on   *)
(* cexp atoms in place, so prove over fresh vars + MATCH_MP forward).        *)
let CEXP_PROD_REARR = prove
 (`!a b c p q:complex. a * b = c ==> (a * p) * (b * q) = c * (p * q)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    CONV_TAC COMPLEX_RING);;

(* Inner identity: the convolution of the two modulated functions at x       *)
(* equals e^{-iwx} times the (unmodulated) convolution -- because the two    *)
(* e^{-iw.} factors recombine via drop(x-y) + drop y = drop x.               *)
let CONV283M_INNER = prove
 (`!(f:real->complex) g w x:real^1. schwartz f /\ schwartz g
    ==> integral (:real^1) (\y. (\u. cexp(--(ii * Cx w * Cx(drop u))) * f(drop
      u)) (x - y) *
                                (\u. cexp(--(ii * Cx w * Cx(drop u))) * g(drop
                                  u)) y) =
        cexp(--(ii * Cx w * Cx(drop x))) * convol f g (drop x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[convol] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `integral (:real^1)
     (\y. cexp(--(ii * Cx w * Cx(drop x))) *
          ((f:real->complex)(drop x - drop y) * (g:real->complex)(drop y)))`
            THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[DROP_SUB] THEN MATCH_MP_TAC CEXP_PROD_REARR THEN
    REWRITE_TAC[GSYM CEXP_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_SUB] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y:real^1. (f:real->complex)(drop x - drop y) * g(drop y)) integrable_on
     (:real^1)`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real->complex`; `g:real->complex`; `drop(x:real^1)`]
      CONVOL_INTEGRAND_INTEGRABLE) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_COMPLEX_LMUL]);;

let FOURIER_CONVOLUTION = prove
 (`!(f:real->complex) g w. schwartz f /\ schwartz g
     ==> fourier (convol f g) w = Cx(sqrt(&2 * pi)) * fourier f w * fourier g
       w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fourier] THEN
  SUBGOAL_THEN
   `integral (:real^1) (\x. cexp(--(ii * Cx w * Cx(drop x))) * convol f g (drop
     x)) =
    integral (:real^1)
      (\x. integral (:real^1)
        (\y. (\u. cexp(--(ii * Cx w * Cx(drop u))) * (f:real->complex)(drop u))
          (x - y) *
             (\u. cexp(--(ii * Cx w * Cx(drop u))) * (g:real->complex)(drop u))
               y))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[CONV283M_INNER]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`( * ):complex->complex->complex`;
    `\u:real^1. cexp(--(ii * Cx w * Cx(drop u))) * (f:real->complex)(drop u)`;
    `\u:real^1. cexp(--(ii * Cx w * Cx(drop u))) * (g:real->complex)(drop u)`]
   DOUBLE_INTEGRAL_CONVOLUTION) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FOURIER_MODULATE_ABSINT THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INNER_INT_FOURIER] THEN
  MP_TAC PI_POS THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* 255K: the convolution of two Schwartz functions is continuous everywhere. *)
(* Direct from the library CONTINUOUS_ON_CONVOLUTION_L1_LINF (f in L^1 =     *)
(* SCHWARTZ_ABSINT, g measurable + bounded).  Combined with 283M + transform *)
(* injectivity (DOUBLE_TRANSFORM) this upgrades the a.e. identity gt_m =     *)
(* (1/sqrt2pi) gt*psicheck to an EVERYWHERE identity (Fremlin (h)(v)).       *)
(* ------------------------------------------------------------------------- *)
let SCHWARTZ_MEASURABLE_BOUNDED = prove
 (`!g:real->complex. schwartz g
     ==> (\v. g(drop v)) measurable_on (:real^1) /\ bounded (IMAGE (\v. g(drop
       v)) (:real^1))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MP_TAC(MATCH_MP SCHWARTZ_CONT (ASSUME `schwartz (g:real->complex)`)) THEN
      REWRITE_TAC[];
    FIRST_ASSUM(X_CHOOSE_TAC `B:real` o MATCH_MP SCHWARTZ_BOUNDED) THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `B:real` THEN
    X_GEN_TAC `v:real^1` THEN REWRITE_TAC[IN_UNIV] THEN ASM_REWRITE_TAC[]]);;

let CONVOL_CONTINUOUS = prove
 (`!(f:real->complex) g. schwartz f /\ schwartz g
     ==> (\x. convol f g (drop x)) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. convol f g (drop x)) =
    (\x. integral (:real^1) (\y. (\v. (f:real->complex)(drop v)) (x - y) *
                                 (\v. (g:real->complex)(drop v)) y))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
     REWRITE_TAC[convol] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_SUB]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CONVOLUTION_L1_LINF THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(MATCH_MP SCHWARTZ_ABSINT (ASSUME `schwartz (f:real->complex)`)) THEN
     REWRITE_TAC[];
    MP_TAC(MATCH_MP SCHWARTZ_MEASURABLE_BOUNDED (ASSUME `schwartz
      (g:real->complex)`)) THEN
    SIMP_TAC[];
    MP_TAC(MATCH_MP SCHWARTZ_MEASURABLE_BOUNDED (ASSUME `schwartz
      (g:real->complex)`)) THEN
    SIMP_TAC[]]);;

(* convol f g is globally LIPSCHITZ (f,g Schwartz): the difference splits as *)
(*   convol f g u - convol f g w = int_t (f(u-t) - f(w-t)) g(t),             *)
(* and |f(u-t)-f(w-t)| <= K_f |u-w| (SCHWARTZ_LIPSCHITZ on f, arg-diff =     *)
(* u-w),                                                                     *)
(* so the norm is <= K_f |u-w| int_t|g| = (K_f ||g||_1) |u-w|.  This local   *)
(* Lipschitz bound is exactly the hypothesis FOURIER_283J needs to invert    *)
(* the                                                                       *)
(* transform of convol f g pointwise.                                        *)
let CONVOL_LIPSCHITZ = prove
 (`!(f:real->complex) g. schwartz f /\ schwartz g
     ==> ?K. &0 <= K /\
             !u w. norm(convol f g u - convol f g w) <= K * abs(u - w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real->complex` SCHWARTZ_LIPSCHITZ) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kf:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `(\t. lift(norm((g:real->complex)(drop t)))) integrable_on (:real^1)`
    ASSUME_TAC THENL
   [MP_TAC(ISPEC `g:real->complex` SCHWARTZ_ABSINT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    REWRITE_TAC[o_DEF] THEN
    DISCH_THEN(ACCEPT_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE);
      ALL_TAC] THEN
  ABBREV_TAC `Ng = drop(integral (:real^1) (\t.
    lift(norm((g:real->complex)(drop t)))))` THEN
  SUBGOAL_THEN `&0 <= Ng` ASSUME_TAC THENL
   [EXPAND_TAC "Ng" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE]; ALL_TAC] THEN
  EXISTS_TAC `Kf * Ng:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `w:real`] THEN
  REWRITE_TAC[convol] THEN
  MP_TAC(ISPECL [`\t. (f:real->complex)(u - drop t) * g(drop t)`;
                 `\t. (f:real->complex)(w - drop t) * g(drop t)`;
                 `(:real^1)`] INTEGRAL_SUB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONVOL_INTEGRAND_INTEGRABLE THEN
     ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^1) (\t. lift(Kf * abs(u - w) *
    norm((g:real->complex)(drop t)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\t. (f:real->complex)(u - drop t) * g(drop t)`;
                     `\t. (f:real->complex)(w - drop t) * g(drop t)`;
                     `(:real^1)`] INTEGRABLE_SUB) THEN
      ASM_SIMP_TAC[CONVOL_INTEGRAND_INTEGRABLE];
      REWRITE_TAC[REAL_ARITH `Kf * abs(u - w) * n = (Kf * abs(u - w)) * n`]
        THEN
      SUBGOAL_THEN
       `(\t. lift((Kf * abs(u - w)) * norm((g:real->complex)(drop t)))) =
        (\t. (Kf * abs(u - w)) % lift(norm((g:real->complex)(drop t))))`
       SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL]; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
        BETA_TAC THEN
      SUBGOAL_THEN
        `abs((u - drop t) - (w - drop t)) = abs(u - w)` ASSUME_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; COMPLEX_NORM_MUL;
        REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        ASM_MESON_TAC[]];
    REWRITE_TAC[REAL_ARITH `Kf * abs(u - w) * n = (Kf * abs(u - w)) * n`] THEN
    SUBGOAL_THEN
     `(\t. lift((Kf * abs(u - w)) * norm((g:real->complex)(drop t)))) =
      (\t. (Kf * abs(u - w)) % lift(norm((g:real->complex)(drop t))))`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
    EXPAND_TAC "Ng" THEN REAL_ARITH_TAC]);;

(* convol f g is absolutely integrable AS A FUNCTION of x (f,g Schwartz): it *)
(* is                                                                        *)
(* continuous (CONVOL_CONTINUOUS, hence measurable) and dominated by         *)
(*   dm(x) = int_t norm(f(x-t)) norm(g(t)) dt = |f|*|g|(x)                   *)
(* which is integrable [DOUBLE_INTEGRABLE_CONVOLUTION with the bilinear real *)
(* product BILINEAR_LIFT_MUL on the lifted norms of f,g -- both L^1 by       *)
(* SCHWARTZ_ABSINT]; norm(convol f g x) <= dm(x) is CONVOL_NORM_BOUND. This  *)
(* is                                                                        *)
(* the L^1 hypothesis FOURIER_283J needs (alongside CONVOL_LIPSCHITZ).       *)
let CONVOL_ABSINT = prove
 (`!(f:real->complex) g. schwartz f /\ schwartz g
     ==> (\z. convol f g (drop z)) absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC
   `\z. integral (:real^1)
          (\t. lift(norm((f:real->complex)(drop z - drop t)) *
                    norm((g:real->complex)(drop t))))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC CONVOL_CONTINUOUS THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`\x y. lift(drop x * drop y)`;
                   `\z. lift(norm((f:real->complex)(drop z)))`;
                   `\z. lift(norm((g:real->complex)(drop z)))`]
      DOUBLE_INTEGRABLE_CONVOLUTION) THEN
    REWRITE_TAC[BILINEAR_LIFT_MUL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPEC `f:real->complex` SCHWARTZ_ABSINT) THEN
         ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
          REWRITE_TAC[o_DEF];
        MP_TAC(ISPEC `g:real->complex` SCHWARTZ_ABSINT) THEN
          ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
          REWRITE_TAC[o_DEF]];
      REWRITE_TAC[LIFT_DROP; DROP_SUB]];
    X_GEN_TAC `z:real^1` THEN REWRITE_TAC[IN_UNIV] THEN
    MP_TAC(ISPECL [`f:real->complex`; `g:real->complex`;
      `drop z`] CONVOL_NORM_BOUND) THEN
    ASM_REWRITE_TAC[]]);;

(* Fremlin (h)(v) uniqueness bridge: if convol cf cg (cf,cg Schwartz) has    *)
(* the                                                                       *)
(* SAME Fourier transform as sqrt2pi times a Schwartz gtm, then              *)
(*   convol cf cg = sqrt2pi * gtm  EVERYWHERE.                               *)
(* Fremlin's route (avoids proving convol Schwartz): convol cf cg is L^1     *)
(* (CONVOL_ABSINT), Lipschitz (CONVOL_LIPSCHITZ), and its transform sqrt2pi  *)
(* gtm^                                                                      *)
(* is L^1 (gtm Schwartz => SCHWARTZ_FHAT_ABSINT), so FOURIER_283J inverts it *)
(* pointwise: convol x = (1/sqrt2pi) int e^{ixy}(convol)^ = int e^{ixy}      *)
(* gtm^;                                                                     *)
(* FOURIER_284C_INVERSION on the Schwartz gtm gives int e^{ixy} gtm^ =       *)
(* sqrt2pi                                                                   *)
(* gtm x.  Everywhere, not just a.e.                                         *)
let CONVOL_SCHWARTZ_EQ = prove
 (`!(cf:real->complex) cg (gtm:real->complex).
     schwartz cf /\ schwartz cg /\ schwartz gtm /\
     (!w. fourier (convol cf cg) w = Cx(sqrt(&2 * pi)) * fourier gtm w)
     ==> !x. convol cf cg x = Cx(sqrt(&2 * pi)) * gtm x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cf:real->complex`; `cg:real->complex`] CONVOL_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN
    `Kc:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`convol cf cg`; `x:real`; `Kc:real`; `&1`] FOURIER_283J) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `v:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs((x - v) - x) = abs v` (fun th ->
        MP_TAC(GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [th]
          (SPECL [`x - v:real`; `x:real`]
            (ASSUME `!u w. norm(convol cf cg u - convol cf cg w) <= Kc * abs(u
              - w)`)))) THENL
       [REAL_ARITH_TAC; REWRITE_TAC[]];
      MATCH_MP_TAC CONVOL_ABSINT THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(\z. fourier (convol cf cg) (drop z)) =
        (\z. Cx(sqrt(&2 * pi)) * fourier gtm (drop z))`
       SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL THEN
      MATCH_MP_TAC SCHWARTZ_FHAT_ABSINT THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`gtm:real->complex`; `x:real`] FOURIER_284C_INVERSION) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `II = integral (:real^1)
     (\y. cexp(ii * Cx x * Cx(drop y)) * fourier gtm (drop y))` THEN
  SUBGOAL_THEN
   `integral (:real^1)
      (\y. cexp(ii * Cx x * Cx(drop y)) * Cx(sqrt(&2 * pi)) * fourier gtm (drop
        y)) =
    Cx(sqrt(&2 * pi)) * II` SUBST1_TAC THENL
   [EXPAND_TAC "II" THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV)
     [SIMPLE_COMPLEX_ARITH `a * s * b = s * a * b`] THEN
    MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
    MATCH_MP_TAC FOURIER_INV_MODULATED_INTEGRABLE THEN
    MATCH_MP_TAC SCHWARTZ_FHAT_ABSINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `Cx(inv(sqrt(&2 * pi))) * Cx(sqrt(&2 * pi)) = Cx(&1)` MP_TAC THENL
   [REWRITE_TAC[GSYM CX_MUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC COMPLEX_RING);;
