(* ========================================================================= *)
(*                                                                           *)
(*   Quantum optics library: single mode electromagnetic field.              *)
(*                                                                           *)
(*    (c) Copyright, Mohamed Yousri Mahmoud , 2012-2014                      *)
(*                   Hardware Verification Group,                            *)
(*                   Concordia University                                    *)
(*                                                                           *)
(*           Contact: <mo_solim@ece.concordia.ca>,                           *)
(*                                                                           *)
(* Last update: April 18, 2016                                               *)
(*                                                                           *)
(* ========================================================================= *)


needs "Functionspaces/cfunspace.ml";;

(*****************************************************************************)
(* SQUARE INTEGRABLE FUNCTIONS (L2)                                          *)
(*****************************************************************************)

parse_as_infix("complex_measurable_on",(12,"right"));;

let complex_measurable = new_definition
 `f complex_measurable_on s <=>  (\x. Re (f x)) real_measurable_on s /\
   (\x. Im (f x)) real_measurable_on s`;;

let sq_integrable = new_specification ["sq_integrable"]
  (prove(`?s. !f. f IN s <=> f complex_measurable_on (:real) /\ (\x. norm (f x) pow 2)
  real_integrable_on (:real)`, EXISTS_TAC `{f| f complex_measurable_on (:real) /\
  (\x. norm (f x) pow 2) real_integrable_on (:real)}` THEN SIMP_TAC[IN_ELIM_THM]));;

let r_inprod = new_definition
 `r_inprod f g = complex(real_integral (:real) (\x:real. Re (cnj (f x) * (g x))),
 real_integral (:real) (\x. Im (cnj (f x) * (g x))) )`;;

(*****************************************************************************)
(*We will prove each property of the  inner space      in the   following    *)
(*theorems. We will conclude all properties in one theorem at the very end   *)
(*****************************************************************************)

let FRECHET_REAL_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL = prove
(`!f f' f'' x a b.
     a < b /\ x IN real_interval[a,b] /\
     (f has_real_derivative f') (atreal x within (real_interval[a,b])) /\
     (f has_real_derivative f'') (atreal x within (real_interval[a,b]))
     ==> f' = f''`,
  let tem = REWRITE_RULE[MESON[] `A/\B/\C ==> Q <=> C ==> A /\ B ==> Q `]
  FRECHET_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL in
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN ]
  THEN   REWRITE_TAC[MESON[] `A/\B/\C ==> Q <=> C ==> A /\ B ==> Q `;
  IMAGE_LIFT_REAL_INTERVAL ] THEN
  DISCH_THEN  (ASSUME_TAC o (MATCH_MP tem)) THEN
  POP_ASSUM(ASSUME_TAC o( SIMP_RULE[LIFT_IN_INTERVAL ;DIMINDEX_1;LIFT_DROP;
  ARITH_RULE`x <= i /\ i <= x <=> i=(x:num)`;lift;LAMBDA_BETA])) THEN
  DISCH_THEN (fun th1 -> POP_ASSUM (MP_TAC o (SIMP_RULE[GSYM LIFT_EQ_CMUL;
  LIFT_EQ])o(Pa.SPEC `vec 1:`)o (SIMP_RULE[th1;FUN_EQ_THM])))
  THEN   REWRITE_TAC[]);;

let  cfun_almost_zero = new_specification ["cfun_almost_zero"]
(prove(`?f.(?k. real_negligible k /\ !x. ~(x IN k) ==> f x = Cx(&0))`,
  Pa.EXISTS_TAC `cfun_zero:` THEN REWRITE_TAC[cfun_zero;K_THM]THEN Pa.EXISTS_TAC `{}:`
THEN REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY]));;
let is_almost_zero = new_definition
 `is_almost_zero1 f = !a b. (?k. real_negligible k /\ !x. x IN real_interval[a,b]
  DIFF k ==> f x = Cx(&0))`;;

let REAL_INTEGRA_ZERO_SUBINTERVALS = prove
(`!f. (!x. &0 <= f x) /\ (f has_real_integral &0) (:real) ==>
   !a b. (f has_real_integral &0) (real_interval[a,b])`,
        REPEAT STRIP_TAC THEN Pa.ASM_CASES_TAC `b<=a:`
        THENL[ASM_SIMP_TAC[HAS_REAL_INTEGRAL_NULL];ALL_TAC] THEN
        Pa.SUBGOAL_THEN `!a b. f real_integrable_on (real_interval[a,b]):`
        ASSUME_TAC THENL[
        RULE_ASSUM_TAC(REWRITE_RULE[HAS_REAL_INTEGRAL_ALT;SET_RULE `x IN (:real)`;ETA_AX])
        THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
        MP_TAC (Pa.SPECL [`f:`;`real_interval[a,b]:`] REAL_INTEGRAL_POS)
        THEN ASM_SIMP_TAC[] THEN
        MP_TAC (Pa.SPECL [`f:`;`real_interval[a,b]:`;`(:real):`] REAL_INTEGRAL_SUBSET_LE)
        THEN RULE_ASSUM_TAC(REWRITE_RULE[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL])
        THEN IMP_REWRITE_TAC[SET_RULE `!s. ~(s={}) ==> s SUBSET (:real)`;
        REAL_INTERVAL_NE_EMPTY;GSYM REAL_LE_ANTISYM;
        HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        ASM_SIMP_TAC[REAL_ARITH `~(b <= a) ==> a <= b`]);;


let REAL_POW2_0 = REWRITE_RULE[REAL_ADD_LID;REAL_POW_ZERO; ARITH]
(SPEC `&0` REAL_SOS_EQ_0);;

let RINPROD_ALMOST_ZERO = prove(
 `!f. f IN sq_integrable ==> (r_inprod f f = Cx (&0) <=> is_almost_zero1  f)`,
 REWRITE_TAC[sq_integrable;r_inprod;r_inprod;RE_CX;IM_CX;GSYM CX_DEF;
COMPLEX_MUL_CNJ;GSYM CX_POW;REAL_INTEGRAL_0; CX_INJ] THEN
REPEAT STRIP_TAC THEN EQ_TAC THENL[
 POP_ASSUM MP_TAC THEN REWRITE_TAC[MESON[] `P==>Q==>A <=> P/\Q ==>A`] THEN
 DISCH_THEN (fun thm -> ASSUME_TAC(REWRITE_RULE
 [GSYM HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] thm) THEN MP_TAC thm) THEN
Pa.SUBGOAL_THEN `!a b. (\x. norm (f x) pow 2) real_integrable_on (real_interval[a,b]):`
        ASSUME_TAC THENL[
        RULE_ASSUM_TAC(REWRITE_RULE[HAS_REAL_INTEGRAL_ALT;SET_RULE `x IN (:real)`;ETA_AX])
        THEN ASM_REWRITE_TAC[];ALL_TAC]
THEN MP_TAC (Pa.SPEC `(\x. norm ((f:real->complex) x) pow 2):`
HAS_REAL_DERIVATIVE_INDEFINITE_INTEGRAL) THEN ASM_REWRITE_TAC[] THEN
MP_TAC (Pa.SPEC `(\x. norm ((f:real->complex) x) pow 2):`
REAL_INTEGRA_ZERO_SUBINTERVALS) THEN
ASM_SIMP_TAC[REAL_LE_POW_2;HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL]
THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
SUBGOAL_THEN `(!a b. ?k. real_negligible k /\
          (!x. x IN real_interval [a,b] DIFF k
               ==> ((\x. &0) has_real_derivative norm ((f:real->complex) x) pow 2)
                   (atreal x within real_interval [a,b]))) ==>
                (!a b.
      ?k. real_negligible k /\
          (!x. x IN real_interval [a,b] DIFF k ==> norm (f x) pow 2 = &0))`
                  ASSUME_TAC
 THENL[REPEAT STRIP_TAC THEN
 POP_ASSUM (MP_TAC o SPECL [`a:real`;`b:real`]) THEN REPEAT STRIP_TAC
 THEN Pa.ASM_CASES_TAC `a < b:` THENL[
 Pa.EXISTS_TAC `k:` THEN ASM_SIMP_TAC[] THEN
 ASSUME_TAC (Pa.SPECL [`&0:`;`atreal x within real_interval [a,b]:`] HAS_REAL_DERIVATIVE_CONST)
  THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FRECHET_REAL_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL
  THEN MAP_EVERY Pa.EXISTS_TAC [`(\x. &0):`;`x':`;`a:`;`b:`] THEN
  ASM_SIMP_TAC[]  THEN ASM_MESON_TAC[IN_DIFF ];
  Pa.EXISTS_TAC `{a}:`
  THEN ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE ;FINITE_SING;real_interval;IN_ELIM_THM;IN_DIFF;IN_SING]
  THEN ASM_MESON_TAC[REAL_FIELD `~(a < b) /\ (a <= x /\ x <= b) /\
  ~(x = a) <=> F`]];ALL_TAC] THEN
        DISCH_THEN (fun th -> POP_ASSUM (fun th1 -> ASSUME_TAC
        (SIMP_RULE[REAL_POW2_0;COMPLEX_NORM_ZERO ](MATCH_MP th1 th))))
  THEN ASM_SIMP_TAC[is_almost_zero];ALL_TAC] THEN
  REWRITE_TAC[is_almost_zero] THEN REPEAT STRIP_TAC
  THEN  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_ALT;SET_RULE `x IN (:real)`] THEN
   Pa.SUBGOAL_THEN `!a b. ((\x. norm (f x) pow 2) has_real_integral &0)
     (real_interval [a,b]):` ASSUME_TAC
   THENL[
   IMP_REWRITE_TAC[HAS_REAL_INTEGRAL_NEGLIGIBLE;REAL_POW2_0;COMPLEX_NORM_ZERO ];
   ALL_TAC] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[HAS_REAL_INTEGRAL_INTEGRABLE];
   EXISTS_TAC  `&1` THEN ASM_SIMP_TAC [REAL_ARITH `&0 < &1`] THEN
   REPEAT STRIP_TAC THEN
   IMP_REWRITE_TAC[REAL_INTEGRAL_UNIQUE] THEN EXISTS_TAC  `&0` THEN
   ASM_SIMP_TAC [REAL_ARITH `&0 - &0 = &0`;REAL_ABS_NUM]]);;

let ALOMST_ZERO_ZERO = prove
 (`!f g. is_almost_zero1 f ==> r_inprod g f = Cx(&0)`,
 REWRITE_TAC[r_inprod;COMPLEX_EQ;CX_DEF;RE;IM] THEN
 REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
 REWRITE_TAC[HAS_REAL_INTEGRAL_ALT;SET_RULE `x IN (:real)`]
 THEN  RULE_ASSUM_TAC(REWRITE_RULE[is_almost_zero])
   THENL[Pa.SUBGOAL_THEN `!a b.  ((\x. Re (cnj (g x) * f x)) has_real_integral &0)
     (real_interval [a,b]):` ASSUME_TAC THENL[
   REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_NEGLIGIBLE THEN
          POP_ASSUM ( (X_CHOOSE_TAC `s:real->bool`) o  SPEC_ALL) THEN
         Pa.EXISTS_TAC `s:` THEN ASM_SIMP_TAC[COMPLEX_MUL_RZERO;RE_CX;IM_CX];ALL_TAC];
          Pa.SUBGOAL_THEN `!a b.  ((\x. Im (cnj (g x) * f x)) has_real_integral &0)
     (real_interval [a,b]):` ASSUME_TAC
         THENL [REPEAT STRIP_TAC THEN  MATCH_MP_TAC HAS_REAL_INTEGRAL_NEGLIGIBLE THEN
          POP_ASSUM ( (X_CHOOSE_TAC `s:real->bool`) o  SPEC_ALL)
         THEN Pa.EXISTS_TAC `s:` THEN ASM_SIMP_TAC[COMPLEX_MUL_RZERO;RE_CX;IM_CX];ALL_TAC]]
         THEN ASM_MESON_TAC[REAL_SUB_RZERO;HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL;REAL_ABS_0]);;

let RINPROD_ZERO_EQ = prove
(`!x y. x IN sq_integrable  /\ r_inprod x x = Cx(&0)
     ==> r_inprod y x = Cx(&0)`,
 MESON_TAC[ALOMST_ZERO_ZERO;RINPROD_ALMOST_ZERO]);;

let SQ_RULE = REAL_FIELD `(a+b) pow 2 = a pow 2 + b pow 2 + &2 * a * b`;;
let SQ_RULE_SUB = REAL_FIELD `(a-b) pow 2 = a pow 2 + b pow 2 - &2 * a * b`;;

let ABS_POW_2 = MESON[REAL_ABS_REFL;REAL_LE_POW_2] `!x. abs (x pow 2) = x pow 2`;;

let SQ_INTEGRABLE_SUBSPACE = prove(
`is_cfun_subspace sq_integrable`,
REWRITE_TAC[is_cfun_subspace;sq_integrable;complex_measurable;cfun_zero;
K_THM;RE_CX;IM_CX;REAL_MEASURABLE_ON_0;COMPLEX_NORM_0;REAL_POW_ZERO;
ARITH;REAL_INTEGRABLE_0] THEN REPEAT STRIP_TAC
THENL[
ASM_SIMP_TAC[CFUN_SMUL;REAL_MEASURABLE_ON_LMUL;RE;complex_mul;
REAL_MEASURABLE_ON_SUB]
;ASM_SIMP_TAC[CFUN_SMUL;REAL_MEASURABLE_ON_LMUL;IM;complex_mul;
REAL_MEASURABLE_ON_ADD]
;ASM_SIMP_TAC[CFUN_SMUL;COMPLEX_NORM_MUL;REAL_POW_MUL;REAL_INTEGRABLE_LMUL]
;ASM_SIMP_TAC[CFUN_ADD_THM;RE_ADD;REAL_MEASURABLE_ON_ADD]
;ASM_SIMP_TAC[CFUN_ADD_THM;IM_ADD;REAL_MEASURABLE_ON_ADD]
;RULE_ASSUM_TAC(REWRITE_RULE[SQ_RULE;COMPLEX_SQNORM])
THEN ASM_SIMP_TAC[CFUN_ADD_THM;complex_add;COMPLEX_SQNORM;RE;IM;SQ_RULE;
REAL_FIELD `((a1:real)+b1+c1) + a2 + b2 + c2 = (a1+a2) + (b1+b2) + c1+ c2`]
THEN MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]
THEN MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]
THEN MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN REPEAT STRIP_TAC
THENL [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
THEN Pa.EXISTS_TAC `\x'.( Re (x x') pow 2 + Im (x x') pow 2) +
   (Re (y x') pow 2 + Im (y x') pow 2):`
THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
REAL_INTEGRABLE_ADD;REAL_ABS_MUL;REAL_ABS_NUM] THEN
ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+a2-c1)+b1+b2`;
GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2];
ALL_TAC] THEN
MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
THEN Pa.EXISTS_TAC `\x'.( Re (x x') pow 2 + Im (x x') pow 2) +
   (Re (y x') pow 2 + Im (y x') pow 2):`
THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
REAL_INTEGRABLE_ADD;REAL_ABS_MUL;REAL_ABS_NUM] THEN
ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+a2)+(b1+b2-c1)`;
GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]]);;

let RINPROD_SELF_POS = prove(
 `!f. f IN sq_integrable
       ==> real (r_inprod f f) /\
                &0 <= real_of_complex (r_inprod f f)`,
 REWRITE_TAC[sq_integrable;REAL;r_inprod;COMPLEX_MUL_CNJ;RE_CX;IM_CX;GSYM CX_POW
 ;RE;IM;REAL_INTEGRAL_0;GSYM CX_DEF;REAL_OF_COMPLEX_CX] THEN
REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_POS
THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let RINPROD_CNJ = prove(
 `!f g. f IN sq_integrable /\ g IN sq_integrable
    ==> cnj (r_inprod f g) = r_inprod g f`,
         REWRITE_TAC[sq_integrable;complex_measurable;RE;IM;cnj;COMPLEX_SQNORM;
         r_inprod;complex_mul]
         THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC
         THENL[AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
         REAL_ARITH_TAC;ALL_TAC] THEN
         Pa.SUBGOAL_THEN `(\x. Re (f x) * Im (g x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (g x') pow 2 + Im (g x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+b2-c1)+(b1+a2)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
    Pa.SUBGOAL_THEN `(\x. Im (f x) * Re (g x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (g x') pow 2 + Im (g x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (b1+a2-c1)+(b2+a1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC]      THEN
    ASM_SIMP_TAC[GSYM REAL_NEG_LMUL;REAL_INTEGRABLE_SUB;REAL_INTEGRABLE_NEG;REAL_INTEGRABLE_ADD;
        GSYM REAL_INTEGRAL_NEG]  THEN
        AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC);;

let RINPROD_RSMUL = prove(
 `!f g a. f IN sq_integrable /\ g IN sq_integrable
    ==> r_inprod f (a%g) = a * r_inprod f g`,
        REWRITE_TAC[sq_integrable;complex_measurable;CFUN_SMUL;RE;IM;cnj;COMPLEX_SQNORM;
         r_inprod;complex_mul]
         THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[PAIR_EQ] THEN
        Pa.SUBGOAL_THEN `(\x. Re (f x) * Im (g x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (g x') pow 2 + Im (g x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+b2-c1)+(b1+a2)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
    Pa.SUBGOAL_THEN `(\x. Im (f x) * Re (g x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (g x') pow 2 + Im (g x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (b1+a2-c1)+(b2+a1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
     Pa.SUBGOAL_THEN `(\x. Re (f x) * Re (g x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (g x') pow 2 + Im (g x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+a2-c1)+(b2+b1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
    Pa.SUBGOAL_THEN `(\x. Im (f x) * Im (g x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (g x') pow 2 + Im (g x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (b1+b2-c1)+(a2+a1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
        IMP_REWRITE_TAC[GSYM REAL_NEG_LMUL;REAL_INTEGRABLE_SUB;
        REAL_INTEGRABLE_NEG;REAL_INTEGRABLE_ADD;
    GSYM REAL_INTEGRAL_LMUL;REAL_INTEGRABLE_LMUL;
        GSYM REAL_INTEGRAL_SUB;GSYM REAL_INTEGRAL_ADD]
        THEN REPEAT STRIP_TAC THEN
     ((AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC)
         ORELSE (MATCH_MP_TAC REAL_INTEGRABLE_LMUL ORELSE ALL_TAC)) THEN
         (MATCH_MP_TAC REAL_INTEGRABLE_SUB ORELSE MATCH_MP_TAC REAL_INTEGRABLE_ADD)
        THEN ASM_SIMP_TAC[REAL_INTEGRABLE_NEG]);;
let RINPROD_LADD = prove
(`!f g z. f IN sq_integrable /\ g IN sq_integrable /\ z IN sq_integrable
    ==> r_inprod (f+g) z= r_inprod f z + r_inprod g z`,
        REWRITE_TAC[sq_integrable;complex_measurable;CFUN_ADD_THM;RE;IM;cnj;COMPLEX_SQNORM;
         r_inprod;complex_mul;RE_ADD;IM_ADD;GSYM REAL_NEG_LMUL;REAL_SUB_RNEG;
         REAL_ADD_RDISTRIB;GSYM real_sub;complex_add]
         THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[PAIR_EQ] THEN
    Pa.SUBGOAL_THEN `(\x. Re (f x) * Im (z x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (z x') pow 2 + Im (z x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+b2-c1)+(b1+a2)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
    Pa.SUBGOAL_THEN `(\x. Im (f x) * Re (z x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (z x') pow 2 + Im (z x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (b1+a2-c1)+(b2+a1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
         Pa.SUBGOAL_THEN `(\x. Re (g x) * Im (z x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (g x') pow 2 + Im (g x') pow 2) +
           (Re (z x') pow 2 + Im (z x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+b2-c1)+(b1+a2)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
    Pa.SUBGOAL_THEN `(\x. Im (g x) * Re (z x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (g x') pow 2 + Im (g x') pow 2) +
           (Re (z x') pow 2 + Im (z x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (b1+a2-c1)+(b2+a1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN

     Pa.SUBGOAL_THEN `(\x. Re (f x) * Re (z x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (z x') pow 2 + Im (z x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+a2-c1)+(b2+b1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
    Pa.SUBGOAL_THEN `(\x. Im (f x) * Im (z x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (f x') pow 2 + Im (f x') pow 2) +
           (Re (z x') pow 2 + Im (z x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (b1+b2-c1)+(a2+a1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC]      THEN
    Pa.SUBGOAL_THEN `(\x. Re (g x) * Re (z x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (g x') pow 2 + Im (g x') pow 2) +
           (Re (z x') pow 2 + Im (z x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (a1+a2-c1)+(b2+b1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC] THEN
    Pa.SUBGOAL_THEN `(\x. Im (g x) * Im (z x)) real_integrable_on (:real):`
         ASSUME_TAC THENL[
         MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE
        THEN Pa.EXISTS_TAC `\x'.inv (&2) * (( Re (g x') pow 2 + Im (g x') pow 2) +
           (Re (z x') pow 2 + Im (z x') pow 2)):`
        THEN ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL;REAL_MEASURABLE_ON_MUL;
        REAL_INTEGRABLE_ADD;REAL_INTEGRABLE_LMUL;REAL_ABS_MUL;REAL_ABS_NUM
        ;REAL_FIELD `x <=  inv (&2) * y <=> &2 * x  <= y`] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        ONCE_REWRITE_TAC[GSYM ABS_POW_2] THEN
        REWRITE_TAC[REAL_ARITH `(((a1:real)+b1)+a2+b2)-c1 = (b1+b2-c1)+(a2+a1)`;
        GSYM SQ_RULE_SUB;REAL_ABS_POW] THEN MESON_TAC[REAL_LE_ADD;REAL_LE_POW_2]
         ;ALL_TAC]       THEN
        IMP_REWRITE_TAC[GSYM REAL_NEG_LMUL;REAL_INTEGRABLE_SUB;
        REAL_INTEGRABLE_NEG;REAL_INTEGRABLE_ADD;
    GSYM REAL_INTEGRAL_LMUL;REAL_INTEGRABLE_LMUL;
        GSYM REAL_INTEGRAL_SUB;GSYM REAL_INTEGRAL_ADD]
        THEN REPEAT STRIP_TAC THEN
     ((AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC)
         ORELSE (MATCH_MP_TAC REAL_INTEGRABLE_LMUL ORELSE ALL_TAC)) THEN
         (MATCH_MP_TAC REAL_INTEGRABLE_SUB ORELSE MATCH_MP_TAC REAL_INTEGRABLE_ADD)
        THEN ASM_SIMP_TAC[REAL_INTEGRABLE_NEG]);;



let SQ_INTEGRABLE_INNER_SPACE = prove
 (`is_inner_space (sq_integrable, r_inprod)`,
  REWRITE_TAC[is_inner_space] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RINPROD_LADD;RINPROD_RSMUL;RINPROD_RSMUL;RINPROD_ZERO_EQ;RINPROD_CNJ;
  RINPROD_SELF_POS;SQ_INTEGRABLE_SUBSPACE]
   );;
