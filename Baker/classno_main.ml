(* ========================================================================= *)
(* The class number one problem: the imaginary quadratic fields of class     *)
(* number one.                                                               *)
(*                                                                           *)
(* Purpose: Baker, Transcendental Number Theory, Theorem 5.1 (Baker 1966,    *)
(* Stark 1967; Heegner 1952): for squarefree d, form_classno (qdisc d) = 1,  *)
(* i.e. the discriminant of Q(sqrt(-d)) has only one reduced primitive form  *)
(* (the class number of Gauss is one), if and only if d is one of 1, 2, 3,   *)
(* 7, 11, 19, 43, 67, 163 (CLASS_NUMBER_ONE). CLASSNO_NO_LARGE: no prime     *)
(* d = 3 mod 8 with d > 46500 has form_classno(-d) = 1: the linear form of   *)
(* CLASSNO_LINEAR_FORM contradicts the Laurent bound                         *)
(* CLASSNO_LAURENT_INSTANCE for d >= 10^16 and the two continued-fraction    *)
(* stages CLASSNO_CF_STAGE1, CLASSNO_CF_STAGE2 for 46500 < d < 10^16.        *)
(* CLASS_NUMBER_ONE_BOUND_LAURENT: form_classno (qdisc d) = 1 implies        *)
(* d < 10^16 (the Laurent bound alone, no continued fractions);              *)
(* CLASS_NUMBER_ONE_FINITE: the set of these d is finite.                    *)
(* CLASS_NUMBER_ONE_FINITE_BAKER: finiteness again, by BAKER_FELDMAN against *)
(* the linear form (the qualitative route of Baker 1966, without the Laurent *)
(* bound and the continued fractions). The small d come from                 *)
(* CLASSNO_ONE_CASES, CLASSNO_NINE, CLASSNO_SEARCH and CLASSNO_WITNESS.      *)
(*                                                                           *)
(* Note: in the comments l1 = log((5 + sqrt 21) / 2),                        *)
(* l2 = log(23 + 4 sqrt 33), s = sqrt d. The numerical inequalities use      *)
(* PI_APPROX_32, the Steiner enclosures of log 2 and log 3 and               *)
(* LAURENT_CORNER_EXP_8_5.                                                   *)
(*                                                                           *)
(* Main results: CLASS_NUMBER_ONE, CLASS_NUMBER_ONE_BOUND_LAURENT,           *)
(* CLASS_NUMBER_ONE_FINITE, CLASS_NUMBER_ONE_FINITE_BAKER, CLASSNO_NO_LARGE; *)
(* CLASSNO_MAIN_INV_EXP (inv X <= lam <= a exp(-y) gives exp y <= a X, also  *)
(* used by Baker/cn_main.ml); helper names CLASSNO_MAIN_*.                   *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (form_classno, qdisc), Baker/classno_forms.ml *)
(* (CLASSNO_ONE_CASES, CLASSNO_NINE, CLASSNO_SEARCH, CLASSNO_WITNESS),       *)
(* Baker/classno_linear.ml (CLASSNO_LINEAR_FORM), Baker/classno_nf.ml        *)
(* (CLASSNO_LAURENT_INSTANCE), Baker/classno_cf.ml (CLASSNO_CF_STAGE1,       *)
(* CLASSNO_CF_STAGE2), Baker/theorem.ml (BAKER_FELDMAN), Baker/bridge.ml     *)
(* (ALGEBRAIC_NUMBER_CX_SQRT and the closure rules), Baker/steiner.ml        *)
(* (STEINER_LOG_2_BOUNDS, STEINER_LOG_3_BOUNDS), Baker/laurent_corner.ml     *)
(* (LAURENT_CORNER_EXP_8_5, LAURENT_CORNER_LOG_BOUNDS,                       *)
(* LAURENT_CORNER_DIV_LE), Baker/twolog.ml (LOG_LE_SUB_1), Baker/lemmas.ml   *)
(* (REAL_POW_DIV_LE_EXP).                                                    *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files, 100/dirichlet.ml before *)
(* Multivariate/gamma.ml), so that the file also loads alone.                *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Multivariate/gamma.ml";;
needs "Baker/theorem.ml";;
needs "Baker/classno_linear.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Elementary analytic tools.                                             *)
(* ------------------------------------------------------------------------- *)

(* (a + log t)^2 <= a^2 t for a >= 2, t >= 1 (log t <= 2 (sqrt t - 1)).      *)

let CLASSNO_MAIN_LOG_SQUARE_LE = prove
 (`!a t. &2 <= a /\ &1 <= t ==> (a + log t) pow 2 <= a pow 2 * t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= sqrt t /\ sqrt t pow 2 = t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log t = &2 * log(sqrt t)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_SQRT; REAL_ARITH `&1 <= (t:real) ==> &0 < t`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(sqrt t) /\ log(sqrt t) <= sqrt t - &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_LE_SUB_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (a - &2) * (sqrt t - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a pow 2 * t = (a * sqrt t) pow 2` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

(* Two-sided bounds for log x from P = 2^a 3^b and log y <= y - 1.           *)

let CLASSNO_MAIN_LOG_POW23_BOUNDS = prove
 (`!x a b. &0 < x
           ==> &a * log(&2) + &b * log(&3) + &1 - (&2 pow a * &3 pow b) / x
               <= log x /\
               log x <= &a * log(&2) + &b * log(&3) +
                        x / (&2 pow a * &3 pow b) - &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `(p:real) = &2 pow a * &3 pow b` THEN
  SUBGOAL_THEN `&0 < (p:real)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log p = &a * log(&2) + &b * log(&3)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW;
             REAL_ARITH `&0 < (&2:real) /\ &0 < (&3:real)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(x / p) <= x / p - &1 /\ log(p / x) <= p / x - &1`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_LE_SUB_1 THEN ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* From c l <= 8800 exp(-y), l >= L > 0, 8800 <= K c L: y <= log K.          *)

let CLASSNO_MAIN_EXP_STAGE = prove
 (`!c L l y K. &0 < c /\ &0 < L /\ &0 < K /\ L <= l /\
              c * l <= &8800 * exp(--y) /\ &8800 <= K * c * L
              ==> y <= log K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (c:real) * (l:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(K:real) * (c:real) * (L:real) <= K * c * (l:real)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp y * c * l <= exp y * &8800 * exp(--y)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(e:real) * &8800 * f = &8800 * e * f`] THEN
  REWRITE_TAC[REAL_EXP_NEG_MUL; REAL_MUL_RID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp y <= K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `c * l:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`exp y`; `K:real`] LOG_MONO_LE_IMP) THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP]);;

(* From exp(-x) <= lam <= 8800 exp(-y): y <= x + 8800 (log 8800 < 8800).     *)

let CLASSNO_MAIN_EXP_COMPARE = prove
 (`!x y lam. exp(--x) <= lam /\ lam <= &8800 * exp(--y) ==> y <= x + &8800`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp(y - x) <= &8800` ASSUME_TAC THENL
   [REWRITE_TAC[real_sub; REAL_EXP_ADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp y * &8800 * exp(--y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `(e:real) * &8800 * f = &8800 * e * f`] THEN
      REWRITE_TAC[REAL_EXP_NEG_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&8800:real` LOG_LT_X) THEN
  MP_TAC(SPECL [`exp(y - x)`; `&8800:real`] LOG_MONO_LE_IMP) THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. Crude enclosures of sqrt 21, sqrt 33, l1 and l2                        *)
(*    (LAURENT_CORNER_EXP_8_5 and the Steiner enclosures of log 2, log 3).   *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_MAIN_SQRT_BOUNDS = prove
 (`&45825 / &10000 <= sqrt(&21) /\ sqrt(&21) <= &45826 / &10000 /\
   &57445 / &10000 <= sqrt(&33) /\ sqrt(&33) <= &57446 / &10000`,
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC REAL_LE_RSQRT ORELSE MATCH_MP_TAC REAL_LE_LSQRT) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let CLASSNO_MAIN_L1_BOUNDS = prove
 (`&1566 / &1000 <= log((&5 + sqrt(&21)) / &2) /\
   log((&5 + sqrt(&21)) / &2) <= &1568 / &1000`,
  MP_TAC CLASSNO_MAIN_SQRT_BOUNDS THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(&5 + sqrt(&21)) / &2`; `(&8:real) / &5`;
                `(&4953:real) / &1000`; `(&4954:real) / &1000`]
    LAURENT_CORNER_LOG_BOUNDS) THEN
  REWRITE_TAC[LAURENT_CORNER_EXP_8_5] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`(&4954:real) / &1000`; `(&4954:real) / &1000`;
                `(&5 + sqrt(&21)) / &2`; `(&479125:real) / &100000`]
    LAURENT_CORNER_DIV_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CLASSNO_MAIN_L2_BOUNDS = prove
 (`&19 / &5 <= log(&23 + &4 * sqrt(&33)) /\
   log(&23 + &4 * sqrt(&33)) <= &39 / &10`,
  MP_TAC CLASSNO_MAIN_SQRT_BOUNDS THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&23 + &4 * sqrt(&33)`; `4`; `1`]
    CLASSNO_MAIN_LOG_POW23_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MP_TAC(SPECL [`&48:real`; `&48:real`; `&23 + &4 * sqrt(&33)`;
                `(&45978:real) / &1000`]
    LAURENT_CORNER_DIV_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC STEINER_LOG_2_BOUNDS THEN MP_TAC STEINER_LOG_3_BOUNDS THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 3. The numerical inequalities: the Laurent bound beats the linear form    *)
(*    for s >= 10^8, and the two continued fraction stages give s < 400,     *)
(*    then s < 215.64.                                                       *)
(* ------------------------------------------------------------------------- *)

(* With bb = b1/(2 l2) + b2/(2 l1) <= 2^34 t, t = s / 10^8 >= 1, and         *)
(* A = 34 log 2 + 0.38: the max is at most A + log t, its square at most     *)
(* A^2 t; so the left side is at most 7.34e6 t < 9.51e6 t <= pi s / 33.      *)

let CLASSNO_MAIN_LAURENT_ARITH = prove
 (`!l1 l2 b1 b2 s.
        &3 / &2 <= l1 /\ l1 <= &1568 / &1000 /\
        &19 / &5 <= l2 /\ l2 <= &39 / &10 /\
        &1 <= b1 /\ &1 <= b2 /\ b1 <= &391 * s /\ b2 <= &160 * s /\
        &10 pow 8 <= s
        ==> &32 * &4 pow 4 *
            max (max (&10 / &4) (&1))
                (log(b1 / (&4 * (l2 / &2)) + b2 / (&4 * (l1 / &2))) +
                 &38 / &100) pow 2 *
            (l1 / &2) * (l2 / &2) + &8800 < pi * s / &33`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `(bb:real) = b1 / (&4 * (l2 / &2)) + b2 / (&4 * (l1 / &2))` THEN
  ABBREV_TAC `(t:real) = s / &10 pow 8` THEN
  SUBGOAL_THEN `&1 <= (t:real) /\ (s:real) = &10 pow 8 * t` STRIP_ASSUME_TAC
  THENL [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (bb:real) /\ bb <= &2 pow 34 * t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`b1:real`; `&391 * (s:real)`; `&4 * ((l2:real) / &2)`;
                  `(&38:real) / &5`] LAURENT_CORNER_DIV_LE) THEN
    MP_TAC(SPECL [`b2:real`; `&160 * (s:real)`; `&4 * ((l1:real) / &2)`;
                  `&3:real`] LAURENT_CORNER_DIV_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (t:real)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(bb) <= &34 * log(&2) + log(t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&2 pow 34 * t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW; REAL_ARITH `&0 < (&2:real)`;
                   REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `(A:real) = &34 * log(&2) + &38 / &100` THEN
  SUBGOAL_THEN `&3 <= (A:real) /\ A <= &2395 / &100` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MP_TAC STEINER_LOG_2_BOUNDS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(t)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `(M:real) = max (max (&10 / &4) (&1)) (log bb + &38 / &100)` THEN
  SUBGOAL_THEN `&0 <= (M:real) /\ M <= A + log t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(M:real) pow 2 <= (&2395 / &100) pow 2 * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(A + log t) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(A:real) pow 2 * t` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CLASSNO_MAIN_LOG_SQUARE_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(M:real) pow 2 * l1 * l2 <=
    ((&2395 / &100) pow 2 * t) * (&1568 / &1000) * (&39 / &10)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&314 / &100 * s <= pi * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Stage 1: 2.329e-11 l1 <= 8800 exp(-pi s/33) gives pi s/33 <= 50 log 2.    *)

let CLASSNO_MAIN_STAGE1_ARITH = prove
 (`!l lam s. &1566 / &1000 <= l /\ &2329 / &10 pow 14 * l <= lam /\
            lam <= &8800 * exp(--(pi * s / &33))
            ==> s < &400`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(&2329:real) / &10 pow 14`; `(&1566:real) / &1000`; `l:real`;
                `pi * s / &33`; `(&2:real) pow 50`] CLASSNO_MAIN_EXP_STAGE) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[LOG_POW; REAL_ARITH `&0 < (&2:real)`] THEN
  ASM_CASES_TAC `(s:real) < &400` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pi * &400 <= pi * s` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[PI_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC STEINER_LOG_2_BOUNDS THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

(* Stage 2: 6.84e-6 l1 <= 8800 exp(-pi s/33) gives pi s/33 <= log K with     *)
(* K = 821551538, log K <= log(2^9 3^13) + K/(2^9 3^13) - 1 < 20.5268.       *)

let CLASSNO_MAIN_STAGE2_ARITH = prove
 (`!l lam s. &1566 / &1000 <= l /\ &684 / &10 pow 8 * l <= lam /\
            lam <= &8800 * exp(--(pi * s / &33))
            ==> s < &21564 / &100`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(s:real) < &21564 / &100` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`(&684:real) / &10 pow 8`; `(&1566:real) / &1000`; `l:real`;
                `pi * s / &33`; `&821551538:real`] CLASSNO_MAIN_EXP_STAGE) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&821551538:real`; `9`; `13`]
    CLASSNO_MAIN_LOG_POW23_BOUNDS) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `pi * &21564 / &100 <= pi * s` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[PI_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC STEINER_LOG_2_BOUNDS THEN MP_TAC STEINER_LOG_3_BOUNDS THEN
  MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. No large d: the Laurent bound for d >= 10^16 and the                   *)
(*    two continued fraction stages for 46500 < d < 10^16.                   *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_MAIN_QDISC = prove
 (`!d. d MOD 8 = 3 ==> qdisc d = --(&d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qdisc] THEN
  MP_TAC(SPECL [`d:num`; `4`; `2`] MOD_MOD) THEN
  REWRITE_TAC[ARITH_RULE `4 * 2 = 8`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[]);;

let CLASSNO_MAIN_LAURENT_LARGE = prove
 (`!d. prime d /\ d MOD 8 = 3 /\ 10 EXP 16 <= d
       ==> ~(form_classno (--(&d)) = 1)`,
  GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d:num` CLASSNO_LINEAR_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:num`; `b2:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b1:num`; `b2:num`] CLASSNO_LAURENT_INSTANCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&10 pow 8 <= sqrt(&d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`log((&5 + sqrt(&21)) / &2)`; `log(&23 + &4 * sqrt(&33))`;
                `&b1:real`; `&b2:real`; `sqrt(&d)`]
    CLASSNO_MAIN_LAURENT_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MP_TAC CLASSNO_MAIN_L1_BOUNDS THEN MP_TAC CLASSNO_MAIN_L2_BOUNDS THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(y:real) <= x + &8800 ==> x + &8800 < y ==> F`) THEN
  MATCH_MP_TAC CLASSNO_MAIN_EXP_COMPARE THEN
  EXISTS_TAC `abs(&b2 * log(&23 + &4 * sqrt(&33)) -
                  &b1 * log((&5 + sqrt(&21)) / &2))` THEN
  ASM_REWRITE_TAC[]);;

let CLASSNO_NO_LARGE = prove
 (`!d. prime d /\ d MOD 8 = 3 /\ 46500 < d ==> ~(form_classno (--(&d)) = 1)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `10 EXP 16 <= d` THENL
   [MP_TAC(SPEC `d:num` CLASSNO_MAIN_LAURENT_LARGE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `d:num` CLASSNO_LINEAR_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:num`; `b2:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&d) < &10 pow 8` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; REAL_POS] THEN
    UNDISCH_TAC `~(10 EXP 16 <= d)` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b2 < 40577071451` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b1:num`; `b2:num`] CLASSNO_CF_STAGE1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(&d) < &400` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_MAIN_STAGE1_ARITH THEN
    MAP_EVERY EXISTS_TAC
     [`log((&5 + sqrt(&21)) / &2)`;
      `abs(&b2 * log(&23 + &4 * sqrt(&33)) -
           &b1 * log((&5 + sqrt(&21)) / &2))`] THEN
    ASM_REWRITE_TAC[CLASSNO_MAIN_L1_BOUNDS];
    ALL_TAC] THEN
  SUBGOAL_THEN `b2 < 130770` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b1:num`; `b2:num`] CLASSNO_CF_STAGE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(&d) < &21564 / &100` MP_TAC THENL
   [MATCH_MP_TAC CLASSNO_MAIN_STAGE2_ARITH THEN
    MAP_EVERY EXISTS_TAC
     [`log((&5 + sqrt(&21)) / &2)`;
      `abs(&b2 * log(&23 + &4 * sqrt(&33)) -
           &b1 * log((&5 + sqrt(&21)) / &2))`] THEN
    ASM_REWRITE_TAC[CLASSNO_MAIN_L1_BOUNDS];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) <= y ==> y < x ==> F`) THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  SUBGOAL_THEN `(&46501:real) <= &d` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 5. The headline theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

let CLASS_NUMBER_ONE_BOUND_LAURENT = prove
 (`!d. squarefree d /\ form_classno (qdisc d) = 1 ==> d < 10 EXP 16`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d:num` CLASSNO_ONE_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
    (SPEC `d:num` CLASSNO_MAIN_LAURENT_LARGE)) THEN
  ASM_SIMP_TAC[GSYM CLASSNO_MAIN_QDISC]);;

let CLASS_NUMBER_ONE_FINITE = prove
 (`FINITE {d | squarefree d /\ form_classno (qdisc d) = 1}`,
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d:num | d < 10 EXP 16}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[CLASS_NUMBER_ONE_BOUND_LAURENT]);;

let CLASS_NUMBER_ONE = prove
 (`!d. squarefree d
      ==> (form_classno (qdisc d) = 1 <=> d IN {1,2,3,7,11,19,43,67,163})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; REWRITE_TAC[CLASSNO_NINE]] THEN
  MP_TAC(SPEC `d:num` CLASSNO_ONE_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN TRY(ASM_REWRITE_TAC[IN_INSERT] THEN NO_TAC) THEN
  SUBGOAL_THEN `qdisc d = --(&d)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [MATCH_MP_TAC CLASSNO_MAIN_QDISC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `d IN {3,11,19,43,67,163}` THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `d <= 46500` THENL
   [MP_TAC(SPEC `d:num` CLASSNO_SEARCH) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`d:num`; `a:int`; `b:int`] CLASSNO_WITNESS) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPEC `d:num` CLASSNO_NO_LARGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Finiteness by the qualitative route (Baker 1966): BAKER_FELDMAN and    *)
(*    CLASSNO_LINEAR_FORM alone (no Laurent bound, no continued fractions).  *)
(* ------------------------------------------------------------------------- *)

(* exp(c s) <= a s^k forces s <= a / (c / (k + 1))^(k + 1) for s > 0.        *)

let CLASSNO_MAIN_EXP_DOMINATES = prove
 (`!c a k. &0 < c
           ==> ?S. !s. &0 < s /\ exp(c * s) <= a * s pow k ==> s <= S`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(a:real) / ((c:real) / &(k + 1)) pow (k + 1)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < ((c:real) / &(k + 1)) pow (k + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `(s:real) pow k` THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(c * s)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c * s:real`; `k + 1`] REAL_POW_DIV_LE_EXP) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) = y ==> x <= e ==> y <= e`) THEN
  REWRITE_TAC[real_div; REAL_POW_MUL; GSYM ADD1; real_pow] THEN
  REAL_ARITH_TAC);;

(* BAKER_FELDMAN for the linear form b2 l2 - b1 l1 (degree 1 data).          *)

let CLASSNO_MAIN_BAKER_LOWER = prove
 (`?C. !b1 b2 B.
        &2 <= B /\ &b1 <= B /\ &b2 <= B /\
        ~(&b2 * log(&23 + &4 * sqrt(&33)) = &b1 * log((&5 + sqrt(&21)) / &2))
        ==> inv(B pow C) <= abs(&b2 * log(&23 + &4 * sqrt(&33)) -
                                &b1 * log((&5 + sqrt(&21)) / &2))`,
  SUBGOAL_THEN `&0 < (&5 + sqrt(&21)) / &2 /\ &0 < &23 + &4 * sqrt(&33)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC CLASSNO_MAIN_SQRT_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `\r. if r = 1 then Cx(log((&5 + sqrt(&21)) / &2))
                          else Cx(log(&23 + &4 * sqrt(&33)))`; `1`]
    BAKER_FELDMAN) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM CX_EXP; EXP_LOG] THEN
    REWRITE_TAC[CX_DIV; CX_ADD; CX_MUL] THEN
    SIMP_TAC[ALGEBRAIC_NUMBER_DIV; ALGEBRAIC_NUMBER_ADD; ALGEBRAIC_NUMBER_MUL;
             ALGEBRAIC_NUMBER_CX_NUM; ALGEBRAIC_NUMBER_CX_SQRT];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`b1:num`; `b2:num`; `B:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`B:real`;
    `\j. Cx(if j = 0 then &0 else if j = 1 then --(&b1) else &b2)`;
    `\j:num. 1`;
    `\j i. if i = 0 then --(if j = 0 then (&0:real) else if j = 1 then --(&b1)
                           else &b2)
           else if i = 1 then &1 else &0`]) THEN
  REWRITE_TAC[VSUM_2; LE_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; COMPLEX_NORM_CX; CX_INJ] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `(x:real) = y ==> i <= abs x ==> i <= abs y`) THEN
    REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_POW_1;
              COMPLEX_MUL_RID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  CONJ_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC] THEN
  X_GEN_TAC `i:num` THEN
  REPEAT COND_CASES_TAC THEN
  SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC);;

(* inv X <= lam <= a exp(-y), X > 0 gives exp y <= a X.                      *)

let CLASSNO_MAIN_INV_EXP = prove
 (`!X y lam a. &0 < X /\ inv X <= lam /\ lam <= a * exp(--y)
               ==> exp y <= a * X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(exp y * X) * inv X <= (exp y * X) * a * exp(--y)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `(e:real) * X * a * f = (a * X) * e * f`] THEN
  REWRITE_TAC[REAL_EXP_NEG_MUL; REAL_MUL_RID]);;

(* Finiteness by the qualitative route (Baker 1966): BAKER_FELDMAN against   *)
(* CLASSNO_LINEAR_FORM (no Laurent bound, no continued fractions).           *)

let CLASS_NUMBER_ONE_FINITE_BAKER = prove
 (`FINITE {d | squarefree d /\ form_classno (qdisc d) = 1}`,
  X_CHOOSE_THEN `C:num` (LABEL_TAC "baker") CLASSNO_MAIN_BAKER_LOWER THEN
  MP_TAC(SPECL [`pi / &33`; `(&8800:real) * &391 pow C`; `C:num`]
    CLASSNO_MAIN_EXP_DOMINATES) THEN
  ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real` (LABEL_TAC "dom")) THEN
  X_CHOOSE_TAC `N:num` (SPEC `max ((S:real) pow 2) (&10000)` REAL_ARCH_SIMPLE)
  THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d:num | d <= N}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `10000 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `d:num` CLASSNO_ONE_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `form_classno (--(&d)) = 1` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLASSNO_MAIN_QDISC]; ALL_TAC] THEN
  MP_TAC(SPEC `d:num` CLASSNO_LINEAR_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:num`; `b2:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&100 <= sqrt(&d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "baker" (MP_TAC o SPECL [`b1:num`; `b2:num`;
                                       `&391 * sqrt(&d)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `exp(pi * sqrt(&d) / &33) <= &8800 * (&391 * sqrt(&d)) pow C`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_MAIN_INV_EXP THEN
    EXISTS_TAC `abs(&b2 * log(&23 + &4 * sqrt(&33)) -
                    &b1 * log((&5 + sqrt(&21)) / &2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&d) <= S` ASSUME_TAC THENL
   [REMOVE_THEN "dom" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `pi / &33 * s = pi * s / &33`;
                GSYM REAL_MUL_ASSOC; GSYM REAL_POW_MUL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&d:real) <= &N` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(S:real) pow 2` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(&d:real) = sqrt(&d) pow 2` SUBST1_TAC THENL
       [SIMP_TAC[SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;
