(* ========================================================================= *)
(* Sharpening I: the numeric layer.                                          *)
(*                                                                           *)
(* Purpose: the choice of the parameters of the parametric core              *)
(* SHARP_CORE_PARAMETRIC (Baker/sharp_core.ml) for n principal logarithms of *)
(* algebraic numbers of degree at most D: the design facts shared by the two *)
(* endings (SHARP_CORE_DESIGN) and the ending for integer coefficients, the  *)
(* core property sharp_core_property_alg n D C K cB (SHARP_CORE_ALGEBRAIC).  *)
(* The design is the Q-power design for rational data with the radius        *)
(* Q^(8 c) instead of Q^8 in the extrapolation steps and at Lemma 8, c = D^n *)
(* for integer coefficients (c = 2 D^(2n) for algebraic coefficients,        *)
(* Baker/sharpc_num.ml). The radius must grow with D: the Liouville bound    *)
(* sharp_liou5 contains the denominator (e^19 (l + h) / h)^(h S0) about      *)
(* nproduct dd times, so in the first step (R 0 = h, R 1 = h Q) the loss is  *)
(* about c h S0 log Q, while the radius Q^8 only gains                       *)
(* 8 R(0) (S(1) + 1) log Q, about 4 h S0 log Q. With the radius Q^(8 c) the  *)
(* gain is 8 c h S0 / 2 log Q (SHARP_STEP_INEQ_ALG); correspondingly         *)
(* a = (8 c + 3) n, S0 = gN Q^(a + 8 c + 3) (Siegel count),                  *)
(* J = (a + 1)(n + 2) and e = J + 72 n + 256 + 8 c (Q = 2^e g0N, absorbing   *)
(* every factor polynomial in c). For D = 1 the radius, a and S0 are those   *)
(* of the design for rational data. The constants of SHARP_CORE_ALGEBRAIC    *)
(* are C = 2^((e + 1) M + 9) (D + 6), K = M = J + a + 8 c + 3 and            *)
(* cB = 2^(70 + (e + 1)(a + 1)).                                             *)
(*                                                                           *)
(* Parts 1 and 2: generic estimates with all parameters as variables         *)
(*   (exponential bounds for the size functions of the core, estimates in    *)
(*   the powers of Q, the log-domain and Lemma 8 exponent inequalities,      *)
(*   counting). Part A: bounds for principal logarithms of roots of integer  *)
(*   polynomials. Part B: exponential bounds for the generic bound functions *)
(*   sharp_psize, sharp_liou5, sharp_lb8 of Baker/sharp_defs.ml at the       *)
(*   integer instance (the body lemmas SHARP_PSIZE_INT_BODY,                 *)
(*   SHARP_LIOU5_INT_BODY, SHARP_LB8_INT_BODY are the only lemmas that       *)
(*   unfold them). Part C: the parameter design. Part D: the extrapolation   *)
(*   step and Lemma 8. Part E: the step and Lemma 8 hypotheses of the        *)
(*   parametric core, the design facts SHARP_CORE_DESIGN, the data lemma     *)
(*   SHARP_CORE_DATA_ALG and SHARP_CORE_ALGEBRAIC.                           *)
(*                                                                           *)
(* Main results: SHARP_CORE_ALGEBRAIC, SHARP_CORE_DATA_ALG,                  *)
(*   SHARP_CORE_DESIGN (the numeric hypotheses of SHARP_CORE_PARAMETRIC in   *)
(*   the integer form, for any analytic size Bq and degree data dd1; used by *)
(*   both endings); SHARP_ALGDATA_LG_BOUND (|z| <= log H + D + 4 for a       *)
(*   principal logarithm z of a root of an integer polynomial of degree <= D *)
(*   and height <= H), SHARP_PSIZE_ALG_LE_EXP, SHARP_LIOU5_ALG_GE_EXP,       *)
(*   SHARP_LB8_ALG_GE_EXP (the bound functions at the integer instance in    *)
(*   exponential form), SHARP_STEP_COND_ALG, SHARP_LEMMA8_COND_ALG (the step *)
(*   and Lemma 8 hypotheses of the parametric core), the body lemmas,        *)
(*   SHARP_LEMMA8_LOGINEQ_GEN; the generic SHARP_UBD_LE_EXP,                 *)
(*   SHARP_ERRB_LE_EXP, SHARP_STEP_ABS, SHARP_LEMMA8_ABS, SHARP_MEXPR_LE,    *)
(*   SHARP_ERR_INEQ, SHARP_FINAL_U.                                          *)
(*                                                                           *)
(* Uses: Baker/sharp_defs.ml (sharp_index, sharp_algdata, sharp_psize,       *)
(*   sharp_liou5, sharp_lb8, sharp_ubd, sharp_errb, sharp_lv, sharp_omega,   *)
(*   sharp_core_property_alg), Baker/sharp_core.ml (SHARP_CORE_PARAMETRIC),  *)
(*   Baker/sharp_aux.ml (CARD_SHARP_INDEX, SHARP_OMEGA_BOUNDS),              *)
(*   Baker/sharp_arith.ml (SHARP_DELTAREP_INT, REAL_LE_MUL_5,                *)
(*   REAL_LE_MUL_6), Baker/sharp_sec4.ml                                     *)
(*   (COMPLEX_SUBFIELD_GENERATED_UNION_RATIONAL), Baker/uniform.ml           *)
(*   (SHARPC_COEFDATA_INTEGER), Baker/liouville_inequality.ml                *)
(*   (INTEGER_POLY_ROOT_BOUND), Baker/simple.ml                              *)
(*   (ALGEBRAIC_ROOT_LOWER_BOUND), Baker/sharp_poly.ml (PRIME_IN_INTERVAL),  *)
(*   Baker/numeric_dmax.ml (REAL_NUM_CEIL), Baker/lemmas.ml (REAL_LE_1_MUL,  *)
(*   REAL_TWO_POW_LE_EXP, LOG_2_LE_1), Baker/bounds.ml (FACT_LE_SELF_EXP),   *)
(*   Baker/estimates.ml (LOG_LE_SELF).                                       *)
(* ========================================================================= *)

needs "Baker/simple.ml";;
needs "Baker/sharp_core.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Part 1. Generic estimates for the parameter design of Parts C to E (all   *)
(* parameters are variables): exponential bounds for the size functions of   *)
(* the core.                                                                 *)
(* ------------------------------------------------------------------------- *)

let REAL_POW_EXP_LOG = prove
 (`!x k. &0 < x ==> x pow k = exp(&k * log x)`,
  SIMP_TAC[REAL_EXP_N; EXP_LOG]);;

let PRODUCT_POW_EXP_SUM = prove
 (`!n (Hb:num->real) (Lv:num->num) l.
     (!r. r IN 1..n ==> &0 < Hb r)
     ==> product(1..n) (\r. Hb r pow (Lv r * l)) =
         exp(&l * sum(1..n) (\r. &(Lv r) * log(Hb r)))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM SUM_LMUL; REAL_EXP_SUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (Hb:num->real) r` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_EXP_LOG] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC);;

let SUM_LV_LOG_POS = prove
 (`!n (Hb:num->real) (Lv:num->num).
     (!r. r IN 1..n ==> &1 <= Hb r)
     ==> &0 <= sum(1..n) (\r. &(Lv r) * log(Hb r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC LOG_POS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_NUMSEG]);;

let CARD_SHARP_INDEX_LE_EXP = prove
 (`!h L0 Lv n Lm.
     (!r. r IN 1..n ==> Lv r <= Lm)
     ==> &(CARD(sharp_index h L0 Lv n)) <= exp(&h + &L0 + &n * &Lm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CARD_SHARP_INDEX] THEN
  TRANS_TAC REAL_LE_TRANS `&2 pow (h + L0 + n * Lm)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; EXP_ADD] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
     [MESON_TAC[LT_POW2_REFL; LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
     [MESON_TAC[LT_POW2_REFL; ARITH_RULE `a < b ==> a + 1 <= b`]; ALL_TAC] THEN
    TRANS_TAC LE_TRANS `nproduct(1..n) (\r. 2 EXP Lm)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN
      STRIP_TAC THEN REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `Lm + 1` THEN CONJ_TAC THENL
       [REWRITE_TAC[LE_ADD_RCANCEL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_NUMSEG];
        MESON_TAC[LT_POW2_REFL; ARITH_RULE `a < b ==> a + 1 <= b`]];
      REWRITE_TAC[NPRODUCT_CONST_NUMSEG_1; GSYM EXP_MULT] THEN
      REWRITE_TAC[MULT_SYM; LE_REFL]];
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_TWO_POW_LE_EXP]]);;

let SHARP_UBD_LE_EXP = prove
 (`!n h L0 Lv Lm P B S0 T0 N z Ec Ep.
     &1 <= B /\ &0 <= P /\ P <= exp Ep /\
     &(CARD(sharp_index h L0 Lv n)) <= exp Ec
     ==> sharp_ubd n h L0 Lv Lm P B S0 T0 N z <=
         exp(Ec + Ep + &((L0 + 2) * (N + h)) +
             &S0 * log(&4 * B + &2) + &((n - 1) * Lm) + z * T0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_ubd; REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_MUL_6 THEN
  ASM_SIMP_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_LE_REFL; REAL_TWO_POW_LE_EXP;
               REAL_POW_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_POW_EXP_LOG THEN
    ASM_REAL_ARITH_TAC]);;

let SHARP_ERRB_LE_EXP = prove
 (`!n h L0 Lv Lm P B S0 T0 d0 N z Ec Ep Nmax zmax.
     &1 <= B /\ &0 <= P /\ P <= exp Ep /\
     &(CARD(sharp_index h L0 Lv n)) <= exp Ec /\
     &0 <= T0 /\ &0 <= d0 /\ &0 <= z /\ z <= zmax /\ N <= Nmax
     ==> sharp_errb n h L0 Lv Lm P B S0 T0 d0 N z <=
         exp(Ec + Ep + &((L0 + 2) * (Nmax + h)) +
             &S0 * log(&4 * B + &2) + &((n - 1) * Lm) + zmax * (T0 + d0)) *
         (zmax * d0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_errb] THEN
  TRANS_TAC REAL_LE_TRANS
   `exp Ec * exp Ep * exp(&((L0 + 2) * (Nmax + h))) *
    exp(&S0 * log(&4 * B + &2)) * exp(&((n - 1) * Lm)) *
    (zmax * d0 * exp(zmax * (T0 + d0)))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[REAL_EXP_ADD] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL_6 THEN
  ASM_SIMP_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_LE_REFL;
               REAL_TWO_POW_LE_EXP] THEN
  REPEAT CONJ_TAC THEN FIRST
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC THEN NO_TAC;
    TRANS_TAC REAL_LE_TRANS `&2 pow ((L0 + 2) * (Nmax + h))` THEN
    REWRITE_TAC[REAL_TWO_POW_LE_EXP] THEN MATCH_MP_TAC REAL_POW_MONO THEN
    REWRITE_TAC[REAL_ARITH `&1 <= &2`; LE_MULT_LCANCEL; LE_ADD_RCANCEL] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_POW_EXP_LOG THEN
    ASM_REAL_ARITH_TAC THEN NO_TAC;
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN NO_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]);;

let SIXTEEN_POW_LE_EXP = prove
 (`!k. &16 pow k <= exp(&4 * &k)`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `&16 = &2 pow 4`; REAL_POW_POW] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_TWO_POW_LE_EXP]);;

let EXP_NEG_SMALL = prove
 (`!x. &2 * exp(--(x + &3)) + exp(--(x + &2)) + exp(--(x + &2)) < exp(--x)`,
  GEN_TAC THEN REWRITE_TAC[REAL_NEG_ADD; REAL_EXP_ADD] THEN
  SUBGOAL_THEN `&4 <= exp(&2) /\ &8 <= exp(&3)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&4 = &2 pow 2 /\ &8 = &2 pow 3`] THEN
    REWRITE_TAC[REAL_TWO_POW_LE_EXP];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  SUBGOAL_THEN `&0 < exp(x)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(exp(&2)) <= inv(&4) /\ inv(exp(&3)) <= inv(&8)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(exp x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(exp x) * inv(exp(&2)) <= inv(exp x) * inv(&4) /\
    inv(exp x) * inv(exp(&3)) <= inv(exp x) * inv(&8)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SHARP_STEP_ABS = prove
 (`!ub rho R R1 S1 cst Qr Eu Ev E.
     1 <= R /\ 1 <= R1 /\ &1 < Qr /\ &0 <= ub /\ ub <= exp Eu /\
     &4 * &R1 / rho = inv(Qr pow 8) /\
     Eu + Ev + &3 <= &8 * &R * (&S1 + &1) * log Qr /\
     log(&2 * &R) + &S1 + cst + (&S1 + &1) * (log(&R1) + &4 * &R1) + Ev + &2
     <= E
     ==> &2 * ub * (&4 * &R1 / rho) pow (R * (S1 + 1)) +
         exp(--E) * &2 * &R * &2 pow S1 * exp(cst) *
         (&R1 * &16 pow R1) pow (S1 + 1)
         <= exp(--Ev)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < Qr /\ &0 < &R /\ &0 < &R1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(Qr pow 8) pow (R * (S1 + 1)) =
    exp(--(&8 * &R * (&S1 + &1) * log Qr))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_INV; REAL_POW_POW; REAL_POW_EXP_LOG;
                 GSYM REAL_EXP_NEG] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * ub * exp(--(&8 * &R * (&S1 + &1) * log Qr)) <=
    &2 * exp(--(Ev + &3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &2`] THEN
    TRANS_TAC REAL_LE_TRANS
     `exp Eu * exp(--(&8 * &R * (&S1 + &1) * log Qr))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--E) * &2 * &R * &2 pow S1 * exp(cst) *
    (&R1 * &16 pow R1) pow (S1 + 1) <= exp(--(Ev + &2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * &R /\ &0 < &16 pow R1 /\ &0 < &R1 * &16 pow R1`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &16 pow R1` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < &2`];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `exp(--E) * exp(log(&2 * &R)) * exp(&S1) * exp(cst) *
      exp((&S1 + &1) * (log(&R1) + &4 * &R1))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC] THEN
    SUBST1_TAC(REAL_ARITH
     `exp(--E) * &2 * &R * &2 pow S1 * exp(cst) *
      (&R1 * &16 pow R1) pow (S1 + 1) =
      exp(--E) * (&2 * &R) * &2 pow S1 * exp(cst) *
      (&R1 * &16 pow R1) pow (S1 + 1)`) THEN
    MATCH_MP_TAC REAL_LE_MUL_5 THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_EXP_POS_LE; REAL_LE_REFL; REAL_TWO_POW_LE_EXP;
                 REAL_LT_IMP_LE; REAL_POW_LE; REAL_POW_EXP_LOG;
                 REAL_EXP_MONO_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_LE_LADD] THEN
    SUBST1_TAC(SYM(SPEC `&4 * &R1` LOG_EXP)) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[SIXTEEN_POW_LE_EXP];
    ALL_TAC] THEN
  MP_TAC(SPEC `Ev:real` EXP_NEG_SMALL) THEN
  SUBGOAL_THEN `&0 <= exp(--(Ev + &2))` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SHARP_LEMMA8_ABS = prove
 (`!ub rhoX X Y pr cst Qr Eu E8 E err lb.
     1 <= X /\ 1 <= pr /\ &1 < Qr /\ &0 <= ub /\ ub <= exp Eu /\
     &4 * &X / rhoX = inv(Qr pow 8) /\
     err <= exp(--(E8 + &2)) /\ exp(--E8) <= lb /\
     Eu + E8 + &3 <= &8 * &X * (&Y + &1) * log Qr /\
     log(&2 * &pr * &X) + &Y * log(&2 * &pr) + cst +
     (&Y + &1) * (log(&X) + &4 * &X) + E8 + &2 <= E
     ==> (&2 * ub * (&4 * &X / rhoX) pow (X * (Y + 1)) +
          exp(--E) * &2 * &pr * &X * (&2 * &pr) pow Y * exp(cst) *
          (&X * &16 pow X) pow (Y + 1)) + err < lb`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < Qr /\ &0 < &X /\ &0 < &pr` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(Qr pow 8) pow (X * (Y + 1)) =
    exp(--(&8 * &X * (&Y + &1) * log Qr))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_INV; REAL_POW_POW; REAL_POW_EXP_LOG;
                 GSYM REAL_EXP_NEG] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * ub * exp(--(&8 * &X * (&Y + &1) * log Qr)) <=
    &2 * exp(--(E8 + &3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &2`] THEN
    TRANS_TAC REAL_LE_TRANS
     `exp Eu * exp(--(&8 * &X * (&Y + &1) * log Qr))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--E) * &2 * &pr * &X * (&2 * &pr) pow Y * exp(cst) *
    (&X * &16 pow X) pow (Y + 1) <= exp(--(E8 + &2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 < &2 * &pr * &X /\ &0 < &2 * &pr /\ &0 < &16 pow X /\
      &0 < &X * &16 pow X`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &16 pow X` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < &2`];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `exp(--E) * exp(log(&2 * &pr * &X)) * exp(&Y * log(&2 * &pr)) *
      exp(cst) * exp((&Y + &1) * (log(&X) + &4 * &X))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC] THEN
    SUBST1_TAC(REAL_ARITH
     `exp(--E) * &2 * &pr * &X * (&2 * &pr) pow Y * exp(cst) *
      (&X * &16 pow X) pow (Y + 1) =
      exp(--E) * (&2 * &pr * &X) * (&2 * &pr) pow Y * exp(cst) *
      (&X * &16 pow X) pow (Y + 1)`) THEN
    MATCH_MP_TAC REAL_LE_MUL_5 THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_EXP_POS_LE; REAL_LE_REFL;
                 REAL_LT_IMP_LE; REAL_POW_LE; REAL_POW_EXP_LOG;
                 REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_LE_LADD] THEN
    SUBST1_TAC(SYM(SPEC `&4 * &X` LOG_EXP)) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[SIXTEEN_POW_LE_EXP];
    ALL_TAC] THEN
  MP_TAC(SPEC `E8:real` EXP_NEG_SMALL) THEN
  SUBGOAL_THEN `&0 <= exp(--(E8 + &2))` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 2. Estimates in the powers of Q = 2^e g0N (SHARP_QPOW_GE,            *)
(* SHARP_Q_BASIC) and for the unit of small quantities sg = (n + 1) u,       *)
(* S0 = q10 u (SHARP_SG_AUX).                                                *)
(* ------------------------------------------------------------------------- *)

let SHARP_QPOW_GE = prove
 (`!e g0N Q m k. 1 <= g0N /\ Q = 2 EXP e * g0N /\ k <= e * m
                 ==> &2 pow k <= &Q pow m`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `&2 pow (e * m)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `2 EXP e * 1 <= 2 EXP e * g0N` MP_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL]; REWRITE_TAC[MULT_CLAUSES]]);;

let SHARP_Q_BASIC = prove
 (`!e g0N Q. 1 <= g0N /\ Q = 2 EXP e * g0N /\ 256 <= e
             ==> &2 <= &Q /\ &1 <= &Q /\ &0 < &Q /\ &128 <= log(&Q) /\
                 log(&Q) <= &Q /\ &(g0N) <= &Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 pow e <= &Q` ASSUME_TAC THENL
   [MP_TAC(SPECL [`e:num`; `g0N:num`; `Q:num`; `1`; `e:num`]
      SHARP_QPOW_GE) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; LE_REFL; REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= &2 pow e` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `log(&2 pow e)` THEN CONJ_TAC THENL
     [SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`] THEN
      TRANS_TAC REAL_LE_TRANS `&e * &1 / &2` THEN CONJ_TAC THENL
       [UNDISCH_TAC `256 <= e` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN
          REWRITE_TAC[REAL_POS; CONJUNCT1 LOG_2_BOUNDS]];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[LOG_LE_SELF];
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `1 * g0N <= 2 EXP e * g0N` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN ARITH_TAC;
      REWRITE_TAC[MULT_CLAUSES]]]);;

let SHARP_SG_AUX = prove
 (`!n L Ln Lm S0 u sg q10.
     1 <= n /\ &1 <= u /\ &L <= u /\ &Ln <= u /\ &Lm = u /\
     &S0 = q10 * u /\ &2 <= q10 /\ &n + &1 <= q10 /\ sg = (&n + &1) * u
     ==> &1 <= sg /\ &L <= sg /\ &L + &2 <= &3 * sg /\ &Lm <= sg /\
         &n * &Lm <= sg /\ &((n - 1) * Lm) <= sg /\ &Ln <= sg /\
         &((n - 1) * L) <= sg /\ &n <= sg /\ &2 <= &S0 /\ sg <= &S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * u <= &S0 /\ &0 <= &n * u /\ &(n - 1) * u <= &n * u /\
                &n <= &n * u /\ &(n - 1) * &L <= &(n - 1) * u /\
                (&n + &1) * u <= q10 * u`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The log-domain inequalities: Ec, Ep bound log CARD and log P              *)
(* (SHARP_EP_BOUND), and at the points l/pr the error terms add up to at     *)
(* most 16 X S0, the exponent of eps (SHARP_LEMMA8_EPSINEQ).                 *)
(* ------------------------------------------------------------------------- *)

let SHARP_EP_BOUND = prove
 (`!n h S0 sg Ec Ep lB T0 L Lm.
     1 <= h /\ &1 <= sg /\ &L + &2 <= &3 * sg /\ &L <= sg /\
     &n * &Lm <= sg /\ &((n - 1) * Lm) <= sg /\ &14 * sg <= &S0 /\
     Ec = &h + &L + &n * &Lm /\
     Ep = Ec + &36 * &h * &S0 + &((L + 2) * (2 * h + 1)) + &S0 * lB +
          &((n - 1) * Lm) + &h * T0 /\
     &0 <= lB /\ lB <= &h /\ &0 <= T0 /\ T0 <= sg
     ==> Ec <= &3 * &h * sg /\ Ep <= &38 * &h * &S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &h` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sg <= &h * sg /\ &h <= &h * sg /\
    &((L + 2) * (2 * h + 1)) <= (&3 * sg) * (&3 * &h) /\
    &S0 * lB <= &S0 * &h /\ &h * T0 <= &h * sg /\
    &h * (&14 * sg) <= &h * &S0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ec <= &3 * &h * sg` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `Ec <= &3 * &h * sg` THEN UNDISCH_TAC `&h <= &h * sg` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SHARP_LEMMA8_EPSINEQ = prove
 (`!S0 X Y pr Nl E8.
     &2 * &pr <= &S0 /\ &2 * &pr <= &X /\ Nl <= X /\ Y + 1 <= S0 /\
     1 <= X /\ 1 <= pr /\ 2 <= S0 /\ E8 <= &X * &S0
     ==> log(&2 * &pr * &X) + &Y * log(&2 * &pr) + &(S0 * Nl) +
         (&Y + &1) * (log(&X) + &4 * &X) + E8 + &2 <= &16 * &X * &S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &X /\ &1 <= &pr /\ &2 <= &S0 /\ &Nl <= &X /\ &Y + &1 <=
    &S0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * &pr * &X) <= &X * &S0 /\
                &Y * log(&2 * &pr) <= &X * &S0 /\
                &(S0 * Nl) <= &X * &S0 /\
                (&Y + &1) * (log(&X) + &4 * &X) <= &5 * &X * &S0 /\
                &2 <= &X * &S0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * &pr /\ &0 < &2 * &pr * &X /\ &0 <= log(&X) /\
                  log(&X) <= &X /\ log(&2 * &pr) <= &2 * &pr`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_LE_SELF THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_LE_SELF THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&2 * &pr * &X` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_LE_SELF THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[REAL_ARITH `&2 * p * x = x * (&2 * p)`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      TRANS_TAC REAL_LE_TRANS `&S0 * &X` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
        REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      TRANS_TAC REAL_LE_TRANS `&S0 * (&5 * &X)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      TRANS_TAC REAL_LE_TRANS `&1 * &2` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `E8 <= &X * &S0` THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Lemma 8 exponent EM: the product of the Lemma 8 factors is at most    *)
(* exp(EM) (SHARP_MEXPR_LE), EM is monotone in l and m (SHARP_EM_MONO), and  *)
(* n log pr + EM is bounded by the design quantities (SHARP_EMMAX_BOUND).    *)
(* ------------------------------------------------------------------------- *)

let SHARP_MEXPR_LE = prove
 (`!n h L0 Lv Lm P B (Hb:num->real) (m:num->num) l pr Nz Ec Ep T0.
     1 <= pr /\ &1 <= B /\ &0 <= P /\ P <= exp Ep /\
     &(CARD(sharp_index h L0 Lv n)) <= exp Ec /\ &0 <= Ec /\ &0 <= Ep /\
     (!r. r IN 1..n ==> &1 <= Hb r /\ Lv r <= Lm) /\
     sum(1..n) (\r. &(Lv r) * log(Hb r)) <= T0
     ==> (&(CARD(sharp_index h L0 Lv n)) * P *
          (&pr pow (2 * h * (L0 + 2)) * exp(&18 * &(l + pr * h)) pow (m 0)) *
          &2 pow ((L0 + 2) * (Nz + h)) *
          (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * Lm)) *
         product(1..n) (\r. Hb r pow (Lv r * l)) *
         product(1..n) (\r. (Hb r * (&1 + &pr * Hb r)) pow (Lv r * l))
         <= exp(Ec + Ep + &(2 * h * (L0 + 2)) * log(&pr) +
                &(m 0) * (&18 * &(l + pr * h)) + &((L0 + 2) * (Nz + h)) +
                &(nsum(1..n-1) m) * log(&4 * B + &2) + &((n - 1) * Lm) +
                &l * T0 + &l * (&2 * T0 + &n * &Lm * log(&1 + &pr))) /\
         product(1..n) (\r. Hb r pow (Lv r * l)) *
         (&pr pow (2 * h * (L0 + 2)) * exp(&18 * &(l + pr * h)) pow (m 0))
         <= exp(Ec + Ep + &(2 * h * (L0 + 2)) * log(&pr) +
                &(m 0) * (&18 * &(l + pr * h)) + &((L0 + 2) * (Nz + h)) +
                &(nsum(1..n-1) m) * log(&4 * B + &2) + &((n - 1) * Lm) +
                &l * T0 + &l * (&2 * T0 + &n * &Lm * log(&1 + &pr))) /\
         &0 <= Ec + Ep + &(2 * h * (L0 + 2)) * log(&pr) +
                &(m 0) * (&18 * &(l + pr * h)) + &((L0 + 2) * (Nz + h)) +
                &(nsum(1..n-1) m) * log(&4 * B + &2) + &((n - 1) * Lm) +
                &l * T0 + &l * (&2 * T0 + &n * &Lm * log(&1 + &pr)) /\
         &0 < product(1..n) (\r. Hb r pow (Lv r * l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r IN 1..n ==> &0 < (Hb:num->real) r` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `&1 <= x ==> &0 < x`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &pr /\ &1 <= &pr /\ &0 <= log(&pr) /\ &0 <= log(&1 +
    &pr) /\
                &0 <= log(&4 * B + &2) /\ &0 <= T0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &pr` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    TRY(MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC) THEN
    TRANS_TAC REAL_LE_TRANS `sum(1..n) (\r. &(Lv r) *
      log((Hb:num->real) r))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LV_LOG_POS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `A1 = &(2 * h * (L0 + 2)) * log(&pr)` THEN
  ABBREV_TAC `A2 = &(m 0) * (&18 * &(l + pr * h))` THEN
  ABBREV_TAC `A3 = &((L0 + 2) * (Nz + h))` THEN
  ABBREV_TAC `A4 = &(nsum(1..n-1) m) * log(&4 * B + &2)` THEN
  ABBREV_TAC `A5 = &((n - 1) * Lm)` THEN
  ABBREV_TAC `A6 = &l * T0` THEN
  ABBREV_TAC `A7 = &l * (&2 * T0 + &n * &Lm * log(&1 + &pr))` THEN
  SUBGOAL_THEN `&0 <= A1 /\ &0 <= A2 /\ &0 <= A3 /\ &0 <= A4 /\ &0 <= A5 /\
                &0 <= A6 /\ &0 <= A7`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A1"; "A2"; "A3"; "A4"; "A5"; "A6"; "A7"] THEN
    REPEAT CONJ_TAC THEN REWRITE_TAC[REAL_POS] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN TRY REAL_ARITH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= &2 * x + y`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&pr pow (2 * h * (L0 + 2)) = exp A1 /\
                exp(&18 * &(l + pr * h)) pow (m 0) = exp A2 /\
                &2 pow ((L0 + 2) * (Nz + h)) <= exp A3 /\
                (&4 * B + &2) pow (nsum(1..n-1) m) = exp A4 /\
                &2 pow ((n - 1) * Lm) <= exp A5`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A1"; "A2"; "A3"; "A4"; "A5"] THEN
    REWRITE_TAC[REAL_EXP_N; REAL_TWO_POW_LE_EXP] THEN
    SUBGOAL_THEN `&0 < &4 * B + &2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[EXP_LOG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `product(1..n) (\r. (Hb:num->real) r pow (Lv r * l)) <= exp A6 /\
                &0 < product(1..n) (\r. (Hb:num->real) r pow (Lv r * l))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRODUCT_POW_EXP_SUM; REAL_EXP_POS_LT] THEN
    EXPAND_TAC "A6" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product(1..n) (\r. ((Hb:num->real) r * (&1 + &pr * Hb r)) pow (Lv r * l))
    <= exp A7`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `\r. (Hb:num->real) r * (&1 + &pr * Hb r)`;
                   `Lv:num->num`; `l:num`] PRODUCT_POW_EXP_SUM) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (Hb:num->real) r` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "A7" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum(1..n) (\r. &2 * (&(Lv r) * log((Hb:num->real) r)) +
                     log(&1 + &pr) * &(Lv r))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `&1 <= (Hb:num->real) r /\ Lv r <= Lm` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && free_in `Lm:num` (concl th))) THEN
        ASM_REWRITE_TAC[IN_NUMSEG];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (Hb:num->real) r /\ &0 < &1 + &pr * Hb r`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_MUL] THEN
      SUBGOAL_THEN `log(&1 + &pr * (Hb:num->real) r) <= log(&1 + &pr) +
        log(Hb r)`
      MP_TAC THENL
       [SUBGOAL_THEN `&0 < &1 + &pr` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[GSYM LOG_MUL] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `&(Lv r) * log(&1 + &pr * (Hb:num->real) r) <=
                    &(Lv r) * (log(&1 + &pr) + log(Hb r))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
    SUBGOAL_THEN `sum(1..n) (\r. &((Lv:num->num) r)) <= &n * &Lm` MP_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `sum(1..n) (\r:num. &Lm)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[IN_NUMSEG];
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `log(&1 + &pr) * sum(1..n) (\r. &((Lv:num->num) r)) <=
                  log(&1 + &pr) * (&n * &Lm)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `sum(1..n) (\r. &((Lv:num->num) r) * log((Hb:num->real) r)) <=
      T0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product(1..n) (\r. ((Hb:num->real) r * (&1 + &pr *
    Hb r)) pow (Lv r * l))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN
    SUBGOAL_THEN `&0 < (Hb:num->real) r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `exp(Ec + Ep + A1 + A2 + A3 + A4 + A5 + A6 + A7) =
                  (exp Ec * exp Ep * (exp A1 * exp A2) * exp A3 * exp A4 *
                   exp A5) * exp A6 * exp A7` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_EXP_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL_6 THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_LE_REFL] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE THEN
        REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS `exp A6 * exp A1 * exp A2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let SHARP_EM_MONO = prove
 (`!n h L0 Lm (m:num->num) l pr B Ec Ep T0.
     m 0 <= L0 /\ nsum(1..n-1) m <= (n - 1) * L0 /\ l <= 4 * h /\
     &1 <= B /\ 1 <= pr /\ &0 <= T0
     ==> Ec + Ep + &(2 * h * (L0 + 2)) * log(&pr) +
         &(m 0) * (&18 * &(l + pr * h)) + &((L0 + 2) * ((l + 1) + h)) +
         &(nsum(1..n-1) m) * log(&4 * B + &2) + &((n - 1) * Lm) +
         &l * T0 + &l * (&2 * T0 + &n * &Lm * log(&1 + &pr))
         <= Ec + Ep + &(2 * h * (L0 + 2)) * log(&pr) +
            &L0 * (&18 * &(4 * h + pr * h)) +
            &((L0 + 2) * ((4 * h + 1) + h)) +
            &((n - 1) * L0) * log(&4 * B + &2) + &((n - 1) * Lm) +
            &(4 * h) * T0 + &(4 * h) * (&2 * T0 + &n * &Lm * log(&1 + &pr))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log(&4 * B + &2) /\ &0 <= log(&1 +
    &pr)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    MP_TAC(SPEC `pr:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(m 0) * (&18 * &(l + pr * h)) <= &L0 * (&18 * &(4 * h + pr *
    h)) /\
                &((L0 + 2) * ((l + 1) + h)) <= &((L0 + 2) * ((4 * h + 1) +
                  h)) /\
                &(nsum(1..n-1) m) * log(&4 * B + &2) <=
                &((n - 1) * L0) * log(&4 * B + &2) /\
                &l * T0 <= &(4 * h) * T0 /\
                &l * (&2 * T0 + &n * &Lm * log(&1 + &pr)) <=
                &(4 * h) * (&2 * T0 + &n * &Lm * log(&1 + &pr))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_POS];
        ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_ARITH `&0 <= &18`] THEN
        ASM_ARITH_TAC];
      REWRITE_TAC[REAL_OF_NUM_LE; LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= &2 * x + y`) THEN
      ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SHARP_EMMAX_BOUND = prove
 (`!n h L0 Lm pr B Ec Ep T0 S0 sg.
     1 <= h /\ 1 <= pr /\ &1 <= B /\ &1 <= sg /\
     Ec <= &3 * &h * sg /\ Ep <= &38 * &h * &S0 /\
     &L0 + &2 <= &3 * sg /\ &L0 <= sg /\ &n * &Lm <= sg /\
     &((n - 1) * L0) <= sg /\ &((n - 1) * Lm) <= sg /\ &n <= sg /\
     &0 <= T0 /\ T0 <= sg /\ log(&4 * B + &2) <= &h
     ==> &n * log(&pr) +
         (Ec + Ep + &(2 * h * (L0 + 2)) * log(&pr) +
          &L0 * (&18 * &(4 * h + pr * h)) +
          &((L0 + 2) * ((4 * h + 1) + h)) +
          &((n - 1) * L0) * log(&4 * B + &2) + &((n - 1) * Lm) +
          &(4 * h) * T0 + &(4 * h) * (&2 * T0 + &n * &Lm * log(&1 + &pr)))
         <= &38 * &h * &S0 + &136 * &pr * &h * sg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &pr` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&pr) /\ log(&pr) <= &pr /\ &0 <= log(&1 + &pr) /\
                log(&1 + &pr) <= &pr /\ &0 <= log(&4 * B + &2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_LE_SELF THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sg /\ sg <= &h * sg /\ &h * sg <= &pr * &h * sg /\
                &pr * sg <= &pr * &h * sg`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&h <= &pr * &h /\ &0 <= &L0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN
     GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(2 * h * (L0 + 2)) * log(&pr) <= (&2 * &h * (&3 * sg)) * &pr`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
        [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&L0 * (&18 * &(4 * h + pr * h)) <= sg * (&18 * (&5 * &pr * &h))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&((L0 + 2) * ((4 * h + 1) + h)) <= (&3 * sg) * (&6 * &h)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&((n - 1) * L0) * log(&4 * B + &2) <= sg * &h /\
                &(4 * h) * T0 <= (&4 * &h) * sg /\
                &n * log(&pr) <= sg * &pr`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_LE_REFL] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(4 * h) * (&2 * T0 + &n * &Lm * log(&1 + &pr)) <=
                (&4 * &h) * (&2 * sg + sg * &pr)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= sg /\ y <= z ==> &2 * x + y <= &2 * sg +
      z`) THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  UNDISCH_TAC `Ec <= &3 * &h * sg` THEN UNDISCH_TAC `Ep <= &38 * &h * &S0` THEN
  UNDISCH_TAC `&((n - 1) * Lm) <= sg` THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Counting, the bounds for omega and Nl, and the remaining design facts.    *)
(* ------------------------------------------------------------------------- *)

let SHARP_NONDIV_CARD = prove
 (`!pr h. 2 <= pr
          ==> 2 * h <= CARD {l | 1 <= l /\ l <= 4 * h /\ ~(pr divides l)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?f. (!k. 1 <= k ==> 2 * k - 1 <= f k /\ f k <= 2 * k) /\
                    (!k. 1 <= k ==> ~(pr divides f k))`
  (X_CHOOSE_THEN `f:num->num` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `\k. if pr divides (2 * k) then 2 * k - 1 else 2 * k` THEN
    CONJ_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `pr divides 1` MP_TAC THENL
     [SUBGOAL_THEN `1 = 2 * k - (2 * k - 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; MATCH_MP_TAC DIVIDES_SUB THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[DIVIDES_ONE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:num->num) (1..2 * h) SUBSET
                {l | 1 <= l /\ l <= 4 * h /\ ~(pr divides l)}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      not(free_in `divides` (concl th)) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS `CARD(IMAGE (f:num->num) (1..2 * h))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`k1:num`; `k2:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `k1:num` th) THEN
                              MP_TAC(SPEC `k2:num` th)) o
      check (fun th -> not(free_in `divides` (concl th)) &&
                       is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..4 * h` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
    MESON_TAC[]]);;

let EXP_NEG_SMALL2 = prove
 (`!x. exp(--(x + &1)) + exp(--(x + &2)) < exp(--x)`,
  GEN_TAC THEN REWRITE_TAC[REAL_NEG_ADD; REAL_EXP_ADD] THEN
  SUBGOAL_THEN `&2 <= exp(&1) /\ &4 <= exp(&2)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `1` REAL_TWO_POW_LE_EXP) THEN
    MP_TAC(SPEC `2` REAL_TWO_POW_LE_EXP) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  SUBGOAL_THEN `&0 < inv(exp x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(exp(&1)) <= inv(&2) /\ inv(exp(&2)) <= inv(&4)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(exp x) * inv(exp(&1)) <= inv(exp x) * inv(&2) /\
    inv(exp x) * inv(exp(&2)) <= inv(exp x) * inv(&4)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SHARP_T0_LE_SG = prove
 (`!n g0 g0N lA gN Q a L Ln sg.
     1 <= n /\ &1 <= g0 /\ g0 <= &g0N /\ &g0N <= &Q /\ &0 <= lA /\
     lA <= &gN /\ 1 <= gN /\ &1 <= &Q /\
     &L = &gN * &Q pow a /\ &Ln = &Q pow (a + 1) /\
     sg = (&n + &1) * &gN * &Q pow (a + 1)
     ==> &0 <= &L * &(n - 1) * g0 + &Ln * (lA + &1) /\
         &L * &(n - 1) * g0 + &Ln * (lA + &1) <= sg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &gN /\ &0 <= &Q pow a /\ &0 <= &Q pow (a + 1) /\
                &Q pow (a + 1) = &Q pow a * &Q`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&L * g0 <= &gN * &Q pow (a + 1) /\
                &Ln * (lA + &1) <= &2 * (&gN * &Q pow (a + 1)) /\
                &0 <= &L * g0 /\ &0 <= &Ln * (lA + &1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&2 * g * q:real = q * (&2 * g)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
                      ASM_REAL_ARITH_TAC];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(n - 1) * (&L * g0) <= &(n - 1) * (&gN * &Q pow (a + 1)) /\
                &0 <= &(n - 1) * (&L * g0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(n - 1) = &n - &1` SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUB]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SHARP_ERR_INEQ = prove
 (`!n h L Lm Ln S0 X sg Ec Ep lB T0.
     1 <= h /\ 1 <= X /\ &1 <= sg /\ &L + &2 <= &3 * sg /\
     &((n - 1) * Lm) <= sg /\ &Ln <= sg /\ &0 <= T0 /\ T0 <= sg /\
     &0 <= lB /\ lB <= &h /\ Ec <= &3 * &h * sg /\ Ep <= &38 * &h * &S0 /\
     &78 * &h <= &X /\ &38 * sg <= &S0
     ==> Ec + Ep + &((L + 2) * ((X + 1) + h)) + &S0 * lB + &((n - 1) * Lm) +
         &X * (T0 + &1) + &X + &Ln + &2 <= &X * &S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &X` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&h <= &X` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&h * sg <= &X * sg /\ sg <= &X * sg /\ &1 <= &X * sg /\
                &((L + 2) * ((X + 1) + h)) <= (&3 * sg) * (&3 * &X) /\
                &S0 * lB <= &h * &S0 /\ &X * (T0 + &1) <= &X * (&2 * sg) /\
                &X <= &X * sg /\
                &h * &S0 * &78 <= &X * &S0 /\ &X * (&38 * sg) <= &X * &S0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN MP_TAC(SPEC `L:num` REAL_POS) THEN
      ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH `h * s * c:real = s * (c * h)`] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `Ec <= &3 * &h * sg` THEN UNDISCH_TAC `Ep <= &38 * &h * &S0` THEN
  UNDISCH_TAC `&((L + 2) * ((X + 1) + h)) <= (&3 * sg) * (&3 * &X)` THEN
  UNDISCH_TAC `&((n - 1) * Lm) <= sg` THEN
  ASM_REAL_ARITH_TAC);;

let SHARP_QPOW_ABSORB = prove
 (`!e g0N Q c j k m.
     1 <= g0N /\ Q = 2 EXP e * g0N /\ &0 <= c /\ c <= &2 pow j /\
     j + k <= e * m
     ==> c * &2 pow k <= &Q pow m`,
  REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `&2 pow j * &2 pow k` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN MATCH_MP_TAC SHARP_QPOW_GE THEN
    ASM_MESON_TAC[]]);;

let SHARP_LOG_RATIO_STEP = prove
 (`!h Q K. 1 <= h /\ &1 <= &Q
           ==> log((&(h * Q EXP (K + 1)) + &h) / &h) <= &(K + 1) * log(&Q) +
             &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &h /\ &1 <= &Q pow (K + 1) /\ &0 <
    &Q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&(h * Q EXP (K + 1)) + &h) / &h = &Q pow (K + 1) +
    &1` SUBST1_TAC
  THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    UNDISCH_TAC `&0 < &h` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `log(&2 * &Q pow (K + 1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Q pow (K + 1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &2`; LOG_POW] THEN
  MP_TAC LOG_2_LE_1 THEN REAL_ARITH_TAC);;

let SHARP_FINAL_U = prove
 (`!e g0N gN h Q M g0 A B.
     1 <= g0N /\ g0 <= &g0N /\ &g0N < g0 + &1 /\ &1 <= g0 /\
     log A <= &gN /\ &gN < log A + &1 /\ &1 <= log A /\
     log(&4 * B + &2) <= &h /\ &h < log(&4 * B + &2) + &1 /\ &2 <= B /\
     2 EXP e * g0N = Q
     ==> &17 * &h * &gN * &Q pow M <=
         &2 pow ((e + 1) * M + 9) * g0 pow M * log A * log B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= log B /\ log(&4 * B + &2) <= &3 +
    log B` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `log(&2)` THEN
       REWRITE_TAC[CONJUNCT1 LOG_2_BOUNDS] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `log(exp(&3) * B)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `3` REAL_TWO_POW_LE_EXP) THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&8 * B <= exp(&3) * B` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &h /\ &h <= &9 * log B /\ &0 <= &gN /\ &gN <= &2 *
    log A /\
                &0 <= &Q /\ &Q <= &2 pow (e + 1) * g0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "Q" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&Q pow M <= &2 pow ((e + 1) * M) * g0 pow M` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_POW; GSYM REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &Q pow M /\ &0 <= log A /\ &0 <=
    log B` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `&17 * (&9 * log B) * (&2 * log A) * (&2 pow ((e + 1) * M) * g0 pow M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &17`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 pow ((e + 1) * M) * g0 pow M * log A *
    log B` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part A. Principal logarithms of roots of integer polynomials: for a root  *)
(* exp(z) of an integer polynomial of degree <= D with coefficients bounded  *)
(* by H, |Re z| <= log H + log(1 + D) and so |z| <= log H + D + 4.           *)
(* ------------------------------------------------------------------------- *)

let SHARP_ALGDATA_LG_BOUND = prove
 (`!n (lg:num->complex) (a:num->num->real) (dd:num->num) (H:num->real) D r.
     sharp_algdata n lg a dd H /\ r IN 1..n /\ dd r <= D /\
     --pi < Im(lg r) /\ Im(lg r) <= pi
     ==> norm(lg r) <= log(H r) + &D + &4`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sharp_algdata] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pi <= &4` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &D /\ &1 <= &(dd(r:num)) /\ &(dd r) <= &D`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (H:num->real) r` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(Re((lg:num->complex) r)) <= &1 + &(dd r) * (H:num->real) r`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_CEXP] THEN MATCH_MP_TAC INTEGER_POLY_ROOT_BOUND THEN
    EXISTS_TAC `(a:num->num->real) r` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * (H:num->real) r) <= exp(Re((lg:num->complex) r))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_CEXP] THEN
    MATCH_MP_TAC ALGEBRAIC_ROOT_LOWER_BOUND THEN
    MAP_EVERY EXISTS_TAC [`(a:num->num->real) r`; `(dd:num->num) r`] THEN
    ASM_REWRITE_TAC[CEXP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &(dd r) * (H:num->real) r <= (&1 + &D) * H r`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&(dd r) * (H:num->real) r <= &D * H r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + &D /\ &0 < &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `Re((lg:num->complex) r) <= log(&1 + &D) + log((H:num->real) r) /\
    --(log(&2) + log(H r)) <= Re(lg r)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LOG_MUL] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      SUBGOAL_THEN `&0 < &2 * (H:num->real) r` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM LOG_INV] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_INV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) <= log(&1 + &D) /\ log(&1 + &D) <= &D`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `(lg:num->complex) r` COMPLEX_NORM_LE_RE_IM) THEN
  MAP_EVERY UNDISCH_TAC
   [`Re((lg:num->complex) r) <= log(&1 + &D) + log((H:num->real) r)`;
    `--(log(&2) + log((H:num->real) r)) <= Re((lg:num->complex) r)`;
    `log(&2) <= log(&1 + &D)`; `log(&1 + &D) <= &D`; `pi <= &4`;
    `--pi < Im((lg:num->complex) r)`; `Im((lg:num->complex) r) <= pi`] THEN
  REAL_ARITH_TAC);;

let SHARP_ALG_LG_BOUNDS = prove
 (`!n (lg:num->complex) (a:num->num->real) (dd:num->num) D A g0.
     &1 <= g0 /\ exp(&1) <= A /\
     sharp_algdata n lg a dd (\r. if r = n then A else exp g0) /\
     (!r. r IN 1..n
          ==> dd r <= D /\ --pi < Im(lg r) /\ Im(lg r) <= pi)
     ==> (!r. r IN 1..n-1 ==> norm(lg r) <= g0 + &D + &4) /\
         (1 <= n ==> norm(lg n) <= log A + &D + &4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r IN 1..n /\ ~(r = n)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `r IN 1..n-1` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`n:num`; `lg:num->complex`; `a:num->num->real`;
                   `dd:num->num`; `\r:num. if r = n then (A:real) else exp g0`;
                   `D:num`; `r:num`] SHARP_ALGDATA_LG_BOUND) THEN
    ASM_SIMP_TAC[LOG_EXP];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`n:num`; `lg:num->complex`; `a:num->num->real`;
                   `dd:num->num`; `\r:num. if r = n then (A:real) else exp g0`;
                   `D:num`; `n:num`] SHARP_ALGDATA_LG_BOUND) THEN
    ASM_SIMP_TAC[IN_NUMSEG; LE_REFL]]);;

let SHARP_ALG_NL_BOUND = prove
 (`!n (lg:num->complex) D g0 g0N.
     (!r. r IN 1..n-1 ==> norm(lg r) <= g0 + &D + &4) /\ g0 <= &g0N
     ==> &1 + &2 * sum(1..n-1) (\i. norm(lg i))
         <= &(2 * (n - 1) * (g0N + D + 4) + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sum(1..n-1) (\i. norm((lg:num->complex) i)) <=
                sum(1..n-1) (\i. &(g0N + D + 4))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    TRANS_TAC REAL_LE_TRANS `g0 + &D + &4` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n - 1 + 1) - 1 = n - 1`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;

let SHARP_ALG_SUM_LV_LOG = prove
 (`!n A g0 L Ln D.
     1 <= n /\ &1 <= g0 /\ &1 <= A /\ &0 <= log A
     ==> sum(1..n) (\r. &(sharp_lv n L Ln r) *
                        log(&2 * (\r. if r = n then A else exp g0) r)) <=
         &L * &(n - 1) * (g0 + &D + &4) + &Ln * (log A + &D + &5) /\
         sum(1..n) (\r. &(sharp_lv n L Ln r) *
                        log((\r. if r = n then A else exp g0) r)) <=
         &L * &(n - 1) * (g0 + &D + &4) + &Ln * (log A + &D + &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < n /\ 1 <= n` (fun th ->
      REWRITE_TAC[MATCH_MP SUM_CLAUSES_RIGHT th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sharp_lv] THEN
  SUBGOAL_THEN
   `!f:real->real. sum(1..n-1) (\r. &(if r = n then Ln else L) *
                                    f (if r = n then A else exp g0)) =
                  sum(1..n-1) (\r. &L * f(exp g0))`
  (fun th -> REWRITE_TAC[REWRITE_RULE[] (SPEC `\x:real. log(&2 * x)` th);
                         REWRITE_RULE[] (SPEC `\x:real. log x` th)])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(r:num = n)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n - 1 + 1) - 1 = n - 1`] THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; REAL_ARITH `&0 < &2`; LOG_EXP] THEN
  MP_TAC LOG_2_LE_1 THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &L * &(n - 1) /\ &0 <= &Ln` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&(n - 1) * &L * x = (&L * &(n - 1)) * x`] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) <= b /\ c <= d ==> a + c <= b + d`) THEN
  CONJ_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `D:num` REAL_POS) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part B. Exponential bounds for the bound functions sharp_psize,           *)
(* sharp_liou5 and sharp_lb8 of Baker/sharp_defs.ml at the integer instance  *)
(* (the Delta representation of integer coefficients: sizes                  *)
(* W s = (4 B + 2)^s 2^((n-1) L), degrees E = 0, multiplier bound Mb = 1,    *)
(* coefficient degrees db = 1 and any coefficient height Hb). The body       *)
(* lemmas SHARP_PSIZE_INT_BODY, SHARP_LIOU5_INT_BODY, SHARP_LB8_INT_BODY     *)
(* give the three functions at this instance explicitly; they are the only   *)
(* lemmas that unfold the definitions here. The Siegel bound is at most the  *)
(* exponential bound for rational data (with log(2 H) for log H), the        *)
(* Liouville bound at an integer l is at least exp(-c (EB + log c)) and the  *)
(* Lemma 8 bound at l/q at least exp(-q^n c (n log q + log c + EM)),         *)
(* c >= nproduct dd, EB and EM the exponents for rational data plus terms in *)
(* log(1 + D).                                                               *)
(* ------------------------------------------------------------------------- *)

let SHARP_PSIZE_INT_BODY = prove
 (`!n h L0 Lv L S0 B (H:num->real) Hb.
     sharp_psize n h L0 Lv S0 H Hb
       (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * L)) (\s. 0) =
    &(CARD(sharp_index h L0 Lv n)) *
    max (&1)
        (exp(&36 * &h * &S0) * &2 pow ((L0 + 2) * (2 * h + 1)) *
         (&4 * B + &2) pow S0 * &2 pow ((n - 1) * L) *
         product(1..n) (\r. (&2 * H r) pow (Lv r * h)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sharp_psize] THEN
  REWRITE_TAC[MULT_CLAUSES; real_pow; REAL_MUL_LID; REAL_MUL_RID;
              NPRODUCT_ONE; PRODUCT_ONE; GSYM REAL_MUL_ASSOC]);;

let SHARP_LIOU5_INT_BODY = prove
 (`!n h L0 Lv L P B S0 (dd:num->num) (H:num->real) Hb l.
     sharp_liou5 n h L0 Lv P S0 dd H (\r. 1) Hb
       (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * L)) (\s. 0) (\s. &1) l =
    inv((exp(&19) * (&l + &h) / &h) pow (h * S0) *
        &(FACT(nproduct(1..n) dd)) *
        (max (&1)
          ((&(CARD(sharp_index h L0 Lv n)) * P *
            (exp(&19) * (&l + &h) / &h) pow (h * S0) *
            &2 pow ((L0 + 2) * ((l + 1) + h)) *
            (&4 * B + &2) pow S0 * &2 pow ((n - 1) * L)) *
           product(1..n) (\r. H r pow (Lv r * l)) *
           product(1..n) (\r. (H r * (&1 + &(dd r) * H r)) pow (Lv r * l))))
        pow (nproduct(1..n) dd - 1) *
        product(1..n) (\r. H r pow (Lv r * l)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sharp_liou5] THEN
  REWRITE_TAC[MULT_CLAUSES; real_pow; REAL_MUL_LID; REAL_MUL_RID;
              NPRODUCT_ONE; PRODUCT_ONE; GSYM REAL_MUL_ASSOC]);;

let SHARP_LB8_INT_BODY = prove
 (`!n h L0 Lv L P B (dd:num->num) (H:num->real) Hb (m:num->num) l q Nz.
     sharp_lb8 n h L0 Lv P dd H (\r. 1) Hb
       (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * L)) (\s. 0) (\s. &1)
       m l q Nz =
    inv(&(FACT(nproduct(1..n) (\r. q * dd r))) *
        (max (&1)
          ((&(CARD(sharp_index h L0 Lv n)) * P *
            (&q pow (2 * h * (L0 + 2)) * exp(&18 * &(l + q * h)) pow (m 0)) *
            &2 pow ((L0 + 2) * (Nz + h)) *
            (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * L)) *
           product(1..n) (\r. H r pow (Lv r * l)) *
           product(1..n) (\r. (H r * (&1 + &(q * dd r) * H r))
                              pow (Lv r * l))))
        pow (nproduct(1..n) (\r. q * dd r) - 1) *
        product(1..n) (\r. H r pow (Lv r * l))) /
    (&q pow (2 * h * (L0 + 2)) * exp(&18 * &(l + q * h)) pow (m 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sharp_lb8] THEN
  REWRITE_TAC[MULT_CLAUSES; real_pow; REAL_MUL_LID; REAL_MUL_RID;
              NPRODUCT_ONE; PRODUCT_ONE; GSYM REAL_MUL_ASSOC]);;

let SHARP_PSIZE_ALG_POS = prove
 (`!n h L0 Lv Lm S0 B (H:num->real) Hb.
     &0 <= sharp_psize n h L0 Lv S0 H Hb
             (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SHARP_PSIZE_INT_BODY] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC);;

let SHARP_PRODUCT_DEG_LE_EXP = prove
 (`!n (H:num->real) (dd:num->num) (Lv:num->num) Lm l T0 D.
     (!r. r IN 1..n ==> &1 <= H r /\ dd r <= D /\ Lv r <= Lm) /\
     sum(1..n) (\r. &(Lv r) * log(H r)) <= T0
     ==> product(1..n) (\r. (H r * (&1 + &(dd r) * H r)) pow (Lv r * l)) <=
         exp(&l * (&2 * T0 + &n * &Lm * log(&1 + &D)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `\r. (H:num->real) r * (&1 + &(dd r) * H r)`;
                 `Lv:num->num`; `l:num`] PRODUCT_POW_EXP_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= (H:num->real) r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..n) (\r. &2 * (&(Lv r) * log((H:num->real) r)) +
                   log(&1 + &D) * &(Lv r))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= (H:num->real) r /\ dd r <= D` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        is_forall(concl th) && free_in `Lm:num` (concl th))) THEN
      ASM_SIMP_TAC[IN_NUMSEG];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (H:num->real) r /\ &0 < &1 + &(dd r) * H r /\
                  &0 < &1 + &D`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL] THEN
    SUBGOAL_THEN
     `log(&1 + &(dd r) * (H:num->real) r) <= log(&1 + &D) + log(H r)`
    MP_TAC THENL
     [ASM_SIMP_TAC[GSYM LOG_MUL] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&(dd r) * (H:num->real) r <= &D * H r` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `&(Lv r) * log(&1 + &(dd r) * (H:num->real) r) <=
      &(Lv r) * (log(&1 + &D) + log(H r))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  SUBGOAL_THEN `sum(1..n) (\r. &((Lv:num->num) r)) <= &n * &Lm` MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `sum(1..n) (\r:num. &Lm)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[IN_NUMSEG];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= log(&1 + &D)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN MP_TAC(SPEC `D:num` REAL_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&1 + &D) * sum(1..n) (\r. &((Lv:num->num) r)) <=
                log(&1 + &D) * (&n * &Lm)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `sum(1..n) (\r. &((Lv:num->num) r) * log((H:num->real) r)) <=
    T0` THEN
  REAL_ARITH_TAC);;

let SHARP_PSIZE_ALG_LE_EXP = prove
 (`!n h L0 Lv Lm S0 B (H:num->real) Hb Ec T1.
     &1 <= B /\ &(CARD(sharp_index h L0 Lv n)) <= exp Ec /\
     (!r. r IN 1..n ==> &1 <= H r) /\
     sum(1..n) (\r. &(Lv r) * log(&2 * H r)) <= T1
     ==> sharp_psize n h L0 Lv S0 H Hb
           (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0) <=
         exp(Ec + &36 * &h * &S0 + &((L0 + 2) * (2 * h + 1)) +
             &S0 * log(&4 * B + &2) + &((n - 1) * Lm) + &h * T1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SHARP_PSIZE_INT_BODY] THEN
  ABBREV_TAC
   `E1 = &36 * &h * &S0 + &((L0 + 2) * (2 * h + 1)) +
         &S0 * log(&4 * B + &2) + &((n - 1) * Lm) + &h * T1` THEN
  SUBGOAL_THEN `!r. r IN 1..n ==> &0 < &2 * (H:num->real) r` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < &2 * x`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= T1 /\ &0 <= log(&4 * B + &2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS
       `sum(1..n) (\r. &((Lv:num->num) r) * log(&2 * (H:num->real) r))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC LOG_POS THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &2 * x`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E1` ASSUME_TAC THENL
   [EXPAND_TAC "E1" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(&36 * &h * &S0) * &2 pow ((L0 + 2) * (2 * h + 1)) *
    (&4 * B + &2) pow S0 * &2 pow ((n - 1) * Lm) *
    product(1..n) (\r. (&2 * (H:num->real) r) pow (Lv r * h)) <= exp E1`
  ASSUME_TAC THENL
   [EXPAND_TAC "E1" THEN REWRITE_TAC[REAL_EXP_ADD] THEN
    MP_TAC(ISPECL [`n:num`; `\r. &2 * (H:num->real) r`;
                   `Lv:num->num`; `h:num`] PRODUCT_POW_EXP_SUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL_5 THEN
    REWRITE_TAC[REAL_EXP_POS_LE; REAL_LE_REFL; REAL_TWO_POW_LE_EXP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_POW_EXP_LOG THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_MAX_LE] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBST1_TAC(SYM REAL_EXP_0) THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE]);;

let SHARP_LIOU5_ALG_GE_EXP = prove
 (`!n h L0 Lv Lm P B S0 (dd:num->num) (H:num->real) Hb l Ec Ep T0 D c.
     1 <= h /\ &1 <= B /\ &0 <= P /\ P <= exp Ep /\
     &(CARD(sharp_index h L0 Lv n)) <= exp Ec /\ &0 <= Ec /\ &0 <= Ep /\
     (!r. r IN 1..n ==> &1 <= H r /\ 1 <= dd r /\ dd r <= D /\ Lv r <= Lm) /\
     nproduct(1..n) dd <= c /\
     sum(1..n) (\r. &(Lv r) * log(H r)) <= T0
     ==> exp(--(&c * ((Ec + Ep + &(h * S0) * (&19 + log((&l + &h) / &h)) +
                       &((L0 + 2) * ((l + 1) + h)) + &S0 * log(&4 * B + &2) +
                       &((n - 1) * Lm) +
                       &l * (&3 * T0 + &n * &Lm * log(&1 + &D))) +
                      log(&c))))
         <= sharp_liou5 n h L0 Lv P S0 dd H (\r. 1) Hb
              (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0)
              (\s. &1) l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SHARP_LIOU5_INT_BODY] THEN
  ABBREV_TAC `Dp = nproduct(1..n) (dd:num->num)` THEN
  ABBREV_TAC `N5 = exp(&19) * (&l + &h) / &h` THEN
  ABBREV_TAC `PH = product(1..n) (\r. (H:num->real) r pow (Lv r * l))` THEN
  ABBREV_TAC
   `PH2 = product(1..n)
           (\r. ((H:num->real) r * (&1 + &(dd r) * H r)) pow (Lv r * l))` THEN
  ABBREV_TAC
   `EB = Ec + Ep + &(h * S0) * (&19 + log((&l + &h) / &h)) +
         &((L0 + 2) * ((l + 1) + h)) + &S0 * log(&4 * B + &2) +
         &((n - 1) * Lm) + &l * (&3 * T0 + &n * &Lm * log(&1 + &D))` THEN
  SUBGOAL_THEN `!r. r IN 1..n ==> &0 < (H:num->real) r` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `&1 <= x ==> &0 < x`]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Dp /\ 1 <= c` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `1 <= Dp` (fun th -> ASM_MESON_TAC[th; LE_TRANS]) THEN
    EXPAND_TAC "Dp" THEN
    TRANS_TAC LE_TRANS `nproduct(1..n) (\r:num. 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[NPRODUCT_CONST_NUMSEG_1; EXP_ONE; LE_REFL];
      MATCH_MP_TAC NPRODUCT_LE_NUMSEG THEN ASM_SIMP_TAC[IN_NUMSEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= T0` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sum(1..n) (\r. &((Lv:num->num) r) * log((H:num->real) r))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LV_LOG_POS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&l + &h) / &h /\ &1 <= (&l + &h) / &h` STRIP_ASSUME_TAC
  THENL
   [SUBGOAL_THEN `&0 < &h /\ &0 < &l + &h` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_RDIV_EQ] THEN
    MP_TAC(SPEC `l:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= log((&l + &h) / &h) /\ &0 <= log(&4 * B + &2) /\
    &0 <= log(&1 + &D)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `D:num` REAL_POS) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `N5 pow (h * S0) = exp(&(h * S0) * (&19 + log((&l + &h) / &h))) /\
    &0 < N5`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N5" THEN
    SUBGOAL_THEN `&0 < exp(&19) * (&l + &h) / &h` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_EXP_LOG; LOG_MUL; REAL_EXP_POS_LT; LOG_EXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `PH <= exp(&l * T0) /\ &0 < PH` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "PH" THEN
    SIMP_TAC[ASSUME `!r. r IN 1..n ==> &0 < (H:num->real) r`;
             PRODUCT_POW_EXP_SUM; REAL_EXP_POS_LT; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `PH2 <= exp(&l * (&2 * T0 + &n * &Lm * log(&1 + &D)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "PH2" THEN MATCH_MP_TAC SHARP_PRODUCT_DEG_LE_EXP THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= EB` ASSUME_TAC THENL
   [EXPAND_TAC "EB" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `N5 pow (h * S0) * PH <= exp EB` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `exp(&(h * S0) * (&19 + log((&l + &h) / &h))) * exp(&l * T0)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN EXPAND_TAC "EB" THEN
    SUBGOAL_THEN
     `&0 <= &((L0 + 2) * ((l + 1) + h)) + &S0 * log(&4 * B + &2) +
            &((n - 1) * Lm) + &l * (&2 * T0 + &n * &Lm * log(&1 + &D))`
    MP_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS] THEN TRY ASM_REAL_ARITH_TAC THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&0 <= Ec` THEN UNDISCH_TAC `&0 <= Ep` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `MX = max (&1)
          ((&(CARD(sharp_index h L0 Lv n)) * P * N5 pow (h * S0) *
            &2 pow ((L0 + 2) * ((l + 1) + h)) * (&4 * B + &2) pow S0 *
            &2 pow ((n - 1) * Lm)) * PH * PH2)` THEN
  SUBGOAL_THEN `&1 <= MX /\ MX <= exp EB` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "MX" THEN REWRITE_TAC[REAL_MAX_LE] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      SUBST1_TAC(SYM REAL_EXP_0) THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `(exp Ec * exp Ep * exp(&(h * S0) * (&19 + log((&l + &h) / &h))) *
       exp(&((L0 + 2) * ((l + 1) + h))) * exp(&S0 * log(&4 * B + &2)) *
       exp(&((n - 1) * Lm))) * exp(&l * T0) *
      exp(&l * (&2 * T0 + &n * &Lm * log(&1 + &D)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      EXPAND_TAC "EB" THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; REAL_POW_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL_6 THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_LE_REFL;
                      REAL_TWO_POW_LE_EXP] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE THEN
                                ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_POW_EXP_LOG THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "PH2" THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_POW_LE THEN
      SUBGOAL_THEN `&1 <= (H:num->real) r` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "PH2" THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_POW_LE THEN
      SUBGOAL_THEN `&1 <= (H:num->real) r` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(FACT Dp) <= exp(&Dp * log(&Dp))` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&Dp pow Dp` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; FACT_LE_SELF_EXP];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_POW_EXP_LOG THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT; REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `exp(&Dp * (EB + log(&Dp)))` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    SUBGOAL_THEN `&1 <= &Dp /\ &Dp <= &c` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= log(&Dp) /\ log(&Dp) <= log(&c)` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN
   `exp(&Dp * (EB + log(&Dp))) =
    exp EB * exp(&Dp * log(&Dp)) * exp EB pow (Dp - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `N5 pow (h * S0) * &(FACT Dp) * MX pow (Dp - 1) * PH =
    (N5 pow (h * S0) * PH) * &(FACT Dp) * MX pow (Dp - 1)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]]);;

let SHARP_PRODUCT_DEG_SPLIT = prove
 (`!n (H:num->real) (dd:num->num) (Lv:num->num) Lm l q D.
     (!r. r IN 1..n ==> &1 <= H r /\ dd r <= D /\ Lv r <= Lm)
     ==> product(1..n) (\r. (H r * (&1 + &(q * dd r) * H r)) pow (Lv r * l))
         <= product(1..n) (\r. (H r * (&1 + &q * H r)) pow (Lv r * l)) *
            exp(&l * (&n * &Lm * log(&1 + &D)))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `product(1..n) (\r. ((H:num->real) r * (&1 + &q * H r)) pow (Lv r * l)) *
    product(1..n) (\r. (&1 + &D) pow (Lv r * l))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG; GSYM REAL_POW_MUL] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `&1 <= (H:num->real) r /\ dd r <= D` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_SIMP_TAC[IN_NUMSEG];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &q * (H:num->real) r /\ &(dd r) <= &D`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (H:num->real) r * (&1 + &(q * dd r) * H r)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `(&q * (H:num->real) r) * &(dd r) <= (&q * H r) * &D`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&q * (H:num->real) r) * &D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MP_TAC(SPEC `D:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    SUBGOAL_THEN `&1 <= (H:num->real) r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `\r:num. &1 + &D`; `Lv:num->num`; `l:num`]
                PRODUCT_POW_EXP_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(SPEC `D:num` REAL_POS) THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS; SUM_RMUL; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LOG_POS THEN MP_TAC(SPEC `D:num` REAL_POS) THEN
    REAL_ARITH_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `sum(1..n) (\r:num. &Lm)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[IN_NUMSEG];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC]);;

let SHARP_LB8_ALG_GE_EXP = prove
 (`!n h L0 Lv Lm P B (dd:num->num) (H:num->real) Hb (m:num->num) l q Nz
    Ec Ep T0 D c.
     1 <= q /\ &1 <= B /\ &0 <= P /\ P <= exp Ep /\
     &(CARD(sharp_index h L0 Lv n)) <= exp Ec /\ &0 <= Ec /\ &0 <= Ep /\
     (!r. r IN 1..n ==> &1 <= H r /\ 1 <= dd r /\ dd r <= D /\ Lv r <= Lm) /\
     nproduct(1..n) dd <= c /\
     sum(1..n) (\r. &(Lv r) * log(H r)) <= T0
     ==> exp(--(&(q EXP n) * &c *
                (&n * log(&q) + log(&c) +
                 (Ec + Ep + &(2 * h * (L0 + 2)) * log(&q) +
                  &(m 0) * (&18 * &(l + q * h)) + &((L0 + 2) * (Nz + h)) +
                  &(nsum(1..n-1) m) * log(&4 * B + &2) + &((n - 1) * Lm) +
                  &l * T0 + &l * (&2 * T0 + &n * &Lm * log(&1 + &q))) +
                 &l * (&n * &Lm * log(&1 + &D)))))
         <= sharp_lb8 n h L0 Lv P dd H (\r. 1) Hb
              (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0)
              (\s. &1) m l q Nz`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `h:num`; `L0:num`; `Lv:num->num`; `Lm:num`;
                 `P:real`; `B:real`; `H:num->real`; `m:num->num`; `l:num`;
                 `q:num`; `Nz:num`; `Ec:real`; `Ep:real`; `T0:real`]
                SHARP_MEXPR_LE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `H:num->real`; `dd:num->num`; `Lv:num->num`;
                 `Lm:num`; `l:num`; `q:num`; `D:num`]
                SHARP_PRODUCT_DEG_SPLIT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SHARP_LB8_INT_BODY] THEN
  ABBREV_TAC
   `Dn = &q pow (2 * h * (L0 + 2)) * exp(&18 * &(l + q * h)) pow (m 0)` THEN
  ABBREV_TAC `PH = product(1..n) (\r. (H:num->real) r pow (Lv r * l))` THEN
  ABBREV_TAC
   `PH2 = product(1..n) (\r. ((H:num->real) r * (&1 + &q * H r))
                             pow (Lv r * l))` THEN
  ABBREV_TAC
   `PH2q = product(1..n) (\r. ((H:num->real) r * (&1 + &(q * dd r) * H r))
                              pow (Lv r * l))` THEN
  ABBREV_TAC
   `Kc = &(CARD(sharp_index h L0 Lv n)) * P * Dn *
         &2 pow ((L0 + 2) * (Nz + h)) *
         (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * Lm)` THEN
  ABBREV_TAC
   `EMr = Ec + Ep + &(2 * h * (L0 + 2)) * log(&q) +
          &(m 0) * (&18 * &(l + q * h)) + &((L0 + 2) * (Nz + h)) +
          &(nsum(1..n-1) m) * log(&4 * B + &2) + &((n - 1) * Lm) +
          &l * T0 + &l * (&2 * T0 + &n * &Lm * log(&1 + &q))` THEN
  ABBREV_TAC `ED = &l * (&n * &Lm * log(&1 + &D))` THEN
  ABBREV_TAC `Dq = nproduct(1..n) (\r. q * (dd:num->num) r)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= ED` ASSUME_TAC THENL
   [EXPAND_TAC "ED" THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LOG_POS THEN MP_TAC(SPEC `D:num` REAL_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Dn` ASSUME_TAC THENL
   [EXPAND_TAC "Dn" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LT THEN
    REWRITE_TAC[REAL_EXP_POS_LT; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= nproduct(1..n) (dd:num->num)` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `nproduct(1..n) (\r:num. 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[NPRODUCT_CONST_NUMSEG_1; EXP_ONE; LE_REFL];
      MATCH_MP_TAC NPRODUCT_LE_NUMSEG THEN ASM_SIMP_TAC[IN_NUMSEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Dq = q EXP n * nproduct(1..n) (dd:num->num)` ASSUME_TAC THENL
   [EXPAND_TAC "Dq" THEN SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG] THEN
    REWRITE_TAC[NPRODUCT_CONST_NUMSEG_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= q EXP n` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Dq` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(FACT Dq) <= exp(&Dq * log(&Dq))` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&Dq pow Dq` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; FACT_LE_SELF_EXP];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_POW_EXP_LOG THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kc * PH` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [EXPAND_TAC "Kc" THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; REAL_POW_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= max (&1) (Kc * PH * PH2q) /\
                max (&1) (Kc * PH * PH2q) <= exp(EMr + ED)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MAX_LE] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      SUBST1_TAC(SYM REAL_EXP_0) THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(Kc * PH) * PH2 * exp ED` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Kc" THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; REAL_POW_LE] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[REAL_EXP_ADD; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN
  TRANS_TAC REAL_LE_TRANS `exp(--(&Dq * (log(&Dq) + EMr + ED)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    SUBGOAL_THEN `&1 <= &(nproduct(1..n) (dd:num->num)) /\
                  &(nproduct(1..n) dd) <= &c /\ &0 < &(q EXP n)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `log(&Dq) <= &n * log(&q) + log(&c) /\ &0 <= log(&Dq)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
        SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[LOG_POW; REAL_LE_LADD] THEN
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_POS THEN MATCH_MP_TAC REAL_LE_1_MUL THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_POW] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
        ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_POS];
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(&Dq * (log(&Dq) + EMr + ED)) =
    exp(&Dq * log(&Dq)) * exp(EMr + ED) pow (Dq - 1) * exp(EMr + ED)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS `exp EMr` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part C. The parameter design, with the radius exponent 8 c (c >= 1; the   *)
(* main theorem takes c = D^n): b = 8 c + 3, a = b n, J = (a + 1)(n + 2),    *)
(* e = J + 72 n + 256 + 8 c, Q = 2^e g0N, L = gN Q^a, Ln = Q^(a+1),          *)
(* Lm = gN Q^(a+1), S0 = gN Q^(a+b), R K = h Q^K, X = h Q^J,                 *)
(* sg = (n + 1) gN Q^(a+1). For c = 1 this is the design for rational        *)
(* data (radius Q^8) except for e.                                           *)
(* ------------------------------------------------------------------------- *)

let SHARP_SG_FACTS_ALG = prove
 (`!n a b gN Q L Lm Ln S0 sg.
     1 <= n /\ 1 <= gN /\ 2 <= Q /\ n + 1 <= Q /\ 2 <= b /\
     L = gN * Q EXP a /\ Lm = gN * Q EXP (a + 1) /\ Ln = Q EXP (a + 1) /\
     S0 = gN * Q EXP (a + b) /\ sg = (&n + &1) * &gN * &Q pow (a + 1)
     ==> &1 <= sg /\ &L <= sg /\ &L + &2 <= &3 * sg /\ &Lm <= sg /\
         &n * &Lm <= sg /\ &((n - 1) * Lm) <= sg /\ &Ln <= sg /\
         &((n - 1) * L) <= sg /\ &n <= sg /\ &2 <= &S0 /\ sg <= &S0 /\
         &L = &gN * &Q pow a /\ &Lm = &gN * &Q pow (a + 1) /\
         &Ln = &Q pow (a + 1) /\ &S0 = &gN * &Q pow (a + b) /\
         &1 <= &gN /\ &2 <= &Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &gN /\ &2 <= &Q /\ &n + &1 <= &Q` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&L = &gN * &Q pow a /\ &Lm = &gN * &Q pow (a + 1) /\
    &Ln = &Q pow (a + 1) /\ &S0 = &gN * &Q pow (a + b)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `&Q <= &Q pow (b - 1) /\ &1 <= &Q pow a /\
                &1 <= &Q pow (a + 1) /\ &Q pow a <= &Q pow (a + 1) /\
                &Q pow (a + b) = &Q pow (b - 1) * &Q pow (a + 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ARITH_TAC];
      REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `L:num`; `Ln:num`; `Lm:num`; `S0:num`;
                `&gN * &Q pow (a + 1)`; `sg:real`; `&Q pow (b - 1)`]
         SHARP_SG_AUX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIRST
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC THEN NO_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC THEN NO_TAC;
      REAL_ARITH_TAC THEN NO_TAC;
      ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let SHARP_INDEX_CARD_GE_ALG = prove
 (`!n a b gN Q h L Ln S0 Dp.
     1 <= n /\ 1 <= gN /\ 2 EXP (n + 1) * Dp <= Q /\ a = b * n /\
     L = gN * Q EXP a /\ Ln = Q EXP (a + 1) /\ S0 = gN * Q EXP (a + b)
     ==> 2 * Dp * h * (S0 + 1) EXP n <=
         CARD(sharp_index h L (sharp_lv n L Ln) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `Dp = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; LE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Q` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `2 EXP (n + 1) * Dp` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= S0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CARD_SHARP_INDEX] THEN
  SUBGOAL_THEN `nproduct(1..n) (\r. sharp_lv n L Ln r + 1) =
                (L + 1) EXP (n - 1) * (Ln + 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `0 < n /\ 1 <= n` (fun th ->
      REWRITE_TAC[MATCH_MP NPRODUCT_CLAUSES_RIGHT th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[sharp_lv] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS `nproduct(1..n-1) (\r. L + 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[NPRODUCT_CONST_NUMSEG_1]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L + 1) * (L + 1) EXP (n - 1) * (Ln + 1) =
                (L + 1) EXP n * (Ln + 1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MULT_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `n = SUC(n - 1)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 * D * h * x = h * (2 * D) * x`] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
  REWRITE_TAC[ASSUME `(L + 1) * (L + 1) EXP (n - 1) * (Ln + 1) =
                      (L + 1) EXP n * (Ln + 1)`] THEN
  TRANS_TAC LE_TRANS `(2 * Dp) * (2 * S0) EXP n` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS `Q * S0 EXP n` THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_EXP; MULT_ASSOC] THEN
    SUBGOAL_THEN `(2 * Dp) * 2 EXP n = 2 EXP (n + 1) * Dp` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q * S0 EXP n = L EXP n * Ln` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[MULT_EXP; EXP_EXP; RIGHT_ADD_DISTRIB; EXP_ADD; EXP_1] THEN
    REWRITE_TAC[MULT_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ARITH_TAC; ARITH_TAC]);;

let SHARP_NUM_POW_LE_TWO_POW = prove
 (`!c k. &c pow k <= &2 pow (k * c)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[REAL_POS; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  MESON_TAC[LT_POW2_REFL; LT_IMP_LE]);;

let SHARP_CPOLY_BOUNDS = prove
 (`!c n J. 1 <= c
           ==> &c * (&17 + &2 * &c) <= &2 pow 5 * &2 pow (2 * c) /\
               &c * (&59 + &J) <= &2 pow 6 * &2 pow (c + J) /\
               &c * (&16 + &2 * &c) * (&n + &1) <=
               &2 pow 5 * &2 pow (2 * c + n) /\
               &c pow 2 + &1 <= &2 pow 1 * &2 pow (2 * c) /\
               &2 pow (n + 1) * &c <= &2 pow (n + 1 + c) /\
               &4 * &c pow 2 <= &2 pow 2 * &2 pow (2 * c) /\
               &2 * &n <= &2 pow 1 * &2 pow n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &c` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&c <= &c pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&c pow 2 <= &2 pow (2 * c) /\ &c <= &2 pow c /\
                &n + &1 <= &2 pow n /\ &J + &1 <= &2 pow J /\
                &0 <= &2 pow c`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SHARP_NUM_POW_LE_TWO_POW] THEN
    MP_TAC(SPECL [`c:num`; `1`] SHARP_NUM_POW_LE_TWO_POW) THEN
    REWRITE_TAC[REAL_POW_1; MULT_CLAUSES] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD; REAL_OF_NUM_POW] THEN
    REWRITE_TAC[LE_0] THEN
    MESON_TAC[LT_POW2_REFL; ARITH_RULE `a < b ==> a + 1 <= b`];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS `&2 pow c * (&59 + &J)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 pow c * (&59 + &J) <= &2 pow c * (&64 * &2 pow J)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS `&18 * &c pow 2 * (&n + &1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&c pow 2 * (&n + &1) <= &2 pow (2 * c) * &2 pow n`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
                      REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &2 pow (2 * c) * &2 pow n` MP_TAC THENL
     [SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS]; REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SHARP_DESIGN_CFACTS_ALG = prove
 (`!n c a J e g0N gN h Q S0 sg X.
     1 <= n /\ 1 <= c /\ (8 * c + 3) * n = a /\ (a + 1) * (n + 2) = J /\
     J + 72 * n + 256 + 8 * c = e /\
     1 <= g0N /\ 2 EXP e * g0N = Q /\ 1 <= gN /\ 1 <= h /\
     &S0 = &gN * &Q pow (a + 8 * c + 3) /\
     sg = (&n + &1) * &gN * &Q pow (a + 1) /\ &X = &h * &Q pow J
     ==> &c * (&17 + &2 * &c) <= &Q pow (8 * c) /\
         &c * (&59 + &J * log(&Q)) <= &Q pow J /\
         &c * (&16 + &2 * &c) * sg <= &S0 /\
         &c pow 2 + &1 <= &Q pow J /\
         &2 pow (n + 1) * &c <= &Q /\
         &4 * &c pow 2 <= &Q /\
         g0N + c + 4 <= Q /\
         &(2 * (n - 1) * (g0N + c + 4) + 1) <= &X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`; `g0N:num`; `Q:num`] SHARP_Q_BASIC) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:num`; `n:num`; `J:num`] SHARP_CPOLY_BOUNDS) THEN
  ASM_REWRITE_TAC[GSYM REAL_POW_ADD] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. k <= e ==> &2 pow k <= &Q` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`e:num`; `g0N:num`; `Q:num`; `1`; `k:num`]
      SHARP_QPOW_GE) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. 1 <= m ==> &Q <= &Q pow m` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= J /\ J + 2 * c + n + 8 <= e` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a + 1) * (n + 2) = J` THEN UNDISCH_TAC `1 <= n` THEN
    UNDISCH_TAC `J + 72 * n + 256 + 8 * c = e` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&Q pow 2 <= &Q pow J /\ &1 <= &Q pow J /\
                &0 <= &gN * &Q pow (a + 1) /\
                &Q pow (a + 8 * c + 3) = &Q pow (8 * c + 2) * &Q pow (a + 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `g0N + c + 4 <= Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `c + 5 <= 2 EXP e` ASSUME_TAC THENL
     [TRANS_TAC LE_TRANS `2 EXP (c + 3)` THEN CONJ_TAC THENL
       [REWRITE_TAC[EXP_ADD] THEN MP_TAC(SPEC `c:num` LT_POW2_REFL) THEN
        ARITH_TAC;
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c + 5) * g0N <= 2 EXP e * g0N /\ c * 1 <= c * g0N`
    MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_MULT_LCANCEL]; ALL_TAC] THEN
    UNDISCH_TAC `2 EXP e * g0N = Q` THEN UNDISCH_TAC `1 <= g0N` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&Q` THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&2 pow (5 + 2 * c)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS `(&c * (&59 + &J)) * &Q` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN
      SUBGOAL_THEN `&J * log(&Q) <= &J * &Q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      UNDISCH_TAC `&1 <= &Q` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&Q pow 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&2 pow (6 + c + J)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&Q * &gN * &Q pow (a + 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_POW_LE THEN
                                ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(a:real) * b * c * d = (a * b * c) * d`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `&2 pow (5 + 2 * c + n)` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS `&Q` THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&2 pow (1 + 2 * c)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS `&2 pow (n + 1 + c)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS `&2 pow (2 + 2 * c)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &n <= &Q /\ &(g0N + c + 4) <= &Q /\ &1 <= &(g0N + c + 4)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
      TRANS_TAC REAL_LE_TRANS `&2 pow (1 + n)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS `&Q pow J` THEN CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&Q pow 2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  TRANS_TAC REAL_LE_TRANS `(&2 * &n) * &(g0N + c + 4)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
                 GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD] THEN
    UNDISCH_TAC `&1 <= &(g0N + c + 4)` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
    REAL_ARITH_TAC]);;

let SHARP_DESIGN_KFACTS_ALG = prove
 (`!n c a J e g0N gN Q S0 sg K.
     1 <= n /\ (8 * c + 3) * n = a /\ (a + 1) * (n + 2) = J /\
     J + 72 * n + 256 + 8 * c = e /\ 1 <= g0N /\ 2 EXP e * g0N = Q /\
     1 <= gN /\ &S0 = &gN * &Q pow (a + 8 * c + 3) /\
     sg = (&n + &1) * &gN * &Q pow (a + 1) /\ K < J
     ==> &2 pow (K + 1) * &31 * sg * &Q pow (K + 1 + 8 * c) <=
         &Q pow K * &S0 /\
         &2 pow (K + 1) <= &2 * &Q pow K /\
         &2 pow (K + 1) * &(K + 1) <= &2 * &Q pow K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`; `g0N:num`; `Q:num`] SHARP_Q_BASIC) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!d j k m. &0 <= d /\ d <= &2 pow j /\ j + k <= e * m
                          ==> d * &2 pow k <= &Q pow m` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SHARP_QPOW_ABSORB THEN
    MAP_EVERY EXISTS_TAC [`e:num`; `g0N:num`; `j:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `K + 1 + n + 5 <= e /\ 2 <= e` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `K < J` THEN UNDISCH_TAC `J + 72 * n + 256 + 8 * c = e` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&n + &1 <= &2 pow n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    MESON_TAC[LT_POW2_REFL; ARITH_RULE `a < b ==> a + 1 <= b`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(&31 * (&n + &1)) * &2 pow (K + 1) <= &Q pow 1` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n + 5` THEN
      REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_ADD] THEN
        CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
        SUBGOAL_THEN `&0 <= &2 pow n` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_1; GSYM REAL_MUL_ASSOC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= &gN * &Q pow (a + K + 2 + 8 * c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&2 pow (K + 1) * &31 * sg * &Q pow (K + 1 + 8 * c) =
      (&31 * (&n + &1) * &2 pow (K + 1)) *
      (&gN * &Q pow (a + K + 2 + 8 * c)) /\
      &Q pow K * &S0 = &Q * (&gN * &Q pow (a + K + 2 + 8 * c))`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_ADD] THEN
      CONJ_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    SUBGOAL_THEN `&1 * &2 pow K <= &Q pow K` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[real_pow; ADD_CLAUSES] THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE `1 * K <= e * K ==> K <= e * K`) THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      REAL_ARITH_TAC];
    SUBGOAL_THEN `&(K + 1) * &2 pow K <= &Q pow K` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `K:num` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_POS];
        REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
        MESON_TAC[LT_POW2_REFL; ARITH_RULE `a < b ==> a + 1 <= b`];
        MATCH_MP_TAC(ARITH_RULE `2 * K <= e * K ==> K + K <= e * K`) THEN
        REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN REAL_ARITH_TAC]]);;

let SHARP_DESIGN_QFACTS_ALG = prove
 (`!n c a J e g0N gN h Q S0 sg X.
     1 <= n /\ 1 <= c /\ (8 * c + 3) * n = a /\ (a + 1) * (n + 2) = J /\
     J + 72 * n + 256 + 8 * c = e /\
     1 <= g0N /\ 2 EXP e * g0N = Q /\ 1 <= gN /\ 1 <= h /\
     &S0 = &gN * &Q pow (a + 8 * c + 3) /\
     sg = (&n + &1) * &gN * &Q pow (a + 1) /\ &X = &h * &Q pow J
     ==> &2 pow J * &78 <= &Q pow J /\
         &2 pow J * &52 * sg * &Q pow (8 * c) <= &S0 /\
         &2 pow (J + 70 * n + 6) * &c <= &Q pow (2 * a + 2) /\
         &2 pow (J + 71 * n + 78) * &c pow 2 <= &Q pow (a + 8 * c + 3) /\
         &38 * sg <= &S0 /\ &78 * &h <= &X /\
         &2 * &2 pow 70 * &Q pow (a + 1) <= &S0 /\
         &2 * &2 pow 70 * &Q pow (a + 1) <= &X /\
         &2 pow J * &3 <= &X * &S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`; `g0N:num`; `Q:num`] SHARP_Q_BASIC) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!d j k m. &0 <= d /\ d <= &2 pow j /\ j + k <= e * m
                          ==> d * &2 pow k <= &Q pow m` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SHARP_QPOW_ABSORB THEN
    MAP_EVERY EXISTS_TAC [`e:num`; `g0N:num`; `j:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= J /\ a + 2 <= J /\ 2 <= J /\
                J + 72 * n + 256 + 8 * c <= e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a + 1) * (n + 2) = J` THEN UNDISCH_TAC `1 <= n` THEN
    UNDISCH_TAC `J + 72 * n + 256 + 8 * c = e` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k m. k <= e /\ 1 <= m ==> k <= e * m` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `k <= e /\ e * 1 <= e * m ==> k <= e * m`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&n + &1 <= &2 pow n /\ &1 <= &gN /\ &1 <= &h /\
                &c <= &2 pow c /\ &c pow 2 <= &2 pow (2 * c) /\
                &0 <= &2 pow n`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SHARP_NUM_POW_LE_TWO_POW] THEN
    MP_TAC(SPECL [`c:num`; `1`] SHARP_NUM_POW_LE_TWO_POW) THEN
    REWRITE_TAC[REAL_POW_1; MULT_CLAUSES] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE; LE_0] THEN
    MESON_TAC[LT_POW2_REFL; ARITH_RULE `a < b ==> a + 1 <= b`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&78 * &2 pow J <= &Q pow J /\ &78 * &2 pow 0 <= &Q pow J /\
    &3 * &2 pow J <= &Q pow J /\
    (&52 * (&n + &1)) * &2 pow J <= &Q pow 2 /\
    (&38 * (&n + &1)) * &2 pow 0 <= &Q pow (8 * c + 2) /\
    &c * &2 pow (J + 70 * n + 6) <= &Q pow (2 * a + 2) /\
    &c pow 2 * &2 pow (J + 71 * n + 78) <= &Q pow (a + 8 * c + 3) /\
    &1 * &2 pow 71 <= &Q pow (8 * c + 2) /\
    &1 * &2 pow 71 <= &Q pow (J - (a + 1))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THENL
     [EXISTS_TAC `7`; EXISTS_TAC `7`; EXISTS_TAC `2`; EXISTS_TAC `n + 6`;
      EXISTS_TAC `n + 6`; EXISTS_TAC `c:num`; EXISTS_TAC `2 * c`;
      EXISTS_TAC `0`; EXISTS_TAC `0`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_POW_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&0 <= &gN * &Q pow (a + 1 + 8 * c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `((&52 * (&n + &1)) * &2 pow J) * (&gN * &Q pow (a + 1 + 8 * c))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&Q pow 2 * (&gN * &Q pow (a + 1 + 8 * c))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `a + 8 * c + 3 = (a + 1 + 8 * c) + 2`;
                  REAL_POW_ADD] THEN
      REAL_ARITH_TAC];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&0 <= &gN * &Q pow (a + 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&38 * (&n + &1)) * (&gN * &Q pow (a + 1)) <=
                  &Q pow (8 * c + 2) * (&gN * &Q pow (a + 1))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(&38 * (&n + &1)) * &2 pow 0 <= &Q pow (8 * c + 2)` THEN
      REWRITE_TAC[real_pow; REAL_MUL_RID];
      REWRITE_TAC[ARITH_RULE `a + 8 * c + 3 = (a + 1) + (8 * c + 2)`;
                  REAL_POW_ADD] THEN
      REAL_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS `&h * &78` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    UNDISCH_TAC `&78 * &2 pow 0 <= &Q pow J` THEN
    REWRITE_TAC[real_pow; REAL_MUL_RID];
    TRANS_TAC REAL_LE_TRANS `&Q pow (8 * c + 2) * &Q pow (a + 1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_POW_LE THEN
                                ASM_REAL_ARITH_TAC] THEN
      UNDISCH_TAC `&1 * &2 pow 71 <= &Q pow (8 * c + 2)` THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&Q pow (8 * c + 2) * &Q pow (a + 1) = &Q pow (a + 8 * c + 3)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS `&Q pow (J - (a + 1)) * &Q pow (a + 1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_POW_LE THEN
                                ASM_REAL_ARITH_TAC] THEN
      UNDISCH_TAC `&1 * &2 pow 71 <= &Q pow (J - (a + 1))` THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN
    SUBGOAL_THEN `J - (a + 1) + a + 1 = J` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS `&Q pow J` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&h * &Q pow J` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC]]);;

let SHARP_S_FACTS_ALG = prove
 (`!n c a J e g0N gN Q L S0 (S:num->num) Y.
     1 <= n /\ (8 * c + 3) * n = a /\ (a + 1) * (n + 2) = J /\
     J + 72 * n + 256 + 8 * c = e /\
     1 <= g0N /\ 2 EXP e * g0N = Q /\ 1 <= gN /\
     gN * Q EXP a = L /\ gN * Q EXP (a + 8 * c + 3) = S0 /\
     (!K. S K = gN * g0N EXP (a + 8 * c + 3) *
                2 EXP (e * (a + 8 * c + 3) - K)) /\
     S J - n * L = Y
     ==> S 0 = S0 /\
         (!K. K < J ==> 2 * S(K + 1) <= S K /\
                        &(S(K + 1)) * &2 pow (K + 1) = &S0 /\
                        S(K + 1) + 1 <= S0) /\
         &(S J) * &2 pow J = &S0 /\ n * L + Y = S J /\ &(S J) <= &2 * &Y /\
         Y + 1 <= S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `J + 1 <= e * (a + 8 * c + 3) /\ 1 <= J` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `J + 1 <= e /\ e * 1 <= e * m ==> J + 1 <= e * m`) THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN
      UNDISCH_TAC `J + 72 * n + 256 + 8 * c = e` THEN ARITH_TAC;
      UNDISCH_TAC `(a + 1) * (n + 2) = J` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!K. K <= e * (a + 8 * c + 3) ==> &(S K) * &2 pow K =
    &S0` ASSUME_TAC THENL
   [X_GEN_TAC `K:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[SUB_ADD] THEN
    EXPAND_TAC "S0" THEN EXPAND_TAC "Q" THEN
    REWRITE_TAC[MULT_EXP; EXP_EXP] THEN REWRITE_TAC[MULT_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= Q /\ 2 <= S0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`e:num`; `g0N:num`; `Q:num`] SHARP_Q_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S0" THEN
    TRANS_TAC LE_TRANS `Q EXP 1` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[EXP_1]; ALL_TAC] THEN
    TRANS_TAC LE_TRANS `Q EXP (a + 8 * c + 3)` THEN CONJ_TAC THENL
     [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(S J) * &2 pow J = &S0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      free_in `&S0` (concl th))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * n * L <= (S:num->num) J` ASSUME_TAC THENL
   [SUBGOAL_THEN `&(2 * n * L) * &2 pow J <= &((S:num->num) J) *
     &2 pow J` MP_TAC THENL
     [REWRITE_TAC[ASSUME `&(S J) * &2 pow J = &S0`] THEN
      SUBGOAL_THEN `&(2 * n) * &2 pow J <= &Q pow (8 * c + 3)` MP_TAC THENL
       [MATCH_MP_TAC SHARP_QPOW_ABSORB THEN
        MAP_EVERY EXISTS_TAC [`e:num`; `g0N:num`; `n + 1`] THEN
        ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; EXP_ADD; EXP_1] THEN
          MESON_TAC[LT_POW2_REFL; LT_IMP_LE; LE_MULT_RCANCEL; MULT_SYM];
          MATCH_MP_TAC(ARITH_RULE
           `k <= e /\ e * 1 <= e * m ==> k <= e * m`) THEN
          REWRITE_TAC[LE_MULT_LCANCEL] THEN
          UNDISCH_TAC `J + 72 * n + 256 + 8 * c = e` THEN ARITH_TAC];
        ALL_TAC] THEN
      DISCH_TAC THEN EXPAND_TAC "S0" THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      TRANS_TAC REAL_LE_TRANS `(&(2 * n) * &2 pow J) * (&gN * &Q pow a)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `&Q pow (8 * c + 3) * (&gN * &Q pow a)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
        REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC];
      SIMP_TAC[REAL_LE_RMUL_EQ; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
      REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. 1 <= K /\ K <= e * (a + 8 * c + 3) ==> 2 * (S:num->num) K <= S0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&((S:num->num) K) * &2 pow K = &S0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `&S0` (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&((S:num->num) 0) * &2 pow 0 = &S0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `&S0` (concl th) && not(free_in `1 <= K` (concl th)))) THEN
      ARITH_TAC;
      REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_OF_NUM_EQ]];
    X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&((S:num->num) (K + 1)) * &2 pow (K + 1) = &S0 /\
                  &((S:num->num) K) * &2 pow K = &S0 /\
                  2 * (S:num->num) (K + 1) <= S0`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC; FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `2 * (S:num->num) (K + 1) <= S0` THEN UNDISCH_TAC `2 <=
        S0` THEN
      ARITH_TAC] THEN
    MATCH_MP_TAC EQ_IMP_LE THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&2 pow K` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&((S:num->num) (K + 1)) * &2 pow (K + 1) = &S0` THEN
    UNDISCH_TAC `&((S:num->num) K) * &2 pow K = &S0` THEN
    REWRITE_TAC[REAL_POW_ADD; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(S:num->num) J - n * L = Y` THEN UNDISCH_TAC `2 * n * L <=
      (S:num->num) J` THEN
    ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `(S:num->num) J - n * L = Y` THEN UNDISCH_TAC `2 * n * L <=
      (S:num->num) J` THEN
    ARITH_TAC;
    SUBGOAL_THEN `2 * (S:num->num) J <= S0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(S:num->num) J - n * L = Y` THEN UNDISCH_TAC `2 <= S0` THEN
      ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Part D. The log-domain inequalities of an extrapolation step (the         *)
(* Liouville loss at most c times the rational one plus the upper bound      *)
(* exponent, against the gain 8 c R(K) (S(K+1) + 1) log Q) and of Lemma 8.   *)
(* ------------------------------------------------------------------------- *)

let SHARP_EB_ALG_BOUND = prove
 (`!n h K D S0 sg Ec Ep lB T0 L Lm RK1 Qr lQ.
     1 <= h /\ &1 <= sg /\ &L + &2 <= &3 * sg /\ &((n - 1) * Lm) <= sg /\
     &n * &Lm <= sg /\ &0 <= T0 /\ T0 <= sg /\ lB <= &h /\ &1 <= Qr /\
     Ec <= &3 * &h * sg /\ Ep <= &38 * &h * &S0 /\
     &RK1 = &h * Qr pow (K + 1) /\
     log((&RK1 + &h) / &h) <= &(K + 1) * lQ + &1 /\
     &0 <= log(&1 + &D) /\ log(&1 + &D) <= &D
     ==> Ec + Ep + &(h * S0) * (&19 + log((&RK1 + &h) / &h)) +
         &((L + 2) * ((RK1 + 1) + h)) + &S0 * lB + &((n - 1) * Lm) +
         &RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D))
         <= &59 * &h * &S0 + &(K + 1) * &h * &S0 * lQ +
            (&16 + &D) * (&h * sg * Qr pow (K + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &h` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= Qr pow (K + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W1 = &h * sg * Qr pow (K + 1)` THEN
  SUBGOAL_THEN `&h * sg <= W1 /\ sg <= &h * sg /\ &1 <= &h * sg`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W1" THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&h <= &RK1 /\ &RK1 * sg = W1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "W1" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(h * S0) * (&19 + log((&RK1 + &h) / &h)) <=
    &20 * &h * &S0 + &(K + 1) * &h * &S0 * lQ`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&h * &S0) * (&20 + &(K + 1) * lQ)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
        ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&((L + 2) * ((RK1 + 1) + h)) <= &9 * W1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    TRANS_TAC REAL_LE_TRANS `(&3 * sg) * (&3 * &RK1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN
      MP_TAC(SPEC `L:num` REAL_POS) THEN MP_TAC(SPEC `RK1:num` REAL_POS) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM(ASSUME `&RK1 * sg = W1`)] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&S0 * lB <= &h * &S0` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D)) <= (&3 + &D) * W1`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&RK1 * (&3 * sg + sg * &D)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH
       `t <= s /\ y <= z ==> &3 * t + y <= &3 * s + z`) THEN
      ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
      REWRITE_TAC[GSYM(ASSUME `&RK1 * sg = W1`)] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&(h * S0) * (&19 + log((&RK1 + &h) / &h)) <=
     &20 * &h * &S0 + &(K + 1) * &h * &S0 * lQ`;
    `&((L + 2) * ((RK1 + 1) + h)) <= &9 * W1`;
    `&S0 * lB <= &h * &S0`;
    `&RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D)) <= (&3 + &D) * W1`;
    `Ec <= &3 * &h * sg`; `Ep <= &38 * &h * &S0`;
    `&((n - 1) * Lm) <= sg`; `&h * sg <= W1`; `sg <= &h * sg`] THEN
  REAL_ARITH_TAC);;

let SHARP_STEP_INEQ_ALG = prove
 (`!n h K c D S0 sg Ec Ep lB T0 L Lm RK RK1 SK1 NRK rhoK Qr lQ.
     1 <= h /\ 1 <= c /\ D <= c /\ &1 <= sg /\ &L + &2 <= &3 * sg /\
     &((n - 1) * Lm) <= sg /\ &n * &Lm <= sg /\ &0 <= T0 /\ T0 <= sg /\
     lB <= &h /\ &1 <= Qr /\
     Ec <= &3 * &h * sg /\ Ep <= &38 * &h * &S0 /\
     &RK = &h * Qr pow K /\ &RK1 = &h * Qr pow (K + 1) /\
     &NRK = &4 * Qr pow (8 * c) * &RK1 + &1 /\
     rhoK = &4 * Qr pow (8 * c) * &RK1 /\
     &SK1 * &2 pow (K + 1) = &S0 /\
     log((&RK1 + &h) / &h) <= &(K + 1) * lQ + &1 /\
     &2 pow (K + 1) * &31 * sg * Qr pow (K + 1 + 8 * c) <= Qr pow K * &S0 /\
     &2 pow (K + 1) <= &2 * Qr pow K /\
     &2 pow (K + 1) * &(K + 1) <= &2 * Qr pow K /\
     &c * (&17 + &2 * &c) <= Qr pow (8 * c) /\
     &0 <= log(&1 + &D) /\ log(&1 + &D) <= &D /\ &120 <= lQ
     ==> Ec + Ep + &((L + 2) * (NRK + h)) + &S0 * lB + &((n - 1) * Lm) +
         rhoK * T0 +
         (&c * ((Ec + Ep + &(h * S0) * (&19 + log((&RK1 + &h) / &h)) +
                 &((L + 2) * ((RK1 + 1) + h)) + &S0 * lB + &((n - 1) * Lm) +
                 &RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D))) +
                log(&c)) + &1) + &3
         <= &8 * &RK * (&SK1 + &1) * (&c * lQ)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `h:num`; `K:num`; `D:num`; `S0:num`; `sg:real`;
                `Ec:real`; `Ep:real`; `lB:real`; `T0:real`; `L:num`; `Lm:num`;
                `RK1:num`; `Qr:real`; `lQ:real`] SHARP_EB_ALG_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `EB = Ec + Ep + &(h * S0) * (&19 + log((&RK1 + &h) / &h)) +
         &((L + 2) * ((RK1 + 1) + h)) + &S0 * lB + &((n - 1) * Lm) +
         &RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &c /\ &D <= &c` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Qr pow K /\ &1 <= Qr pow (K + 1) /\
                &1 <= Qr pow (8 * c) /\
                Qr pow (8 * c) * Qr pow (K + 1) = Qr pow (K + 1 + 8 * c)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `W1 = &h * sg * Qr pow (K + 1)` THEN
  ABBREV_TAC `Wt = &h * sg * Qr pow (K + 1 + 8 * c)` THEN
  SUBGOAL_THEN `&1 <= W1 /\ &h * sg <= W1 /\ Qr pow (8 * c) * W1 = Wt /\
                &h * sg <= Wt /\ &1 <= &h * sg`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &h * sg` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&h * sg <= W1` ASSUME_TAC THENL
     [EXPAND_TAC "W1" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `Qr pow (8 * c) * W1 = Wt` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["W1"; "Wt"] THEN
      REWRITE_TAC[GSYM(ASSUME
       `Qr pow (8 * c) * Qr pow (K + 1) = Qr pow (K + 1 + 8 * c)`)] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `W1:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&((L + 2) * (NRK + h)) <= &18 * Wt /\ rhoK * T0 <= &4 * Wt`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&h <= Qr pow (8 * c) * &RK1` ASSUME_TAC THENL
     [REWRITE_TAC[ASSUME `&RK1 = &h * Qr pow (K + 1)`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(a:real) * h * b = h * a * b`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sg * (Qr pow (8 * c) * &RK1) = Wt` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `&h * sg * Qr pow (K + 1 + 8 * c) = Wt`)) THEN
      REWRITE_TAC[ASSUME `&RK1 = &h * Qr pow (K + 1)`] THEN
      REWRITE_TAC[GSYM(ASSUME
       `Qr pow (8 * c) * Qr pow (K + 1) = Qr pow (K + 1 + 8 * c)`)] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      TRANS_TAC REAL_LE_TRANS `(&3 * sg) * (&6 * Qr pow (8 * c) * &RK1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        MP_TAC(SPEC `L:num` REAL_POS) THEN MP_TAC(SPEC `NRK:num` REAL_POS) THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `sg * (Qr pow (8 * c) * &RK1) = Wt` THEN REAL_ARITH_TAC];
      REWRITE_TAC[ASSUME `rhoK = &4 * Qr pow (8 * c) * &RK1`] THEN
      TRANS_TAC REAL_LE_TRANS `(&4 * Qr pow (8 * c) * &RK1) * sg` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `sg * (Qr pow (8 * c) * &RK1) = Wt` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&c * (EB + log(&c)) + &1 <=
    &59 * &c * (&h * &S0) + &c * &(K + 1) * &h * &S0 * lQ + Wt`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `log(&c) <= &c /\ &0 <= &c` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC LOG_LE_SELF; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&c * (&16 + &D) * W1 + &c * log(&c) + &1 <= Wt`
    ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `(&c * (&17 + &2 * &c)) * W1` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `&c * log(&c) <= &c * &c` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `&c * (&16 + &D) <= &c * (&16 + &c) /\
                      &1 * &1 <= &c * W1 /\ &c * &c <= (&c * &c) * W1`
        MP_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
            GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        SUBGOAL_THEN `(&c * (&16 + &D)) * W1 <= (&c * (&16 + &c)) * W1`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `Qr pow (8 * c) * W1 = Wt`)) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&c * EB <= &c * (&59 * &h * &S0 + &(K + 1) * &h * &S0 * lQ +
                       (&16 + &D) * W1)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&c * (&16 + &D) * W1 + &c * log(&c) + &1 <= Wt` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `t = &2 pow (K + 1)` THEN
  ABBREV_TAC `Z = &h * Qr pow K * &S0` THEN
  SUBGOAL_THEN `&0 < t /\ &0 <= &S0 /\ &0 <= Z /\ &0 <= lQ`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN EXPAND_TAC "Z" THEN REWRITE_TAC[REAL_POS] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&S0 * lB <= &h * &S0` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t * ((&39 + &59 * &c) * (&h * &S0) + &c * &(K + 1) * &h * &S0 * lQ +
         &31 * Wt) <=
    t * (&8 * &RK * (&SK1 + &1) * (&c * lQ))`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LCANCEL_IMP o
               CONJ (ASSUME `&0 < t`)) THEN
    SUBGOAL_THEN `sg <= &h * sg` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&c * (EB + log(&c)) + &1 <=
       &59 * &c * (&h * &S0) + &c * &(K + 1) * &h * &S0 * lQ + Wt`;
      `&((L + 2) * (NRK + h)) <= &18 * Wt`; `rhoK * T0 <= &4 * Wt`;
      `&S0 * lB <= &h * &S0`; `Ec <= &3 * &h * sg`; `Ep <= &38 * &h * &S0`;
      `&((n - 1) * Lm) <= sg`; `&h * sg <= Wt`; `&1 <= &h * sg`;
      `&1 <= sg`] THEN
    REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `t * (&h * &S0) <= &2 * Z` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&2 * Qr pow K) * (&h * &S0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
      EXPAND_TAC "Z" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t * &(K + 1)) * (&h * &S0 * lQ) <= &2 * Z * lQ`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&2 * Qr pow K) * (&h * &S0 * lQ)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS];
      EXPAND_TAC "Z" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t * &31 * Wt <= Z` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `&h * sg * Qr pow (K + 1 + 8 * c) = Wt`)) THEN
    EXPAND_TAC "Z" THEN
    TRANS_TAC REAL_LE_TRANS
     `&h * (t * &31 * sg * Qr pow (K + 1 + 8 * c))` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t * (&8 * &RK * (&SK1 + &1) * (&c * lQ)) =
    &8 * &c * Z * lQ + &8 * &c * t * &RK * lQ /\
    &0 <= &8 * &c * t * &RK * lQ /\
    (&79 + &118 * &c) * Z <= &6 * &c * Z * lQ`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Z" THEN
      REWRITE_TAC[GSYM(ASSUME `&SK1 * t = &S0`);
                  ASSUME `&RK = &h * Qr pow K`] THEN
      REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `Z * (&79 + &118 * c) <= Z * (&6 * c * lQ)
        ==> (&79 + &118 * c) * Z <= &6 * c * Z * lQ`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&c * &120 <= &c * lQ` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `t * (&8 * &RK * (&SK1 + &1) * (&c * lQ)) =
                      &8 * &c * Z * lQ + &8 * &c * t * &RK * lQ`] THEN
  SUBGOAL_THEN
   `t * ((&39 + &59 * &c) * (&h * &S0)) <= (&39 + &59 * &c) * (&2 * Z) /\
    t * (&c * &(K + 1) * &h * &S0 * lQ) <= &c * (&2 * Z * lQ)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `t * a * b:real = a * t * b`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [REAL_ARITH
       `t * c * k * h * s * l:real = c * (t * k) * h * s * l`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`t * ((&39 + &59 * &c) * (&h * &S0)) <= (&39 + &59 * &c) * (&2 * Z)`;
    `t * (&c * &(K + 1) * &h * &S0 * lQ) <= &c * (&2 * Z * lQ)`;
    `t * &31 * Wt <= Z`; `(&79 + &118 * &c) * Z <= &6 * &c * Z * lQ`;
    `&0 <= &8 * &c * t * &RK * lQ`] THEN
  REAL_ARITH_TAC);;

let SHARP_LEMMA8_LOGINEQ_GEN = prove
 (`!n h J S0 sg X Y SJ Ec Ep lB T0 L Lm NX rhoX E8 V lQ.
     1 <= h /\ 1 <= X /\ &1 <= sg /\ &L + &2 <= &3 * sg /\
     &((n - 1) * Lm) <= sg /\ &0 <= T0 /\ T0 <= sg /\ &0 <= lB /\
     lB <= &h /\ Ec <= &3 * &h * sg /\ Ep <= &38 * &h * &S0 /\
     &1 <= V /\ &h <= &X /\
     &NX = &4 * V * &X + &1 /\ rhoX = &4 * V * &X /\
     &SJ <= &2 * &Y /\ &SJ * &2 pow J = &S0 /\
     &2 pow J * &78 * &h <= &X /\
     &2 pow J * &52 * sg * V <= &S0 /\
     &2 pow J * E8 <= &2 * &X * &S0 /\ &2 pow J * &3 <= &X * &S0 /\
     &1 <= lQ
     ==> Ec + Ep + &((L + 2) * (NX + h)) + &S0 * lB + &((n - 1) * Lm) +
         rhoX * T0 + E8 + &3 <= &8 * &X * (&Y + &1) * lQ`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &X` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &S0 /\ &0 < &2 pow J /\ &1 <= &2 pow J`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&((L + 2) * (NX + h)) <= &18 * sg * V * &X /\
                rhoX * T0 <= &4 * sg * V * &X /\
                &h * sg <= sg * V * &X /\ sg <= sg * V * &X /\
                &S0 * lB <= &h * &S0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= V * &X /\ &h <= V *
     &X` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      TRANS_TAC REAL_LE_TRANS `(&3 * sg) * (&6 * V * &X)` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      MP_TAC(SPEC `L:num` REAL_POS) THEN MP_TAC(SPEC `NX:num` REAL_POS) THEN
      REWRITE_TAC[ASSUME `&NX = &4 * V * &X + &1`] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[ASSUME `rhoX = &4 * V * &X`] THEN
      TRANS_TAC REAL_LE_TRANS `(&4 * V * &X) * sg` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ec + Ep + &((L + 2) * (NX + h)) + &S0 * lB +
                &((n - 1) * Lm) + rhoX * T0 + E8 + &3 <=
                &39 * &h * &S0 + &26 * sg * V * &X + E8 + &3`
  ASSUME_TAC THENL
   [UNDISCH_TAC `Ec <= &3 * &h * sg` THEN UNDISCH_TAC `Ep <= &38 * &h *
     &S0` THEN
    UNDISCH_TAC `&((L + 2) * (NX + h)) <= &18 * sg * V * &X` THEN
    UNDISCH_TAC `rhoX * T0 <= &4 * sg * V * &X` THEN
    UNDISCH_TAC `&h * sg <= sg * V * &X` THEN
    UNDISCH_TAC `sg <= sg * V * &X` THEN
    UNDISCH_TAC `&S0 * lB <= &h * &S0` THEN
    UNDISCH_TAC `&((n - 1) * Lm) <= sg` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow J * (&39 * &h * &S0 + &26 * sg * V * &X + E8 + &3)
                <= &4 * &X * &S0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 pow J * (&78 * &h) <= &X /\
                  &2 pow J * (&52 * sg * V * &X) <= &X * &S0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        TRANS_TAC REAL_LE_TRANS `&X * (&2 pow J * &52 * sg * V)` THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&S0 * (&2 pow J * (&78 * &h)) <= &S0 * &X` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&2 pow J * (&52 * sg * V * &X) <= &X * &S0` THEN
    UNDISCH_TAC `&2 pow J * E8 <= &2 * &X * &S0` THEN
    UNDISCH_TAC `&2 pow J * &3 <= &X * &S0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * &X * &S0 <= &2 pow J * (&8 * &X * (&Y + &1) * lQ)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&S0 <= &2 * &Y * &2 pow J /\
                  &Y <= (&Y + &1) * lQ` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `&SJ * &2 pow J = &S0`)) THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC;
        TRANS_TAC REAL_LE_TRANS `(&Y + &1) * &1` THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&4 * &X * (&2 * &Y * &2 pow J)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&2 pow J * (&8 * &X) * &Y` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&8 * &X * (&Y + &1) * lQ = (&8 * &X) * ((&Y + &1) *
      lQ)`]
    THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&39 * &h * &S0 + &26 * sg * V * &X + E8 +
    &3` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 pow J * (&39 * &h * &S0 + &26 * sg * V * &X + E8 +
    &3) <=
                &2 pow J * (&8 * &X * (&Y + &1) * lQ)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;


let SHARP_STEP_EPS_GEN = prove
 (`!S0 X RK RK1 SK1 Nl Ev.
     1 <= RK /\ RK <= X /\ 1 <= RK1 /\ RK1 <= X /\ SK1 + 1 <= S0 /\
     2 <= S0 /\ Nl <= X /\ Ev <= &6 * &X * &S0
     ==> log(&2 * &RK) + &SK1 + &(S0 * Nl) +
         (&SK1 + &1) * (log(&RK1) + &4 * &RK1) + Ev + &2
         <= &16 * &X * &S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &RK /\ &RK <= &X /\ &1 <= &RK1 /\ &RK1 <= &X /\
                &SK1 + &1 <= &S0 /\ &2 <= &S0 /\ &Nl <= &X`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * &RK) <= &2 * &X /\ &0 <= log(&RK1) /\
                log(&RK1) <= &X`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&2 * &RK` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_LE_SELF THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `&RK1` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOG_LE_SELF THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&SK1 + &1) * (log(&RK1) + &4 * &RK1) <= &S0 * (&5 * &X) /\
    &(S0 * Nl) <= &S0 * &X /\ &X * &2 <= &X * &S0 /\ &1 * &S0 <= &X * &S0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `&(S0 * Nl) <= &S0 * &X` THEN
  UNDISCH_TAC `(&SK1 + &1) * (log(&RK1) + &4 * &RK1) <= &S0 * (&5 * &X)` THEN
  UNDISCH_TAC `Ev <= &6 * &X * &S0` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC);;

let SHARP_STEP_EV_ALG = prove
 (`!h K J c D S0 sg X EB Qr lQ.
     1 <= h /\ 1 <= c /\ D <= c /\ K + 1 <= J /\ &1 <= Qr /\ &0 <= lQ /\
     &1 <= sg /\ &1 <= &S0 /\ &X = &h * Qr pow J /\
     EB <= &59 * &h * &S0 + &(K + 1) * &h * &S0 * lQ +
           (&16 + &D) * (&h * sg * Qr pow (K + 1)) /\
     &c * (&59 + &J * lQ) <= Qr pow J /\
     &c * (&16 + &2 * &c) * sg <= &S0 /\ &c pow 2 + &1 <= Qr pow J
     ==> &c * (EB + log(&c)) + &1 <= &6 * &X * &S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &c /\ &D <= &c /\ &(K + 1) <= &J`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `Qr pow (K + 1) <= Qr pow J /\ &1 <= Qr pow J /\
                &0 <= Qr pow (K + 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&c) <= &c /\ &0 <= &c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_LE_SELF; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&c * (&59 * &h * &S0 + &(K + 1) * &h * &S0 * lQ) <= &X * &S0 /\
    &c * ((&16 + &D) * (&h * sg * Qr pow (K + 1))) <= &X * &S0 /\
    &c * log(&c) + &1 <= &X * &S0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `(&h * &S0) * (&c * (&59 + &J * lQ))` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `&(K + 1) * lQ <= &J * lQ` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `&c * (&59 + &(K + 1) * lQ) <= &c * (&59 + &J * lQ)`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= &h * &S0` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[IMP_IMP] THEN
        DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL) THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC RAND_CONV
         [REAL_ARITH `(h * q) * s:real = (h * s) * q`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]]];
      TRANS_TAC REAL_LE_TRANS
       `(&h * Qr pow J) * (&c * (&16 + &2 * &c) * sg)` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `&c * (&16 + &D) <= &c * (&16 + &2 * &c)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `(&c * (&16 + &D)) * (&h * sg * Qr pow (K + 1)) <=
                      (&c * (&16 + &2 * &c)) * (&h * sg * Qr pow J)`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
            REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
            ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC];
      TRANS_TAC REAL_LE_TRANS `&c pow 2 + &1` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN
        SUBGOAL_THEN `&c * log(&c) <= &c * &c` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `Qr pow J` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      GEN_REWRITE_TAC RAND_CONV
       [REAL_ARITH `(h * q) * s:real = q * h * s`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_1_MUL THEN
                            ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&c * EB <= &c * (&59 * &h * &S0 + &(K + 1) * &h * &S0 * lQ +
                     (&16 + &D) * (&h * sg * Qr pow (K + 1)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &X * &S0` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&c * (&59 * &h * &S0 + &(K + 1) * &h * &S0 * lQ) <= &X * &S0`;
    `&c * ((&16 + &D) * (&h * sg * Qr pow (K + 1))) <= &X * &S0`;
    `&c * log(&c) + &1 <= &X * &S0`] THEN
  REAL_ARITH_TAC);;

let SHARP_EMMAX_ALG_BOUND = prove
 (`!n h L0 Lm pr B Ec Ep T0 S0 sg c D.
     1 <= h /\ 1 <= pr /\ &1 <= B /\ &1 <= sg /\ 1 <= c /\ D <= c /\
     Ec <= &3 * &h * sg /\ Ep <= &38 * &h * &S0 /\
     &L0 + &2 <= &3 * sg /\ &L0 <= sg /\ &n * &Lm <= sg /\
     &((n - 1) * L0) <= sg /\ &((n - 1) * Lm) <= sg /\ &n <= sg /\
     &0 <= T0 /\ T0 <= sg /\ log(&4 * B + &2) <= &h /\
     &0 <= log(&1 + &D) /\ log(&1 + &D) <= &D
     ==> &n * log(&pr) + log(&c) +
         (Ec + Ep + &(2 * h * (L0 + 2)) * log(&pr) +
          &L0 * (&18 * &(4 * h + pr * h)) +
          &((L0 + 2) * ((4 * h + 1) + h)) +
          &((n - 1) * L0) * log(&4 * B + &2) + &((n - 1) * Lm) +
          &(4 * h) * T0 + &(4 * h) * (&2 * T0 + &n * &Lm * log(&1 + &pr))) +
         &(4 * h) * (&n * &Lm * log(&1 + &D))
         <= &38 * &h * &S0 + &141 * &c * &pr * &h * sg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `h:num`; `L0:num`; `Lm:num`; `pr:num`; `B:real`;
                `Ec:real`; `Ep:real`; `T0:real`; `S0:num`; `sg:real`]
         SHARP_EMMAX_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &pr /\ &1 <= &c /\ &D <= &c`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&c) <= &c` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_LE_SELF THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &pr * &h * sg /\ &c * &1 <= &c * (&pr * &h * sg)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &pr * &h * sg` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(4 * h) * (&n * &Lm * log(&1 + &D)) <=
                &4 * &c * (&pr * &h * sg)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&n * &Lm * log(&1 + &D) <= sg * &D` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&(4 * h) * (sg * &D)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `(&(4 * h) * sg) * &D <= (&(4 * h) * sg) * (&c * &pr)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `&c * &1` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&136 * &pr * &h * sg <= &136 * &c * &pr * &h * sg`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&(4 * h) * (&n * &Lm * log(&1 + &D)) <= &4 * &c * (&pr * &h * sg)`;
    `&136 * &pr * &h * sg <= &136 * &c * &pr * &h * sg`;
    `&c * &1 <= &c * (&pr * &h * sg)`; `log(&c) <= &c`] THEN
  REAL_ARITH_TAC);;

let SHARP_E8_BOUND_ALG = prove
 (`!n a b c J h gN pr Qr S0 X sg.
     1 <= n /\ 1 <= c /\ &1 <= Qr /\ 1 <= h /\ 1 <= gN /\
     &pr <= &2 pow 70 * Qr pow (a + 1) /\
     (a + 1) * (n + 2) = J /\ &X = &h * Qr pow J /\
     &S0 = &gN * Qr pow (a + b) /\ sg = (&n + &1) * &gN * Qr pow (a + 1) /\
     &2 pow (J + 70 * n + 6) * &c <= Qr pow (2 * a + 2) /\
     &2 pow (J + 71 * n + 78) * &c pow 2 <= Qr pow (a + b)
     ==> &2 pow J * (&(pr EXP n) * &c *
                     (&38 * &h * &S0 + &141 * &c * &pr * &h * sg))
         <= &2 * &X * &S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &2 pow J /\ &0 <= Qr pow (a + 1) /\ &0 <= &h * &S0 /\
                &0 <= &h * &gN /\ &0 <= &pr pow n /\ &0 <= &2 pow (70 * n) /\
                &0 <= Qr pow ((a + 1) * n) /\
                &0 <= Qr pow ((a + 1) * (n + 1)) /\
                &0 <= &c /\ &0 <= &c pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN NO_TAC) THEN
    REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&pr pow n <= &2 pow (70 * n) * Qr pow ((a + 1) * n) /\
                &pr * &pr pow n <=
                &2 pow (70 * n + 70) * Qr pow ((a + 1) * (n + 1))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow); GSYM ADD1] THEN
    REWRITE_TAC[GSYM REAL_POW_POW; GSYM REAL_POW_MUL] THEN
    REWRITE_TAC[ARITH_RULE `70 * n + 70 = 70 * SUC n`; GSYM REAL_POW_POW;
                GSYM REAL_POW_MUL; ADD1] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `Qr pow (2 * a + 2) * Qr pow ((a + 1) * n) = Qr pow J /\
                Qr pow ((a + 1) * (n + 1)) * Qr pow (a + 1) = Qr pow J`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD; GSYM(ASSUME `(a + 1) * (n + 2) = J`)] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow J * &38 * &c * &pr pow n <= Qr pow J` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `(&2 pow (J + 70 * n + 6) * &c) * Qr pow ((a + 1) * n)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM(ASSUME
       `Qr pow (2 * a + 2) * Qr pow ((a + 1) * n) = Qr pow J`)] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN
     `(&2 pow J * &38 * &c) * &pr pow n <=
      (&2 pow J * &38 * &c) * (&2 pow (70 * n) * Qr pow ((a + 1) * n))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &2 pow J * &c * &2 pow (70 * n) * Qr pow ((a + 1) * n)`
    MP_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 pow J * &141 * (&n + &1) * &c pow 2 * (&pr * &pr pow n) *
    Qr pow (a + 1) <= Qr pow (a + b) * Qr pow J`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `(&2 pow (J + 71 * n + 78) * &c pow 2) *
      (Qr pow ((a + 1) * (n + 1)) * Qr pow (a + 1))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&141 * (&n + &1) <= &2 pow 8 * &2 pow n` ASSUME_TAC THENL
     [SUBGOAL_THEN `&n + &1 <= &2 pow n` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
        MESON_TAC[LT_POW2_REFL; ARITH_RULE `a < b ==> a + 1 <= b`];
        CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&2 pow (J + 71 * n + 78) =
      (&2 pow J * &2 pow (70 * n + 70)) * (&2 pow 8 * &2 pow n)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &2 pow J * &2 pow (70 * n + 70) /\
                  &0 <= Qr pow ((a + 1) * (n + 1)) * Qr pow (a + 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `(&2 pow J * &c pow 2 * &141 * (&n + &1)) *
      (&2 pow (70 * n + 70) * Qr pow ((a + 1) * (n + 1)) * Qr pow (a + 1))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(&2 pow J * &c pow 2 * &141 * (&n + &1)) *
        ((&pr * &pr pow n) * Qr pow (a + 1)) <=
        (&2 pow J * &c pow 2 * &141 * (&n + &1)) *
        ((&2 pow (70 * n + 70) * Qr pow ((a + 1) * (n + 1))) *
         Qr pow (a + 1))`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&2 pow J * &c pow 2) * (&141 * (&n + &1)) *
      (&2 pow (70 * n + 70) * Qr pow ((a + 1) * (n + 1)) * Qr pow (a + 1)) <=
      (&2 pow J * &c pow 2) * (&2 pow 8 * &2 pow n) *
      (&2 pow (70 * n + 70) * Qr pow ((a + 1) * (n + 1)) * Qr pow (a + 1))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 pow J * &38 * &c * &pr pow n) * (&h * &S0) <=
    Qr pow J * (&h * &S0) /\
    (&2 pow J * &141 * (&n + &1) * &c pow 2 * (&pr * &pr pow n) *
     Qr pow (a + 1)) * (&h * &gN) <=
    (Qr pow (a + b) * Qr pow J) * (&h * &gN)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `sg = (&n + &1) * &gN * Qr pow (a + 1)`;
              ASSUME `&X = &h * Qr pow J`; ASSUME `&S0 = &gN * Qr pow (a + b)`;
              GSYM REAL_OF_NUM_POW; REAL_POW_2] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part E. Assembly. The step and Lemma 8 hypotheses of                      *)
(* SHARP_CORE_PARAMETRIC in the integer form for the design of Part C        *)
(* (radius Q^(8 c)), then the design facts SHARP_CORE_DESIGN: for the data,  *)
(* an analytic size Bq, degree data dd1 with dd1 r <= D1 and                 *)
(* nproduct dd1 <= c, naturals g0N >= g0, gN >= log A + D + 5,               *)
(* h >= log(4 Bq + 2) and a prime pr in (Q^(a+1), 2^70 Q^(a+1)], the numeric *)
(* hypotheses of the parametric core hold once |Lambda| <= exp(-17 X S0);    *)
(* then the data lemma for integer coefficients SHARP_CORE_DATA_ALG (Bq = B, *)
(* dd1 = dd, c = D^n) and SHARP_CORE_ALGEBRAIC. The remaining parameters are *)
(*   L0 = L = gN Q^a, Ln = Q^(a+1), Lm = gN Q^(a+1), S0 = gN Q^(a+8c+3),     *)
(*   R K = h Q^K, S K = S0 / 2^K, X = R J, Y = S J - n L,                    *)
(*   rho K = 4 Q^(8c) R(K+1), NR K = rho K + 1, rhoX = 4 Q^(8c) X,           *)
(*   NX = rhoX + 1, K8 = 4 h, T0 = L (n-1) (g0 + D + 4) +                    *)
(*   Ln (log A + D + 5),                                                     *)
(*   d0 = Ln |Lambda|, Nl = 2 (n-1) (g0N + D + 4) + 1, eps = exp(-16 X S0),  *)
(*   V K = exp(-(c (EB K + log c) + 1)), EB K the Liouville exponent at      *)
(*   R(K+1) (SHARP_LIOU5_ALG_GE_EXP, with D1 for D).                         *)
(* ------------------------------------------------------------------------- *)

let SHARP_STEP_COND_ALG = prove
 (`!n h L Lv Lm P B S0 T0 d0 (dd:num->num) (H:num->real) Hb Ec Ep sg c D Q
    E X Nl J K RK RK1 SK SK1 rhoK NRK VK.
     1 <= h /\ 1 <= c /\ D <= c /\ &2 <= B /\
     &1 <= sg /\ &L + &2 <= &3 * sg /\ &((n - 1) * Lm) <= sg /\
     &n * &Lm <= sg /\ &0 <= T0 /\ T0 <= sg /\ 2 <= S0 /\ &2 <= &Q /\
     &128 <= log(&Q) /\ log(&4 * B + &2) <= &h /\
     &0 <= Ec /\ Ec <= &3 * &h * sg /\ &0 <= Ep /\ Ep <= &38 * &h * &S0 /\
     &(CARD(sharp_index h L Lv n)) <= exp Ec /\ &0 <= P /\ P <= exp Ep /\
     (!r. r IN 1..n ==> &1 <= H r /\ 1 <= dd r /\ dd r <= D /\ Lv r <= Lm) /\
     nproduct(1..n) dd <= c /\ sum(1..n) (\r. &(Lv r) * log(H r)) <= T0 /\
     (!N z. N <= X + 1 /\ &0 <= z /\ z <= &X
            ==> sharp_errb n h L Lv Lm P B S0 T0 d0 N z <= exp(--(E + &2))) /\
     &16 * &X * &S0 = E /\ &X = &h * &Q pow J /\ Nl <= X /\ K < J /\
     RK = h * Q EXP K /\ RK1 = h * Q EXP (K + 1) /\ RK1 <= X /\
     rhoK = &4 * &Q pow (8 * c) * &RK1 /\
     NRK = 4 * Q EXP (8 * c) * RK1 + 1 /\
     2 * SK1 <= SK /\ &SK1 * &2 pow (K + 1) = &S0 /\ SK1 + 1 <= S0 /\
     &2 pow (K + 1) * &31 * sg * &Q pow (K + 1 + 8 * c) <= &Q pow K * &S0 /\
     &2 pow (K + 1) <= &2 * &Q pow K /\
     &2 pow (K + 1) * &(K + 1) <= &2 * &Q pow K /\
     &c * (&17 + &2 * &c) <= &Q pow (8 * c) /\
     &c * (&59 + &J * log(&Q)) <= &Q pow J /\
     &c * (&16 + &2 * &c) * sg <= &S0 /\ &c pow 2 + &1 <= &Q pow J /\
     VK = exp(--(&c * ((Ec + Ep + &(h * S0) * (&19 + log((&RK1 + &h) / &h)) +
                        &((L + 2) * ((RK1 + 1) + h)) +
                        &S0 * log(&4 * B + &2) + &((n - 1) * Lm) +
                        &RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D))) +
                       log(&c)) + &1))
     ==> RK <= RK1 /\ 2 * SK1 <= SK /\ &4 * &RK1 <= rhoK /\
         rhoK + &1 <= &NRK /\
         (!l. RK < l /\ l <= RK1
              ==> sharp_errb n h L Lv Lm P B S0 T0 d0 (l + 1) (&l)
                  <= exp(--E) /\
                  VK + sharp_errb n h L Lv Lm P B S0 T0 d0 (l + 1) (&l) <
                  sharp_liou5 n h L Lv P S0 dd H (\r. 1) Hb
                    (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm))
                    (\s. 0) (\s. &1) l) /\
         &2 * sharp_ubd n h L Lv Lm P B S0 T0 NRK rhoK *
         (&4 * &RK1 / rhoK) pow (RK * (SK1 + 1)) +
         exp(--E) * &2 * &RK * &2 pow SK1 * exp(&(S0 * Nl)) *
         (&RK1 * &16 pow RK1) pow (SK1 + 1)
         <= VK`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &h /\ &2 <= &S0 /\ &0 < &Q /\ &1 <= &Q /\ 2 <= Q`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `&2 <= &Q` THEN REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&RK = &h * &Q pow K /\ &RK1 = &h * &Q pow (K + 1) /\
    &NRK = &4 * &Q pow (8 * c) * &RK1 + &1`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= RK /\ 1 <= RK1 /\ RK <= RK1 /\ RK <= X`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `h * Q EXP K <= h * Q EXP (K + 1) /\ 1 <= h * Q EXP K`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP;
                  ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
      MAP_EVERY UNDISCH_TAC [`2 <= Q`; `1 <= h`] THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`h * Q EXP K <= h * Q EXP (K + 1)`; `1 <= h * Q EXP K`; `RK1 <= X`;
      `RK = h * Q EXP K`; `RK1 = h * Q EXP (K + 1)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &Q pow (8 * c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&1 + &D) /\ log(&1 + &D) <= &D /\ &0 <= log(&c)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN MP_TAC(SPEC `D:num` REAL_POS) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_LE THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  ABBREV_TAC
   `EBK = Ec + Ep + &(h * S0) * (&19 + log((&RK1 + &h) / &h)) +
          &((L + 2) * ((RK1 + 1) + h)) + &S0 * log(&4 * B + &2) +
          &((n - 1) * Lm) + &RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D))` THEN
  ABBREV_TAC `Ev0 = &c * (EBK + log(&c))` THEN
  SUBGOAL_THEN `log((&RK1 + &h) / &h) <= &(K + 1) * log(&Q) + &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `RK1 = h * Q EXP (K + 1)`] THEN
    MATCH_MP_TAC SHARP_LOG_RATIO_STEP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EBK <= &59 * &h * &S0 + &(K + 1) * &h * &S0 * log(&Q) +
           (&16 + &D) * (&h * sg * &Q pow (K + 1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "EBK" THEN MATCH_MP_TAC SHARP_EB_ALG_BOUND THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ev0 + &1 <= &6 * &X * &S0` ASSUME_TAC THENL
   [EXPAND_TAC "Ev0" THEN MATCH_MP_TAC SHARP_STEP_EV_ALG THEN
    MAP_EVERY EXISTS_TAC [`h:num`; `K:num`; `J:num`; `D:num`; `sg:real`;
                          `&Q`; `log(&Q)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `K < J` THEN ARITH_TAC;
      UNDISCH_TAC `&128 <= log(&Q)` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&2 <= &S0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ASSUME `rhoK = &4 * &Q pow (8 * c) * &RK1`] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&4 * x = &4 * &1 * x`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &4`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS];
    REWRITE_TAC[ASSUME `rhoK = &4 * &Q pow (8 * c) * &RK1`;
                ASSUME `&NRK = &4 * &Q pow (8 * c) * &RK1 + &1`; REAL_LE_REFL];
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `sharp_errb n h L Lv Lm P B S0 T0 d0 (l + 1) (&l) <= exp(--(E + &2))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
      MAP_EVERY UNDISCH_TAC [`l <= RK1`; `RK1 <= X`] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `exp(--(E + &2))` THEN
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[REAL_EXP_MONO_LE] THEN
                                REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `exp(--Ev0) <=
      sharp_liou5 n h L Lv P S0 dd H (\r. 1) Hb
        (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0) (\s. &1) l`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `Lv:num->num`; `Lm:num`;
                    `P:real`; `B:real`; `S0:num`; `dd:num->num`;
                    `H:num->real`; `Hb:real`; `l:num`; `Ec:real`; `Ep:real`;
                    `T0:real`; `D:num`; `c:num`] SHARP_LIOU5_ALG_GE_EXP) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        UNDISCH_TAC `&2 <= B` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> b <= c ==> a <= c`) THEN
      REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN EXPAND_TAC "Ev0" THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_LE_RADD] THEN
      EXPAND_TAC "EBK" THEN
      SUBGOAL_THEN `&0 < &h /\ &l <= &RK1 /\ &0 < (&l + &h) / &h`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `&1 <= &h` THEN REAL_ARITH_TAC;
          REWRITE_TAC[REAL_OF_NUM_LE] THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC REAL_LT_DIV THEN MP_TAC(SPEC `l:num` REAL_POS) THEN
          UNDISCH_TAC `&1 <= &h` THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `log((&l + &h) / &h) <= log((&RK1 + &h) / &h) /\
        &((L + 2) * ((l + 1) + h)) <= &((L + 2) * ((RK1 + 1) + h)) /\
        &l * (&3 * T0 + &n * &Lm * log(&1 + &D)) <=
        &RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D))`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          SIMP_TAC[REAL_LE_DIV2_EQ; ASSUME `&0 < &h`] THEN
          UNDISCH_TAC `&l <= &RK1` THEN REAL_ARITH_TAC;
          REWRITE_TAC[REAL_OF_NUM_LE; LE_MULT_LCANCEL] THEN
          UNDISCH_TAC `l <= RK1` THEN ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 <= x /\ &0 <= y ==> &0 <= &3 * x + y`) THEN
          CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          REWRITE_TAC[REAL_POS] THEN FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `&(h * S0) * (&19 + log((&l + &h) / &h)) <=
        &(h * S0) * (&19 + log((&RK1 + &h) / &h))`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        UNDISCH_TAC `log((&l + &h) / &h) <= log((&RK1 + &h) / &h)` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`&((L + 2) * ((l + 1) + h)) <= &((L + 2) * ((RK1 + 1) + h))`;
        `&l * (&3 * T0 + &n * &Lm * log(&1 + &D)) <=
         &RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D))`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBST1_TAC(ASSUME `VK = exp(--(Ev0 + &1))`) THEN
    MP_TAC(SPEC `Ev0:real` EXP_NEG_SMALL2) THEN
    SUBGOAL_THEN `exp(--(E + &2)) <= exp(--(Ev0 + &2))` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MAP_EVERY UNDISCH_TAC [`Ev0 + &1 <= &6 * &X * &S0`;
                             `&16 * &X * &S0 = E`] THEN
      SUBGOAL_THEN `&0 <= &X * &S0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`exp(--Ev0) <=
       sharp_liou5 n h L Lv P S0 dd H (\r. 1) Hb
         (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0) (\s. &1)
         l`;
      `sharp_errb n h L Lv Lm P B S0 T0 d0 (l + 1) (&l) <=
       exp(--(E + &2))`] THEN
    REWRITE_TAC[REAL_ARITH `--(&c * x + &1) = --(&c * x + &1)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(ASSUME `VK = exp(--(Ev0 + &1))`) THEN
  MP_TAC(SPECL
   [`sharp_ubd n h L Lv Lm P B S0 T0 NRK rhoK`; `rhoK:real`; `RK:num`;
    `RK1:num`; `SK1:num`; `&(S0 * Nl)`; `&Q pow c`;
    `Ec + Ep + &((L + 2) * (NRK + h)) + &S0 * log(&4 * B + &2) +
     &((n - 1) * Lm) + rhoK * T0`;
    `Ev0 + &1`; `E:real`] SHARP_STEP_ABS) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    TRANS_TAC REAL_LTE_TRANS `&Q` THEN CONJ_TAC THENL
     [UNDISCH_TAC `&2 <= &Q` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; UNDISCH_TAC `1 <= c` THEN ARITH_TAC];
    REWRITE_TAC[sharp_ubd] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE] THEN
    TRY(MATCH_MP_TAC REAL_POW_LE THEN UNDISCH_TAC `&2 <= B` THEN
        REAL_ARITH_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SHARP_UBD_LE_EXP THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `&2 <= B` THEN REAL_ARITH_TAC;
    REWRITE_TAC[ASSUME `rhoK = &4 * &Q pow (8 * c) * &RK1`; REAL_POW_POW] THEN
    SUBGOAL_THEN `c * 8 = 8 * c` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&RK1 = &0) /\ ~(&Q pow (8 * c) = &0)` MP_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN UNDISCH_TAC `1 <= RK1` THEN
        ARITH_TAC;
        MATCH_MP_TAC REAL_POW_NZ THEN UNDISCH_TAC `&2 <= &Q` THEN
        REAL_ARITH_TAC];
      CONV_TAC REAL_FIELD];
    MP_TAC(SPECL [`n:num`; `h:num`; `K:num`; `c:num`; `D:num`; `S0:num`;
                  `sg:real`; `Ec:real`; `Ep:real`; `log(&4 * B + &2)`;
                  `T0:real`; `L:num`; `Lm:num`; `RK:num`; `RK1:num`;
                  `SK1:num`; `NRK:num`; `rhoK:real`; `&Q`; `log(&Q)`]
                 SHARP_STEP_INEQ_ALG) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `&128 <= log(&Q)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[LOG_POW; ASSUME `&0 < &Q`] THEN
    REWRITE_TAC[ASSUME
     `Ec + Ep + &(h * S0) * (&19 + log((&RK1 + &h) / &h)) +
      &((L + 2) * ((RK1 + 1) + h)) + &S0 * log(&4 * B + &2) +
      &((n - 1) * Lm) + &RK1 * (&3 * T0 + &n * &Lm * log(&1 + &D)) = EBK`;
     ASSUME `&c * (EBK + log(&c)) = Ev0`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM(ASSUME `&16 * &X * &S0 = E`)] THEN
    MATCH_MP_TAC SHARP_STEP_EPS_GEN THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let SHARP_LEMMA8_COND_ALG = prove
 (`!n h L Lv Lm P B S0 T0 d0 (dd:num->num) (H:num->real) Hb Ec Ep sg c D Q
    E X Y SJ Nl J aQ gN pr NX rhoX (m:num->num) l.
     1 <= n /\ 1 <= h /\ 1 <= c /\ D <= c /\ &2 <= B /\ 1 <= gN /\
     &1 <= sg /\ &L + &2 <= &3 * sg /\ &L <= sg /\ &n * &Lm <= sg /\
     &((n - 1) * L) <= sg /\ &((n - 1) * Lm) <= sg /\ &n <= sg /\
     &0 <= T0 /\ T0 <= sg /\ 2 <= S0 /\ &2 <= &Q /\ &128 <= log(&Q) /\
     log(&4 * B + &2) <= &h /\
     &0 <= Ec /\ Ec <= &3 * &h * sg /\ &0 <= Ep /\ Ep <= &38 * &h * &S0 /\
     &(CARD(sharp_index h L Lv n)) <= exp Ec /\ &0 <= P /\ P <= exp Ep /\
     (!r. r IN 1..n ==> &1 <= H r /\ 1 <= dd r /\ dd r <= D /\ Lv r <= Lm) /\
     nproduct(1..n) dd <= c /\ sum(1..n) (\r. &(Lv r) * log(H r)) <= T0 /\
     (!N z. N <= X + 1 /\ &0 <= z /\ z <= &X
            ==> sharp_errb n h L Lv Lm P B S0 T0 d0 N z <= exp(--(E + &2))) /\
     &16 * &X * &S0 = E /\ &X = &h * &Q pow J /\ Nl <= X /\
     (aQ + 1) * (n + 2) = J /\
     &S0 = &gN * &Q pow (aQ + 8 * c + 3) /\
     sg = (&n + &1) * &gN * &Q pow (aQ + 1) /\
     &SJ <= &2 * &Y /\ &SJ * &2 pow J = &S0 /\ Y + 1 <= S0 /\
     NX = 4 * Q EXP (8 * c) * X + 1 /\ rhoX = &4 * &Q pow (8 * c) * &X /\
     prime pr /\ &pr <= &2 pow 70 * &Q pow (aQ + 1) /\
     &2 * &2 pow 70 * &Q pow (aQ + 1) <= &S0 /\
     &2 * &2 pow 70 * &Q pow (aQ + 1) <= &X /\
     &2 pow J * &78 <= &Q pow J /\
     &2 pow J * &52 * sg * &Q pow (8 * c) <= &S0 /\
     &2 pow (J + 70 * n + 6) * &c <= &Q pow (2 * aQ + 2) /\
     &2 pow (J + 71 * n + 78) * &c pow 2 <= &Q pow (aQ + 8 * c + 3) /\
     &2 pow J * &3 <= &X * &S0 /\
     (!i. i < n ==> m i <= L) /\ 1 <= l /\ l <= 4 * h
     ==> (&2 * sharp_ubd n h L Lv Lm P B S0 T0 NX rhoX *
          (&4 * &X / rhoX) pow (X * (Y + 1)) +
          exp(--E) * &2 * &pr * &X * (&2 * &pr) pow Y * exp(&(S0 * Nl)) *
          (&X * &16 pow X) pow (Y + 1)) +
         sharp_errb n h L Lv Lm P B S0 T0 d0 (l + 1) (&l / &pr)
         < sharp_lb8 n h L Lv P dd H (\r. 1) Hb
             (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0)
             (\s. &1) m l pr (l + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 <= pr` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_GE_2 THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &pr /\ 1 <= pr /\ &2 <= &S0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= h`; `2 <= pr`; `2 <= S0`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &Q /\ &0 < &Q` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&2 <= &Q` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&78 * &h <= &X` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `&X = &h * &Q pow J`] THEN
    TRANS_TAC REAL_LE_TRANS `&h * &78` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    TRANS_TAC REAL_LE_TRANS `&2 pow J * &78` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &78 <= x * &78`) THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &X /\ 1 <= X /\ 4 * h <= X` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &X /\ &4 * &h <= &X` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&78 * &h <= &X`; `&1 <= &h`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&1 + &D) /\ log(&1 + &D) <= &D /\ &1 <= &c`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN MP_TAC(SPEC `D:num` REAL_POS) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_LE THEN REWRITE_TAC[REAL_POS];
      ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  ABBREV_TAC
   `EMmax = Ec + Ep + &(2 * h * (L + 2)) * log(&pr) +
            &L * (&18 * &(4 * h + pr * h)) +
            &((L + 2) * ((4 * h + 1) + h)) +
            &((n - 1) * L) * log(&4 * B + &2) + &((n - 1) * Lm) +
            &(4 * h) * T0 +
            &(4 * h) * (&2 * T0 + &n * &Lm * log(&1 + &pr))` THEN
  ABBREV_TAC
   `E8 = &(pr EXP n) * &c *
         (&n * log(&pr) + log(&c) + EMmax +
          &(4 * h) * (&n * &Lm * log(&1 + &D)))` THEN
  SUBGOAL_THEN
   `&n * log(&pr) + log(&c) + EMmax + &(4 * h) * (&n * &Lm * log(&1 + &D))
    <= &38 * &h * &S0 + &141 * &c * &pr * &h * sg`
  ASSUME_TAC THENL
   [EXPAND_TAC "EMmax" THEN
    MATCH_MP_TAC SHARP_EMMAX_ALG_BOUND THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= EMmax` ASSUME_TAC THENL
   [EXPAND_TAC "EMmax" THEN
    SUBGOAL_THEN `&0 <= log(&pr) /\ &0 <= log(&4 * B + &2) /\
                  &0 <= log(&1 + &pr)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN TRY REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E8 /\ &2 pow J * E8 <= &2 * &X * &S0 /\
                E8 <= &X * &S0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= log(&pr) /\ &0 <= log(&c)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= E8` ASSUME_TAC THENL
     [EXPAND_TAC "E8" THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 pow J * E8 <= &2 * &X * &S0` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS
       `&2 pow J * (&(pr EXP n) * &c *
                    (&38 * &h * &S0 + &141 * &c * &pr * &h * sg))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
                        ALL_TAC] THEN
        EXPAND_TAC "E8" THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC SHARP_E8_BOUND_ALG THEN
        MAP_EVERY EXISTS_TAC [`aQ:num`; `8 * c + 3`; `gN:num`; `&Q`] THEN
        ASM_REWRITE_TAC[ARITH_RULE `a + 8 * c + 3 = a + (8 * c + 3)`] THEN
        REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    SUBGOAL_THEN `&2 * E8 <= &2 pow J * E8` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN
      UNDISCH_TAC `(aQ + 1) * (n + 2) = J` THEN ARITH_TAC;
      UNDISCH_TAC `&2 pow J * E8 <= &2 * &X * &S0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--E8) <=
    sharp_lb8 n h L Lv P dd H (\r. 1) Hb
      (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0) (\s. &1)
      m l pr (l + 1)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `Lv:num->num`; `Lm:num`;
                  `P:real`; `B:real`; `dd:num->num`; `H:num->real`;
                  `Hb:real`; `m:num->num`; `l:num`; `pr:num`; `l + 1`;
                  `Ec:real`; `Ep:real`; `T0:real`; `D:num`; `c:num`]
                 SHARP_LB8_ALG_GE_EXP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `&2 <= B` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> b <= c ==> a <= c`) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    EXPAND_TAC "E8" THEN ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
                    ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) <= c /\ b <= d ==> a + b <= c + d`) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "EMmax" THEN MATCH_MP_TAC SHARP_EM_MONO THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `1 <= n` THEN ARITH_TAC;
        TRANS_TAC LE_TRANS `nsum(1..n-1) (\i:num. L)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC NSUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
          REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          MAP_EVERY UNDISCH_TAC [`i <= n - 1`; `1 <= n`] THEN ARITH_TAC;
          REWRITE_TAC[NSUM_CONST_NUMSEG] THEN
          SUBGOAL_THEN `((n - 1) + 1) - 1 = n - 1` SUBST1_TAC THENL
           [ARITH_TAC; REWRITE_TAC[LE_REFL]]];
        UNDISCH_TAC `&2 <= B` THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`sharp_ubd n h L Lv Lm P B S0 T0 NX rhoX`; `rhoX:real`; `X:num`;
    `Y:num`; `pr:num`; `&(S0 * Nl)`; `&Q pow c`;
    `Ec + Ep + &((L + 2) * (NX + h)) + &S0 * log(&4 * B + &2) +
     &((n - 1) * Lm) + rhoX * T0`;
    `E8:real`; `E:real`;
    `sharp_errb n h L Lv Lm P B S0 T0 d0 (l + 1) (&l / &pr)`;
    `sharp_lb8 n h L Lv P dd H (\r. 1) Hb
       (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0) (\s. &1)
       m l pr (l + 1)`]
   SHARP_LEMMA8_ABS) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    TRANS_TAC REAL_LTE_TRANS `&Q` THEN CONJ_TAC THENL
     [UNDISCH_TAC `&2 <= &Q` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; UNDISCH_TAC `1 <= c` THEN ARITH_TAC];
    REWRITE_TAC[sharp_ubd] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE] THEN
    TRY(MATCH_MP_TAC REAL_POW_LE THEN UNDISCH_TAC `&2 <= B` THEN
        REAL_ARITH_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SHARP_UBD_LE_EXP THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `&2 <= B` THEN REAL_ARITH_TAC;
    REWRITE_TAC[ASSUME `rhoX = &4 * &Q pow (8 * c) * &X`; REAL_POW_POW] THEN
    SUBGOAL_THEN `c * 8 = 8 * c` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&X = &0) /\ ~(&Q pow (8 * c) = &0)` MP_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `&1 <= &X` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_NZ THEN UNDISCH_TAC `&2 <= &Q` THEN
        REAL_ARITH_TAC];
      CONV_TAC REAL_FIELD];
    TRANS_TAC REAL_LE_TRANS `exp(--(E + &2))` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `sharp_errb` (concl th))) THEN
      SUBGOAL_THEN `&0 < &pr` ASSUME_TAC THENL
       [UNDISCH_TAC `&1 <= &pr` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`l <= 4 * h`; `4 * h <= X`] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
        SIMP_TAC[REAL_LE_LDIV_EQ; ASSUME `&0 < &pr`] THEN
        TRANS_TAC REAL_LE_TRANS `&X` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN
          MAP_EVERY UNDISCH_TAC [`l <= 4 * h`; `4 * h <= X`] THEN ARITH_TAC;
          ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2; REAL_LE_RADD] THEN
      SUBGOAL_THEN `&0 <= &X * &S0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      UNDISCH_TAC `E8 <= &X * &S0` THEN UNDISCH_TAC `&16 * &X * &S0 = E` THEN
      REAL_ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(SPECL [`n:num`; `h:num`; `J:num`; `S0:num`; `sg:real`; `X:num`;
                  `Y:num`; `SJ:num`; `Ec:real`; `Ep:real`;
                  `log(&4 * B + &2)`; `T0:real`; `L:num`; `Lm:num`;
                  `NX:num`; `rhoX:real`; `E8:real`; `&Q pow (8 * c)`;
                  `&c * log(&Q)`] SHARP_LEMMA8_LOGINEQ_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `&0 <= log(&4 * B + &2)` MP_TAC THENL
         [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `4 * h <= X` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
                    GSYM REAL_OF_NUM_POW];
        ASM_REWRITE_TAC[] THEN
        TRANS_TAC REAL_LE_TRANS `&h * (&2 pow J * &78)` THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
        TRANS_TAC REAL_LE_TRANS `&1 * &128` THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_POW] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`S0:num`; `X:num`; `Y:num`; `pr:num`; `Nl:num`;
                  `E8:real`] SHARP_LEMMA8_EPSINEQ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MAP_EVERY UNDISCH_TAC
       [`&pr <= &2 pow 70 * &Q pow (aQ + 1)`;
        `&2 * &2 pow 70 * &Q pow (aQ + 1) <= &S0`;
        `&2 * &2 pow 70 * &Q pow (aQ + 1) <= &X`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[ASSUME `&16 * &X * &S0 = E`]]]);;

(* ------------------------------------------------------------------------- *)
(* The design-facts lemma common to the two endings: for the data, an        *)
(* analytic size Bq >= 2, degree data dd1 with dd1 r <= D1, a radius         *)
(* exponent c at least D, D1 and nproduct dd1, the naturals a, J, e, Q, g0N, *)
(* gN >= log A + D + 5, h >= log(4 Bq + 2), L, Ln, Lm, S0, X of the design,  *)
(* a prime pr in (Ln, 2^70 Ln], |Lambda| <= exp(-17 X S0) and any P between  *)
(* 0 and the Siegel bound at the integer instance with Bq, every numeric     *)
(* hypothesis of SHARP_CORE_PARAMETRIC holds in the integer form (the bound  *)
(* functions at the integer instance with dd1 and Bq; T0, d0, Nl, eps, R, S, *)
(* rho, NR, V, Y, rhoX, NX, K8 as above). The ending for integer             *)
(* coefficients uses it with Bq = B, dd1 = dd, D1 = D, c = D^n; the ending   *)
(* for algebraic coefficients with Bq = Bp, dd1, D1 = 2 D^(n+1),             *)
(* c = 2 D^(2n) and the domination of Part B of Baker/sharpc_num.ml.         *)
(* ------------------------------------------------------------------------- *)

let SHARP_CORE_DESIGN = prove
 (`!n D (lg:num->complex) (a:num->num->real) (dd:num->num) (bb:num->complex)
    (dd1:num->num) D1 (H:num->real) (Lv:num->num) A Bq Hb P g0 c aQ J e
    g0N gN h Q pr L Ln Lm S0 X.
     1 <= n /\ &1 <= g0 /\ exp(&1) <= A /\ &2 <= Bq /\
     (\r. if r = n then A else exp g0) = H /\ sharp_algdata n lg a dd H /\
     (!r. r IN 1..n ==> dd r <= D /\ --pi < Im(lg r) /\ Im(lg r) <= pi) /\
     (!r. r IN 1..n ==> 1 <= dd1 r /\ dd1 r <= D1) /\ &1 <= norm(bb n) /\
     1 <= c /\ D <= c /\ D1 <= c /\ nproduct(1..n) dd1 <= c /\
     (8 * c + 3) * n = aQ /\ (aQ + 1) * (n + 2) = J /\
     J + 72 * n + 256 + 8 * c = e /\ 2 EXP e * g0N = Q /\
     g0 <= &g0N /\ 1 <= g0N /\ log A + &D + &5 <= &gN /\
     log(&4 * Bq + &2) <= &h /\ 1 <= h /\
     gN * Q EXP aQ = L /\ Q EXP (aQ + 1) = Ln /\ gN * Q EXP (aQ + 1) = Lm /\
     gN * Q EXP (aQ + 8 * c + 3) = S0 /\ h * Q EXP J = X /\
     sharp_lv n L Ln = Lv /\ prime pr /\ Ln < pr /\ pr <= 2 EXP 70 * Ln /\
     norm(vsum(1..n) (\r. bb r * lg r)) <= exp(--(&17 * &X * &S0)) /\
     &0 <= P /\
     P <= sharp_psize n h L Lv S0 H Hb
            (\s. (&4 * Bq + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0)
     ==> ?T0 d0 Nl eps (R:num->num) (S:num->num) (rho:num->real)
          (NR:num->num) (V:num->real) Y rhoX NX K8.
           L <= Lm /\ Ln <= Lm /\
           (!m. (!i. i < n ==> m i <= L) ==> nsum(1..n-1) m <= S0) /\
           (!k. k <= c
                ==> 2 * k * h * (S0 + 1) EXP n <=
                    CARD(sharp_index h L Lv n)) /\
           &0 <= d0 /\
           (!mu. mu IN cartesian_product (1..n) (\r. 0..Lv r)
                 ==> norm(sharp_omega n bb lg mu) <= T0 /\
                     norm(sharp_omega n bb lg mu -
                          vsum(1..n) (\r. Cx(&(mu r)) * lg r)) <= d0) /\
           &1 + &2 * sum(1..n-1) (\i. norm(lg i)) <= &Nl /\
           (!l. 1 <= l /\ l <= h
                ==> sharp_errb n h L Lv Lm P Bq S0 T0 d0 (l + 1) (&l)
                    <= eps) /\
           R 0 = h /\ S 0 = S0 /\
           (!K. K < J
                ==> R K <= R(K + 1) /\ 2 * S(K + 1) <= S K /\
                    &4 * &(R(K + 1)) <= rho K /\ rho K + &1 <= &(NR K) /\
                    (!l. R K < l /\ l <= R(K + 1)
                         ==> sharp_errb n h L Lv Lm P Bq S0 T0 d0 (l + 1) (&l)
                             <= eps /\
                             V K +
                             sharp_errb n h L Lv Lm P Bq S0 T0 d0 (l + 1) (&l)
                             < sharp_liou5 n h L Lv P S0 dd1 H (\r. 1) Hb
                                 (\s. (&4 * Bq + &2) pow s *
                                      &2 pow ((n - 1) * Lm))
                                 (\s. 0) (\s. &1) l) /\
                    &2 * sharp_ubd n h L Lv Lm P Bq S0 T0 (NR K) (rho K) *
                    (&4 * &(R(K + 1)) / rho K) pow (R K * (S(K + 1) + 1)) +
                    eps * &2 * &(R K) * &2 pow (S(K + 1)) * exp(&(S0 * Nl)) *
                    (&(R(K + 1)) * &16 pow (R(K + 1))) pow (S(K + 1) + 1)
                    <= V K) /\
           1 <= X /\ X <= R J /\ n * L + Y <= S J /\ &4 * &X <= rhoX /\
           rhoX + &1 <= &NX /\ K8 <= pr * X /\
           (!m l. (!i. i < n ==> m i <= L) /\ 1 <= l /\ l <= K8 /\
                  ~(pr divides l)
                  ==> (&2 * sharp_ubd n h L Lv Lm P Bq S0 T0 NX rhoX *
                       (&4 * &X / rhoX) pow (X * (Y + 1)) +
                       eps * &2 * &pr * &X * (&2 * &pr) pow Y *
                       exp(&(S0 * Nl)) * (&X * &16 pow X) pow (Y + 1)) +
                      sharp_errb n h L Lv Lm P Bq S0 T0 d0 (l + 1) (&l / &pr)
                      < sharp_lb8 n h L Lv P dd1 H (\r. 1) Hb
                          (\s. (&4 * Bq + &2) pow s * &2 pow ((n - 1) * Lm))
                          (\s. 0) (\s. &1) m l pr (l + 1)) /\
           h * (L + 2) <=
           (L + 1) * CARD {l | 1 <= l /\ l <= K8 /\ ~(pr divides l)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* ---- basic facts on Q and gN ---- *)
  MP_TAC(SPECL [`e:num`; `g0N:num`; `Q:num`] SHARP_Q_BASIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `J + 72 * n + 256 + 8 * c = e` THEN
    ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `&1 <= log A /\ &1 <= &gN /\ 1 <= gN /\ &0 < A /\ &1 <= A`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= log A` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= exp(&1)` ASSUME_TAC THENL
     [MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &gN` ASSUME_TAC THENL
     [MP_TAC(SPEC `D:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= Q /\ n + 1 <= Q` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 pow (n + 1) <= &Q pow 1` MP_TAC THENL
     [MATCH_MP_TAC SHARP_QPOW_GE THEN
      MAP_EVERY EXISTS_TAC [`e:num`; `g0N:num`] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `J + 72 * n + 256 + 8 * c = e` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_1; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    MP_TAC(SPEC `n + 1` LT_POW2_REFL) THEN
    UNDISCH_TAC `&2 <= &Q` THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* ---- the design quantities ---- *)
  ABBREV_TAC `sg = (&n + &1) * &gN * &Q pow (aQ + 1)` THEN
  ABBREV_TAC `E = &16 * &X * &S0` THEN
  MP_TAC(SPECL [`n:num`; `aQ:num`; `8 * c + 3`; `gN:num`; `Q:num`; `L:num`;
                `Lm:num`; `Ln:num`; `S0:num`; `sg:real`]
               SHARP_SG_FACTS_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  MAP_EVERY (fun t -> FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
                        concl th = t)))
   [`&L = &gN * &Q pow aQ`; `&Lm = &gN * &Q pow (aQ + 1)`;
    `&Ln = &Q pow (aQ + 1)`; `&S0 = &gN * &Q pow (aQ + 8 * c + 3)`] THEN
  MP_TAC(SPECL [`n:num`; `c:num`; `aQ:num`; `J:num`; `e:num`; `g0N:num`;
                `gN:num`; `h:num`; `Q:num`; `S0:num`; `sg:real`; `X:num`]
         SHARP_DESIGN_CFACTS_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num`; `aQ:num`; `J:num`; `e:num`; `g0N:num`;
                `gN:num`; `h:num`; `Q:num`; `S0:num`; `sg:real`; `X:num`]
         SHARP_DESIGN_QFACTS_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW];
    STRIP_TAC] THEN
  SUBGOAL_THEN `?S:num->num. !K. S K = gN * g0N EXP (aQ + 8 * c + 3) *
                                       2 EXP (e * (aQ + 8 * c + 3) - K)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\K. gN * g0N EXP (aQ + 8 * c + 3) *
                    2 EXP (e * (aQ + 8 * c + 3) - K)` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Y = (S:num->num) J - n * L` THEN
  MP_TAC(SPECL [`n:num`; `c:num`; `aQ:num`; `J:num`; `e:num`; `g0N:num`;
                `gN:num`; `Q:num`; `L:num`; `S0:num`; `S:num->num`; `Y:num`]
         SHARP_S_FACTS_ALG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* ---- the data quantities ---- *)
  ABBREV_TAC `Lam = vsum(1..n) (\r. (bb:num->complex) r * lg r)` THEN
  ABBREV_TAC `d0 = &Ln * norm(Lam:complex)` THEN
  ABBREV_TAC
   `T0 = &L * &(n - 1) * (g0 + &D + &4) + &Ln * (log A + &D + &5)` THEN
  ABBREV_TAC `Ec = &h + &L + &n * &Lm` THEN
  ABBREV_TAC `Ep = Ec + &36 * &h * &S0 + &((L + 2) * (2 * h + 1)) +
                   &S0 * log(&4 * Bq + &2) + &((n - 1) * Lm) + &h * T0` THEN
  ABBREV_TAC `Nl = 2 * (n - 1) * (g0N + D + 4) + 1` THEN
  SUBGOAL_THEN `!r. r IN 1..n ==> &1 <= (H:num->real) r` ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM REAL_EXP_0) THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `L <= Lm /\ Ln <= Lm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN EXPAND_TAC "Lm" THEN EXPAND_TAC "Ln" THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP] THEN
      UNDISCH_TAC `2 <= Q` THEN ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN UNDISCH_TAC `1 <= gN` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN 1..n ==> (Lv:num->num) r <= Lm` ASSUME_TAC THENL
   [EXPAND_TAC "Lv" THEN REWRITE_TAC[sharp_lv] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r IN 1..n ==> &1 <= (H:num->real) r /\ 1 <= (dd1:num->num) r /\
                      dd1 r <= D1 /\ (Lv:num->num) r <= Lm`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\r. &((Lv:num->num) r) * log(&2 * (H:num->real) r)) <= T0 /\
    sum(1..n) (\r. &((Lv:num->num) r) * log((H:num->real) r)) <= T0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `A:real`; `g0:real`; `L:num`; `Ln:num`; `D:num`]
      SHARP_ALG_SUM_LV_LOG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `sharp_lv n L Ln = Lv`;
                ASSUME
     `&L * &(n - 1) * (g0 + &D + &4) + &Ln * (log A + &D + &5) = T0`] THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= T0 /\ T0 <= sg` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `g0 + &D + &4`; `g0N + D + 4`; `log A + &D + &4`;
                  `gN:num`; `Q:num`; `aQ:num`; `L:num`; `Ln:num`; `sg:real`]
                 SHARP_T0_LE_SG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&(g0N + D + 4) <= &Q` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN
        MAP_EVERY UNDISCH_TAC [`g0N + c + 4 <= Q`; `D <= c`] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      MP_TAC(SPEC `D:num` REAL_POS) THEN
      MAP_EVERY UNDISCH_TAC [`&1 <= g0`; `g0 <= &g0N`; `&1 <= log A`;
                             `log A + &D + &5 <= &gN`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `(log A + &D + &4) + &1 = log A + &D + &5`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD(sharp_index h L Lv n)) <= exp Ec` ASSUME_TAC THENL
   [EXPAND_TAC "Ec" THEN MATCH_MP_TAC CARD_SHARP_INDEX_LE_EXP THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `P <= exp Ep` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sharp_psize n h L Lv S0 H Hb
        (\s. (&4 * Bq + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXPAND_TAC "Ep" THEN MATCH_MP_TAC SHARP_PSIZE_ALG_LE_EXP THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&4 * Bq + &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `h:num`; `S0:num`; `sg:real`; `Ec:real`; `Ep:real`;
                `log(&4 * Bq + &2)`; `T0:real`; `L:num`; `Lm:num`]
               SHARP_EP_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&38 * sg <= &S0`; `&1 <= sg`] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= Ec /\ &0 <= Ep` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= Ec` ASSUME_TAC THENL
     [EXPAND_TAC "Ec" THEN
      REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Ep" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &h /\ &1 <= &X /\ 1 <= X /\ &78 * &h <= &X`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &h` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= &X` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&78 * &h <= &X`; `&1 <= &h`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE];
    ALL_TAC] THEN
  (* ---- the smallness of Lambda ---- *)
  SUBGOAL_THEN `norm(Lam:complex) <= &1 /\ &0 <= d0 /\ d0 <= &1 /\
                &X * d0 <= exp(&X + &Ln - &17 * &X * &S0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(Lam:complex) <= exp(--(&17 * &X * &S0))` ASSUME_TAC
    THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp(--(&17 * &X * &S0)) <= &1 /\ &0 <= &X * &S0 /\
                  &Ln <= &17 * &X * &S0` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
        ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &17`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
        SUBGOAL_THEN `&1 * &S0 <= &X * &S0` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
          FIRST_ASSUM ACCEPT_TAC;
          MAP_EVERY UNDISCH_TAC [`&Ln <= sg`; `sg <= &S0`; `&2 <= &S0`] THEN
          REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(Lam:complex) <= &1` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`norm(Lam:complex) <= exp(--(&17 * &X * &S0))`;
        `exp(--(&17 * &X * &S0)) <= &1`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "d0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; NORM_POS_LE];
      TRANS_TAC REAL_LE_TRANS `&Ln * exp(--(&17 * &X * &S0))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `exp(&Ln) * exp(--(&17 * &X * &S0))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        MP_TAC(SPEC `&Ln` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
        ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        UNDISCH_TAC `&Ln <= &17 * &X * &S0` THEN REAL_ARITH_TAC];
      TRANS_TAC REAL_LE_TRANS
       `exp(&X) * exp(&Ln) * exp(--(&17 * &X * &S0))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
        REPEAT CONJ_TAC THENL
         [MP_TAC(SPEC `&X` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; NORM_POS_LE];
          MATCH_MP_TAC REAL_LE_MUL2 THEN
          REWRITE_TAC[REAL_POS; NORM_POS_LE] THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(SPEC `&Ln` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
        REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* ---- the error bound ---- *)
  MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `Lm:num`; `Ln:num`; `S0:num`;
                `X:num`; `sg:real`; `Ec:real`; `Ep:real`;
                `log(&4 * Bq + &2)`; `T0:real`] SHARP_ERR_INEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!N z. N <= X + 1 /\ &0 <= z /\ z <= &X
          ==> sharp_errb n h L Lv Lm P Bq S0 T0 d0 N z <= exp(--(E + &2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `Lv:num->num`; `Lm:num`;
                  `P:real`; `Bq:real`; `S0:num`; `T0:real`; `d0:real`;
                  `N:num`; `z:real`; `Ec:real`; `Ep:real`; `X + 1`; `&X`]
                 SHARP_ERRB_LE_EXP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `&2 <= Bq` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(y:real) <= z ==> x <= y ==> x <= z`) THEN
    TRANS_TAC REAL_LE_TRANS
     `exp(Ec + Ep + &((L + 2) * ((X + 1) + h)) + &S0 * log(&4 * Bq + &2) +
          &((n - 1) * Lm) + &X * (T0 + &1)) *
      exp(&X + &Ln - &17 * &X * &S0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_POS_LE];
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        SUBGOAL_THEN `&X * d0 <= &X * &1` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
          FIRST_ASSUM ACCEPT_TAC;
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      MAP_EVERY UNDISCH_TAC
       [`&16 * &X * &S0 = E`;
        `Ec + Ep + &((L + 2) * ((X + 1) + h)) + &S0 * log(&4 * Bq + &2) +
         &((n - 1) * Lm) + &X * (T0 + &1) + &X + &Ln + &2 <= &X * &S0`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Nl <= X` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 * (n - 1) * (g0N + c + 4) + 1` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Nl" THEN REWRITE_TAC[LE_ADD_RCANCEL; LE_MULT_LCANCEL] THEN
      UNDISCH_TAC `D <= c` THEN ARITH_TAC;
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!r. r IN 1..n-1 ==> norm((lg:num->complex) r) <= g0 + &D + &4) /\
    norm((lg:num->complex) n) <= log A + &D + &4`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `lg:num->complex`; `a:num->num->real`;
                  `dd:num->num`; `D:num`; `A:real`; `g0:real`]
                 SHARP_ALG_LG_BOUNDS) THEN
    REWRITE_TAC[ASSUME `(\r:num. if r = n then (A:real) else exp g0) = H`] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* ---- R, rho, NR, V ---- *)
  SUBGOAL_THEN `?R:num->num. !K. R K = h * Q EXP K` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\K. h * Q EXP K` THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?rho:num->real. !K. rho K = &4 * &Q pow (8 * c) * &(R(K + 1))`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\K. &4 * &Q pow (8 * c) * &((R:num->num)(K + 1))` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?NR:num->num. !K. NR K = 4 * Q EXP (8 * c) * R(K + 1) + 1`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\K. 4 * Q EXP (8 * c) * (R:num->num)(K + 1) + 1` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?V:num->real.
      !K. V K = exp(--(&c * ((Ec + Ep +
                              &(h * S0) * (&19 + log((&(R(K + 1)) + &h) / &h)) +
                              &((L + 2) * ((R(K + 1) + 1) + h)) +
                              &S0 * log(&4 * Bq + &2) + &((n - 1) * Lm) +
                              &(R(K + 1)) *
                              (&3 * T0 + &n * &Lm * log(&1 + &D1))) +
                             log(&c)) + &1))`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `\K. exp(--(&c * ((Ec + Ep +
                        &(h * S0) * (&19 + log((&((R:num->num)(K + 1)) + &h) /
                                               &h)) +
                        &((L + 2) * ((R(K + 1) + 1) + h)) +
                        &S0 * log(&4 * Bq + &2) + &((n - 1) * Lm) +
                        &(R(K + 1)) * (&3 * T0 + &n * &Lm * log(&1 + &D1))) +
                       log(&c)) + &1))` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* ---- the design facts ---- *)
  MAP_EVERY EXISTS_TAC
   [`T0:real`; `d0:real`; `Nl:num`; `exp(--E)`; `R:num->num`; `S:num->num`;
    `rho:num->real`; `NR:num->num`; `V:num->real`; `Y:num`;
    `&4 * &Q pow (8 * c) * &X`; `4 * Q EXP (8 * c) * X + 1`; `4 * h`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `m:num->num` THEN DISCH_TAC THEN
    TRANS_TAC LE_TRANS `(n - 1) * L` THEN CONJ_TAC THENL
     [TRANS_TAC LE_TRANS `nsum(1..n-1) (\i:num. L)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC NSUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[NSUM_CONST_NUMSEG; ARITH_RULE `(n - 1 + 1) - 1 = n - 1`;
                    LE_REFL]];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      MAP_EVERY UNDISCH_TAC [`&((n - 1) * L) <= sg`; `sg <= &S0`] THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    EXPAND_TAC "Lv" THEN MATCH_MP_TAC SHARP_INDEX_CARD_GE_ALG THEN
    MAP_EVERY EXISTS_TAC [`aQ:num`; `8 * c + 3`; `gN:num`; `Q:num`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [TRANS_TAC LE_TRANS `2 EXP (n + 1) * c` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[LE_MULT_LCANCEL];
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL;
                    GSYM REAL_OF_NUM_POW] THEN
        FIRST_ASSUM ACCEPT_TAC];
      UNDISCH_TAC `(8 * c + 3) * n = aQ` THEN ARITH_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `bb:num->complex`; `lg:num->complex`; `L:num`;
                  `Ln:num`; `mu:num->num`; `g0 + &D + &4`;
                  `log A + &D + &4`] SHARP_OMEGA_BOUNDS) THEN
    REWRITE_TAC[ASSUME `sharp_lv n L Ln = Lv`;
                ASSUME `vsum(1..n) (\r. (bb:num->complex) r * lg r) = Lam`;
                REAL_ARITH `(x + &D + &4) + &1 = x + &D + &5`;
                ASSUME `&L * &(n - 1) * (g0 + &D + &4) +
                        &Ln * (log A + &D + &5) = T0`;
                ASSUME `&Ln * norm(Lam:complex) = d0`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    EXPAND_TAC "Nl" THEN MATCH_MP_TAC SHARP_ALG_NL_BOUND THEN
    EXISTS_TAC `g0:real` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    TRANS_TAC REAL_LE_TRANS `exp(--(E + &2))` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `sharp_errb` (concl th))) THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN `h <= X` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
        MAP_EVERY UNDISCH_TAC [`&78 * &h <= &X`; `&1 <= &h`] THEN
        REAL_ARITH_TAC;
        UNDISCH_TAC `l <= h` THEN ARITH_TAC];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC];
    REWRITE_TAC[ASSUME `!K. (R:num->num) K = h * Q EXP K`; EXP;
                MULT_CLAUSES];
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `c:num`; `aQ:num`; `J:num`; `e:num`; `g0N:num`;
                  `gN:num`; `Q:num`; `S0:num`; `sg:real`; `K:num`]
                 SHARP_DESIGN_KFACTS_ALG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPEC `K:num` (ASSUME
     `!K. K < J ==> 2 * (S:num->num)(K + 1) <= S K /\
                    &(S(K + 1)) * &2 pow (K + 1) = &S0 /\
                    S(K + 1) + 1 <= S0`)) THEN
    REWRITE_TAC[ASSUME `K < J`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SHARP_STEP_COND_ALG THEN
    MAP_EVERY EXISTS_TAC [`Ec:real`; `Ep:real`; `sg:real`; `c:num`; `D1:num`;
                          `Q:num`; `X:num`; `J:num`; `K:num`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(SPEC `K:num` th))) THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "X" THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW];
      REWRITE_TAC[ASSUME `!K. (R:num->num) K = h * Q EXP K`] THEN
      EXPAND_TAC "X" THEN REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP] THEN
      MAP_EVERY UNDISCH_TAC [`K < J`; `2 <= Q`] THEN ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ASSUME `!K. (R:num->num) K = h * Q EXP K`] THEN
    REWRITE_TAC[ASSUME `h * Q EXP J = X`; LE_REFL];
    REWRITE_TAC[ASSUME `n * L + Y = (S:num->num) J`; LE_REFL];
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&4 * x = &4 * &1 * x`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &4`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
                GSYM REAL_OF_NUM_POW; REAL_LE_REFL];
    SUBGOAL_THEN `2 <= pr /\ 2 * h <= X` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PRIME_GE_2 THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN
        MAP_EVERY UNDISCH_TAC [`&78 * &h <= &X`; `&1 <= &h`] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    TRANS_TAC LE_TRANS `2 * 2 * h` THEN CONJ_TAC THENL
     [ARITH_TAC; MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`m:num->num`; `l:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SHARP_LEMMA8_COND_ALG THEN
    MAP_EVERY EXISTS_TAC [`Ec:real`; `Ep:real`; `sg:real`; `c:num`; `D1:num`;
                          `Q:num`; `(S:num->num) J`; `J:num`; `aQ:num`;
                          `gN:num`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "X" THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW];
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[];
      REWRITE_TAC[];
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE;
                  ASSUME `Q EXP (aQ + 1) = Ln`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    SUBGOAL_THEN `2 * h <= CARD {l | 1 <= l /\ l <= 4 * h /\ ~(pr divides l)}`
    MP_TAC THENL
     [MATCH_MP_TAC SHARP_NONDIV_CARD THEN MATCH_MP_TAC PRIME_GE_2 THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN TRANS_TAC LE_TRANS `(L + 1) * 2 * h` THEN CONJ_TAC THENL
     [ARITH_TAC; REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The data lemma for integer coefficients: SHARP_CORE_PARAMETRIC at the     *)
(* integer instance (coefficient data SHARPC_COEFDATA_INTEGER of height B,   *)
(* the Delta representation SHARP_DELTAREP_INT) with the design facts of     *)
(* SHARP_CORE_DESIGN for Bq = B, dd1 = dd, D1 = D, c = D^n; the rational     *)
(* betas do not change the field (COMPLEX_SUBFIELD_GENERATED_UNION_RATIONAL).*)
(* ------------------------------------------------------------------------- *)

let SHARP_CORE_DATA_ALG = prove
 (`!n D (lg:num->complex) (a:num->num->real) (dd:num->num) (bb:num->real)
    A B g0 c aQ J e g0N gN h Q pr.
     1 <= n /\ 1 <= D /\ &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
     sharp_algdata n lg a dd (\r. if r = n then A else exp g0) /\
     (!r. r IN 1..n
          ==> dd r <= D /\ --pi < Im(lg r) /\ Im(lg r) <= pi /\
              integer(bb r) /\ abs(bb r) <= B) /\
     ~(bb n = &0) /\
     D EXP n = c /\ (8 * c + 3) * n = aQ /\ (aQ + 1) * (n + 2) = J /\
     J + 72 * n + 256 + 8 * c = e /\ 2 EXP e * g0N = Q /\
     g0 <= &g0N /\ 1 <= g0N /\ log A + &D + &5 <= &gN /\
     log(&4 * B + &2) <= &h /\ 1 <= h /\
     prime pr /\ Q EXP (aQ + 1) < pr /\ pr <= 2 EXP 70 * Q EXP (aQ + 1) /\
     norm(vsum(1..n) (\r. Cx(bb r) * lg r)) <=
     exp(--(&17 * &(h * Q EXP J) * &(gN * Q EXP (aQ + 8 * c + 3))))
     ==> ?jj g. (!r. jj r < pr) /\
                g IN ring_carrier(subfield_generated complex_ring
                                   (IMAGE (\r. cexp(lg r)) (1..n))) /\
                cexp(lg n) =
                cproduct(1..n-1) (\r. cexp(lg r) pow jj r) * g pow pr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* ---- the degree data: c = D^n ---- *)
  SUBGOAL_THEN `1 <= c /\ D <= c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!r. r IN 1..n
         ==> dd r <= D /\ --pi < Im((lg:num->complex) r) /\ Im(lg r) <= pi) /\
    (!r. r IN 1..n ==> integer((bb:num->real) r) /\ abs(bb r) <= B) /\
    (!r. r IN 1..n ==> 1 <= (dd:num->num) r /\ dd r <= D)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME
     `sharp_algdata n lg a dd (\r. if r = n then A else exp g0)`) THEN
    MP_TAC(ASSUME
     `!r. r IN 1..n
          ==> dd r <= D /\ --pi < Im((lg:num->complex) r) /\
              Im(lg r) <= pi /\ integer((bb:num->real) r) /\
              abs(bb r) <= B`) THEN
    REWRITE_TAC[sharp_algdata] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nproduct(1..n) (dd:num->num) <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    TRANS_TAC LE_TRANS `nproduct(1..n) (\r:num. D)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_LE_NUMSEG THEN ASM_SIMP_TAC[IN_NUMSEG];
      REWRITE_TAC[NPRODUCT_CONST_NUMSEG_1; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= norm(Cx((bb:num->real) n))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_CX] THEN MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && free_in `integer` (concl th))) THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ASSUME `1 <= n`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* ---- the design facts (SHARP_CORE_DESIGN, Bq = B, dd1 = dd) ---- *)
  ABBREV_TAC `L = gN * Q EXP aQ` THEN
  ABBREV_TAC `Ln = Q EXP (aQ + 1)` THEN
  ABBREV_TAC `Lm = gN * Q EXP (aQ + 1)` THEN
  ABBREV_TAC `S0 = gN * Q EXP (aQ + 8 * c + 3)` THEN
  ABBREV_TAC `X = h * Q EXP J` THEN
  ABBREV_TAC `Lv = sharp_lv n L Ln` THEN
  ABBREV_TAC `H = \r:num. if r = n then (A:real) else exp g0` THEN
  MP_TAC(SPECL [`n:num`; `D:num`; `lg:num->complex`; `a:num->num->real`;
                `dd:num->num`; `\r. Cx((bb:num->real) r)`; `dd:num->num`;
                `D:num`; `H:num->real`; `Lv:num->num`; `A:real`; `B:real`;
                `B:real`;
                `sharp_psize n h L Lv S0 H B
                   (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0)`;
                `g0:real`; `c:num`; `aQ:num`; `J:num`; `e:num`; `g0N:num`;
                `gN:num`; `h:num`; `Q:num`; `pr:num`; `L:num`; `Ln:num`;
                `Lm:num`; `S0:num`; `X:num`] SHARP_CORE_DESIGN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SHARP_PSIZE_ALG_POS; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC] THEN
  (* ---- the parametric core at the integer instance ---- *)
  MP_TAC(SPECL [`n:num`; `lg:num->complex`; `a:num->num->real`;
                `dd:num->num`; `\r. Cx((bb:num->real) r)`;
                `\r j. if j = 0 then --((bb:num->real) r)
                       else if j = 1 then &1 else &0`;
                `\r:num. 1`; `H:num->real`; `B:real`;
                `\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)`;
                `\s:num. 0`; `\s:num. &1`; `\m:num->num. 1`; `B:real`;
                `h:num`; `L:num`; `L:num`; `Ln:num`; `Lm:num`; `S0:num`;
                `T0:real`; `d0:real`; `Nl:num`; `eps:real`; `J:num`;
                `R:num->num`; `S:num->num`; `rho:num->real`; `NR:num->num`;
                `V:num->real`; `X:num`; `Y:num`; `rhoX:real`; `NX:num`;
                `pr:num`; `K8:num`] SHARP_CORE_PARAMETRIC) THEN
  REWRITE_TAC[ASSUME `sharp_lv n L Ln = Lv`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `&2 <= B` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SHARPC_COEFDATA_INTEGER THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      UNDISCH_TAC `&2 <= B` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SHARP_DELTAREP_INT THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `&2 <= B` THEN REAL_ARITH_TAC;
      REWRITE_TAC[COMPLEX_NORM_CX] THEN
      MP_TAC(ASSUME
       `!r. r IN 1..n ==> integer((bb:num->real) r) /\ abs(bb r) <= B`) THEN
      MESON_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NPRODUCT_ONE; MULT_CLAUSES] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* ---- the field: the betas Cx(bb r) are rational ---- *)
  SUBGOAL_THEN
   `subfield_generated complex_ring
      (IMAGE (\r. cexp((lg:num->complex) r)) (1..n) UNION
       IMAGE (\r. Cx((bb:num->real) r)) (1..n)) =
    subfield_generated complex_ring (IMAGE (\r. cexp(lg r)) (1..n))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC COMPLEX_SUBFIELD_GENERATED_UNION_RATIONAL THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    EXISTS_TAC `(bb:num->real) r` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RATIONAL_INTEGER THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
      is_forall(concl th) && free_in `integer` (concl th))) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The algebraic sharp core: with c = D^n, a = (8 c + 3) n,                  *)
(* J = (a + 1)(n + 2), e = J + 72 n + 256 + 8 c and M = J + a + 8 c + 3,     *)
(*   C = 2^((e+1) M + 9) (D + 6), K = M, cB = 2^(70 + (e+1)(a+1)),           *)
(* since 17 X S0 = 17 h gN Q^M <= 2^((e+1) M + 9) g0^M log(A e^(D+5)) log B  *)
(* (SHARP_FINAL_U), log A + D + 5 <= (D + 6) log A, and                      *)
(* pr <= 2^70 Q^(a+1) <= cB g0^M, pr > Q >= 4 c^2 >= 4 D^2.                  *)
(* ------------------------------------------------------------------------- *)

let SHARP_CORE_ALGEBRAIC = prove
 (`!n D. 1 <= n /\ 1 <= D
         ==> ?C K cB. &0 <= C /\ &1 <= cB /\
                      sharp_core_property_alg n D C K cB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = D EXP n` THEN
  ABBREV_TAC `aQ = (8 * c + 3) * n` THEN
  ABBREV_TAC `J = (aQ + 1) * (n + 2)` THEN
  ABBREV_TAC `e = J + 72 * n + 256 + 8 * c` THEN
  ABBREV_TAC `M = J + aQ + 8 * c + 3` THEN
  MAP_EVERY EXISTS_TAC [`&2 pow ((e + 1) * M + 9) * (&D + &6)`; `M:num`;
                        `&2 pow (70 + (e + 1) * (aQ + 1))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `D:num` REAL_POS) THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sharp_core_property_alg] THEN
  MAP_EVERY X_GEN_TAC [`lg:num->complex`; `a:num->num->real`; `dd:num->num`;
                       `bb:num->real`; `A:real`; `B:real`; `g0:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `1 <= c /\ D <= c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log A /\ &0 < log(&4 * B + &2) /\ &0 < A`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `&1` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `g0:real` REAL_NUM_CEIL) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `g0N:num` STRIP_ASSUME_TAC)]
  THEN
  MP_TAC(SPEC `log A + &D + &5` REAL_NUM_CEIL) THEN ANTS_TAC THENL
   [MP_TAC(SPEC `D:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `gN:num` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPEC `log(&4 * B + &2)` REAL_NUM_CEIL) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `1 <= g0N /\ 1 <= h` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN CONJ_TAC THEN
    TRY ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Q = 2 EXP e * g0N` THEN
  SUBGOAL_THEN `1 <= Q EXP (aQ + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `Q EXP (aQ + 1)` PRIME_IN_INTERVAL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pr:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&Q <= &2 pow (e + 1) * g0` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_POW_ADD;
                REAL_POW_1; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&pr <= &2 pow (70 + (e + 1) * (aQ + 1)) * g0 pow M`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&2 pow 70 * &Q pow (aQ + 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(SPECL [`&2`; `70`; `(e + 1) * (aQ + 1)`] REAL_POW_ADD) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(&2 pow (e + 1) * g0) pow (aQ + 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_POW_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "M" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * D EXP 2 <= pr` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:num`; `n:num`; `J:num`] SHARP_CPOLY_BOUNDS) THEN
    ASM_REWRITE_TAC[GSYM REAL_POW_ADD] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&2 pow (2 + 2 * c) <= &Q` ASSUME_TAC THENL
     [MP_TAC(SPECL [`e:num`; `g0N:num`; `Q:num`; `1`; `2 + 2 * c`]
        SHARP_QPOW_GE) THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; REAL_POW_1] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      EXPAND_TAC "e" THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `Q <= Q EXP (aQ + 1)` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN REWRITE_TAC[LE_EXP] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `D EXP 2 <= c EXP 2` ASSUME_TAC THENL
     [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `4 * c EXP 2 <= Q` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL;
                  GSYM REAL_OF_NUM_POW] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`D EXP 2 <= c EXP 2`; `Q <= Q EXP (aQ + 1)`;
                             `Q EXP (aQ + 1) < pr`] THEN ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `pr:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&17 * &(h * Q EXP J) * &(gN * Q EXP (aQ + 8 * c + 3)) <=
    (&2 pow ((e + 1) * M + 9) * (&D + &6)) * g0 pow M * log A * log B`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&17 * &(h * Q EXP J) * &(gN * Q EXP (aQ + 8 * c + 3)) =
                  &17 * &h * &gN * &Q pow M` SUBST1_TAC THENL
     [EXPAND_TAC "M" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      REWRITE_TAC[ARITH_RULE `J + aQ + 8 * c + 3 = J + (aQ + 8 * c + 3)`;
                  REAL_POW_ADD] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`e:num`; `g0N:num`; `gN:num`; `h:num`; `Q:num`; `M:num`;
                  `g0:real`; `A * exp(&D + &5)`; `B:real`] SHARP_FINAL_U) THEN
    SUBGOAL_THEN `log(A * exp(&D + &5)) = log A + &D + &5` SUBST1_TAC THENL
     [ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `D:num` REAL_POS) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(y:real) <= z ==> x <= y ==> x <= z`) THEN
    SUBGOAL_THEN `&0 <= &2 pow ((e + 1) * M + 9) * g0 pow M /\
                  &0 <= log B` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `log A + &D + &5 <= (&D + &6) * log A` ASSUME_TAC THENL
     [MP_TAC(SPEC `D:num` REAL_POS) THEN
      SUBGOAL_THEN `&D * &1 <= &D * log A` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&2 pow ((e + 1) * M + 9) * g0 pow M) * (log A + &D + &5) * log B <=
      (&2 pow ((e + 1) * M + 9) * g0 pow M) * ((&D + &6) * log A) * log B`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`n:num`; `D:num`; `lg:num->complex`; `a:num->num->real`; `dd:num->num`;
    `bb:num->real`; `A:real`; `B:real`; `g0:real`; `c:num`; `aQ:num`;
    `J:num`; `e:num`; `g0N:num`; `gN:num`; `h:num`; `Q:num`; `pr:num`]
   SHARP_CORE_DATA_ALG) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `(x:real) < y ==> y <= z ==> x < z`)) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN ASM_REWRITE_TAC[]);;
