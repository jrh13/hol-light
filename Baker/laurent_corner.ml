(* ========================================================================= *)
(* Two logarithms, the Laurent bound: the corner constant of                 *)
(* Corollary 2.                                                              *)
(*                                                                           *)
(* Purpose: the constant of M. Laurent, Linear forms in two logarithms and   *)
(* interpolation determinants II, Acta Arith. 133 (2008), Corollary 2 at     *)
(* mu = 1 and m = 10: laurent_bound 5 h a1 a2 <= 32/36 h^2 a1 a2 for h >= 10 *)
(* and a1, a2 >= 6 (Laurent, with mu < 1: 25.2 instead of 32). The maximum   *)
(* of 36 laurent_bound / (h^2 a1 a2) over that domain is 31.288, at the      *)
(* corner (10, 6, 6).                                                        *)
(*                                                                           *)
(* Method (monotonicity plus one interval evaluation): every ingredient of   *)
(* laurent_bound (omega, theta, the constants C and C prime, the main term,  *)
(* the sqrt(omega theta) term and the logarithmic term) is bounded by a      *)
(* rational value at the corner, using only that omega, theta, 1/H, 1/a_i    *)
(* decrease, and the logarithm via log Y <= k log rho - 1 + Y / rho^k. The   *)
(* generic statement LAURENT_CORNER_GENERIC takes all corner values as       *)
(* parameters with simple rational side conditions; an instance only checks  *)
(* those numerically (REAL_RAT_REDUCE_CONV). Enclosures of log rho come from *)
(* TAYLOR_CEXP at a rational point y near log rho and the tangent bounds     *)
(* LOG_LE_EXP, LOG_GE_EXP.                                                   *)
(*                                                                           *)
(* Main results: LAURENT_BOUND_CORNER_5_10, the further instances            *)
(* LAURENT_BOUND_CORNER_53_20 (rho = 5.3, h >= 20, a_i >= 6.3, constant      *)
(* 25 / 6.3^2) and LAURENT_BOUND_CORNER_55_30 (rho = 5.5, h >= 30, a_i >=    *)
(* 6.5, constant 22.5 / 6.5^2), LAURENT_CORNER_GENERIC,                      *)
(* LAURENT_CORNER_TAYLOR_EXP, LAURENT_CORNER_LOG_BOUNDS,                     *)
(* LAURENT_CORNER_LOG_5 (1.609 <= log 5 <= 1.61); helper names               *)
(* LAURENT_CORNER_*.                                                         *)
(*                                                                           *)
(* Uses: Baker/laurent_defs.ml (laurent_bound, laurent_C, laurent_Cp),       *)
(* Baker/twolog_param.ml (LOG_LE_EXP, LOG_GE_EXP), TAYLOR_CEXP of            *)
(* Multivariate/transcendentals.ml.                                          *)
(* ========================================================================= *)

needs "Baker/twolog_param.ml";;
needs "Baker/laurent_defs.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary helpers.                                                       *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORNER_DIV_LE = prove
 (`!x x0 y y0. &0 <= x /\ x <= x0 /\ &0 < y0 /\ y0 <= y ==> x / y <= x0 / y0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]);;

let LAURENT_CORNER_TAYLOR_EXP = prove
 (`!n x. abs(exp x - sum(0..n) (\k. x pow k / &(FACT k))) <=
         exp(abs x) * abs x pow (n + 1) / &(FACT n)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`n:num`; `Cx x`] TAYLOR_CEXP) THEN
  REWRITE_TAC[RE_CX; GSYM CX_POW; GSYM CX_DIV; VSUM_CX; GSYM CX_EXP;
              GSYM CX_SUB; COMPLEX_NORM_CX]);;

let LAURENT_CORNER_LOG_BOUNDS = prove
 (`!x y e0 e1.
        &0 < x /\ &0 < e0 /\ e0 <= exp y /\ exp y <= e1
        ==> y + &1 - e1 / x <= log x /\ log x <= y - &1 + x / e0`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`x:real`; `y:real`] LOG_GE_EXP) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `b <= c ==> (y + &1 - b <= l ==> y + &1 - c <= l)`) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    MP_TAC(SPECL [`x:real`; `y:real`] LOG_LE_EXP) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `b <= c ==> (l <= y - &1 + b ==> l <= y - &1 + c)`) THEN
    MATCH_MP_TAC LAURENT_CORNER_DIV_LE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Rational enclosures of log 5 (and of log 5.3, log 5.5 for the optional    *)
(* instances), from TAYLOR_CEXP at y = 8/5, 5/3, 17/10 with n = 14.          *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORNER_EXP_8_5 = prove
 (`&4953 / &1000 <= exp(&8 / &5) /\ exp(&8 / &5) <= &4954 / &1000`,
  MP_TAC(SPECL [`14`; `&8 / &5`] LAURENT_CORNER_TAYLOR_EXP) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let LAURENT_CORNER_LOG_5 = prove
 (`&1609 / &1000 <= log(&5) /\ log(&5) <= &161 / &100`,
  MP_TAC(SPECL [`&5`; `&8 / &5`; `&4953 / &1000`; `&4954 / &1000`]
    LAURENT_CORNER_LOG_BOUNDS) THEN
  REWRITE_TAC[LAURENT_CORNER_EXP_8_5] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let LAURENT_CORNER_EXP_5_3 = prove
 (`&52944 / &10000 <= exp(&5 / &3) /\ exp(&5 / &3) <= &52945 / &10000`,
  MP_TAC(SPECL [`14`; `&5 / &3`] LAURENT_CORNER_TAYLOR_EXP) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let LAURENT_CORNER_LOG_53_10 = prove
 (`&1667 / &1000 <= log(&53 / &10) /\ log(&53 / &10) <= &417 / &250`,
  MP_TAC(SPECL [`&53 / &10`; `&5 / &3`; `&52944 / &10000`; `&52945 / &10000`]
    LAURENT_CORNER_LOG_BOUNDS) THEN
  REWRITE_TAC[LAURENT_CORNER_EXP_5_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let LAURENT_CORNER_EXP_17_10 = prove
 (`&54739 / &10000 <= exp(&17 / &10) /\ exp(&17 / &10) <= &5474 / &1000`,
  MP_TAC(SPECL [`14`; `&17 / &10`] LAURENT_CORNER_TAYLOR_EXP) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let LAURENT_CORNER_LOG_11_2 = prove
 (`&213 / &125 <= log(&11 / &2) /\ log(&11 / &2) <= &341 / &200`,
  MP_TAC(SPECL [`&11 / &2`; `&17 / &10`; `&54739 / &10000`; `&5474 / &1000`]
    LAURENT_CORNER_LOG_BOUNDS) THEN
  REWRITE_TAC[LAURENT_CORNER_EXP_17_10] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Omega and theta at the corner: both decrease in H, so for H >= H0 they    *)
(* are bounded by their values at H0 (rational upper bounds s0, om0, th0     *)
(* of the square root and of omega, theta at H0).                            *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORNER_OMEGA_THETA = prove
 (`!H H0 s0 om0 th0.
        &0 < H0 /\ H0 <= H /\ &0 <= s0 /\
        &1 + inv(&4 * H0 pow 2) <= s0 pow 2 /\
        &2 * (&1 + s0) <= om0 /\ s0 + inv(&2 * H0) <= th0
        ==> &4 <= laurent_omega H /\ laurent_omega H <= om0 /\
            &1 <= laurent_theta H /\ laurent_theta H <= th0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[laurent_omega; laurent_theta] THEN
  SUBGOAL_THEN `&0 < H` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * H0 pow 2 /\ &4 * H0 pow 2 <= &4 * H pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * H pow 2) /\
                inv(&4 * H pow 2) <= inv(&4 * H0 pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sqrt(&1 + inv(&4 * H pow 2)) /\
                sqrt(&1 + inv(&4 * H pow 2)) <= s0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_ONE] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * H) /\ inv(&2 * H) <= inv(&2 * H0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The radicand X of laurent_C decreases in H, a1, a2 and increases in       *)
(* lam, omega, theta: bound it by its rational corner value.                 *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORNER_X_LE = prove
 (`!lam H om th a1 a2 l1 a0 H0 om0 th0 r0 sh0.
        &0 <= lam /\ lam <= l1 /\ &0 < H0 /\ H0 <= H /\
        &0 <= om /\ om <= om0 /\ &0 <= th /\ th <= th0 /\
        &0 < a0 /\ a0 <= a1 /\ a0 <= a2 /\
        &0 <= r0 /\ om0 pow 5 * th0 <= r0 pow 4 /\
        &0 < sh0 /\ sh0 pow 2 <= H0
        ==> &0 <= om pow 2 / &9 +
                  &8 * lam * sqrt(sqrt(om pow 5 * th)) /
                  (&3 * sqrt(a1 * a2) * sqrt H) +
                  &4 / &3 * (inv a1 + inv a2) * lam * om / H /\
            om pow 2 / &9 +
            &8 * lam * sqrt(sqrt(om pow 5 * th)) /
            (&3 * sqrt(a1 * a2) * sqrt H) +
            &4 / &3 * (inv a1 + inv a2) * lam * om / H
            <= om0 pow 2 / &9 + &8 * l1 * r0 / (&3 * a0 * sh0) +
               &4 / &3 * (&2 / a0) * l1 * om0 / H0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(sqrt(om pow 5 * th)) /\
                sqrt(sqrt(om pow 5 * th)) <= r0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= om pow 5 * th /\ om pow 5 * th <= om0 pow 5 * th0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE];
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_LE2]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a0 <= sqrt(a1 * a2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sh0 <= sqrt H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &8 * lam * sqrt(sqrt(om pow 5 * th)) /
          (&3 * sqrt(a1 * a2) * sqrt H) /\
    &8 * lam * sqrt(sqrt(om pow 5 * th)) / (&3 * sqrt(a1 * a2) * sqrt H) <=
    &8 * l1 * r0 / (&3 * a0 * sh0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &3 * a0 * sh0 /\
                  &3 * a0 * sh0 <= &3 * sqrt(a1 * a2) * sqrt H`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= sqrt(sqrt(om pow 5 * th)) / (&3 * sqrt(a1 * a2) * sqrt H) /\
      sqrt(sqrt(om pow 5 * th)) / (&3 * sqrt(a1 * a2) * sqrt H) <=
      r0 / (&3 * a0 * sh0)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LAURENT_CORNER_DIV_LE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &4 / &3 * (inv a1 + inv a2) * lam * om / H /\
    &4 / &3 * (inv a1 + inv a2) * lam * om / H <=
    &4 / &3 * (&2 / a0) * l1 * om0 / H0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= inv a1 + inv a2 /\ inv a1 + inv a2 <= &2 / a0`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < inv a1 /\ inv a1 <= inv a0 /\
                    &0 < inv a2 /\ inv a2 <= inv a0`
      MP_TAC THENL
       [REPEAT CONJ_TAC THEN
        (MATCH_MP_TAC REAL_LT_INV ORELSE MATCH_MP_TAC REAL_LE_INV2) THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= om / H /\ om / H <= om0 / H0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LAURENT_CORNER_DIV_LE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `om pow 2 <= om0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `om:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The constants C and C prime: positivity and corner bounds.                *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORNER_C_ATOM = prove
 (`!lam om X l0 om0 x0 C0.
        &0 < l0 /\ l0 <= lam /\ &4 <= om /\ om <= om0 /\
        &0 <= X /\ X <= x0 pow 2 /\ &0 <= x0 /\
        inv(l0 pow 3) * (om0 / &6 + x0 / &2) pow 2 <= C0
        ==> &0 < inv(lam pow 3) * (om / &6 + sqrt X / &2) pow 2 /\
            inv(lam pow 3) * (om / &6 + sqrt X / &2) pow 2 <= C0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt X /\ sqrt X <= x0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam pow 3 /\ l0 pow 3 <= lam pow 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(lam pow 3) /\ inv(lam pow 3) <= inv(l0 pow 3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 / &3 <= om / &6 + sqrt X / &2 /\
                om / &6 + sqrt X / &2 <= om0 / &6 + x0 / &2`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(l0 pow 3) * (om0 / &6 + x0 / &2) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]]);;

let LAURENT_CORNER_C = prove
 (`!rho h a1 a2 l0 l1 h0 a0 H0 s0 om0 th0 r0 sh0 x0 C0.
        &0 < l0 /\ l0 <= log rho /\ log rho <= l1 /\
        &0 < h0 /\ h0 <= h /\ &0 < a0 /\ a0 <= a1 /\ a0 <= a2 /\
        &0 < H0 /\ H0 <= h0 / l1 + &1 /\
        &0 <= s0 /\ &1 + inv(&4 * H0 pow 2) <= s0 pow 2 /\
        &2 * (&1 + s0) <= om0 /\ s0 + inv(&2 * H0) <= th0 /\
        &0 <= r0 /\ om0 pow 5 * th0 <= r0 pow 4 /\
        &0 < sh0 /\ sh0 pow 2 <= H0 /\
        &0 <= x0 /\
        om0 pow 2 / &9 + &8 * l1 * r0 / (&3 * a0 * sh0) +
        &4 / &3 * (&2 / a0) * l1 * om0 / H0 <= x0 pow 2 /\
        inv(l0 pow 3) * (om0 / &6 + x0 / &2) pow 2 <= C0
        ==> &4 <= laurent_omega(h / log rho + &1) /\
            laurent_omega(h / log rho + &1) <= om0 /\
            &1 <= laurent_theta(h / log rho + &1) /\
            laurent_theta(h / log rho + &1) <= th0 /\
            &0 < laurent_C rho h a1 a2 /\ laurent_C rho h a1 a2 <= C0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `h0 / l1 <= h / log rho` ASSUME_TAC THENL
   [MATCH_MP_TAC LAURENT_CORNER_DIV_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `H0 <= h / log rho + &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`h / log rho + &1`; `H0:real`; `s0:real`; `om0:real`;
                `th0:real`] LAURENT_CORNER_OMEGA_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[laurent_C] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC LAURENT_CORNER_C_ATOM THEN
  MAP_EVERY EXISTS_TAC [`l0:real`; `om0:real`; `x0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!x y z:real. &0 <= x /\ x <= y /\ y <= z ==> &0 <= x /\ x <= z`) THEN
  EXISTS_TAC `om0 pow 2 / &9 + &8 * l1 * r0 / (&3 * a0 * sh0) +
              &4 / &3 * (&2 / a0) * l1 * om0 / H0` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LAURENT_CORNER_X_LE THEN EXISTS_TAC `th0:real` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let LAURENT_CORNER_CP_ATOM = prove
 (`!C om th lam l0 C0 om0 th0 p0.
        &0 < C /\ C <= C0 /\ &0 < om /\ om <= om0 /\ &0 < th /\ th <= th0 /\
        &0 < l0 /\ l0 <= lam /\
        &0 <= p0 /\ C0 * om0 * th0 / l0 pow 3 <= p0 pow 2
        ==> &0 < sqrt(C * om * th / lam pow 3) /\
            sqrt(C * om * th / lam pow 3) <= p0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < l0 pow 3 /\ l0 pow 3 <= lam pow 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < th / lam pow 3 /\ th / lam pow 3 <= th0 / l0 pow 3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LAURENT_CORNER_DIV_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < om * th / lam pow 3 /\
                om * th / lam pow 3 <= om0 * th0 / l0 pow 3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C * om * th / lam pow 3 /\
                C * om * th / lam pow 3 <= C0 * om0 * th0 / l0 pow 3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The three terms of laurent_bound, each bounded by a multiple of           *)
(* P = h^2 a1 a2: the main term C (h + lam)^2 a1 a2, the term                *)
(* sqrt(omega theta) (h + lam), and log(C prime (h + lam)^2 a1 a2) via       *)
(* the tangent bound log x <= k log rho - 1 + x / rho^k (LOG_LE_EXP).        *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORNER_SUM3 = prove
 (`!t1 t2 t3 c1 c2 c3 c P.
        t1 <= c1 * P /\ t2 <= c2 * P /\ t3 <= c3 * P /\
        c1 + c2 + c3 <= c /\ &0 <= P
        ==> t1 + t2 + t3 <= c * P`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(c1:real) + c2 + c3`; `c:real`; `P:real`] REAL_LE_RMUL) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let LAURENT_CORNER_TERM1 = prove
 (`!C C0 Y Z P.
        &0 < C /\ C <= C0 /\ &0 <= Y /\ Y <= Z * P
        ==> C * Y <= (C0 * Z) * P`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let LAURENT_CORNER_TERM2 = prove
 (`!S q0 lam h e D P.
        &0 <= S /\ S <= q0 /\ &0 <= h + lam /\ h + lam <= e * h /\
        &0 <= e /\ &0 < D /\ D * h <= P
        ==> S * (h + lam) <= (q0 * e / D) * P`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(q0:real) * e * h` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `q0 * e * h = (q0 * e / D) * (D * h)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < D` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let LAURENT_CORNER_TERM3 = prove
 (`!Cp p0 Y Z P rho l1 k D2.
        &1 < rho /\ log rho <= l1 /\ &0 < Cp /\ Cp <= p0 /\
        &0 < Y /\ Y <= Z * P /\ &0 < D2 /\ D2 <= P /\ &1 <= &k * l1
        ==> log(Cp * Y) <= ((&k * l1 - &1) / D2 + p0 * Z / rho pow k) * P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(Cp * Y) <= log(p0 * Y)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(p0 * Y) <= &k * log rho - &1 + (p0 * Y) / rho pow k`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`p0 * Y:real`; `&k * log rho`] LOG_LE_EXP) THEN
    REWRITE_TAC[REAL_EXP_N] THEN
    SUBGOAL_THEN `exp(log rho) = rho` SUBST1_TAC THENL
     [MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&k * log rho <= &k * l1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(p0 * Y) / rho pow k <= (p0 * Z / rho pow k) * P`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(p0 * Z / rho pow k) * P = (p0 * (Z * P)) / rho pow k`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&k * l1 - &1 <= ((&k * l1 - &1) / D2) * P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((&k * l1 - &1) / D2) * D2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Generic corner evaluation: for h >= h0, a1, a2 >= a0, the quotient        *)
(* laurent_bound rho h a1 a2 / (h^2 a1 a2) is at most c, provided the        *)
(* rational side conditions on the corner values hold (they are checked      *)
(* by REAL_RAT_REDUCE_CONV in each instance).                                *)
(* ------------------------------------------------------------------------- *)

let LAURENT_CORNER_GENERIC = prove
 (`!rho h a1 a2 l0 l1 h0 a0 H0 s0 om0 th0 r0 sh0 x0 C0 q0 p0 k c.
        &1 < rho /\ &0 < l0 /\ l0 <= log rho /\ log rho <= l1 /\
        &0 < h0 /\ h0 <= h /\ &0 < a0 /\ a0 <= a1 /\ a0 <= a2 /\
        &0 < H0 /\ H0 <= h0 / l1 + &1 /\
        &0 <= s0 /\ &1 + inv(&4 * H0 pow 2) <= s0 pow 2 /\
        &2 * (&1 + s0) <= om0 /\ s0 + inv(&2 * H0) <= th0 /\
        &0 <= r0 /\ om0 pow 5 * th0 <= r0 pow 4 /\
        &0 < sh0 /\ sh0 pow 2 <= H0 /\
        &0 <= x0 /\
        om0 pow 2 / &9 + &8 * l1 * r0 / (&3 * a0 * sh0) +
        &4 / &3 * (&2 / a0) * l1 * om0 / H0 <= x0 pow 2 /\
        inv(l0 pow 3) * (om0 / &6 + x0 / &2) pow 2 <= C0 /\
        &0 <= q0 /\ om0 * th0 <= q0 pow 2 /\
        &0 <= p0 /\ C0 * om0 * th0 / l0 pow 3 <= p0 pow 2 /\
        &1 <= &k * l1 /\
        C0 * (&1 + l1 / h0) pow 2 +
        q0 * (&1 + l1 / h0) / (h0 * a0 pow 2) +
        (&k * l1 - &1) / (h0 pow 2 * a0 pow 2) +
        p0 * (&1 + l1 / h0) pow 2 / rho pow k <= c
        ==> laurent_bound rho h a1 a2 <= c * h pow 2 * a1 * a2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rho:real`; `h:real`; `a1:real`; `a2:real`; `l0:real`;
                `l1:real`; `h0:real`; `a0:real`; `H0:real`; `s0:real`;
                `om0:real`; `th0:real`; `r0:real`; `sh0:real`; `x0:real`;
                `C0:real`] LAURENT_CORNER_C) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < laurent_Cp rho h a1 a2 /\ laurent_Cp rho h a1 a2 <= p0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[laurent_Cp] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MATCH_MP_TAC LAURENT_CORNER_CP_ATOM THEN
    MAP_EVERY EXISTS_TAC [`l0:real`; `C0:real`; `om0:real`; `th0:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h /\ &0 < a1 /\ &0 < a2 /\ &0 < log rho /\ &0 <= l1`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h + log rho /\ h + log rho <= (&1 + l1 / h0) * h /\
                &0 <= &1 + l1 / h0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= l1 / h0 /\ l1 <= l1 / h0 * h` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `l1 / h0 * h = (l1 * h) / h0` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; ASSUME `&0 < h0`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ASSUME `log rho <= l1`) THEN MP_TAC(ASSUME `&0 < h`) THEN
    MP_TAC(ASSUME `&0 < log rho`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a0 pow 2 <= a1 * a2 /\ &0 < a1 * a2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h + log rho) pow 2 * a1 * a2 <=
                (&1 + l1 / h0) pow 2 * h pow 2 * a1 * a2`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (h + log rho) pow 2 * a1 * a2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `h0 pow 2 * a0 pow 2 <= h pow 2 * a1 * a2 /\
                &0 < h0 pow 2 * a0 pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h0 * a0 pow 2) * h <= h pow 2 * a1 * a2 /\
                &0 < h0 * a0 pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `h pow 2 * a1 * a2 = (h * a1 * a2) * (h:real)`
      SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[laurent_bound] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC LAURENT_CORNER_SUM3 THEN
  MAP_EVERY EXISTS_TAC
   [`C0 * (&1 + l1 / h0) pow 2`;
    `q0 * (&1 + l1 / h0) / (h0 * a0 pow 2)`;
    `(&k * l1 - &1) / (h0 pow 2 * a0 pow 2) +
     p0 * (&1 + l1 / h0) pow 2 / rho pow k`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LAURENT_CORNER_TERM1 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC LAURENT_CORNER_TERM2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `om0 * th0:real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC LAURENT_CORNER_TERM3 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The corner instances. Corner values (rounded in the safe direction): l0,  *)
(* l1 bound log rho, H0 <= h0 / l1 + 1, s0 >= sqrt(1 + 1/(4 H0^2)), om0 =    *)
(* 2(1 + s0), th0 >= s0 + 1/(2 H0), r0 the fourth root of om0^5 th0, sh0 <=  *)
(* sqrt H0, x0 >= sqrt of the radicand, C0, q0 >= sqrt(om0 th0), p0 the C    *)
(* prime bound, k with rho^k near the argument of the logarithm. Values of   *)
(* 36 (resp. (rho+1)^2) times the bound: 31.34 <= 32 (exact corner value     *)
(* 31.288), 24.29 <= 25 (24.247), 21.88 <= 22.5 (21.837).                    *)
(* ------------------------------------------------------------------------- *)

let LAURENT_BOUND_CORNER_5_10 = prove
 (`!h a1 a2. &10 <= h /\ &6 <= a1 /\ &6 <= a2
            ==> laurent_bound (&5) h a1 a2 <= &32 / &36 * h pow 2 * a1 * a2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`&5`; `h:real`; `a1:real`; `a2:real`; `&1609 / &1000`; `&161 / &100`;
    `&10`; `&6`; `&7211 / &1000`; `&5013 / &5000`; `&10013 / &2500`;
    `&10721 / &10000`; `&57657 / &10000`; `&6713 / &2500`;
    `&19279 / &10000`; `&6391 / &10000`; `&20723 / &10000`;
    `&4059 / &5000`; `5`; `&32 / &36`] LAURENT_CORNER_GENERIC) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LAURENT_CORNER_LOG_5] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* A further instance: rho = 5.3, m = 20, Corollary-2 constant 25.           *)

let LAURENT_BOUND_CORNER_53_20 = prove
 (`!h a1 a2. &20 <= h /\ &63 / &10 <= a1 /\ &63 / &10 <= a2
            ==> laurent_bound (&53 / &10) h a1 a2 <=
                &25 / (&63 / &10) pow 2 * h pow 2 * a1 * a2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`&53 / &10`; `h:real`; `a1:real`; `a2:real`; `&1667 / &1000`;
    `&417 / &250`; `&20`; `&63 / &10`; `&129903 / &10000`;
    `&10009 / &10000`; `&20009 / &5000`; `&2079 / &2000`;
    `&57153 / &10000`; `&36041 / &10000`; `&3531 / &2000`;
    `&2593 / &5000`; `&20397 / &10000`; `&3413 / &5000`; `6`;
    `&25 / (&63 / &10) pow 2`] LAURENT_CORNER_GENERIC) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LAURENT_CORNER_LOG_53_10] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* A further instance: rho = 5.5, m = 30, constant 22.5.                     *)

let LAURENT_BOUND_CORNER_55_30 = prove
 (`!h a1 a2. &30 <= h /\ &13 / &2 <= a1 /\ &13 / &2 <= a2
            ==> laurent_bound (&11 / &2) h a1 a2 <=
                &45 / &2 / (&13 / &2) pow 2 * h pow 2 * a1 * a2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`&11 / &2`; `h:real`; `a1:real`; `a2:real`; `&213 / &125`;
    `&341 / &200`; `&30`; `&13 / &2`; `&11622 / &625`; `&2001 / &2000`;
    `&4001 / &1000`; `&411 / &400`; `&56973 / &10000`; `&43121 / &10000`;
    `&16893 / &10000`; `&4619 / &10000`; `&20277 / &10000`;
    `&6197 / &10000`; `6`; `&45 / &2 / (&13 / &2) pow 2`]
   LAURENT_CORNER_GENERIC) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LAURENT_CORNER_LOG_11_2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
