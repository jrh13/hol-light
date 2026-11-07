(* ========================================================================= *)
(* Two logarithms, the Laurent bound: the parameter recipe of the            *)
(* numeric layer.                                                            *)
(*                                                                           *)
(* Purpose: the parameters of M. Laurent, Linear forms in two logarithms and *)
(* interpolation determinants II, Acta Arith. 133 (2008), proof of Theorem 2 *)
(* (section 3) at mu = 1. For rho in [4, 8], h >= 10, a1, a2 >= 1 and        *)
(* a1 a2 >= (log rho)^2 they are, with lam = log rho and H = h / lam + 1:    *)
(*   L   the integer with H + sqrt(H^2 + 1/4) - 1/2 < L <= ... + 1/2,        *)
(*   k   the square of the positive root of U X^2 - V X - W,                 *)
(*       U = lam (L - H), V = L / 3,                                         *)
(*       W = (1/a1 + 1/a2) / 3 + (2/3) sqrt(L / (a1 a2)),                    *)
(*   K = 1 + floor(k L a1 a2), R1 = 1 + floor(sqrt(L a2 / a1)),              *)
(*   R2 = 1 + floor(sqrt(K - 1) sqrt(L a2 / a1)), S1, S2 symmetric,          *)
(* together with: the grid conditions L <= R1 S1, (K - 1) L < R2 S2; the     *)
(* root identities; the inequality (16) of Laurent (Laurent, Mignotte,       *)
(* Nesterenko, J. Number Theory 55 (1995), Lemme 9; our own proof) combined  *)
(* with Phi >= 0 (the g-term line); the bounds K L lam <= C (h + lam)^2      *)
(* a1 a2 + sqrt(omega theta) (h + lam) (Laurent (19)), L R, L S <= 1.86 C    *)
(* prime (h + lam)^2 a1 a2 (Laurent (21), (27)) and R a1 + S a2 <=           *)
(* C (h + lam)^2 a1 a2 / 2.                                                  *)
(*                                                                           *)
(* Route (own proofs of the steps of Laurent, section 3):                    *)
(*  - with s = sqrt(H^2 + 1/4): omega = 2 (H + s) / H, theta = (s + 1/2) / H *)
(*    and sqrt(omega theta) H = H + s + 1/2, the upper end of the interval;  *)
(*    L^2 <= omega H (L - H) on the interval (a quadratic inequality);       *)
(*  - Lemma 5 of Laurent at alpha = 5/2 by fourth powers, then               *)
(*    lam sqrt(k) L <= Z H with Z = sqrt(C lam^3) by monotonicity in L^2 /   *)
(*    (L - H);                                                               *)
(*  - (16): g L (R a1 + S a2) is increasing in R and S; substitute the upper *)
(*    bounds 1 + (1 + t) sqrt(L a2 / a1) etc. and use                        *)
(*    c / d <= x + c / (x + d) for c <= d^2 (LAURENT_PA_FRAC);               *)
(*  - Phi >= 0 from the quadratic: U k = V sqrt k + W;                       *)
(*  - crude size bounds from 4 H <= 3 lam sqrt(k) L (k >= (V/U)^2).          *)
(*                                                                           *)
(* The lemmas and the final theorem are stated and proved under              *)
(* prioritize_real (the statement of the final theorem does not depend on    *)
(* the priority); the file ends with prioritize_num.                         *)
(*                                                                           *)
(* Main results: LAURENT_PARAM_MAIN (the parameters with all the properties  *)
(* above); helper names LAURENT_PA_*.                                        *)
(*                                                                           *)
(* Uses: Baker/laurent_defs.ml (laurent_omega, laurent_theta, laurent_C,     *)
(* laurent_Cp), Baker/twolog_param.ml (REAL_NUM_FLOOR, LOG_LE_EXP,           *)
(* LOG_GE_EXP, EXP_1_APPROX, EXP_NUM_GE_POW).                                *)
(* ========================================================================= *)

needs "Baker/twolog_param.ml";;
needs "Baker/laurent_defs.ml";;

prioritize_real();;
prioritize_num();;

(* The lemmas below are pure real analysis: parse with real priority.        *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* 1. Numerical facts: 1.3 <= log rho <= 2.1 for rho in [4, 8].              *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PA_LOG_RHO = prove
 (`!rho. &4 <= rho /\ rho <= &8
         ==> &13 / &10 <= log rho /\ log rho <= &21 / &10`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`rho:real`; `&1`] LOG_GE_EXP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp(&1) / rho <= &7 / &10` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= rho ==> &0 < rho`] THEN
      MP_TAC EXP_1_APPROX THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MP_TAC(SPECL [`rho:real`; `&2`] LOG_LE_EXP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `rho / exp(&2) <= &11 / &10` MP_TAC THENL
     [SIMP_TAC[REAL_LE_LDIV_EQ; REAL_EXP_POS_LT] THEN
      MP_TAC(SPEC `2` EXP_NUM_GE_POW) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* 2. omega, theta and the interval for L (Laurent (8), (11)): with          *)
(*    s = sqrt(H^2 + 1/4), omega H = 2 (H + s), theta H = s + 1/2.           *)
(* ------------------------------------------------------------------------- *)

(* Elementary facts on s = sqrt(H^2 + 1/4).                                  *)

let LAURENT_PA_SQRT_QUARTER = prove
 (`!H. &0 < H
       ==> H < sqrt(H pow 2 + &1 / &4) /\
           sqrt(H pow 2 + &1 / &4) <= H + &1 / &2 /\
           &1 / &2 <= sqrt(H pow 2 + &1 / &4) /\
           sqrt(H pow 2 + &1 / &4) pow 2 = H pow 2 + &1 / &4`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= H pow 2 + &1 / &4` ASSUME_TAC THENL
   [MP_TAC(SPEC `H:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    MP_TAC(SPEC `H:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[SQRT_POW_2]]);;

(* Closed forms of omega and theta; sqrt(omega theta) H = H + s + 1/2.       *)

let LAURENT_PA_OMEGA_THETA = prove
 (`!H. &0 < H
       ==> laurent_omega H = &2 * (H + sqrt(H pow 2 + &1 / &4)) / H /\
           laurent_theta H = (sqrt(H pow 2 + &1 / &4) + &1 / &2) / H /\
           sqrt(laurent_omega H * laurent_theta H) =
           (H + sqrt(H pow 2 + &1 / &4) + &1 / &2) / H`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `H:real` LAURENT_PA_SQRT_QUARTER) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = sqrt(H pow 2 + &1 / &4)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&1 + inv(&4 * H pow 2)) = s / H` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_POW_DIV] THEN UNDISCH_TAC `&0 < H` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[laurent_omega; laurent_theta] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < H` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `&0 < H` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `s pow 2 = H pow 2 + &1 / &4` THEN
      UNDISCH_TAC `&0 < H` THEN CONV_TAC REAL_FIELD]]);;

(* omega and theta are nonnegative.                                          *)

let LAURENT_PA_OMEGA_THETA_POS = prove
 (`!H. &0 < H ==> &0 <= laurent_omega H /\ &0 <= laurent_theta H`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 + inv(&4 * H pow 2)) /\ &0 <= inv(&2 * H)`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MP_TAC(SPEC `H:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[laurent_omega; laurent_theta] THEN REAL_ARITH_TAC]);;

(* On the interval of L: L^2 <= omega H (L - H) (Laurent (11)), 4 H (L - H)  *)
(* <= L^2 and L <= sqrt(omega theta) H (Laurent (8)).                        *)

let LAURENT_PA_INTERVAL = prove
 (`!H x. &0 < H /\
         H + sqrt(H pow 2 + &1 / &4) - &1 / &2 < x /\
         x <= H + sqrt(H pow 2 + &1 / &4) + &1 / &2
         ==> H < x /\ &2 * H - &1 / &2 < x /\ x <= &2 * H + &1 /\
             x pow 2 <= laurent_omega H * H * (x - H) /\
             &4 * H * (x - H) <= x pow 2 /\
             x <= sqrt(laurent_omega H * laurent_theta H) * H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `H:real` LAURENT_PA_OMEGA_THETA) THEN
  MP_TAC(SPEC `H:real` LAURENT_PA_SQRT_QUARTER) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = sqrt(H pow 2 + &1 / &4)` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(&2 * (H + s) / H) * H * (x - H) = &2 * (H + s) * (x - H)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < H` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(x - H - s - &1 / &2) * (x - H - s + &1 / &2) <= &0`
    MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `s pow 2 = H pow 2 + &1 / &4` THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `x - &2 * H` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `(H + s + &1 / &2) / H * H = H + s + &1 / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < H` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The positive root of U X^2 - V X - W (its square is k).                *)
(* ------------------------------------------------------------------------- *)

(* sqrt k = (V + sqrt(V^2 + 4 U W)) / (2 U), with the consequences V / U <=  *)
(* sqrt k and (V / U)^2 + W / U <= k used in Baker/laurent_param.ml.         *)

let LAURENT_PA_ROOT = prove
 (`!U V W. &0 < U /\ &0 < V /\ &0 <= W
           ==> ?k. &0 < k /\
                   sqrt k = (V + sqrt(V pow 2 + &4 * U * W)) / (&2 * U) /\
                   U * k = V * sqrt k + W /\
                   V / U <= sqrt k /\ (V / U) pow 2 + W / U <= k`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = sqrt(V pow 2 + &4 * U * W)` THEN
  SUBGOAL_THEN `V <= d /\ d pow 2 = V pow 2 + &4 * U * W`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= U * W` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN
      MP_TAC(SPEC `V:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `V / U <= (V + d) / (&2 * U)` ASSUME_TAC THENL
   [SUBGOAL_THEN `V / U = (V + V) / (&2 * U)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < U` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < U ==> &0 < &2 * U`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `U * ((V + d) / (&2 * U)) pow 2 = V * ((V + d) / (&2 * U)) + W`
  ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 = V pow 2 + &4 * U * W` THEN
    UNDISCH_TAC `&0 < U` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `y = (V + d) / (&2 * U)` THEN
  SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `V / U` THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  EXISTS_TAC `y pow 2` THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_POW_LT] THEN
  SUBGOAL_THEN `y pow 2 = (V * y + W) / U /\
                (V / U) pow 2 + W / U = (V * (V / U) + W) / U`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < U` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> a + c <= b + c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* 4. Laurent (19) and (21): lam sqrt(k) L <= Z H, Z = sqrt(C lam^3),        *)
(*    via Lemma 5 at alpha = 5/2 and monotonicity in L^2 / (L - H).          *)
(* ------------------------------------------------------------------------- *)

(* Lemma 5 at alpha = 5/2: L^2 / (L - H) times sqrt L is at most omega^(5/4) *)
(* theta^(1/4) H^(3/2), compared as fourth powers.                           *)

let LAURENT_PA_LEMMA5 = prove
 (`!P x om th H.
     &0 <= P /\ P <= om * H /\ &0 <= x /\ x <= sqrt(om * th) * H /\
     &0 <= om /\ &0 <= th /\ &0 <= H
     ==> P * sqrt x <= sqrt(sqrt(om pow 5 * th)) * H * sqrt H`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= om pow 5 * th /\ &0 <= om * th` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `4:num` THEN
  REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P * sqrt x) pow 4 = P pow 4 * (sqrt x pow 2) pow 2 /\
    (sqrt(sqrt(om pow 5 * th)) * H * sqrt H) pow 4 =
    (sqrt(sqrt(om pow 5 * th)) pow 2) pow 2 * H pow 4 * (sqrt H pow 2) pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(om * H) pow 4 * (sqrt(om * th) * H) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_POW_2; REAL_POW_LE2];
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
    REAL_ARITH_TAC]);;

(* Monotonicity of p / 6 + sqrt(p^2 / 9 + c1 p + c2 q) / 2 in p and q.       *)

let LAURENT_PA_F_MONO = prove
 (`!p q p' q' c1 c2.
     &0 <= p /\ p <= p' /\ q <= q' /\ &0 <= c1 /\ &0 <= c2
     ==> p / &6 + sqrt(p pow 2 / &9 + c1 * p + c2 * q) / &2 <=
         p' / &6 + sqrt(p' pow 2 / &9 + c1 * p' + c2 * q') / &2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a:real) <= a' /\ b <= b' ==> a / &6 + b / &2 <= a' / &6 + b' / &2`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  MATCH_MP_TAC(REAL_ARITH
   `(x:real) <= x' /\ y <= y' /\ z <= z'
    ==> x / &9 + y + z <= x' / &9 + y' + z'`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* The algebraic identity behind Laurent (18).                               *)

let LAURENT_PA_SQRTK_ALG = prove
 (`!lam x H ia sx sa D.
     ~(lam = &0) /\ ~(x - H = &0) /\ ~(sa = &0) /\
     D = (x / &3) pow 2 + &4 * (lam * (x - H)) * (ia / &3 + &2 / &3 * sx / sa)
     ==> (x pow 2 / (x - H)) pow 2 / &9 +
         (&4 / &3 * ia * lam) * (x pow 2 / (x - H)) +
         (&8 / &3 * lam / sa) * (x pow 2 / (x - H) * sx) =
         (x / (x - H)) pow 2 * D`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`~(lam = &0)`; `~(x - H = &0)`; `~(sa = &0)`] THEN
  CONV_TAC REAL_FIELD);;

(* Laurent (18): lam sqrt(k) L as a function of P = L^2 / (L - H) and P sqrt *)
(* L.                                                                        *)

let LAURENT_PA_SQRTK_L = prove
 (`!lam H x a1 a2 k.
     &0 < lam /\ H < x /\ &0 < x /\ &0 < a1 /\ &0 < a2 /\
     sqrt k =
     (x / &3 +
      sqrt((x / &3) pow 2 + &4 * (lam * (x - H)) *
           ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))))) /
     (&2 * (lam * (x - H)))
     ==> lam * sqrt k * x =
         (x pow 2 / (x - H)) / &6 +
         sqrt((x pow 2 / (x - H)) pow 2 / &9 +
              (&4 / &3 * (inv a1 + inv a2) * lam) * (x pow 2 / (x - H)) +
              (&8 / &3 * lam / sqrt(a1 * a2)) * (x pow 2 / (x - H) * sqrt x)) /
         &2`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SQRT_DIV] THEN
  SUBGOAL_THEN `&0 < sqrt(a1 * a2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ABBREV_TAC
   `D = (x / &3) pow 2 + &4 * (lam * (x - H)) *
        ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt x / sqrt(a1 * a2))` THEN
  MP_TAC(SPECL [`lam:real`; `x:real`; `H:real`; `inv a1 + inv a2`;
                `sqrt x`; `sqrt(a1 * a2)`; `D:real`] LAURENT_PA_SQRTK_ALG) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `sqrt((x / (x - H)) pow 2) = x / (x - H)` SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < lam`; `H < x`] THEN CONV_TAC REAL_FIELD);;

(* Z H in the same shape, with omega H and omega^(5/4) theta^(1/4) H^(3/2)   *)
(* in place of P and P sqrt L.                                               *)

let LAURENT_PA_ZH = prove
 (`!lam H om th a1 a2.
     &0 < H /\ &0 < a1 /\ &0 < a2
     ==> (om / &6 +
          sqrt(om pow 2 / &9 +
               &8 * lam * sqrt(sqrt(om pow 5 * th)) /
               (&3 * sqrt(a1 * a2) * sqrt H) +
               &4 / &3 * (inv a1 + inv a2) * lam * om / H) / &2) * H =
         (om * H) / &6 +
         sqrt((om * H) pow 2 / &9 +
              (&4 / &3 * (inv a1 + inv a2) * lam) * (om * H) +
              (&8 / &3 * lam / sqrt(a1 * a2)) *
              (sqrt(sqrt(om pow 5 * th)) * H * sqrt H)) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(a1 * a2) /\ &0 < sqrt H /\ sqrt H pow 2 = H`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[REAL_LT_MUL];
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `Q = sqrt(sqrt(om pow 5 * th))` THEN
  ABBREV_TAC `sa = sqrt(a1 * a2)` THEN
  ABBREV_TAC `sh = sqrt H` THEN
  MATCH_MP_TAC(REAL_ARITH
   `(b:real) * H = b'
    ==> (om / &6 + b / &2) * H = (om * H) / &6 + b' / &2`) THEN
  SUBGOAL_THEN `!X. sqrt X * H = sqrt(X * H pow 2)` (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[SQRT_MUL] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  MAP_EVERY UNDISCH_TAC [`sh pow 2 = H`; `&0 < sa`; `&0 < sh`; `&0 < H`] THEN
  CONV_TAC REAL_FIELD);;

(* Laurent (19) in the form lam sqrt(k) L <= Z H.                            *)

let LAURENT_PA_KL = prove
 (`!lam H x om th a1 a2 k.
     &0 < lam /\ &0 < H /\ H < x /\ &0 < a1 /\ &0 < a2 /\
     &0 <= om /\ &0 <= th /\
     x pow 2 <= om * H * (x - H) /\ x <= sqrt(om * th) * H /\
     sqrt k =
     (x / &3 +
      sqrt((x / &3) pow 2 + &4 * (lam * (x - H)) *
           ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))))) /
     (&2 * (lam * (x - H)))
     ==> lam * sqrt k * x <=
         (om / &6 +
          sqrt(om pow 2 / &9 +
               &8 * lam * sqrt(sqrt(om pow 5 * th)) /
               (&3 * sqrt(a1 * a2) * sqrt H) +
               &4 / &3 * (inv a1 + inv a2) * lam * om / H) / &2) * H`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`lam:real`; `H:real`; `x:real`; `a1:real`; `a2:real`; `k:real`]
    LAURENT_PA_SQRTK_L) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`lam:real`; `H:real`; `om:real`; `th:real`;
                `a1:real`; `a2:real`]
    LAURENT_PA_ZH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 <= x pow 2 / (x - H) /\ x pow 2 / (x - H) <= om * H`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC LAURENT_PA_F_MONO THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LAURENT_PA_LEMMA5 THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC]]);;

(* The choice of k together with (19).                                       *)

let LAURENT_PA_K_EXISTS = prove
 (`!lam H x om th a1 a2.
     &0 < lam /\ &0 < H /\ H < x /\ &0 < a1 /\ &0 < a2 /\
     &0 <= om /\ &0 <= th /\
     x pow 2 <= om * H * (x - H) /\ x <= sqrt(om * th) * H
     ==> ?k. &0 < k /\
             (lam * (x - H)) * k =
             x / &3 * sqrt k +
             ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))) /\
             x / &3 / (lam * (x - H)) <= sqrt k /\
             (x / &3 / (lam * (x - H))) pow 2 +
             ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))) /
             (lam * (x - H)) <= k /\
             lam * sqrt k * x <=
             (om / &6 +
              sqrt(om pow 2 / &9 +
                   &8 * lam * sqrt(sqrt(om pow 5 * th)) /
                   (&3 * sqrt(a1 * a2) * sqrt H) +
                   &4 / &3 * (inv a1 + inv a2) * lam * om / H) / &2) * H`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`lam * (x - H)`; `x / &3`;
                `(inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))`]
    LAURENT_PA_ROOT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_ADD THEN
          ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC;
          MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
          CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC LAURENT_PA_KL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* lam k L^2 <= C (lam H)^2 with C = Z^2 / lam^3.                            *)

let LAURENT_PA_KL_C = prove
 (`!lam H x k Z.
     &0 < lam /\ &0 <= k /\ &0 <= x /\ lam * sqrt k * x <= Z * H
     ==> lam * k * x pow 2 <= inv(lam pow 3) * Z pow 2 * (lam * H) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(lam * sqrt k * x) pow 2 <= (Z * H) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `lam * k * x pow 2 = (lam pow 2 * k * x pow 2) / lam /\
    inv(lam pow 3) * Z pow 2 * lam pow 2 * H pow 2 = (Z pow 2 * H pow 2) / lam`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ]]);;

(* Laurent (21): sqrt(k) L^2 <= Cp (lam H)^2 with Cp = Z sqrt(omega theta) / *)
(* lam^3.                                                                    *)

let LAURENT_PA_KL_CP = prove
 (`!lam H x k Z c.
     &0 < lam /\ &0 <= k /\ &0 <= x /\
     lam * sqrt k * x <= Z * H /\ x <= c * H
     ==> sqrt k * x pow 2 <= (Z * c / lam pow 3) * (lam * H) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(lam * sqrt k * x) * x <= (Z * H) * (c * H)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `sqrt k * x pow 2 = ((lam * sqrt k * x) * x) / lam /\
    (Z * c / lam pow 3) * (lam * H) pow 2 = ((Z * H) * (c * H)) / lam`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ]]);;

(* The closed form of laurent_Cp in terms of Z.                              *)

let LAURENT_PA_CP_EQ = prove
 (`!lam Z om th.
     &0 < lam /\ &0 <= Z /\ &0 <= om * th
     ==> sqrt((inv(lam pow 3) * Z pow 2) * om * th / lam pow 3) =
         Z * sqrt(om * th) / lam pow 3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_POW_LE; REAL_LT_IMP_LE];
    REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
    ASM_SIMP_TAC[SQRT_POW_2] THEN UNDISCH_TAC `&0 < lam` THEN
    CONV_TAC REAL_FIELD]);;

(* Unfolding of the definitions laurent_C and laurent_Cp.                    *)

let LAURENT_PA_C_UNFOLD = prove
 (`!rho h a1 a2 lam H.
     log rho = lam /\ h / lam + &1 = H
     ==> laurent_C rho h a1 a2 =
         inv(lam pow 3) *
         (laurent_omega H / &6 +
          sqrt(laurent_omega H pow 2 / &9 +
               &8 * lam *
               sqrt(sqrt(laurent_omega H pow 5 * laurent_theta H)) /
               (&3 * sqrt(a1 * a2) * sqrt H) +
               &4 / &3 * (inv a1 + inv a2) * lam * laurent_omega H / H) /
          &2) pow 2 /\
         laurent_Cp rho h a1 a2 =
         sqrt(laurent_C rho h a1 a2 * laurent_omega H * laurent_theta H /
              lam pow 3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[laurent_C; laurent_Cp] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Laurent (16) = LMN Lemme 9 (own proof) and Phi >= 0.                   *)
(* ------------------------------------------------------------------------- *)

(* c / d <= x + c / (x + d) for x >= 0 and c <= d^2.                         *)

let LAURENT_PA_FRAC = prove
 (`!x c d. &0 <= x /\ &0 < d /\ c <= d pow 2 ==> c / d <= x + c / (x + d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x + d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c / d = c / (x + d) + (c * x) / (d * (x + d))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < x + d` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= x ==> a + b <= x + a`) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) * c <= x * e ==> c * x <= x * e`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d pow 2` THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* With A = sqrt(x) sqrt(a1 a2): a1 sqrt(x a2 / a1) = A, a2 sqrt(x a1 / a2)  *)
(* = A, A^2 = x a1 a2.                                                       *)

let LAURENT_PA_SQRT_PROD = prove
 (`!x a1 a2. &0 <= x /\ &0 < a1 /\ &0 < a2
             ==> a1 * sqrt(x * a2 / a1) = sqrt x * sqrt(a1 * a2) /\
                 a2 * sqrt(x * a1 / a2) = sqrt x * sqrt(a1 * a2) /\
                 (sqrt x * sqrt(a1 * a2)) pow 2 = x * a1 * a2 /\
                 sqrt(x / (a1 * a2)) = sqrt x / sqrt(a1 * a2) /\
                 sqrt(x / (a1 * a2)) = (sqrt x * sqrt(a1 * a2)) / (a1 * a2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SQRT_DIV; SQRT_MUL] THEN
  MP_TAC(SPEC `a1:real` SQRT_POW_2) THEN MP_TAC(SPEC `a2:real` SQRT_POW_2) THEN
  MP_TAC(SPEC `x:real` SQRT_POW_2) THEN
  MP_TAC(SPEC `a1:real` SQRT_POS_LT) THEN
  MP_TAC(SPEC `a2:real` SQRT_POS_LT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONV_TAC REAL_FIELD);;

(* Laurent (16) = LMN Lemme 9, with K = t^2 + 1: the g-term is increasing in *)
(* R and S, then LAURENT_PA_FRAC at x = a1, a2.                              *)

let LAURENT_PA_LMN16 = prove
 (`!x a1 a2 t K R S u v A.
     &0 < x /\ &0 < a1 /\ &0 < a2 /\ &0 <= t /\ K = t pow 2 + &1 /\
     &0 < R /\ &0 < S /\ &0 < A /\
     a1 * u = A /\ a2 * v = A /\ A pow 2 = x * a1 * a2 /\
     R - &1 <= (&1 + t) * u /\ S - &1 <= (&1 + t) * v
     ==> (&1 / &4 - (K * x) / (&12 * R * S)) * x * (R * a1 + S * a2) <=
         x * A * t / &3 + &2 / &3 * x * A + x * (a1 + a2) / &3 -
         x * A / (&6 * (&1 + t))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = (&1 + t) * A` THEN
  SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `R * a1 <= a1 + B /\ S * a2 <= a2 + B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 + (&1 + t) * u) * a1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "B" THEN
        UNDISCH_TAC `a1 * u = A` THEN CONV_TAC REAL_RING];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 + (&1 + t) * v) * a2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "B" THEN
        UNDISCH_TAC `a2 * v = A` THEN CONV_TAC REAL_RING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R * a1 /\ &0 < S * a2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a1 * a2) / (a1 + B) <= a2 / R /\ (a1 * a2) / (a2 + B) <= a1 / S`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `a2 / R = (a1 * a2) / (R * a1) /\
                  a1 / S = (a1 * a2) / (S * a2)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < a1`; `&0 < a2`; `&0 < R`; `&0 < S`] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  ABBREV_TAC `J = (K * A pow 2) / B` THEN
  ABBREV_TAC `G1 = (K * A pow 2) / (a1 + B)` THEN
  ABBREV_TAC `G2 = (K * A pow 2) / (a2 + B)` THEN
  SUBGOAL_THEN `J <= a1 + G1 /\ J <= a2 + G2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `K * A pow 2 <= B pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `B pow 2 = K * A pow 2 + (&2 * t) * A pow 2`
      SUBST1_TAC THENL
       [EXPAND_TAC "B" THEN UNDISCH_TAC `K = t pow 2 + &1` THEN
        CONV_TAC REAL_RING;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> (a:real) <= a + b`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["J"; "G1"; "G2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC LAURENT_PA_FRAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 / &4 - (K * x) / (&12 * R * S)) * x * (R * a1 + S * a2) =
    x * (R * a1 + S * a2) / &4 - (K * x pow 2 / &12) * (a1 / S + a2 / R)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < R`; `&0 < S`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x / &12 * (G1 + G2) <= (K * x pow 2 / &12) * (a1 / S + a2 / R)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `(K * x pow 2 / &12) * ((a1 * a2) / (a2 + B) + (a1 * a2) / (a1 + B))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MAP_EVERY EXPAND_TAC ["G1"; "G2"] THEN
      UNDISCH_TAC `A pow 2 = x * a1 * a2` THEN
      MAP_EVERY UNDISCH_TAC [`&0 < x`; `&0 < a1`; `&0 < a2`; `&0 < B`] THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_POS];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `x * (&2 * J - a1 - a2) <= x * (G1 + G2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x * (R * a1 + S * a2) <= x * (a1 + B + a2 + B)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `x * B / &2 - x * J / &6 =
    x * A * t / &3 + &2 / &3 * x * A - &2 * (x * A / (&6 * (&1 + t)))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["J"; "B"] THEN
    MAP_EVERY UNDISCH_TAC [`K = t pow 2 + &1`; `&0 < A`; `&0 <= t`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x * A / (&6 * (&1 + t))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`x / &12 * (G1 + G2) <= (K * x pow 2 / &12) * (a1 / S + a2 / R)`;
    `x * (&2 * J - a1 - a2) <= x * (G1 + G2)`;
    `x * (R * a1 + S * a2) <= x * (a1 + B + a2 + B)`;
    `x * B / &2 - x * J / &6 =
     x * A * t / &3 + &2 / &3 * x * A - &2 * (x * A / (&6 * (&1 + t)))`;
    `&0 <= x * A / (&6 * (&1 + t))`] THEN
  REAL_ARITH_TAC);;

(* Phi >= 0: the main term of Laurent condition (2), from U k = V sqrt k + W *)
(* and K - 1 <= k L a1 a2 <= K.                                              *)

let LAURENT_PA_PHI = prove
 (`!x a1 a2 n k U A.
     &0 < x /\ &0 < a1 /\ &0 < a2 /\ &0 <= n /\ &0 <= k /\ &0 < U /\
     &0 <= A /\ A pow 2 = x * a1 * a2 /\
     sqrt(x / (a1 * a2)) = A / (a1 * a2) /\
     U * k = x / &3 * sqrt k +
             ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))) /\
     n <= k * x * a1 * a2 /\ k * x * a1 * a2 <= n + &1
     ==> x * A * sqrt n / &3 + &2 / &3 * x * A + x * (a1 + a2) / &3
         <= (n + &1) * U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a1 * a2 /\ &0 < x * a1 * a2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `A * sqrt n <= (x * a1 * a2) * sqrt k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2:num` THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(A * sqrt n) pow 2 = (x * a1 * a2) * n /\
      ((x * a1 * a2) * sqrt k) pow 2 = (x * a1 * a2) * (k * x * a1 * a2)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 / &3 * x * A + x * (a1 + a2) / &3 =
    (x * a1 * a2) * ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2)))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`&0 < a1`; `&0 < a2`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(x * a1 * a2) * (U * k)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`x / &3`; `A * sqrt n`; `(x * a1 * a2) * sqrt k`]
      REAL_LE_LMUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MP_TAC(SPECL [`U:real`; `k * x * a1 * a2`; `n + &1`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Sizes: K >= 2, R2, S2 >= 2, the grid conditions, L R and L S           *)
(*    (Laurent (27)) and R a1 + S a2.                                        *)
(* ------------------------------------------------------------------------- *)

(* 4 H <= 3 lam sqrt(k) L, from sqrt k >= V / U and 4 H (L - H) <= L^2.      *)

let LAURENT_PA_Y_LOWER = prove
 (`!lam H x k.
     &0 < lam /\ H < x /\ &0 < x /\ &4 * H * (x - H) <= x pow 2 /\
     (x / &3) / (lam * (x - H)) <= sqrt k
     ==> &4 * H <= &3 * lam * sqrt k * x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < lam * (x - H)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(x / &3) / (lam * (x - H)) <= sqrt k` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x * x / &3 <= x * (sqrt k * lam * (x - H))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * H) * (x - H) <= (&3 * lam * sqrt k * x) * (x - H)`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`x * x / &3 <= x * (sqrt k * lam * (x - H))`;
      `&4 * H * (x - H) <= x pow 2`] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  MATCH_MP_TAC REAL_LE_RMUL_EQ THEN ASM_REAL_ARITH_TAC);;

(* k L a1 a2 >= 1 (hence K >= 2) and k L^2 >= 2.                             *)

let LAURENT_PA_KBIG = prove
 (`!lam H x a1 a2 k.
     &0 < lam /\ lam <= &21 / &10 /\ &23 / &4 <= H /\ &0 < x /\
     x <= &2 * H + &1 /\ &1 <= a1 /\ &1 <= a2 /\ lam pow 2 <= a1 * a2 /\
     &0 <= k /\ &4 * H <= &3 * lam * sqrt k * x
     ==> &1 <= k * x * a1 * a2 /\ &2 <= k * x pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `y = sqrt k * x` THEN
  SUBGOAL_THEN `&0 <= y /\ y pow 2 = k * x pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * y <= &21 / &10 * y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `&3 * y <= y * y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `y pow 2 = k * x pow 2` THEN REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `x <= (lam * y) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 * H / &3) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * H + &1` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&23 / &4 * H <= H * H` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lam * y) pow 2 <= (k * x * a1 * a2) * x` MP_TAC THENL
   [SUBGOAL_THEN `(lam * y) pow 2 = lam pow 2 * (k * x pow 2) /\
                  (k * x * a1 * a2) * x = (a1 * a2) * (k * x pow 2)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 * x <= (k * x * a1 * a2) * x` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  MATCH_MP_TAC REAL_LE_RMUL_EQ THEN ASM_REWRITE_TAC[]);;

(* sqrt(K - 1) sqrt(L a2 / a1) >= 1 (hence R2 >= 2).                         *)

let LAURENT_PA_R2_POS = prove
 (`!n x a1 a2 k.
     &1 <= n /\ k * x * a1 * a2 < n + &1 /\ &0 < x /\ &1 <= a1 /\ &1 <= a2 /\
     &0 <= k /\ &2 <= k * x pow 2
     ==> &1 <= sqrt n * sqrt(x * a2 / a1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SQRT_MUL] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_ONE] THEN
  REWRITE_TAC[REAL_ARITH `n * x * a / b = (n * x * a) / b`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= a ==> &0 < a`;
               REAL_MUL_LID] THEN
  SUBGOAL_THEN `(k * x * a1 * a2) * (x * a2) <= (&2 * n) * (x * a2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * a1 <= (k * x pow 2) * a1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((k * x pow 2) * a1) * &1 <= ((k * x pow 2) * a1) * a2 pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(k * x * a1 * a2) * (x * a2) <= (&2 * n) * (x * a2)`;
    `&2 * a1 <= (k * x pow 2) * a1`;
    `((k * x pow 2) * a1) * &1 <= ((k * x pow 2) * a1) * a2 pow 2`] THEN
  REAL_ARITH_TAC);;

(* sqrt(x a2 / a1) sqrt(x a1 / a2) = x (for the grid conditions).            *)

let LAURENT_PA_GRID = prove
 (`!x a1 a2. &0 <= x /\ &0 < a1 /\ &0 < a2
             ==> sqrt(x * a2 / a1) * sqrt(x * a1 / a2) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SQRT_MUL] THEN
  SUBGOAL_THEN `(x * a2 / a1) * (x * a1 / a2) = x pow 2` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < a1`; `&0 < a2`] THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[POW_2_SQRT]]);;

(* Laurent (27) for L R with the constant 1.86 (crude estimates, using H >=  *)
(* 23/4).                                                                    *)

let LAURENT_PA_LR = prove
 (`!lam H x a1 a2 k n R.
     &13 / &10 <= lam /\ &23 / &4 <= H /\ &9 <= x /\ x <= &2 * H + &1 /\
     &1 <= a1 /\ &1 <= a2 /\ lam pow 2 <= a1 * a2 /\ &0 <= k /\
     &4 * H <= &3 * lam * sqrt k * x /\
     &0 <= n /\ n <= k * x * a1 * a2 /\
     R - &1 <= (&1 + sqrt n) * sqrt(x * a2 / a1)
     ==> x * R <= &186 / &100 * (sqrt k * x pow 2) * a1 * a2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x * a2 / a1 /\ &0 < a1 * a2 /\ &0 <= sqrt k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt n * sqrt(x * a2 / a1) <= sqrt k * x * a2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2:num` THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(k * x * a1 * a2) * (x * a2 / a1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&1 <= a1` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * sqrt(x * a2 / a1) <= sqrt x * (a1 * a2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2:num` THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_ARITH `&9 <= x ==> &0 <= x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(a1 pow 3 * a2) * (x * a2 / a1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * (a1 * a2)` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `a1 pow 3 * a2 = a1 pow 2 * (a1 * a2)`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE_1; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&1 <= a1` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt x <= x / &3` ASSUME_TAC THENL
   [SUBGOAL_THEN `&3 <= sqrt x /\ sqrt x * sqrt x = x` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&3 * sqrt x <= sqrt x * sqrt x` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `P = a1 * a2` THEN
  ABBREV_TAC `u = sqrt(x * a2 / a1)` THEN
  ABBREV_TAC `t = sqrt n` THEN
  ABBREV_TAC `y = sqrt k * x` THEN
  SUBGOAL_THEN `&1 + u <= &86 / &100 * y * P` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `lam:real` REAL_LE_LCANCEL_IMP) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt x * P <= x / &3 * P /\ x * P <= (&2 * H + &1) * P /\
                  (&4 * H) * P <= (&3 * lam * y) * P /\
                  &23 / &4 * P <= H * P /\
                  &13 / &10 * lam <= lam * lam`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `lam pow 2 <= P` THEN REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t * u <= y * P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y * a2` THEN CONJ_TAC THENL
     [EXPAND_TAC "y" THEN UNDISCH_TAC `t * u <= sqrt k * x * a2` THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "P" THEN
      REWRITE_TAC[REAL_ARITH `y * a1 * a2 = (y * a2) * a1`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `R <= &186 / &100 * y * P` ASSUME_TAC THENL
   [UNDISCH_TAC `R - &1 <= (&1 + t) * u` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt k * x pow 2) * P = x * y * P` SUBST1_TAC THENL
   [EXPAND_TAC "y" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `&186 / &100 * x * y * P = x * (&186 / &100 * y * P)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* R a1 + S a2 <= lam k L^2 a1 a2 / 2.                                       *)

let LAURENT_PA_RA = prove
 (`!lam H x a1 a2 k n R S.
     &0 < lam /\ &0 < H /\ H < x /\ &12 <= x /\ &0 < a1 /\ &0 < a2 /\
     &0 <= k /\
     (lam * (x - H)) * k =
     x / &3 * sqrt k +
     ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))) /\
     &4 <= lam * sqrt k * x /\
     &0 <= n /\ n <= k * x * a1 * a2 /\
     R - &1 <= (&1 + sqrt n) * sqrt(x * a2 / a1) /\
     S - &1 <= (&1 + sqrt n) * sqrt(x * a1 / a2)
     ==> R * a1 + S * a2 <= lam * k * x pow 2 * a1 * a2 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `a1:real`; `a2:real`] LAURENT_PA_SQRT_PROD) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < a1 * a2 /\ &0 < sqrt(a1 * a2) /\
                sqrt(a1 * a2) pow 2 = a1 * a2 /\ &0 <= sqrt k /\
                sqrt k pow 2 = k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE;
                 SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a1 + a2 + &2 * (sqrt x * sqrt(a1 * a2)) =
    &3 * ((inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))) * (a1 * a2)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`sqrt(a1 * a2) pow 2 = a1 * a2`; `&0 < sqrt(a1 * a2)`;
      `&0 < a1`; `&0 < a2`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `W = (inv a1 + inv a2) / &3 + &2 / &3 * sqrt(x / (a1 * a2))` THEN
  ABBREV_TAC `A = sqrt x * sqrt(a1 * a2)` THEN
  ABBREV_TAC `t = sqrt n` THEN
  SUBGOAL_THEN `&0 <= A /\ &0 <= t` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "t"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t * A <= sqrt k * x * a1 * a2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2:num` THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(t * A) pow 2 = n * (x * a1 * a2) /\
                  (sqrt k * x * a1 * a2) pow 2 =
                  (k * x * a1 * a2) * (x * a1 * a2)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "t" THEN ASM_SIMP_TAC[SQRT_POW_2];
        UNDISCH_TAC `sqrt k pow 2 = k` THEN CONV_TAC REAL_RING];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `R * a1 <= a1 + A + t * A /\ S * a2 <= a2 + A + t * A`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(R - &1) * a1 <= ((&1 + t) * sqrt(x * a2 / a1)) * a1`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `((&1 + t) * sqrt(x * a2 / a1)) * a1 = A + t * A`
      SUBST1_TAC THENL
       [UNDISCH_TAC `a1 * sqrt(x * a2 / a1) = A` THEN CONV_TAC REAL_RING;
        REAL_ARITH_TAC];
      SUBGOAL_THEN `(S - &1) * a2 <= ((&1 + t) * sqrt(x * a1 / a2)) * a2`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `((&1 + t) * sqrt(x * a1 / a2)) * a2 = A + t * A`
      SUBST1_TAC THENL
       [UNDISCH_TAC `a2 * sqrt(x * a1 / a2) = A` THEN CONV_TAC REAL_RING;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `W = (lam * (x - H)) * k - x / &3 * sqrt k` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `(lam * (x - H)) * k = x / &3 * sqrt k + W` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&3 * ((lam * (x - H)) * k) + sqrt k * x <= lam * k * x pow 2 / &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= lam * H * k /\
                  (lam * k) * (&12 * x) <= (lam * k) * (x * x) /\
                  &4 * (sqrt k * x) <= (lam * sqrt k * x) * (sqrt k * x) /\
                  (lam * sqrt k * x) * (sqrt k * x) = lam * k * x pow 2`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `sqrt k pow 2 = k` THEN CONV_TAC REAL_RING];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&3 * ((lam * (x - H)) * k) + sqrt k * x) * (a1 * a2) <=
    (lam * k * x pow 2 / &2) * (a1 * a2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`R * a1 <= a1 + A + t * A`; `S * a2 <= a2 + A + t * A`;
    `t * A <= sqrt k * x * a1 * a2`;
    `a1 + a2 + &2 * A =
     &3 * ((lam * (x - H)) * k - x / &3 * sqrt k) * (a1 * a2)`;
    `(&3 * ((lam * (x - H)) * k) + sqrt k * x) * (a1 * a2) <=
     (lam * k * x pow 2 / &2) * (a1 * a2)`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 7. The main theorem (stated and proved with real priority; its statement  *)
(*    parses to the same term under prioritize_num).                         *)
(* ------------------------------------------------------------------------- *)

let LAURENT_PARAM_MAIN = prove
 (`!rho h a1 a2.
     &4 <= rho /\ rho <= &8 /\ &10 <= h /\
     &1 <= a1 /\ &1 <= a2 /\ log rho pow 2 <= a1 * a2
     ==> ?K L R1 S1 R2 S2 k.
           let H = h / log rho + &1 in
           let U = log rho * (&L - H) in
           let V = &L / &3 in
           let W = (inv a1 + inv a2) / &3 + &2 / &3 * sqrt(&L / (a1 * a2)) in
           2 <= K /\ 11 <= L /\ 1 <= R1 /\ 1 <= S1 /\ 1 <= R2 /\ 1 <= S2 /\
           2 <= (R1 + R2) - 1 /\ 2 <= (S1 + S2) - 1 /\
           L <= R1 * S1 /\ (K - 1) * L < R2 * S2 /\
           H + sqrt(H pow 2 + &1 / &4) - &1 / &2 < &L /\
           &L <= H + sqrt(H pow 2 + &1 / &4) + &1 / &2 /\
           &0 < k /\ U * k = V * sqrt k + W /\
           V / U <= sqrt k /\ (V / U) pow 2 + W / U <= k /\
           &K - &1 <= k * &L * a1 * a2 /\ k * &L * a1 * a2 < &K /\
           &((R1 + R2) - 1) - &1 <= (&1 + sqrt(&K - &1)) * sqrt(&L * a2 / a1) /\
           &((S1 + S2) - 1) - &1 <= (&1 + sqrt(&K - &1)) * sqrt(&L * a1 / a2) /\
           (&1 / &4 - &(K * L) / (&12 * &((R1 + R2) - 1) * &((S1 + S2) - 1))) *
           &L * (&((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2) <=
           log rho * &K * &L - &K * (h + log rho) -
           &L * sqrt(&L) * sqrt(a1 * a2) / (&6 * (&1 + sqrt(&K - &1))) /\
           &(K * L) * log rho <=
             laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 +
             sqrt(laurent_omega H * laurent_theta H) * (h + log rho) /\
           &(L * ((R1 + R2) - 1)) <=
             &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 *
             a1 * a2 /\
           &(L * ((S1 + S2) - 1)) <=
             &186 / &100 * laurent_Cp rho h a1 a2 * (h + log rho) pow 2 *
             a1 * a2 /\
           &((R1 + R2) - 1) * a1 + &((S1 + S2) - 1) * a2 <=
             laurent_C rho h a1 a2 * (h + log rho) pow 2 * a1 * a2 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `rho:real` LAURENT_PA_LOG_RHO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `lam = log rho` THEN
  SUBGOAL_THEN `&0 < lam /\ &0 < a1 /\ &0 < a2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `H = h / lam + &1` THEN
  SUBGOAL_THEN `&23 / &4 <= H /\ h + lam = lam * H` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&19 / &4 <= x ==> &23 / &4 <= x + &1`) THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < H` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`rho:real`; `h:real`; `a1:real`; `a2:real`; `lam:real`;
                `H:real`] LAURENT_PA_C_UNFOLD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th] THEN
                       REWRITE_TAC[CONJUNCT1 th]) THEN
  MP_TAC(SPEC `H:real` LAURENT_PA_OMEGA_THETA_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPEC `H:real` LAURENT_PA_SQRT_QUARTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPEC `H + sqrt(H pow 2 + &1 / &4) + &1 / &2` REAL_NUM_FLOOR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `H + sqrt(H pow 2 + &1 / &4) - &1 / &2 < &L /\
    &L <= H + sqrt(H pow 2 + &1 / &4) + &1 / &2`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`H:real`; `&L`] LAURENT_PA_INTERVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `12 <= L` ASSUME_TAC THENL
   [SUBGOAL_THEN `&11 < &L` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&12 <= &L /\ &0 < &L` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `12 <= L` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `om = laurent_omega H` THEN
  ABBREV_TAC `th = laurent_theta H` THEN
  ABBREV_TAC
   `Z = om / &6 +
        sqrt(om pow 2 / &9 +
             &8 * lam * sqrt(sqrt(om pow 5 * th)) /
             (&3 * sqrt(a1 * a2) * sqrt H) +
             &4 / &3 * (inv a1 + inv a2) * lam * om / H) / &2` THEN
  MP_TAC(SPECL [`lam:real`; `H:real`; `&L`; `om:real`; `th:real`;
                `a1:real`; `a2:real`] LAURENT_PA_K_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * H <= &3 * lam * sqrt k * &L` ASSUME_TAC THENL
   [MATCH_MP_TAC LAURENT_PA_Y_LOWER THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`lam:real`; `H:real`; `&L`; `a1:real`; `a2:real`; `k:real`]
    LAURENT_PA_KBIG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC `k * &L * a1 * a2` REAL_NUM_FLOOR) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `&1 <= k * &L * a1 * a2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &n` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`&1 <= k * &L * a1 * a2`; `k * &L * a1 * a2 < &n + &1`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= &n /\ &0 <= &n /\ &0 <= sqrt(&n) /\ sqrt(&n) pow 2 = &n /\
    &0 <= &L * a2 / a1 /\ &0 <= &L * a1 / a2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_POS] THEN
    SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_POS] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `sqrt(&L * a2 / a1)` REAL_NUM_FLOOR) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `sqrt(&L * a1 / a2)` REAL_NUM_FLOOR) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `sqrt(&n) * sqrt(&L * a2 / a1)` REAL_NUM_FLOOR) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `sqrt(&n) * sqrt(&L * a1 / a2)` REAL_NUM_FLOOR) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `k * &L * a2 * a1 < &n + &1 /\ &n <= k * &L * a2 * a1 /\
                lam pow 2 <= a2 * a1 /\ k * &L * a1 * a2 <= &n + &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`k * &L * a1 * a2 < &n + &1`; `&n <= k * &L * a1 * a2`;
      `lam pow 2 <= a1 * a2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= r2 /\ 1 <= s2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`&n`; `&L`; `a1:real`; `a2:real`; `k:real`]
      LAURENT_PA_R2_POS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`&n`; `&L`; `a2:real`; `a1:real`; `k:real`]
      LAURENT_PA_R2_POS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    REWRITE_TAC[ARITH_RULE `1 <= r <=> 0 < r`; GSYM REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`&1 <= sqrt(&n) * sqrt(&L * a2 / a1)`;
        `sqrt(&n) * sqrt(&L * a2 / a1) < &r2 + &1`] THEN
      REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`&1 <= sqrt(&n) * sqrt(&L * a1 / a2)`;
        `sqrt(&n) * sqrt(&L * a1 / a2) < &s2 + &1`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&L`; `a1:real`; `a2:real`] LAURENT_PA_SQRT_PROD) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `&0 < sqrt(&L) * sqrt(a1 * a2) /\ &0 <= sqrt(&L) * sqrt(a1 * a2) /\
    &0 < lam * (&L - H) /\ &9 <= &L /\ &4 <= lam * sqrt k * &L /\
    &0 <= &L * lam /\ &0 <= a1 * a2 /\ &0 <= lam /\
    &0 <= &186 / &100 * a1 * a2 /\ &0 <= a1 * a2 / &2 /\
    &0 < &r1 + &r2 + &1 /\ &0 < &s1 + &s2 + &1 /\
    &n + &1 = sqrt(&n) pow 2 + &1 /\
    (&r1 + &r2 + &1) - &1 <= (&1 + sqrt(&n)) * sqrt(&L * a2 / a1) /\
    (&s1 + &s2 + &1) - &1 <= (&1 + sqrt(&n)) * sqrt(&L * a1 / a2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < a1 * a2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt(&L) * sqrt(a1 * a2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < lam * (&L - H)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `H < &L` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &L * lam` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`&0 < sqrt(&L) * sqrt(a1 * a2)`; `&12 <= &L`; `&23 / &4 <= H`;
      `&4 * H <= &3 * lam * sqrt k * &L`; `&0 < a1 * a2`; `&0 < lam`;
      `&r1 <= sqrt(&L * a2 / a1)`; `&r2 <= sqrt(&n) * sqrt(&L * a2 / a1)`;
      `&s1 <= sqrt(&L * a1 / a2)`; `&s2 <= sqrt(&n) * sqrt(&L * a1 / a2)`] THEN
    MP_TAC(SPEC `r1:num` REAL_POS) THEN MP_TAC(SPEC `r2:num` REAL_POS) THEN
    MP_TAC(SPEC `s1:num` REAL_POS) THEN MP_TAC(SPEC `s2:num` REAL_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Z` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= Z * H` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * sqrt k * &L` THEN
      CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_POS] THEN TRY(MATCH_MP_TAC SQRT_POS_LE) THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
      MATCH_MP_TAC(CONJUNCT2 REAL_LE_MUL_EQ) THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lam * k * &L pow 2 <= inv(lam pow 3) * Z pow 2 * (lam * H) pow 2 /\
    sqrt k * &L pow 2 <= (Z * sqrt(om * th) / lam pow 3) * (lam * H) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LAURENT_PA_KL_C THEN REWRITE_TAC[REAL_POS] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC LAURENT_PA_KL_CP THEN REWRITE_TAC[REAL_POS] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`lam:real`; `Z:real`; `om:real`; `th:real`]
    LAURENT_PA_CP_EQ) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC]
 THEN
  MAP_EVERY EXISTS_TAC
   [`n + 1`; `L:num`; `r1 + 1`; `s1 + 1`; `r2 + 1`; `s2 + 1`; `k:real`] THEN
  REWRITE_TAC[ARITH_RULE `((r1 + 1) + (r2 + 1)) - 1 = r1 + r2 + 1`;
              ARITH_RULE `(n + 1) - 1 = n`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              REAL_ARITH `(x + &1) - &1 = x`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `1 <= n` THEN ARITH_TAC;
    UNDISCH_TAC `12 <= L` THEN ARITH_TAC;
    ARITH_TAC;
    ARITH_TAC;
    ARITH_TAC;
    ARITH_TAC;
    UNDISCH_TAC `1 <= r2` THEN ARITH_TAC;
    UNDISCH_TAC `1 <= s2` THEN ARITH_TAC;
    SUBGOAL_THEN `&L < (&r1 + &1) * (&s1 + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `sqrt(&L * a2 / a1) * sqrt(&L * a1 / a2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC LAURENT_PA_GRID THEN REWRITE_TAC[REAL_POS] THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_LT_MUL2 THEN REPEAT CONJ_TAC THEN
        TRY(MATCH_MP_TAC SQRT_POS_LE) THEN FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
      ARITH_TAC];
    SUBGOAL_THEN `&n * &L < (&r2 + &1) * (&s2 + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(sqrt(&n) * sqrt(&L * a2 / a1)) *
                  (sqrt(&n) * sqrt(&L * a1 / a2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        MP_TAC(SPECL [`&L`; `a1:real`; `a2:real`] LAURENT_PA_GRID) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[REAL_POS] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `sqrt(&n) pow 2 = &n` THEN CONV_TAC REAL_RING;
        MATCH_MP_TAC REAL_LT_MUL2 THEN REPEAT CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
            MATCH_MP_TAC SQRT_POS_LE) THEN
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
      ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(SPECL [`&L`; `a1:real`; `a2:real`; `sqrt(&n)`; `&n + &1`;
                  `&r1 + &r2 + &1`; `&s1 + &s2 + &1`;
                  `sqrt(&L * a2 / a1)`; `sqrt(&L * a1 / a2)`;
                  `sqrt(&L) * sqrt(a1 * a2)`] LAURENT_PA_LMN16) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&L`; `a1:real`; `a2:real`; `&n`; `k:real`;
                  `lam * (&L - H)`; `sqrt(&L) * sqrt(a1 * a2)`]
      LAURENT_PA_PHI) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN
     `&n * (&L * lam) <= (k * &L * a1 * a2) * (&L * lam) /\
      (lam * k * &L pow 2) * (a1 * a2) <=
      (inv(lam pow 3) * Z pow 2 * (lam * H) pow 2) * (a1 * a2) /\
      &L * lam <= (sqrt(om * th) * H) * lam`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC];
    MP_TAC(SPECL [`lam:real`; `H:real`; `&L`; `a1:real`; `a2:real`; `k:real`;
                  `&n`; `&r1 + &r2 + &1`] LAURENT_PA_LR) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(sqrt k * &L pow 2) * (&186 / &100 * a1 * a2) <=
      ((Z * sqrt(om * th) / lam pow 3) * (lam * H) pow 2) *
      (&186 / &100 * a1 * a2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC];
    MP_TAC(SPECL [`lam:real`; `H:real`; `&L`; `a2:real`; `a1:real`; `k:real`;
                  `&n`; `&s1 + &s2 + &1`] LAURENT_PA_LR) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(sqrt k * &L pow 2) * (&186 / &100 * a1 * a2) <=
      ((Z * sqrt(om * th) / lam pow 3) * (lam * H) pow 2) *
      (&186 / &100 * a1 * a2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC];
    MP_TAC(SPECL [`lam:real`; `H:real`; `&L`; `a1:real`; `a2:real`; `k:real`;
                  `&n`; `&r1 + &r2 + &1`; `&s1 + &s2 + &1`] LAURENT_PA_RA) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(lam * k * &L pow 2) * (a1 * a2 / &2) <=
      (inv(lam pow 3) * Z pow 2 * (lam * H) pow 2) * (a1 * a2 / &2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC]]
);;

prioritize_num();;
