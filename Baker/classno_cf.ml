(* ========================================================================= *)
(* Enclosures of log eps_21 and log eps_33 and the two continued-fraction    *)
(* stages of the endgame.                                                    *)
(*                                                                           *)
(* Purpose: l1 = log eps and l2 = log eps1 with eps = (5 + sqrt 21) / 2 and  *)
(* eps1 = 23 + 4 sqrt 33, the fundamental units of Q(sqrt 21) and            *)
(* Q(sqrt 33), are enclosed to within 1e-28 (CLASSNO_CF_LOG_EPS21_BOUNDS,    *)
(* CLASSNO_CF_LOG_EPS33_BOUNDS), and the convergents p17/q17, p18/q18 and    *)
(* p8/q8, p9/q9 of theta = l2 / l1 = 2.44330503934277137096... give lower    *)
(* bounds for abs(b2 l2 - b1 l1): 2.329e-11 l1 for                           *)
(* 1 <= b2 < q18 = 40577071451 (CLASSNO_CF_STAGE1) and 6.84e-6 l1 for        *)
(* 1 <= b2 < q9 = 130770 (CLASSNO_CF_STAGE2). This is the continued-fraction *)
(* step that reduces the bound for d to the range of the witness search      *)
(* (Baker and Wustholz, Logarithmic Forms and Diophantine Geometry,          *)
(* sec. 3.1: computing the continued fraction for log alpha1 / log alpha2;   *)
(* the Baker-Davenport reduction as in the Steiner proof of                  *)
(* Baker/steiner.ml).                                                        *)
(*                                                                           *)
(* Method: (1) the real Taylor bound for log(1 - x) with a radius r          *)
(* (CLASSNO_CF_LOG_TAYLOR of Baker/steiner.ml), and the unimodular lemma     *)
(* (best approximation of the second kind, without continued fractions): if  *)
(* p s - r q = +-1, 0 < q, and the linear forms q x - p y and s x - r y have *)
(* opposite signs, then abs(q x - p y) <= abs(b x - a y) for all integers a  *)
(* and 0 < b < s (CLASSNO_CF_UNIMODULAR). (2) Enclosures of width below      *)
(* 2e-30 of log(16/15), log(25/24), log(81/80) (shared with the Steiner      *)
(* theorem, Baker/steiner.ml) and log(576/575) by the Taylor series, and     *)
(* log 5 = 16 a + 12 b + 7 c, log 46 = 39 a + 27 b + 17 c - d.               *)
(* (3) eps = 5 (1 - z1), z1 = (5 - sqrt 21) / 10, with z1^2 = z1 - 1/25, and *)
(* eps1 = 46 (1 - z2), z2 = (23 - 4 sqrt 33) / 46, with z2^2 = z2 - 1/2116:  *)
(* the Taylor polynomials reduce to A + B z. (4) The four convergent         *)
(* inequalities and the two stages.                                          *)
(*                                                                           *)
(* Main results: CLASSNO_CF_STAGE1, CLASSNO_CF_STAGE2,                       *)
(* CLASSNO_CF_LOG_EPS21_BOUNDS, CLASSNO_CF_LOG_EPS33_BOUNDS,                 *)
(* CLASSNO_CF_UNIMODULAR; helper names CLASSNO_CF_*.                         *)
(*                                                                           *)
(* Uses: Baker/steiner.ml (CLASSNO_CF_LOG_TAYLOR,                            *)
(* CLASSNO_CF_LOG_16_15_BOUNDS, CLASSNO_CF_LOG_25_24_BOUNDS,                 *)
(* CLASSNO_CF_LOG_81_80_BOUNDS).                                             *)
(* ========================================================================= *)

needs "Baker/steiner.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Tools.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* If 0 < b < s and b = u q + v s with q > 0, then u <> 0 and u v <= 0.      *)

let CLASSNO_CF_INT_SIGNS = prove
 (`!q s b u v:int.
        &0 < q /\ &0 < b /\ b < s /\ b = u * q + v * s
        ==> &1 <= abs u /\ u * v <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&1 <= u:int /\ v:int <= &0) \/ (u <= -- &1 /\ &1 <= v)`
  STRIP_ASSUME_TAC THENL
   [DISJ_CASES_TAC(INT_ARITH `v:int <= &0 \/ &1 <= v`) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`--v:int`; `s:int`] INT_LE_MUL) THEN
      MP_TAC(SPECL [`--u:int`; `q:int`] INT_LE_MUL) THEN
      MAP_EVERY UNDISCH_TAC
       [`b:int = u * q + v * s`; `&0 < b:int`; `b:int < s`; `&0 < q:int`;
        `v:int <= &0`] THEN
      INT_ARITH_TAC;
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`v - &1:int`; `s:int`] INT_LE_MUL) THEN
      MP_TAC(SPECL [`u:int`; `q:int`] INT_LE_MUL) THEN
      MAP_EVERY UNDISCH_TAC
       [`b:int = u * q + v * s`; `&0 < b:int`; `b:int < s`; `&0 < q:int`;
        `&1 <= v:int`] THEN
      INT_ARITH_TAC];
    MP_TAC(SPECL [`u:int`; `--v:int`] INT_LE_MUL) THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= u:int`; `v:int <= &0`] THEN INT_ARITH_TAC;
    MP_TAC(SPECL [`--u:int`; `v:int`] INT_LE_MUL) THEN
    MAP_EVERY UNDISCH_TAC [`u:int <= -- &1`; `&1 <= v:int`] THEN
    INT_ARITH_TAC]);;

let CLASSNO_CF_ABS_ADD_SAME_SIGN = prove
 (`!x y:real. &0 <= x * y ==> abs x <= abs(x + y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN
  UNDISCH_TAC `&0 <= x * y` THEN REAL_ARITH_TAC);;

(* The unimodular lemma. Write (a,b) = u (p,q) + v (r,s) (determinant +-1);  *)
(* then u <> 0 and u v <= 0, so the two summands of                          *)
(* b x - a y = u (q x - p y) + v (s x - r y) have the same sign.             *)

let CLASSNO_CF_UNIMODULAR = prove
 (`!x y:real p q r s a b:int.
        abs(p * s - r * q) = &1 /\ &0 < q /\ &0 < b /\ b < s /\
        (real_of_int q * x - real_of_int p * y) *
        (real_of_int s * x - real_of_int r * y) <= &0
        ==> abs(real_of_int q * x - real_of_int p * y)
            <= abs(real_of_int b * x - real_of_int a * y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?u v:int. a = u * p + v * r /\ b = u * q + v * s`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`(p * s - r * q) * (a * s - r * b):int`;
      `(p * s - r * q) * (p * b - a * q):int`] THEN
    SUBGOAL_THEN `(p * s - r * q) * (p * s - r * q) = &1:int` MP_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
       (INT_ARITH `abs(x:int) = &1 ==> x = &1 \/ x = -- &1`)) THEN
      CONV_TAC INT_REDUCE_CONV;
      DISCH_TAC THEN CONJ_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC INT_RING];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q:int`; `s:int`; `b:int`; `u:int`; `v:int`]
    CLASSNO_CF_INT_SIGNS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[int_le; int_of_num_th; int_abs_th; int_mul_th] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `real_of_int b * x - real_of_int a * y =
    real_of_int u * (real_of_int q * x - real_of_int p * y) +
    real_of_int v * (real_of_int s * x - real_of_int r * y)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`a:int = u * p + v * r`; `b:int = u * q + v * s`] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[int_add_th; int_mul_th] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `abs(real_of_int u * (real_of_int q * x - real_of_int p * y))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= (u - &1) * l ==> l <= u * l`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    UNDISCH_TAC `&1 <= abs(real_of_int u)` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CLASSNO_CF_ABS_ADD_SAME_SIGN THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= --(u * v) * --(l * m) ==> &0 <= (u * l) * (v * m)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    MAP_EVERY UNDISCH_TAC
     [`real_of_int u * real_of_int v <= &0`;
      `(real_of_int q * x - real_of_int p * y) *
       (real_of_int s * x - real_of_int r * y) <= &0`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 2. The enclosure of log(576/575) by the Taylor series of log(1 - 1/N)    *)
(* (10 terms; width < 2e-30; those of log(16/15), log(25/24), log(81/80) are *)
(* in Baker/steiner.ml), and log 5, log 46 in terms of them.                 *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CF_LOG_576_575_BOUNDS = prove
 (`&173761989854079928561170433106 / &10 pow 32 <= log(&576 / &575) /\
   log(&576 / &575) <= &173761989854079928561170433194 / &10 pow 32`,
  MP_TAC(SPEC `&575 / &576` LOG_INV) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`10`; `&1 / &576`; `&1 / &576`] CLASSNO_CF_LOG_TAYLOR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* 5 = (16/15)^16 (25/24)^12 (81/80)^7 and                                   *)
(* 46 (576/575) = (16/15)^39 (25/24)^27 (81/80)^17.                          *)

let CLASSNO_CF_LOG_5_DECOMP = prove
 (`log(&5) =
   &16 * log(&16 / &15) + &12 * log(&25 / &24) + &7 * log(&81 / &80)`,
  SIMP_TAC[GSYM LOG_POW; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM LOG_MUL; REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let CLASSNO_CF_LOG_46_DECOMP = prove
 (`log(&46) =
   (&39 * log(&16 / &15) + &27 * log(&25 / &24) + &17 * log(&81 / &80)) -
   log(&576 / &575)`,
  REWRITE_TAC[REAL_ARITH `(x:real) = y - z <=> x + z = y`] THEN
  SIMP_TAC[GSYM LOG_POW; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM LOG_MUL; REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* 3. The units. sqrt 21 and sqrt 33 to 10^-32; the Taylor polynomials of    *)
(* log(1 - z) reduced modulo the quadratic equations of z1 and z2.           *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CF_SQRT21_BOUNDS = prove
 (`&458257569495584000658804719372800 / &10 pow 32 <= sqrt(&21) /\
   sqrt(&21) <= &458257569495584000658804719372801 / &10 pow 32`,
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let CLASSNO_CF_SQRT33_BOUNDS = prove
 (`&574456264653802865985061146821892 / &10 pow 32 <= sqrt(&33) /\
   sqrt(&33) <= &574456264653802865985061146821893 / &10 pow 32`,
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let CLASSNO_CF_TAYLOR_Z21 = prove
 (`!z. z pow 2 = z - &1 / &25
       ==> sum(1..21) (\k. z pow k / &k) =
           --(&57834202950088634383 / &652965545654296875000) +
           &221538261213433856069 / &70478820800781250000 * z`,
  GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let CLASSNO_CF_TAYLOR_Z33 = prove
 (`!z. z pow 2 = z - &1 / &2116
       ==> sum(1..9) (\k. z pow k / &k) =
           --(&43633050166861 / &50519982824478720) +
           &1983552921032253 / &701666428117760 * z`,
  GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let CLASSNO_CF_LOG_Z21_BOUNDS = prove
 (`--(&4263867546168929593670247064623) / &10 pow 32
   <= log(&1 - (&5 - sqrt(&21)) / &10) /\
   log(&1 - (&5 - sqrt(&21)) / &10)
   <= --(&4263867546168929593670247064514) / &10 pow 32`,
  MP_TAC CLASSNO_CF_SQRT21_BOUNDS THEN STRIP_TAC THEN
  MP_TAC(SPECL [`21`; `(&5 - sqrt(&21)) / &10`; `&21 / &500`]
    CLASSNO_CF_LOG_TAYLOR) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&458257569495584000658804719372800 / &10 pow 32 <= sqrt(&21)`;
      `sqrt(&21) <= &458257569495584000658804719372801 / &10 pow 32`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..21) (\k. ((&5 - sqrt(&21)) / &10) pow k / &k) =
    --(&57834202950088634383 / &652965545654296875000) +
    &221538261213433856069 / &70478820800781250000 *
    ((&5 - sqrt(&21)) / &10)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CLASSNO_CF_TAYLOR_Z21 THEN
    MP_TAC(SPEC `&21` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY UNDISCH_TAC
   [`&458257569495584000658804719372800 / &10 pow 32 <= sqrt(&21)`;
    `sqrt(&21) <= &458257569495584000658804719372801 / &10 pow 32`] THEN
  REAL_ARITH_TAC);;

let CLASSNO_CF_LOG_Z33_BOUNDS = prove
 (`--(&47292515599398526062119451107) / &10 pow 32
   <= log(&1 - (&23 - &4 * sqrt(&33)) / &46) /\
   log(&1 - (&23 - &4 * sqrt(&33)) / &46)
   <= --(&47292515599398526062119451105) / &10 pow 32`,
  MP_TAC CLASSNO_CF_SQRT33_BOUNDS THEN STRIP_TAC THEN
  MP_TAC(SPECL [`9`; `(&23 - &4 * sqrt(&33)) / &46`; `&1 / &2000`]
    CLASSNO_CF_LOG_TAYLOR) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&574456264653802865985061146821892 / &10 pow 32 <= sqrt(&33)`;
      `sqrt(&33) <= &574456264653802865985061146821893 / &10 pow 32`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..9) (\k. ((&23 - &4 * sqrt(&33)) / &46) pow k / &k) =
    --(&43633050166861 / &50519982824478720) +
    &1983552921032253 / &701666428117760 * ((&23 - &4 * sqrt(&33)) / &46)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CLASSNO_CF_TAYLOR_Z33 THEN
    MP_TAC(SPEC `&33` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY UNDISCH_TAC
   [`&574456264653802865985061146821892 / &10 pow 32 <= sqrt(&33)`;
    `sqrt(&33) <= &574456264653802865985061146821893 / &10 pow 32`] THEN
  REAL_ARITH_TAC);;

(* eps = 5 (1 - z1) and eps1 = 46 (1 - z2).                                  *)

let CLASSNO_CF_LOG_EPS21_DECOMP = prove
 (`log((&5 + sqrt(&21)) / &2) =
   log(&5) + log(&1 - (&5 - sqrt(&21)) / &10)`,
  SUBGOAL_THEN `(&5 + sqrt(&21)) / &2 = &5 * (&1 - (&5 - sqrt(&21)) / &10)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LOG_MUL THEN
  MP_TAC(SPEC `&21` SQRT_POS_LE) THEN REWRITE_TAC[REAL_POS] THEN
  REAL_ARITH_TAC);;

let CLASSNO_CF_LOG_EPS33_DECOMP = prove
 (`log(&23 + &4 * sqrt(&33)) =
   log(&46) + log(&1 - (&23 - &4 * sqrt(&33)) / &46)`,
  SUBGOAL_THEN
   `&23 + &4 * sqrt(&33) = &46 * (&1 - (&23 - &4 * sqrt(&33)) / &46)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LOG_MUL THEN
  MP_TAC(SPEC `&33` SQRT_POS_LE) THEN REWRITE_TAC[REAL_POS] THEN
  REAL_ARITH_TAC);;

(* The enclosures of l1 = log eps and l2 = log eps1 (widths < 1e-28).        *)

let CLASSNO_CF_LOG_EPS21_BOUNDS = prove
 (`&1566799236972411078664056862561 / &10 pow 30
   <= log((&5 + sqrt(&21)) / &2) /\
   log((&5 + sqrt(&21)) / &2)
   <= &1566799236972411078664056862599 / &10 pow 30`,
  REWRITE_TAC[CLASSNO_CF_LOG_EPS21_DECOMP; CLASSNO_CF_LOG_5_DECOMP] THEN
  MP_TAC CLASSNO_CF_LOG_16_15_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_25_24_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_81_80_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_Z21_BOUNDS THEN
  REAL_ARITH_TAC);;

let CLASSNO_CF_LOG_EPS33_BOUNDS = prove
 (`&3828168471333101014963363758711 / &10 pow 30
   <= log(&23 + &4 * sqrt(&33)) /\
   log(&23 + &4 * sqrt(&33))
   <= &3828168471333101014963363758800 / &10 pow 30`,
  REWRITE_TAC[CLASSNO_CF_LOG_EPS33_DECOMP; CLASSNO_CF_LOG_46_DECOMP] THEN
  MP_TAC CLASSNO_CF_LOG_16_15_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_25_24_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_81_80_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_576_575_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_Z33_BOUNDS THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. The convergents p17/q17 = 20275614827/8298437772 (above theta),        *)
(* p18/q18 = 99142163158/40577071451 (below), p17 q18 - p18 q17 = 1, and     *)
(* p8/q8 = 49797/20381 (below), p9/q9 = 319511/130770 (above),               *)
(* p8 q9 - p9 q8 = -1; the two stages.                                       *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_CF_CONVERGENTS = prove
 (`&2329 / &10 pow 14 * log((&5 + sqrt(&21)) / &2)
   <= &20275614827 * log((&5 + sqrt(&21)) / &2) -
      &8298437772 * log(&23 + &4 * sqrt(&33)) /\
   &0 < &40577071451 * log(&23 + &4 * sqrt(&33)) -
        &99142163158 * log((&5 + sqrt(&21)) / &2) /\
   &684 / &10 pow 8 * log((&5 + sqrt(&21)) / &2)
   <= &20381 * log(&23 + &4 * sqrt(&33)) -
      &49797 * log((&5 + sqrt(&21)) / &2) /\
   &0 < &319511 * log((&5 + sqrt(&21)) / &2) -
        &130770 * log(&23 + &4 * sqrt(&33))`,
  MP_TAC CLASSNO_CF_LOG_EPS21_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_EPS33_BOUNDS THEN
  REAL_ARITH_TAC);;

let CLASSNO_CF_STAGE1 = prove
 (`!b1 b2. 1 <= b2 /\ b2 < 40577071451
          ==> &2329 / &10 pow 14 * log((&5 + sqrt(&21)) / &2)
              <= abs(&b2 * log(&23 + &4 * sqrt(&33)) -
                     &b1 * log((&5 + sqrt(&21)) / &2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`log(&23 + &4 * sqrt(&33))`; `log((&5 + sqrt(&21)) / &2)`;
    `&20275614827:int`; `&8298437772:int`; `&99142163158:int`;
    `&40577071451:int`; `&b1:int`; `&b2:int`] CLASSNO_CF_UNIMODULAR) THEN
  REWRITE_TAC[int_of_num_th; INT_OF_NUM_LT] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[ARITH] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `1 <= b2` THEN ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 <= --x * y ==> x * y <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      MP_TAC CLASSNO_CF_CONVERGENTS THEN
      MP_TAC CLASSNO_CF_LOG_EPS21_BOUNDS THEN REAL_ARITH_TAC];
    MP_TAC CLASSNO_CF_CONVERGENTS THEN REAL_ARITH_TAC]);;

let CLASSNO_CF_STAGE2 = prove
 (`!b1 b2. 1 <= b2 /\ b2 < 130770
          ==> &684 / &10 pow 8 * log((&5 + sqrt(&21)) / &2)
              <= abs(&b2 * log(&23 + &4 * sqrt(&33)) -
                     &b1 * log((&5 + sqrt(&21)) / &2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`log(&23 + &4 * sqrt(&33))`; `log((&5 + sqrt(&21)) / &2)`;
    `&49797:int`; `&20381:int`; `&319511:int`;
    `&130770:int`; `&b1:int`; `&b2:int`] CLASSNO_CF_UNIMODULAR) THEN
  REWRITE_TAC[int_of_num_th; INT_OF_NUM_LT] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[ARITH] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `1 <= b2` THEN ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x * --y ==> x * y <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      MP_TAC CLASSNO_CF_CONVERGENTS THEN
      MP_TAC CLASSNO_CF_LOG_EPS21_BOUNDS THEN REAL_ARITH_TAC];
    MP_TAC CLASSNO_CF_CONVERGENTS THEN REAL_ARITH_TAC]);;
