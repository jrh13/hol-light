(* ========================================================================= *)
(* Zero-free regions for L(s,c) in a rectangle, uniform in the modulus.      *)
(*                                                                           *)
(* ZF_RECT: let c be nonprincipal mod d, T >= 1, 0 < kap <= 1 with           *)
(* kap <= L(1,c) if c is real, and Lg = 1 + log(16 d (T + 4)).  Then for     *)
(*   1 - kap / (10^20 Lg^12) <= Re s <= 2,  |Im s| <= T:                     *)
(*     L(s,c) <> 0  and  |L'(s,c) / L(s,c)| <= 10^20 Lg^12 / kap^2.          *)
(*                                                                           *)
(* Method.  ZF_LINE combines LFUN_LOWER_ABSTRACT with LFUN_DERIV_BOUND       *)
(* (M1 = 24 (1 + log N)^2): a bound M2 for |L(y + 2it,c^2)| on 1 < y <= 2    *)
(* gives L <> 0 and a bound for L'/L on the line Im s = t for                *)
(* 1 - 1/(2048 M1^4 M2) <= Re s <= 2.                                        *)
(*  * c^2 nonprincipal: M2 = 12 Lg by LFUN_BOUND (ZF_COMPLEX_M2,             *)
(*    ZF_RECT_COMPLEX).                                                      *)
(*  * c^2 principal, i.e. c real (CHARACTER_SQUARE_PRINCIPAL_REAL): for      *)
(*    |t| >= ta, M2 = (1 + log d) (3 + log N + 1/(2 ta)) by                  *)
(*    PRINCIPAL_LFUN_BOUND and ZETA_LINE_BOUND (ZF_REAL_M2); for             *)
(*    Re s >= 1 + ta, ZF_RIGHT (DSERIES_NEG_LOG_DERIV, LAMBDA_SERIES_BOUND); *)
(*    near s = 1 the disc ZF_DISC of radius kap / (48 Lg^2) around 1 (from   *)
(*    L(1,c) >= kap and the mean value theorem with LFUN_DERIV_BOUND); here  *)
(*    ta = kap / (96 Lg^2) (ZF_RECT_REAL).                                   *)
(* ========================================================================= *)

needs "Sieve/lfun.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* A zero-free segment on a horizontal line.                                 *)
(* ------------------------------------------------------------------------- *)

let ZF_LINE = prove
 (`!d c N M2 s.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ 16 <= N /\
     &d * (abs(Im s) + &4) <= &N /\ &1 <= M2 /\
     (!y. &1 < y /\ y <= &2
          ==> norm(dseries (\n. c n pow 2) (Cx y + Cx(&2) * ii * Cx(Im s)))
              <= M2) /\
     &1 - inv(&2048 * (&24 * (&1 + log(&N)) pow 2) pow 4 * M2) <= Re s /\
     Re s <= &2
     ==> ~(dseries c s = Cx(&0)) /\
         norm(complex_derivative (dseries c) s / dseries c s) <=
         &1024 * (&24 * (&1 + log(&N)) pow 2) pow 4 * M2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `M1 = &24 * (&1 + log(&N)) pow 2` THEN
  SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= M1 /\ &2 * log(&N) <= &2048 * M1 pow 4 * M2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 + log(&N) <= M1` ASSUME_TAC THENL
     [EXPAND_TAC "M1" THEN
      MATCH_MP_TAC(REAL_ARITH
       `&1 <= x /\ x <= x pow 2 ==> x <= &24 * x pow 2`) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * x <= x * x ==> x <= x * x`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2048 * M1 pow 4 * &1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ x <= M ==> &2 * x <= &2048 * M`) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M1:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `eta = inv(&2048 * M1 pow 4 * M2)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= inv(&2 * log(&N))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(complex_derivative (dseries c) s) <= M1` ASSUME_TAC THENL
   [EXPAND_TAC "M1" THEN MATCH_MP_TAC LFUN_DERIV_BOUND THEN
    EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `Im s`; `M1:real`; `M2:real`;
                `Re s`] LFUN_LOWER_ABSTRACT) THEN
  ASM_REWRITE_TAC[GSYM COMPLEX_EXPAND] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN EXPAND_TAC "M1" THEN
    MATCH_MP_TAC LFUN_DERIV_BOUND THEN
    EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * eta * M1` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&2 * eta * M1 <= norm(dseries c s)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV] THEN
  SUBGOAL_THEN `&0 < norm(dseries c s)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1024 * M1 pow 4 * M2) * (&2 * eta * M1)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(&1024 * M1 pow 4 * M2) * (&2 * eta * M1) = M1`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `~(&2048 * M1 pow 4 * M2 = &0)` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The bound M2 for L(s,c^2), and the region right of Re s = 1.              *)
(* ------------------------------------------------------------------------- *)

let CHARACTER_SQUARE = prove
 (`!d c. dirichlet_character d c ==> dirichlet_character d (\n. c n pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_POW_2] THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_GROUPMUL THEN ASM_REWRITE_TAC[]);;

let RE_IM_LINE2 = prove
 (`!y t. Re(Cx y + Cx(&2) * ii * Cx t) = y /\
         Im(Cx y + Cx(&2) * ii * Cx t) = &2 * t`,
  REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX;
              RE_MUL_II; IM_MUL_II] THEN REAL_ARITH_TAC);;

let ZF_COMPLEX_M2 = prove
 (`!d c N t y. dirichlet_character d c /\ ~((\n. c n pow 2) = chi_0 d) /\
               &d * (&2 * abs t + &3) <= &N /\ &1 < y
               ==> norm(dseries (\n. c n pow 2) (Cx y + Cx(&2) * ii * Cx t))
                   <= &12 * (&1 + log(&N))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CHARACTER_SQUARE) THEN
  MP_TAC(SPECL [`d:num`; `\n. (c:num->complex) n pow 2`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC LFUN_BOUND THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[RE_IM_LINE2; REAL_ABS_MUL; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `&1 <= &d` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&N)` MP_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN
    SUBGOAL_THEN `&0 <= &d * &2 * abs t` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_INV) THEN ASM_REAL_ARITH_TAC);;

let REAL_CHARACTER_SQUARE = prove
 (`!d c. dirichlet_character d c /\ (!n. real(c n))
         ==> (\n. c n pow 2) = chi_0 d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; chi_0] THEN
  X_GEN_TAC `n:num` THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `n:num`]
    DIRICHLET_CHARACTER_EQ_0) THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_REAL_CASES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CX_INJ; GSYM CX_NEG; REAL_OF_NUM_EQ; ARITH_EQ;
              REAL_ARITH `~(--(&1) = &0)`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING);;

let ZF_REAL_M2 = prove
 (`!d c N t y ta.
     dirichlet_character d c /\ (!n. real(c n)) /\ 1 <= d /\ 1 <= N /\
     &0 < ta /\ ta <= abs t /\ &2 * abs t + &2 <= &N /\
     &1 < y /\ y <= &2
     ==> norm(dseries (\n. c n pow 2) (Cx y + Cx(&2) * ii * Cx t)) <=
         (&1 + log(&d)) * (&3 + log(&N) + inv(&2 * ta))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] REAL_CHARACTER_SQUARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + log(&d)) * norm(zeta(Cx y + Cx(&2) * ii * Cx t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRINCIPAL_LFUN_BOUND THEN ASM_REWRITE_TAC[RE_IM_LINE2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 + log(&N) + inv(abs(Im(Cx y + Cx(&2) * ii * Cx t)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ZETA_LINE_BOUND THEN ASM_REWRITE_TAC[RE_IM_LINE2] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs y + abs(&2 * t)` THEN
      CONJ_TAC THENL
       [MP_TAC(SPEC `Cx y + Cx(&2) * ii * Cx t` COMPLEX_NORM_LE_RE_IM) THEN
        REWRITE_TAC[RE_IM_LINE2];
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[RE_IM_LINE2; REAL_ADD_ASSOC; REAL_LE_LADD] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

let ZF_RIGHT = prove
 (`!d c s ta.
     dirichlet_character d c /\ &0 < ta /\ ta <= &1 /\
     &1 + ta <= Re s /\ Re s <= &2
     ==> ~(dseries c s = Cx(&0)) /\
         norm(complex_derivative (dseries c) s / dseries c s) <=
         &12 / ta pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DIRICHLET_CHARACTER_DSERIES_HYPS)
    THEN
  SUBGOAL_THEN `&1 < Re s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DSERIES_NZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:num->complex`; `s:complex`] DSERIES_NEG_LOG_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LNEG] THEN
  REWRITE_TAC[GSYM complex_div] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[NORM_NEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC DSERIES_NORM_BOUND THEN
  MAP_EVERY EXISTS_TAC [`&1`; `1`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_POW_1;
                REAL_MUL_LID] THEN
    SUBGOAL_THEN `abs(mangoldt n) <= log(&n)` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `abs x <= y <=> --y <= x /\ x <= y`] THEN
      MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
      MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= log(&n)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&n) * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS;
      NORM_POS_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / (Re s - &1) * exp((Re s - &1) / &2) *
              (&1 + &2 / (Re s - &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LAMBDA_SERIES_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u = Re s - &1` THEN
  SUBGOAL_THEN `ta <= u /\ u <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 / u <= &2 / ta` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(u / &2) <= &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `u / &2` REAL_EXP_BOUND_LEMMA) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / ta /\ &1 <= &1 / ta` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &2`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / ta * &2 * (&3 * (&1 / ta))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_POS_LE]; ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `&2 / u <= &2 / ta /\ &1 <= &1 / ta /\
          &2 / ta = &2 * (&1 / ta:real)
          ==> &1 + &2 / u <= &3 * (&1 / ta)`) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    SUBGOAL_THEN `~(ta = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

(* ------------------------------------------------------------------------- *)
(* A zero-free disc around s = 1 for real characters.                        *)
(* ------------------------------------------------------------------------- *)

let ZF_DISC = prove
 (`!d c N kap s.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ 16 <= N /\
     &d * &5 <= &N /\ &0 < kap /\ kap <= &1 /\
     kap <= norm(dseries c (Cx(&1))) /\
     norm(s - Cx(&1)) <= kap / (&48 * (&1 + log(&N)) pow 2)
     ==> ~(dseries c s = Cx(&0)) /\
         norm(complex_derivative (dseries c) s / dseries c s) <=
         &48 * (&1 + log(&N)) pow 2 / kap`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `M1 = &24 * (&1 + log(&N)) pow 2` THEN
  SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + log(&N) <= (&1 + log(&N)) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * x <= x * x ==> x <= x * x`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `rho = kap / (&2 * M1)` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= &1 / &2 /\ rho <= inv(&2 * log(&N)) /\
                M1 * rho = kap / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN
    SUBGOAL_THEN `&2 * log(&N) <= &2 * M1 /\ &2 <= &2 * M1` STRIP_ASSUME_TAC
    THENL [EXPAND_TAC "M1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&2 <= x ==> &0 < x`] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * M1)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `~(M1 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(s - Cx(&1)) <= rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN EXPAND_TAC "M1" THEN
    UNDISCH_TAC `norm(s - Cx(&1)) <= kap / (&48 * (&1 + log(&N)) pow 2)` THEN
    REWRITE_TAC[REAL_ARITH `&2 * &24 * x = &48 * x`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN cball(Cx(&1),rho)
        ==> (dseries c has_complex_derivative
             complex_derivative (dseries c) z) (at z within cball(Cx(&1),rho))
               /\
            norm(complex_derivative (dseries c) z) <= M1`
  (LABEL_TAC "dz") THENL
   [X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
    MP_TAC(SPEC `Cx(&1) - z` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; GSYM dist] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `{s | Re s > &0}` THEN
      REWRITE_TAC[OPEN_HALFSPACE_RE_GT; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[HOLOMORPHIC_LFUN]; ALL_TAC] THEN
      REWRITE_TAC[real_gt] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "M1" THEN MATCH_MP_TAC LFUN_DERIV_BOUND THEN
      EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&d * &5` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dseries c`; `complex_derivative (dseries c)`;
                 `cball(Cx(&1),rho)`; `M1:real`]
    COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:complex`; `Cx(&1)`]) THEN
  ASM_REWRITE_TAC[IN_CBALL; DIST_REFL; dist] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `M1 * norm(s - Cx(&1)) <= kap / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M1 * rho:real` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "M1" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `kap / &2 <= norm(dseries c s)` ASSUME_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `!a b:complex x. norm(a - b) <= x /\ x <= kap / &2 /\ kap <= norm b
                      ==> kap / &2 <= norm a`) THEN
    EXISTS_TAC `dseries c (Cx(&1))` THEN
    EXISTS_TAC `M1 * norm(s - Cx(&1))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `kap / &2 <= norm(dseries c s)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV] THEN
  SUBGOAL_THEN `&0 < norm(dseries c s)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M1:real` THEN CONJ_TAC THENL
   [USE_THEN "dz" (MP_TAC o SPEC `s:complex`) THEN
    REWRITE_TAC[IN_CBALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&48 * (&1 + log(&N)) pow 2 / kap) * (kap / &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `~(kap = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "M1" THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The zero-free rectangle.                                                  *)
(* ------------------------------------------------------------------------- *)

let CHARACTER_SQUARE_PRINCIPAL_REAL = prove
 (`!d c. dirichlet_character d c /\ (\n. c n pow 2) = chi_0 d
         ==> !n. real(c n)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  REWRITE_TAC[chi_0] THEN COND_CASES_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(c:num->complex) n = Cx(&1) \/ c n = --Cx(&1)` MP_TAC THENL
     [UNDISCH_TAC `(c:num->complex) n pow 2 = Cx(&1)` THEN
      CONV_TAC COMPLEX_RING;
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_CX; REAL_NEG]];
    MP_TAC(SPECL [`d:num`; `c:num->complex`; `n:num`]
      DIRICHLET_CHARACTER_EQ_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_CX]]);;

let ZF_LG_FACTS = prove
 (`!d Tn. 2 <= d /\ 1 <= Tn
         ==> 16 <= 16 * d * (Tn + 4) /\
             &d * &5 <= &(16 * d * (Tn + 4)) /\
             &2 * &Tn + &2 <= &(16 * d * (Tn + 4)) /\
             &d * (&Tn + &4) <= &(16 * d * (Tn + 4)) /\
             &d * (&2 * &Tn + &3) <= &(16 * d * (Tn + 4)) /\
             &0 < log(&(16 * d * (Tn + 4))) /\
             &1 + log(&d) <= &1 + log(&(16 * d * (Tn + 4)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 <= 16 * d * (Tn + 4)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `16 * 1 * 1 <= x ==> 16 <= x`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&2 <= &d /\ &1 <= &Tn` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&d - &2) * &Tn` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REAL_ARITH_TAC]);;

let LG_POW_COMPARE = prove
 (`!Lg kap K m. &1 <= Lg /\ &0 < kap /\ kap <= &1 /\ &0 <= K /\
                K <= &10 pow 20 /\ m <= 12
                ==> K * Lg pow m <= &10 pow 20 * Lg pow 12 / kap pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < kap pow 2 /\ kap pow 2 <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow 20 * Lg pow 12` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
     ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= x ==> &0 <= x`]]);;

let LG_INV_COMPARE = prove
 (`!Lg kap K m. &1 <= Lg /\ &0 < kap /\ kap <= &1 /\ &0 < K /\
                K <= &10 pow 20 /\ m <= 12
                ==> kap / (&10 pow 20 * Lg pow 12) <= inv(K * Lg pow m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * inv(&10 pow 20 * Lg pow 12)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT;
      REAL_ARITH `&1 <= x ==> &0 < x`];
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE;
      REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]]);;

let ZF_RECT_COMPLEX = prove
 (`!d c Tn kap s.
     dirichlet_character d c /\ ~(c = chi_0 d) /\
     ~((\n. c n pow 2) = chi_0 d) /\ 1 <= Tn /\ &0 < kap /\ kap <= &1 /\
     &1 - kap / (&10 pow 20 * (&1 + log(&(16 * d * (Tn + 4)))) pow 12)
     <= Re s /\ Re s <= &2 /\ abs(Im s) <= &Tn
     ==> ~(dseries c s = Cx(&0)) /\
         norm(complex_derivative (dseries c) s / dseries c s) <=
         &10 pow 20 * (&1 + log(&(16 * d * (Tn + 4)))) pow 12 / kap pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `Tn:num`] ZF_LG_FACTS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `N = 16 * d * (Tn + 4)` THEN
  ABBREV_TAC `Lg = &1 + log(&N)` THEN
  SUBGOAL_THEN `&1 <= Lg` ASSUME_TAC THENL
   [EXPAND_TAC "Lg" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2048 * (&24 * Lg pow 2) pow 4 * (&12 * Lg) = &8153726976 * Lg pow 9 /\
    &1024 * (&24 * Lg pow 2) pow 4 * (&12 * Lg) = &4076863488 * Lg pow 9`
  STRIP_ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `N:num`; `&12 * Lg`;
                `s:complex`] ZF_LINE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&d * (&Tn + &4)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN EXPAND_TAC "Lg" THEN
      MATCH_MP_TAC ZF_COMPLEX_M2 THEN EXISTS_TAC `d:num` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&d * (&2 * &Tn + &3)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `!x y s. x <= y /\ &1 - x <= s ==> &1 - y <= s`) THEN
      EXISTS_TAC `kap / (&10 pow 20 * Lg pow 12)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LG_INV_COMPARE THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4076863488 * Lg pow 9` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LG_POW_COMPARE THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC);;

let ZF_RECT_REAL = prove
 (`!d c Tn kap s.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n)) /\
     1 <= Tn /\ &0 < kap /\ kap <= &1 /\ kap <= Re(dseries c (Cx(&1))) /\
     &1 - kap / (&10 pow 20 * (&1 + log(&(16 * d * (Tn + 4)))) pow 12)
     <= Re s /\ Re s <= &2 /\ abs(Im s) <= &Tn
     ==> ~(dseries c s = Cx(&0)) /\
         norm(complex_derivative (dseries c) s / dseries c s) <=
         &10 pow 20 * (&1 + log(&(16 * d * (Tn + 4)))) pow 12 / kap pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `Tn:num`] ZF_LG_FACTS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `N = 16 * d * (Tn + 4)` THEN
  ABBREV_TAC `Lg = &1 + log(&N)` THEN
  SUBGOAL_THEN `&1 <= Lg /\ Lg <= Lg pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Lg" THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * x <= x * x ==> x <= x * x`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ta = kap / (&96 * Lg pow 2)` THEN
  SUBGOAL_THEN `&0 < ta /\ ta <= &1 /\ &2 * ta = kap / (&48 * Lg pow 2) /\
                kap / (&10 pow 20 * Lg pow 12) <= ta`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ta" THEN
    SUBGOAL_THEN `&1 <= Lg pow 2 /\ Lg pow 2 <= Lg pow 12` STRIP_ASSUME_TAC
    THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE_1; MATCH_MP_TAC REAL_POW_MONO]
      THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < &96 * x`] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(Lg pow 2 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 + ta <= Re s` THENL
   [MP_TAC(SPECL [`d:num`; `c:num->complex`; `s:complex`; `ta:real`]
      ZF_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&12 / ta pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&12 / ta pow 2 = &110592 * Lg pow 4 / kap pow 2`
    SUBST1_TAC THENL
     [EXPAND_TAC "ta" THEN
      SUBGOAL_THEN `~(kap = &0) /\ ~(Lg = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
    REWRITE_TAC[GSYM real_div] THEN
    MP_TAC(SPECL [`Lg:real`; `&1`; `&110592`; `4`] LG_POW_COMPARE) THEN
    ASM_REWRITE_TAC[REAL_POW_ONE; REAL_DIV_1] THEN
    ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `ta <= abs(Im s)` THENL
   [ALL_TAC;
    MP_TAC(SPECL [`d:num`; `c:num->complex`; `N:num`; `kap:real`; `s:complex`]
      ZF_DISC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUN_1_POS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(SPEC `dseries c (Cx(&1))` COMPLEX_NORM_GE_RE_IM) THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check
          (fun th -> concl th = `&2 * ta = kap / (&48 * Lg pow 2)`)) THEN
        MP_TAC(SPEC `s - Cx(&1)` COMPLEX_NORM_LE_RE_IM) THEN
        REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; REAL_SUB_RZERO] THEN
        ASM_REAL_ARITH_TAC];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&48 * Lg pow 2 / kap` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&48 * Lg pow 2 / kap pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
        ALL_TAC] THEN
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_SIMP_TAC[REAL_POW_LT] THEN
        REWRITE_TAC[REAL_POW_2] THEN
        MATCH_MP_TAC(REAL_ARITH `x * x <= x * &1 ==> x * x <= x`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
      MP_TAC(SPECL [`Lg:real`; `&1`; `&48`; `2`] LG_POW_COMPARE) THEN
      ASM_REWRITE_TAC[REAL_POW_ONE; REAL_DIV_1] THEN
      ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC;
       ALL_TAC] THEN
      REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `&2048 * (&24 * Lg pow 2) pow 4 * (&51 * Lg pow 3 / kap) =
                (&34653339648 * Lg pow 11) / kap /\
                &1024 * (&24 * Lg pow 2) pow 4 * (&51 * Lg pow 3 / kap) =
                (&17326669824 * Lg pow 11) / kap`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `N:num`; `&51 * Lg pow 3 / kap`;
                `s:complex`] ZF_LINE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&d * (&Tn + &4)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&51 * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
       ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
      ASM_SIMP_TAC[REAL_POW_LE_1];
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 + log(&d)) * (&3 + log(&N) + inv(&2 * ta))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ZF_REAL_M2 THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(&2 * ta) = &48 * (Lg pow 2 / kap)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[REAL_INV_DIV] THEN REWRITE_TAC[real_div;
        REAL_MUL_ASSOC];
        ALL_TAC] THEN
      SUBGOAL_THEN `Lg pow 2 <= Lg pow 2 / kap /\ &0 <= log(&d)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
          MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
          ASM_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Lg * (&51 * (Lg pow 2 / kap))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div] THEN
        CONV_TAC REAL_RING];
      MATCH_MP_TAC(REAL_ARITH
       `!x y s. x <= y /\ &1 - x <= s ==> &1 - y <= s`) THEN
      EXISTS_TAC `kap / (&10 pow 20 * Lg pow 12)` THEN
      ASM_REWRITE_TAC[REAL_INV_DIV] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT;
          REAL_ARITH `&1 <= x ==> &0 < x`] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POW_LE;
          REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
        REPEAT CONJ_TAC THENL
         [REAL_ARITH_TAC; REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&17326669824 * Lg pow 11) / kap` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&17326669824 * Lg pow 11) / kap pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE;
        REAL_ARITH `&1 <= x ==> &0 <= x`] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `x * x <= x * &1 ==> x * x <= x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
  MP_TAC(SPECL [`Lg:real`; `&1`; `&17326669824`; `11`] LG_POW_COMPARE) THEN
  ASM_REWRITE_TAC[REAL_POW_ONE; REAL_DIV_1] THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let ZF_RECT = prove
 (`!d c Tn kap s.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ 1 <= Tn /\
     &0 < kap /\ kap <= &1 /\
     ((!n. real(c n)) ==> kap <= Re(dseries c (Cx(&1)))) /\
     &1 - kap / (&10 pow 20 * (&1 + log(&(16 * d * (Tn + 4)))) pow 12)
     <= Re s /\ Re s <= &2 /\ abs(Im s) <= &Tn
     ==> ~(dseries c s = Cx(&0)) /\
         norm(complex_derivative (dseries c) s / dseries c s) <=
         &10 pow 20 * (&1 + log(&(16 * d * (Tn + 4)))) pow 12 / kap pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `!n. real((c:num->complex) n)` THENL
   [MATCH_MP_TAC ZF_RECT_REAL THEN ASM_MESON_TAC[];
    MATCH_MP_TAC ZF_RECT_COMPLEX THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CHARACTER_SQUARE_PRINCIPAL_REAL]]);;
