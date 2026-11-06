(* ========================================================================= *)
(* Hua's theorem (Hua Loo-Keng 1938): every large N == 5 (mod 24) is a sum   *)
(* of five squares of primes.                                                *)
(*   HUA_FIVE_PRIME_SQUARES:                                                 *)
(*     ?N0. !N. N0 <= N /\ (N == 5) (mod 24)                                 *)
(*              ==> ?p1 p2 p3 p4 p5. prime p1 /\ prime p2 /\ prime p3 /\     *)
(*                                   prime p4 /\ prime p5 /\                 *)
(*                                   p1 EXP 2 + p2 EXP 2 + p3 EXP 2 +        *)
(*                                   p4 EXP 2 + p5 EXP 2 = N                 *)
(*   HUA_WEIGHTED_COUNT: the number of representations weighted by           *)
(*   log p1 ... log p5 (waring_conv hua_psqw N 5 N) is at least c N^(3/2).   *)
(* Method.  HUA_FIXED is the explicit circle method inequality               *)
(*   M J Re(hua_sing N Q) - (E_major + E_main + E_minor) <= M waring_conv    *)
(*   hua_psqw N 5 N,                                                         *)
(* with J = waring_conv (waring_klam 2) N 5 N >= P^3 / 2^33 (HUA_J_LOWER);   *)
(* the minor arcs contribute at most the maximum of |hua_psqexp| over them   *)
(* times the fourth moment.  Parameters: P^2 <= N < (P + 1)^2, L = log P,    *)
(* L^191 <= R <= 2 L^191 (U = V = R in Vaughan's identity),                  *)
(* L^784 <= Q <= 2 L^784, Kw = N DIV Q, M = 5 N + 1, and Siegel-Walfisz      *)
(* (THETA_AP_UNIFORM) with A = 3925, B = 785.  For L large and               *)
(* L^4000 <= P the estimates HUA_MINOR_ESTIMATE (the minor arc bound is at   *)
(* most 4 e P / L^7), HUA_EA_BOUND, HUA_EM_BOUND and HUA_EMIN_BOUND make the *)
(* errors small against the main term, and HUA_MAIN_LOWER gives              *)
(* waring_conv hua_psqw N 5 N >= c P^3.                                      *)
(* ========================================================================= *)

needs "Sieve/hua_singular.ml";;
needs "Sieve/waring.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The circle method inequality.                                             *)
(* ------------------------------------------------------------------------- *)

let hua_minor = new_definition
 `hua_minor P Kw Q U V D1 D2 =
  &18 * U +
  &1 * &P * (&1 + log(&D1)) * (&2 * sqrt(hua_e1 P D1 Q Kw) * log(&P)) +
  log(&P) * &P * (&1 + log(&D2)) * sqrt(hua_e1 P D2 Q Kw) +
  (&2 * log(&P) + &1) *
  (&P * sqrt(sqrt(&10642752 * log(&P) pow 5 * (&1 + log V) pow 6 *
    sqrt(sqrt(&2 * (&1 + log(&Kw)) / U + inv V + inv(&Q) + inv(&P) +
              &Kw * (&1 + log(&Kw)) / &P pow 2)))))`;;

let HUA_MINOR_POINT = prove
 (`!N P M Kw Q j U V D1 D2.
     P EXP 2 <= N /\ N < (P + 1) EXP 2 /\
     j < M /\ ~(j IN circ_major M Kw Q) /\ 1 <= Q /\ 1 <= Kw /\ 3 <= P /\
     &2 <= U /\ &2 <= V /\ 1 <= D1 /\ V <= &D1 /\ 1 <= D2 /\ U * V <= &D2 /\
     &2 * (&1 + log(&Kw)) / U + inv V + inv(&Q) + inv(&P) +
     &Kw * (&1 + log(&Kw)) / &P pow 2 <= &1
     ==> norm(hua_psqexp N (&j / &M)) <=
         hua_minor P Kw Q U V D1 D2 + sqrt(&P) * log(&P) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `P:num`; `&j / &M`] HUA_PSQEXP_LAMBDA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`; `j:num`; `P:num`; `U:real`;
                `V:real`; `D1:num`; `D2:num`] HUA_MINOR_LAMBDA) THEN
  ASM_REWRITE_TAC[GSYM hua_minor] THEN
  MATCH_ACCEPT_TAC(NORM_ARITH
   `!s t:complex a b. norm t <= a ==> norm(s - t) <= b
                      ==> norm s <= a + b`));;

let HUA_MINOR_SUM = prove
 (`!N P M Kw Q Bm.
     1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ 2 * N < M /\ &0 <= Bm /\
     (!j. j < M /\ ~(j IN circ_major M Kw Q)
          ==> norm(hua_psqexp N (&j / &M)) <= Bm)
     ==> norm(vsum ({j | j < M} DIFF circ_major M Kw Q)
                (\j. hua_psqexp N (&j / &M) pow 5 * expi(--(&N * &j / &M))))
         <= Bm * (&M * log(&P) pow 4 *
                  (&P pow 2 + &2 * &P pow 2 * (&1 + log(&(P EXP 2))) pow 3))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum ({j | j < M} DIFF circ_major M Kw Q)
                  (\j. Bm * norm(hua_psqexp N (&j / &M)) pow 4)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG_LT; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_EXPI; REAL_MUL_RID;
                COMPLEX_NORM_POW] THEN
    REWRITE_TAC[REAL_RING `(x:real) pow 5 = x * x pow 4`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `sum {j | j < M} (\j. Bm * norm(hua_psqexp N (&j / &M)) pow 4)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE];
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HUA_FOURTH_MOMENT THEN
    ASM_REWRITE_TAC[]]);;

let HUA_FIXED = prove
 (`!N P M Kw Q D Bm.
     1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ 5 * N < M /\
     1 <= Q /\ 2 <= Kw /\ Kw <= M /\ 2 * Q EXP 2 < Kw /\ &0 <= D /\
     &0 <= Bm /\
     (!q h b. 1 <= q /\ q <= Q /\ h <= P /\ b < q /\ coprime(b,q)
              ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                          (\p. log(&p)) - &h / &(phi q)) <= D) /\
     (!j. j < M /\ ~(j IN circ_major M Kw Q)
          ==> norm(hua_psqexp N (&j / &M)) <= Bm)
     ==> &M * waring_conv (waring_klam 2) N 5 N * Re(hua_sing N Q) -
         (&Q * &Q * (&3 * (&2 * &M / &Kw + &1)) *
          (&5 * (&P * log(&P) + &P + &1) pow 4 *
           ((&Q * D + log(&Q) + &2) * (&1 + &2 * pi * &N / &Kw))) +
          (&4 pow 4 * root 2 (&N) * (&18 * &M * &Kw)) *
          sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                           (\a. norm(Cx(inv(&(phi q))) *
                                     hua_pcsum q a) pow 5)) +
          Bm * (&M * log(&P) pow 4 *
                (&P pow 2 + &2 * &P pow 2 * (&1 + log(&(P EXP 2))) pow 3)))
         <= &M * waring_conv hua_psqw N 5 N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `M:num`] HUA_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{j | j < M} = circ_major M Kw Q UNION
                              ({j | j < M} DIFF circ_major M Kw Q)`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`M:num`; `Kw:num`; `Q:num`] CIRC_MAJOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_UNION; CIRC_MAJOR_FINITE; FINITE_DIFF; FINITE_NUMSEG_LT;
           SET_RULE `DISJOINT (s:num->bool) (t DIFF s)`] THEN
  MP_TAC(SPECL [`N:num`; `P:num`; `M:num`; `Kw:num`; `Q:num`; `D:real`]
    HUA_MAJOR_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `M:num`; `Kw:num`; `Q:num`] HUA_MAJOR_MAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `P:num`; `M:num`; `Kw:num`; `Q:num`; `Bm:real`]
    HUA_MINOR_SUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `vmaj = vsum (circ_major M Kw Q)
                (\j. hua_psqexp N (&j / &M) pow 5 *
                     expi(--(&N * &j / &M)))` THEN
  ABBREV_TAC `vmin = vsum ({j | j < M} DIFF circ_major M Kw Q)
                (\j. hua_psqexp N (&j / &M) pow 5 *
                     expi(--(&N * &j / &M)))` THEN
  ABBREV_TAC `vmod = vsum(1..Q) (\q. vsum {a | a < q /\ coprime(a,q)}
                (\a. vsum (circ_arc M Kw q a)
                  (\j. (Cx(inv(&(phi q))) * hua_pcsum q a *
                        waring_vsm 2 N (&j / &M - &a / &q)) pow 5 *
                       expi(--(&N * &j / &M)))))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&M * waring_conv hua_psqw N 5 N = Re vmaj + Re vmin`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM RE_ADD] THEN ASM_REWRITE_TAC[RE_CX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&M * waring_conv (waring_klam 2) N 5 N * Re(hua_sing N Q) =
    Re(Cx(&M * waring_conv (waring_klam 2) N 5 N) * hua_sing N Q)`
  SUBST1_TAC THENL [REWRITE_TAC[RE_MUL_CX; REAL_MUL_ASSOC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`vmaj:complex`; `vmod:complex`;
                 `Cx(&M * waring_conv (waring_klam 2) N 5 N) * hua_sing N Q`;
                 `vmin:complex`] RE_CHAIN_LOWER) THEN
  MATCH_MP_TAC(REAL_ARITH
   `n1 <= e1 /\ n2 <= e2 /\ n3 <= e3
    ==> r - n1 - n2 - n3 <= s ==> r - (e1 + e2 + e3) <= s`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Estimates for the minor arcs.                                             *)
(* ------------------------------------------------------------------------- *)

let LPOW_DIV_LE = prove
 (`!L p i j c x. &1 <= L /\ L pow (i + j) <= p /\ &0 <= c /\
                 x <= c * L pow i
                 ==> x / p <= c / L pow j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= (L:real) pow i /\ &1 <= L pow j /\ &1 <= L pow (i + j)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p /\ &0 < (L:real) pow j` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * (L:real) pow i` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(L:real) pow i = inv(L pow j) * L pow (i + j)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD] THEN UNDISCH_TAC `&0 < L pow j` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let HUA_E1_SMALL = prove
 (`!P D Q Kw L.
     &1 <= L /\ L pow 4000 <= &P /\ &Kw * &Q <= &4 * &P pow 2 /\
     &1 + log(&Kw) <= &5 * L /\ &0 <= log(&Kw) /\ L pow 784 <= &Q /\
     &D <= &4 * L pow 382
     ==> hua_e1 P D Q Kw <= &6976 / L pow 19`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hua_e1] THEN
  SUBGOAL_THEN `&1 <= (L:real) pow 382 /\ &1 <= L pow 784 /\ &1 <= L pow 4000`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &P /\ &0 < &Q` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&D pow 2 <= &16 * (L:real) pow 764` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `(&4 * (L:real) pow 382) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_POW_MUL; GSYM REAL_POW_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= &960 / l /\ b <= &896 / l /\ c <= &5120 / l
    ==> a + b + c <= &6976 / l`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC LPOW_DIV_LE THEN EXISTS_TAC `383` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 4000` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&48 * (&5 * (L:real)) * (&4 * L pow 382)` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `383 = SUC 382`; real_pow] THEN REAL_ARITH_TAC];
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC LPOW_DIV_LE THEN EXISTS_TAC `764` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 784` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&Kw <= &4 * &P pow 2 / &Q` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&1 + log(&Kw)) * &Kw) * &D pow 2 <=
    ((&5 * L) * (&4 * &P pow 2 / &Q)) * (&16 * (L:real) pow 764)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&16 * (&1 + log(&Kw)) * &Kw * &D pow 2 / &P pow 2 =
    (&16 / &P pow 2) * (((&1 + log(&Kw)) * &Kw) * &D pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&16 / &P pow 2) *
              (((&5 * (L:real)) * (&4 * &P pow 2 / &Q)) * (&16 * L pow 764))`
                  THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&P pow 2 = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&16 / &P pow 2) *
    (((&5 * (L:real)) * (&4 * &P pow 2 / &Q)) * (&16 * L pow 764)) =
    (&5120 * L pow 765) / &Q`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `765 = SUC 764`; real_pow] THEN
    UNDISCH_TAC `~(&P pow 2 = &0)` THEN UNDISCH_TAC `&0 < &Q` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC LPOW_DIV_LE THEN EXISTS_TAC `765` THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let HUA_S_SMALL = prove
 (`!P Kw Q R L.
     &1 <= L /\ L pow 4000 <= &P /\ &Kw * &Q <= &4 * &P pow 2 /\
     &1 + log(&Kw) <= &5 * L /\ &0 <= log(&Kw) /\ L pow 784 <= &Q /\
     L pow 191 <= &R
     ==> &2 * (&1 + log(&Kw)) / &R + inv(&R) + inv(&Q) + inv(&P) +
         &Kw * (&1 + log(&Kw)) / &P pow 2 <= &33 / L pow 190`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= (L:real) pow 191 /\ L pow 191 <= &Q /\ L pow 191 <= &P`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 784`;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 4000`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &P /\ &0 < &Q /\ &0 < &R` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x c. &0 <= c /\ x <= c * L ==> x / &R <= c / L pow 190 /\
                                                x / &Q <= c / L pow 190 /\
                                                x / &P <= c / L pow 190`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC LPOW_DIV_LE THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= &10 / l /\ b <= &1 / l /\ c <= &1 / l /\ d <= &1 / l /\
    e <= &20 / l ==> a + b + c + d + e <= &33 / l`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&2 * (&1 + log(&Kw))`; `&10`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `&1`]) THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[real_div; REAL_MUL_LID] THEN SIMP_TAC[]];
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `&1`]) THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[real_div; REAL_MUL_LID] THEN SIMP_TAC[]];
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `&1`]) THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[real_div; REAL_MUL_LID] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&P pow 2 = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&20 * L) / &Q` THEN CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`&20 * L`; `&20`]) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]] THEN
  SUBGOAL_THEN `&Kw * &Q <= &4 * &P pow 2 /\ &0 <= &1 + log(&Kw)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  SUBGOAL_THEN `&Kw * (&1 + log(&Kw)) * inv(&P pow 2) =
                ((&Kw * &Q) * (&1 + log(&Kw))) * inv(&P pow 2) * inv(&Q)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&4 * &P pow 2) * (&5 * L)) * inv(&P pow 2) * inv(&Q)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_POS; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `~(&P pow 2 = &0)` THEN
    CONV_TAC REAL_FIELD]);;

let HUA_T3_BOUND = prove
 (`!P Kw Q R L e.
     L = log(&P) /\ &1 <= L /\ L pow 4000 <= &P /\ &Kw * &Q <= &4 * &P pow 2 /\
     &1 + log(&Kw) <= &5 * L /\ &0 <= log(&Kw) /\ L pow 784 <= &Q /\
     L pow 191 <= &R /\ &0 <= log(&R) /\ &1 + log(&R) <= &193 * L /\
     &630000 <= e * L
     ==> (&2 * log(&P) + &1) *
         (&P * sqrt(sqrt(&10642752 * log(&P) pow 5 * (&1 + log(&R)) pow 6 *
           sqrt(sqrt(&2 * (&1 + log(&Kw)) / &R + inv(&R) + inv(&Q) +
                     inv(&P) + &Kw * (&1 + log(&Kw)) / &P pow 2)))))
         <= e * &P / L pow 7`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `L = log(&P)`)) THEN
  ABBREV_TAC `s = &2 * (&1 + log(&Kw)) / &R + inv(&R) + inv(&Q) + inv(&P) +
                  &Kw * (&1 + log(&Kw)) / &P pow 2` THEN
  SUBGOAL_THEN `s <= &33 / L pow 190` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC HUA_S_SMALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REWRITE_TAC[real_div] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L pow 9 /\ &0 < L pow 47 /\ &0 < L pow 94 /\
                &1 <= (L:real) pow 2 /\ &0 < L pow 190 /\ &0 < L pow 36`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(sqrt s) <= &3 / L pow 47` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&33 / L pow 190` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((&3 / L pow 47) pow 2) pow 2 = (&81 * L pow 2) / L pow 190`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_DIV; GSYM REAL_POW_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `(L:real) pow 190 = L pow 2 * L pow 188` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (L:real) pow 188` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&1 <= (L:real) pow 2` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Y = &10642752 * L pow 5 * (&1 + log(&R)) pow 6 * sqrt(sqrt s)`
    THEN
  SUBGOAL_THEN `Y <= &1650133385386802679744 / L pow 36` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&10642752 * L pow 5 * (&193 * L) pow 6 * (&3 / L pow 47)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
                      ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_POW_MUL] THEN
      SUBGOAL_THEN `(L:real) pow 47 = L pow 5 * L pow 6 * L pow 36` SUBST1_TAC
      THENL
       [REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (L:real) pow 5 /\ &0 < L pow 6` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `&0 < (L:real) pow 36` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(sqrt Y) <= &210000 / L pow 9` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN SIMP_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1650133385386802679744 / L pow 36` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_DIV; REAL_POW_POW] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&3 * L) * (&P * &210000 / L pow 9)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN
        MATCH_MP_TAC SQRT_POS_LE THEN EXPAND_TAC "Y" THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LE_POW_2; SQRT_POS_LE] THEN
        TRY(MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC) THEN
        MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real) pow 9 = L * L pow 8 /\ L pow 8 = L * L pow 7`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (L:real) pow 7` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 * L) * (&P * &210000 / (L * L * L pow 7)) =
                (&630000 / L) * &P / L pow 7`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < (L:real) pow 7` THEN UNDISCH_TAC `&1 <= L` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
      REAL_ARITH `&1 <= L ==> &0 < L`] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE]]);;

let HUA_SQRT_E1_BOUND = prove
 (`!P D Q Kw L e.
     &1 <= L /\ L pow 4000 <= &P /\ &Kw * &Q <= &4 * &P pow 2 /\
     &1 + log(&Kw) <= &5 * L /\ &0 <= log(&Kw) /\ L pow 784 <= &Q /\
     &D <= &4 * L pow 382 /\ &0 < e /\ &1039396096 <= e pow 2 * L
     ==> sqrt(hua_e1 P D Q Kw) <= e / (&386 * L pow 9)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (L:real) pow 9 /\ &0 < L pow 18 /\ &0 < L pow 19`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&6976 / L pow 19` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HUA_E1_SMALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(L:real) pow 19 = L * L pow 18 /\ L pow 18 = (L pow 9) pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[REAL_POW_POW; GSYM(CONJUNCT2 real_pow)] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 < (L pow 9) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_MUL;
               REAL_ARITH `&1 <= L ==> &0 < L`; REAL_POW_LT;
               REAL_ARITH `&0 < &386 pow 2`] THEN
  SUBGOAL_THEN `~((L:real) pow 9 pow 2 = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `e pow 2 / (&386 pow 2 * L pow 9 pow 2) * L * L pow 9 pow 2 =
    (e pow 2 * L) / &148996`
  SUBST1_TAC THENL
   [UNDISCH_TAC `~((L:real) pow 9 pow 2 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &148996`] THEN
  ASM_REAL_ARITH_TAC);;

let HUA_MINOR_ESTIMATE = prove
 (`!P Kw Q R L e.
     L = log(&P) /\ &1 <= L /\ L pow 4000 <= &P /\
     &Kw * &Q <= &4 * &P pow 2 /\ &1 + log(&Kw) <= &5 * L /\
     &0 <= log(&Kw) /\ L pow 784 <= &Q /\ L pow 191 <= &R /\
     &R <= &2 * L pow 191 /\ &1 + log(&R) <= &193 * L /\ &0 <= log(&R) /\
     &0 < e /\ &630000 <= e * L /\ &36 <= e * L /\
     &1039396096 <= e pow 2 * L
     ==> hua_minor P Kw Q (&R) (&R) R (R * R) <= &4 * e * &P / L pow 7`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hua_minor] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `L = log(&P)`)) THEN
  SUBGOAL_THEN `&0 < (L:real) pow 7 /\ &0 < L pow 9 /\ &1 <= L pow 191 /\
                &0 < &P`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(L:real) pow 4000` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&R <= &4 * (L:real) pow 382 /\ &R * &R <= &4 * L pow 382`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(L:real) pow 382 = L pow 191 * L pow 191` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (L:real) pow 191` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&2 * (L:real) pow 191 <= &2 * L pow 191 * L pow 191`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 <= (L:real) pow 191 * L pow 191` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * (L:real) pow 191) * (&2 * L pow 191)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:num`; `R:num`; `Q:num`; `Kw:num`; `L:real`; `e:real`]
    HUA_SQRT_E1_BOUND) THEN
  MP_TAC(SPECL [`P:num`; `R * R:num`; `Q:num`; `Kw:num`; `L:real`; `e:real`]
    HUA_SQRT_E1_BOUND) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`P:num`; `Kw:num`; `Q:num`; `R:num`; `L:real`; `e:real`]
    HUA_T3_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= x /\ b <= x /\ c <= x /\ d <= x ==> a + b + c + d <= &4 * x`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. y * L pow 7 <= e * &P ==> y <= e * &P / L pow 7`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&36 * (L:real) pow 191 * L pow 7` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(e * L) * (L:real) pow 3999` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e * L) * (L:real) pow 3999 = e * L pow 4000` SUBST1_TAC
    THENL
     [REWRITE_TAC[ARITH_RULE `4000 = SUC 3999`; real_pow] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * &P * (&193 * L) * (&2 * e / (&386 * L pow 9) * L)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[hua_e1] THEN
          REWRITE_TAC[real_div] THEN
          REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_LE_POW_2] THEN
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~((L:real) = &0) /\ ~(L pow 7 = &0)` MP_TAC THENL
       [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `9 = SUC(SUC 7)`; real_pow] THEN
      CONV_TAC REAL_FIELD];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * &P * (&386 * L) * (e / (&386 * L pow 9))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
        SUBGOAL_THEN `&0 < &R` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[LOG_MUL]] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
        SUBGOAL_THEN `&0 < &R` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[LOG_MUL]] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[hua_e1] THEN
        REWRITE_TAC[real_div] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~((L:real) = &0) /\ ~(L pow 7 = &0)` MP_TAC THENL
       [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `9 = SUC(SUC 7)`; real_pow] THEN
      CONV_TAC REAL_FIELD]]);;

(* ------------------------------------------------------------------------- *)
(* Estimates for the major arcs and the main term.                           *)
(* ------------------------------------------------------------------------- *)

let HUA_EA_BOUND = prove
 (`!m p L q k n Cb e.
     &1 <= L /\ &1 <= p /\ &1 <= q /\ &0 < k /\ k <= m /\
     n <= &2 * q * k /\ p pow 2 <= n /\
     q <= &2 * L pow 784 /\ &0 <= Cb /\ &0 < e /\
     &3965760 * Cb <= e * L /\ &11897280 * L pow 3924 <= e * p
     ==> q * q * (&3 * (&2 * m / k + &1)) *
         (&5 * (p * L + p + &1) pow 4 *
          ((q * (Cb * p / L pow 3925) + log q + &2) *
           (&1 + &2 * pi * n / k)))
         <= &2 * e * m * p pow 3`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = Cb * p / (L:real) pow 3925` THEN
  SUBGOAL_THEN `&0 < (L:real) pow 3925 /\ &0 <= D` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m /\ &0 < n /\ &0 < (p:real) pow 2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
    TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(p:real) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * (&2 * m / k + &1) <= &18 * q * m / (p:real) pow 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= m / k /\ m / k <= &2 * q * m / (p:real) pow 2`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&2 * (q:real) * m * inv(n)) * k` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(&2 * (q:real) * m * inv n) * k = (m * (&2 * q * k)) / n`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
                        ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&9 * (m:real) / k` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&9 * (&2 * q * m / (p:real) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p * (L:real) + p + &1) pow 4 <= &81 * p pow 4 * L pow 4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * p * (L:real)) pow 4` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= p ==> &0 <= x + p + &1`) THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&1 * &1 <= p * (L:real)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
          SUBGOAL_THEN `p * &1 <= p * (L:real)` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            REAL_ARITH_TAC]]];
      REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real) * D + log q + &2 <= q * (D + &3)` ASSUME_TAC THENL
   [MP_TAC(SPEC `q:real` LOG_LT_X) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &2 * pi * n / k <= &17 * (q:real)` ASSUME_TAC THENL
   [SUBGOAL_THEN `n / k <= &2 * (q:real) /\ pi <= &4 /\ &0 <= n / k`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `pi * n / k <= &4 * (&2 * (q:real))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PI_POS_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `q * q * (&18 * q * m / p pow 2) *
              (&5 * (&81 * p pow 4 * (L:real) pow 4) * ((q * (D + &3)) * (&17
                * q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= p ==> &0 <= x + p + &1`) THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC `q:real` LOG_POS) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= (q:real) * D` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POS; PI_POS_LE; REAL_LE_DIV; REAL_LT_IMP_LE]];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= p ==> &0 <= x + p + &1`) THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MP_TAC(SPEC `q:real` LOG_POS) THEN ANTS_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `&0 <= (q:real) * D` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          ASM_SIMP_TAC[REAL_POS; PI_POS_LE; REAL_LE_DIV; REAL_LT_IMP_LE]];
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MP_TAC(SPEC `q:real` LOG_POS) THEN ANTS_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `&0 <= (q:real) * D` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          ASM_SIMP_TAC[REAL_POS; PI_POS_LE; REAL_LE_DIV; REAL_LT_IMP_LE]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real) pow 2 = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `q * q * (&18 * q * m / p pow 2) *
    (&5 * (&81 * p pow 4 * (L:real) pow 4) * ((q * (D + &3)) * (&17 * q))) =
    &123930 * q pow 5 * m * p pow 2 * L pow 4 * (D + &3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 + 2`; REAL_POW_ADD] THEN
    UNDISCH_TAC `~(p pow 2 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow 5 <= &32 * (L:real) pow 3920` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `(&2 * (L:real) pow 784) pow 5` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&123930 * (&32 * (L:real) pow 3920) * m * p pow 2 * L pow 4 * (D
      + &3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "D" THEN
  SUBGOAL_THEN `~((L:real) = &0) /\ ~(L pow 3920 = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&123930 * (&32 * (L:real) pow 3920) * m * p pow 2 * L pow 4 *
    (Cb * p / L pow 3925 + &3) =
    m * p pow 2 * ((&3965760 * Cb) / L * p + &11897280 * L pow 3924)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3925 = SUC(3920 + 4)`; real_pow; REAL_POW_ADD;
                ARITH_RULE `3924 = 3920 + 4`] THEN
    UNDISCH_TAC `~(L pow 3920 = &0)` THEN UNDISCH_TAC `~(L = &0)` THEN
    SUBGOAL_THEN `~((L:real) pow 4 = &0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * e * m * (p:real) pow 3 = m * p pow 2 * (e * p + e * p)`
  SUBST1_TAC THENL [REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow] THEN
                    REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC;
   ASM_REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= L ==> &0 < L`]);;

let HUA_SUM_PHI_DECAY = prove
 (`?Cs. &0 <= Cs /\
        !Q. sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}
                             (\a. norm(Cx(inv(&(phi q))) *
                                       hua_pcsum q a) pow 5))
            <= Cs`,
  X_CHOOSE_THEN `Ch:real` STRIP_ASSUME_TAC HTERM_ABS_DECAY THEN
  EXISTS_TAC `&5 * Ch` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..Q) (\q. Ch * &q rpow (--(&5 / &4)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `Q = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `~(Q = 0) ==> 1 <= Q`] THEN
  REWRITE_TAC[RPOW_ONE] THEN
  MP_TAC(SPECL [`1`; `Q:num`; `&1 / &4`] SUM_RPOW_TAIL) THEN
  REWRITE_TAC[LE_REFL; REAL_ARITH `--(&1 / &4 + &1) = --(&5 / &4)`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[RPOW_ONE] THEN
  DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= &4 ==> &1 + x <= &5`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / (&1 / &4)` THEN
  CONJ_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]);;

let HUA_EM_BOUND = prove
 (`!N P M Kw Q X Cs e.
     1 <= P /\ N <= 4 * P EXP 2 /\ Kw * Q <= N /\ 1 <= Q /\ &0 <= X /\
     X <= Cs /\ &0 < e /\ &36864 * Cs <= e * &Q
     ==> (&4 pow 4 * root 2 (&N) * (&18 * &M * &Kw)) * X
         <= e * &M * &P pow 3`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ROOT_2] THEN
  SUBGOAL_THEN `sqrt(&N) <= &2 * &P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [REAL_ARITH_TAC;
    ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_MUL;
                REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Q /\ &0 < &P` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&Kw <= &4 * &P pow 2 / &Q` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4 pow 4 * (&2 * &P) * (&18 * &M * (&4 * &P pow 2 / &Q))) * Cs`
    THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      SIMP_TAC[REAL_POS; REAL_POW_LE; SQRT_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
       REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&4 pow 4 * (&2 * &P) * (&18 * &M * (&4 * &P pow 2 / &Q))) * Cs =
    (&36864 * Cs / &Q) * &M * &P pow 3`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POS; REAL_POW_LE]]);;

let HUA_EMIN_BOUND = prove
 (`!P M Bm L e.
     L = log(&P) /\ &1 <= L /\ 1 <= P /\ &0 <= Bm /\ &0 <= e /\
     Bm <= &5 * e * &P / L pow 7
     ==> Bm * (&M * log(&P) pow 4 *
               (&P pow 2 + &2 * &P pow 2 * (&1 + log(&(P EXP 2))) pow 3))
         <= &275 * e * &M * &P pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &P` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&(P EXP 2)) = &2 * (L:real)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_POW; LOG_POW]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `L = log(&P)`)) THEN
  SUBGOAL_THEN `&0 < (L:real) pow 7 /\ &0 <= L pow 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT; MATCH_MP_TAC REAL_POW_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&P pow 2 + &2 * &P pow 2 * (&1 + &2 * (L:real)) pow 3 <= &55 * &P pow 2 *
       L pow 3`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + &2 * (L:real)) pow 3 <= &27 * L pow 3 /\ &1 <= L pow 3`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * (L:real)) pow 3` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &P pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&P pow 2 * &1 <= &P pow 2 * (L:real) pow 3 /\
                  &P pow 2 * (&1 + &2 * L) pow 3 <=
                  &P pow 2 * (&27 * L pow 3)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&5 * e * &P / (L:real) pow 7) * (&M * L pow 4 * (&55 * &P pow 2
      * L pow 3))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= &P pow 2 + &2 * &P pow 2 * (&1 + &2 * (L:real)) pow 3`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `~((L:real) pow 7 = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `7 = 4 + 3`; REAL_POW_ADD] THEN
  CONV_TAC REAL_FIELD);;

let HUA_J_LOWER = prove
 (`!N P. 1 <= P /\ P EXP 2 <= N /\ N < (P + 1) EXP 2 /\ 32 <= N
         ==> &P pow 3 / &2 pow 33 <= waring_conv (waring_klam 2) N 5 N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `N:num`; `5`; `N:num`] JCONV_LOWER) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  SUBGOAL_THEN `&P <= root 2 (&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `root 2 (&P pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC REAL_ROOT_POW THEN REWRITE_TAC[REAL_POS] THEN ARITH_TAC;
      MATCH_MP_TAC ROOT_MONO_LE THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N /\ &N <= &4 * &P pow 2 /\ &0 < &P` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_POW; REAL_OF_NUM_MUL;
                REAL_OF_NUM_LE] THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `(P + 1) EXP 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP_2] THEN
    SUBGOAL_THEN `1 <= P * P /\ 1 * P <= P * P` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x`) THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[]];
      ARITH_TAC];
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&2) * inv(&2) pow 30 * &P pow 5 / &N` THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
            [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC]) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
  SUBGOAL_THEN `inv(&2) * inv(&2) pow 30 * &P pow 5 / &N =
                (&P pow 3 / &2 pow 33) * (&4 * &P pow 2 / &N)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID]]);;

let HUA_MINOR_POS = prove
 (`!P Kw Q U V D1 D2.
     1 <= P /\ 1 <= D1 /\ 1 <= D2 /\ 1 <= Kw /\ 1 <= Q /\ &0 <= U /\
     &0 <= V
     ==> &0 <= hua_minor P Kw Q U V D1 D2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hua_minor; hua_e1] THEN
  SUBGOAL_THEN `!x:real. x pow 6 = (x pow 3) pow 2` (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&P) /\ &0 <= log(&D1) /\ &0 <= log(&D2) /\
                &0 <= log(&Kw)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_POW_LE; REAL_LE_POW_2] THEN
  TRY ASM_REAL_ARITH_TAC THEN
  REPEAT(MATCH_MP_TAC SQRT_POS_LE) THEN
  REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL ORELSE
          MATCH_MP_TAC REAL_LE_DIV ORELSE MATCH_MP_TAC REAL_LE_INV ORELSE
          MATCH_MP_TAC SQRT_POS_LE) THEN TRY CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LE_POW_2] THEN
  ASM_REAL_ARITH_TAC);;

let HUA_FINAL_ARITH = prove
 (`!m J R w EA EM En p c0.
     &0 < m /\ &0 <= p /\ &0 < c0 /\ p pow 3 / &2 pow 33 <= J /\ c0 <= R /\
     m * J * R - (EA + EM + En) <= m * w /\
     EA <= &2 * (c0 / &2 pow 45) * m * p pow 3 /\
     EM <= (c0 / &2 pow 45) * m * p pow 3 /\
     En <= &275 * (c0 / &2 pow 45) * m * p pow 3
     ==> c0 / &2 pow 34 * p pow 3 <= w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (p:real) pow 3 / &2 pow 33` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `((p:real) pow 3 / &2 pow 33) * c0 <= J * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real) * (p pow 3 / &2 pow 33) * c0 <= m * J * R` ASSUME_TAC
    THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (m:real) * p pow 3 * c0` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real) * (c0 / &2 pow 34 * p pow 3) <= m * w` MP_TAC THENL
   [SUBGOAL_THEN
     `(m:real) * (p pow 3 / &2 pow 33) * c0 = (m * p pow 3 * c0) / &2 pow 33 /\
      &2 * (c0 / &2 pow 45) * m * p pow 3 =
      &2 * (m * p pow 3 * c0) / &2 pow 45 /\
      (c0 / &2 pow 45) * m * p pow 3 = (m * p pow 3 * c0) / &2 pow 45 /\
      &275 * (c0 / &2 pow 45) * m * p pow 3 =
      &275 * (m * p pow 3 * c0) / &2 pow 45 /\
      m * (c0 / &2 pow 34 * p pow 3) = (m * p pow 3 * c0) / &2 pow 34`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN REPEAT CONJ_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && can (find_term (fun t -> t = `&2 pow 45` ||
                                                 t = `&2 pow 34` ||
                                                 t = `&2 pow 33`))
                                       (rand(concl th))))) THEN
    ABBREV_TAC `X = (m:real) * p pow 3 * c0` THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE REAL_RAT_REDUCE_CONV) THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

let HUA_SQRT_TERM = prove
 (`!P L e. &1 <= L /\ L pow 4000 <= &P /\ &0 < e /\ &1 <= e pow 2 * L
           ==> sqrt(&P) * L pow 2 <= e * &P / L pow 7`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (L:real) pow 7 /\ &1 <= L pow 4000` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
                    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&P) /\ sqrt(&P) pow 2 = &P` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = sqrt(&P)` THEN
  SUBGOAL_THEN `(L:real) pow 9 <= e * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e pow 2 * (L:real) pow 4000` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(e pow 2 * L) * (L:real) pow 3999` THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
                        ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `4000 = SUC 3999`; real_pow] THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `s pow 2 = &P`)) THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `(s * (L:real) pow 2) * L pow 7 = s * L pow 9 /\
                e * s pow 2 = s * (e * s)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[ARITH_RULE `9 = 2 + 7`; REAL_POW_ADD] THEN
    CONJ_TAC THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let HUA_FINAL_STEP = prove
 (`!m J R w EA EM En.
     m * J * R - (EA + EM + En) <= m * w
     ==> !p c0. &0 < m /\ &0 <= p /\ &0 < c0 /\ p pow 3 / &2 pow 33 <= J /\
                c0 <= R /\
                EA <= &2 * (c0 / &2 pow 45) * m * p pow 3 /\
                EM <= (c0 / &2 pow 45) * m * p pow 3 /\
                En <= &275 * (c0 / &2 pow 45) * m * p pow 3
                ==> c0 / &2 pow 34 * p pow 3 <= w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HUA_FINAL_ARITH THEN
  MAP_EVERY EXISTS_TAC [`m:real`; `J:real`; `R:real`; `EA:real`; `EM:real`;
                        `En:real`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hua's theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let HUA_MAIN_LOWER = prove
 (`?c N0. &0 < c /\
          !N P. N0 <= N /\ (N == 5) (mod 24) /\
                P EXP 2 <= N /\ N < (P + 1) EXP 2
                ==> c * &P pow 3 <= waring_conv hua_psqw N 5 N`,
  X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `Q0:num` STRIP_ASSUME_TAC)
    HUA_SING_LOWER THEN
  X_CHOOSE_THEN `Cs:real` STRIP_ASSUME_TAC HUA_SUM_PHI_DECAY THEN
  MP_TAC(SPECL [`3925`; `785`] THETA_AP_UNIFORM) THEN
  DISCH_THEN(X_CHOOSE_TAC `Cb:real`) THEN
  MP_TAC(SPECL [`4000`; `&1`; `&1`] POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_TAC `L1:real`) THEN
  ABBREV_TAC `e = c0 / &2 pow 45` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC
   `K0 = max (&33) (max (&Q0) (max L1 (max ((&3965760 * abs Cb) / e)
         (max (&11897280 / e) (max ((&36864 * Cs) / e) (max (&630000 / e)
         (max (&36 / e) (max (&1039396096 / (e * e)) (&1 / (e * e))))))))))`
             THEN
  MP_TAC(SPEC `exp K0` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `P0:num`) THEN
  EXISTS_TAC `c0 / &2 pow 34` THEN EXISTS_TAC `(P0 + 1) EXP 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `P:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `P0 < P:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P + 1) EXP 2 <= (P0 + 1) EXP 2` MP_TAC THENL
     [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= P /\ &0 < &P /\ exp K0 <= &P` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&P0` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = log(&P)` THEN
  SUBGOAL_THEN `K0 <= L:real` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `K0:real`)) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MAX_LE]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `!x. x / e <= L ==> x <= e * L:real` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x / (e * e) <= L ==> x <= e pow 2 * L:real` ASSUME_TAC
    THENL
   [GEN_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&33 <= L /\ &Q0 <= L /\ L1 <= L /\
    &3965760 * abs Cb <= e * L /\ &11897280 <= e * L /\
    &36864 * Cs <= e * L /\ &630000 <= e * L /\ &36 <= e * L /\
    &1039396096 <= e pow 2 * L /\ &1 <= e pow 2 * L`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_MP_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L /\ &0 < L` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&33 <= L` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L pow 4000 <= &P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp L` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    EXPAND_TAC "L" THEN ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPEC `&2 * L pow 191` NUM_FLOOR_HALF) THEN ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &2 * x`) THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `&2 * L pow 784` NUM_FLOOR_HALF) THEN ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &2 * x`) THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `L pow 191 <= &R /\ L pow 784 <= &Q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&2 * L pow 191 <= &2 * &R`;
      UNDISCH_TAC `&2 * L pow 784 <= &2 * &Q`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `L <= L pow 191 /\ L <= L pow 784 /\ &2 * L pow 784 <= L pow
      785`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC) THEN
    REWRITE_TAC[ARITH_RULE `785 = SUC 784`; real_pow] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&33 <= L` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN UNDISCH_TAC `&1 <= L` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= &R /\ &Q0 <= &Q /\ &1 <= &Q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`L pow 191 <= &R`; `L pow 784 <= &Q`;
                           `(L:real) <= L pow 191`; `(L:real) <= L pow 784`;
                           `&33 <= L`; `&Q0 <= L`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_LE]) THEN
  SUBGOAL_THEN `N <= 4 * P EXP 2` ASSUME_TAC THENL
   [MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `(P + 1) EXP 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP_2] THEN
    SUBGOAL_THEN `1 <= P * P /\ 1 * P <= P * P:num` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x`) THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[]];
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&33 <= &P /\ &P <= &N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`L pow 4000 <= &P`; `&33 <= L`] THEN
      SUBGOAL_THEN `(L:real) <= L pow 4000` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        REAL_ARITH_TAC];
      REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `P EXP 2` THEN ASM_REWRITE_TAC[EXP_2] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `P = 1 * P:num`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * Q EXP 2 + 1) * Q <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL;
                GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * &Q pow 3` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&1 <= &Q pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &Q` MP_TAC THENL [REWRITE_TAC[REAL_POS];
       ALL_TAC] THEN
      SPEC_TAC(`&Q`,`x:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(x:real) * &1 <= x * x pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real) pow 3 = x * x pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&3 * (&2 * (L:real) pow 784) pow 3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) * L pow 2352` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `&33 <= L` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN UNDISCH_TAC `&0 < L` THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 4000` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`L pow 4000 <= &P`; `&P <= &N`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `Q:num`] DIV_PARAMETER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `Kw = N DIV Q` THEN STRIP_TAC THEN
  ABBREV_TAC `M = 5 * N + 1` THEN
  SUBGOAL_THEN `5 * N < M /\ Kw <= M /\ 2 <= Kw /\ 3 <= P /\ 32 <= N /\
                1 <= Kw:num`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    SUBGOAL_THEN `33 <= P /\ Kw <= N:num` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `Kw * Q:num` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `Kw = Kw * 1:num`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= Q EXP 2 /\ 33 * 33 <= P EXP 2` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[EXP_2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x`) THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`2 * Q EXP 2 < Kw`; `P EXP 2 <= N`;
                           `Kw <= N:num`; `33 <= P`; `1 <= Q EXP 2`;
                           `33 * 33 <= P EXP 2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&Kw * &Q <= &4 * &P pow 2 /\ &1 <= &Kw /\ &Kw <= &4 * &P pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`Kw * Q <= N:num`; `N <= 4 * P EXP 2`;
     `1 <= Kw:num`;
                           `1 <= Q:num`] THEN
    SUBGOAL_THEN `Kw <= Kw * Q:num` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `Kw = Kw * 1:num`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC[];
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` LOG_LE) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&Kw) /\ &1 + log(&Kw) <= &5 * L` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 + log(&4 * &P pow 2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&1 <= &Kw` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `log(&4 * &P pow 2) = &2 * log(&2) + &2 * L` SUBST1_TAC
    THENL
     [SUBGOAL_THEN `&4 * &P pow 2 = &2 pow 2 * &P pow 2` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[LOG_MUL; REAL_POW_LT; REAL_ARITH `&0 < &2`;
               ASSUME `&0 < &P`; LOG_POW] THEN
      EXPAND_TAC "L" THEN REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`log(&2) <= &1`; `&1 <= L`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&R) /\ &1 + log(&R) <= &193 * L` STRIP_ASSUME_TAC
  THENL
   [SUBGOAL_THEN `&1 <= &R` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `2 <= R` THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 + log(&2 * L pow 191)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&1 <= &R` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; REAL_ARITH `&0 < &2`; LOG_POW] THEN
    MP_TAC(SPEC `L:real` LOG_LT_X) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`log(&2) <= &1`; `&1 <= L`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Bm = hua_minor P Kw Q (&R) (&R) R (R * R) +
                   sqrt(&P) * (L:real) pow 2` THEN
  SUBGOAL_THEN `&0 <= Bm /\ Bm <= &5 * e * &P / (L:real) pow 7`
    STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "Bm" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC HUA_MINOR_POS THEN ASM_REWRITE_TAC[REAL_POS] THEN
        UNDISCH_TAC `2 <= R` THEN REWRITE_TAC[MULT_EQ_0;
          ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= &4 * e * p / l /\ b <= e * p / l ==> a + b <= &5 * e * p / l`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HUA_MINOR_ESTIMATE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HUA_SQRT_TERM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < M /\ ~(j IN circ_major M Kw Q)
        ==> norm(hua_psqexp N (&j / &M)) <= Bm`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Bm" THEN EXPAND_TAC "L" THEN
    MATCH_MP_TAC HUA_MINOR_POINT THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_OF_NUM_MUL; REAL_OF_NUM_LE;
     LE_REFL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `2 <= R` THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&33 / (L:real) pow 190` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HUA_S_SMALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(L:real) <= L pow 190` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN SUBGOAL_THEN `&0 < (L:real) pow 190` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(L:real) <= L pow 190`; `&33 <= L`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MAP_EVERY UNDISCH_TAC [`(L:real) <= L pow 190`; `&33 <= L`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `D = abs Cb * &P / (L:real) pow 3925` THEN
  SUBGOAL_THEN `&0 < (L:real) pow 3925` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN UNDISCH_TAC `&0 < L pow 3925` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q h b. 1 <= q /\ q <= Q /\ h <= P /\ b < q /\ coprime(b,q)
            ==> abs(sum {p | prime p /\ p <= h /\ (p == b) (mod q)}
                        (\p. log(&p)) - &h / &(phi q)) <= D`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Cb * &P / log(&P) pow 3925` THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Cb:real`)) (concl th)))
      THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `&33 <= &P` THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&Q` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        MAP_EVERY UNDISCH_TAC [`&Q <= &2 * (L:real) pow 784`;
                               `&2 * L pow 784 <= L pow 785`] THEN
        REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      UNDISCH_TAC `&0 < L pow 3925` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `P:num`; `M:num`; `Kw:num`; `Q:num`; `D:real`;
                `Bm:real`] HUA_FIXED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`&P`; `c0:real`] o MATCH_MP HUA_FINAL_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `5 * N < M` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HUA_J_LOWER THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `hua_sing`)) (concl th))) THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "D" THEN MATCH_MP_TAC HUA_EA_BOUND THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE; REAL_OF_NUM_LT;
                    REAL_OF_NUM_MUL; REAL_OF_NUM_POW] THEN
    CONJ_TAC THENL [UNDISCH_TAC `1 <= Kw` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(e * (L:real)) * L pow 3924` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN UNDISCH_TAC `&0 < (L:real)` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [UNDISCH_TAC `&0 < (e:real)` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L:real) pow 4000` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
      ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    MATCH_MP_TAC HUA_EM_BOUND THEN EXISTS_TAC `Q:num` THEN
    EXISTS_TAC `Cs:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * (L:real)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [UNDISCH_TAC `&0 < (e:real)` THEN REAL_ARITH_TAC;
                      ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`(L:real) <= L pow 784`; `(L:real) pow 784 <= &Q`]
      THEN REAL_ARITH_TAC];
    EXPAND_TAC "L" THEN MATCH_MP_TAC HUA_EMIN_BOUND THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < (e:real)` THEN REAL_ARITH_TAC]);;

let HUA_FIVE_PRIME_SQUARES = prove
 (`?N0. !N. N0 <= N /\ (N == 5) (mod 24)
            ==> ?p1 p2 p3 p4 p5. prime p1 /\ prime p2 /\ prime p3 /\
                                 prime p4 /\ prime p5 /\
                                 p1 EXP 2 + p2 EXP 2 + p3 EXP 2 +
                                 p4 EXP 2 + p5 EXP 2 = N`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)
    HUA_MAIN_LOWER THEN
  EXISTS_TAC `N0 + 1` THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC HUA_EXISTS THEN
  MP_TAC(SPECL [`2`; `N:num`] NUM_KTH_ROOT) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `P:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x <= y ==> &0 < y`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
  REWRITE_TAC[ARITH_RULE `0 < P <=> ~(P = 0)`] THEN DISCH_TAC THEN
  UNDISCH_TAC `N < (P + 1) EXP 2` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let HUA_WEIGHTED_COUNT = prove
 (`?c N0. &0 < c /\
          !N. N0 <= N /\ (N == 5) (mod 24)
              ==> c * &N rpow (&3 / &2) <= waring_conv hua_psqw N 5 N`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)
    HUA_MAIN_LOWER THEN
  EXISTS_TAC `c / &8` THEN EXISTS_TAC `N0 + 1` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `N:num`] NUM_KTH_ROOT) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `P:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= y ==> a <= y`) THEN
  SUBGOAL_THEN `1 <= P` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= P <=> ~(P = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `N < (P + 1) EXP 2` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&N rpow (&3 / &2) = sqrt(&N) pow 3` SUBST1_TAC THENL
   [SIMP_TAC[GSYM RPOW_SQRT; REAL_POS] THEN
    SIMP_TAC[RPOW_RPOW; REAL_POS; GSYM RPOW_POW] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&N) <= &2 * &P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [REAL_ARITH_TAC;
    ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_MUL;
                REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `(P + 1) EXP 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `1 <= P * P /\ 1 * P <= P * P:num` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x`) THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[]];
      ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / &8 * (&2 * &P) pow 3` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS];
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]);;
