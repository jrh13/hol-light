(* ========================================================================= *)
(* Hua's theorem III: the singular series                                    *)
(*   hua_sing N Q = sum_{q <= Q} hua_term N q,                               *)
(*   hua_term N q = sum_{a < q, (a,q) = 1} (hua_pcsum q a / phi q)^5 e(-N    *)
(*   a/q).                                                                   *)
(* * Decay.  HUA_PCSUM_MOBIUS: hua_pcsum q a = sum_{e | q} mu(e) waring_csum *)
(*   2 (q/e) (a e); WARING_CSUM_DECAY with the gcd reduction                 *)
(*   (WARING_CSUM_COFACTOR_BOUND), the divisor bound and phi(q) >= c q^(1 -  *)
(*   d) (PHI_LOWER_RPOW) give                                                *)
(*     HTERM_ABS_DECAY: sum_{(a,q)=1} |hua_pcsum q a / phi q|^5 <= C         *)
(*     q^(-5/4).                                                             *)
(* * Local densities over units: hua_loc L s c counts the s-tuples of units  *)
(*   mod L whose squares sum to c mod L, and                                 *)
(*     HUA_LOC_SING: sum_{d | L} hua_term c d = L hua_loc L 5 c / phi(L)^5,  *)
(*   by HUA_LOC_FOURIER and HUA_PCSUM_SCALE (a periodic sum over the units   *)
(*   mod L, UNITS_PERIODIC_SUM); this is multiplicative in L                 *)
(*   (CRT_UNITS_SUM2, HDEN_MULTIPLICATIVE).                                  *)
(* * Hensel lifting over units (HUA_LOC_PRIMEPOW_LOWER) and unit solubility  *)
(*   (HUA_SOLUBLE): for N == 5 (mod 24), N - 1 is a sum of four unit squares *)
(*   mod 8, mod 3 and mod every prime p >= 5 (two squares and                *)
(*   1 = (3/5)^2 + (4/5)^2 for p >= 7, explicit tuples for p = 5).           *)
(* * HUA_SING_LOWER: there are c0 > 0 and Q0 with c0 <= Re(hua_sing N Q) for *)
(*   all N == 5 (mod 24) and Q >= Q0 (local factors as in                    *)
(*   waring_singular.ml).                                                    *)
(* ========================================================================= *)

needs "Sieve/hua_major.ml";;
needs "Sieve/waring_singular.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Decay of the complete sums.                                               *)
(* ------------------------------------------------------------------------- *)

let HUA_PCSUM_MOBIUS = prove
 (`!q a. 1 <= q
         ==> hua_pcsum q a =
             vsum {e | e divides q}
                  (\e. Cx(mobius e) * waring_csum 2 (q DIV e) (a * e))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {d | d divides q}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. (if coprime(b,q) then &1 else &0) =
        sum {d | d divides q} (\d. if d divides b then mobius d else &0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[COPRIME_GCD] THEN
    MP_TAC(SPEC `gcd(b,q)` DIVISORSUM_MOBIUS) THEN ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; GCD_ZERO] THEN
      ASM_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET; ETA_AX] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; DIVIDES_GCD] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[hua_pcsum] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {b | b < q}
                (\b. Cx(if coprime(b,q) then &1 else &0) *
                     expi(&a * &(b EXP 2) / &q))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM VSUM_CX; GSYM VSUM_COMPLEX_RMUL] THEN
  MP_TAC(GEN `f:num->num->complex`
   (MP (ISPECL [`f:num->num->complex`; `{b:num | b < q}`;
                `{d | d divides q}`] VSUM_SWAP)
       (CONJ (SPEC `q:num` FINITE_NUMSEG_LT)
             (ASSUME `FINITE {d | d divides q}`)))) THEN
  DISCH_THEN(fun sw -> GEN_REWRITE_TAC LAND_CONV [sw]) THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `d:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= d /\ q = d * q DIV d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= d <=> ~(d = 0)`] THEN DISCH_TAC THEN
      UNDISCH_TAC `d divides q` THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
      ASM_ARITH_TAC;
      ASM_MESON_TAC[DIVIDES_DIV_MULT; MULT_SYM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q DIV d = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `q = d * q DIV d` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_RESTRICT_IND] THEN ASM_SIMP_TAC[VSUM_MULTIPLES_LT] THEN
  REWRITE_TAC[waring_csum] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `&q = &d * &(q DIV d)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  SUBGOAL_THEN `~(&d = &0) /\ ~(&(q DIV d) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN UNDISCH_TAC `1 <= d` THEN ARITH_TAC;
    CONV_TAC REAL_FIELD]);;

let WARING_CSUM_COFACTOR_BOUND = prove
 (`!d. &0 < d /\ d <= &1 / &2
       ==> ?Cw. &0 <= Cw /\
               !q a e. 1 <= q /\ coprime(a,q) /\ e divides q
                       ==> norm(waring_csum 2 (q DIV e) (a * e)) <=
                           Cw * &q rpow (&1 / &2 + d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `d:real`] WARING_CSUM_DECAY) THEN
  ASM_REWRITE_TAC[ARITH; EXP_1] THEN
  REWRITE_TAC[REAL_ARITH `&1 - inv(&2) + d = &1 / &2 + d`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Cw:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `a:num`; `e:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `s = &1 / &2 + d` THEN
  SUBGOAL_THEN `&0 <= s /\ &1 - s <= s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `L:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides]) THEN
  SUBGOAL_THEN `~(e = 0) /\ ~(L = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `1 <= e * L` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT] THEN
  SUBGOAL_THEN `gcd(a * e,L) divides e` ASSUME_TAC THENL
   [UNDISCH_TAC `coprime(a,e * L)` THEN CONV_TAC NUMBER_RULE; ALL_TAC] THEN
  MP_TAC(SPECL [`a * e:num`; `L:num`] GCD_COPRIME_EXISTS) THEN
  ABBREV_TAC `g = gcd(a * e,L)` THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `L1:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(g = 0) /\ ~(L1 = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `L = L1 * g:num` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `waring_csum 2 L (a * e) = Cx(&g) * waring_csum 2 L1 b`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`2`; `L1:num`; `L:num`; `b:num`] WARING_CSUM_SCALE) THEN
    SUBGOAL_THEN `L DIV L1 = g` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DIV_MULT]; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0];
        CONV_TAC NUMBER_RULE];
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &g /\ &1 <= &g /\ &g <= &e` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&g <= &e rpow s * &g rpow s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&g rpow (&1 - s) * &g rpow s` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM RPOW_ADD; REAL_ARITH `(&1 - s) + s = &1`;
                   RPOW_POW; REAL_POW_1; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&g rpow s` THEN
      ASM_SIMP_TAC[RPOW_MONO_LE] THEN MATCH_MP_TAC RPOW_LE2 THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&g * (Cw * &L1 rpow s)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL; RPOW_MUL] THEN
  SUBGOAL_THEN `&0 <= &L1 rpow s` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&g * &L1 rpow s <= (&e rpow s * &g rpow s) * &L1 rpow s`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (ASSUME `&0 <= Cw`)) THEN
  MATCH_MP_TAC(REAL_ARITH `a = c /\ b = d ==> a <= b ==> c <= d`) THEN
  CONJ_TAC THEN REAL_ARITH_TAC);;

let HUA_PCSUM_DECAY = prove
 (`!d. &0 < d /\ d <= &1 / &2
       ==> ?Cp. &0 <= Cp /\
               !q a. 1 <= q /\ coprime(a,q)
                     ==> norm(hua_pcsum q a) <= Cp *
                         &q rpow (&1 / &2 + &2 * d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d:real` WARING_CSUM_COFACTOR_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cw:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `d:real` DIVISOR_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ct:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Ct * Cw:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `a:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {e | e divides q}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[HUA_PCSUM_MOBIUS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {e | e divides q} (\e. Cw * &q rpow (&1 / &2 + d))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE; REAL_ABS_MOBIUS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD {e | e divides q}) <= Ct * &q rpow d` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Cw * &q rpow (&1 / &2 + d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_RMUL o C CONJ
    (ASSUME `&0 <= Cw * &q rpow (&1 / &2 + d)`)) THEN
  MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 + &2 * d = d + (&1 / &2 + d)`] THEN
  ASM_SIMP_TAC[RPOW_ADD] THEN CONV_TAC REAL_RING);;

let PHI_LOWER_RPOW = prove
 (`!d. &0 < d
       ==> ?c. &0 < c /\ !q. 1 <= q ==> c * &q rpow (&1 - d) <= &(phi q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d:real` DIVISOR_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ct:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv(Ct:real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &q /\ &0 < &(phi q) /\ &0 < Ct` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&q / &(phi q) <= Ct * &q rpow d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {e | e divides q} (\e. inv(&(phi e)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PHI_RATIO_LE THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {e | e divides q} (\e. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[FINITE_DIVISORS; ARITH_RULE `1 <= q ==> ~(q = 0)`] THEN
      X_GEN_TAC `e:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
      REWRITE_TAC[ARITH_RULE `1 <= e <=> ~(e = 0)`] THEN DISCH_TAC THEN
      UNDISCH_TAC `e divides q` THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[SUM_CONST; FINITE_DIVISORS;
                   ARITH_RULE `1 <= q ==> ~(q = 0)`; REAL_MUL_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q rpow d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_SUB; RPOW_POW; REAL_POW_1] THEN
  UNDISCH_TAC `&q / &(phi q) <= Ct * &q rpow d` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&0 < c /\ &0 < r ==> inv c * q * inv r = q / (c * r)`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL] THEN REAL_ARITH_TAC);;

let HTERM_ABS_DECAY = prove
 (`?Ch. &0 <= Ch /\
        !q. 1 <= q
            ==> sum {a | a < q /\ coprime(a,q)}
                    (\a. norm(Cx(inv(&(phi q))) * hua_pcsum q a) pow 5)
                <= Ch * &q rpow (--(&5 / &4))`,
  MP_TAC(SPEC `&1 / &60` HUA_PCSUM_DECAY) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cp:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `&1 / &60` PHI_LOWER_RPOW) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(Cp / c:real) pow 5` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {a | a < q /\ coprime(a,q)}
                  (\a. (Cp / c) pow 5 * &q rpow (--(&9 / &4)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_COPRIME_RESIDUES; IN_ELIM_THM] THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV;
                REAL_ABS_NUM] THEN
    SUBGOAL_THEN `&0 < &q rpow (&1 - &1 / &60)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < c * &q rpow (&1 - &1 / &60)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `inv(&(phi q)) * norm(hua_pcsum q a) <= (Cp / c) * &q rpow (--(&9 / &20))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(c * &q rpow (&1 - &1 / &60)) *
                  (Cp * &q rpow (&1 / &2 + &2 * &1 / &60))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[NORM_POS_LE; REAL_LE_INV_EQ; REAL_POS] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[REAL_ARITH
         `--(&9 / &20) = (&1 / &2 + &2 * &1 / &60) - (&1 - &1 / &60)`] THEN
        ASM_SIMP_TAC[RPOW_SUB] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < &q rpow (&1 - &1 / &60)` THEN
        UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((Cp / c) * &q rpow (--(&9 / &20))) pow 5` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[NORM_POS_LE; REAL_LE_INV_EQ; REAL_POS];
      ASM_SIMP_TAC[REAL_POW_MUL; RPOW_POW_MUL] THEN
      REWRITE_TAC[REAL_ARITH `&5 * --(&9 / &20) = --(&9 / &4)`; REAL_LE_REFL]];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES; CARD_COPRIME_RESIDUES] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&q * (Cp / c) pow 5 * &q rpow (--(&9 / &4))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_OF_NUM_LE; PHI_LIMIT] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[RPOW_POS_LE;
     REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `--(&5 / &4) = &1 + --(&9 / &4)`] THEN
  ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;

let HUA_TERM_BOUND = prove
 (`?Ch. &0 <= Ch /\
        !N q. 1 <= q ==> norm(hua_term N q) <= Ch * &q rpow (--(&5 / &4))`,
  MP_TAC HTERM_ABS_DECAY THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Ch:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {a | a < q /\ coprime(a,q)}
                  (\a. norm(Cx(inv(&(phi q))) * hua_pcsum q a) pow 5)` THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[hua_term] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; NORM_EXPI; REAL_MUL_RID;
              REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Local densities over units.                                               *)
(* ------------------------------------------------------------------------- *)

let hua_loc = new_recursive_definition num_RECURSION
 `(hua_loc L 0 c = if L divides c then &1 else &0) /\
  (hua_loc L (SUC s) c =
     sum {x | x < L /\ coprime(x,L)}
       (\x. hua_loc L s (c + (L - 1) * x EXP 2)))`;;

let HUA_LOC_FOURIER = prove
 (`!L s c. 1 <= L
           ==> Cx(&L * hua_loc L s c) =
               vsum {a | a < L}
                 (\a. hua_pcsum L a pow s * expi(--(&c * &a / &L)))`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[hua_loc; complex_pow; COMPLEX_MUL_LID] THEN
    MP_TAC(SPECL [`L:num`; `--(&c)`] VSUM_EXPI_RESIDUES) THEN
    ASM_SIMP_TAC[INTEGER_NEG; INTEGER_CLOSED;
                 ARITH_RULE `1 <= L ==> ~(L = 0)`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[INTEGER_NEG; GSYM real_div] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[INTEGER_DIV_DIVIDES; ARITH_RULE `1 <= L ==> ~(L = 0)`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[hua_loc; GSYM SUM_LMUL] THEN
  SIMP_TAC[GSYM VSUM_CX; FINITE_COPRIME_RESIDUES] THEN
  ASM_SIMP_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_COPRIME_RESIDUES] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_COPRIME_RESIDUES] THEN
  SUBGOAL_THEN
   `vsum {x | x < L /\ coprime(x,L)}
         (\x. expi (--(&(c + (L - 1) * x EXP 2) * &a / &L))) =
    expi(--(&c * &a / &L)) * hua_pcsum L a`
  SUBST1_TAC THENL
   [REWRITE_TAC[hua_pcsum] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_COPRIME_RESIDUES] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM EXPI_ADD] THEN
    MATCH_MP_TAC EXPI_INTEGER_DIFF THEN
    SUBGOAL_THEN `&0 < &L` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
                 GSYM REAL_OF_NUM_SUB] THEN
    SUBGOAL_THEN
     `--((&c + (&L - &1) * &(x EXP 2)) * &a / &L) -
      (--(&c * &a / &L) + &a * &(x EXP 2) / &L) =
      --(&(x EXP 2) * &a)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &L` THEN CONV_TAC REAL_FIELD;
      SIMP_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[complex_pow] THEN CONV_TAC COMPLEX_RING);;

let CRT_VSUM2 = prove
 (`!m n (f:num->complex) g.
     coprime(m,n) /\ ~(m = 0) /\ ~(n = 0)
     ==> vsum {x | x < m * n} (\x. Cx(g(x MOD n)) * f(x MOD m)) =
         Cx(sum {b | b < n} g) * vsum {a | a < m} f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_EQ] THEN
  SIMP_TAC[RE_VSUM; IM_VSUM; FINITE_NUMSEG_LT; RE_MUL_CX; IM_MUL_CX] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `m:num`; `g:num->real`;
                   `\x. Re((f:num->complex) x)`] CRT_SUM2);
    MP_TAC(ISPECL [`n:num`; `m:num`; `g:num->real`;
                   `\x. Im((f:num->complex) x)`] CRT_SUM2)] THEN
  ASM_MESON_TAC[COPRIME_SYM]);;

let PERIODIC_MOD = prove
 (`!(f:num->A) L. ~(L = 0) /\ (!x. f(x + L) = f x) ==> !x. f x = f(x MOD L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k y. (f:num->A)(y + k * L) = f y` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[ADD_ASSOC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `L:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [CONJUNCT1 th]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]);;

let UNITS_PERIODIC_SUM = prove
 (`!(f:num->complex) d m.
     1 <= d /\ (!x. f(x + d) = f x)
     ==> vsum {r | r < d * m /\ coprime(r,d * m)} f =
         Cx(&(phi(d * m)) / &(phi d)) * vsum {r | r < d /\ coprime(r,d)} f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(phi d)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`m:num`,`m:num`) THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; LT; EMPTY_GSPEC; VSUM_CLAUSES; PHI_0;
                    real_div; REAL_MUL_LZERO; COMPLEX_MUL_LZERO;
                    COMPLEX_VEC_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THENL
   [ASM_SIMP_TAC[MULT_CLAUSES; REAL_DIV_REFL; REAL_LT_IMP_NZ;
                 COMPLEX_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` PRIME_FACTOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m1:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides]) THEN
  SUBGOAL_THEN `2 <= p /\ ~(m1 = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(p * m1 = 0)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m1:num`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * m1 < p * m1 ==> m1 < p * m1`) THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `d * p * m1 = (d * m1) * p:num` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = d * m1:num` THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. (f:num->complex)(x + L) = f x` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN SPEC_TAC(`m1:num`,`k:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[ADD_ASSOC];
    ALL_TAC] THEN
  ASM_CASES_TAC `p divides L` THENL
   [SUBGOAL_THEN `phi(L * p) = p * phi L` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[PHI_MUL_PRIME] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `vsum {r | r < L * p /\ coprime(r,L * p)} f =
      vsum {r | r < L * p}
           (\r. if coprime(r,L) then (f:num->complex) r else vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VSUM_RESTRICT_SET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:num` THEN
      ASM_CASES_TAC `r < L * p:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p divides L` THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\r. if coprime(r,L) then (f:num->complex) r else vec 0`;
      `L:num`; `p:num`] VSUM_PERIODIC) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:num` THEN REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[NUMBER_RULE `coprime(x + L:num,L) <=> coprime(x,L)`];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM VSUM_RESTRICT_SET] THEN
    SUBGOAL_THEN `{r | r IN {r | r < L} /\ coprime(r,L)} =
                  {r | r < L /\ coprime(r,L)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(L,p)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `phi(L * p) = (p - 1) * phi L` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[PHI_MUL_PRIME] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum {r | r < L * p /\ coprime(r,L * p)} f =
    vsum {r | r < L * p}
         (\r. Cx(if coprime(r MOD p,p) then &1 else &0) *
              (\a. if coprime(a,L) then (f:num->complex) a else vec 0)
              (r MOD L))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VSUM_RESTRICT_SET] THEN
    SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum {r | r < L * p}
                  (\r. if coprime(r,L * p) then (f:num->complex) r
                       else vec 0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM VSUM_RESTRICT_SET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COPRIME_LMOD] THEN
    SUBGOAL_THEN `coprime(r,L * p) <=> coprime(r,L) /\ coprime(r,p)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `coprime(L,p)` THEN CONV_TAC NUMBER_RULE; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:num->complex`; `L:num`] PERIODIC_MOD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    MAP_EVERY ASM_CASES_TAC [`coprime(r,L)`; `coprime(r,p)`] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO;
                    COMPLEX_VEC_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:num`; `p:num`;
                 `\a. if coprime(a,L) then (f:num->complex) a else vec 0`;
                 `\b. if coprime(b,p) then &1 else &0`] CRT_VSUM2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VSUM_RESTRICT_SET; GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{r | r IN {r | r < L} /\ coprime(r,L)} =
                {r | r < L /\ coprime(r,L)} /\
                {b | b IN {b | b < p} /\ coprime(b,p)} =
                {b | b < p /\ coprime(b,p)}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_COPRIME_RESIDUES; CARD_COPRIME_RESIDUES] THEN
  ASM_SIMP_TAC[PHI_PRIME; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div; REAL_MUL_ASSOC]);;

let HUA_PCSUM_SCALE = prove
 (`!d L b. 1 <= d /\ 1 <= L /\ d divides L
           ==> hua_pcsum L (b * (L DIV d)) = Cx(&(phi L) / &(phi d)) *
               hua_pcsum d b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides]) THEN
  SUBGOAL_THEN `~(d = 0) /\ ~(m = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `1 <= d * m` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT] THEN REWRITE_TAC[hua_pcsum] THEN
  SUBGOAL_THEN
   `!r. expi(&(b * m) * &(r EXP 2) / &(d * m)) =
        expi(&b * &(r EXP 2) / &d)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&d = &0) /\ ~(&m = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC UNITS_PERIODIC_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN BETA_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&b * &x / &d = &x * &b / &d`] THEN
  MATCH_MP_TAC EXPI_CONG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_EXP THEN CONV_TAC NUMBER_RULE);;

let HUA_LOC_SING = prove
 (`!L c. 1 <= L
         ==> vsum {d | d divides L} (\d. hua_term c d) =
             Cx(&L * hua_loc L 5 c / &(phi L) pow 5)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(phi L)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&(phi L)) pow 5 * vsum {d | d divides L} (\d. hua_term c d) =
    Cx(&L * hua_loc L 5 c)`
  MP_TAC THENL
   [ASM_SIMP_TAC[HUA_LOC_FOURIER] THEN
    MP_TAC(ISPECL [`\a. hua_pcsum L a pow 5 * expi(--(&c * &a / &L))`;
                   `L:num`] VSUM_GCD_GROUP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_DIVISORS] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`L:num`; `d:num`] DIVISOR_REFLECT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[hua_term] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_COPRIME_RESIDUES] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `b:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`d:num`; `L:num`; `b:num`] HUA_PCSUM_SCALE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `&0 < &(phi d)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
      MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `m = L DIV d` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> concl th = `d * m = L:num`)) THEN
    SUBGOAL_THEN `~(&d = &0) /\ ~(&m = &0)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN CONJ_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~(d * m = 0)` THEN ASM_REWRITE_TAC[MULT_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN `&c * &(b * m) / &(d * m) = &c * &b / &d` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      UNDISCH_TAC `~(&d = &0)` THEN UNDISCH_TAC `~(&m = &0)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM COMPLEX_POW_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(Cx(&(phi L)) pow 5 = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_EQ_0; CX_INJ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx(&L * hua_loc L 5 c / &(phi L) pow 5) =
                Cx(&L * hua_loc L 5 c) / Cx(&(phi L)) pow 5`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_POW; GSYM CX_DIV; CX_INJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `!z v w:complex. ~(z = Cx(&0)) /\ z * v = w ==> v = w / z`) THEN
  ASM_REWRITE_TAC[]);;

let HUA_LOC_CONG = prove
 (`!L s c c'. (c == c') (mod L) ==> hua_loc L s c = hua_loc L s c'`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[hua_loc] THENL
   [SUBGOAL_THEN `L divides c <=> L divides c'` (fun th -> REWRITE_TAC[th])
    THEN UNDISCH_TAC `(c:num == c') (mod L)` THEN CONV_TAC NUMBER_RULE;
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(c:num == c') (mod L)` THEN CONV_TAC NUMBER_RULE]);;

let CRT_UNITS_SUM2 = prove
 (`!m n (f:num->real) g.
     coprime(m,n) /\ ~(m = 0) /\ ~(n = 0)
     ==> sum {x | x < m * n /\ coprime(x,m * n)}
             (\x. f(x MOD m) * g(x MOD n)) =
         sum {a | a < m /\ coprime(a,m)} f *
         sum {b | b < n /\ coprime(b,n)} g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `n:num`;
                 `\a. if coprime(a,m) then (f:num->real) a else &0`;
                 `\b. if coprime(b,n) then (g:num->real) b else &0`]
    CRT_SUM2) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `{x:num | x < k /\ P x} = {x | x IN {x | x < k} /\ P
      x}`]
    THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COPRIME_LMOD] THEN
  SUBGOAL_THEN `coprime(x,m * n) <=> coprime(x,m) /\ coprime(x,n)`
  SUBST1_TAC THENL [CONV_TAC NUMBER_RULE; ALL_TAC] THEN
  MAP_EVERY ASM_CASES_TAC [`coprime(x,m)`; `coprime(x,n)`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]);;

let HUA_LOC_MUL = prove
 (`!s L1 L2 c.
     coprime(L1,L2) /\ ~(L1 = 0) /\ ~(L2 = 0)
     ==> hua_loc (L1 * L2) s c = hua_loc L1 s c * hua_loc L2 s c`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[hua_loc] THENL
   [SUBGOAL_THEN `L1 * L2 divides c <=> L1 divides c /\ L2 divides c`
    SUBST1_TAC THENL
     [UNDISCH_TAC `coprime(L1:num,L2)` THEN CONV_TAC NUMBER_RULE;
      MAP_EVERY ASM_CASES_TAC [`L1 divides c`; `L2 divides c`] THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!x. hua_loc L1 s (c + (L1 * L2 - 1) * x EXP 2) =
        hua_loc L1 s (c + (L1 - 1) * (x MOD L1) EXP 2) /\
        hua_loc L2 s (c + (L1 * L2 - 1) * x EXP 2) =
        hua_loc L2 s (c + (L2 - 1) * (x MOD L2) EXP 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC HUA_LOC_CONG THEN
    ASM_SIMP_TAC[WLOC_SHIFT_CONG] THEN
    SUBGOAL_THEN `L1 * L2 = L2 * L1:num` SUBST1_TAC THENL
     [ARITH_TAC; ASM_SIMP_TAC[WLOC_SHIFT_CONG]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L1:num`; `L2:num`;
                 `\y. hua_loc L1 s (c + (L1 - 1) * y EXP 2)`;
                 `\y. hua_loc L2 s (c + (L2 - 1) * y EXP 2)`]
                   CRT_UNITS_SUM2) THEN
  ASM_REWRITE_TAC[]);;

let HUA_LOC_1 = prove
 (`!s c. hua_loc 1 s c = &1`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[hua_loc; DIVIDES_1; COPRIME_1] THEN
  REWRITE_TAC[ARITH_RULE `x < 1 <=> x = 0`; SING_GSPEC; SUM_SING]);;

let HDEN_MULTIPLICATIVE = prove
 (`!s c. real_multiplicative (\L. &L * hua_loc L s c / &(phi L) pow s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MULTIPLICATIVE] THEN
  REWRITE_TAC[HUA_LOC_1; PHI_1; REAL_POW_ONE; REAL_DIV_1; REAL_MUL_LID] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HUA_LOC_MUL; PHI_MULTIPLICATIVE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_MUL; real_div; REAL_INV_MUL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Representations and unit solubility.                                      *)
(* ------------------------------------------------------------------------- *)

let HUA_LOC_POS = prove
 (`!L s c. &0 <= hua_loc L s c`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[hua_loc] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[FINITE_COPRIME_RESIDUES]]);;

let HUA_LOC_STEP_LOWER = prove
 (`!L s c x. x < L /\ coprime(x,L)
             ==> hua_loc L s (c + (L - 1) * x EXP 2) <= hua_loc L (SUC s) c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hua_loc] THEN
  MP_TAC(ISPECL [`\x. hua_loc L s (c + (L - 1) * x EXP 2)`;
                 `{x | x < L /\ coprime(x,L)}`; `x:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_COPRIME_RESIDUES; IN_ELIM_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= d ==> d = s - a ==> a <= s`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN
  SIMP_TAC[FINITE_DELETE; FINITE_COPRIME_RESIDUES; HUA_LOC_POS]);;

let HUA_LOC_REPR = prove
 (`!L s c y.
     ~(L = 0) /\ (!i. 1 <= i /\ i <= s ==> coprime(y i,L)) /\
     (nsum(1..s) (\i. y i EXP 2) == c) (mod L)
     ==> &1 <= hua_loc L s c`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[hua_loc] THENL
   [SUBGOAL_THEN `(L:num) divides c` (fun th -> REWRITE_TAC[th; REAL_LE_REFL])
     THEN
    UNDISCH_TAC `(nsum(1..0) (\i. y i EXP 2) == c) (mod L)` THEN
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH] THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  ABBREV_TAC `x0 = y(SUC s) MOD L` THEN
  SUBGOAL_THEN `x0 < L /\ coprime(x0,L)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN ASM_SIMP_TAC[MOD_LT_EQ; COPRIME_LMOD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= hua_loc L s (c + (L - 1) * x0 EXP 2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:num->num` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(nsum(1..SUC s) (\i. y i EXP 2) == c) (mod L)` THEN
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN
    MP_TAC(SPECL [`y(SUC s):num`; `L:num`] CONG_MOD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `2` o MATCH_MP CONG_EXP) THEN
    SUBGOAL_THEN `(L - 1) + 1 = L` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`nsum(1..s) (\i. y i EXP 2)`,`S:num`) THEN
    SPEC_TAC(`x0 EXP 2`,`X:num`) THEN SPEC_TAC(`y(SUC s) EXP 2`,`Y:num`) THEN
    SPEC_TAC(`L - 1`,`B:num`) THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `hua_loc L s (c + (L - 1) * x0 EXP 2)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM hua_loc] THEN MATCH_MP_TAC HUA_LOC_STEP_LOWER THEN
  ASM_REWRITE_TAC[]);;

let HLOC4_REPR = prove
 (`!L c y1 y2 y3 y4.
     ~(L = 0) /\ coprime(y1,L) /\ coprime(y2,L) /\ coprime(y3,L) /\
     coprime(y4,L) /\
     (y1 EXP 2 + y2 EXP 2 + y3 EXP 2 + y4 EXP 2 == c) (mod L)
     ==> &1 <= hua_loc L 4 c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HUA_LOC_REPR THEN
  EXISTS_TAC `\i. if i = 1 then y1 else if i = 2 then y2
                  else if i = 3 then y3 else y4:num` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `(y1 EXP 2 + y2 EXP 2 + y3 EXP 2 + y4 EXP 2 == c) (mod L)` THEN
  REWRITE_TAC[ADD_ASSOC]);;

let WARING_LOC_POS_REPR = prove
 (`!k L s c. &0 < waring_loc k L s c
             ==> ?y. (nsum(1..s) (\i. y i EXP k) == c) (mod L)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[waring_loc] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN DISCH_TAC THEN
    EXISTS_TAC `\i:num. 0` THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH] THEN
    UNDISCH_TAC `L divides c` THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?x. x < L /\ &0 < waring_loc k L s (c + (L - 1) * x EXP k)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[] `(~(?x:num. P x) ==> F) ==> ?x. P x`) THEN
    DISCH_TAC THEN
    UNDISCH_TAC
      `&0 < sum {x | x < L} (\x. waring_loc k L s (c + (L - 1) * x EXP k))`
    THEN REWRITE_TAC[REAL_NOT_LT] THEN
    TRANS_TAC REAL_LE_TRANS `sum {x | x < L:num} (\x. &0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_NOT_LT];
      REWRITE_TAC[SUM_0; REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c + (L - 1) * x EXP k`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y:num->num`) THEN
  EXISTS_TAC `\i. if i = SUC s then x else (y:num->num) i` THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN
  SUBGOAL_THEN
   `nsum(1..s) (\i. (if i = SUC s then x else (y:num->num) i) EXP k) =
    nsum(1..s) (\i. y i EXP k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(L - 1) + 1 = L` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(nsum(1..s) (\i. y i EXP k) == c + (L - 1) * x EXP k) (mod L)`
  THEN SPEC_TAC(`nsum(1..s) (\i. y i EXP k)`,`S:num`) THEN
  SPEC_TAC(`x EXP k`,`X:num`) THEN SPEC_TAC(`L - 1`,`B:num`) THEN
  CONV_TAC NUMBER_RULE);;

let TWO_SQUARES_MOD = prove
 (`!p c. prime p ==> ?x y. (x EXP 2 + y EXP 2 == c) (mod p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `2`; `2`; `c:num`] SOLUBLE_GROWTH) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`2`; `p:num`; `2`; `c:num`] WARING_LOC_POS_REPR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:num->num`) THEN
  MAP_EVERY EXISTS_TAC [`(y:num->num) 1`; `(y:num->num) 2`] THEN
  UNDISCH_TAC `(nsum(1..2) (\i. y i EXP 2) == c) (mod p)` THEN
  REWRITE_TAC[num_CONV `2`; NSUM_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[NSUM_SING_NUMSEG]);;

let FOUR_UNIT_SQUARES = prove
 (`!p c. prime p /\ 7 <= p ==> &1 <= hua_loc p 4 c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ (p - 1) + 1 = p` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. 0 < x /\ x < 7 ==> coprime(x,p)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PRIME_COPRIME_LT THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`5`; `1`; `p:num`] CONG_SOLVE) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:num`) THEN
  SUBGOAL_THEN `coprime(1,p) /\ coprime(3 * w,p) /\ coprime(4 * w,p)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `coprime(w,p)` ASSUME_TAC THENL
     [UNDISCH_TAC `(5 * w == 1) (mod p)` THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[COPRIME_LMUL; COPRIME_1] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((3 * w) EXP 2 + (4 * w) EXP 2 == 1) (mod p)` ASSUME_TAC THENL
   [UNDISCH_TAC `(5 * w == 1) (mod p)` THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `c + 2 * (p - 1)`] TWO_SQUARES_MOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` (X_CHOOSE_TAC `y:num`)) THEN
  ASM_CASES_TAC `p divides x` THEN ASM_CASES_TAC `p divides y` THENL
   [MATCH_MP_TAC HLOC4_REPR THEN
    MAP_EVERY EXISTS_TAC [`3 * w`; `4 * w`; `3 * w`; `4 * w`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x EXP 2 + y EXP 2 == c + 2 * (p - 1)) (mod p)` THEN
    UNDISCH_TAC `((3 * w) EXP 2 + (4 * w) EXP 2 == 1) (mod p)` THEN
    UNDISCH_TAC `p divides x` THEN UNDISCH_TAC `p divides y` THEN
    UNDISCH_TAC `(p - 1) + 1 = p` THEN
    SPEC_TAC(`(3 * w) EXP 2`,`A:num`) THEN
      SPEC_TAC(`(4 * w) EXP 2`,`B:num`) THEN
    SPEC_TAC(`p - 1`,`P1:num`) THEN CONV_TAC NUMBER_RULE;
    MATCH_MP_TAC HLOC4_REPR THEN
    MAP_EVERY EXISTS_TAC [`y:num`; `3 * w`; `4 * w`; `1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
      ALL_TAC] THEN
    UNDISCH_TAC `(x EXP 2 + y EXP 2 == c + 2 * (p - 1)) (mod p)` THEN
    UNDISCH_TAC `((3 * w) EXP 2 + (4 * w) EXP 2 == 1) (mod p)` THEN
    UNDISCH_TAC `p divides x` THEN UNDISCH_TAC `(p - 1) + 1 = p` THEN
    SPEC_TAC(`(3 * w) EXP 2`,`A:num`) THEN
      SPEC_TAC(`(4 * w) EXP 2`,`B:num`) THEN
    SPEC_TAC(`p - 1`,`P1:num`) THEN CONV_TAC NUMBER_RULE;
    MATCH_MP_TAC HLOC4_REPR THEN
    MAP_EVERY EXISTS_TAC [`x:num`; `3 * w`; `4 * w`; `1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
      ALL_TAC] THEN
    UNDISCH_TAC `(x EXP 2 + y EXP 2 == c + 2 * (p - 1)) (mod p)` THEN
    UNDISCH_TAC `((3 * w) EXP 2 + (4 * w) EXP 2 == 1) (mod p)` THEN
    UNDISCH_TAC `p divides y` THEN UNDISCH_TAC `(p - 1) + 1 = p` THEN
    SPEC_TAC(`(3 * w) EXP 2`,`A:num`) THEN
      SPEC_TAC(`(4 * w) EXP 2`,`B:num`) THEN
    SPEC_TAC(`p - 1`,`P1:num`) THEN CONV_TAC NUMBER_RULE;
    MATCH_MP_TAC HLOC4_REPR THEN
    MAP_EVERY EXISTS_TAC [`x:num`; `y:num`; `1`; `1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
      ALL_TAC] THEN
    UNDISCH_TAC `(x EXP 2 + y EXP 2 == c + 2 * (p - 1)) (mod p)` THEN
    UNDISCH_TAC `(p - 1) + 1 = p` THEN
    SPEC_TAC(`p - 1`,`P1:num`) THEN CONV_TAC NUMBER_RULE]);;

let HUA_CONG_24 = prove
 (`!c. (c == 5) (mod 24) ==> c MOD 8 = 5 /\ c MOD 3 = 2`,
  GEN_TAC THEN REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`c:num`; `24`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN CONJ_TAC THEN
  MATCH_MP_TAC MOD_UNIQ THENL
   [EXISTS_TAC `3 * c DIV 24`; EXISTS_TAC `8 * c DIV 24 + 1`] THEN
  ARITH_TAC);;

let FOUR_UNIT_SQUARES_5 = prove
 (`!c. &1 <= hua_loc 5 4 c`,
  GEN_TAC THEN
  SUBGOAL_THEN `c MOD 5 = 0 \/ c MOD 5 = 1 \/ c MOD 5 = 2 \/ c MOD 5 = 3 \/
                c MOD 5 = 4` MP_TAC THENL
   [MP_TAC(SPECL [`c:num`; `5`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `coprime(1,5) /\ coprime(2,5)` STRIP_ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV COPRIME_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC HLOC4_REPR THENL
   [MAP_EVERY EXISTS_TAC [`1`; `1`; `2`; `2`];
    MAP_EVERY EXISTS_TAC [`2`; `2`; `2`; `2`];
    MAP_EVERY EXISTS_TAC [`1`; `1`; `1`; `2`];
    MAP_EVERY EXISTS_TAC [`1`; `2`; `2`; `2`];
    MAP_EVERY EXISTS_TAC [`1`; `1`; `1`; `1`]] THEN
  ASM_REWRITE_TAC[ARITH_EQ; CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let HUA_SOLUBLE = prove
 (`!p c. prime p /\ (c == 5) (mod 24)
         ==> &1 <= hua_loc (p EXP (2 * index p 2 + 1)) 4
                        (c + (p EXP (2 * index p 2 + 1) - 1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HUA_CONG_24) THEN
  ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[INDEX_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC HLOC4_REPR THEN MAP_EVERY EXISTS_TAC [`1`; `1`; `1`; `1`] THEN
    REWRITE_TAC[COPRIME_1; ARITH_EQ; CONG] THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `index p 2 = 0` SUBST1_TAC THENL
   [REWRITE_TAC[INDEX_EQ_0] THEN DISJ2_TAC THEN DISJ2_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EXP_1] THEN
  ASM_CASES_TAC `p = 3` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC HLOC4_REPR THEN MAP_EVERY EXISTS_TAC [`1`; `1`; `1`; `1`] THEN
    REWRITE_TAC[COPRIME_1; ARITH_EQ; CONG] THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `p = 5` THENL
   [ASM_REWRITE_TAC[FOUR_UNIT_SQUARES_5]; ALL_TAC] THEN
  MATCH_MP_TAC FOUR_UNIT_SQUARES THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p = 0 \/ p = 1 \/ p = 4 \/ p = 6` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN UNDISCH_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV PRIME_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hensel lifting over units.                                                *)
(* ------------------------------------------------------------------------- *)

let SUM_MOD_PERIODIC_UNITS = prove
 (`!(f:num->real) L L'.
     ~(L = 0) /\ ~(L' = 0) /\ L divides L' /\
     (!x. coprime(x,L') <=> coprime(x,L))
     ==> sum {x | x < L' /\ coprime(x,L')} (\x. f(x MOD L)) =
         &(L' DIV L) * sum {y | y < L /\ coprime(y,L)} f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`L':num`; `L:num`] DIVISOR_REFLECT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. if coprime(y,L) then (f:num->real) y else &0`;
                 `L:num`; `L' DIV L`] SUM_MOD_PERIODIC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COPRIME_LMOD] THEN
  REWRITE_TAC[SET_RULE `{x:num | x < k /\ P x} = {x | x IN {x | x < k} /\ P
      x}`]
    THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN DISCH_THEN SUBST1_TAC THEN
  REFL_TAC);;

let HUA_LOC_REDUCE = prove
 (`!r L L' m0.
     ~(L = 0) /\ ~(L' = 0) /\ L divides L' /\
     (!x. coprime(x,L') <=> coprime(x,L))
     ==> sum {m | m < L'}
             (\m. if (m == m0) (mod L) then hua_loc L' r m else &0) =
         &(L' DIV L) pow r * hua_loc L r m0`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[hua_loc; real_pow; REAL_MUL_LID] THEN
    TRANS_TAC EQ_TRANS
     `sum {m | m < L'}
          (\m. if m = 0 then (if (L:num) divides m0 then &1 else &0) else &0)`
            THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THENL
       [REWRITE_TAC[NUMBER_RULE `(0 == m0) (mod L) <=> (L:num) divides m0`];
        SUBGOAL_THEN `~((L':num) divides m)` (fun th -> REWRITE_TAC[th]) THENL
         [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
          COND_CASES_TAC THEN REWRITE_TAC[]]];
      REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`]];
    ALL_TAC] THEN
  REWRITE_TAC[hua_loc] THEN
  SUBGOAL_THEN
   `!m. (if (m == m0) (mod L)
         then sum {x | x < L' /\ coprime(x,L')}
                  (\x. hua_loc L' r (m + (L' - 1) * x EXP 2))
         else &0) =
        sum {x | x < L' /\ coprime(x,L')}
            (\x. if (m == m0) (mod L)
                 then hua_loc L' r (m + (L' - 1) * x EXP 2) else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUM_0]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_COPRIME_RESIDUES] THEN
  DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum {x | x < L' /\ coprime(x,L')}
        (\x. &(L' DIV L) pow r *
             hua_loc L r (m0 + (L - 1) * (x MOD L) EXP 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
    ABBREV_TAC `t = (L' - 1) * x EXP 2` THEN
    SUBGOAL_THEN
     `!m. (if (m == m0) (mod L) then hua_loc L' r (m + t) else &0) =
          (\y. if (y == m0 + t) (mod L) then hua_loc L' r y else &0)
          ((m + t) MOD L')`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `((m + t) MOD L' == m0 + t) (mod L) <=> (m == m0) (mod L)`
      SUBST1_TAC THENL
       [MP_TAC(SPECL [`m + t:num`; `L':num`] CONG_MOD) THEN
        UNDISCH_TAC `(L:num) divides L'` THEN CONV_TAC NUMBER_RULE;
        ALL_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC HUA_LOC_CONG THEN
      MESON_TAC[CONG_MOD; CONG_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\y. if (y == m0 + t) (mod L) then hua_loc L' r y else &0`;
                   `L':num`; `t:num`] SUM_SHIFT_MOD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`L:num`; `L':num`; `m0 + t:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC HUA_LOC_CONG THEN EXPAND_TAC "t" THEN
    MATCH_MP_TAC SHIFT_CONG_DIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; real_pow] THEN
  MP_TAC(ISPECL [`\y. hua_loc L r (m0 + (L - 1) * y EXP 2)`; `L:num`; `L':num`]
    SUM_MOD_PERIODIC_UNITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let HUA_LOC_PEEL_LOWER = prove
 (`!L s c P.
     ~(L = 0) /\
     (!m. m < L /\ P m
          ==> ?x. x < L /\ coprime(x,L) /\
                  ((c + (L - 1) * x EXP 2) == m) (mod L))
     ==> sum {m | m < L} (\m. if P m then hua_loc L s m else &0)
         <= hua_loc L (SUC s) c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hua_loc] THEN
  SUBGOAL_THEN
   `!x. hua_loc L s (c + (L - 1) * x EXP 2) =
        hua_loc L s ((c + (L - 1) * x EXP 2) MOD L)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC HUA_LOC_CONG THEN MESON_TAC[CONG_MOD; CONG_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (c + (L - 1) * x EXP 2) MOD L`;
                 `\x. hua_loc L s ((c + (L - 1) * x EXP 2) MOD L)`;
                 `{x | x < L /\ coprime(x,L)}`; `{m | m < L:num}`]
    SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_COPRIME_RESIDUES; SUBSET; FORALL_IN_IMAGE;
                 IN_ELIM_THM; MOD_LT_EQ];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {x | (x < L /\ coprime(x,L)) /\ (c + (L - 1) * x EXP 2) MOD L = m}
        (\x. hua_loc L s m)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM]] THEN
  SUBGOAL_THEN
   `FINITE {x | (x < L /\ coprime(x,L)) /\ (c + (L - 1) * x EXP 2) MOD L = m}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x | x < L:num}` THEN
    SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; HUA_LOC_POS]] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[HUA_LOC_POS; REAL_OF_NUM_LE] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num` THEN
  SIMP_TAC[CONG] THEN ASM_SIMP_TAC[MOD_LT]);;

let HUA_LOC_PRIMEPOW_LOWER = prove
 (`!s p g h c.
     prime p /\ 2 * index p 2 + 1 <= g /\ g <= h /\
     &1 <= hua_loc (p EXP g) s (c + (p EXP g - 1))
     ==> &(p EXP (h - g)) pow s <= hua_loc (p EXP h) (SUC s) c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p EXP g = 0) /\ ~(p EXP h = 0) /\ p EXP g divides p EXP h`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ; DIVIDES_EXP_LE_IMP]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. coprime(x,p EXP h) <=> coprime(x,p EXP g)` ASSUME_TAC
  THENL
   [GEN_TAC THEN REWRITE_TAC[COPRIME_REXP] THEN
    SUBGOAL_THEN `~(h = 0) /\ ~(g = 0)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p EXP h`; `s:num`; `c:num`;
                 `\m. (m == c + (p EXP g - 1)) (mod (p EXP g))`]
    HUA_LOC_PEEL_LOWER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `2`; `1`; `c + (p EXP h - 1) * m`; `g:num`]
      HENSEL_ITER) THEN
    ASM_REWRITE_TAC[EXP_ONE; DIVIDES_ONE; ARITH_RULE `1 <= 2`] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
      SUBGOAL_THEN `(p EXP g - 1) + 1 = p EXP g /\ (p EXP h - 1) + 1 = p EXP h`
      MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(m == c + p EXP g - 1) (mod (p EXP g))` THEN
      UNDISCH_TAC `p EXP g divides p EXP h` THEN
      SPEC_TAC(`p EXP g - 1`,`A:num`) THEN SPEC_TAC(`p EXP h - 1`,`B:num`)
        THEN
      SPEC_TAC(`p EXP g`,`G:num`) THEN SPEC_TAC(`p EXP h`,`H:num`) THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `h:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v MOD p EXP h` THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COPRIME_REXP] THEN DISJ1_TAC THEN
      SUBGOAL_THEN `coprime(v,p) /\ p divides p EXP h` MP_TAC THENL
       [CONJ_TAC THENL
         [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
          MATCH_MP_TAC DIVIDES_REXP THEN REWRITE_TAC[DIVIDES_REFL] THEN
          ASM_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(SPECL [`v:num`; `p EXP h`] CONG_MOD) THEN
      SPEC_TAC(`p EXP h`,`H:num`) THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MP_TAC(SPECL [`v:num`; `p EXP h`] CONG_MOD) THEN
    DISCH_THEN(MP_TAC o SPEC `2` o MATCH_MP CONG_EXP) THEN
    SUBGOAL_THEN `(p EXP h - 1) + 1 = p EXP h` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(v EXP 2 == c + (p EXP h - 1) * m) (mod (p EXP h))` THEN
    SPEC_TAC(`(v MOD p EXP h) EXP 2`,`Y:num`) THEN
    SPEC_TAC(`v EXP 2`,`X:num`) THEN
    SPEC_TAC(`p EXP h - 1`,`B:num`) THEN SPEC_TAC(`p EXP h`,`H:num`) THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPECL [`s:num`; `p EXP g`; `p EXP h`; `c + (p EXP g - 1)`]
    HUA_LOC_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `p EXP h DIV p EXP g = p EXP (h - g)` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    ASM_SIMP_TAC[ADD_CLAUSES; GSYM EXP_ADD; SUB_ADD; LT_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* The singular series.                                                      *)
(* ------------------------------------------------------------------------- *)

let HUA_TERM_1 = prove
 (`!N. hua_term N 1 = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[hua_term; hua_pcsum; PHI_1] THEN
  SUBGOAL_THEN `!P. {a | a < 1 /\ P a} = if P 0 then {0} else {}`
  (fun th -> REWRITE_TAC[th; COPRIME_1]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; NOT_IN_EMPTY;
                    ARITH_RULE `a < 1 <=> a = 0`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_SING; REAL_MUL_LZERO; real_div; REAL_MUL_RZERO;
              REAL_NEG_0; EXPI_0; REAL_INV_1; COMPLEX_MUL_LID;
              COMPLEX_POW_ONE; COMPLEX_MUL_RID]);;

let HLOCAL_FACTOR_SUM = prove
 (`!c p e. prime p
           ==> Cx(&(p EXP e) * hua_loc (p EXP e) 5 c / &(phi(p EXP e)) pow 5) =
               Cx(&1) + vsum(1..e) (\j. hua_term c (p EXP j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ 2 <= p` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; PRIME_GE_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`p EXP e`; `c:num`] HUA_LOC_SING) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `{d | d divides p EXP e} = IMAGE (\j. p EXP j) (0..e)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0;
                 DIVIDES_PRIMEPOW] THEN MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[EQ_PRIMEPOW];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; EXP; HUA_TERM_1; ADD_CLAUSES]);;

let HLOCAL_FACTOR_LARGE = prove
 (`!c p e Ch d.
     prime p /\ &0 <= Ch /\ &0 < d /\
     (!q. 1 <= q ==> norm(hua_term c q) <= Ch * &q rpow (--(&1 + d)))
     ==> &1 - &2 * Ch * &p rpow (--(&1 + d)) <=
         &(p EXP e) * hua_loc (p EXP e) 5 c / &(phi(p EXP e)) pow 5`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = &p rpow (--(&1 + d))` THEN
  SUBGOAL_THEN `&0 <= x /\ x <= &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; ASSUME `&0 < &p`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&p rpow (--(&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_MONO_LE THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[RPOW_NEG; RPOW_POW; REAL_POW_1; real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:num`; `p:num`; `e:num`] HLOCAL_FACTOR_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
  REWRITE_TAC[RE_CX; RE_ADD] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs y <= &2 * Ch * x ==> &1 - &2 * Ch * x <= &1 + y`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vsum(1..e) (\j. hua_term c (p EXP j)))` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..e) (\j. Ch * x pow j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Ch * &(p EXP j) rpow (--(&1 + d))` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      EXPAND_TAC "x" THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_POW; RPOW_NUM_POW; REAL_LE_REFL]];
    REWRITE_TAC[SUM_LMUL] THEN
    MP_TAC(SPECL [`x:real`; `e:num`] GEOM_SUM_LE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `Ch * sum(1..e) (\j. x pow j) <= Ch * (&2 * x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]);;

let HLOCAL_FACTOR_SMALL = prove
 (`!p c h.
     prime p /\ (c == 5) (mod 24) /\ 2 * index p 2 + 1 <= h
     ==> inv(&p pow (4 * (2 * index p 2 + 1))) <=
         &(p EXP h) * hua_loc (p EXP h) 5 c / &(phi(p EXP h)) pow 5`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `g = 2 * index p 2 + 1` THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(SPECL [`4`; `p:num`; `g:num`; `h:num`; `c:num`]
    HUA_LOC_PRIMEPOW_LOWER) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC HUA_SOLUBLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC 4 = 5`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &(phi(p EXP h)) /\ &(phi(p EXP h)) <= &p pow h`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
      MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0];
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; PHI_LIMIT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(phi(p EXP h)) pow 5` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 < &p pow g` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&p pow (4 * g)) * (&p pow h) pow 5` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `d = h - g:num` THEN
  SUBGOAL_THEN `h = g + d:num` SUBST_ALL_TAC THENL [ASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(&p pow (4 * g)) * (&p pow (g + d)) pow 5 =
    &(p EXP (g + d)) * &(p EXP d) pow 4`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_POW_ADD] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
    UNDISCH_TAC `&0 < &p pow g` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]);;

let HUA_SING_LOWER = prove
 (`?c0 Q0. &0 < c0 /\
           !N Q. (N == 5) (mod 24) /\ Q0 <= Q ==> c0 <= Re(hua_sing N Q)`,
  ABBREV_TAC `d = &1 / &4` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC HUA_TERM_BOUND THEN
  REWRITE_TAC[REAL_ARITH `--(&5 / &4) = --(&1 + &1 / &4)`] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cw:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d:real`; `d / (&4 * (Cw + &1))`] RPOW_NEG_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `P0:num` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `c1 = product {p | prime p /\ p <= P0}
                     (\p. inv(&p pow (4 * (2 * index p 2 + 1))))` THEN
  SUBGOAL_THEN `&0 < c1` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
    REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `~(p = 0) ==> 0 < p`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `c1 * d / (&4 * (Cw + &1))`] RPOW_NEG_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `Q1:num` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `c1 / &4` THEN EXISTS_TAC `P0 + Q1:num` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `Q:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `L = FACT Q EXP 3` THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[EXP_EQ_0; FACT_NZ]; ALL_TAC] THEN
  ABBREV_TAC `f = \n. &n * hua_loc n 5 N / &(phi n) pow 5` THEN
  SUBGOAL_THEN `real_multiplicative f` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[HDEN_MULTIPLICATIVE]; ALL_TAC] THEN
  MP_TAC(SPECL [`Q:num`; `3`] FACT_POW_PRIMES) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= 3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `L:num`] REAL_MULTIPLICATIVE_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1 / &2 <= (f:num->real) L` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{p | prime p /\ p <= Q} =
      {p | prime p /\ p <= P0} UNION {p | prime p /\ P0 < p /\ p <= Q}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `x:num` THEN ASM_CASES_TAC `prime x` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `P0 + Q1 <= Q:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `FINITE {p | prime p /\ P0 < p /\ p <= Q}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | prime p /\ p <= Q}` THEN
      REWRITE_TAC[FINITE_ATMOST; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_UNION o rand o snd) THEN
    ASM_REWRITE_TAC[FINITE_ATMOST] THEN ANTS_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY]
      THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `c / &2 = c * &1 / &2`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXPAND_TAC "c1" THEN MATCH_MP_TAC PRODUCT_LE THEN
        REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
        X_GEN_TAC `p:num` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
          REWRITE_TAC[REAL_POS];
          ALL_TAC] THEN
        EXPAND_TAC "f" THEN BETA_TAC THEN MATCH_MP_TAC HLOCAL_FACTOR_SMALL THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`p:num`; `2`] INDEX_LT_SELF) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o
          check (fun th -> is_forall(concl th) &&
                           can (find_term ((=) `index p L`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `1 <= 2`] THEN ARITH_TAC;
      REAL_ARITH_TAC;
      ABBREV_TAC `B = {p | prime p /\ P0 < p /\ p <= Q}` THEN
        SUBGOAL_THEN `!p. p IN B ==> &0 <= &2 * Cw * &p rpow (--(&1 + d)) /\
                                     &2 * Cw * &p rpow (--(&1 + d)) <= &1`
        ASSUME_TAC THENL
         [EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
          X_GEN_TAC `p:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `&0 < &p /\ &1 <= &p` STRIP_ASSUME_TAC THENL
           [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
            ALL_TAC] THEN
          CONJ_TAC THENL
           [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
            ASM_SIMP_TAC[REAL_POS; RPOW_POS_LE; REAL_LT_IMP_LE];
            ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2 * Cw * d / (&4 * (Cw + &1))` THEN CONJ_TAC THENL
           [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&p rpow (--d)` THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
              FIRST_X_ASSUM(MATCH_MP_TAC o
                check (fun th -> can (find_term ((=) `d / (&4 * (Cw + &1))`))
                                 (concl th))) THEN
              ASM_ARITH_TAC];
            ALL_TAC] THEN
          SUBGOAL_THEN `d <= &1` ASSUME_TAC THENL
           [EXPAND_TAC "d" THEN REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `&2 * Cw * d / (&4 * (Cw + &1)) = (Cw * d) / (&2 * (Cw +
            &1))`
          SUBST1_TAC THENL
           [UNDISCH_TAC `&0 <= Cw` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
                       REAL_ARITH `&0 <= Cw ==> &0 < &2 * (Cw + &1)`] THEN
          SUBGOAL_THEN `Cw * d <= Cw * &1` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
             ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
      SUBGOAL_THEN `FINITE(B:num->bool)` ASSUME_TAC THENL
         [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `product B (\p. &1 - &2 * Cw * &p rpow (--(&1 + d)))` THEN
        CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&1 - sum B (\p. &2 * Cw * &p rpow (--(&1 + d)))` THEN
          CONJ_TAC THENL
           [ALL_TAC;
            MATCH_MP_TAC PRODUCT_ONE_MINUS THEN ASM_SIMP_TAC[]] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= &1 / &2 ==> &1 / &2 <= &1 - x`) THEN
          REWRITE_TAC[SUM_LMUL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2 * Cw * (&P0 rpow (--d) / d)` THEN CONJ_TAC THENL
           [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
            MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC `sum(P0+1..Q) (\n. &n rpow (--(d + &1)))` THEN
            CONJ_TAC THENL
             [REWRITE_TAC[REAL_ARITH `--(&1 + d) = --(d + &1)`] THEN
              MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
              SIMP_TAC[FINITE_NUMSEG; RPOW_POS_LE; REAL_POS] THEN
              EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG]
                THEN
              ARITH_TAC;
              MATCH_MP_TAC SUM_RPOW_TAIL THEN ASM_REWRITE_TAC[]];
            ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2 * Cw * ((d / (&4 * (Cw + &1))) / d)` THEN CONJ_TAC
            THENL
           [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
            ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o
              check (fun th -> can (find_term ((=) `d / (&4 * (Cw + &1))`))
                               (concl th) && is_forall(concl th))) THEN
            ARITH_TAC;
            ALL_TAC] THEN
        SUBGOAL_THEN `&2 * Cw * ((d / (&4 * (Cw + &1))) / d) = Cw / (&2 * (Cw +
          &1))`
          SUBST1_TAC THENL
           [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 <= Cw` THEN
            CONV_TAC REAL_FIELD;
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
                         REAL_ARITH `&0 <= Cw ==> &0 < &2 * (Cw + &1)`] THEN
            ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o
            check (fun th -> can (find_term ((=) `B:num->bool`)) (concl th) &&
                             is_forall(concl th))) THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        EXPAND_TAC "f" THEN BETA_TAC THEN MATCH_MP_TAC HLOCAL_FACTOR_LARGE THEN
        UNDISCH_TAC `(p:num) IN B` THEN EXPAND_TAC "B" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`L:num`; `N:num`] HUA_LOC_SING) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&L * hua_loc L 5 N / &(phi L) pow 5 = (f:num->real) L`
  SUBST1_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `D = {m:num | m divides L /\ Q < m}` THEN
  SUBGOAL_THEN `FINITE(D:num->bool) /\ D SUBSET (Q+1..L)` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{m:num | m divides L}` THEN
      SIMP_TAC[FINITE_DIVISORS; ASSUME `~(L = 0)`] THEN
      SIMP_TAC[SUBSET; IN_ELIM_THM];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `{m:num | m divides L} = (1..Q) UNION D` SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM;
                                     IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(m = 0)` MP_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `0 divides (L:num)` THEN ASM_REWRITE_TAC[DIVIDES_ZERO];
        ARITH_TAC];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "L" THEN MATCH_MP_TAC DIVIDES_TRANS THEN
      EXISTS_TAC `FACT Q` THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIVIDES_FACT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC DIVIDES_REXP THEN REWRITE_TAC[DIVIDES_REFL] THEN
        ARITH_TAC]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_UNION o lhand o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [EXPAND_TAC "D" THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_NUMSEG;
                NOT_IN_EMPTY] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM hua_sing] THEN DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
  REWRITE_TAC[RE_ADD; RE_CX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(Re(vsum D (\d. hua_term N d))) <= c1 / &4` MP_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vsum D (\d. hua_term N d))` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum D (\q. Cw * &q rpow (--(&1 + d)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cw * (&Q rpow (--d) / d)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(Q+1..L) (\n. &n rpow (--(d + &1)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `--(&1 + d) = --(d + &1)`] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; RPOW_POS_LE; REAL_POS];
      MATCH_MP_TAC SUM_RPOW_TAIL THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cw * ((c1 * d / (&4 * (Cw + &1))) / d)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      check (fun th -> can (find_term ((=) `c1 * d / (&4 * (Cw + &1))`))
                       (concl th) && is_forall(concl th))) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cw * ((c1 * d / (&4 * (Cw + &1))) / d) =
                c1 / &4 * (Cw / (Cw + &1))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 <= Cw` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= Cw ==> &0 < Cw + &1`] THEN
  REAL_ARITH_TAC);;
