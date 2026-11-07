(* ========================================================================= *)
(* The unit equation a u + b v = e in a fixed order.                         *)
(*                                                                           *)
(* Purpose: for fixed order elements a, b, e that do not vanish at index 1   *)
(* (hence at no conjugate, NF_ORDER_ZERO) the logarithms of the conjugates   *)
(* of all units u with a u + b v = e (v a unit) are bounded, hence u 1       *)
(* lies in a finite set (Northcott). Route: let k0 be the conjugate where    *)
(* the norm of u is smallest and m0 = -log of that norm. The logs of the     *)
(* conjugates of a unit sum to 0, so m0 >= 0 and every abs log of a          *)
(* conjugate of u is at most n m0. At k0, E = -a u / e satisfies             *)
(* |E| exp(m0) <= K and 1 + E = (b / e) v. The logs of the conjugates of v   *)
(* are at most n (log 2K + n m0), so bounded generation writes v as a        *)
(* product of powers of a fixed finite set S of units with exponent sum      *)
(* linear in m0. Then clog(1 + E) is a non-zero linear form in the fixed     *)
(* logarithms clog(b k0 / e k0), 2 pi ii and clog(s k0), s in S, with        *)
(* integer coefficients at most 2 + nsum mm; BAKER_FELDMAN in the form       *)
(* BAKER_ONE_PLUS_E (uniformly in k0 in 1..n) gives                          *)
(* exp(m0) <= 2 K (b0 + c0 m0)^C, and POLYLOG_BOUND bounds m0.               *)
(*                                                                           *)
(* Main results: NF_UNIT_EQUATION_LOG_BOUND, NF_UNIT_EQUATION.               *)
(*                                                                           *)
(* Uses: Baker/thue.ml (BAKER_ONE_PLUS_E, NF_ORDER_ALGEBRAIC),               *)
(* Baker/lemmas.ml (POLYLOG_BOUND and other generic lemmas),                 *)
(* Baker/nf_units.ml (NF_UNITS_BOUNDED_GENERATION, NF_UNIT_LOG_SUM),         *)
(* Baker/nf_order.ml (NF_ORDER_ZERO), Baker/ant_bridge_nf.ml                 *)
(* (NF_ORDER_NORTHCOTT), Baker/bridge.ml (ALGEBRAIC_NUMBER_DIV),             *)
(* Baker/nf_defs.ml (NF_DATA_1_IN).                                          *)
(* ========================================================================= *)

needs "Baker/thue.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary facts.                                                         *)
(* ------------------------------------------------------------------------- *)

let NF_UNITEQ_NONZERO = prove
 (`!n c r (a:num->complex) k.
        nf_data n c r /\ nf_order n r a /\ ~(a 1 = Cx(&0)) /\ k IN 1..n
        ==> ~(a k = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  ASM_MESON_TAC[NF_ORDER_ZERO]);;

let NF_UNITEQ_SUM_ZERO_ABS = prove
 (`!n (f:num->real) t.
        1 <= n /\ sum(1..n) f = &0 /\ (!k. k IN 1..n ==> f k <= t)
        ==> &0 <= t /\ !k. k IN 1..n ==> abs(f k) <= &n * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1..n`; `f:num->real`; `t:real`] SUM_BOUND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&0`; `t:real`; `&n`] REAL_LE_LMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `1..n`; `k:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_SUB_LZERO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(1..n) DELETE k`; `f:num->real`; `t:real`] SUM_BOUND) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE; FINITE_NUMSEG; CARD_NUMSEG_1] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 * t <= &n * t /\ &(n - 1) * t <= &n * t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:num->real) k <= t` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let NF_UNITEQ_CONSTANTS = prove
 (`!n (a:num->complex) b e.
        ?K. &1 <= K /\
            !k. k IN 1..n
                ==> norm(a k / e k) <= K /\ norm(e k / b k) <= K /\
                    norm(a k / b k) <= K`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`\k. norm((a:num->complex) k / (e:num->complex) k) +
         norm(e k / (b:num->complex) k) + norm(a k / b k)`; `1..n`]
   UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_TAC `K0:real`) THEN
  EXISTS_TAC `max (&1) K0` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(a:num->complex) k / (e:num->complex) k` NORM_POS_LE) THEN
  MP_TAC(ISPEC `(e:num->complex) k / (b:num->complex) k` NORM_POS_LE) THEN
  MP_TAC(ISPEC `(a:num->complex) k / (b:num->complex) k` NORM_POS_LE) THEN
  REAL_ARITH_TAC);;

let NF_UNITEQ_ONE_PLUS_E = prove
 (`!a u b v e:complex.
        ~(e = Cx(&0)) /\ a * u + b * v = e
        ==> Cx(&1) + --(a * u) / e = b / e * v`,
  REPEAT GEN_TAC THEN CONV_TAC COMPLEX_FIELD);;

let NF_UNITEQ_E_BOUND = prove
 (`!a u e:complex K.
        ~(u = Cx(&0)) /\ norm(a / e) <= K
        ==> norm(--(a * u) / e) * exp(--log(norm u)) <= K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(--(a * u) / e) = norm(a / e) * norm(u:complex)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `--(a * u) / e = --((a / e) * u):complex` SUBST1_TAC THENL
     [REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
      REWRITE_TAC[NORM_NEG; COMPLEX_NORM_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(u:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--log(norm(u:complex))) = inv(norm u)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN AP_TERM_TAC THEN MATCH_MP_TAC EXP_LOG THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
               REAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* The logarithmic size of v from that of u.                                 *)
(* ------------------------------------------------------------------------- *)

let NF_UNITEQ_V_UPPER = prove
 (`!a u b v e:complex K m.
        ~(b = Cx(&0)) /\ ~(u = Cx(&0)) /\ ~(v = Cx(&0)) /\
        a * u + b * v = e /\ norm(e / b) <= K /\ norm(a / b) <= K /\
        &1 <= K /\ abs(log(norm u)) <= m
        ==> log(norm v) <= log(&2 * K) + m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
   [MP_TAC(SPEC `log(norm(u:complex))` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp m` ASSUME_TAC THENL
   [MP_TAC(SPEC `m:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(u:complex) <= exp m` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(u:complex) = exp(log(norm u))` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v:complex) <= (&2 * K) * exp m` ASSUME_TAC THENL
   [SUBGOAL_THEN `v = e / b - (a / b) * u:complex` SUBST1_TAC THENL
     [UNDISCH_TAC `a * u + b * v = e:complex` THEN
      UNDISCH_TAC `~(b = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `norm(e / b:complex) + norm(a / b:complex) * norm(u:complex)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(a / b:complex) * norm(u:complex) <= K * exp m`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `K * &1 <= K * exp m` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `norm(e / b:complex) <= K` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * K` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log((&2 * K) * exp m) = log(&2 * K) + m` (SUBST1_TAC o SYM)
  THENL
   [ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP]; ALL_TAC] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[COMPLEX_NORM_NZ]);;

let NF_UNITEQ_V_LOG_BOUND = prove
 (`!n c r (a:num->complex) b e K u v m.
        nf_data n c r /\ nf_unit n r u /\ nf_unit n r v /\ &1 <= K /\
        (!k. k IN 1..n
             ==> ~(a k = Cx(&0)) /\ ~(b k = Cx(&0)) /\ ~(e k = Cx(&0))) /\
        (!k. k IN 1..n
             ==> norm(a k / e k) <= K /\ norm(e k / b k) <= K /\
                 norm(a k / b k) <= K) /\
        (!k. k IN 1..n ==> a k * u k + b k * v k = e k) /\
        (!k. k IN 1..n ==> abs(log(norm(u k))) <= m)
        ==> !k. k IN 1..n
                ==> abs(log(norm(v k))) <= &n * (log(&2 * K) + m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_MESON_TAC[nf_data]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `\k. log(norm((v:num->complex) k))`;
                `log(&2 * K) + m`] NF_UNITEQ_SUM_ZERO_ABS) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN(ACCEPT_TAC o CONJUNCT2)] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC NF_UNIT_LOG_SUM THEN
    MAP_EVERY EXISTS_TAC [`c:num->real`; `r:num->complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC NF_UNITEQ_V_UPPER THEN
  MAP_EVERY EXISTS_TAC [`(a:num->complex) k`; `(u:num->complex) k`;
                        `(b:num->complex) k`; `(e:num->complex) k`] THEN
  ASM_MESON_TAC[NF_UNIT_NONZERO]);;

(* ------------------------------------------------------------------------- *)
(* The main estimate.                                                        *)
(* ------------------------------------------------------------------------- *)

let NF_UNIT_EQUATION_LOG_BOUND = prove
 (`!n c r a b e.
       nf_data n c r /\ nf_order n r a /\ nf_order n r b /\
       nf_order n r e /\
       ~(a 1 = Cx(&0)) /\ ~(b 1 = Cx(&0)) /\ ~(e 1 = Cx(&0))
       ==> ?H. !u v. nf_unit n r u /\ nf_unit n r v /\
                     (!k. k IN 1..n ==> a k * u k + b k * v k = e k)
                     ==> !k. k IN 1..n ==> abs(log(norm(u k))) <= H`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_MESON_TAC[nf_data]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN 1..n
        ==> ~((a:num->complex) k = Cx(&0)) /\
            ~((b:num->complex) k = Cx(&0)) /\
            ~((e:num->complex) k = Cx(&0))`
  (LABEL_TAC "nz") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NF_UNITEQ_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `a:num->complex`; `b:num->complex`;
                `e:num->complex`] NF_UNITEQ_CONSTANTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K"))) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`]
    NF_UNITS_BOUNDED_GENERATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:(num->complex)->bool` (X_CHOOSE_THEN `C1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "gen"))))) THEN
  MP_TAC(ISPECL
   [`1..n`; `S:(num->complex)->bool`; `\(k:num) (s:num->complex). s k`;
    `\k:num. (b:num->complex) k / (e:num->complex) k`] BAKER_ONE_PLUS_E) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `~((b:num->complex) k = Cx(&0)) /\ ~((e:num->complex) k = Cx(&0))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[COMPLEX_DIV_EQ_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALGEBRAIC_NUMBER_DIV THEN
      ASM_MESON_TAC[NF_ORDER_ALGEBRAIC];
      X_GEN_TAC `s:num->complex` THEN DISCH_TAC THEN
      SUBGOAL_THEN `nf_unit n r (s:num->complex)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[NF_ORDER_ALGEBRAIC; nf_unit; NF_UNIT_NONZERO]];
    DISCH_THEN(X_CHOOSE_THEN `C:num` (LABEL_TAC "baker"))] THEN
  SUBGOAL_THEN `&0 <= log(&2 * K)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL
   [`&2 * K`; `&2 + abs C1 * (&1 + &n * log(&2 * K))`;
    `abs C1 * &n * &n`; `1`; `C:num`] POLYLOG_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
      ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `Y1:real` (LABEL_TAC "poly"))] THEN
  EXISTS_TAC `&n * log(max (&2 * K) Y1)` THEN
  MAP_EVERY X_GEN_TAC [`u:num->complex`; `v:num->complex`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq"))) THEN
  MP_TAC(ISPECL [`n:num`; `\k. log(norm((u:num->complex) k))`]
    REAL_MIN_INDEX_NUMSEG) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; BETA_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  ABBREV_TAC `m0 = --log(norm((u:num->complex) k0))` THEN
  MP_TAC(SPECL [`n:num`; `\k. --log(norm((u:num->complex) k))`; `m0:real`]
    NF_UNITEQ_SUM_ZERO_ABS) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_NEG] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUM_NEG; REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC NF_UNIT_LOG_SUM THEN
      MAP_EVERY EXISTS_TAC [`c:num->real`; `r:num->complex`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN EXPAND_TAC "m0" THEN
      REWRITE_TAC[REAL_LE_NEG2] THEN USE_THEN "min" MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ulog"))] THEN
  SUBGOAL_THEN `exp(m0) <= max (&2 * K) Y1` ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `&n * m0` THEN CONJ_TAC THENL
     [USE_THEN "ulog" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]] THEN
  SUBGOAL_THEN `&1 <= exp m0` ASSUME_TAC THENL
   [MP_TAC(SPEC `m0:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "nz" (MP_TAC o SPEC `k0:num`) THEN
  USE_THEN "K" (MP_TAC o SPEC `k0:num`) THEN
  USE_THEN "eq" (MP_TAC o SPEC `k0:num`) THEN
  REWRITE_TAC[ASSUME `k0 IN 1..n`] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~((u:num->complex) k0 = Cx(&0)) /\ ~((v:num->complex) k0 = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC NF_UNIT_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `r:num->complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `E = --((a:num->complex) k0 * (u:num->complex) k0) /
                  (e:num->complex) k0` THEN
  SUBGOAL_THEN `norm(E:complex) * exp m0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN EXPAND_TAC "m0" THEN
    MATCH_MP_TAC NF_UNITEQ_E_BOUND THEN CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 / &2 < norm(E:complex)` THENL
   [MATCH_MP_TAC(REAL_ARITH `(x:real) <= &2 * K ==> x <= max (&2 * K) Y1`) THEN
    MATCH_MP_TAC REAL_POW_LE_BOUND_HALF THEN
    MAP_EVERY EXISTS_TAC [`norm(E:complex)`; `1`] THEN
    ASM_REWRITE_TAC[REAL_POW_1; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(E:complex) <= &1 / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `a:num->complex`;
                `b:num->complex`; `e:num->complex`; `K:real`;
                `u:num->complex`; `v:num->complex`; `&n * m0`]
    NF_UNITEQ_V_LOG_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  USE_THEN "gen" (MP_TAC o SPECL
   [`v:num->complex`; `&n * (log(&2 * K) + &n * m0)`]) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mm:(num->complex)->num`
   (CONJUNCTS_THEN2 (LABEL_TAC "vdec") ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `Cx(&1) + E = (b:num->complex) k0 / (e:num->complex) k0 *
                 cproduct S (\s:num->complex. s k0 pow mm s)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `cproduct S (\s:num->complex. s k0 pow mm s) = (v:num->complex) k0`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN REMOVE_THEN "vdec" MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "E" THEN MATCH_MP_TAC NF_UNITEQ_ONE_PLUS_E THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(E = Cx(&0))` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[COMPLEX_DIV_EQ_0; COMPLEX_NEG_EQ_0; COMPLEX_ENTIRE;
                DE_MORGAN_THM] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "baker" (MP_TAC o SPECL
   [`k0:num`; `mm:(num->complex)->num`; `E:complex`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) <= Y1 ==> x <= max (&2 * K) Y1`) THEN
  REMOVE_THEN "poly" MATCH_MP_TAC THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_BOUND_CHAIN THEN
  MAP_EVERY EXISTS_TAC
   [`&2 + &(nsum S (mm:(num->complex)->num))`; `norm(E:complex)`;
    `&2 * norm(E:complex)`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_POW_1; LOG_EXP; REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `nsum S (mm:(num->complex)->num)` REAL_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&2 + abs C1 * (&1 + &n * log(&2 * K))) + (abs C1 * &n) * (&n * m0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LINEAR_BOUND_ABS THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Finiteness (export).                                                      *)
(* ------------------------------------------------------------------------- *)

let NF_UNIT_EQUATION = prove
 (`!n c r a b e.
   nf_data n c r /\ nf_order n r a /\ nf_order n r b /\
   nf_order n r e /\
   ~(a 1 = Cx(&0)) /\ ~(b 1 = Cx(&0)) /\ ~(e 1 = Cx(&0))
   ==> ?U. FINITE U /\
           !u v. nf_unit n r u /\ nf_unit n r v /\
                 (!k. k IN 1..n ==> a k * u k + b k * v k = e k)
                 ==> u 1 IN U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    MP_TAC(MATCH_MP NF_UNIT_EQUATION_LOG_BOUND th) THEN
    STRIP_ASSUME_TAC th) THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real` (LABEL_TAC "H")) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `exp H`]
    NF_ORDER_NORTHCOTT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:(num->complex)->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "north")))) THEN
  EXISTS_TAC `IMAGE (\w:num->complex. w 1) A` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`u:num->complex`; `v:num->complex`] THEN STRIP_TAC THEN
  REMOVE_THEN "H" (MP_TAC o SPECL [`u:num->complex`; `v:num->complex`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REMOVE_THEN "north" (MP_TAC o SPEC `u:num->complex`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[nf_unit]; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((u:num->complex) k = Cx(&0))` ASSUME_TAC THENL
     [ASM_MESON_TAC[NF_UNIT_NONZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `norm((u:num->complex) k) = exp(log(norm(u k)))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x:real) <= h ==> x <= h`) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w:num->complex` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:num->complex` THEN
    ASM_SIMP_TAC[]]);;
