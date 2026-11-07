(* ========================================================================= *)
(* The numeric core for an upper bound of the degree product.                *)
(*                                                                           *)
(* Purpose: BAKER_CORE_NUMERIC (Baker/param.ml) is stated for the exact      *)
(* degree product D = nproduct V d. All requirements on the base q are       *)
(* monotone in D (BAKER_PARAMS_MONO, BAKER_LPAR_MONO), so the same           *)
(* conclusion holds for every upper bound Dm of D; this is the form used by  *)
(* the core lower bounds of Baker/explicit.ml, where only Dm = Dmax Dx^m is  *)
(* known.                                                                    *)
(*                                                                           *)
(* Main results: BAKER_CORE_NUMERIC_DMAX (BAKER_CORE_NUMERIC for an upper    *)
(*   bound Dm of the degree product); SMALL_INDEPENDENT_MONO (no relation    *)
(*   with coefficients <= Y implies none with coefficients <= X <= Y);       *)
(*   REAL_NUM_CEIL (a small real fact, also used by later files).            *)
(*                                                                           *)
(* Uses: Baker/param.ml (BAKER_CORE_NUMERIC; baker_c, baker_J, baker_e1,     *)
(*   baker_kpar, baker_Lpar), Baker/intpoly.ml (intpoly), Baker/lemmas.ml    *)
(*   (REAL_LE_1_MUL).                                                        *)
(* ========================================================================= *)

needs "Baker/param.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The numeric core for an upper bound Dm of the degree product.             *)
(* ------------------------------------------------------------------------- *)

let BAKER_PARAMS_MONO = prove
 (`!n D Dm q.
     D <= Dm /\ 1 <= q
     ==> baker_c D <= baker_c Dm /\ baker_J n D <= baker_J n Dm /\
         baker_e1 n D <= baker_e1 n Dm /\
         baker_kpar n D q <= baker_kpar n Dm q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `baker_c D <= baker_c Dm` ASSUME_TAC THENL
   [REWRITE_TAC[baker_c] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `baker_J n D <= baker_J n Dm` ASSUME_TAC THENL
   [REWRITE_TAC[baker_J; LE_ADD_RCANCEL] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[baker_e1] THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b /\ c <= d ==> a + c + 4 <= b + d + 4`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL];
    REWRITE_TAC[baker_kpar; LE_EXP] THEN COND_CASES_TAC THENL
     [ASM_ARITH_TAC; DISJ2_TAC THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]]]);;

let BAKER_LPAR_MONO = prove
 (`!n D Dm q. D <= Dm /\ 1 <= q ==> baker_Lpar n D q <= baker_Lpar n Dm q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_Lpar; LE_MULT_LCANCEL] THEN
  DISJ2_TAC THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_EXP] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISJ2_TAC THEN MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL; baker_c] THEN
  ASM_ARITH_TAC);;

let SMALL_INDEPENDENT_MONO = prove
 (`!n (lg:num->complex) X Y.
     X <= Y /\
     (!b. (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= Y) /\
          vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
          ==> !r. r IN 1..n ==> b r = &0)
     ==> !b. (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= X) /\
             vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
             ==> !r. r IN 1..n ==> b r = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let BAKER_CORE_NUMERIC_DMAX = prove
 (`!n lg theta V (g:num->(num->complex)->complex) e G a d H beta
    Bb Lam d0 lmin Gn M q h Dm.
    1 <= n /\ &1 <= G /\ FINITE V /\ (1..n) SUBSET V /\
    (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
    (!j. j <= n ==> intpoly V e G (g j)) /\
    ~(g n theta = Cx(&0)) /\ norm(g n theta) <= Gn /\ &1 <= Gn /\
    (!j. j < n ==> beta j * g n theta = --(g j theta)) /\
    (!r. r IN V
         ==> 1 <= d r /\ &1 <= H r /\
             (!j. integer(a r j) /\ abs(a r j) <= H r) /\
             ~(a r (d r) = &0) /\
             vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
    (!b. (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= &(baker_Lpar n Dm q)) /\
         vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
         ==> !r. r IN 1..n ==> b r = &0) /\
    &1 <= Bb /\ (!j. j < n ==> norm(beta j) <= Bb) /\
    &1 <= Lam /\ (!r. r IN 1..n ==> norm(lg r) <= Lam) /\
    sum(1..n) (\r. norm(lg r)) <= Lam /\
    &0 < lmin /\ lmin <= &1 /\ (!r. r IN 1..n ==> lmin <= norm(lg r)) /\
    &n <= M /\ nproduct V d <= Dm /\ &Dm <= M /\ Lam <= M /\
    sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= M /\
    log(inv lmin) <= M /\
    &112 <= log(&q) /\
    &2176 * M pow 3 * &2 pow (baker_J n Dm) <= &q /\
    &(baker_c Dm * (n + 1)) * (&8 * M + &75) *
    (&6 * M) pow (n + 3) * &2 pow (baker_J n Dm + 1) <= &q /\
    1 <= h /\ M <= &h /\
    log(&(baker_kpar n Dm q)) <= &h /\
    log G <= &h /\ log Bb <= &h /\ log Gn <= &h /\
    sum V (\r. &(e r) * log(&(d r + 1) * H r pow 3)) <= &h /\
    norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n) <= d0 /\
    d0 <= exp(--(&q pow (baker_e1 n Dm + 1) * &h))
    ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 <= q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&16 <= &q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2176 * M pow 3 * &2 pow baker_J n Dm` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&1 <= M` ASSUME_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `&n` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &16 <= &2176 * x`) THEN
      MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. (!r. r IN 1..n
             ==> integer(b r) /\
                 abs(b r) <=
                 &(baker_Lpar n (nproduct (V:num->bool) (d:num->num)) q)) /\
        vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
        ==> !r. r IN 1..n ==> b r = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMALL_INDEPENDENT_MONO THEN
    EXISTS_TAC `&(baker_Lpar n Dm q)` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC BAKER_LPAR_MONO THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(SPECL
   [`n:num`; `lg:num->complex`; `theta:num->complex`; `V:num->bool`;
    `g:num->(num->complex)->complex`; `e:num->num`; `G:real`;
    `a:num->num->real`; `d:num->num`; `H:num->real`; `beta:num->complex`;
    `Bb:real`; `Lam:real`; `d0:real`; `lmin:real`; `Gn:real`; `M:real`;
    `q:num`; `h:num`] BAKER_CORE_NUMERIC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `nproduct V (d:num->num)`; `Dm:num`; `q:num`]
               BAKER_PARAMS_MONO) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&1 <= &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&Dm` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    TRANS_TAC REAL_LE_TRANS `&2176 * M pow 3 * &2 pow baker_J n Dm` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN
      TRANS_TAC REAL_LE_TRANS `&n` THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS
     `&(baker_c Dm * (n + 1)) * (&8 * M + &75) * (&6 * M) pow (n + 3) *
      &2 pow (baker_J n Dm + 1)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&n` THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_MULT2 THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
      [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS `log(&(baker_kpar n Dm q))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[baker_kpar; ARITH_RULE `0 < x <=> ~(x = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS `exp(--(&q pow (baker_e1 n Dm + 1) * &h))` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* An integer ceiling.                                                       *)
(* ------------------------------------------------------------------------- *)

let REAL_NUM_CEIL = prove
 (`!x. &0 <= x ==> ?n. x <= &n /\ &n < x + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN
    SUBGOAL_THEN `&k = &(k - 1) + &1` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REAL_ARITH_TAC]]);;
