(* ========================================================================= *)
(* HOL Light implementation of Wilf-Zeilberger and related methods.          *)
(*                                                                           *)
(* See J. Harrison, "Formal Proofs of Hypergeometric Sums", Journal of       *)
(* Automated Reasoning 55 (2015), DOI 10.1007/s10817-015-9338-0.             *)
(* ========================================================================= *)

needs "Multivariate/gamma.ml";;

(* ------------------------------------------------------------------------- *)
(* An ad-hoc real power function with properties we want.                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("spow",(24,"left"));;

let spow = new_definition
 `x spow y = if x = &0 then &0
             else if x < &0 then cos(y * pi) * (--x) rpow y else x rpow y`;;

let SPOW_STEP_UP = prove
 (`!x y. x spow (y + &1) = x spow y * x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_SIMP_TAC[spow; REAL_LT_REFL; RPOW_ZERO; REAL_MUL_RZERO] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[RPOW_ADD; REAL_NEG_GT0; RPOW_POW; REAL_POW_1] THEN
    REWRITE_TAC[REAL_ARITH `(y + &1) * pi = y * pi + pi`] THEN
    REWRITE_TAC[COS_ADD; SIN_PI; COS_PI] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[RPOW_ADD; REAL_ARITH `~(x = &0) /\ ~(x < &0) ==> &0 < x`] THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1]]);;

let SPOW_STEP_DOWN = prove
 (`!x y. x spow (y - &1) = x spow y / x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_SIMP_TAC[spow; REAL_LT_REFL; RPOW_ZERO; REAL_ARITH `x / &0 = &0`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[RPOW_SUB; REAL_NEG_GT0; RPOW_POW; REAL_POW_1] THEN
    REWRITE_TAC[REAL_ARITH `(y - &1) * pi = y * pi - pi`] THEN
    REWRITE_TAC[COS_SUB; SIN_PI; COS_PI] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[RPOW_SUB; REAL_ARITH `~(x = &0) /\ ~(x < &0) ==> &0 < x`] THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1]]);;

let SPOW_EQ_0 = prove
 (`!x y. x spow y = &0 <=> x = &0 \/ x < &0 /\ cos(y * pi) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[spow] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[RPOW_EQ_0; REAL_ENTIRE] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Version of REAL_FIELD where we conveniently have an implication with      *)
(* nonzeroness of any inverted terms.                                        *)
(* ------------------------------------------------------------------------- *)

let SPECIAL_REAL_FIELD_TAC =
  let is_inv =
    let inv_tm = `inv:real->real`
    and is_div = is_binop `(/):real->real->real` in
    fun tm -> (is_div tm || (is_comb tm && rator tm = inv_tm)) &&
              not(is_ratconst(rand tm)) in
  fun (asl,tm) ->
    let ant,con = dest_imp tm in
    let is_freeinv t = is_inv t && free_in t tm in
    let ivtms = setify(find_terms is_freeinv con) in
    let itms = setify(map rand (find_terms is_freeinv con)) in
    let hyps = map (fun t -> SPEC t REAL_MUL_RINV) itms in
    let aths = CONJUNCTS (ASSUME ant) in
    let pths = map (fun th -> tryfind (MP th) aths) hyps in
    let gvs = map (genvar o type_of) itms in
    (DISCH_TAC THEN MAP_EVERY MP_TAC pths THEN
     MAP_EVERY SPEC_TAC (zip ivtms gvs) THEN
     CONV_TAC REAL_RING) (asl,tm);;

(* ------------------------------------------------------------------------- *)
(* Generalizations of factorial and binomial coefficients to R.              *)
(* ------------------------------------------------------------------------- *)

let rfact = new_definition
 `rfact x = gamma(x + &1)`;;

let rbinom = new_definition
 `rbinom(n,k) = rfact n / (rfact k * rfact (n - k))`;;

let RFACT_STEP_UP = prove
 (`!n. rfact(n + &1) = if n = --(&1) then &1 else (n + &1) * rfact n`,
  GEN_TAC THEN REWRITE_TAC[rfact] THEN
  GEN_REWRITE_TAC LAND_CONV [GAMMA_RECURRENCE] THEN
  REWRITE_TAC[REAL_ARITH `x:real = -- &1 <=> x + &1 = &0`]);;

let RFACT_STEP_DOWN = prove
 (`!n. rfact(n - &1) = rfact n / n`,
  GEN_TAC THEN REWRITE_TAC[rfact] THEN
  GEN_REWRITE_TAC LAND_CONV [GAMMA_RECURRENCE_ALT] THEN
  BINOP_TAC THEN TRY AP_TERM_TAC THEN REAL_ARITH_TAC);;

let RBINOM_TOP_STEP = prove
 (`!k n. ~(n + &1 = &0) /\ ~(n + &1 = k)
         ==> rbinom(n + &1,k) = (n + &1) / (n - k + &1) * rbinom (n,k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rbinom] THEN
  REWRITE_TAC[REAL_ARITH `(n + &1) - k = (n - k) + &1`] THEN
  REWRITE_TAC[RFACT_STEP_UP] THEN
  REPEAT(COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let RBINOM_BOTTOM_STEP = prove
 (`!k n. ~(k + &1 = &0)
         ==> rbinom(n,k + &1) = (n - k) / (k + &1) * rbinom(n,k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rbinom] THEN
  REWRITE_TAC[REAL_ARITH `n - (k + &1) = (n - k) - &1`] THEN
  REWRITE_TAC[RFACT_STEP_UP; RFACT_STEP_DOWN] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let RBINOM_TOP_STEP_DOWN = prove
 (`!k n. rbinom(n - &1,k) = (n - k) / n * rbinom(n,k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rbinom] THEN
  REWRITE_TAC[RFACT_STEP_DOWN; REAL_ARITH `n - &1 - k = n - k - &1`]  THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC);;

let RBINOM_BOTTOM_STEP_DOWN = prove
 (`!k n. ~(n + &1 = k) ==> rbinom(n,k - &1) = k / (n - k + &1) * rbinom(n,k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rbinom; RFACT_STEP_DOWN] THEN
  ASM_SIMP_TAC[REAL_ARITH `n - (k - &1) = (n - k) + &1`; RFACT_STEP_UP] THEN
  ASM_SIMP_TAC[REAL_ARITH `n - k = -- &1 <=> n + &1 = k`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC);;

let RBINOM_STEP_BOTH_UP = prove
 (`!k n. ~(k + &1 = &0) /\ ~(n + &1 = &0)
         ==> rbinom(n + &1,k + &1) = (n + &1) / (k + &1) * rbinom(n,k)`,
  REWRITE_TAC[rbinom; REAL_ARITH `(n + &1) - (k + &1) = n - k`] THEN
  SIMP_TAC[RFACT_STEP_UP; REAL_ARITH `n = --x <=> n + x = &0`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC);;

let RBINOM_STEP_BOTH_DOWN = prove
 (`!k n. rbinom(n - &1,k - &1) = k / n * rbinom(n,k)`,
  REWRITE_TAC[rbinom; REAL_ARITH `(n - &1) - (k - &1) = n - k`] THEN
  REWRITE_TAC[RFACT_STEP_DOWN] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC);;

let LIM_RFACT = prove
 (`!net:(A)net nn n.
        (nn ---> &n) net ==> ((\a. rfact(nn a)) ---> &(FACT n)) net`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfact; GSYM GAMMA_FACT] THEN
  MATCH_MP_TAC(SPEC `gamma` REALLIM_REAL_CONTINUOUS_FUNCTION) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; REALLIM_ADD; REALLIM_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_GAMMA THEN REAL_ARITH_TAC);;

let LIM_INV_RFACT = prove
 (`!net:(A)net nn x.
        integer x /\ x < &0 /\ (nn ---> x) net
        ==> ((\a. inv(rfact(nn a))) ---> &0) net`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 = inv(gamma(x + &1))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN REWRITE_TAC[GAMMA_EQ_0; REAL_INV_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [is_int]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` (DISJ_CASES_THEN SUBST_ALL_TAC)) THENL
     [ASM_REAL_ARITH_TAC; EXISTS_TAC `m - 1`] THEN
    REWRITE_TAC[REAL_ARITH `(--x + &1) + y = &0 <=> y = x - &1`] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH `--x < &0 ==> &0 < x`)) THEN
    SIMP_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_SUB; LE_1];
    REWRITE_TAC[rfact] THEN MATCH_MP_TAC(REWRITE_RULE[o_THM]
     (SPEC `inv o gamma` REALLIM_REAL_CONTINUOUS_FUNCTION)) THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_ATREAL_RECIP_GAMMA;
                 REALLIM_ADD; REALLIM_CONST]]);;

let LIM_RBINOM = prove
 (`!net:(A)net nn kk n k.
        (nn ---> &n) net /\ (kk ---> &k) net
        ==> ((\a. rbinom(nn a,kk a)) ---> &(binom(n,k))) net`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rbinom; REAL_OF_NUM_BINOM] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REALLIM_DIV THEN
    ASM_SIMP_TAC[REAL_ENTIRE; REAL_OF_NUM_EQ; FACT_NZ; LIM_RFACT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REALLIM_MUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; FACT_NZ; LIM_RFACT] THEN
    MATCH_MP_TAC LIM_RFACT THEN
    ASM_SIMP_TAC[REALLIM_SUB; GSYM REAL_OF_NUM_SUB];
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    SUBST1_TAC(REAL_ARITH `&0 = (&(FACT n) * inv(&(FACT k))) * &0`) THEN
    MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_MUL THEN ASM_SIMP_TAC[LIM_RFACT] THEN
      MATCH_MP_TAC REALLIM_INV THEN
      ASM_SIMP_TAC[LIM_RFACT; REAL_OF_NUM_EQ; FACT_NZ];
      MATCH_MP_TAC LIM_INV_RFACT THEN EXISTS_TAC `&n - &k:real` THEN
      ASM_SIMP_TAC[INTEGER_CLOSED; REALLIM_SUB] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC]]);;

let REALLIM_SPOW = prove
 (`!net:A net f l.
        (f ---> l) net ==> ((\x. t spow f x) ---> t spow l) net`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t = &0` THEN
  ASM_REWRITE_TAC[spow; REALLIM_CONST] THEN DISCH_TAC THEN
  ASM_CASES_TAC `t < &0` THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC REALLIM_MUL) THEN
  ASM_SIMP_TAC[REALLIM_RPOW_COMPOSE; REALLIM_CONST; REAL_NEG_GT0;
               REAL_ARITH `~(t = &0) /\ ~(t < &0) ==> &0 < t`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[o_DEF] (ONCE_REWRITE_RULE[IMP_CONJ]
      REALLIM_COMPOSE_AT))) THEN
  REWRITE_TAC[EVENTUALLY_TRUE] THEN
  MATCH_MP_TAC(ISPEC `cos` REALLIM_REAL_CONTINUOUS_FUNCTION) THEN
  SIMP_TAC[REALLIM_RMUL; REALLIM_ATREAL_ID; REAL_CONTINUOUS_AT_COS]);;

let REALLIM_SPOW_COMPOSE = prove
 (`!net:A net f g l m.
        (f ---> l) net /\ (g ---> m) net /\ ~(l = &0)
        ==> ((\x. (f x) spow (g x)) ---> l spow m) net`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP
  (REAL_ARITH `~(x = &0) ==> &0 < x /\ ~(x < &0) \/ x < &0 /\ ~(&0 < x)`)) THEN
  GEN_REWRITE_TAC LAND_CONV [spow] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THENL
   [EXISTS_TAC `\x:A. (f x) rpow (g x)` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC EVENTUALLY_MONO THEN
      EXISTS_TAC `\x. &0 < (f:A->real) x` THEN
      SIMP_TAC[spow; REAL_ARITH `&0 < x ==> ~(x = &0) /\ ~(x < &0)`] THEN
      MATCH_MP_TAC EVENTUALLY_MONO THEN
      EXISTS_TAC `\x. abs((f:A->real) x - l) < l` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[tendsto_real]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REALLIM_RPOW_COMPOSE THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `\x:A. cos(g x * pi) * (--f x) rpow (g x)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC EVENTUALLY_MONO THEN
      EXISTS_TAC `\x. (f:A->real) x < &0` THEN
      SIMP_TAC[spow; REAL_ARITH `x < &0 ==> ~(x = &0)`] THEN
      MATCH_MP_TAC EVENTUALLY_MONO THEN
      EXISTS_TAC `\x. abs((f:A->real) x - l) < --l` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[tendsto_real]) THEN
      ASM_REWRITE_TAC[REAL_NEG_GT0];
      MATCH_MP_TAC REALLIM_MUL THEN
      ASM_SIMP_TAC[REALLIM_RPOW_COMPOSE; REALLIM_NEG; REAL_NEG_GT0] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[o_DEF] (ONCE_REWRITE_RULE[IMP_CONJ]
          REALLIM_COMPOSE_AT))) THEN
      REWRITE_TAC[EVENTUALLY_TRUE] THEN
      MATCH_MP_TAC(ISPEC `cos` REALLIM_REAL_CONTINUOUS_FUNCTION) THEN
      SIMP_TAC[REALLIM_RMUL; REALLIM_ATREAL_ID; REAL_CONTINUOUS_AT_COS]]]);;

let RFACT_EQ_0 = prove
 (`!x. rfact x = &0 <=> integer x /\ x < &0`,
  REWRITE_TAC[rfact; GAMMA_EQ_0; GSYM NONPOSITIVE_INTEGER_ALT] THEN
  GEN_TAC THEN ASM_CASES_TAC `integer x` THENL
   [ASM_SIMP_TAC[INTEGER_CLOSED; REAL_LT_INTEGERS];
    ASM_MESON_TAC[INTEGER_CLOSED; REAL_ARITH `(x + a) - a:real = x`]]);;

let REAL_CONTINUOUS_AT_RFACT = prove
 (`!x. ~(integer x /\ x <= -- &1) ==> rfact real_continuous atreal x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[rfact] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN
  SIMP_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_CONST;
           REAL_CONTINUOUS_AT_ID] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_GAMMA THEN GEN_TAC THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `(x + &1) + n = &0 ==> x = --(n + &1)`)) THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let REAL_CONTINUOUS_AT_INV_RFACT = prove
 (`!x. (inv o rfact) real_continuous atreal x`,
  GEN_TAC THEN  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[rfact] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[o_ASSOC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN
  SIMP_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_CONST;
           REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_ATREAL_RECIP_GAMMA]);;

let REAL_CONTINUOUS_RFACT_COMPOSE_WITHIN = prove
 (`!nn s z:real^N.
        nn real_continuous (at z within s) /\
        ~(integer(nn z) /\ nn z <= -- &1)
        ==> (\x. rfact(nn x)) real_continuous (at z within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_AT_RFACT]);;

let REAL_CONTINUOUS_INV_RFACT_COMPOSE_WITHIN = prove
 (`!nn s z:real^N.
        nn real_continuous (at z within s)
        ==> (\x. inv(rfact(nn x))) real_continuous (at z within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM o_DEF; o_ASSOC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  REWRITE_TAC[REAL_CONTINUOUS_AT_INV_RFACT]);;

let REAL_CONTINUOUS_RBINOM_COMPOSE_WITHIN = prove
 (`!nn kk s a:real^N.
      nn real_continuous (at a within s) /\
      kk real_continuous (at a within s) /\
      ~(integer(nn a) /\ nn a <= -- &1)
      ==> (\x. rbinom (nn x,kk x)) real_continuous (at a within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rbinom; real_div; REAL_INV_MUL] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_CONTINUOUS_RFACT_COMPOSE_WITHIN];
    ASM_SIMP_TAC[REAL_CONTINUOUS_INV_RFACT_COMPOSE_WITHIN;
                 REAL_CONTINUOUS_MUL; REAL_CONTINUOUS_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* Representation (using functions) of polynomials w.r.t. an N-indexed       *)
(* family of variables over the rational numbers.                            *)
(* ------------------------------------------------------------------------- *)

let ratpoly = new_definition
 `ratpoly p <=>
         (!m. rational(p m)) /\
         FINITE {m | ~(p m = &0)} /\
         (!m. ~(p m = &0) ==> FINITE {i:num | ~(m i = 0)})`;;

let COUNTABLE_RATPOLY = prove
 (`COUNTABLE ratpoly`,
  GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[ratpoly] THEN
  REWRITE_TAC[COUNTABLE; ge_c] THEN MP_TAC(ISPEC
   `{m | FINITE {i:num | ~(m i = 0)}} CROSS rational` CARD_EQ_LIST_GEN) THEN
  SUBGOAL_THEN `{m | FINITE {i:num | ~(m i = 0)}} CROSS rational =_c (:num)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CROSS; GSYM mul_c] THEN
    TRANS_TAC CARD_EQ_TRANS `(:num) *_c (:num)` THEN
    REWRITE_TAC[CARD_SQUARE_NUM] THEN
    MATCH_MP_TAC CARD_MUL_CONG THEN REWRITE_TAC[CARD_EQ_RATIONAL] THEN
    REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
     [TRANS_TAC CARD_LE_TRANS `(:(num#num)list)` THEN CONJ_TAC THENL
       [REWRITE_TAC[le_c; IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC
         `\m. list_of_set (IMAGE (\i:num. (i,m i)) {i | ~(m i = 0)})` THEN
        MAP_EVERY X_GEN_TAC [`m1:num->num`; `m2:num->num`] THEN
        REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM
         `set_of_list:(num#num)list->num#num->bool`) THEN
        ASM_SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_IMAGE] THEN
        GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
        REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM;
                    PAIR_EQ; FORALL_PAIR_THM; IN_ELIM_THM] THEN
        DISCH_TAC THEN X_GEN_TAC `i:num` THEN
        ASM_CASES_TAC `m2(i:num) = 0` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
        ASM_REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC CARD_EQ_IMP_LE THEN
        W(MP_TAC o PART_MATCH (lhand o rand) CARD_EQ_LIST o lhand o snd) THEN
        REWRITE_TAC[GSYM MUL_C_UNIV; INFINITE; CARD_MUL_FINITE_EQ] THEN
        REWRITE_TAC[UNIV_NOT_EMPTY; GSYM INFINITE; num_INFINITE] THEN
        MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
        REWRITE_TAC[CARD_SQUARE_NUM]];
      REWRITE_TAC[LE_C; IN_UNIV; IN_ELIM_THM] THEN
      EXISTS_TAC `\m:num->num. m 0` THEN X_GEN_TAC `j:num` THEN
      EXISTS_TAC `\i. if i = 0 then j else 0` THEN REWRITE_TAC[MESON[]
       `~((if x = a then c else z) = z) <=> x = a /\ ~(c = z)`] THEN
      REWRITE_TAC[SET_RULE `{x | x = a /\ P x} = {x | x IN {a} /\ P x}`] THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_SING]];
    FIRST_ASSUM(MP_TAC o MATCH_MP CARD_INFINITE_CONG) THEN
    SIMP_TAC[num_INFINITE] THEN DISCH_THEN(K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_TRANS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CARD_LE_TRANS)] THEN
  REWRITE_TAC[le_c; IN_ELIM_THM] THEN EXISTS_TAC
   `\p. list_of_set (IMAGE (\m. (m,p m)) {m:num->num | ~(p m = &0)})` THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_CROSS; IN_ELIM_THM] THEN
  CONJ_TAC THENL [SIMP_TAC[IN]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:(num->num)->real`; `q:(num->num)->real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM
   `set_of_list:((num->num)#real)list->(num->num)#real->bool`) THEN
  ASM_SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM;
              PAIR_EQ; FORALL_PAIR_THM; IN_ELIM_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `f:num->num` THEN
  ASM_CASES_TAC `p(f:num->num) = &0` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:num->num`) THEN
  ASM_REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1] THEN ASM_MESON_TAC[]);;

let poly_eval = new_definition
 `poly_eval p x =
    sum (:num->num) (\m. p m * product (:num) (\i. x i pow m i))`;;

let POLY_EVAL_RATPOLY = prove
 (`!p x. ratpoly p
         ==> poly_eval p x =
             sum {m | ~(p m = &0)}
                 (\m. p m * product {i | ~(m i = 0)} (\i. x i pow m i))`,
  REWRITE_TAC[ratpoly] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[poly_eval] THEN
  MATCH_MP_TAC SUM_EQ_SUPERSET THEN
  ASM_SIMP_TAC[SUBSET_UNIV; IN_ELIM_THM; REAL_MUL_LZERO] THEN
  X_GEN_TAC `m:num->num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PRODUCT_SUPERSET THEN
  SIMP_TAC[IN_ELIM_THM; SUBSET_UNIV; real_pow]);;

(* ------------------------------------------------------------------------- *)
(* Hence polynomial functions of two real variables over the rationals       *)
(* plus a finite set of parameters.                                          *)
(* ------------------------------------------------------------------------- *)

let ratpolyfun = new_definition
 `ratpolyfun s f <=>
    ?p. ratpoly p /\
        f = \(x,y). poly_eval p (\i. EL i (CONS x (CONS y (list_of_set s))))`;;

let COUNTABLE_RATPOLYFUN = prove
 (`!s. COUNTABLE(ratpolyfun s)`,
  GEN_TAC THEN MP_TAC(ISPEC
   `\p (x,y). poly_eval p (\i. EL i (CONS x (CONS y (list_of_set s))))`
   (MATCH_MP COUNTABLE_IMAGE COUNTABLE_RATPOLY)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[ratpolyfun] THEN MESON_TAC[]);;

let RATPOLYFUN_CONST = prove
 (`!s c. rational c ==> ratpolyfun s (\(x,y). c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ratpolyfun; ratpoly] THEN
  EXISTS_TAC `\m. if m = \i:num. 0 then c else &0` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[RATIONAL_CLOSED];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{(\i:num. 0)}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY];
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    REWRITE_TAC[poly_eval; FORALL_PAIR_THM] THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
    SIMP_TAC[SUM_DELTA; IN_UNIV; real_pow; PRODUCT_ONE; REAL_MUL_RID]]);;

let RATPOLYFUN_VAR = prove
 (`!s. ratpolyfun s (\(n,k). n) /\ ratpolyfun s (\(n,k). k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ratpolyfun; ratpoly] THENL
   [EXISTS_TAC `\m. if m = \i. if i = 0 then 1 else 0 then &1 else &0`;
    EXISTS_TAC `\m. if m = \i. if i = 1 then 1 else 0 then &1 else &0`] THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[RATIONAL_CLOSED; COND_ID] THEN
  ONCE_REWRITE_TAC[COND_RATOR] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[MESON[] `~(if p then F else T) <=> p`] THEN
  REWRITE_TAC[SING_GSPEC; FINITE_SING] THEN SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MESON[] `~(if p then F else T) <=> p`] THEN
  REWRITE_TAC[SING_GSPEC; FINITE_SING] THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[poly_eval; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  SIMP_TAC[SUM_DELTA; IN_UNIV; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[real_pow; REAL_POW_1] THEN
  SIMP_TAC[PRODUCT_DELTA; IN_UNIV; EL; HD] THEN
  REWRITE_TAC[num_CONV `1`; EL; HD; TL]);;

let RATPOLYFUN_PARAMETER = prove
 (`!s a. FINITE s /\ a IN s ==> ratpolyfun s (\(x,y). a)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o MATCH_MP MEM_LIST_OF_SET) THEN
  ASM_REWRITE_TAC[MEM_EXISTS_EL] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (STRIP_ASSUME_TAC o GSYM)) THEN
  REWRITE_TAC[ratpolyfun; ratpoly] THEN
  EXISTS_TAC `\m. if m = \i. if i = n + 2 then 1 else 0 then &1 else &0` THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[RATIONAL_CLOSED; COND_ID] THEN
  ONCE_REWRITE_TAC[COND_RATOR] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[MESON[] `~(if p then F else T) <=> p`] THEN
  REWRITE_TAC[SING_GSPEC; FINITE_SING] THEN SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MESON[] `~(if p then F else T) <=> p`] THEN
  REWRITE_TAC[SING_GSPEC; FINITE_SING] THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[poly_eval; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  SIMP_TAC[SUM_DELTA; IN_UNIV; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[real_pow; REAL_POW_1] THEN
  SIMP_TAC[PRODUCT_DELTA; IN_UNIV] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n + 2 = SUC(SUC n)`; EL; HD; TL]);;

let RATPOLYFUN_NEG = prove
 (`!p s. ratpolyfun s (\(n,k). p n k) ==> ratpolyfun s (\(n,k). --(p n k))`,
  MAP_EVERY X_GEN_TAC [`f:real->real->real`; `s:real->bool`] THEN
  REWRITE_TAC[ratpolyfun; FUN_EQ_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:(num->num)->real` THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `?r. ratpoly r /\ !xs. --(poly_eval p xs) = poly_eval r xs`
  MP_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]] THEN
  EXISTS_TAC `(\m. --(p m)):(num->num)->real` THEN
  REWRITE_TAC[poly_eval; REAL_MUL_LNEG; SUM_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ratpoly]) THEN REWRITE_TAC[ratpoly] THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED; REAL_NEG_EQ_0]);;

let RATPOLYFUN_ADD = prove
 (`!p q s. ratpolyfun s (\(n,k). p n k) /\ ratpolyfun s (\(n,k). q n k)
           ==> ratpolyfun s (\(n,k). p n k + q n k)`,
  MAP_EVERY X_GEN_TAC
   [`f:real->real->real`; `g:real->real->real`; `s:real->bool`] THEN
  REWRITE_TAC[ratpolyfun] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `p:(num->num)->real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `q:(num->num)->real` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM])) THEN
  SIMP_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN REPEAT(DISCH_THEN(K ALL_TAC)) THEN
  SUBGOAL_THEN
   `?r. ratpoly r /\ !xs. poly_eval p xs + poly_eval q xs = poly_eval r xs`
  MP_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]] THEN
  EXISTS_TAC `\m. (p:(num->num)->real) m + q m` THEN CONJ_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[ratpoly] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RATIONAL_CLOSED] THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{m:num->num | ~(p m = &0)} UNION {m | ~(q m = &0)}` THEN
      ASM_REWRITE_TAC[FINITE_UNION; SUBSET; IN_UNION; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
       `~(x + y = &0) ==> ~(x = &0) \/ ~(y = &0)`)) THEN
      ASM_SIMP_TAC[]];
    GEN_TAC THEN REWRITE_TAC[poly_eval; REAL_ADD_RDISTRIB] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_ADD_GEN THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ratpoly]) THEN
    REWRITE_TAC[REAL_ENTIRE; IN_UNIV; DE_MORGAN_THM] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT]]);;

let RATPOLYFUN_SUB = prove
 (`!p q s. ratpolyfun s (\(n,k). p n k) /\ ratpolyfun s (\(n,k). q n k)
           ==> ratpolyfun s (\(n,k). p n k - q n k)`,
  SIMP_TAC[real_sub; RATPOLYFUN_ADD; RATPOLYFUN_NEG]);;

let RATPOLYFUN_MUL = prove
 (`!p q s. ratpolyfun s (\(n,k). p n k) /\ ratpolyfun s (\(n,k). q n k)
           ==> ratpolyfun s (\(n,k). p n k * q n k)`,
  MAP_EVERY X_GEN_TAC
   [`f:real->real->real`; `g:real->real->real`; `s:real->bool`] THEN
  REWRITE_TAC[ratpolyfun] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `p:(num->num)->real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `q:(num->num)->real` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM])) THEN
  SIMP_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN REPEAT(DISCH_THEN(K ALL_TAC)) THEN
  SUBGOAL_THEN
   `?r. ratpoly r /\ !xs. poly_eval p xs * poly_eval q xs = poly_eval r xs`
  MP_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]] THEN
  EXISTS_TAC `\m. sum {(k,l) | (\i. k i + l i) = m}
                      (\(k:num->num,l). p k * q l)` THEN
  CONJ_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[ratpoly] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC RATIONAL_SUM THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[RATIONAL_CLOSED];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\(k:num->num,l) i. k i + l i)
                        {k,l | ~(p k * q l = &0)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[REAL_ENTIRE] THEN
        REWRITE_TAC[SET_RULE
         `{k,l | ~(P k \/ Q l)} =
          {k,l | k IN {x | ~P x} /\ l IN {x | ~Q x}}`] THEN
        MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `m:num->num` THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
          SUM_EQ_0)) THEN
        REWRITE_TAC[FORALL_IN_GSPEC; IN_IMAGE; EXISTS_PAIR_THM] THEN
        REWRITE_TAC[IN_ELIM_PAIR_THM] THEN SET_TAC[]];
      FIRST_ASSUM(MP_TAC o MATCH_MP
        (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] SUM_EQ_0)) THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`k:num->num`; `l:num->num`] THEN
      REWRITE_TAC[DE_MORGAN_THM; REAL_ENTIRE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[ADD_EQ_0; FINITE_UNION; SET_RULE
       `{x | ~(P x /\ Q x)} = {x | ~P x} UNION {x | ~Q x}`]];
    GEN_TAC THEN REWRITE_TAC[poly_eval] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [GSYM SUM_SUPPORT] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_PRODUCT o lhand o snd) THEN
    REWRITE_TAC[support; IN_UNIV; NEUTRAL_REAL_ADD; IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[ratpoly]) THEN
      REWRITE_TAC[REAL_ENTIRE; IN_UNIV; DE_MORGAN_THM] THEN
      ONCE_REWRITE_TAC[SET_RULE
       `{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`] THEN
      ASM_SIMP_TAC[FINITE_RESTRICT];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL
     [`\(k:num->num,l) i. k i + l i`; `(:num->num)`]
     (ONCE_REWRITE_RULE[MESON[]
        `(!f g s t. P f g s t) <=> (!f t g s. P f g s t)`] SUM_GROUP)) THEN
    DISCH_THEN(fun th ->
     W(MP_TAC o PART_MATCH (rand o rand) th o lhand o snd)) THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ANTS_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IN] FINITE_PRODUCT_DEPENDENT) THEN
      REWRITE_TAC[REAL_ENTIRE; IN_UNIV; DE_MORGAN_THM] THEN
      ONCE_REWRITE_TAC[SET_RULE
       `(\x. P x /\ Q x) = {x | x IN {y | P y} /\ Q x}`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ratpoly]) THEN
      ASM_SIMP_TAC[FINITE_RESTRICT];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num->num` THEN
    REWRITE_TAC[IN_UNIV] THEN GEN_REWRITE_TAC RAND_CONV [GSYM SUM_SUPPORT] THEN
    REWRITE_TAC[support; IN_UNIV; NEUTRAL_REAL_ADD] THEN
    REWRITE_TAC[SET_RULE `{x | x IN {a,b | P a b} /\ Q x} =
      {a,b | P a b /\ Q(a,b)}`] THEN
    MATCH_MP_TAC(MESON[SUM_EQ]
     `s = t /\ (!x. x IN s ==> f x = g x) ==> sum s f = sum t g`) THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`m1:num->num`; `m2:num->num`] THEN
      MATCH_MP_TAC(TAUT
       `(r ==> (p <=> q)) ==> (p /\ r <=> r /\ q)`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
      ASM_CASES_TAC `(p:(num->num)->real) m1 = &0` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(q:(num->num)->real) m2 = &0` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM REAL_ENTIRE; REAL_POW_ADD] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV;
      MAP_EVERY X_GEN_TAC [`m1:num->num`; `m2:num->num`] THEN
      REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_RING
       `z:real = x * y ==> (p * x) * q * y = (p * q) * z`) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_POW_ADD]] THEN
    MATCH_MP_TAC PRODUCT_MUL_GEN THEN
    REWRITE_TAC[REAL_POW_EQ_1; SET_RULE
     `{i | i IN UNIV /\ ~(p i \/ q i)} = {i | i IN {j | ~q j} /\ ~p i}`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ratpoly]) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT]]);;

let RATPOLYFUN_POW = prove
 (`!p r s. ratpolyfun s (\(n,k). p n k)
           ==> ratpolyfun s (\(n,k). (p n k) pow r)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN SIMP_TAC[real_pow; RATPOLYFUN_CONST; RATIONAL_CLOSED] THEN
  ASM_SIMP_TAC[RATPOLYFUN_MUL]);;

let RATPOLYFUN_TAC =
  REPEAT((MATCH_MP_TAC RATPOLYFUN_NEG) ORELSE
         (MATCH_MP_TAC RATPOLYFUN_POW) ORELSE
         (MATCH_MP_TAC RATPOLYFUN_ADD THEN CONJ_TAC) ORELSE
         (MATCH_MP_TAC RATPOLYFUN_SUB THEN CONJ_TAC) ORELSE
         (MATCH_MP_TAC RATPOLYFUN_MUL THEN CONJ_TAC)) THEN
  REWRITE_TAC[RATPOLYFUN_VAR] THEN
  ((MATCH_MP_TAC RATPOLYFUN_PARAMETER THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT] THEN
    NO_TAC) ORELSE
   (MATCH_MP_TAC RATPOLYFUN_CONST THEN
    ASM_SIMP_TAC[RATIONAL_CLOSED]));;

(* ------------------------------------------------------------------------- *)
(* The magical set avoiding all rational algebraic varieties.                *)
(* ------------------------------------------------------------------------- *)

let ratty = new_definition
 `ratty s t <=> ?p. ratpolyfun s p /\ p t = &0 /\ ~(!w. p w = &0)`;;

let magical_set = new_definition
 `magical_set s =
        INTERS { {z | ~((FST p)(FST(SND p) + Re z,SND(SND p) + Im z) = &0)} |
                 p IN (ratpolyfun s DELETE (\x. &0)) CROSS
                      (integer CROSS integer)}`;;

let IN_MAGICAL_SET_IMP_NOT_RATTY = prove
 (`!s d e n k. integer k /\ complex(d,e) IN magical_set s
             ==> ~ratty s (&n + d,k + e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [magical_set]) THEN
  REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[ratty; NOT_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:real#real->real` THEN
  DISCH_THEN(MP_TAC o SPECL [`&n:real`; `k:real`]) THEN
  REWRITE_TAC[IN_DELETE] THEN ASM_SIMP_TAC[IN; INTEGER_CLOSED] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; IM; RE]);;

let DENSE_MAGICAL_SET = prove
 (`closure (magical_set s) = (:complex)`,
  REWRITE_TAC[SET_RULE `s = UNIV <=> UNIV DIFF s = {}`] THEN
  REWRITE_TAC[GSYM INTERIOR_COMPLEMENT] THEN
  REWRITE_TAC[magical_set; INTERS_UNIONS] THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`] THEN
  MATCH_MP_TAC NOWHERE_DENSE_COUNTABLE_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC COUNTABLE_IMAGE THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN
    MATCH_MP_TAC COUNTABLE_CROSS THEN
    SIMP_TAC[COUNTABLE_CROSS; COUNTABLE_INTEGER; COUNTABLE_RATPOLYFUN;
             COUNTABLE_DELETE];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; SET_RULE
   `UNIV DIFF {z | ~P z} = {x | P x}`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_DELETE] THEN
  MAP_EVERY X_GEN_TAC [`p:real#real->real`; `n:real`; `k:real`] THEN
  REWRITE_TAC[IN] THEN STRIP_TAC THEN
  ABBREV_TAC `q:complex->real = \z. p(n + Re z,k + Im z)` THEN
  SUBGOAL_THEN `real_polynomial_function (q:complex->real)` ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC NOWHERE_DENSE_ALGEBRAIC_VARIETY THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[CONTRAPOS_THM; FORALL_PAIR_THM; FUN_EQ_THM] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `complex(x - n,y - k)`) THEN
    REWRITE_TAC[RE; IM; REAL_SUB_ADD2]] THEN
  SUBGOAL_THEN
   `q:complex->real = (\z. p(Re z,Im z)) o (\z. complex(n,k) + z)`
  SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[o_DEF; FUN_EQ_THM; RE; IM; RE_ADD; IM_ADD];
    MATCH_MP_TAC REAL_VECTOR_POLYNOMIAL_FUNCTION_o] THEN
  SIMP_TAC[VECTOR_POLYNOMIAL_FUNCTION_ADD; VECTOR_POLYNOMIAL_FUNCTION_ID;
           VECTOR_POLYNOMIAL_FUNCTION_CONST] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ratpolyfun]) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(num->num)->real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[POLY_EVAL_RATPOLY] THEN
  MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_SUM THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ratpoly]) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_MUL THEN
  REWRITE_TAC[real_polynomial_function_RULES] THEN
  MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_PRODUCT THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_POW THEN
  SPEC_TAC(`i:num`,`j:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
  SIMP_TAC[RE_DEF; real_polynomial_function_RULES; DIMINDEX_2; ARITH;
           EL; HD; TL; IM_DEF] THEN
  MATCH_MP_TAC num_INDUCTION THEN
  SIMP_TAC[real_polynomial_function_RULES; DIMINDEX_2; ARITH; EL; HD; TL]);;

let APPROACHABLE_WITHIN_AUGMENTED_MAGICAL_SET = prove
 (`!p s. open s /\ Cx(&0) limit_point_of s
       ==> ~trivial_limit (at(Cx(&0)) within (s INTER magical_set p))`,
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; GSYM IN_CLOSURE_DELETE] THEN
  REWRITE_TAC[SET_RULE `(s INTER t) DELETE a = (s DELETE a) INTER t`] THEN
  ASM_SIMP_TAC[CLOSURE_OPEN_INTER_SUPERSET; DENSE_MAGICAL_SET; SUBSET_UNIV;
               OPEN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* The key theorem supporting the WZ method.                                 *)
(* ------------------------------------------------------------------------- *)

let ZEILBERGER_GEN = prove
 (`!P e f h ff hh p q s.
        open s /\ Cx(&0) limit_point_of (s INTER {z | &0 < Re z}) /\
        ((!n. FINITE {k | ~(f n k = &0)}) /\
         (!n. FINITE {k | ~(h n k = &0)})) /\
        ((!n k. P n ==> (ff ---> f n k) (at(complex(&n,&k)) within
                                         { complex(&n,&k) + x | x IN s})) /\
         (!n k. P n ==> (hh ---> h n k) (at(complex(&n,&k))
                                    within { complex(&n,&k) + x | x IN s}))) /\
        (ratpolyfun e p /\ ratpolyfun e q) /\
        (!n. P n ==> ~(q(&n,&0) = &0)) /\
        (!n k. ~ratty e (n,k) /\ &0 < n
               ==> hh(complex(n,k)) =
                   p(n,k + &1) / q(n,k + &1) * ff(complex(n,k + &1)) -
                   p(n,k) / q(n,k) * ff(complex(n,k)))
        ==> !n. P n
                ==> sum (:num) (\k. h n k) = --(p(&n,&0) / q(&n,&0) * f n 0)`,
  let lemma = prove
   (`(f ---> l) (at a within {a + z | z IN s}) <=>
     ((\w. f(a + w)) ---> l) (at (Cx(&0)) within s)`,
    REWRITE_TAC[REALLIM_WITHIN] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[dist; COMPLEX_SUB_RZERO; VECTOR_ARITH
     `(a + z) - a:complex = z`]) in
  REWRITE_TAC[lemma] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_THEN `(P:num->bool) n` (K ALL_TAC) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?m.  ~(q(&n,&m + &1) = &0) /\
          (!k. ~(f n k = &0) ==> k < m) /\
          (!k. ~(h n k = &0) ==> k < m)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `FINITE {k | ~((f:num->num->real) n k = &0)} /\
      FINITE {k | ~((h:num->num->real) n k = &0)}`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `FINITE {k | (q:real#real->real)(&n,&k) = &0}`
    MP_TAC THENL
     [REWRITE_TAC[SET_RULE
       `{k | (q:real#real->real)(&n,&k) = &0} =
        {k | &k IN {x | (q:real#real->real)(&n,x) = &0}}`] THEN
      MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
      W(MP_TAC o PART_MATCH (lhs o rand)
        POLYNOMIAL_FUNCTION_FINITE_ROOTS o snd) THEN
      ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      UNDISCH_TAC `ratpolyfun e q` THEN
      REWRITE_TAC[ratpolyfun; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `s:(num->num)->real` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[POLY_EVAL_RATPOLY] THEN
      MATCH_MP_TAC POLYNOMIAL_FUNCTION_SUM THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ratpoly]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; REAL_MUL_ASSOC] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC POLYNOMIAL_FUNCTION_MUL THEN
      REWRITE_TAC[POLYNOMIAL_FUNCTION_CONST] THEN
      MATCH_MP_TAC POLYNOMIAL_FUNCTION_PRODUCT THEN
      ASM_SIMP_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC POLYNOMIAL_FUNCTION_POW THEN
      SPEC_TAC(`i:num`,`j:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
      REWRITE_TAC[EL; HD; POLYNOMIAL_FUNCTION_CONST] THEN
      MATCH_MP_TAC num_INDUCTION THEN
      REWRITE_TAC[EL; HD; POLYNOMIAL_FUNCTION_CONST; TL] THEN
      REWRITE_TAC[POLYNOMIAL_FUNCTION_ID];
      ALL_TAC] THEN
    REWRITE_TAC[IMP_IMP; GSYM FINITE_UNION] THEN DISCH_THEN
     (MP_TAC o SPEC `\i:num. i` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
    REWRITE_TAC[FORALL_IN_UNION; IN_ELIM_THM] THEN
    MATCH_MP_TAC(MESON[]
     `(!a. P a ==> Q(a + 1)) ==> ((?a. P a) ==> (?b. Q b))`) THEN
    SIMP_TAC[REAL_OF_NUM_ADD; ARITH_RULE `m < n + 1 <=> m <= n`] THEN
    MESON_TAC[ARITH_RULE `~((a + 1) + 1 <= a)`];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `at (Cx(&0)) within
     ((s INTER {z | &0 < Re z}) INTER magical_set e)`
        REALLIM_UNIQUE) THEN
  EXISTS_TAC `\z. sum (0..m) (\k. hh(complex(&n,&k) + z))` THEN
  ASM_SIMP_TAC[APPROACHABLE_WITHIN_AUGMENTED_MAGICAL_SET;
               OPEN_INTER; REWRITE_RULE[real_gt] OPEN_HALFSPACE_RE_GT] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `sum (:num) (\k. (h:num->num->real) n k) =
      sum (0..m) (\k. (h:num->num->real) n k)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_SUPERSET THEN
      REWRITE_TAC[SUBSET_UNIV; IN_UNIV; IN_NUMSEG; LE_0] THEN
      ASM_MESON_TAC[LT_IMP_LE];
      MATCH_MP_TAC REALLIM_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN
      STRIP_TAC THEN MATCH_MP_TAC REALLIM_WITHIN_SUBSET THEN
      EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\z. sum (0..m)
              (\k. p(&n + Re z,(&k + &1) + Im z) /
                   q(&n + Re z,(&k + &1) + Im z) *
                   ff(complex (&n,&k + &1) + z) -
                   p(&n + Re z,&k + Im z) /
                   q(&n + Re z,&k + Im z) *
                   ff(complex (&n,&k) + z))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; GSYM DIST_NZ] THEN X_GEN_TAC `w:complex` THEN
      STRIP_TAC THEN REWRITE_TAC[complex_add; RE; IM] THEN
      MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FINITE_INTSEG] THEN
      X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH
       `(x + &1) + y = (x + y) + &1`] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC IN_MAGICAL_SET_IMP_NOT_RATTY THEN
        ASM_REWRITE_TAC[COMPLEX; INTEGER_CLOSED] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTER]) THEN
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; SUM_DIFFS_ALT; LE_0] THEN
    SUBGOAL_THEN
     `--(p (&n,&0) / q (&n,&0) * f n 0):real =
      p(&n,&(m + 1)) / q(&n,&(m + 1)) * f n (m + 1) -
      p(&n,&0) / q(&n,&0) * f n 0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_RING `b = &0 ==> --y = a * b - y`) THEN
      ASM_MESON_TAC[ARITH_RULE `~(m + 1 < m)`];
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC REALLIM_MUL THEN
    (CONJ_TAC THENL
      [ALL_TAC;
       MATCH_MP_TAC REALLIM_WITHIN_SUBSET THEN
       EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
       ASM SET_TAC[]]) THEN
    MATCH_MP_TAC(MESON[REAL_CONTINUOUS_AT_WITHIN; REAL_CONTINUOUS_WITHIN]
     `f real_continuous at z /\ f z = l ==> (f ---> l) (at z within s)`) THEN
    REWRITE_TAC[IM_CX; RE_CX; REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_DIV_AT THEN
    ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_ADD_RID; GSYM REAL_OF_NUM_ADD] THEN
    (CONJ_TAC THENL
      [UNDISCH_TAC `ratpolyfun e p`; UNDISCH_TAC `ratpolyfun e q`]) THEN
    REWRITE_TAC[ratpolyfun; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `s:(num->num)->real` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[POLY_EVAL_RATPOLY] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_SUM THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ratpoly]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_PRODUCT THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_POW THEN
    SPEC_TAC(`i:num`,`j:num`) THEN
    REPLICATE_TAC 2 (TRY(MATCH_MP_TAC num_INDUCTION THEN
           REWRITE_TAC[EL; HD; TL] THEN CONJ_TAC)) THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
    REWRITE_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT]]);;

(* ------------------------------------------------------------------------- *)
(* The basic case that we normally use.                                      *)
(* ------------------------------------------------------------------------- *)

let ZEILBERGER = prove
 (`!P e f h ff hh p q.
        ((!n. FINITE {k | ~(f n k = &0)}) /\
         (!n. FINITE {k | ~(h n k = &0)})) /\
        ((!n k. P n ==> (ff ---> f n k) (at(complex(&n,&k)))) /\
         (!n k. P n ==> (hh ---> h n k) (at(complex(&n,&k))))) /\
        (ratpolyfun e p /\ ratpolyfun e q) /\
        (!n. P n ==> ~(q(&n,&0) = &0)) /\
        (!n k. ~ratty e (n,k) /\ &0 < n
               ==> hh(complex(n,k)) =
                   p(n,k + &1) / q(n,k + &1) * ff(complex(n,k + &1)) -
                   p(n,k) / q(n,k) * ff(complex(n,k)))
        ==> !n. P n
                ==> sum (:num) (\k. h n k) = --(p(&n,&0) / q(&n,&0) * f n 0)`,
  MP_TAC ZEILBERGER_GEN THEN
  REPLICATE_TAC 8 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `(:complex)`) THEN
  REWRITE_TAC[OPEN_UNIV; INTER_UNIV] THEN
  GEN_REWRITE_TAC LAND_CONV [IMP_CONJ] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM IN_CLOSURE_DELETE] THEN SIMP_TAC[SET_RULE
     `~(a IN s) ==> s DELETE a = s`; IN_ELIM_THM; RE_CX; REAL_LT_REFL] THEN
    REWRITE_TAC[RE_DEF; GSYM real_gt; CLOSURE_HALFSPACE_COMPONENT_GT] THEN
    REWRITE_TAC[GSYM RE_DEF; RE_CX; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `!w. {w + z | z IN (:complex)} = (:complex)`
     (fun th -> REWRITE_TAC[th; WITHIN_UNIV]) THEN
    GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[IN_UNIV; COMPLEX_RING `w + z:complex = y <=> z = y - w`] THEN
    REWRITE_TAC[EXISTS_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Finite-support preprocessing for summands over the natural numbers.       *)
(* ------------------------------------------------------------------------- *)

let FINITE_SUPPORT_BINOM = prove
 (`!m n. (!k. k <= m k) ==> FINITE {k | ~(binom(n,m k) = 0)}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  REWRITE_TAC[FINITE_NUMSEG; BINOM_EQ_0; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ARITH_TAC);;

let FINITE_SUPPORT_ADD = prove
 (`!f g:A->num.
        FINITE {k | ~(f k = 0)} /\ FINITE {k | ~(g k = 0)}
        ==> FINITE {k | ~(f k + g k = 0)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FINITE_UNION] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN ARITH_TAC);;

let FINITE_SUPPORT_MUL = prove
 (`!f g:A->num.
        FINITE {k | ~(f k = 0)} \/ FINITE {k | ~(g k = 0)}
        ==> FINITE {k | ~(f k * g k = 0)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN CONV_TAC NUM_RING);;

let rec FINITE_SUPPORT_TAC gl =
  ((MATCH_MP_TAC FINITE_SUPPORT_BINOM THEN ARITH_TAC) ORELSE
   (MATCH_MP_TAC FINITE_SUPPORT_ADD THEN
    CONJ_TAC THEN FINITE_SUPPORT_TAC) ORELSE
   (MATCH_MP_TAC FINITE_SUPPORT_MUL THEN
     ((DISJ1_TAC THEN FINITE_SUPPORT_TAC) ORELSE
      (DISJ2_TAC THEN FINITE_SUPPORT_TAC)))) gl;;

(* ------------------------------------------------------------------------- *)
(* A variant over the reals that devolves to the above at the base.          *)
(* ------------------------------------------------------------------------- *)

let FINITE_SUPPORT_REAL_ADD = prove
 (`!f g:A->real.
        FINITE {k | ~(f k = &0)} /\ FINITE {k | ~(g k = &0)}
        ==> FINITE {k | ~(f k + g k = &0)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FINITE_UNION] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let FINITE_SUPPORT_REAL_SUB = prove
 (`!f g:A->real.
        FINITE {k | ~(f k = &0)} /\ FINITE {k | ~(g k = &0)}
        ==> FINITE {k | ~(f k - g k = &0)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FINITE_UNION] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let FINITE_SUPPORT_REAL_INV = prove
 (`!f:A->real.
        FINITE {k | ~(f k = &0)} ==> FINITE {k | ~(inv(f k) = &0)}`,
  REWRITE_TAC[REAL_INV_EQ_0]);;

let FINITE_SUPPORT_REAL_POW = prove
 (`!f:A->real n.
        FINITE {k | ~(f k = &0)} /\ ~(n = 0)
        ==> FINITE {k | ~(f k pow n = &0)}`,
  SIMP_TAC[REAL_POW_EQ_0] THEN SET_TAC[]);;

let FINITE_SUPPORT_SPOW = prove
 (`!f:A->real y.
        FINITE {k | ~(f k = &0)} /\ ~(y = &0)
        ==> FINITE {k | ~(f k spow y = &0)}`,
  REPEAT GEN_TAC THEN SIMP_TAC[SPOW_EQ_0] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  SET_TAC[]);;

let FINITE_SUPPORT_REAL_MUL = prove
 (`!f g:A->real.
        FINITE {k | ~(f k = &0)} \/ FINITE {k | ~(g k = &0)}
        ==> FINITE {k | ~(f k * g k = &0)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[REAL_ENTIRE] THEN SET_TAC[]);;

let FINITE_SUPPORT_REAL_DIV = prove
 (`!f g:A->real.
        FINITE {k | ~(f k = &0)} \/ FINITE {k | ~(g k = &0)}
        ==> FINITE {k | ~(f k / g k = &0)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[REAL_DIV_EQ_0] THEN SET_TAC[]);;

let FINITE_SUPPORT_REAL_OF_NUM = prove
 (`!f:A->num.
        FINITE {k | ~(f k = 0)} ==> FINITE {k | ~(&(f k) = &0)}`,
  REWRITE_TAC[REAL_OF_NUM_EQ]);;

let rec REAL_FINITE_SUPPORT_TAC gl =
  ((MATCH_MP_TAC FINITE_SUPPORT_REAL_OF_NUM THEN FINITE_SUPPORT_TAC) ORELSE
   (MATCH_MP_TAC FINITE_SUPPORT_REAL_INV THEN
    REAL_FINITE_SUPPORT_TAC) ORELSE
   (MATCH_MP_TAC FINITE_SUPPORT_REAL_POW THEN
    CONJ_TAC THENL [REAL_FINITE_SUPPORT_TAC; ARITH_TAC]) ORELSE
   (MATCH_MP_TAC FINITE_SUPPORT_SPOW THEN
    CONJ_TAC THENL [REAL_FINITE_SUPPORT_TAC; REAL_ARITH_TAC]) ORELSE
   ((MATCH_MP_TAC FINITE_SUPPORT_REAL_ADD ORELSE
     MATCH_MP_TAC FINITE_SUPPORT_REAL_SUB) THEN
   CONJ_TAC THEN FINITE_SUPPORT_TAC) ORELSE
   ((MATCH_MP_TAC FINITE_SUPPORT_REAL_MUL ORELSE
     MATCH_MP_TAC FINITE_SUPPORT_REAL_DIV) THEN
    ((DISJ1_TAC THEN REAL_FINITE_SUPPORT_TAC) ORELSE
      (DISJ2_TAC THEN REAL_FINITE_SUPPORT_TAC)))) gl;;

(* ------------------------------------------------------------------------- *)
(* Establish support containment, universalization and finite support.       *)
(* ------------------------------------------------------------------------- *)

let support_containment =
  let dummy = prove
   (`(!n k. ~(k IN s n) ==> f n k = &0)
     ==> !n. sum (s n) (f n) = sum (s n) (f n)`,
    REWRITE_TAC[]) in
  fun ntm tm ->
    let th = PART_MATCH rand dummy (mk_forall(ntm,mk_eq(tm,tm))) in
    let tm' = lhand(concl th) in
    let th' = funpow 2 BINDER_CONV
       (RAND_CONV (LAND_CONV(TRY_CONV BETA_CONV))) tm' in
    rand(concl th');;

let finite_support =
  let dummy = prove
   (`(!n. FINITE {k | ~(f n k = &0)})
     ==> !n. sum (s n) (f n) = sum (s n) (f n)`,
    REWRITE_TAC[]) in
  fun ntm tm ->
    let th = PART_MATCH rand dummy (mk_forall(ntm,mk_eq(tm,tm))) in
    let tm' = lhand(concl th) in
    let th' =
      BINDER_CONV (RAND_CONV (RAND_CONV (ABS_CONV (BINDER_CONV
        (LAND_CONV (RAND_CONV (LAND_CONV (TRY_CONV BETA_CONV)))))))) tm' in
    rand(concl th');;

let SUPPORT_CONTAINMENT_TAC =
  REWRITE_TAC[IN_NUMSEG; REAL_ENTIRE; REAL_DIV_EQ_0; REAL_OF_NUM_EQ;
              BINOM_EQ_0; SPOW_EQ_0; REAL_POW_EQ_0; ARITH_EQ; FACT_NZ;
              REAL_NEG_EQ_0; IN_UNIV; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_ARITH_TAC;;

let SUPPORT_CONTAINMENT_IMP_UNIVERSALIZE = prove
 (`(!n k. ~(k IN s n) ==> f n k = &0)
   ==> !n:num. sum (s n) (f n) = sum (:num) (f n)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
  ASM SET_TAC[]);;

let SUPPORT_CONTAINMENT_IMP_FINITE = prove
 (`(!n k. ~(k IN a n..b n) ==> f n k = &0)
   ==> !n:num. FINITE {k | ~(f n k = &0)}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `a(n:num)..b n` THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ASM SET_TAC[]);;

let SUPPORT_RULE ntm tm =
  let cth = prove(support_containment ntm tm,SUPPORT_CONTAINMENT_TAC) in
  let eth =
   CONV_RULE (BINDER_CONV (BINOP_CONV (RAND_CONV (TRY_CONV BETA_CONV))))
             (MATCH_MP SUPPORT_CONTAINMENT_IMP_UNIVERSALIZE cth) in
  let fth =
    try MATCH_MP SUPPORT_CONTAINMENT_IMP_FINITE cth
    with Failure _ ->
      prove(finite_support ntm tm,GEN_TAC THEN REAL_FINITE_SUPPORT_TAC) in
  cth,eth,fth;;

(* ------------------------------------------------------------------------- *)
(* Convert core term into its limit variant.                                 *)
(* ------------------------------------------------------------------------- *)

let pats =
  [`&(binom(p,q))`,`rbinom(&p,&q)`;
   `&(FACT p)`,`rfact(&p)`;
   `&(p + q)`,`&p + &q`;
   `&(p - q)`,`&p - &q`;
   `&(p * q)`,`&p * &q`;
   `&(p EXP n)`,`&p pow n`];;

let repper tm =
  tryfind (fun (ptm,qtm) -> instantiate (term_match [] ptm tm) qtm)
          pats;;

let ron_tm = `(&):num->real`;;

let real_ty = `:real`;;

let rec limit_variant ktm ntm tm =
  let tm' =  try repper tm with Failure _ -> tm in
  if is_comb tm' then
     let ltm,rtm = dest_comb tm' in
     if ltm = ron_tm && (rtm = ktm || rtm = ntm)
     then mk_var(fst(dest_var rtm),real_ty)
     else mk_comb(limit_variant ktm ntm ltm,limit_variant ktm ntm rtm)
  else tm';;

(* ------------------------------------------------------------------------- *)
(* Convert the initial problem to the three key theorems.                    *)
(* ------------------------------------------------------------------------- *)

let add_tm = `(+):num->num->num`;;

let pth_mult = prove
 (`(!k. ~(k IN s) ==> f k = &0) /\
   sum s (\k. f k) = sum (:num) (\k. f k) /\
   FINITE {k | ~(f k = &0)}
   ==> !c. (!k. ~(k IN s) ==> c * f k = &0) /\
           c * sum s (\k. f k) = sum (:num) (\k. c * f k) /\
           FINITE {k | ~(c * f k = &0)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN
  STRIP_TAC THEN GEN_TAC THEN REPEAT CONJ_TAC THEN
  ASM_REWRITE_TAC[SUM_LMUL] THEN ASM_SIMP_TAC[REAL_ENTIRE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM]);;

let pth_add = prove
 (`((!k. ~(k IN s) ==> f' k = &0) /\
    f = sum (:num) (\k. f' k) /\
    FINITE {k | ~(f' k = &0)}) /\
   ((!k. ~(k IN t) ==> g' k = &0) /\
    g = sum (:num) (\k. g' k) /\
    FINITE {k | ~(g' k = &0)})
   ==> ((!k. ~(k IN s UNION t) ==> f' k + g' k = &0) /\
         f + g =
         sum (:num) (\k. f' k + g' k) /\
         FINITE {k | ~(f' k + g' k = &0)})`,
  SIMP_TAC[IN_UNION; DE_MORGAN_THM; REAL_ADD_LID] THEN
  SIMP_TAC[SUM_ADD_GEN; IN_UNIV; ETA_AX] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o last o CONJUNCTS)) THEN
  REWRITE_TAC[IMP_IMP; GSYM FINITE_UNION] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let OUTPUT_SIMP_CONV =
  REWRITE_CONV[real_div; REAL_INV_MUL; REAL_INV_POW; REAL_INV_INV] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; MULT_CLAUSES] THENC
  REWRITE_CONV[CONJUNCT1 binom; BINOM_REFL] THENC
  REAL_RAT_REDUCE_CONV THENC
  REWRITE_CONV[REAL_MUL_LZERO; REAL_INV_0; REAL_MUL_RZERO] THENC
  REAL_RAT_REDUCE_CONV THENC
  REWRITE_CONV[REAL_MUL_LZERO; REAL_INV_0; REAL_MUL_RZERO] THENC
  REAL_RAT_REDUCE_CONV;;

let WZ_INITIAL_REDUCTIONS ntm stm rtm ctm atm =
  let ktm,bod = dest_abs (rand stm) in
  let parms =
    filter (fun t -> type_of t = `:real`)
           (map (fun t -> if type_of t = `:num` then mk_comb(`real_of_num`,t)
                          else t)
                (subtract (frees stm) [ntm])) in
  let nntm = mk_var(fst(dest_var ntm),real_ty)
  and kktm = mk_var(fst(dest_var ktm),real_ty) in

  let cth0,eth0,fth0 = SUPPORT_RULE ntm stm in
  let cmbth0 =
    GEN ntm (CONJ (SPEC ntm cth0) (CONJ  (SPEC ntm eth0) (SPEC ntm fth0))) in
  let cths =
    map (fun (c,i) ->
          let ntm' = if i = 0 then ntm
                     else mk_comb(mk_comb(add_tm,ntm),mk_small_numeral i) in
          SPEC c (MATCH_MP pth_mult (SPEC ntm' cmbth0)))
        (zip ctm (0--(length ctm-1))) in
  let efth1 =
    CONJUNCT2
     (end_itlist (fun th1 th2 -> MATCH_MP pth_add (CONJ th1 th2)) cths) in
  let eth1 = CONJUNCT1 efth1
  and fth1 = CONJUNCT2 efth1 in
  let eth = GEN ntm eth1
  and fth = GEN ntm fth1 in

  let hbod = body(rand(rand(concl eth1)))
  and rtm' = subst [nntm,mk_comb(ron_tm,ntm); kktm,mk_comb(ron_tm,ktm)]
                   rtm in
  let ptm = if atm = [] then concl TRUTH
            else list_mk_conj atm in
  let pth =
   (REWRITE_CONV[REAL_OF_NUM_EQ; REAL_OF_NUM_LT;
                 REAL_OF_NUM_LE; REAL_OF_NUM_GT;
                 REAL_OF_NUM_GE; REAL_OF_NUM_SUC;
                 REAL_OF_NUM_ADD; REAL_OF_NUM_MUL;
                 REAL_OF_NUM_POW] THENC
    REWRITE_CONV[GSYM LE_SUC_LT;
                 ARITH_RULE `~(m = n) <=> m + 1 <= n \/ n + 1 <= m`] THENC
    REWRITE_CONV[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_LT;
                 GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_GT;
                 GSYM REAL_OF_NUM_GE; GSYM REAL_OF_NUM_SUC;
                 GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
                 GSYM REAL_OF_NUM_POW]) ptm in

  let th0 =
    PURE_REWRITE_RULE[RE; IM]
     (CONV_RULE (TOP_DEPTH_CONV GEN_BETA_CONV)
    (SPECL [mk_abs(ntm,rand(concl pth));
            mk_setenum(parms,`:real`);
            list_mk_abs([ntm;ktm],bod);
            list_mk_abs([ntm;ktm],hbod);
            mk_abs(`z:complex`,
                   subst [`Re z`,nntm; `Im z`,kktm]
                         (limit_variant ktm ntm bod));
            mk_abs(`z:complex`,
                   subst [`Re z`,nntm; `Im z`,kktm]
                         (limit_variant ktm ntm hbod));
            mk_gabs(mk_pair(nntm,kktm),lhand rtm');
            mk_gabs(mk_pair(nntm,kktm),rand rtm')]
     ZEILBERGER)) in
  let th1 =
   MP (GEN_REWRITE_RULE I [IMP_CONJ] th0)
      (CONJ fth0 fth) in
  let th2 = GEN_REWRITE_RULE (RAND_CONV o BINDER_CONV o RAND_CONV o LAND_CONV)
   [GSYM eth] th1 in
  let th3 = GEN_REWRITE_RULE (RAND_CONV o BINDER_CONV o LAND_CONV)
                [SYM pth] th2 in
  let th4 = PURE_REWRITE_RULE[CONJUNCT1(SPEC_ALL IMP_CLAUSES)] th3 in

  let atms = filter (fun a -> not(free_in ntm a)) atm in

  atms,th4;;

(* ------------------------------------------------------------------------- *)
(* Normalize terms to separate out non-constant part (usually linear form).  *)
(* ------------------------------------------------------------------------- *)

let SEPARATE_CONSTANT_CONV =
  let pth = prove
   (`x + &(SUC n) = (x + &1) + &n /\
     x + -- &(SUC n) = (x - &1) + -- &n`,
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC) in
  let conv0 = GEN_REWRITE_CONV I [REAL_ADD_RID; REAL_ARITH `x + -- &0 = x`]
  and conv1 =
   (RAND_CONV(RAND_CONV num_CONV) THENC
    GEN_REWRITE_CONV I [CONJUNCT1 pth]) ORELSEC
   (RAND_CONV(RAND_CONV(RAND_CONV num_CONV)) THENC
    GEN_REWRITE_CONV I [CONJUNCT2 pth]) in
  REAL_POLY_CONV THENC
  PURE_REWRITE_CONV[REAL_ADD_ASSOC] THENC
  REPEATC conv1 THENC TRY_CONV conv0;;

(* ------------------------------------------------------------------------- *)
(* Apply conv to rbinom, rfact, RHS argument of spow.                        *)
(* ------------------------------------------------------------------------- *)

let pat_rfact = `rfact x`
and pat_rbinom = `rbinom(x,y)`
and pat_spow = `x spow y`;;

let APPLY_FBPOW_CONV conv tm =
  if can (term_match [] pat_rfact) tm ||
     can (term_match [] pat_spow) tm
  then RAND_CONV conv tm
  else if can (term_match [] pat_rbinom) tm
  then RAND_CONV(BINOP_CONV conv) tm
  else failwith "APPLY_FBPOW_CONV";;

(* ------------------------------------------------------------------------- *)
(* Expand `rfact(n + &1)` and `rfact(n - &1)`                                *)
(* ------------------------------------------------------------------------- *)

let pth_up = prove
 (`~ratty e (n,k)
   ==> ratpolyfun e (\(n,k). p n k) /\ ~(!n k. p n k + &1 = &0)
       ==> rfact(p n k + &1) = (p n k + &1) * rfact(p n k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFACT_STEP_UP] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ratty]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(\(n,k). p n k + &1):real#real->real`) THEN
  ASM_REWRITE_TAC[REAL_ADD_LINV] THEN
  ASM_SIMP_TAC[RATPOLYFUN_ADD; RATPOLYFUN_CONST; RATIONAL_CLOSED] THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM]);;

let pth_down = prove
 (`~ratty e (n,k) ==> rfact(p n k - &1) = rfact(p n k) / p n k`,
  REWRITE_TAC[RFACT_STEP_DOWN]);;

let RFACT_STEP_CONV nrth =
  let pth_down' = MATCH_MP pth_down nrth
  and pth_up' = MATCH_MP pth_up nrth in
  fun tm ->
    try PART_MATCH lhs pth_down' tm with Failure _ ->
    let th = PART_MATCH (lhs o rand) pth_up' tm in
    let sth = prove(lhand(concl th),
     CONJ_TAC THENL [RATPOLYFUN_TAC; ALL_TAC] THEN
     DISCH_THEN(MP_TAC o SPECL [`&1 / &12345`; `&7 / &44`]) THEN
     CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC) in
    MP th sth;;

(* ------------------------------------------------------------------------- *)
(* Expand `rbinom(n +/- &1,k)`, `rbinom(n,k +/- &1)`                         *)
(* ------------------------------------------------------------------------- *)

let pth_top_down = prove
 (`~ratty e (n,k)
   ==> rbinom(p n k - &1,q n k) =
       (p n k - q n k) / p n k * rbinom(p n k,q n k)`,
  REWRITE_TAC[RBINOM_TOP_STEP_DOWN]);;

let pth_both_down = prove
 (`~ratty e (n,k)
   ==> rbinom(p n k - &1,q n k - &1) =
       q n k / p n k * rbinom(p n k,q n k)`,
  REWRITE_TAC[RBINOM_STEP_BOTH_DOWN]);;

let pth_both_up,pth_top_up,pth_bottom_up,pth_bottom_down =
  let ths = (CONJUNCTS o prove)
 (`(~ratty e (n,k)
    ==> (ratpolyfun e (\(n,k). p n k) /\ ratpolyfun e (\(n,k). q n k)) /\
        ~(!n k. p n k + &1 = &0) /\ ~(!n k. q n k + &1 = &0)
        ==> rbinom(p n k + &1,q n k + &1) =
            (p n k + &1) / (q n k + &1) * rbinom(p n k,q n k)) /\
   (~ratty e (n,k)
    ==> (ratpolyfun e (\(n,k). p n k) /\ ratpolyfun e (\(n,k). q n k)) /\
        (~(!n k. p n k + &1 = &0) /\ ~(!n k. p n k + &1 = q n k))
        ==> rbinom(p n k + &1,q n k) =
            (p n k + &1) / (p n k - q n k + &1) * rbinom (p n k,q n k)) /\
   (~ratty e (n,k)
    ==> (ratpolyfun e (\(n,k). p n k) /\ ratpolyfun e (\(n,k). q n k)) /\
        ~(!n k. q n k + &1 = &0)
        ==> rbinom(p n k,q n k + &1) =
            (p n k - q n k) / (q n k + &1) * rbinom(p n k,q n k)) /\
   (~ratty e (n,k)
    ==> (ratpolyfun e (\(n,k). p n k) /\ ratpolyfun e (\(n,k). q n k)) /\
        ~(!n k. p n k + &1 = q n k)
        ==> rbinom(p n k,q n k - &1) =
            q n k / (p n k - q n k + &1) * rbinom(p n k,q n k))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RBINOM_STEP_BOTH_UP;
    MATCH_MP_TAC RBINOM_TOP_STEP;
    MATCH_MP_TAC RBINOM_BOTTOM_STEP;
    MATCH_MP_TAC RBINOM_BOTTOM_STEP_DOWN] THEN
  REPEAT CONJ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ratty]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_SUB_0] THEN
  DISCH_THEN(fun th -> W(fun (asl,w) ->
    MP_TAC(SPEC (mk_gabs(`(n:real,k:real)`,lhand(rand w))) th))) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ ~r ==> ~(p /\ q /\ ~r) ==> ~q`) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[RATPOLYFUN_SUB; RATPOLYFUN_ADD; RATPOLYFUN_CONST;
               RATIONAL_CLOSED; REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[REAL_SUB_0]) in
  el 0 ths,el 1 ths,el 2 ths,el 3 ths;;

let RBINOM_STEP_CONV nrth =
  let ths =
    map (C MATCH_MP nrth)
        [pth_top_down; pth_both_down; pth_both_up;
         pth_top_up; pth_bottom_up; pth_bottom_down] in
  let pth_top_down' = el 0 ths
  and pth_both_down' = el 1 ths
  and pth_both_up' = el 2 ths
  and pth_top_up' = el 3 ths
  and pth_bottom_up' = el 4 ths
  and pth_bottom_down' = el 5 ths in
  fun tm ->
    try PART_MATCH lhs pth_both_down' tm with Failure _ ->
    try PART_MATCH lhs pth_top_down' tm with Failure _ ->
    let th = try PART_MATCH (lhs o rand) pth_both_up' tm with Failure _ ->
             try PART_MATCH (lhs o rand) pth_top_up' tm with Failure _ ->
             try PART_MATCH (lhs o rand) pth_bottom_up' tm with Failure _ ->
             PART_MATCH (lhs o rand) pth_bottom_down' tm in
    let sth = prove(lhand(concl th),
     CONJ_TAC THENL [REPEAT CONJ_TAC THEN RATPOLYFUN_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN DISCH_THEN(fun th ->
       MP_TAC( SPECL [`&1 / &12345`; `&7 / &44`] th) THEN
       MP_TAC( SPECL [`-- &99 / &12`; `&3 / &4`] th) THEN
       MP_TAC( SPECL [`&0`; `&55`] th)) THEN CONV_TAC REAL_RING) in
    MP th sth;;

(* ------------------------------------------------------------------------- *)
(* And the trivial thing for spow.                                           *)
(* ------------------------------------------------------------------------- *)

let SPOW_STEP_CONV =
  GEN_REWRITE_CONV I [SPOW_STEP_UP; SPOW_STEP_DOWN];;

(* ------------------------------------------------------------------------- *)
(* Discharge nonzeroness conditions away from rational varieties.            *)
(* ------------------------------------------------------------------------- *)

let pth_zero = prove
 (`!x. ~rational x ==> ~(x = &0)`,
  MESON_TAC[RATIONAL_CLOSED]);;

let pth_rfact = prove
 (`!x. ~(rational x /\ x <= -- &1) ==> ~(rfact x = &0)`,
  GEN_TAC THEN REWRITE_TAC[RFACT_EQ_0] THEN
  ASM_CASES_TAC `integer x` THEN ASM_SIMP_TAC[RATIONAL_CLOSED] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; REAL_LT_INTEGERS] THEN REAL_ARITH_TAC);;

let pth_rbinom = prove
 (`!x y. ~(rational x /\ x <= -- &1) /\
         ~(rational y /\ y <= -- &1) /\
         ~(rational(x - y) /\ x - y <= -- &1)
         ==> ~(rbinom(x,y) = &0)`,
  SIMP_TAC[rbinom; REAL_DIV_EQ_0; REAL_ENTIRE; pth_rfact]);;

let pth_spow = prove
 (`~(x = &0) /\ ~rational y ==> ~(x spow y = &0)`,
  STRIP_TAC THEN ASM_REWRITE_TAC[SPOW_EQ_0; COS_EQ_0] THEN
  REWRITE_TAC[REAL_EQ_MUL_RCANCEL; PI_NZ] THEN
  ASM_MESON_TAC[RATIONAL_CLOSED]);;

let pth_main = prove
 (`~ratty e (n,k)
   ==> ratpolyfun e (\(n,k). p n k) /\ ~(?c. !n k. p n k = c)
       ==> ~rational(p n k)`,
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_IMP] THEN STRIP_TAC THEN
  REWRITE_TAC[ratty] THEN
  EXISTS_TAC `\(x,y). (p:real->real->real) x y - p n k` THEN
  ASM_SIMP_TAC[RATPOLYFUN_SUB; RATPOLYFUN_CONST; REAL_SUB_REFL] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_SUB_0] THEN ASM_MESON_TAC[]);;

let NONZERO_RATTY_TAC =
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  REWRITE_TAC[REAL_POW_EQ_0; REAL_NEG_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  TRY(GEN_REWRITE_TAC RAND_CONV [SPOW_EQ_0] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  (MATCH_MP_TAC pth_rfact ORELSE
   (MATCH_MP_TAC pth_spow THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) ORELSE
   (MATCH_MP_TAC pth_rbinom THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC]) ORELSE
   MATCH_MP_TAC pth_zero) THEN
  TRY(DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC) THEN
  TRY(DISCH_THEN(MP_TAC o CONJUNCT1)) THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP pth_main) THEN
  (CONJ_TAC THENL [RATPOLYFUN_TAC; ALL_TAC]) THEN
  DISCH_THEN(CHOOSE_THEN (fun th ->
    MP_TAC (SPECL [`&1 / &12345`; `&7 / &44`] th) THEN
     MP_TAC (SPECL [`-- &99 / &12`; `&3 / &4`] th) THEN
     MP_TAC (SPECL [`&0`; `&55`] th))) THEN
  CONV_TAC REAL_RING;;

let TACTIC_4 (asl,w) =
  let nrth =
    snd(find (can (term_match [] `~ratty e (n,k)` o concl o snd)) asl) in
 (CONV_TAC(ONCE_DEPTH_CONV(APPLY_FBPOW_CONV SEPARATE_CONSTANT_CONV)) THEN
  CONV_TAC(TOP_DEPTH_CONV
    (RFACT_STEP_CONV nrth ORELSEC RBINOM_STEP_CONV nrth ORELSEC
     SPOW_STEP_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV(APPLY_FBPOW_CONV REAL_POLY_CONV)) THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; REAL_INV_POW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  W(fun (asl,w) ->
     let itms = find_terms
       (fun t -> is_comb t && rator t = `real_inv`) w in
     SUBGOAL_THEN
      (list_mk_conj (map (fun t -> mk_neg(mk_eq(rand t,`&0`))) itms))
     MP_TAC)
  THENL [NONZERO_RATTY_TAC; SPECIAL_REAL_FIELD_TAC]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic side conditions.                                               *)
(* ------------------------------------------------------------------------- *)

let pth = REAL_ARITH `(&0 <= x /\ &0 <= y) /\
                      (~(x = &0) \/ ~(y = &0)) ==> ~(x + y = &0)`
and real_add_tm = `real_add`
and real_mul_tm = `real_mul`;;

let NONZERO_DIVIS_TAC =
  CONV_TAC(RAND_CONV(LAND_CONV REAL_POLY_CONV)) THEN
  REWRITE_TAC[REAL_ADD_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_FIELD
   `a + b = &0 ==> --(inv(b) * a) = inv(b) * b`)) THEN
  REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV
   (COMB2_CONV (RAND_CONV REAL_POLY_CONV) REAL_RAT_REDUCE_CONV)) THEN
  W(fun (asl,w) ->
    let ts = map lhand (striplist (dest_binop real_add_tm) (lhand(rand w))) in
    let cc = abs_num(num_1 // end_itlist gcd_num (map rat_of_term ts)) in
    DISCH_THEN(MP_TAC o AP_TERM (mk_comb(real_mul_tm,term_of_rat cc)))) THEN
  REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV
   (COMB2_CONV (RAND_CONV REAL_POLY_CONV) REAL_RAT_REDUCE_CONV)) THEN
  MATCH_MP_TAC(MESON[] `integer a /\ ~(integer b) ==> ~(a = b)`) THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[INTEGER_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[divides] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV) [EQ_SYM_EQ] THEN
  REWRITE_TAC[MULT_EQ_1] THEN CONV_TAC NUM_REDUCE_CONV;;

let rec NONZERO_INEQ_TAC gl =
 (REWRITE_TAC[REAL_POW_EQ_0; REAL_ENTIRE; DE_MORGAN_THM; ARITH_EQ] THEN
  REPEAT CONJ_TAC THEN
  TRY ASM_REAL_ARITH_TAC THEN
  TRY NONZERO_DIVIS_TAC THEN
  TRY (MATCH_MP_TAC pth THEN CONJ_TAC THENL
        [CONJ_TAC THEN
         REPEAT(ASM_ARITH_TAC ORELSE
                (MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) ORELSE
                (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) ORELSE
                (MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC NUM_REDUCE_CONV)) THEN
         NO_TAC;
         ((DISJ1_TAC THEN NONZERO_INEQ_TAC) ORELSE
          (DISJ2_TAC THEN NONZERO_INEQ_TAC))]) THEN
  NONZERO_DIVIS_TAC) gl;;

let NONZERO_ADHOC_TAC =
  REWRITE_TAC[REAL_POW_EQ_0; REAL_ENTIRE; DE_MORGAN_THM; ARITH_EQ] THEN
  REPEAT CONJ_TAC THEN
  CONV_TAC(RAND_CONV(LAND_CONV REAL_POLY_CONV)) THEN
  TRY NONZERO_INEQ_TAC;;

let REAL_CONTINUOUS_ADHOC_TAC =
  REPEAT
   (MATCH_MP_TAC REAL_CONTINUOUS_POW ORELSE
    MATCH_MP_TAC REAL_CONTINUOUS_NEG ORELSE
    (MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN CONJ_TAC) ORELSE
    (MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC) ORELSE
    (MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC)) THEN
  REWRITE_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT;
              REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONST];;

let REALLIM_NONZERO_TAC =
  REWRITE_TAC[RE; IM] THEN
  REWRITE_TAC[rbinom; RFACT_EQ_0; REAL_ENTIRE; REAL_DIV_EQ_0;
              SPOW_EQ_0; REAL_POW_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REAL_ARITH_TAC;;

let REALLIM_INEQ_TAC =
  REWRITE_TAC[RE; IM] THEN ASM_REAL_ARITH_TAC;;

let REALLIM_CONTINUOUS_TAC =
  REPEAT
  (MATCH_MP_TAC REAL_CONTINUOUS_INV_RFACT_COMPOSE_WITHIN ORELSE
   (MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHIN THEN CONJ_TAC THENL
     [ALL_TAC; REALLIM_NONZERO_TAC]) ORELSE
   (MATCH_MP_TAC(REWRITE_RULE[CONJ_ASSOC]
     REAL_CONTINUOUS_RPOW_COMPOSE_WITHIN) THEN
    CONJ_TAC THENL [CONJ_TAC; REALLIM_NONZERO_TAC]) ORELSE
   (MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC) ORELSE
   (MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN CONJ_TAC) ORELSE
   (MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC) ORELSE
   (MATCH_MP_TAC REAL_CONTINUOUS_NEG) ORELSE
   (MATCH_MP_TAC REAL_CONTINUOUS_POW) ORELSE
   (MATCH_MP_TAC REAL_CONTINUOUS_RFACT_COMPOSE_WITHIN THEN CONJ_TAC THENL
     [ALL_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      REALLIM_INEQ_TAC]) ORELSE
   (MATCH_MP_TAC
     (REWRITE_RULE[CONJ_ASSOC] REAL_CONTINUOUS_RBINOM_COMPOSE_WITHIN) THEN
    CONJ_TAC THENL
     [CONJ_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      REALLIM_INEQ_TAC])
  ) THEN
  REWRITE_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN;
              REAL_CONTINUOUS_CONST] THEN
  NO_TAC;;

let TACTIC_1 =
  REPEAT STRIP_TAC THEN
  REPEAT
   (MATCH_MP_TAC REALLIM_POW ORELSE
    (MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC) ORELSE
    (MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC) ORELSE
    (MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC) ORELSE
    (MATCH_MP_TAC REALLIM_SPOW) ORELSE
    ((MATCH_MP_TAC REALLIM_DIV ORELSE
      MATCH_MP_TAC REALLIM_SPOW_COMPOSE) THEN
     GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
      [CONJ_TAC;
       REWRITE_TAC[REAL_OF_NUM_ADD] THEN
       REWRITE_TAC[SPOW_EQ_0; REAL_POW_EQ_0; REAL_ENTIRE; REAL_DIV_EQ_0;
                   COS_NPI; REAL_POW_EQ_0; REAL_NEG_EQ_0] THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
       REWRITE_TAC[REAL_OF_NUM_EQ; BINOM_EQ_0; FACT_NZ] THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_LT;
                   GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD;
                   GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
       TRY ASM_REAL_ARITH_TAC THEN
       NONZERO_ADHOC_TAC]) ORELSE
      (MATCH_MP_TAC REALLIM_SPOW_COMPOSE THEN
       ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
        [CONJ_TAC;
         REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
         ASM_REAL_ARITH_TAC]) ORELSE
    ((MATCH_MP_TAC LIM_RBINOM THEN CONJ_TAC) ORELSE
     (MATCH_MP_TAC LIM_RFACT) ORELSE
     (MATCH_MP_TAC REALLIM_SPOW_COMPOSE THEN REPEAT CONJ_TAC THENL
       [ALL_TAC; ALL_TAC;
        REWRITE_TAC[RE; IM] THEN NONZERO_ADHOC_TAC]) THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL])) THEN
  REWRITE_TAC[REALLIM_CONST] THEN
   MATCH_MP_TAC(MESON[REAL_CONTINUOUS_AT]
       `f x = y /\ f real_continuous at x ==> (f ---> y) (at x)`) THEN
  REWRITE_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT; RE; IM] THEN
  TRY(GEN_REWRITE_TAC RAND_CONV [GSYM WITHIN_UNIV] THEN
      REALLIM_CONTINUOUS_TAC);;

(* ------------------------------------------------------------------------- *)
(* Assemble the side conditions for ZEILBERGER.                              *)
(* ------------------------------------------------------------------------- *)

let SIDECOND_TAC =
  CONJ_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      REPEAT(MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC) THEN
      MATCH_MP_TAC REALLIM_MUL THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC(MESON[REAL_CONTINUOUS_AT]
          `f x = y /\ f real_continuous at x ==> (f ---> y) (at x)`) THEN
         (CONJ_TAC THENL [REWRITE_TAC[RE; IM] THEN REFL_TAC; ALL_TAC]) THEN
         REAL_CONTINUOUS_ADHOC_TAC;
         ALL_TAC])] THEN
    TRY TACTIC_1;

    CONJ_TAC THENL
     [CONJ_TAC THEN RATPOLYFUN_TAC;
      CONJ_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `n:num`) THEN
        REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_ENTIRE; REAL_DIV_EQ_0;
                    REAL_OF_NUM_EQ; FACT_NZ; BINOM_EQ_0] THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_LT] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        TRY(DISCH_TAC o check (is_imp o snd)) THEN
        TRY NONZERO_ADHOC_TAC;

        TRY(REPEAT STRIP_TAC THEN TACTIC_4)]]];;

(* ------------------------------------------------------------------------- *)
(* Prove a WZ recurrence from an explicit rational certificate.              *)
(* ------------------------------------------------------------------------- *)

let WZ_PROVE ntm stm rtm ctm atm =
  if ctm = [] then failwith "WZ_PROVE: empty coefficient list";
  let atms,th = WZ_INITIAL_REDUCTIONS ntm stm rtm ctm atm in
  let th' =
    prove
     (rand(concl th),
      MAP_EVERY
       (fun a ->
          ASM_CASES_TAC a THENL
           [ALL_TAC; ASM_REWRITE_TAC[] THEN NO_TAC])
       atms THEN
      MATCH_MP_TAC th THEN
      SIDECOND_TAC) in
  CONV_RULE
   (ONCE_DEPTH_CONV(BINDER_CONV(RAND_CONV OUTPUT_SIMP_CONV))) th';;
