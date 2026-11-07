(* ========================================================================= *)
(* Tijdeman: the Catalan exponents are bounded (conditional form).           *)
(*                                                                           *)
(* Purpose: Tijdeman (Acta Arith 29 (1976), sec 5): the exponents of the     *)
(* Catalan equation x^p - y^q = 1 (p, q distinct odd primes, x, y >= 2)      *)
(* are bounded, given the sharp lower bounds for linear forms in two and     *)
(* three logarithms of rationals (sharp_bound_property, Tijdeman Thm 2):     *)
(*   CATALAN_EXPONENT_BOUND_CONDITIONAL                                      *)
(*     sharp_bound_property 2 C2 K2 /\ sharp_bound_property 3 C3 K3          *)
(*     ==> ?M. ... x EXP p = y EXP q + 1 ==> p <= M /\ q <= M                *)
(* The four linear forms (y + 1 = sg^p / q^e2, x - 1 = rho^q / p^e1):        *)
(*   p log x - q log y                  (x = 2, q < p)                       *)
(*   q log(y + 1) - p log(x - 1)        (three logs: q bounded by log p,     *)
(*                                       resp. p bounded by log q)           *)
(*   q log(y + 1) - p log x             (two logs: p bounded, q < p)         *)
(*   q log y - p log(x - 1)             (two logs: q bounded, p < q)         *)
(* with upper bounds from log(1 + t) <= t, and the final step                *)
(* t <= c (log t)^k ==> t <= M (LOG_POLY_BOUND). For general exponents m, n  *)
(* every odd prime factor of m and n is bounded.                             *)
(*                                                                           *)
(* Main results: sharp_bound_property (definition: Tijdeman Thm 2 for n      *)
(*   logarithms of positive rationals), CATALAN_EXPONENT_BOUND_CONDITIONAL,  *)
(*   CATALAN_ODD_PRIME_FACTORS_CONDITIONAL, CATALAN_EQUAL_EXPONENTS;         *)
(*   SHARP_BOUND_2, SHARP_BOUND_3 (sharp_bound_property for two and three    *)
(*   explicit rationals), SHARP_BOUND_PROPERTY_MONO.                         *)
(*                                                                           *)
(* Uses: Baker/catalan_nt.ml (CATALAN_FACTOR_MINUS, CATALAN_FACTOR_PLUS),    *)
(*   Baker/lemmas.ml (LOG_POLY_BOUND, LOG_NUM_GE_1, LOG_NUM_GE_HALF,         *)
(*   EXP_1_LE_3, EXP_ADD_ONE_LT, EXP_NEG_LE_RATIO, REAL_FRAC_LE_CROSS,       *)
(*   ODD_PRIME_GE_3, INV_POW_EXP_NEG).                                       *)
(* ========================================================================= *)

needs "Baker/lemmas.ml";;
needs "Baker/catalan_nt.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Tijdeman Theorem 2 for n logarithms of positive rationals: the bound      *)
(* property (Baker, Sharpening I, with the explicit dependence on the        *)
(* heights exp(g0) and A), proved by SHARP_BAKER_RATIONAL of                 *)
(* Baker/tijdeman.ml.                                                        *)
(* ------------------------------------------------------------------------- *)

let sharp_bound_property = new_definition
 `sharp_bound_property n C K <=>
    !(u:num->num) (v:num->num) (bb:num->real) A B g0.
      &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
      (!r. r IN 1..n
           ==> 1 <= u r /\ 1 <= v r /\ integer(bb r) /\ abs(bb r) <= B) /\
      (!r. r IN 1..n-1 ==> &(u r) <= exp g0 /\ &(v r) <= exp g0) /\
      &(u n) <= A /\ &(v n) <= A /\
      ~(sum(1..n) (\r. bb r * log(&(u r) / &(v r))) = &0)
      ==> exp(--(C * g0 pow K * log A * log B)) <=
          abs(sum(1..n) (\r. bb r * log(&(u r) / &(v r))))`;;

let SHARP_BOUND_2 = prove
 (`!C K. sharp_bound_property 2 C K
         ==> !u1 v1 u2 v2 b1 b2 A B g0.
               &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
               1 <= u1 /\ 1 <= v1 /\ 1 <= u2 /\ 1 <= v2 /\
               &u1 <= exp g0 /\ &v1 <= exp g0 /\ &u2 <= A /\ &v2 <= A /\
               integer b1 /\ integer b2 /\ abs b1 <= B /\ abs b2 <= B /\
               ~(b1 * log(&u1 / &v1) + b2 * log(&u2 / &v2) = &0)
               ==> exp(--(C * g0 pow K * log A * log B)) <=
                   abs(b1 * log(&u1 / &v1) + b2 * log(&u2 / &v2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sharp_bound_property] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\r. if r = 1 then u1 else u2:num`; `\r. if r = 1 then v1 else v2:num`;
    `\r. if r = 1 then b1 else b2:real`; `A:real`; `B:real`; `g0:real`]) THEN
  REWRITE_TAC[SUM_2; ARITH] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN GEN_TAC THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_NUMSEG; ARITH] THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `r = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let SHARP_BOUND_3 = prove
 (`!C K. sharp_bound_property 3 C K
         ==> !u1 v1 u2 v2 u3 v3 b1 b2 b3 A B g0.
               &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
               1 <= u1 /\ 1 <= v1 /\ 1 <= u2 /\ 1 <= v2 /\
               1 <= u3 /\ 1 <= v3 /\
               &u1 <= exp g0 /\ &v1 <= exp g0 /\
               &u2 <= exp g0 /\ &v2 <= exp g0 /\ &u3 <= A /\ &v3 <= A /\
               integer b1 /\ integer b2 /\ integer b3 /\
               abs b1 <= B /\ abs b2 <= B /\ abs b3 <= B /\
               ~(b1 * log(&u1 / &v1) + b2 * log(&u2 / &v2) +
                 b3 * log(&u3 / &v3) = &0)
               ==> exp(--(C * g0 pow K * log A * log B)) <=
                   abs(b1 * log(&u1 / &v1) + b2 * log(&u2 / &v2) +
                       b3 * log(&u3 / &v3))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sharp_bound_property] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\r. if r = 1 then u1 else if r = 2 then u2 else u3:num`;
    `\r. if r = 1 then v1 else if r = 2 then v2 else v3:num`;
    `\r. if r = 1 then b1 else if r = 2 then b2 else b3:real`;
    `A:real`; `B:real`; `g0:real`]) THEN
  REWRITE_TAC[SUM_3; ARITH] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `r = 1 \/ r = 2 \/ r = 3` MP_TAC THENL
     [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[ARITH]];
    REWRITE_TAC[IN_NUMSEG; ARITH] THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `r = 1 \/ r = 2` MP_TAC THENL
     [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[ARITH]]]);;

let SHARP_BOUND_PROPERTY_MONO = prove
 (`!n C K C' K'. sharp_bound_property n C K /\ C <= C' /\ &0 <= C' /\ K <= K'
                 ==> sharp_bound_property n C' K'`,
  REWRITE_TAC[sharp_bound_property] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `exp(--(C * g0 pow K * log A * log B))` THEN
  CONJ_TAC THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  SUBGOAL_THEN `&0 <= log A /\ &0 <= log B /\ g0 pow K <= g0 pow K' /\
                &0 <= g0 pow K`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `C' * g0 pow K * log A * log B` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]]);;

let LOG_POW_RATIO_LE = prove
 (`!a n. &0 < a
         ==> log((a + &1) pow n) <= log(a pow n) + &n / a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + &1) pow n = a pow n * (&1 + inv a) pow n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv a /\ &0 < &1 + inv a` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_ADD THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_01];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW; REAL_LE_LADD] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC LOG_LE THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let CATALAN_LOG_FORMS = prove
 (`!p q x y. 2 <= p /\ 2 <= q /\ 2 <= x /\ 1 <= y /\ x EXP p = y EXP q + 1
   ==> (&0 < &p * log(&x) - &q * log(&y) /\
        &p * log(&x) - &q * log(&y) <= inv(&y pow q)) /\
       (&0 < &q * log(&y + &1) - &p * log(&x) /\
        &q * log(&y + &1) - &p * log(&x) <= &q / &y) /\
       (&0 < &q * log(&y) - &p * log(&x - &1) /\
        &q * log(&y) - &p * log(&x - &1) <= &p / (&x - &1)) /\
       (&0 < &q * log(&y + &1) - &p * log(&x - &1) /\
        &q * log(&y + &1) - &p * log(&x - &1) <= &q / &y + &p / (&x - &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &x - &1 /\ &0 < &y /\ &0 < &x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 < x - &1 <=> &1 < x`; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&x pow p = &y pow q + &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `&y pow q + &1 < (&y + &1) pow q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC EXP_ADD_ONE_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&x - &1) pow p + &1 < &x pow p` ASSUME_TAC THENL
   [SUBGOAL_THEN `&x - &1 = &(x - 1)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `2 <= x ==> 1 <= x`];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
    MP_TAC(SPECL [`x - 1`; `p:num`] EXP_ADD_ONE_LT) THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `2 <= x ==> 1 <= x`;
                 ARITH_RULE `2 <= x ==> 1 <= x - 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &y pow q /\ &0 < (&x - &1) pow p /\ &0 < &x pow p /\
                &0 < (&y + &1) pow q`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < y ==> &0 < y + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&p * log(&x) = log(&x pow p) /\ &q * log(&y) = log(&y pow q) /\
                &q * log(&y + &1) = log((&y + &1) pow q) /\
                &p * log(&x - &1) = log((&x - &1) pow p)`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[LOG_POW; REAL_ARITH `&0 < y ==> &0 < y + &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&y pow q) < log(&x pow p) /\
                log(&x pow p) < log((&y + &1) pow q) /\
                log((&x - &1) pow p) < log(&y pow q)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&x pow p) <= log(&y pow q) + inv(&y pow q)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&x pow p = &y pow q * (&1 + inv(&y pow q))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < &y pow q` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&y pow q)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < a ==> &0 < &1 + a`;
                 REAL_LE_LADD] THEN
    MATCH_MP_TAC LOG_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(SPEC `q:num` (MATCH_MP LOG_POW_RATIO_LE (ASSUME `&0 < &y`))) THEN
  MP_TAC(SPEC `p:num` (MATCH_MP LOG_POW_RATIO_LE (ASSUME `&0 < &x - &1`))) THEN
  REWRITE_TAC[REAL_ARITH `x - &1 + &1 = x`] THEN ASM_REAL_ARITH_TAC);;

let LOG_FACTOR_EQ = prove
 (`!a b c m e. 1 <= a /\ 1 <= b /\ 1 <= c /\ a EXP e * b = c EXP m
               ==> log(&b) = &m * log(&c) - &e * log(&a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &a /\ &0 < &b /\ &0 < &c` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&a pow e * &b) = log(&c pow m)` MP_TAC THENL
   [AP_TERM_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; LOG_POW] THEN REAL_ARITH_TAC);;

let EXP_LE_ONE_FACTOR = prove
 (`!a e. 1 <= a /\ e <= 1 ==> 1 <= a EXP e /\ a EXP e <= a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `e = 0 \/ e = 1` MP_TAC THENL
   [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[EXP; EXP_1; LE_REFL]]);;

let ADD_LE_MULT = prove
 (`!p q. 2 <= p /\ 2 <= q ==> p + q <= p * q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `p:num`; `q:num`] LE_MULT_RCANCEL) THEN
  MP_TAC(SPECL [`2`; `q:num`; `p:num`] LE_MULT_RCANCEL) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MULT_SYM] THEN ARITH_TAC);;

let CATALAN_SIZES = prove
 (`!p q x y rho sg e1 e2.
     2 <= p /\ 2 <= q /\ 2 <= x /\ 1 <= y /\ x EXP p = y EXP q + 1 /\
     e1 <= 1 /\ p EXP e1 * (x - 1) = rho EXP q /\
     e2 <= 1 /\ q EXP e2 * (y + 1) = sg EXP p
     ==> 1 <= rho /\ 2 <= sg /\
         x - 1 <= rho EXP q /\ rho EXP q <= p * (x - 1) /\
         y + 1 <= sg EXP p /\ sg EXP p <= q * (y + 1) /\
         x <= sg EXP q /\ rho <= p * sg /\ sg <= 2 * q * rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `e1:num`] EXP_LE_ONE_FACTOR) THEN
  MP_TAC(SPECL [`q:num`; `e2:num`] EXP_LE_ONE_FACTOR) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= p ==> 1 <= p`] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `x - 1 <= rho EXP q /\ rho EXP q <= p * (x - 1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `rho EXP q`)) THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x - 1 = 1 * (x - 1)`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `y + 1 <= sg EXP p /\ sg EXP p <= q * (y + 1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `sg EXP p`)) THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `y + 1 = 1 * (y + 1)`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= rho` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= r <=> ~(r = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `x - 1 <= rho EXP q` THEN
    ASM_REWRITE_TAC[EXP_ZERO] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `2 <= sg` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 <= s <=> ~(s = 0) /\ ~(s = 1)`] THEN
    CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `y + 1 <= sg EXP p` THEN
    ASM_REWRITE_TAC[EXP_ZERO; EXP_ONE] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `x <= sg EXP q` ASSUME_TAC THENL
   [SUBGOAL_THEN `x EXP p <= (sg EXP q) EXP p` MP_TAC THENL
     [ASM_REWRITE_TAC[EXP_EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      REWRITE_TAC[GSYM EXP_EXP] THEN
      TRANS_TAC LE_TRANS `(y + 1) EXP q` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC EXP_ADD_ONE_LT THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `rho EXP q <= (p * sg) EXP q` MP_TAC THENL
     [TRANS_TAC LE_TRANS `p * sg EXP q` THEN CONJ_TAC THENL
       [TRANS_TAC LE_TRANS `p * (x - 1)` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        REWRITE_TAC[MULT_EXP; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg EXP (p * q) < (2 * q * rho) EXP (p * q)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXP_MONO_LT] THEN ARITH_TAC] THEN
  TRANS_TAC LTE_TRANS `(2 * q) EXP q * x EXP p` THEN CONJ_TAC THENL
   [TRANS_TAC LET_TRANS `(2 * q) EXP q * y EXP q` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MULT_EXP; GSYM EXP_EXP] THEN
      MATCH_MP_TAC EXP_MONO_LE_IMP THEN
      TRANS_TAC LE_TRANS `q * (y + 1)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `(2 * q) * y = q * 2 * y`; LE_MULT_LCANCEL] THEN
      ASM_ARITH_TAC;
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS `(2 * q) EXP q * (2 * rho EXP q) EXP p` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * rho EXP q) EXP p = 2 EXP p * rho EXP (p * q) /\
                (2 * q * rho) EXP (p * q) =
                (2 * q) EXP (p * q) * rho EXP (p * q)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN REWRITE_TAC[MULT_EXP; EXP_EXP] THEN REWRITE_TAC[MULT_AC];
    ALL_TAC] THEN
  REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
  TRANS_TAC LE_TRANS `(2 * q) EXP q * (2 * q) EXP p` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM EXP_ADD; LE_EXP] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; DISJ2_TAC] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC ADD_LE_MULT THEN
    ASM_REWRITE_TAC[]]);;

let EXP_GT_PLUS_ONE = prove
 (`!a b m n. 2 <= b /\ 1 <= m /\ m < n /\ b <= a ==> b EXP m + 1 < a EXP n`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `b EXP (m + 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EXP_ADD; EXP_1] THEN
    SUBGOAL_THEN `2 <= b EXP m` MP_TAC THENL
     [TRANS_TAC LE_TRANS `b EXP 1` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[EXP_1];
        REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `b EXP m * 2 <= b EXP m * b` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ARITH_TAC];
    TRANS_TAC LE_TRANS `a EXP (m + 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC]]);;

let CATALAN_ORDER = prove
 (`!p q x y. 1 <= p /\ 1 <= q /\ 2 <= x /\ 2 <= y /\ x EXP p = y EXP q + 1
             ==> (q < p ==> x < y) /\ (p < q ==> y < x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`x:num`; `y:num`; `q:num`; `p:num`] EXP_GT_PLUS_ONE) THEN
    ASM_REWRITE_TAC[LT_REFL];
    MP_TAC(SPECL [`y:num`; `x:num`; `p:num`; `q:num`] EXP_GT_PLUS_ONE) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let CATALAN_BOUND_X2 = prove
 (`!C K p q y. sharp_bound_property 2 C K /\ &0 <= C /\
               3 <= p /\ 2 <= q /\ q < p /\ 2 <= y /\ 2 EXP p = y EXP q + 1
               ==> &q <= &2 * C * log(&p) pow (K + 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `2`; `y:num`] CATALAN_LOG_FORMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 < &p /\ &0 < &y /\ &1 <= log(&p) /\ &0 < log(&y)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_NUM_GE_1; REAL_OF_NUM_LT;
                 ARITH_RULE `3 <= p ==> 0 < p`;
                 ARITH_RULE `2 <= y ==> 0 < y`] THEN
    MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&y <= &y pow 2 /\ &1 <= &y pow 2 /\ exp(&1) <= &y pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `4 <= y EXP 2` ASSUME_TAC THENL
     [REWRITE_TAC[EXP_2] THEN
      MP_TAC(SPECL [`2`; `y:num`; `2`; `y:num`] LE_MULT2) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXP_2; LE_SQUARE_REFL];
      ASM_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `&3` THEN REWRITE_TAC[EXP_1_LE_3] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SHARP_BOUND_2 o
    check (fun th -> rator(concl th) = `sharp_bound_property 2 C`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`2`; `1`; `y:num`; `1`; `&p`; `--(&q)`;
                             `&y pow 2`; `&p`; `log(&p)`]) THEN
  ASM_SIMP_TAC[REAL_DIV_1; EXP_LOG] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG; REAL_ABS_NEG; REAL_ABS_NUM;
                REAL_OF_NUM_LE] THEN
    REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(&p * log(&2) + --(&q) * log(&y)) =
                &p * log(&2) - &q * log(&y)` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(--(C * log(&p) pow K * (&2 * log(&y)) * log(&p))) <=
                exp(--(&q * log(&y)))` MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&p * log(&2) - &q * log(&y)` THEN
    ASM_SIMP_TAC[GSYM INV_POW_EXP_NEG];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  SUBGOAL_THEN `C * log(&p) pow K * (&2 * log(&y)) * log(&p) =
                (&2 * C * log(&p) pow (K + 1)) * log(&y)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ]);;

let LINEAR_DIVIDE_LEMMA = prove
 (`!m l N0 Z a b.
     &1 / &2 <= l /\ &0 <= N0 /\ &0 <= Z /\ &0 <= a /\
     m * l <= N0 + Z * (a + b * l)
     ==> m <= &2 * N0 + Z * (&2 * a + b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m * l <= (&2 * N0 + Z * (&2 * a + b)) * l` MP_TAC THENL
   [SUBGOAL_THEN `&0 <= (&2 * l - &1) * (N0 + Z * a)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL]];
      UNDISCH_TAC `m * l <= N0 + Z * (a + b * l:real)` THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ]]);;

let LOG_LE_POW_LOG = prove
 (`!a P k. &0 < a /\ 1 <= P /\ a <= &P pow k ==> log a <= &k * log(&P)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &P` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_POW] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_REWRITE_TAC[]);;

let LOG_SMALL_BOUNDS = prove
 (`!P. 2 <= P
       ==> log(&4 * &P pow 2) <= &4 * log(&P) /\
           log(&2 * &P pow 2) <= &4 * log(&P) /\
           log(&4 * &P) <= &3 * log(&P)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `4 <= P EXP 2` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_2] THEN
    MP_TAC(SPECL [`2`; `P:num`; `2`; `P:num`] LE_MULT2) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * P EXP 2 <= P EXP 4 /\ 4 * P <= P EXP 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `P EXP 4 = P EXP 2 * P EXP 2 /\ P EXP 3 = P EXP 2 * P EXP 1`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &P` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_LE_POW_LOG THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &4 /\ &0 < &2`;
               ARITH_RULE `2 <= P ==> 1 <= P`] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  ASM_ARITH_TAC);;

let CATALAN_ALG3 = prove
 (`!C K P t m L.
     &0 <= C /\ 3 <= P /\ 2 <= t /\
     exp(--(C * log(&P) pow K * log(&4 * &P * &t) * log(&P pow 2))) <= L /\
     L <= (&4 * &P pow 2) / &t pow m
     ==> &m <= (&8 + &14 * C) * log(&P) pow (K + 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &P /\ &0 < &t /\ &1 <= log(&P) /\ &1 / &2 <= log(&t)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_NUM_GE_1; LOG_NUM_GE_HALF; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `P:num` LOG_SMALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`C * log(&P) pow K * log(&4 * &P * &t) * log(&P pow 2)`;
                 `&4 * &P pow 2`; `&t pow m`] EXP_NEG_LE_RATIO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &4`] THEN
    TRANS_TAC REAL_LE_TRANS `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&4 * &P * &t) = log(&4 * &P) + log(&t)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC LOG_MUL THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < &4`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&m`; `log(&t)`; `log(&4 * &P pow 2)`;
                `&2 * C * log(&P) pow (K + 1)`; `log(&4 * &P)`; `&1`]
               LINEAR_DIVIDE_LEMMA) THEN
  SUBGOAL_THEN `&0 <= log(&P) pow (K + 1) /\ log(&P) <= log(&P) pow (K + 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&4 * &P pow 2) /\ &0 <= log(&4 * &P)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    REWRITE_TAC[ARITH_RULE `1 <= 4 * n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        free_in `&m * log(&t)` (concl th))) THEN
      MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= a + y ==> x <= a + (z:real)`) THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> m <= a ==> m <= (b:real)`) THEN
  SUBGOAL_THEN `(&2 * C * log(&P) pow (K + 1)) * (&2 * log(&4 * &P) + &1) <=
                (&2 * C * log(&P) pow (K + 1)) * (&7 * log(&P))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * C * log(&P) pow (K + 1)) * (&7 * log(&P)) =
                &14 * C * log(&P) pow (K + 2)` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `K + 2 = (K + 1) + 1`; REAL_POW_ADD; REAL_POW_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CATALAN_ALG2 = prove
 (`!C K P t n m L.
     &0 <= C /\ 3 <= P /\ 2 <= t /\
     exp(--(C * log(&P) pow K * log(&2 * &t pow n) * log(&P))) <= L /\
     L <= (&2 * &P pow 2) / &t pow m
     ==> &m <= &8 * log(&P) + (C * log(&P) pow (K + 1)) * (&n + &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &P /\ &0 < &t /\ &1 <= log(&P) /\ &1 / &2 <= log(&t)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_NUM_GE_1; LOG_NUM_GE_HALF; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `P:num` LOG_SMALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`C * log(&P) pow K * log(&2 * &t pow n) * log(&P)`;
                 `&2 * &P pow 2`; `&t pow m`] EXP_NEG_LE_RATIO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
    TRANS_TAC REAL_LE_TRANS `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= log(&2 * &P pow 2) /\ &0 <= log(&P) pow (K + 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      REWRITE_TAC[ARITH_RULE `1 <= 2 * n <=> ~(n = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&m`; `log(&t)`; `log(&2 * &P pow 2)`;
                `C * log(&P) pow (K + 1)`; `log(&2)`; `&n`]
               LINEAR_DIVIDE_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL] THEN CONJ_TAC THENL
     [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      free_in `&m * log(&t)` (concl th))) THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= a + y ==> x <= a + (z:real)`) THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> m <= a ==> m <= (b:real)`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&2 * u <= &8 * l /\ z * v <= z * w
    ==> &2 * u + z * v <= &8 * l + z * w`) THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN
  MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC);;

let CATALAN_LOG_FACTORS = prove
 (`!p q x y rho sg e1 e2.
     2 <= p /\ 2 <= q /\ 2 <= x /\ 1 <= y /\ 1 <= rho /\ 1 <= sg /\
     p EXP e1 * (x - 1) = rho EXP q /\ q EXP e2 * (y + 1) = sg EXP p
     ==> log(&x - &1) = &q * log(&rho) - &e1 * log(&p) /\
         log(&y + &1) = &p * log(&sg) - &e2 * log(&q)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `2 <= x ==> 1 <= x`;
               REAL_OF_NUM_ADD] THEN
  MATCH_MP_TAC LOG_FACTOR_EQ THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CATALAN_LOWER3 = prove
 (`!C K p q x y rho sg e1 e2 P A.
     sharp_bound_property 3 C K /\
     2 <= p /\ 2 <= q /\ 2 <= x /\ 1 <= y /\ x EXP p = y EXP q + 1 /\
     e1 <= 1 /\ p EXP e1 * (x - 1) = rho EXP q /\
     e2 <= 1 /\ q EXP e2 * (y + 1) = sg EXP p /\
     3 <= P /\ p <= P /\ q <= P /\ exp(&1) <= A /\ &rho <= A /\ &sg <= A
     ==> exp(--(C * log(&P) pow K * log A * log(&P pow 2))) <=
         &q * log(&y + &1) - &p * log(&x - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                `e1:num`; `e2:num`] CATALAN_SIZES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_LOG_FORMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &P /\ &0 < &p /\ &0 < &q /\ &0 < &rho /\ &0 < &sg`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e1 * p <= P EXP 2 /\ e2 * q <= P EXP 2 /\ p * q <= P EXP 2 /\
                2 <= P EXP 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXP_2] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      MP_TAC(SPECL [`1`; `P:num`; `2`; `P:num`] LE_MULT2) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SHARP_BOUND_3 o
    check (fun th -> rator(concl th) = `sharp_bound_property 3 C`)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`p:num`; `1`; `q:num`; `1`; `sg:num`; `rho:num`;
    `&e1 * &p`; `--(&e2 * &q)`; `&p * &q`; `A:real`; `&P pow 2`;
    `log(&P)`]) THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_DIV_1; LOG_DIV] THEN
  SUBGOAL_THEN
   `(&e1 * &p) * log(&p) + --(&e2 * &q) * log(&q) +
    (&p * &q) * (log(&sg) - log(&rho)) =
    &q * log(&y + &1) - &p * log(&x - &1)`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                  `e1:num`; `e2:num`] CATALAN_LOG_FACTORS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LOG_NUM_GE_1; INTEGER_CLOSED; INTEGER_NEG] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_NUM; REAL_OF_NUM_MUL;
              REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REAL_ARITH_TAC));;

let CATALAN_LOWER2A = prove
 (`!C K p q x y rho sg e1 e2 P A.
     sharp_bound_property 2 C K /\
     2 <= p /\ 2 <= q /\ 2 <= x /\ 1 <= y /\ x EXP p = y EXP q + 1 /\
     e1 <= 1 /\ p EXP e1 * (x - 1) = rho EXP q /\
     e2 <= 1 /\ q EXP e2 * (y + 1) = sg EXP p /\
     3 <= P /\ p <= P /\ q <= P /\ exp(&1) <= A /\
     &(sg EXP q) <= A /\ &x <= A
     ==> exp(--(C * log(&P) pow K * log A * log(&P))) <=
         &q * log(&y + &1) - &p * log(&x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                `e1:num`; `e2:num`] CATALAN_SIZES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_LOG_FORMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= sg EXP q` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &P /\ &0 < &p /\ &0 < &q /\ &0 < &x /\ &0 < &sg /\
                &0 < &(sg EXP q)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e2 * q <= P` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `1 * q` THEN
    CONJ_TAC THENL [REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SHARP_BOUND_2 o
    check (fun th -> rator(concl th) = `sharp_bound_property 2 C`)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`q:num`; `1`; `sg EXP q`; `x:num`;
    `--(&e2 * &q)`; `&p`; `A:real`; `&P`; `log(&P)`]) THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_DIV_1; LOG_DIV] THEN
  SUBGOAL_THEN
   `--(&e2 * &q) * log(&q) + &p * (log(&(sg EXP q)) - log(&x)) =
    &q * log(&y + &1) - &p * log(&x)`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                  `e1:num`; `e2:num`] CATALAN_LOG_FACTORS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_POW; LOG_POW] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LOG_NUM_GE_1; INTEGER_CLOSED; INTEGER_NEG] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_NUM; REAL_OF_NUM_MUL;
              REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REAL_ARITH_TAC));;

let CATALAN_LOWER2B = prove
 (`!C K p q x y rho sg e1 e2 P A.
     sharp_bound_property 2 C K /\
     2 <= p /\ 2 <= q /\ 2 <= x /\ 1 <= y /\ x EXP p = y EXP q + 1 /\
     e1 <= 1 /\ p EXP e1 * (x - 1) = rho EXP q /\
     e2 <= 1 /\ q EXP e2 * (y + 1) = sg EXP p /\
     3 <= P /\ p <= P /\ q <= P /\ exp(&1) <= A /\
     &y <= A /\ &(rho EXP p) <= A
     ==> exp(--(C * log(&P) pow K * log A * log(&P))) <=
         &q * log(&y) - &p * log(&x - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                `e1:num`; `e2:num`] CATALAN_SIZES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_LOG_FORMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= rho EXP p` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &P /\ &0 < &p /\ &0 < &q /\ &0 < &y /\ &0 < &rho /\
                &0 < &(rho EXP p)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e1 * p <= P` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `1 * p` THEN
    CONJ_TAC THENL [REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SHARP_BOUND_2 o
    check (fun th -> rator(concl th) = `sharp_bound_property 2 C`)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`p:num`; `1`; `y:num`; `rho EXP p`;
    `&e1 * &p`; `&q`; `A:real`; `&P`; `log(&P)`]) THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_DIV_1; LOG_DIV] THEN
  SUBGOAL_THEN
   `(&e1 * &p) * log(&p) + &q * (log(&y) - log(&(rho EXP p))) =
    &q * log(&y) - &p * log(&x - &1)`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                  `e1:num`; `e2:num`] CATALAN_LOG_FACTORS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_POW; LOG_POW] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LOG_NUM_GE_1; INTEGER_CLOSED; INTEGER_NEG] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_NUM; REAL_OF_NUM_MUL;
              REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REAL_ARITH_TAC));;

let REAL_FRAC_SPLIT_4 = prove
 (`!a b. (&4 * a) / b = (&2 * a) / b + (&2 * a) / b`,
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let CATALAN_STEP1_PGQ = prove
 (`!C K p q x y rho sg e1 e2.
     sharp_bound_property 3 C K /\ &0 <= C /\
     3 <= q /\ q < p /\ 3 <= x /\ 2 <= y /\ x EXP p = y EXP q + 1 /\
     e1 <= 1 /\ p EXP e1 * (x - 1) = rho EXP q /\
     e2 <= 1 /\ q EXP e2 * (y + 1) = sg EXP p
     ==> &q <= (&8 + &14 * C) * log(&p) pow (K + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                `e1:num`; `e2:num`] CATALAN_SIZES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 <= rho` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 <= r <=> ~(r = 0) /\ ~(r = 1)`] THEN
    CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `x - 1 <= rho EXP q` THEN
    ASM_REWRITE_TAC[EXP_ZERO; EXP_ONE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `K:num`; `p:num`; `q:num`; `x:num`; `y:num`;
                `rho:num`; `sg:num`; `e1:num`; `e2:num`; `p:num`;
                `&4 * &p * &rho`] CATALAN_LOWER3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC;
      ASM_ARITH_TAC; ASM_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `&3` THEN
      REWRITE_TAC[EXP_1_LE_3; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 3 <= 4 * n`) THEN
      REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; MULT_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = 1 * r`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      TRANS_TAC LE_TRANS `2 * q * rho` THEN ASM_REWRITE_TAC[MULT_ASSOC] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_LOG_FORMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC CATALAN_ALG3 THEN
  MAP_EVERY EXISTS_TAC
   [`rho:num`; `&q * log(&y + &1) - &p * log(&x - &1)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&q / &y + &p / (&x - &1)` THEN
  ASM_REWRITE_TAC[REAL_FRAC_SPLIT_4] THEN
  SUBGOAL_THEN `&0 < &y /\ &0 < &rho pow q /\ &x - &1 = &(x - 1) /\
                &0 < &(x - 1)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `3 <= x ==> 1 <= x`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; EXP_EQ_0;
                ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_FRAC_LE_CROSS THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THENL
   [TRANS_TAC LE_TRANS `q * p * (x - 1)` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
    TRANS_TAC LE_TRANS `p * p * y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_2; MULT_ASSOC; LE_MULT_RCANCEL] THEN ARITH_TAC];
    TRANS_TAC LE_TRANS `p * p * (x - 1)` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
    REWRITE_TAC[EXP_2; MULT_ASSOC; LE_MULT_RCANCEL] THEN ARITH_TAC]);;

let CATALAN_STEP1_QGP = prove
 (`!C K p q x y rho sg e1 e2.
     sharp_bound_property 3 C K /\ &0 <= C /\
     3 <= p /\ p < q /\ 2 <= x /\ 2 <= y /\ x EXP p = y EXP q + 1 /\
     e1 <= 1 /\ p EXP e1 * (x - 1) = rho EXP q /\
     e2 <= 1 /\ q EXP e2 * (y + 1) = sg EXP p
     ==> &p <= (&8 + &14 * C) * log(&q) pow (K + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                `e1:num`; `e2:num`] CATALAN_SIZES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`C:real`; `K:num`; `p:num`; `q:num`; `x:num`; `y:num`;
                `rho:num`; `sg:num`; `e1:num`; `e2:num`; `q:num`;
                `&4 * &q * &sg`] CATALAN_LOWER3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&3` THEN
      REWRITE_TAC[EXP_1_LE_3; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 3 <= 4 * n`) THEN
      REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      TRANS_TAC LE_TRANS `p * sg` THEN ASM_REWRITE_TAC[MULT_ASSOC] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; MULT_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = 1 * r`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_LOG_FORMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC CATALAN_ALG3 THEN
  MAP_EVERY EXISTS_TAC
   [`sg:num`; `&q * log(&y + &1) - &p * log(&x - &1)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&q / &y + &p / (&x - &1)` THEN
  ASM_REWRITE_TAC[REAL_FRAC_SPLIT_4] THEN
  SUBGOAL_THEN `&0 < &y /\ &0 < &sg pow p /\ &x - &1 = &(x - 1) /\
                &0 < &(x - 1)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `2 <= x ==> 1 <= x`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; EXP_EQ_0;
                ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_FRAC_LE_CROSS THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THENL
   [TRANS_TAC LE_TRANS `q * q * (y + 1)` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
    TRANS_TAC LE_TRANS `(q * q) * (2 * y)` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_2; MULT_AC; LE_REFL]];
    TRANS_TAC LE_TRANS `q * q * (y + 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    TRANS_TAC LE_TRANS `(q * q) * (2 * (x - 1))` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_2; MULT_AC; LE_REFL]]]);;

let CATALAN_STEP2_PGQ = prove
 (`!C K p q x y rho sg e1 e2.
     sharp_bound_property 2 C K /\ &0 <= C /\
     3 <= q /\ q < p /\ 2 <= x /\ 2 <= y /\ x EXP p = y EXP q + 1 /\
     e1 <= 1 /\ p EXP e1 * (x - 1) = rho EXP q /\
     e2 <= 1 /\ q EXP e2 * (y + 1) = sg EXP p
     ==> &p <= &8 * log(&p) + (C * log(&p) pow (K + 1)) * (&q + &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                `e1:num`; `e2:num`] CATALAN_SIZES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `2 <= sg EXP q` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `sg EXP 1` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[EXP_1]; ALL_TAC] THEN
    REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `K:num`; `p:num`; `q:num`; `x:num`; `y:num`;
                `rho:num`; `sg:num`; `e1:num`; `e2:num`; `p:num`;
                `&2 * &sg pow q`] CATALAN_LOWER2A) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `&3` THEN
    REWRITE_TAC[EXP_1_LE_3; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_LOG_FORMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC CATALAN_ALG2 THEN
  MAP_EVERY EXISTS_TAC
   [`sg:num`; `&q * log(&y + &1) - &p * log(&x)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&q / &y` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_FRAC_LE_CROSS THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE;
              REAL_OF_NUM_LT; EXP_EQ_0; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC LE_TRANS `q * q * (y + 1)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
  TRANS_TAC LE_TRANS `(q * q) * (2 * y)` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS `(p * p) * (2 * y)` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE];
    REWRITE_TAC[EXP_2; MULT_AC; LE_REFL]]);;

let CATALAN_STEP2_QGP = prove
 (`!C K p q x y rho sg e1 e2.
     sharp_bound_property 2 C K /\ &0 <= C /\
     3 <= p /\ p < q /\ 2 <= x /\ 2 <= y /\ x EXP p = y EXP q + 1 /\
     e1 <= 1 /\ p EXP e1 * (x - 1) = rho EXP q /\
     e2 <= 1 /\ q EXP e2 * (y + 1) = sg EXP p
     ==> &q <= &8 * log(&q) + (C * log(&q) pow (K + 1)) * (&p + &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`; `rho:num`; `sg:num`;
                `e1:num`; `e2:num`] CATALAN_SIZES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 <= rho` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 <= r <=> ~(r = 0) /\ ~(r = 1)`] THEN
    CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `x - 1 <= rho EXP q` THEN
    ASM_REWRITE_TAC[EXP_ZERO; EXP_ONE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= rho EXP p` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `rho EXP 1` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[EXP_1]; ALL_TAC] THEN
    REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y < 2 * rho EXP p` ASSUME_TAC THENL
   [SUBGOAL_THEN `y EXP q < (2 * rho EXP p) EXP q` MP_TAC THENL
     [TRANS_TAC LTE_TRANS `x EXP p` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS `(2 * rho EXP q) EXP p` THEN CONJ_TAC THENL
       [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MULT_EXP; EXP_EXP] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [MULT_SYM] THEN
      REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_MONO_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `K:num`; `p:num`; `q:num`; `x:num`; `y:num`;
                `rho:num`; `sg:num`; `e1:num`; `e2:num`; `q:num`;
                `&2 * &rho pow p`] CATALAN_LOWER2B) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `&3` THEN
    REWRITE_TAC[EXP_1_LE_3; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_LOG_FORMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC CATALAN_ALG2 THEN
  MAP_EVERY EXISTS_TAC
   [`rho:num`; `&q * log(&y) - &p * log(&x - &1)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&p / (&x - &1)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&x - &1 = &(x - 1)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `2 <= x ==> 1 <= x`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_FRAC_LE_CROSS THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE;
              REAL_OF_NUM_LT; EXP_EQ_0; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC LE_TRANS `p * p * (x - 1)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
  TRANS_TAC LE_TRANS `(q * q) * (x - 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE];
    REWRITE_TAC[EXP_2; MULT_ASSOC; LE_MULT_RCANCEL] THEN ARITH_TAC]);;

let POLYLOG_COMBINE = prove
 (`!C K c1 l m a.
     &0 <= C /\ &0 <= c1 /\ &1 <= l /\ &0 <= a /\
     m <= &8 * l + (C * l pow (K + 1)) * (a + &2) /\
     a <= c1 * l pow (K + 2)
     ==> m <= (&8 + &2 * C + C * c1) * l pow (2 * K + 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l <= l pow (2 * K + 3) /\
                l pow (K + 1) <= l pow (2 * K + 3) /\
                &0 <= l pow (K + 1) /\
                l pow (K + 1) * l pow (K + 2) = l pow (2 * K + 3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C * l pow (K + 1)) * (a + &2) <=
                (C * c1) * l pow (2 * K + 3) + &2 * (C * l pow (K + 1))`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `(C * l pow (K + 1)) * (c1 * l pow (K + 2) + &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `l pow (2 * K + 3)`)) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * l pow (K + 1) <= C * l pow (2 * K + 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let FACTOR_DISJ_EXP = prove
 (`!a b c. b = c \/ a * b = c ==> ?e. e <= 1 /\ a EXP e * b = c`,
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES; LE_0];
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[EXP_1; LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Tijdeman: the exponents of x^p - y^q = 1 (p, q distinct odd primes) are   *)
(* bounded, given the sharp lower bounds for two and three logarithms.       *)
(* ------------------------------------------------------------------------- *)

let CATALAN_EXPONENT_BOUND_CONDITIONAL = prove
 (`!C2 K2 C3 K3.
     sharp_bound_property 2 C2 K2 /\ sharp_bound_property 3 C3 K3
     ==> ?M. !p q x y. prime p /\ prime q /\ ODD p /\ ODD q /\ ~(p = q) /\
                       2 <= x /\ 2 <= y /\ x EXP p = y EXP q + 1
                       ==> p <= M /\ q <= M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?C K. &0 <= C /\ sharp_bound_property 2 C K /\
                      sharp_bound_property 3 C K`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`abs C2 + abs C3`; `K2 + K3`] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC SHARP_BOUND_PROPERTY_MONO THEN
      MAP_EVERY EXISTS_TAC [`C2:real`; `K2:num`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
      ARITH_TAC;
      MATCH_MP_TAC SHARP_BOUND_PROPERTY_MONO THEN
      MAP_EVERY EXISTS_TAC [`C3:real`; `K3:num`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
      ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&8 + &2 * C + C * (&8 + &14 * C)`; `2 * K + 3`]
               LOG_POLY_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `M1:real`) THEN
  MP_TAC(SPEC `M1:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  EXISTS_TAC `M:num` THEN
  SUBGOAL_THEN
   `!n. 3 <= n /\
        &n <= (&8 + &2 * C + C * (&8 + &14 * C)) * log(&n) pow (2 * K + 3)
        ==> n <= M`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    TRANS_TAC REAL_LE_TRANS `M1:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`; `x:num`; `y:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `3 <= p /\ 3 <= q` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ODD_PRIME_GE_3]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_FACTOR_MINUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e1:num` STRIP_ASSUME_TAC o MATCH_MP FACTOR_DISJ_EXP))) THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`] CATALAN_FACTOR_PLUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e2:num` STRIP_ASSUME_TAC o MATCH_MP FACTOR_DISJ_EXP))) THEN
  SUBGOAL_THEN `&1 <= log(&p) /\ &1 <= log(&q) /\ &0 <= &8 + &14 * C`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_NUM_GE_1] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ARITH_RULE `~(p = q) ==> q < p \/ p < q`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `&q <= (&8 + &14 * C) * log(&p) pow (K + 2)` ASSUME_TAC THENL
     [ASM_CASES_TAC `x = 2` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        TRANS_TAC REAL_LE_TRANS `&2 * C * log(&p) pow (K + 1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CATALAN_BOUND_X2 THEN EXISTS_TAC `y:num` THEN
          ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
          REPEAT CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]];
        MATCH_MP_TAC CATALAN_STEP1_PGQ THEN
        MAP_EVERY EXISTS_TAC [`x:num`; `y:num`; `rho:num`; `sg:num`;
                              `e1:num`; `e2:num`] THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`C:real`; `K:num`; `p:num`; `q:num`; `x:num`; `y:num`;
                  `rho:num`; `sg:num`; `e1:num`; `e2:num`]
                 CATALAN_STEP2_PGQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p <= M` (fun th -> REWRITE_TAC[th] THEN MP_TAC th) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYLOG_COMBINE THEN EXISTS_TAC `&q` THEN
      ASM_REWRITE_TAC[REAL_POS];
      ASM_ARITH_TAC];
    SUBGOAL_THEN `&p <= (&8 + &14 * C) * log(&q) pow (K + 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC CATALAN_STEP1_QGP THEN
      MAP_EVERY EXISTS_TAC [`x:num`; `y:num`; `rho:num`; `sg:num`;
                            `e1:num`; `e2:num`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`C:real`; `K:num`; `p:num`; `q:num`; `x:num`; `y:num`;
                  `rho:num`; `sg:num`; `e1:num`; `e2:num`]
                 CATALAN_STEP2_QGP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `q <= M` (fun th -> REWRITE_TAC[th] THEN MP_TAC th) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYLOG_COMBINE THEN EXISTS_TAC `&p` THEN
      ASM_REWRITE_TAC[REAL_POS];
      ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Equal exponents are impossible, and composite exponents reduce to their   *)
(* prime factors: the odd prime factors of the exponents are bounded.        *)
(* ------------------------------------------------------------------------- *)

let CATALAN_EQUAL_EXPONENTS = prove
 (`!p x y. 2 <= p /\ 1 <= y ==> ~(x EXP p = y EXP p + 1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= y` THENL
   [MP_TAC(SPECL [`x:num`; `y:num`; `p:num`] EXP_MONO_LE_IMP) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MP_TAC(SPECL [`y:num`; `p:num`] EXP_ADD_ONE_LT) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`y + 1`; `x:num`; `p:num`] EXP_MONO_LE_IMP) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let CATALAN_ODD_PRIME_FACTORS_CONDITIONAL = prove
 (`!C2 K2 C3 K3.
     sharp_bound_property 2 C2 K2 /\ sharp_bound_property 3 C3 K3
     ==> ?M. !m n x y p q.
               2 <= m /\ 2 <= n /\ 2 <= x /\ 2 <= y /\
               x EXP m = y EXP n + 1 /\
               prime p /\ ODD p /\ p divides m /\
               prime q /\ ODD q /\ q divides n
               ==> p <= M /\ q <= M`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CATALAN_EXPONENT_BOUND_CONDITIONAL) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m1:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides] o check (fun th -> concl th = `p divides m`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides] o check (fun th -> concl th = `q divides n`)) THEN
  SUBGOAL_THEN `~(m1 = 0) /\ ~(n1 = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= x EXP m1 /\ 2 <= y EXP n1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [TRANS_TAC LE_TRANS `x EXP 1`; TRANS_TAC LE_TRANS `y EXP 1`] THEN
    ASM_REWRITE_TAC[EXP_1; LE_EXP] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x EXP m1) EXP p = (y EXP n1) EXP q + 1` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `p:num = q` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPEC `q:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`q:num`; `x EXP m1`; `y EXP n1`] CATALAN_EQUAL_EXPONENTS) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x EXP m1`; `y EXP n1`] THEN
    ASM_REWRITE_TAC[]]);;
