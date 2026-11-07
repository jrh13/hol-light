(* ========================================================================= *)
(* The exponent bound for X^2 = Y^q + 1 (the Ko Chao case of the Catalan     *)
(* reduction; Tijdeman 1976).                                                *)
(*                                                                           *)
(* Purpose: KO_CHAO_DESCENT: X is odd, X = 2 s + 1, 4 s (s + 1) = Y^q, and   *)
(* the coprime factors (4 s, s + 1) or (s, 4 (s + 1)) are q-th powers, so    *)
(* 2^(q-2) a^q - b^q = +-1 with b odd. KO_CHAO_EXPONENT_BOUND: for q >= 5    *)
(* we get b >= 3, a <= b, and Lambda = q log(2 a / b) - log 4 =              *)
(* log((2a)^q / (4 b^q)) is a non-zero linear form in two logarithms with    *)
(* |Lambda| <= 2 / b^q. SHARP_BOUND_2 (u1 / v1 = 4 / 1, g0 = 2,              *)
(* u2 / v2 = 2a / b, A = 2b, B = q) gives                                    *)
(* q log b <= log 2 + C 2^K log(2b) log q, hence q <= c log q and q is       *)
(* bounded (LOG_POLY_BOUND).                                                 *)
(*                                                                           *)
(* Main results: KO_CHAO_EXPONENT_BOUND, KO_CHAO_DESCENT.                    *)
(*                                                                           *)
(* Uses: Baker/tijdeman.ml (SHARP_BAKER_RATIONAL), Baker/catalan.ml          *)
(* (sharp_bound_property, SHARP_BOUND_2, SHARP_BOUND_PROPERTY_MONO),         *)
(* Baker/lemmas.ml (LOG_POLY_BOUND, ODD_PRIME_GE_3 and the elementary EXP    *)
(* and LOG lemmas).                                                          *)
(* ========================================================================= *)

needs "Baker/tijdeman.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary part: the descent.                                             *)
(* ------------------------------------------------------------------------- *)

let KO_CHAO_EXP_ADD_TWO_LT = prove
 (`!u n. 1 <= u /\ 2 <= n ==> u EXP n + 2 < (u + 2) EXP n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`u:num`; `n:num`] EXP_ADD_ONE_LT) THEN
  MP_TAC(SPECL [`u + 1`; `n:num`] EXP_ADD_ONE_LT) THEN
  REWRITE_TAC[ARITH_RULE `(u + 1) + 1 = u + 2`] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= u ==> 1 <= u + 1`] THEN ARITH_TAC);;

let KO_CHAO_EXP2_SPLIT = prove
 (`!q. 2 <= q ==> 2 EXP q = 4 * 2 EXP (q - 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q = (q - 2) + 2`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let KO_CHAO_X_ODD = prove
 (`!q X Y. 2 <= q /\ 2 <= X /\ X EXP 2 = Y EXP q + 1 ==> ODD X`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_EVEN] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?j. X = 2 * j + 2` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o REWRITE_RULE[EVEN_EXISTS] o
      check (fun th -> concl th = `EVEN X`)) THEN
    EXISTS_TAC `k - 1` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * j + 1) * (2 * j + 3) = Y EXP q` ASSUME_TAC THENL
   [UNDISCH_TAC `(2 * j + 2) EXP 2 = Y EXP q + 1` THEN
    REWRITE_TAC[EXP_2] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `2 * j + 1`; `2 * j + 3`; `Y:num`] COPRIME_POW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ARITH_RULE `2 * j + 3 = (2 * j + 1) + 2`) THEN
    REWRITE_TAC[NUMBER_RULE `!a b. coprime(a,a + b) <=> coprime(a,b)`] THEN
    REWRITE_TAC[COPRIME_2; ODD_ADD; ODD_MULT; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num` (X_CHOOSE_THEN `v:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ODD u /\ ODD v` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ODD(u EXP q) /\ ODD(v EXP q)` MP_TAC THENL
     [UNDISCH_TAC `2 * j + 1 = u EXP q` THEN
      UNDISCH_TAC `2 * j + 3 = v EXP q` THEN
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
      REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH];
      ASM_REWRITE_TAC[ODD_EXP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `v EXP q = u EXP q + 2` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= u` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(u = 0) ==> 1 <= u`) THEN DISCH_TAC THEN
    UNDISCH_TAC `ODD u` THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `u + 2 <= v` ASSUME_TAC THENL
   [SUBGOAL_THEN `u < v` MP_TAC THENL
     [SUBGOAL_THEN `u EXP q < v EXP q` MP_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[EXP_MONO_LT] THEN MESON_TAC[]];
      UNDISCH_TAC `ODD u` THEN UNDISCH_TAC `ODD v` THEN
      REWRITE_TAC[ODD_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `m1:num` SUBST1_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `m2:num` SUBST1_TAC) THEN
      REWRITE_TAC[LT_SUC; LT_MULT_LCANCEL; ARITH_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`u:num`; `q:num`] KO_CHAO_EXP_ADD_TWO_LT) THEN
  MP_TAC(SPECL [`u + 2`; `v:num`; `q:num`] EXP_MONO_LE_IMP) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let KO_CHAO_POW_4 = prove
 (`!q A s. 2 <= q /\ 4 * s = A EXP q ==> ?a. s = 2 EXP (q - 2) * a EXP q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EVEN A` MP_TAC THENL
   [SUBGOAL_THEN `EVEN(A EXP q)` MP_TAC THENL
     [UNDISCH_TAC `4 * s = A EXP q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[EVEN_MULT; ARITH];
      REWRITE_TAC[EVEN_EXP] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST_ALL_TAC o
    REWRITE_RULE[EVEN_EXISTS]) THEN
  EXISTS_TAC `a:num` THEN UNDISCH_TAC `4 * s = (2 * a) EXP q` THEN
  SUBGOAL_THEN `(2 * a) EXP q = 4 * 2 EXP (q - 2) * a EXP q` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_EXP; MULT_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KO_CHAO_EXP2_SPLIT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EQ_MULT_LCANCEL; ARITH_EQ] THEN MESON_TAC[]]);;

let KO_CHAO_DESCENT = prove
 (`!q X Y. prime q /\ ODD q /\ 2 <= X /\ 2 <= Y /\ X EXP 2 = Y EXP q + 1
           ==> ?a b. 1 <= a /\ 1 <= b /\ ODD b /\
                     (2 EXP (q - 2) * a EXP q = b EXP q + 1 \/
                      b EXP q = 2 EXP (q - 2) * a EXP q + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `3 <= q` ASSUME_TAC THENL
   [ASM_MESON_TAC[ODD_PRIME_GE_3]; ALL_TAC] THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `X:num`; `Y:num`] KO_CHAO_X_ODD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC o
    REWRITE_RULE[ODD_EXISTS]) THEN
  SUBGOAL_THEN `1 <= s` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(4 * s) * (s + 1) = Y EXP q` ASSUME_TAC THENL
   [UNDISCH_TAC `SUC(2 * s) EXP 2 = Y EXP q + 1` THEN
    REWRITE_TAC[EXP_2] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `EVEN s` THENL
   [MP_TAC(SPECL [`q:num`; `4 * s`; `s + 1`; `Y:num`] COPRIME_POW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COPRIME_LMUL] THEN CONJ_TAC THENL
       [SUBST1_TAC(ARITH_RULE `4 = 2 EXP 2`) THEN
        REWRITE_TAC[COPRIME_LEXP; COPRIME_2; ARITH_EQ; ODD_ADD; ARITH_ODD] THEN
        ASM_REWRITE_TAC[NOT_ODD];
        REWRITE_TAC[NUMBER_RULE `!n. coprime(n,n + 1)`]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:num` (X_CHOOSE_THEN `b:num`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(SPECL [`q:num`; `A:num`; `s:num`] KO_CHAO_POW_4) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN DISCH_TAC THEN
      UNDISCH_TAC `s = 2 EXP (q - 2) * a EXP q` THEN
      ASM_REWRITE_TAC[EXP_ZERO; MULT_CLAUSES] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `1 <= b <=> ~(b = 0)`] THEN DISCH_TAC THEN
      UNDISCH_TAC `s + 1 = b EXP q` THEN
      ASM_REWRITE_TAC[EXP_ZERO] THEN ARITH_TAC;
      SUBGOAL_THEN `ODD(b EXP q)` MP_TAC THENL
       [UNDISCH_TAC `s + 1 = b EXP q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[ODD_ADD; ARITH_ODD; NOT_ODD] THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[ODD_EXP]];
      DISJ2_TAC THEN UNDISCH_TAC `s + 1 = b EXP q` THEN
      UNDISCH_TAC `s = 2 EXP (q - 2) * a EXP q` THEN ARITH_TAC];
    MP_TAC(SPECL [`q:num`; `s:num`; `4 * (s + 1)`; `Y:num`] COPRIME_POW) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[COPRIME_RMUL] THEN CONJ_TAC THENL
         [SUBST1_TAC(ARITH_RULE `4 = 2 EXP 2`) THEN
          REWRITE_TAC[COPRIME_REXP; COPRIME_2; ARITH_EQ] THEN
          ASM_REWRITE_TAC[GSYM NOT_EVEN];
          REWRITE_TAC[NUMBER_RULE `!n. coprime(n,n + 1)`]];
        UNDISCH_TAC `(4 * s) * (s + 1) = Y EXP q` THEN ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `A:num`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(SPECL [`q:num`; `A:num`; `s + 1`] KO_CHAO_POW_4) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN DISCH_TAC THEN
      UNDISCH_TAC `s + 1 = 2 EXP (q - 2) * a EXP q` THEN
      ASM_REWRITE_TAC[EXP_ZERO; MULT_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `1 <= b <=> ~(b = 0)`] THEN DISCH_TAC THEN
      UNDISCH_TAC `s = b EXP q` THEN
      ASM_REWRITE_TAC[EXP_ZERO] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `ODD(b EXP q)` MP_TAC THENL
       [UNDISCH_TAC `s = b EXP q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM NOT_EVEN] THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[ODD_EXP]];
      DISJ1_TAC THEN UNDISCH_TAC `s = b EXP q` THEN
      UNDISCH_TAC `s + 1 = 2 EXP (q - 2) * a EXP q` THEN ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Analytic part: the linear form in two logarithms.                         *)
(* ------------------------------------------------------------------------- *)

let KO_CHAO_EXP_2_GE_4 = prove
 (`&4 <= exp(&2)`,
  SUBGOAL_THEN `exp(&2) = exp(&1) * exp(&1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 * &2 <= exp(&1) * exp(&1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let KO_CHAO_LOG_SUB_LE = prove
 (`!x y. &0 < x /\ x <= y ==> log y - log x <= (y - x) / x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (y:real)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_DIV] THEN
  SUBGOAL_THEN `(y:real) / x = &1 + (y - x) / x` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < (x:real)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_REAL_ARITH_TAC);;

let KO_CHAO_LOG_FORM = prove
 (`!q a b. 2 <= q /\ 1 <= a /\ 2 <= b /\
           (2 EXP (q - 2) * a EXP q = b EXP q + 1 \/
            b EXP q = 2 EXP (q - 2) * a EXP q + 1)
           ==> ~(--(&1) * log(&4 / &1) + &q * log(&(2 * a) / &b) = &0) /\
               abs(--(&1) * log(&4 / &1) + &q * log(&(2 * a) / &b))
               <= &2 / &b pow q`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < &(2 * a) /\ &0 < &b` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `--(&1) * log(&4 / &1) + &q * log(&(2 * a) / &b) =
    log(&(2 * a) pow q) - log(&4 * &b pow q)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_1; LOG_DIV; LOG_MUL; LOG_POW; REAL_POW_LT;
                 REAL_ARITH `&0 < &4`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &b pow q /\ &0 < &(2 * a) pow q /\ &2 <= &b pow q`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    TRANS_TAC LE_TRANS `b EXP 1` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[EXP_1];
      REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * a) EXP q = 4 * 2 EXP (q - 2) * a EXP q` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_EXP; MULT_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KO_CHAO_EXP2_SPLIT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN `&(2 * a) pow q = &4 * &b pow q + &4` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD;
                  REAL_OF_NUM_EQ] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`&4 * &b pow q`; `&(2 * a) pow q`] KO_CHAO_LOG_SUB_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `log(&4 * &b pow q) < log(&(2 * a) pow q)` MP_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&(2 * a) pow q - &4 * &b pow q) / (&4 * &b pow q) <= &2 / &b pow q`
    MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `(x + &4) - x = &4`] THEN
      MATCH_MP_TAC REAL_FRAC_LE_CROSS THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `&4 * &b pow q = &(2 * a) pow q + &4` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD;
                  REAL_OF_NUM_EQ] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`&(2 * a) pow q`; `&4 * &b pow q`] KO_CHAO_LOG_SUB_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `log(&(2 * a) pow q) < log(&4 * &b pow q)` MP_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&4 * &b pow q - &(2 * a) pow q) / &(2 * a) pow q <= &2 / &b pow q`
    MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `(x + &4) - x = &4`] THEN
      MATCH_MP_TAC REAL_FRAC_LE_CROSS THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let KO_CHAO_BOUND_CONDITIONAL = prove
 (`!C K q a b.
     sharp_bound_property 2 C K /\ &0 <= C /\
     3 <= q /\ 1 <= a /\ a <= b /\ 3 <= b /\
     (2 EXP (q - 2) * a EXP q = b EXP q + 1 \/
      b EXP q = 2 EXP (q - 2) * a EXP q + 1)
     ==> &q <= (&1 + &2 * C * &2 pow K) * log(&q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`q:num`; `a:num`; `b:num`] KO_CHAO_LOG_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &b /\ &0 < &b pow q /\ &0 < log(&b) /\
                &1 <= log(&q) /\ log(&2) <= log(&b)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &b` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_LT; LOG_NUM_GE_1] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&1) <= &(2 * b) /\ &4 <= exp(&2) /\ &1 <= exp(&2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[KO_CHAO_EXP_2_GE_4] THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&3` THEN
      REWRITE_TAC[EXP_1_LE_3; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MP_TAC KO_CHAO_EXP_2_GE_4 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP SHARP_BOUND_2 (ASSUME `sharp_bound_property 2 C K`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`4`; `1`; `2 * a`; `b:num`; `--(&1)`; `&q`;
                             `&(2 * b)`; `&q`; `&2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG; REAL_ABS_NEG; REAL_ABS_NUM;
                    REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`(C:real) * &2 pow K * log(&(2 * b)) * log(&q)`; `&2`;
                `&b pow q`]
               EXP_NEG_LE_RATIO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN DISCH_TAC THEN
  SUBGOAL_THEN `log(&(2 * b)) <= &2 * log(&b)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &2`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (C:real) * &2 pow K * log(&q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((C:real) * &2 pow K * log(&q)) * log(&(2 * b)) <=
                (C * &2 pow K * log(&q)) * (&2 * log(&b))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&q * log(&b) <= (&1 + &2 * (C:real) * &2 pow K * log(&q)) * log(&b)`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The export: the exponent q of X^2 = Y^q + 1 is bounded.                   *)
(* ------------------------------------------------------------------------- *)

let KO_CHAO_EXPONENT_BOUND = prove
 (`?M. !q X Y. prime q /\ ODD q /\ 2 <= X /\ 2 <= Y /\
   X EXP 2 = Y EXP q + 1
   ==> q <= M`,
  MP_TAC(SPEC `2` SHARP_BAKER_RATIONAL) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (X_CHOOSE_TAC `K:num`)) THEN
  SUBGOAL_THEN `sharp_bound_property 2 (abs(C0:real)) K` ASSUME_TAC THENL
   [MATCH_MP_TAC SHARP_BOUND_PROPERTY_MONO THEN
    MAP_EVERY EXISTS_TAC [`C0:real`; `K:num`] THEN
    ASM_REWRITE_TAC[LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + &2 * abs(C0:real) * &2 pow K`; `1`] LOG_POLY_BOUND) THEN
  REWRITE_TAC[REAL_POW_1] THEN DISCH_THEN(X_CHOOSE_TAC `M1:real`) THEN
  MP_TAC(SPEC `M1:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 5` THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `X:num`; `Y:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `q <= 4` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `X:num`; `Y:num`] KO_CHAO_DESCENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  SUBGOAL_THEN `3 <= b` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(b = 1) /\ ~(b = 2)` MP_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
       [SUBGOAL_THEN `8 <= 2 EXP (q - 2) * a EXP q` MP_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE `8 * 1 <= x ==> 8 <= x`) THEN
          MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
           [TRANS_TAC LE_TRANS `2 EXP 3` THEN CONJ_TAC THENL
             [CONV_TAC NUM_REDUCE_CONV;
              REWRITE_TAC[LE_EXP; ARITH] THEN ASM_ARITH_TAC];
            REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
            ASM_ARITH_TAC];
          FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
          REWRITE_TAC[EXP_ONE] THEN ARITH_TAC];
        UNDISCH_TAC `ODD 2` THEN REWRITE_TAC[ARITH]];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= b` ASSUME_TAC THENL
   [SUBGOAL_THEN `a EXP q <= b EXP q` MP_TAC THENL
     [SUBGOAL_THEN `2 <= 2 EXP (q - 2) /\ 1 <= b EXP q` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [TRANS_TAC LE_TRANS `2 EXP 1` THEN CONJ_TAC THENL
           [REWRITE_TAC[EXP_1; LE_REFL];
            REWRITE_TAC[LE_EXP; ARITH] THEN ASM_ARITH_TAC];
          REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
          ASM_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `2 * a EXP q <= 2 EXP (q - 2) * a EXP q` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_MONO_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`abs(C0:real)`; `K:num`; `q:num`; `a:num`; `b:num`]
               KO_CHAO_BOUND_CONDITIONAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&q <= &N` MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `M1:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC]);;
