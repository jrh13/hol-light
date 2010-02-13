(* ========================================================================= *)
(* Definability in arithmetic of important notions.                          *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Pairing operation.                                                        *)
(* ------------------------------------------------------------------------- *)

let NPAIR = new_definition
  `NPAIR x y = (x + y) EXP 2 + x + 1`;;

let NPAIR_NONZERO = prove
 (`!x y. ~(NPAIR x y = 0)`,
  REWRITE_TAC[NPAIR; ADD_EQ_0; ARITH]);;

let NPAIR_INJ_LEMMA = prove
 (`x1 + y1 < x2 + y2 ==> NPAIR x1 y1 < NPAIR x2 y2`,
  STRIP_TAC THEN REWRITE_TAC[NPAIR; EXP_2] THEN
  REWRITE_TAC[ARITH_RULE `x + y + 1 < u + v + 1 <=> x + y < u + v`] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `SUC(x1 + y1) * SUC(x1 + y1)` THEN CONJ_TAC THENL
   [ARITH_TAC; ASM_MESON_TAC[LE_TRANS; LE_ADD; LE_MULT2; LE_SUC_LT]]);;

let NPAIR_INJ = prove
 (`(NPAIR x y = NPAIR x' y') <=> (x = x') /\ (y = y')`,
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x' + y' = x + y` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_CASES; NPAIR_INJ_LEMMA; LT_REFL];
    UNDISCH_TAC `NPAIR x y = NPAIR x' y'` THEN
    UNDISCH_TAC `x' + y' = x + y` THEN
    SIMP_TAC[NPAIR; EXP_2] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Decreasingness.                                                           *)
(* ------------------------------------------------------------------------- *)

let NPAIR_LT = prove
 (`!x y. x < NPAIR x y /\ y < NPAIR x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NPAIR] THEN
  REWRITE_TAC[ARITH_RULE `x < a + x + 1`] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `(x + y) + x + 1` THEN
  REWRITE_TAC[LE_ADD_RCANCEL; EXP_2; LE_SQUARE_REFL] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary concepts needed. NB: these are Delta so can be negated freely.  *)
(* ------------------------------------------------------------------------- *)

let primepow = new_definition
  `primepow p x <=> prime(p) /\ ?n. x = p EXP n`;;

let divides_DELTA = prove
 (`m divides n <=> ?x. x <= n /\ n = m * x`,
  REWRITE_TAC[divides] THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES] THEN MESON_TAC[LE_REFL]; ALL_TAC] THEN
  AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(m = 0) ==> 1 <= m`)) THEN
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM;
           RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  MESON_TAC[]);;

let prime_DELTA = prove
 (`prime(p) <=> 2 <= p /\ !n. n < p ==> n divides p ==> n = 1`,
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[ARITH; PRIME_0] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[ARITH; PRIME_1] THEN EQ_TAC THENL
   [ASM_MESON_TAC[prime; LT_REFL; PRIME_GE_2];
    ASM_MESON_TAC[prime;  DIVIDES_LE; LE_LT]]);;

let primepow_DELTA = prove
 (`primepow p x <=>
        prime(p) /\ ~(x = 0) /\
        !z. z <= x ==> z divides x ==> z = 1 \/ p divides z`,
  REWRITE_TAC[primepow; TAUT `a ==> b \/ c <=> a /\ ~b ==> c`] THEN
  ASM_CASES_TAC `prime(p)` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    ASM_REWRITE_TAC[EXP_EQ_0] THEN
    ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:num` o MATCH_MP PRIME_COPRIME) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p divides z` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP COPRIME_EXP) THEN
    ASM_MESON_TAC[COPRIME; DIVIDES_REFL];
    SPEC_TAC(`x:num`,`x:num`) THEN MATCH_MP_TAC num_WF THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = 1` THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EXP]; ALL_TAC] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `q:num` MP_TAC o MATCH_MP PRIME_FACTOR) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `!z. z <= x ==> z divides x /\ ~(z = 1) ==> p divides z` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `q = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q <= x` ASSUME_TAC THENL
     [ASM_MESON_TAC[DIVIDES_LE]; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `p divides x` MP_TAC THENL
     [ASM_MESON_TAC[DIVIDES_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_TAC `y:num`) THEN
    SUBGOAL_THEN `y < x` (ANTE_RES_THEN MP_TAC) THENL
     [MATCH_MP_TAC PRIME_FACTOR_LT THEN
      EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `y = 0` THENL
     [UNDISCH_TAC `x = p * y` THEN ASM_REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!z. z <= y ==> z divides y /\ ~(z = 1) ==> p divides z`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE
        [IMP_IMP]) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `y:num` THEN
        ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `y = 1 * y`] THEN
        REWRITE_TAC[LE_MULT_RCANCEL] THEN
        ASM_REWRITE_TAC[GSYM NOT_LT] THEN
        REWRITE_TAC[num_CONV `1`; LT; DE_MORGAN_THM] THEN
        ASM_MESON_TAC[PRIME_0; PRIME_1];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVIDES_LMUL THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
      EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[EXP]]]);;

(* ------------------------------------------------------------------------- *)
(* Sigma-representability of reflexive transitive closure.                   *)
(* ------------------------------------------------------------------------- *)

let PSEQ = new_recursive_definition num_RECURSION
  `(PSEQ p f m 0 = 0) /\
   (PSEQ p f m (SUC n) = f m + p * PSEQ p f (SUC m) n)`;;

let PSEQ_SPLIT = prove
 (`!f p n m r.
        PSEQ p f m (n + r) = PSEQ p f m n + p EXP n * PSEQ p f (m + n) r`,
  GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; EXP; MULT_CLAUSES; PSEQ] THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_AC; ADD_CLAUSES]);;

let PSEQ_1 = prove
 (`PSEQ p f m 1 = f m`,
  REWRITE_TAC[num_CONV `1`; ADD_CLAUSES; MULT_CLAUSES; PSEQ]);;

let PSEQ_BOUND = prove
 (`!n. ~(p = 0) /\ (!i. i < n ==> f i < p) ==> PSEQ p f 0 n < p EXP n`,
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THENL [REWRITE_TAC[PSEQ; EXP; ARITH]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`f:num->num`; `p:num`; `n:num`; `0`; `1`]
               PSEQ_SPLIT) THEN
  SIMP_TAC[ADD1; ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `p EXP n + p EXP n * PSEQ p f n 1` THEN
  ASM_SIMP_TAC[LT_ADD_RCANCEL; ARITH_RULE `i < n ==> i < SUC n`] THEN
  REWRITE_TAC[ARITH_RULE `p + p * q = p * (q + 1)`] THEN
  ASM_REWRITE_TAC[EXP_ADD; LE_MULT_LCANCEL; EXP_EQ_0] THEN
  MATCH_MP_TAC(ARITH_RULE `x < p ==> x + 1 <= p`) THEN
  ASM_SIMP_TAC[EXP_1; PSEQ_1; LT]);;

let RELPOW_LEMMA_1 = prove
 (`(f 0 = x) /\
   (f n = y) /\
   (!i. i < n ==> R (f i) (f(SUC i)))
   ==> ?p. (?i. i <= n /\ p <= SUC(FACT(f i))) /\
           prime p /\
           (?m. m < p EXP (SUC n) /\
                x < p /\ y < p /\
                (?qx. m = x + p * qx) /\
                (?ry. ry < p EXP n /\ (m = ry + p EXP n * y)) /\
                !q. q < p EXP n
                    ==> primepow p q
                        ==> ?r. r < q /\
                                ?a. a < p /\
                                    ?b. b < p /\
                                        R a b /\
                                        ?s. s <= m /\
                                            (m =
                                             r + q * (a + p * (b + p * s))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?j. j <= n /\ !i. i <= n ==> f i <= f j` MP_TAC THENL
   [SPEC_TAC(`n:num`,`n:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    INDUCT_TAC THENL
     [SIMP_TAC[LE] THEN MESON_TAC[LE_REFL]; ALL_TAC] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    DISJ_CASES_TAC(ARITH_RULE `f(SUC n) <= f(j) \/ f(j) <= f(SUC n)`) THENL
     [EXISTS_TAC `j:num` THEN
      ASM_SIMP_TAC[ARITH_RULE `j <= n ==> j <= SUC n`] THEN
      REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `SUC n` THEN REWRITE_TAC[LE_REFL] THEN
      REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[LE_REFL] THEN ASM_MESON_TAC[LE_TRANS]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ibig:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `(f:num->num) ibig` EUCLID_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:num` THEN CONJ_TAC THENL
   [EXISTS_TAC `ibig:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= n ==> f i < p` ASSUME_TAC THENL
   [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  EXISTS_TAC `PSEQ p f 0 (SUC n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PSEQ_BOUND THEN ASM_SIMP_TAC[LT_SUC_LE]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[PSEQ] THEN MESON_TAC[];
    MP_TAC(SPECL [`f:num->num`; `p:num`; `n:num`; `0`; `1`] PSEQ_SPLIT) THEN
    ASM_SIMP_TAC[ADD1; ADD_CLAUSES] THEN
    DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `PSEQ p f 0 n` THEN
    ASM_SIMP_TAC[PSEQ_BOUND; PSEQ_1; LT_IMP_LE];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
  ASM_SIMP_TAC[primepow; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN X_GEN_TAC `i:num` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_REWRITE_TAC[LT_EXP] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:num->num`; `p:num`; `i:num`; `0`; `SUC n - i`]
               PSEQ_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `i < n ==> (i + SUC n - i = SUC n)`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  EXISTS_TAC `PSEQ p f 0 i` THEN REWRITE_TAC[EQ_ADD_LCANCEL] THEN
  ASM_REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0; ADD_CLAUSES] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[PSEQ_BOUND; LT_TRANS; LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`f:num->num`; `p:num`; `1`; `i:num`; `n - i`]
               PSEQ_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `i < n ==> (1 + n - i = SUC n - i)`] THEN
  DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `PSEQ p f i 1` THEN
  ASM_REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_1] THEN
  ASM_SIMP_TAC[PSEQ_1; LT_IMP_LE] THEN
  MP_TAC(SPECL [`f:num->num`; `p:num`; `1`; `i + 1`; `n - i - 1`]
               PSEQ_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `i < n ==> (1 + n - i - 1 = n - i)`] THEN
  DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `PSEQ p f (i + 1) 1` THEN
  ASM_REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_1] THEN
  ASM_SIMP_TAC[PSEQ_1; ARITH_RULE `i < n ==> i + 1 <= n`] THEN
  ASM_SIMP_TAC[GSYM ADD1] THEN REWRITE_TAC[ADD1] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_ASSOC] THEN
  MATCH_MP_TAC(ARITH_RULE `1 * a <= c ==> a <= b + c`) THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0]);;

let RELPOW_LEMMA_2 = prove
 (`prime p /\ x < p /\ y < p /\
   (?qx. m = x + p * qx) /\
   (?ry. ry < p EXP n /\ (m = ry + p EXP n * y)) /\
   (!q. q < p EXP n
        ==> primepow p q
            ==> ?r a b s. (m = r + q * (a + p * (b + p * s))) /\
                          r < q /\ a < p /\ b < p /\ R a b)
   ==> RELPOW n R x y`,
  STRIP_TAC THEN REWRITE_TAC[RELPOW_SEQUENCE] THEN
  EXISTS_TAC `\i. (m DIV (p EXP i)) MOD p` THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  REWRITE_TAC[EXP; DIV_1] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `qx:num` THEN
    ASM_REWRITE_TAC[ADD_AC; MULT_AC];
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ASSUME `y < p`; MULT_CLAUSES; ADD_CLAUSES] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `ry:num` THEN
    REWRITE_TAC[ASSUME `m = ry + p EXP n * y`] THEN
    ASM_REWRITE_TAC[ADD_AC; MULT_AC];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p EXP i`) THEN
  ASM_SIMP_TAC[LT_EXP; PRIME_GE_2] THEN
  ASM_REWRITE_TAC[primepow] THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(R:num->num->bool) a b` THEN
  MATCH_MP_TAC(TAUT `(b <=> a) ==> a ==> b`) THEN BINOP_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `b + p * s` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_AC; MULT_AC];
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r + a * p EXP i` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC[ADD_AC; MULT_AC]; ALL_TAC] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `p EXP i + a * p EXP i` THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `p + q * p = (q + 1) * p`] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0] THEN
    UNDISCH_TAC `a < p` THEN ARITH_TAC]);;

let RELPOW_LEMMA = prove
 (`RELPOW n R x y <=>
        ?m p. prime p /\ x < p /\ y < p /\
              (?qx. m = x + p * qx) /\
              (?ry. ry < p EXP n /\ (m = ry + p EXP n * y)) /\
              !q. q < p EXP n
                  ==> primepow p q
                      ==> ?r a b s. (m = r + q * (a + p * (b + p * s))) /\
                                    r < q /\ a < p /\ b < p /\ R a b`,
  EQ_TAC THENL
   [ALL_TAC; REWRITE_TAC[RELPOW_LEMMA_2; LEFT_IMP_EXISTS_THM]] THEN
  REWRITE_TAC[RELPOW_SEQUENCE] THEN
  DISCH_THEN(CHOOSE_THEN(MP_TAC o GEN_ALL o MATCH_MP RELPOW_LEMMA_1)) THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[] THEN MESON_TAC[]);;

let RTC_SIGMA = prove
 (`RTC R x y <=>
        ?m p Q. primepow p Q /\ x < p /\ y < p /\
                (?s. m = x + p * s) /\
                (?r. r < Q /\ (m = r + Q * y)) /\
                !q. q < Q
                    ==> primepow p q
                        ==> ?r a b s. (m = r + q * (a + p * (b + p * s))) /\
                                      r < q /\ a < p /\ b < p /\ R a b`,
  REWRITE_TAC[RTC_RELPOW] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    REWRITE_TAC[RELPOW_LEMMA] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    DISCH_TAC THEN EXISTS_TAC `p EXP n` THEN ASM_REWRITE_TAC[primepow] THEN
    MESON_TAC[];
    REWRITE_TAC[primepow] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
    REWRITE_TAC[GSYM primepow] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 3 BINDER_CONV)
     [LEFT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV)
     [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[GSYM RELPOW_LEMMA]]);;

(* ------------------------------------------------------------------------- *)
(* Partially automate actual definability in object language.                *)
(* ------------------------------------------------------------------------- *)

let arith_pair = new_definition
  `arith_pair s t = (s ++ t) ** (s ++ t) ++ s ++ Suc Z`;;

let ARITH_PAIR = prove
 (`!s t v. termval v (arith_pair s t) = NPAIR (termval v s) (termval v t)`,
  REWRITE_TAC[termval; arith_pair; NPAIR; EXP_2; ARITH_SUC]);;

let FVT_PAIR = prove
 (`FVT(arith_pair s t) = FVT(s) UNION FVT(t)`,
  REWRITE_TAC[arith_pair; FVT] THEN SET_TAC[]);;

let OBJECTIFY =
  let is_add = is_binop `(+):num->num->num`
  and is_mul = is_binop `(*):num->num->num`
  and is_le = is_binop `(<=):num->num->bool`
  and is_lt = is_binop `(<):num->num->bool`
  and zero_tm = `0`
  and suc_tm = `SUC`
  and osuc_tm = `Suc`
  and oz_tm = `Z`
  and ov_tm = `V`
  and oadd_tm = `(++)`
  and omul_tm = `(**)`
  and oeq_tm = `(===)`
  and ole_tm = `(<<=)`
  and olt_tm = `(<<)`
  and oiff_tm = `(<->)`
  and oimp_tm = `(-->)`
  and oand_tm = `(&&)`
  and oor_tm = `(||)`
  and onot_tm = `Not`
  and oall_tm = `!!`
  and oex_tm = `??`
  and numeral_tm = `numeral`
  and assign_tm = `(|->):num->term->(num->term)->(num->term)`
  and term_ty = `:term`
  and form_ty = `:form`
  and num_ty = `:num`
  and formsubst_tm = `formsubst`
  and holdsv_tm = `holds v`
  and v_tm = `v:num->num` in
  let objectify1 fn op env tm = mk_comb(op,fn env (rand tm)) in
  let objectify2 fn op env tm =
    mk_comb(mk_comb(op,fn env (lhand tm)),fn env (rand tm)) in
  fun defs ->
    let defs' = [TERMVAL_NUMERAL; ARITH_PAIR] @ defs in
    let rec objectify_term env tm =
      if is_var tm then mk_comb(ov_tm,apply env tm)
      else if tm = zero_tm then oz_tm
      else if is_numeral tm then mk_comb(numeral_tm,tm)
      else if is_add tm then objectify2 objectify_term oadd_tm env tm
      else if is_mul tm then objectify2 objectify_term omul_tm env tm
      else if is_comb tm & rator tm = suc_tm
        then objectify1 objectify_term osuc_tm env tm
      else
        let f,args = strip_comb tm in
        let args' = map (objectify_term env) args in
        try let dth = find
              (fun th -> fst(strip_comb(rand(snd(strip_forall(concl th))))) = f)
              defs' in
            let l,r = dest_eq(snd(strip_forall(concl dth))) in
            list_mk_comb(fst(strip_comb(rand l)),args')
        with Failure _ ->
            let ty = itlist (mk_fun_ty o type_of) args' form_ty in
            let v = mk_var(fst(dest_var f),ty) in
            list_mk_comb(v,args') in
    let rec objectify_formula env fm =
      if is_forall fm then
        let x,bod = dest_forall fm in
        let n = mk_small_numeral
          (itlist (max o dest_small_numeral) (ran env) 0 + 1) in
        mk_comb(mk_comb(oall_tm,n),objectify_formula ((x |-> n) env) bod)
      else if is_exists fm then
        let x,bod = dest_exists fm in
        let n = mk_small_numeral
          (itlist (max o dest_small_numeral) (ran env) 0 + 1) in
        mk_comb(mk_comb(oex_tm,n),objectify_formula ((x |-> n) env) bod)
      else if is_iff fm then objectify2 objectify_formula oiff_tm env fm
      else if is_imp fm then objectify2 objectify_formula oimp_tm env fm
      else if is_conj fm then objectify2 objectify_formula oand_tm env fm
      else if is_disj fm then objectify2 objectify_formula oor_tm env fm
      else if is_neg fm then objectify1 objectify_formula onot_tm env fm
      else if is_le fm then objectify2 objectify_term ole_tm env fm
      else if is_lt fm then objectify2 objectify_term olt_tm env fm
      else if is_eq fm then objectify2 objectify_term oeq_tm env fm
      else objectify_term env fm in
   fun nam th ->
     let ptm,tm = dest_eq(snd(strip_forall(concl th))) in
     let vs = filter (fun v -> type_of v = num_ty) (snd(strip_comb ptm)) in
     let ns = 1--(length vs) in
     let env = itlist2 (fun v n -> v |-> mk_small_numeral n) vs ns undefined in
     let otm = objectify_formula env tm in
     let vs' = map (fun v -> mk_var(fst(dest_var v),term_ty)) vs in
     let stm = itlist2
       (fun v n a -> mk_comb(mk_comb(mk_comb(assign_tm,mk_small_numeral
         n),v),a))
       vs' ns ov_tm in
     let rside = mk_comb(mk_comb(formsubst_tm,stm),otm) in
     let vs'' = subtract (frees rside) vs' @ vs' in
     let lty = itlist (mk_fun_ty o type_of) vs'' (type_of rside) in
     let lside = list_mk_comb(mk_var(nam,lty),vs'') in
     let def = mk_eq(lside,rside) in
     let dth = new_definition def in
     let clside = lhs(snd(strip_forall(concl dth))) in
     let etm = mk_comb(holdsv_tm,clside) in
     let thm =
       (REWRITE_CONV ([dth; holds; HOLDS_FORMSUBST] @ defs') THENC
        REWRITE_CONV [termval; ARITH_EQ; o_THM; valmod] THENC
        GEN_REWRITE_CONV I [GSYM th]) etm in
     dth,DISCH_ALL (GENL (v_tm::vs') thm);;

(* ------------------------------------------------------------------------- *)
(* Some sort of common tactic for free variables.                            *)
(* ------------------------------------------------------------------------- *)

let FV_TAC ths =
  let ths' = ths @
   [FV; FORMSUBST_FV; FVT; TERMSUBST_FVT; IN_ELIM_THM;
    NOT_IN_EMPTY; IN_UNION; IN_DELETE; IN_SING]
  and tac =
     REWRITE_TAC[DISJ_ACI; TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
     REWRITE_TAC[EXISTS_OR_THM; GSYM CONJ_ASSOC; UNWIND_THM2; ARITH_EQ] THEN
     REWRITE_TAC[valmod; ARITH_EQ; FVT] THEN REWRITE_TAC[DISJ_ACI] in
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  ASM_REWRITE_TAC ths' THEN tac THEN ASM_SIMP_TAC ths' THEN tac;;

(* ------------------------------------------------------------------------- *)
(* So do the formula-level stuff (more) automatically.                       *)
(* ------------------------------------------------------------------------- *)

let arith_divides,ARITH_DIVIDES =
  OBJECTIFY [] "arith_divides" divides_DELTA;;

let FV_DIVIDES = prove
 (`!s t. FV(arith_divides s t) = FVT(s) UNION FVT(t)`,
  FV_TAC[arith_divides]);;

let arith_prime,ARITH_PRIME =
  OBJECTIFY [ARITH_DIVIDES] "arith_prime" prime_DELTA;;

let FV_PRIME = prove
 (`!t. FV(arith_prime t) = FVT(t)`,
  FV_TAC[arith_prime; FVT_NUMERAL; FV_DIVIDES]);;

let arith_primepow,ARITH_PRIMEPOW =
  OBJECTIFY [ARITH_PRIME; ARITH_DIVIDES] "arith_primepow" primepow_DELTA;;

let FV_PRIMEPOW = prove
 (`!s t. FV(arith_primepow s t) = FVT(s) UNION FVT(t)`,
  FV_TAC[arith_primepow; FVT_NUMERAL; FV_DIVIDES; FV_PRIME]);;

let arith_rtc,ARITH_RTC =
  OBJECTIFY
   [ARITH_PRIMEPOW;
    ASSUME `!v s t. holds v (R s t) <=> r (termval v s) (termval v t)`]
   "arith_rtc" RTC_SIGMA;;

let FV_RTC = prove
 (`!R. (!s t. FV(R s t) = FVT(s) UNION FVT(t))
       ==> !s t. FV(arith_rtc R s t) = FVT(s) UNION FVT(t)`,
  FV_TAC[arith_rtc; FV_PRIMEPOW]);;

(* ------------------------------------------------------------------------- *)
(* Automate RTC constructions, including parametrized ones.                  *)
(* ------------------------------------------------------------------------- *)

let OBJECTIFY_RTC =
  let pth = prove
   (`(!v x y. holds v (f x y) <=> f' (termval v x) (termval v y))
     ==> !g. (!n. g n = formsubst ((0 |-> n) V)
                                  (arith_rtc f (numeral 0)
                                               (arith_pair (V 0) (numeral 0))))
             ==> !v n. holds v (g n) <=> RTC f' 0 (NPAIR (termval v n) 0)`,
    DISCH_THEN(MP_TAC o MATCH_MP ARITH_RTC) THEN SIMP_TAC[HOLDS_FORMSUBST] THEN
    REWRITE_TAC[termval; o_DEF; ARITH_EQ; valmod;
                ARITH_PAIR; TERMVAL_NUMERAL]) in
  fun def nam th ->
    let th1 = MATCH_MP pth def in
    let v = fst(dest_forall(concl th1)) in
    let th2 = SPEC (mk_var(nam,type_of v)) th1 in
    let dth = new_definition (fst(dest_imp(concl th2))) in
    dth,ONCE_REWRITE_RULE[GSYM th] (MATCH_MP th2 dth);;

let RTCP = new_definition
  `RTCP R m x y <=> RTC (R m) x y`;;

let RTCP_SIGMA = REWRITE_RULE[GSYM RTCP]
        (INST [`(R:num->num->num->bool) m`,`R:num->num->bool`] RTC_SIGMA);;

let arith_rtcp,ARITH_RTCP =
  OBJECTIFY
   [ARITH_PRIMEPOW;
    ASSUME `!v m s t. holds v (R m s t) <=>
                   r (termval v m) (termval v s) (termval v t)`]
   "arith_rtcp" RTCP_SIGMA;;

let ARITH_RTC_PARAMETRIZED = REWRITE_RULE[RTCP] ARITH_RTCP;;

let FV_RTCP = prove
 (`!R. (!s t u. FV(R s t u) = FVT(s) UNION FVT(t) UNION FVT(u))
       ==> !s t u. FV(arith_rtcp R s t u) = FVT(s) UNION FVT(t) UNION FVT(u)`,
  FV_TAC[arith_rtcp; FV_PRIMEPOW]);;

let OBJECTIFY_RTCP =
  let pth = prove
   (`(!v m x y. holds v (f m x y) <=>
                f' (termval v m) (termval v x) (termval v y))
     ==> !g. (!m n. g m n = formsubst ((1 |-> m) ((0 |-> n) V))
                                  (arith_rtcp f (V 1) (numeral 0)
                                               (arith_pair (V 0) (numeral 0))))
             ==> !v m n. holds v (g m n) <=>
                          RTC (f' (termval v m)) 0 (NPAIR (termval v n) 0)`,
    DISCH_THEN(MP_TAC o MATCH_MP ARITH_RTC_PARAMETRIZED) THEN
    SIMP_TAC[HOLDS_FORMSUBST] THEN
    REWRITE_TAC[termval; o_DEF; ARITH_EQ; valmod;
                ARITH_PAIR; TERMVAL_NUMERAL]) in
  fun def nam th ->
    let th1 = MATCH_MP pth def in
    let v = fst(dest_forall(concl th1)) in
    let th2 = SPEC (mk_var(nam,type_of v)) th1 in
    let dth = new_definition (fst(dest_imp(concl th2))) in
    dth,ONCE_REWRITE_RULE[GSYM th] (MATCH_MP th2 dth);;

(* ------------------------------------------------------------------------- *)
(* Generic result about primitive recursion.                                 *)
(* ------------------------------------------------------------------------- *)

let PRIMREC_SIGMA = prove
 (`(fn 0 = e) /\
   (!n. fn (SUC n) = f (fn n) n)
   ==> !x y. RTC (\x y. ?n r. (x = NPAIR n r) /\ (y = NPAIR (SUC n) (f r n)))
                 (NPAIR 0 e) (NPAIR x y) <=>
             (fn(x) = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ONCE_REWRITE_TAC[RTC_CASES_L] THEN ASM_REWRITE_TAC[NPAIR_INJ; NOT_SUC] THEN
  REWRITE_TAC[SUC_INJ; RIGHT_AND_EXISTS_THM] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  ASM_REWRITE_TAC[UNWIND_THM2] THEN ASM_MESON_TAC[]);;

let arith_primrecstep = new_definition
 `arith_primrecstep R s t =
        (formsubst ((0 |-> s) ((1 |-> t) V))
                  (?? 2 (?? 3 (?? 4
                  (V 0 === arith_pair (V 2) (V 3) &&
                   V 1 === arith_pair (Suc(V 2)) (V 4) &&
                   R (V 3) (V 2) (V 4))))))`;;

let ARITH_PRIMRECSTEP = prove
 (`(!v x y z. holds v (R x y z) <=>
              (f (termval v x) (termval v y) = termval v z))
    ==> !v s t. holds v (arith_primrecstep R s t) <=>
                ?n r. (termval v s = NPAIR n r) /\
                      (termval v t = NPAIR (SUC n) (f r n))`,
  STRIP_TAC THEN
  ASM_REWRITE_TAC[arith_primrecstep; holds; HOLDS_FORMSUBST] THEN
  ASM_REWRITE_TAC[termval; valmod; o_DEF; ARITH_EQ; ARITH_PAIR] THEN
  MESON_TAC[]);;

let FV_PRIMRECSTEP = prove
 (`!R. (!s t u. FV(R s t u) SUBSET (FVT(s) UNION FVT(t) UNION FVT(u)))
       ==> !s t. FV(arith_primrecstep R s t) = FVT(s) UNION FVT(t)`,
  REWRITE_TAC[SUBSET; IN_UNION] THEN FV_TAC[arith_primrecstep; FVT_PAIR] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `~a ==> (a \/ b <=> b)`) THEN
  DISCH_THEN(CHOOSE_THEN
   (CONJUNCTS_THEN2(ANTE_RES_THEN MP_TAC) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FVT; IN_SING]);;

let arith_primrec = new_definition
  `arith_primrec R c s t =
        arith_rtc (arith_primrecstep R)
            (arith_pair Z c) (arith_pair s t)`;;

let ARITH_PRIMREC = prove
 (`!fn e f R c.
        (fn 0 = e) /\ (!n. fn (SUC n) = f (fn n) n) /\
        (!v. termval v c = e) /\
                  (!v x y z. holds v (R x y z) <=>
                             (f (termval v x) (termval v y) = termval v z))
                  ==> !v s t. holds v (arith_primrec R c s t) <=>
                               (fn(termval v s) = termval v t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ARITH_PRIMRECSTEP) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ARITH_RTC) THEN
  CONV_TAC(TOP_DEPTH_CONV ETA_CONV) THEN
  SIMP_TAC[arith_primrec; ARITH_PAIR; termval] THEN
  ASM_SIMP_TAC[PRIMREC_SIGMA]);;

let FV_PRIMREC = prove
 (`!R c. (FVT c = {}) /\
         (!s t u. FV(R s t u) SUBSET (FVT(s) UNION FVT(t) UNION FVT(u)))
         ==> !s t. FV(arith_primrec R c s t) = FVT(s) UNION FVT(t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[arith_primrec] THEN
  ASM_SIMP_TAC[FV_RTC; FVT_PAIR; FV_PRIMRECSTEP;
                 UNION_EMPTY; UNION_ACI; FVT]);;
