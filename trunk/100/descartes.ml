(* ========================================================================= *)
(* Rob Arthan's "Descartes's Rule of Signs by an Easy Induction".            *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* A couple of handy lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let OPPOSITE_SIGNS = prove
 (`!a b:real. a * b < &0 <=> &0 < a /\ b < &0 \/ a < &0 /\ &0 < b`,
  REWRITE_TAC[REAL_ARITH `a * b < &0 <=> &0 < a * --b`; REAL_MUL_POS_LT] THEN
  REAL_ARITH_TAC);;

let VARIATION_SET_FINITE = prove
 (`FINITE s ==> FINITE {p,q | p IN s /\ q IN s /\ P p q}`,
  REWRITE_TAC[SET_RULE
   `{p,q | p IN s /\ q IN t /\ R p q} =
    {p,q | p IN s /\ q IN {q | q IN t /\ R p q}}`] THEN
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_RESTRICT]);;

(* ------------------------------------------------------------------------- *)
(* Variation in a sequence of coefficients.                                  *)
(* ------------------------------------------------------------------------- *)

let variation = new_definition
 `variation s (a:num->real) =
     CARD {(p,q) | p IN s /\ q IN s /\ p < q /\
                   a(p) * a(q) < &0 /\
                   !i. i IN s /\ p < i /\ i < q ==> a(i) = &0 }`;;

let VARIATION_EQ = prove
 (`!a b s. (!i. i IN s ==> a i = b i) ==> variation s a = variation s b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[variation] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  ASM_MESON_TAC[]);;

let VARIATION_SUBSET = prove
 (`!a s t. t SUBSET s /\ (!i. i IN (s DIFF t) ==> a i = &0)
           ==> variation s a = variation t a`,
  REWRITE_TAC[IN_DIFF; SUBSET] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[variation] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  ASM_MESON_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL]);;

let VARIATION_SPLIT = prove
 (`!a s n.
        FINITE s /\ n IN s /\ ~(a n = &0)
        ==> variation s a = variation {i | i IN s /\ i <= n} a +
                            variation {i | i IN s /\ n <= i} a`,
  REWRITE_TAC[variation] THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_SIMP_TAC[VARIATION_SET_FINITE; FINITE_RESTRICT] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ARITH_TAC;
    REWRITE_TAC[IN_UNION; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC;
      STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
        MP_TAC(SPEC `n:num` th) THEN ASM_REWRITE_TAC[] THEN ASSUME_TAC th) THEN
      SIMP_TAC[TAUT `~(a /\ b) <=> ~b \/ ~a`] THEN MATCH_MP_TAC MONO_OR] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    TRY(FIRST_ASSUM MATCH_MP_TAC) THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `n:num` th) THEN ASM_REWRITE_TAC[]) THEN
    ASM_ARITH_TAC]);;

let VARIATION_SPLIT_NUMSEG = prove
 (`!a m n p. n IN m..p /\ ~(a n = &0)
             ==> variation(m..p) a = variation(m..n) a + variation(n..p) a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> b /\ c ==> a ==> d`]
     VARIATION_SPLIT)) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC);;

let VARIATION_1 = prove
 (`!a n. variation {n} a = 0`,
  REWRITE_TAC[variation; IN_SING] THEN
  REWRITE_TAC[ARITH_RULE `p:num = n /\ q = n /\ p < q /\ X <=> F`] THEN
  MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; NOT_IN_EMPTY]);;

let VARIATION_2 = prove
 (`!a m n. variation {m,n} a = if a(m) * a(n) < &0 then 1 else 0`,
  GEN_TAC THEN MATCH_MP_TAC WLOG_LT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INSERT_AC; VARIATION_1; GSYM REAL_NOT_LE; REAL_LE_SQUARE];
    REWRITE_TAC[INSERT_AC; REAL_MUL_SYM];
    REPEAT STRIP_TAC THEN REWRITE_TAC[variation; IN_INSERT; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[TAUT
     `a /\ b /\ c /\ d /\ e <=> (a /\ b /\ c) /\ d /\ e`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `m:num < n
      ==> ((p = m \/ p = n) /\ (q = m \/ q = n) /\ p < q <=>
           p = m /\ q = n)`] THEN
    REWRITE_TAC[MESON[] `(p = m /\ q = n) /\ X p q <=>
                         (p = m /\ q = n) /\ X m n`] THEN
    REWRITE_TAC[ARITH_RULE `(i:num = m \/ i = n) /\ m < i /\ i < n <=> F`] THEN
    ASM_CASES_TAC `a m * a(n:num) < &0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[SET_RULE `{p,q | p = a /\ q = b} = {(a,b)}`] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH];
      MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
      SIMP_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; NOT_IN_EMPTY]]]);;

let VARIATION_3 = prove
 (`!a m n p.
        m < n /\ n < p
        ==> variation {m,n,p} a = if a(n) = &0 then variation{m,p} a
                                  else variation {m,n} a + variation{n,p} a`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC VARIATION_SUBSET THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`a:num->real`; `{m:num,n,p}`; `n:num`] VARIATION_SPLIT) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC]);;

let VARIATION_OFFSET = prove
 (`!p m n a. variation(m+p..n+p) a = variation(m..n) (\i. a(i + p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[variation] THEN
  MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN MAP_EVERY EXISTS_TAC
   [`\(i:num,j). i - p,j - p`; `\(i:num,j). i + p,j + p`] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
  SIMP_TAC[VARIATION_SET_FINITE; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `y < &0 ==> x = y ==> x < &0`)) THEN
    BINOP_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i - p:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC EQ_IMP] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The crucial lemma (roughly Lemma 2 in the paper).                         *)
(* ------------------------------------------------------------------------- *)

let ARTHAN_LEMMA = prove
 (`!n a b.
        ~(a n = &0) /\ (b n = &0) /\ (!m. sum(0..m) a = b m)
        ==> ?d. ODD d /\ variation (0..n) a = variation (0..n) b + d`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "*") THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> n = 1 \/ 2 <= n`))
  THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `1` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    REWRITE_TAC[VARIATION_2; OPPOSITE_SIGNS] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th)) THEN
    SIMP_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. 1 < p /\ p <= n /\ ~(a p = &0)` MP_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `2 <= n ==> 1 < n`; LE_REFL];
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b /\ c /\ ~d) <=> a /\ b /\ c ==> d`] THEN
    STRIP_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN(MP_TAC o SPECL
   [`(\i. if i + 1 = 1 then a 0 + a 1 else a(i + 1)):num->real`;
    `(\i. b(i + 1)):num->real`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1) /\ n - 1 + 1 = n`] THEN
  REWRITE_TAC[GSYM(SPEC `1` VARIATION_OFFSET)] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(0..m+1) a` THEN CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_RULE `0 + 1 <= n + 1`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_ASSOC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; SUM_OFFSET] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ABBREV_TAC `a':num->real = \m. if m = 1 then a 0 + a 1 else a m` THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 <= n ==> n - 1 + 1 = n /\ n - 1 - 1 + 1 = n - 1`] THEN
    CONV_TAC NUM_REDUCE_CONV] THEN
  SUBGOAL_THEN
   `variation (1..n) a' = variation {1,p} a' + variation (p..n) a /\
    variation (0..n) a = variation {0,1,p} a + variation (p..n) a`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
     [EXISTS_TAC `variation(1..p) a' + variation(p..n) a'`;
      EXISTS_TAC `variation(0..p) a + variation(p..n) a`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN EXPAND_TAC "a'" THEN
       REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
       BINOP_TAC THENL
        [MATCH_MP_TAC VARIATION_SUBSET; MATCH_MP_TAC VARIATION_EQ] THEN
       EXPAND_TAC "a'" THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
       REWRITE_TAC[IN_NUMSEG] THEN TRY(GEN_TAC THEN ASM_ARITH_TAC) THEN
       (CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[IN_DIFF]]) THEN
       REWRITE_TAC[IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
       REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
       TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (INT_ARITH
   `a + b:int = c + d ==> c = (a + b) - d`)) THEN
  REWRITE_TAC[INT_ARITH `a + b:int = c + d <=> d = (a + b) - c`] THEN
  ASM_CASES_TAC `a 0 + a 1 = &0` THENL
   [SUBGOAL_THEN `!i. 0 < i /\ i < p ==> b i = &0` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `i:num`) THEN
      ASM_SIMP_TAC[SUM_CLAUSES_LEFT; LE_0;
                   ARITH_RULE `0 < i ==> 0 + 1 <= i`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LID] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(b:num->real) p = a p` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
      SIMP_TAC[SUM_CLAUSES_RIGHT; ASSUME `1 < p`;
                 ARITH_RULE `1 < p ==> 0 < p /\ 0 <= p`] THEN
      ASM_REWRITE_TAC[REAL_EQ_ADD_RCANCEL_0] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `variation(0..n) b = variation {0,p} b + variation(1..n) b`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..p) b + variation(p..n) b` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN REWRITE_TAC[IN_NUMSEG] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `p:num`) THEN
        SIMP_TAC[SUM_CLAUSES_RIGHT; ASSUME `1 < p`;
                 ARITH_RULE `1 < p ==> 0 < p /\ 0 <= p`] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `~(ap = &0) ==> s = &0 ==> ~(s + ap = &0)`)) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        BINOP_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
        MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
        (CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC];
    SUBGOAL_THEN `variation(0..n) b = variation {0,1} b + variation(1..n) b`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..1) b + variation(1..n) b` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN REWRITE_TAC[IN_NUMSEG] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `1`) THEN
        SIMP_TAC[SUM_CLAUSES_NUMSEG; num_CONV `1`] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
        ARITH_TAC];
      SUBGOAL_THEN `(b:num->real) 1 = a 0 + a 1` ASSUME_TAC THENL
       [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
        SIMP_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC]]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `0`)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  ASM_SIMP_TAC[VARIATION_3; ARITH; OPPOSITE_SIGNS] THEN COND_CASES_TAC THEN
  REWRITE_TAC[VARIATION_2; OPPOSITE_SIGNS; REAL_LT_REFL] THEN
  EXPAND_TAC "a'" THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < p ==> ~(p = 1)`; REAL_LT_REFL] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(BINDER_CONV(RAND_CONV(RAND_CONV INT_POLY_CONV))) THEN
  REWRITE_TAC[INT_ARITH `x:int = y + --z <=> x + z = y`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_REWRITE_TAC[UNWIND_THM2] THEN
  ASM_REWRITE_TAC[ODD_ADD; ARITH_ODD; ARITH_EVEN] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Relate even-ness or oddity of variation to signs of end coefficients.     *)
(* ------------------------------------------------------------------------- *)

let VARIATION_OPPOSITE_ENDS = prove
 (`!a m n.
    m <= n /\ ~(a m = &0) /\ ~(a n = &0)
    ==> (ODD(variation(m..n) a) <=> a m * a n < &0)`,
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `n - m:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!i:num. m < i /\ i < n ==> a i = &0` THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `ODD(variation {m,n} a)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SUBSET THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG; IN_DIFF; EMPTY_SUBSET] THEN
      REWRITE_TAC[LE_REFL; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[VARIATION_2] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[ARITH]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(fun th ->
        MP_TAC(SPECL [`n:num`; `p:num`] th) THEN
        MP_TAC(SPECL [`p:num`; `m:num`] th)) THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ODD(variation(m..p) a + variation(p..n) a)` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN
      ASM_SIMP_TAC[LT_IMP_LE; IN_NUMSEG];
      ASM_REWRITE_TAC[ODD_ADD; OPPOSITE_SIGNS] THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial with odd variation has at least one positive root.             *)
(* This is the only "analytical" part of the proof.                          *)
(* ------------------------------------------------------------------------- *)

let REAL_POLYFUN_SGN_AT_INFINITY = prove
 (`!a n. ~(a n = &0)
         ==> ?B. &0 < B /\
                 !x. B <= abs x
                     ==> real_sgn(sum(0..n) (\i. a i * x pow i)) =
                         real_sgn(a n * x pow n)`,
  let lemma = prove
   (`abs(x) < abs(y) ==> real_sgn(x + y) = real_sgn y`,
    REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; SUM_SING_NUMSEG];
    ALL_TAC] THEN
  ABBREV_TAC `B = sum (0..n-1) (\i. abs(a i)) / abs(a n)` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS; SUM_POS_LE_NUMSEG];
    ALL_TAC] THEN
  EXISTS_TAC `&1 + B` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; LE_1] THEN MATCH_MP_TAC lemma THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum(0..n-1) (\i. abs(a i)) * abs x pow (n - 1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_ABS_LE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(x:real) pow n = x * x pow (n - 1)` SUBST1_TAC THENL
     [SIMP_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; GSYM REAL_ABS_NZ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]]]);;

let REAL_POLYFUN_HAS_POSITIVE_ROOT = prove
 (`!a n. a 0 < &0 /\ &0 < a n
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x. &0 < x /\ &0 <= sum(0..n) (\i. a i * x pow i)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:num->real`; `n:num`] REAL_POLYFUN_SGN_AT_INFINITY) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:real`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `real_sgn(a n * x pow n) = &1` SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_SGN_EQ; REAL_LT_MUL; REAL_POW_LT; real_gt] THEN
    REWRITE_TAC[REAL_LT_IMP_LE];
    MP_TAC(ISPECL [`\x. sum(0..n) (\i. a i * x pow i)`;
                   `&0`; `x:real`; `&0`] REAL_IVT_INCREASING) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_REAL_INTERVAL;
                 REAL_POW_ZERO; COND_RAND] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG; LE_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real` THEN
      SIMP_TAC[REAL_LT_LE] THEN ASM_CASES_TAC `y:real = &0` THEN
      ASM_SIMP_TAC[REAL_POW_ZERO; COND_RAND; REAL_MUL_RZERO; REAL_MUL_RID] THEN
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN ASM_REAL_ARITH_TAC]]);;

let ODD_VARIATION_POSITIVE_ROOT = prove
 (`!a n. ODD(variation(0..n) a)
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?M. !i. i IN 0..n /\ ~(a i = &0) ==> i <= M` MP_TAC THENL
   [EXISTS_TAC `n:num` THEN SIMP_TAC[IN_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `?i. i IN 0..n /\ ~(a i = &0)` MP_TAC THENL
   [MATCH_MP_TAC(MESON[] `((!i. P i ==> Q i) ==> F) ==> ?i. P i /\ ~Q i`) THEN
    DISCH_TAC THEN SUBGOAL_THEN `variation (0..n) a = variation {0} a`
     (fun th -> SUBST_ALL_TAC th THEN ASM_MESON_TAC[VARIATION_1; ODD]) THEN
    MATCH_MP_TAC VARIATION_SUBSET THEN
    ASM_SIMP_TAC[IN_DIFF] THEN REWRITE_TAC[IN_NUMSEG; SING_SUBSET; LE_0];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> a ==> a /\ b ==> c`] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN REWRITE_TAC[num_MAX] THEN
  REWRITE_TAC[TAUT `p ==> ~(q /\ r) <=> p /\ q ==> ~r`; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p /\ ~r ==> q`] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p:num <= q` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:num->real) p * a q < &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM VARIATION_OPPOSITE_ENDS] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `ODD p ==> p = q ==> ODD q`)) THEN
    MATCH_MP_TAC VARIATION_SUBSET THEN
    REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; IN_DIFF; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC] THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i. (a:num->real)(p + i) / a q`; `q - p:num`]
        REAL_POLYFUN_HAS_POSITIVE_ROOT) THEN
  ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `p:num <= q ==> p + q - p = q`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_div; OPPOSITE_SIGNS; REAL_MUL_POS_LT] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPPOSITE_SIGNS]) THEN
    REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`; GSYM REAL_INV_NEG] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_RING
   `!a. y = a * x ==> x = &0 ==> y = &0`) THEN
  EXISTS_TAC `(a:num->real) q * x pow p` THEN
  REWRITE_TAC[GSYM SUM_LMUL; REAL_ARITH
   `(aq * xp) * api / aq * xi:real = (aq / aq) * api * (xp * xi)`] THEN
  ASM_CASES_TAC `(a:num->real) q = &0` THENL
   [ASM_MESON_TAC[REAL_MUL_LZERO; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_ADD; REAL_DIV_REFL; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MP_TAC(SPEC `p:num` SUM_OFFSET) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; IN_DIFF; DE_MORGAN_THM] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(* Define root multiplicities.                                               *)
(* ------------------------------------------------------------------------- *)

let multiplicity = new_definition
 `multiplicity f r =
        @k. ?a n. ~(sum(0..n) (\i. a i * r pow i) = &0) /\
                  !x. f(x) = (x - r) pow k * sum(0..n) (\i. a i * x pow i)`;;

let MULTIPLICITY_UNIQUE = prove
 (`!f a r b m k.
        (!x. f(x) = (x - r) pow k * sum(0..m) (\j. b j * x pow j)) /\
        ~(sum(0..m) (\j. b j * r pow j) = &0)
        ==> k = multiplicity f r`,
  let lemma = prove
   (`!i j f g. f real_continuous_on (:real) /\ g real_continuous_on (:real) /\
               ~(f r = &0) /\ ~(g r = &0)
               ==> (!x. (x - r) pow i * f(x) = (x - r) pow j * g(x))
                   ==> j = i`,
    MATCH_MP_TAC WLOG_LT THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MP_TAC(ISPECL [`atreal r`; `f:real->real`;
                   `(f:real->real) r`; `&0`]
          REALLIM_UNIQUE) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_ATREAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
      ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV;
                    IN_UNIV];
      MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC `\x:real. (x - r) pow (j - i) * g x` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01; REAL_ARITH `&0 < abs(x - r) <=> ~(x = r)`] THEN
        X_GEN_TAC `x:real` THEN STRIP_TAC THEN MATCH_MP_TAC(REAL_RING
         `!a. a * x = a * y /\ ~(a = &0) ==> x = y`) THEN
        EXISTS_TAC `(x - r:real) pow i` THEN
        ASM_REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD; REAL_POW_EQ_0] THEN
        ASM_SIMP_TAC[REAL_SUB_0; ARITH_RULE `i:num < j ==> i + j - i = j`];
        SUBST1_TAC(REAL_ARITH `&0 = &0 * (g:real->real) r`) THEN
        MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_NULL_POW THEN
          REWRITE_TAC[GSYM REALLIM_NULL; REALLIM_ATREAL_ID] THEN ASM_ARITH_TAC;
          REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
          ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT;
                        REAL_OPEN_UNIV; IN_UNIV]]]]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[multiplicity] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THEN ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`b:num->real`; `m:num`] THEN ASM_REWRITE_TAC[]]);;

let MULTIPLICITY_WORKS = prove
 (`!r n a. 
    (?i. i IN 0..n /\ ~(a i = &0))
    ==> ?b m. 
        ~(sum(0..m) (\i. b i * r pow i) = &0) /\
        !x. sum(0..n) (\i. a i * x pow i) =                    
            (x - r) pow multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r *
            sum(0..m) (\i. b i * x pow i)`,
  REWRITE_TAC[multiplicity] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN  
  DISCH_TAC THEN X_GEN_TAC `a:num->real` THEN
  ASM_CASES_TAC `(a:num->real) n = &0` THENL
   [ASM_CASES_TAC `n = 0` THEN     
    ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2]
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a:num->real`) THEN
    ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; LE_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` MP_TAC) THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:num = n` THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `sum(0..n) (\i. a i * r pow i) = &0` THENL
   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_TAC `sum (0..n) (\i. a i * r pow i) = &0` THEN
      ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2; SUM_SING] THEN
      REWRITE_TAC[real_pow; REAL_MUL_RID] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(GEN `x:real` (ISPECL [`a:num->real`; `x:real`; `r:real`; `n:num`] 
        REAL_SUB_POLYFUN)) THEN ASM_SIMP_TAC[LE_1; REAL_SUB_RZERO] THEN
    ABBREV_TAC `b j = sum (j + 1..n) (\i. a i * r pow (i - j - 1))` THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `b:num->real`) THEN ANTS_TAC THENL
     [EXISTS_TAC `n - 1` THEN REWRITE_TAC[IN_NUMSEG; LE_REFL; LE_0] THEN
      EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[SUB_ADD; LE_1; SUM_SING_NUMSEG; real_pow; REAL_MUL_RID;
                   ARITH_RULE `n - (n - 1) - 1 = 0`];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (fun th ->
        EXISTS_TAC `SUC k` THEN MP_TAC th)) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC];
    MAP_EVERY EXISTS_TAC [`0`; `a:num->real`; `n:num`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LID]]);;
  
let MULTIPLICITY_OTHER_ROOT = prove
 (`!a n r s.
    ~(r = s) /\ (?i. i IN 0..n /\ ~(a i = &0))
     ==> multiplicity (\x. (x - r) pow m * sum(0..n) (\i. a i * x pow i)) s =
         multiplicity (\x.  sum(0..n) (\i. a i * x pow i)) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_UNIQUE THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real`; `n:num`; `a:num->real`] 
        MULTIPLICITY_WORKS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`; `p:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN
   `?b q. !x. sum(0..q) (\j. b j * x pow j) =
              (x - r) pow m * sum (0..p) (\i. c i * x pow i)`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_RING `r * x = s * r * y <=> r = &0 \/ s * y = x`] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_0]] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`c:num->real`; `p:num`; `m:num`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [MAP_EVERY EXISTS_TAC [`c:num->real`; `p:num`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `c:num->real`]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real`; `n:num`] THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
  EXISTS_TAC `\i. (if 0 < i then a(i - 1) else &0) - 
                  (if i <= n then r * a i else &0)` THEN
  EXISTS_TAC `n + 1` THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG] THEN X_GEN_TAC `x:real` THEN
  BINOP_TAC THENL
   [MP_TAC(ARITH_RULE `0 <= n + 1`) THEN SIMP_TAC[SUM_CLAUSES_LEFT] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[SUM_OFFSET; LT_REFL] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; ARITH_RULE `0 < i + 1`] THEN
    REWRITE_TAC[GSYM SUM_LMUL; ADD_SUB; REAL_POW_ADD; REAL_POW_1];
    SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; ARITH_RULE `0 < n + 1`] THEN
    REWRITE_TAC[ADD_SUB; ARITH_RULE `~(n + 1 <= n)`] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_RID; GSYM SUM_LMUL]] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* The main lemmas to be applied iteratively.                                *)
(* ------------------------------------------------------------------------- *)

let VARIATION_POSITIVE_ROOT_FACTOR = prove
 (`!a n r.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b. ~(b(n - 1) = &0) /\
            (!x. sum(0..n) (\i. a i * x pow i) =
                 (x - r) * sum(0..n-1) (\i. b i * x pow i)) /\
            ?d. ODD d /\ variation(0..n) a = variation(0..n-1) b + d`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; real_pow; REAL_MUL_RID] THEN MESON_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `b = \j. sum (j + 1..n) (\i. a i * r pow (i - j - 1))` THEN
  EXISTS_TAC `b:num->real` THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
    ASM_SIMP_TAC[SUM_SING_NUMSEG; ARITH_RULE `n - (n - 1) - 1 = 0`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_RID];
    MP_TAC(GEN `x:real` (SPECL [`a:num->real`; `x:real`; `r:real`; `n:num`]
        REAL_SUB_POLYFUN)) THEN
    ASM_SIMP_TAC[LE_1; REAL_SUB_RZERO] THEN DISCH_THEN(K ALL_TAC) THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:num->real) n = &0` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`n:num`; `\i. if i <= n then a i * (r:real) pow i else &0`;
    `\i. if i <= n then --b i * (r:real) pow (i + 1) else &0`]
   ARTHAN_LEMMA) THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_LT_IMP_NZ; REAL_NEG_0;
               LE_REFL] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `j:num <= n` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `!i:num. i <= j ==> i <= n` MP_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC)] THEN
      REWRITE_TAC[REAL_ARITH `a:real = --b * c <=> a + b * c = &0`] THEN
      REWRITE_TAC[GSYM SUM_RMUL; GSYM REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
      SIMP_TAC[ARITH_RULE `j + 1 <= k ==> k - j - 1 + j + 1 = k`] THEN
      ASM_SIMP_TAC[SUM_COMBINE_R; LE_0];
      REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
      ASM_SIMP_TAC[ARITH_RULE
      `~(j <= n) ==> ((0 <= i /\ i <= j) /\ i <= n <=> 0 <= i /\ i <= n)`] THEN
      ASM_REWRITE_TAC[GSYM numseg]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE
     `x':num = x /\ y' = y ==> x' = y' + d ==> x = y + d`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n) (\i. a i * r pow i)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_EQ THEN SIMP_TAC[IN_NUMSEG];
        ALL_TAC];
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n) (\i. --b i * r pow (i + 1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_EQ THEN SIMP_TAC[IN_NUMSEG];
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n-1) (\i. --b i * r pow (i + 1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET_NUMSEG; IN_DIFF; IN_NUMSEG] THEN
        CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `i:num` THEN STRIP_TAC] THEN
        SUBGOAL_THEN `i:num = n` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        ALL_TAC]] THEN
    REWRITE_TAC[variation] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
      `(a * x) * (b * x'):real = (x * x') * a * b`] THEN
    SIMP_TAC[NOT_IMP; GSYM CONJ_ASSOC; GSYM REAL_POW_ADD;
             REAL_ARITH `--x * --y:real = x * y`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_POW_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_RNEG; REAL_ENTIRE; REAL_NEG_EQ_0; REAL_POW_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ]]);;

let VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR = prove
 (`!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b k m. 0 < k /\ m < n /\ ~(b m = &0) /\
                (!x. sum(0..n) (\i. a i * x pow i) =
                     (x - r) pow k * sum(0..m) (\i. b i * x pow i)) /\
                ~(sum(0..m) (\j. b j * r pow j) = &0) /\
                ?d. EVEN d /\ variation(0..n) a = variation(0..m) b + k + d`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `a:num->real` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; real_pow; REAL_MUL_RID] THEN MESON_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`a:num->real`; `n:num`; `r:real`]
        VARIATION_POSITIVE_ROOT_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:num->real` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `sum(0..n-1) (\i. c i * r pow i) = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `c:num->real`)] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real` THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_ASSOC] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[ADD1; ADD_ASSOC] THEN EXISTS_TAC `d - 1 + e`;
    MAP_EVERY EXISTS_TAC [`c:num->real`; `1`; `n - 1`] THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    EXISTS_TAC `d - 1`] THEN
  UNDISCH_TAC `ODD d` THEN GEN_REWRITE_TAC LAND_CONV [ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[SUC_SUB1; EVEN_ADD; EVEN_MULT; ARITH] THEN ARITH_TAC);;

let VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR = prove
 (`!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b m. m < n /\ ~(b m = &0) /\
              (!x. sum(0..n) (\i. a i * x pow i) =
                   (x - r) pow
                   (multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r) *
                   sum(0..m) (\i. b i * x pow i)) /\
              ~(sum(0..m) (\j. b j * r pow j) = &0) /\
              ?d. EVEN d /\
                  variation(0..n) a = variation(0..m) b +
                     multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r + d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r = k`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`b:num->real`; `m:num`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence the main theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let DESCARTES_RULE_OF_SIGNS = prove
 (`!f a n. f = (\x. sum(0..n) (\i. a i * x pow i)) /\ 
           (?i. i IN 0..n /\ ~(a i = &0))
           ==> ?d. EVEN d /\
                   variation(0..n) a = 
                   nsum {r | &0 < r /\ f(r) = &0} (\r. multiplicity f r) + d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`a:num->real`; `n:num`] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `a:num->real` THEN ASM_CASES_TAC `(a:num->real) n = &0` THENL
   [ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2]
    THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL 
     [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `a:num->real`)] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[IN_NUMSEG; ARITH_RULE `i <= n ==> i <= n - 1 \/ i = n`];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
      ASM_SIMP_TAC[LE_0; LE_1; SUM_CLAUSES_RIGHT] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      MATCH_MP_TAC VARIATION_SUBSET THEN
      REWRITE_TAC[SUBSET_NUMSEG; IN_DIFF; IN_NUMSEG] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; X_GEN_TAC `i:num` THEN STRIP_TAC] THEN
      SUBGOAL_THEN `i:num = n` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    DISCH_THEN(K ALL_TAC)] THEN
  ASM_CASES_TAC `{r | &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0} = {}` THENL
   [ASM_REWRITE_TAC[NSUM_CLAUSES; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM1] THEN
    ONCE_REWRITE_TAC[GSYM NOT_ODD] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ODD_VARIATION_POSITIVE_ROOT) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real`; `n:num`; `a:num->real`] 
    VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:num->real`; `m:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN 
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `b:num->real`) THEN ANTS_TAC THENL
   [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL; LE_0];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:num` 
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d2:num`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  EXISTS_TAC `d1 + d2:num` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[EVEN_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE
   `x + y = z ==> (x + d1) + (y + d2):num = z + d1 + d2`) THEN
  SUBGOAL_THEN
   `{r | &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0} = 
    r INSERT {r | &0 < r /\ sum(0..m) (\i. b i * r pow i) = &0}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `x IN s /\ s DELETE x = t ==> s = x INSERT t`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_0] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN
      X_GEN_TAC `s:real` THEN
      FIRST_X_ASSUM(K ALL_TAC o SPEC_VAR) THEN
      ASM_CASES_TAC `s:real = r` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {r | &0 < r /\ sum(0..m) (\i. b i * r pow i) = &0}`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r | sum(0..m) (\i. b i * r pow i) = &0}` THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_POLYFUN_FINITE_ROOTS] THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL];
    SIMP_TAC[NSUM_CLAUSES; IN_ELIM_THM] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `s1:num = s2 ==> s1 + m = m + s2`) THEN
  MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun t -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [t]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_OTHER_ROOT THEN
  REWRITE_TAC[MESON[] `(?i. P i /\ Q i) <=> ~(!i. P i ==> ~Q i)`] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~(sum (0..m) (\j. b j * r pow j) = &0)` THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LZERO; SUM_0]);;
