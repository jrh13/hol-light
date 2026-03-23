(* ========================================================================= *)
(* Random variables: definitions, measurability, and probability             *)
(* infrastructure (indexed families, Boole's inequality, continuity).        *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapter 3.                *)
(* ========================================================================= *)

needs "Probability/measure.ml";;

(* ------------------------------------------------------------------------- *)
(* Chapter 3: Random Variables                                               *)
(* ------------------------------------------------------------------------- *)

let random_variable = new_definition
  `random_variable (p:(A)prob_space) (X:A->real) <=>
   (!a. {x | x IN prob_carrier p /\ X x <= a} IN prob_events p)`;;

let RANDOM_VARIABLE_CONST = prove
  (`!p:A prob_space c. random_variable p (\x. c)`,
   REPEAT GEN_TAC THEN REWRITE_TAC[random_variable] THEN
   TRY BETA_TAC THEN
   X_GEN_TAC `a:real` THEN
   ASM_CASES_TAC `c:real <= a` THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ c:real <= a} = prob_carrier p`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
     REWRITE_TAC[PROB_CARRIER_IN_EVENTS]];
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ c:real <= a} = {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
     ASM_MESON_TAC[];
     REWRITE_TAC[PROB_EMPTY_IN_EVENTS]]]);;


(* ------------------------------------------------------------------------- *)
(* Indicator functions                                                       *)
(* ------------------------------------------------------------------------- *)

let indicator_fn = new_definition
  `indicator_fn (a:A->bool) (x:A) = if x IN a then &1 else &0`;;


(* ------------------------------------------------------------------------- *)
(* Random variable properties                                                *)
(* ------------------------------------------------------------------------- *)

let RANDOM_VARIABLE_NEG = prove
  (`!p:A prob_space X.
      random_variable p X ==> random_variable p (\x. --(X x))`,
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   REWRITE_TAC[random_variable] THEN
   TRY BETA_TAC THEN DISCH_TAC THEN
   X_GEN_TAC `a:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ --X x <= a} =
      prob_carrier p DIFF
        UNIONS (IMAGE (\n. {x | x IN prob_carrier p /\ X x <= --a - inv(&n + &1)})
                      (:num))`
     SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `y:A` THEN
    REWRITE_TAC[IN_DIFF; UNIONS_IMAGE; IN_UNIV] THEN
    TRY BETA_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `(y:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LE] THEN
    EQ_TAC THENL
    [DISCH_TAC THEN X_GEN_TAC `n:num` THEN
     MATCH_MP_TAC(REAL_ARITH `--x <= a /\ &0 < e ==> --a - e < x`) THEN
     CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC];
     DISCH_TAC THEN
     REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     SUBGOAL_THEN `&0 < --a - (X:A->real) y` MP_TAC THENL
     [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
     DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN `?j:num. k = SUC j` (X_CHOOSE_TAC `j:num`) THENL
     [EXISTS_TAC `k - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `inv(&j + &1) < --a - (X:A->real) y` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_OF_NUM_SUC]; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
     POP_ASSUM MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `n:num` THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    FIRST_X_ASSUM MATCH_ACCEPT_TAC;
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]]);;

let RANDOM_VARIABLE_SCALE = prove
  (`!p:A prob_space X c.
      random_variable p X /\ &0 < c
      ==> random_variable p (\x. c * X x)`,
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
   REWRITE_TAC[random_variable] THEN
   TRY BETA_TAC THEN DISCH_TAC THEN
   X_GEN_TAC `a:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ c * X x <= a} =
      {x | x IN prob_carrier p /\ X x <= a / c}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ];
    FIRST_X_ASSUM MATCH_ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Indexed families of events (using num->event)                             *)
(* ------------------------------------------------------------------------- *)

let PROB_INDEXED_UNION_IN_EVENTS = prove
  (`!p:A prob_space A.
      (!n:num. A n IN prob_events p)
      ==> UNIONS {A n | n IN (:num)} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]]);;

let PROB_INDEXED_INTER_IN_EVENTS = prove
  (`!p:A prob_space A.
      (!n:num. A n IN prob_events p)
      ==> INTERS {A n | n IN (:num)} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV] THEN
    MESON_TAC[]]);;

let PROB_FINITE_INDEXED_UNION_IN_EVENTS = prove
  (`!p:A prob_space (A:num->A->bool) n.
      (!i. i <= n ==> A i IN prob_events p)
      ==> UNIONS (IMAGE A (0..n)) IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG]) THEN
    ARITH_TAC;
    MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG]]);;


(* ------------------------------------------------------------------------- *)
(* Boole's inequality (finite subadditivity for indexed families)            *)
(* ------------------------------------------------------------------------- *)

let PROB_FINITE_SUBADDITIVE = prove
  (`!p:A prob_space (A:num->A->bool) n.
      (!i. i <= n ==> A i IN prob_events p)
      ==> prob p (UNIONS (IMAGE A (0..n))) <= sum (0..n) (\i. prob p (A i))`,
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0] THEN
    REWRITE_TAC[SUM_SING; UNION_EMPTY] THEN
    TRY BETA_TAC THEN
    DISCH_TAC THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC n`] THEN
    REWRITE_TAC[NUMSEG_CLAUSES; ARITH_RULE `0 <= SUC n`] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN
    TRY BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob p (A (SUC n):A->bool) +
                prob p (UNIONS (IMAGE (A:num->A->bool) (0..n)))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_SUBADDITIVE THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
      CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
       REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
       MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG]]];
     MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a + b <= c + a`) THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;


(* ------------------------------------------------------------------------- *)
(* Monotonicity helpers for increasing sequences                             *)
(* ------------------------------------------------------------------------- *)

let INCREASING_MONO = prove
  (`!(A:num->A->bool) m n.
      (!k. A k SUBSET A (SUC k)) /\ m <= n ==> A m SUBSET A n`,
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[LE; SUBSET_REFL];
    STRIP_TAC THEN ASM_CASES_TAC `m = SUC n` THENL
    [ASM_REWRITE_TAC[SUBSET_REFL];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(A:num->A->bool) n` THEN
     CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
      ASM_MESON_TAC[]]]]);;

let INCREASING_UNION_DECOMP = prove
  (`!(A:num->A->bool).
      (!n. A n SUBSET A (SUC n))
      ==> UNIONS {A n | n IN (:num)} =
          A 0 UNION UNIONS {A (SUC n) DIFF A n | n IN (:num)}`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[EXTENSION; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THENL
    [DISCH_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
     DISCH_TAC THEN ASM_CASES_TAC `(x:A) IN A (n:num)` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(DISJ_CASES_TAC) THENL
    [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
     FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` MP_TAC) THEN
     REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
     EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[]]]);;

let INCREASING_A0_DISJOINT_DIFFS = prove
  (`!(A:num->A->bool).
      (!n. A n SUBSET A (SUC n))
      ==> DISJOINT (A 0) (UNIONS {A (SUC n) DIFF A n | n IN (:num)})`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
               UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_DIFF] THEN
   X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN A 0` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN
   X_GEN_TAC `n:num` THEN DISJ2_TAC THEN
   SUBGOAL_THEN `(A:num->A->bool) 0 SUBSET A n` ASSUME_TAC THENL
   [MATCH_MP_TAC INCREASING_MONO THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LE_0]];
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Continuity of probability from below                                      *)
(* If A_0 SUBSET A_1 SUBSET ... and A = UNIONS A_n, then P(A_n) --> P(A)     *)
(* Uses ---> and sequentially from the library                               *)
(* ------------------------------------------------------------------------- *)

let PROB_CONTINUITY_FROM_BELOW = prove
  (`!p:A prob_space A.
      (!n. A n IN prob_events p) /\
      (!n. A n SUBSET A (SUC n))
      ==> ((\n. prob p (A n)) --->
           prob p (UNIONS {A n | n IN (:num)})) sequentially`,
   REPEAT STRIP_TAC THEN
   ABBREV_TAC `B = \n:num. A(SUC n) DIFF (A:num->A->bool) n` THEN
   SUBGOAL_THEN `!n:num. (B:num->A->bool) n IN prob_events (p:A prob_space)`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!i j. ~(i = j) ==> DISJOINT ((B:num->A->bool) i) (B j)`
     ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `i:num < j` THENL
    [SUBGOAL_THEN `(A:num->A->bool) (SUC i) SUBSET A j` MP_TAC THENL
     [MATCH_MP_TAC INCREASING_MONO THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
     SUBGOAL_THEN `(A:num->A->bool) (SUC j) SUBSET A i` MP_TAC THENL
     [MATCH_MP_TAC INCREASING_MONO THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `UNIONS {(B:num->A->bool) n | n IN (:num)} IN
                  prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space) (UNIONS {(A:num->A->bool) n | n IN (:num)}) =
      prob p (A 0) + prob p (UNIONS {(B:num->A->bool) n | n IN (:num)})`
     ASSUME_TAC THENL
   [SUBGOAL_THEN `UNIONS {(A:num->A->bool) n | n IN (:num)} =
                   A 0 UNION UNIONS {(B:num->A->bool) n | n IN (:num)}`
     SUBST1_TAC THENL
    [EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
     MATCH_MP_TAC INCREASING_UNION_DECOMP THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC PROB_ADDITIVE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INCREASING_A0_DISJOINT_DIFFS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!N. sum (0..N) (\n. prob (p:A prob_space) ((B:num->A->bool) n)) =
          prob p ((A:num->A->bool) (SUC N)) - prob p (A 0)`
     ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `!n. prob (p:A prob_space) ((B:num->A->bool) n) =
                        prob p ((A:num->A->bool) (SUC n)) - prob p (A n)`
      (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
     MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[ADD1; SUM_DIFFS_ALT; LE_0]];
    ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`]
     PROB_COUNTABLY_ADDITIVE) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[real_sums; FROM_0; INTER_UNIV; REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
   EXISTS_TAC `SUC N0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?m:num. n = SUC m /\ N0 <= m`
     (CHOOSE_THEN STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
   REWRITE_TAC[REAL_ARITH `x - a - b = x - (a + b):real`] THEN
   ASM_REWRITE_TAC[]);;

let PROB_CONTINUITY_FROM_ABOVE = prove
  (`!p:A prob_space A.
      (!n. A n IN prob_events p) /\
      (!n. A (SUC n) SUBSET A n)
      ==> ((\n. prob p (A n)) --->
           prob p (INTERS {A n | n IN (:num)})) sequentially`,
   REPEAT STRIP_TAC THEN
   ABBREV_TAC `C = \n:num. (A:num->A->bool) 0 DIFF A n` THEN
   SUBGOAL_THEN `!n:num. (A:num->A->bool) n SUBSET A 0` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN
    ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
   SUBGOAL_THEN `!n. (C:num->A->bool) n IN prob_events (p:A prob_space)`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!n. (C:num->A->bool) n SUBSET C(SUC n)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `INTERS {(A:num->A->bool) n | n IN (:num)} SUBSET A 0`
     ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM; IN_UNIV] THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(A:num->A->bool) 0`) THEN
    ANTS_TAC THENL [EXISTS_TAC `0` THEN REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `INTERS {(A:num->A->bool) n | n IN (:num)} IN
                  prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!n. prob (p:A prob_space) ((C:num->A->bool) n) =
                       prob p ((A:num->A->bool) 0) - prob p (A n)`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space) (UNIONS {(C:num->A->bool) n | n IN (:num)}) =
      prob p ((A:num->A->bool) 0) -
      prob p (INTERS {A n | n IN (:num)})`
     ASSUME_TAC THENL
   [SUBGOAL_THEN
      `UNIONS {(C:num->A->bool) n | n IN (:num)} =
       (A:num->A->bool) 0 DIFF INTERS {A n | n IN (:num)}`
      SUBST1_TAC THENL
    [EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
     REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:A` THEN
     REWRITE_TAC[IN_UNIONS; IN_DIFF; IN_INTERS;
                  IN_ELIM_THM; IN_UNIV] THEN
     EQ_TAC THENL
     [(* Forward *)
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool`
        (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `m:num` ASSUME_TAC) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[NOT_FORALL_THM] THEN
      EXISTS_TAC `(A:num->A->bool) m` THEN
      REWRITE_TAC[NOT_IMP] THEN
      CONJ_TAC THENL
      [EXISTS_TAC `m:num` THEN REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      (* Backward *)
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
      REWRITE_TAC[NOT_IMP] THEN
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool`
        (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `m:num` ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM(fun th -> SUBST_ALL_TAC th) THEN
      EXISTS_TAC `(A:num->A->bool) 0 DIFF A m` THEN
      CONJ_TAC THENL
      [EXISTS_TAC `m:num` THEN REWRITE_TAC[];
       REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[]]];
     MATCH_MP_TAC PROB_DIFF_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `C:num->A->bool`]
     PROB_CONTINUITY_FROM_BELOW) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   EXISTS_TAC `N:num` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   ASM_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[REAL_ARITH `(a - x) - (a - y):real = --(x - y)`;
                    REAL_ABS_NEG]);;

