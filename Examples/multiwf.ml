(* ========================================================================= *)
(* Part 1: Background theories.                                              *)
(* ========================================================================= *)

let EMPTY_IS_FINITE = prove
 (`!s. (s = EMPTY) ==> FINITE s`,
  SIMP_TAC[FINITE_RULES]);;

let SING_IS_FINITE = prove
 (`!s a. (s = {a}) ==> FINITE s`,
  SIMP_TAC[FINITE_INSERT; FINITE_RULES]);;

let UNION_NONZERO = prove
 (`{a | ~(f a + g a = 0)} = {a | ~(f a = 0)} UNION {a | ~(g a = 0)}`,
  REWRITE_TAC[ADD_EQ_0; EXTENSION; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM]);;

(* ------------------------------------------------------------------------- *)
(* Definition of type of finite multisets with a few basic operations.       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("mmember",(11,"right"));;
parse_as_infix("munion",(16,"right"));;
parse_as_infix("mdiff",(18,"left"));;

let multiset_tybij_th = prove
 (`?f. FINITE {a:A | ~(f a = 0)}`,
  EXISTS_TAC `\a:A. 0` THEN
  SIMP_TAC[EMPTY_IS_FINITE; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]);;

let multiset_tybij = new_type_definition
  "multiset" ("multiset","multiplicity") multiset_tybij_th;;

let mempty = new_definition
  `mempty = multiset (\b. 0)`;;

let mmember = new_definition
  `a mmember M <=> ~(multiplicity M a = 0)`;;

let msing = new_definition
  `msing a = multiset (\b. if b = a then 1 else 0)`;;

let munion = new_definition
  `M munion N = multiset(\b. multiplicity M b + multiplicity N b)`;;

let mdiff = new_definition
  `M mdiff N = multiset(\b. multiplicity M b - multiplicity N b)`;;

(* ------------------------------------------------------------------------- *)
(* Extensionality for multisets.                                             *)
(* ------------------------------------------------------------------------- *)

let MEXTENSION = prove
 (`(M = N) = !a. multiplicity M a = multiplicity N a`,
  REWRITE_TAC[GSYM FUN_EQ_THM] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  MESON_TAC[multiset_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties of multisets.                                            *)
(* ------------------------------------------------------------------------- *)

let MULTIPLICITY_MULTISET = prove
 (`FINITE {a | ~(f a = 0)} /\ (f a = y) ==> (multiplicity(multiset f) a = y)`,
  SIMP_TAC[multiset_tybij]);;

let MEMPTY = prove
 (`multiplicity mempty a = 0`,
  REWRITE_TAC[mempty] THEN MATCH_MP_TAC MULTIPLICITY_MULTISET THEN
  SIMP_TAC[EMPTY_IS_FINITE; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]);;

let MSING = prove
 (`multiplicity (msing (a:A)) b = if b = a then 1 else 0`,
  REWRITE_TAC[msing] THEN MATCH_MP_TAC MULTIPLICITY_MULTISET THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SING_IS_FINITE THEN EXISTS_TAC `a:A` THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ]);;

let MUNION = prove
 (`multiplicity (M munion N) a = multiplicity M a + multiplicity N a`,
  REWRITE_TAC[munion] THEN MATCH_MP_TAC MULTIPLICITY_MULTISET THEN
  REWRITE_TAC[UNION_NONZERO; FINITE_UNION] THEN SIMP_TAC[multiset_tybij] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[multiset_tybij]);;

let MDIFF = prove
 (`multiplicity (M mdiff N) (a:A) = multiplicity M a - multiplicity N a`,
  REWRITE_TAC[mdiff] THEN MATCH_MP_TAC MULTIPLICITY_MULTISET THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{a:A | ~(multiplicity M a = 0)}` THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; multiset_tybij] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[multiset_tybij] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some trivial properties of multisets that we use later.                   *)
(* ------------------------------------------------------------------------- *)

let MUNION_MEMPTY = prove
 (`~(M munion (msing(a:A)) = mempty)`,
  REWRITE_TAC[MEXTENSION; MEMPTY; MSING; MUNION] THEN
  DISCH_THEN(MP_TAC o SPEC `a:A`) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ]);;

let MMEMBER_MUNION = prove
 (`x mmember (M munion N) <=> x mmember M \/ x mmember N`,
  REWRITE_TAC[mmember; MUNION; ADD_EQ_0; DE_MORGAN_THM]);;

let MMEMBER_MSING = prove
 (`x mmember (msing a) <=> (x = a)`,
  REWRITE_TAC[mmember; MSING] THEN COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ]);;

let MUNION_EMPTY = prove
 (`M munion mempty = M`,
  REWRITE_TAC[MEXTENSION; MUNION; MEMPTY; ADD_CLAUSES]);;

let MUNION_ASSOC = prove
 (`M1 munion (M2 munion M3) = (M1 munion M2) munion M3`,
  REWRITE_TAC[MEXTENSION; MUNION; ADD_ASSOC]);;

let MUNION_AC = prove
 (`(M1 munion M2 = M2 munion M1) /\
   ((M1 munion M2) munion M3 = M1 munion M2 munion M3) /\
   (M1 munion M2 munion M3 = M2 munion M1 munion M3)`,
  REWRITE_TAC[MEXTENSION; MUNION; ADD_AC]);;

let MUNION_11 = prove
 (`(M1 munion N = M2 munion N) <=> (M1 = M2)`,
  REWRITE_TAC[MEXTENSION; MUNION; EQ_ADD_RCANCEL]);;

let MUNION_INUNION = prove
 (`a mmember (M munion (msing b)) /\ ~(b = a) ==> a mmember M`,
  REWRITE_TAC[mmember; MUNION; MSING; ADD_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]);;

let MMEMBER_MDIFF = prove
 (`(a:A) mmember M ==> (M = (M mdiff (msing a)) munion (msing a))`,
  REWRITE_TAC[mmember; MEXTENSION; MUNION; MDIFF; MSING] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(multiplicity M (a:A) = 0)` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Induction principle for multisets.                                        *)
(* ------------------------------------------------------------------------- *)

let MULTISET_INDUCT_LEMMA1 = prove
 (`(!M. ({a | ~(multiplicity M a = 0)} SUBSET s) ==> P M) /\
   (!a:A M. P M ==> P (M munion (msing a)))
   ==> !n M. (multiplicity M a = n) /\
             {a:A | ~(multiplicity M a = 0)} SUBSET (a INSERT s)
             ==> P M`,
  STRIP_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `{a:A | ~(multiplicity M a = 0)} SUBSET (a INSERT s)` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `M = (M mdiff (msing(a:A))) munion (msing a)` SUBST1_TAC THENL
     [MATCH_MP_TAC MMEMBER_MDIFF THEN ASM_REWRITE_TAC[mmember; NOT_SUC];
      ALL_TAC] THEN
    MAP_EVERY (MATCH_MP_TAC o ASSUME)
     [`!a:A M. P M ==> P (M munion msing a)`;
      `!M. (multiplicity M a = n) /\
           {a:A | ~(multiplicity M a = 0)} SUBSET (a INSERT s)
           ==> P M`] THEN
    ASM_REWRITE_TAC[MDIFF; MSING; ARITH_RULE `SUC n - 1 = n`] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{a:A | ~(multiplicity M a = 0)}` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM; SUB_0]]);;

let MULTISET_INDUCT_LEMMA2 = prove
 (`P mempty /\
   (!a:A M. P M ==> P (M munion (msing a)))
   ==> !s. FINITE s ==> !M. {a:A | ~(multiplicity M a = 0)} SUBSET s ==> P M`,
  STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `M:(A)multiset = mempty` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[MEXTENSION; MEMPTY]; X_GEN_TAC `a:A`] THEN
  REPEAT STRIP_TAC THEN MP_TAC MULTISET_INDUCT_LEMMA1 THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM EXISTS_REFL]);;

let MULTISET_INDUCT = prove
 (`P mempty /\
   (!a:A M. P M ==> P (M munion (msing a)))
   ==> !M. P M`,
  DISCH_THEN(MP_TAC o MATCH_MP MULTISET_INDUCT_LEMMA2) THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP] THEN
  GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `{a:A | ~(multiplicity M a = 0)}` THEN
  REWRITE_TAC[SUBSET_REFL; multiset_tybij] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[multiset_tybij]);;

(* ========================================================================= *)
(* Part 2: Transcription of Tobias's paper.                                  *)
(* ========================================================================= *)

parse_as_infix("<<",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Wellfounded part of a relation.                                           *)
(* ------------------------------------------------------------------------- *)

let WFP_RULES,WFP_INDUCT,WFP_CASES = new_inductive_definition
  `!x. (!y. y << x ==> WFP(<<) y) ==> WFP(<<) x`;;

(* ------------------------------------------------------------------------- *)
(* Wellfounded part induction.                                               *)
(* ------------------------------------------------------------------------- *)

let WFP_PART_INDUCT = prove
 (`!P. (!x. x IN WFP(<<) /\ (!y. y << x ==> P(y)) ==> P(x))
       ==> !x:A. x IN WFP(<<) ==> P(x)`,
  GEN_TAC THEN REWRITE_TAC[IN] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b <=> a ==> a /\ b`] THEN
  MATCH_MP_TAC WFP_INDUCT THEN ASM_MESON_TAC[WFP_RULES]);;

(* ------------------------------------------------------------------------- *)
(* A relation is wellfounded iff WFP is the whole universe.                  *)
(* ------------------------------------------------------------------------- *)

let WFP_WF = prove
 (`WF(<<) <=> (WFP(<<) = UNIV:A->bool)`,
  EQ_TAC THENL
   [REWRITE_TAC[WF_IND; EXTENSION; IN; UNIV] THEN MESON_TAC[WFP_RULES];
    DISCH_TAC THEN MP_TAC WFP_PART_INDUCT THEN
    ASM_REWRITE_TAC[IN; UNIV; WF_IND]]);;

(* ------------------------------------------------------------------------- *)
(* This isn't needed for the result as such, but formalizes the last         *)
(* remarks in section 3 that the WFP is exactly those elements that cannot   *)
(* start infinite descending chains.                                         *)
(* ------------------------------------------------------------------------- *)

let WFP_DCHAIN = prove
 (`!(<<):A->A->bool.
        WFP(<<) = {a | !x. (!n. x(SUC n) << x n) ==> ~(x 0 = a)}`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[IN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WFP_INDUCT THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    X_GEN_TAC `x:num->A` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(x:num->A) (SUC 0)`) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(x:num->A) o SUC`) THEN
    ASM_REWRITE_TAC[o_THM];
    X_GEN_TAC `a:A` THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN MP_TAC(ISPECL
     [`\(n:num) (x:A). ~WFP(<<) x`; `\(n:num) x y. ((<<):A->A->bool) y x`;
      `a:A`] DEPENDENT_CHOICE_FIXED) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WFP_CASES] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The multiset order.                                                       *)
(* ------------------------------------------------------------------------- *)

let morder = new_definition
  `morder(<<) N M <=> ?M0 a K. (M = M0 munion (msing a)) /\
                               (N = M0 munion K) /\
                               (!b. b mmember K ==> b << a)`;;

(* ------------------------------------------------------------------------- *)
(* We separate off this part from the proof of LEMMA_2_1.                    *)
(* ------------------------------------------------------------------------- *)

let LEMMA_2_0 = prove
 (`morder(<<) N (M0 munion (msing a))
   ==> (?M. morder(<<) M M0 /\ (N = M munion (msing a))) \/
       (?K. (N = M0 munion K) /\ (!b:A. b mmember K ==> b << a))`,
  GEN_REWRITE_TAC LAND_CONV [morder] THEN
  DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN
   [`M1:(A)multiset`; `b:A`; `K:(A)multiset`]) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `b:A = a` THENL
   [DISJ2_TAC THEN UNDISCH_THEN `b:A = a` SUBST_ALL_TAC THEN
    EXISTS_TAC `K:(A)multiset` THEN ASM_MESON_TAC[MUNION_11]; DISJ1_TAC] THEN
  SUBGOAL_THEN `?M2. M1 = M2 munion (msing(a:A))` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `M1 mdiff (msing(a:A))` THEN
    MAP_EVERY MATCH_MP_TAC [MMEMBER_MDIFF; MUNION_INUNION] THEN
    UNDISCH_TAC `M0 munion (msing a) = M1 munion (msing(b:A))` THEN
    ASM_REWRITE_TAC[MEXTENSION; MUNION; MSING; mmember] THEN
    DISCH_THEN(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `M2 munion K:(A)multiset` THEN ASM_REWRITE_TAC[MUNION_AC] THEN
  REWRITE_TAC[morder] THEN
  MAP_EVERY EXISTS_TAC [`M2:(A)multiset`; `b:A`; `K:(A)multiset`] THEN
  UNDISCH_TAC `M0 munion msing (a:A) = M1 munion msing b` THEN
  ASM_REWRITE_TAC[MUNION_AC] THEN MESON_TAC[MUNION_AC; MUNION_11]);;

(* ------------------------------------------------------------------------- *)
(* The sequence of lemmas from Tobias's paper.                               *)
(* ------------------------------------------------------------------------- *)

let LEMMA_2_1 = prove
 (`(!M b:A. b << a /\ M IN WFP(morder(<<))
            ==> (M munion (msing b)) IN WFP(morder(<<))) /\
   M0 IN WFP(morder(<<)) /\
   (!M. morder(<<) M M0 ==> (M munion (msing a)) IN WFP(morder(<<)))
   ==> (M0 munion (msing a)) IN WFP(morder(<<))`,
  STRIP_TAC THEN REWRITE_TAC[IN] THEN MATCH_MP_TAC WFP_RULES THEN
  X_GEN_TAC `N:(A)multiset` THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP LEMMA_2_0) THENL
   [ASM_MESON_TAC[IN]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  SPEC_TAC(`N:(A)multiset`,`N:(A)multiset`) THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC MULTISET_INDUCT THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MUNION_ASSOC; MMEMBER_MUNION; MMEMBER_MSING]) THEN
  ASM_MESON_TAC[IN; MUNION_EMPTY]);;

let LEMMA_2_2 = prove
 (`(!M b. b << a /\ M IN WFP(morder(<<))
          ==> (M munion (msing b)) IN WFP(morder(<<)))
   ==> !M. M IN WFP(morder(<<)) ==> (M munion (msing a)) IN WFP(morder(<<))`,
  STRIP_TAC THEN MATCH_MP_TAC WFP_PART_INDUCT THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LEMMA_2_1 THEN ASM_REWRITE_TAC[]);;

let LEMMA_2_3 = prove
 (`WF(<<)
   ==> !a M. M IN WFP(morder(<<)) ==> (M munion (msing a)) IN WFP(morder(<<))`,
  REWRITE_TAC[WF_IND] THEN DISCH_THEN MATCH_MP_TAC THEN MESON_TAC[LEMMA_2_2]);;

let LEMMA_2_4 = prove
 (`WF(<<) ==> !M. M IN WFP(morder(<<))`,
  DISCH_TAC THEN MATCH_MP_TAC MULTISET_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[IN] THEN MATCH_MP_TAC WFP_RULES THEN
    REWRITE_TAC[morder; MUNION_MEMPTY];
    ASM_SIMP_TAC[LEMMA_2_3]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the final result.                                                   *)
(* ------------------------------------------------------------------------- *)

let MORDER_WF = prove
 (`WF(<<) ==> WF(morder(<<))`,
  SIMP_TAC[WFP_WF; EXTENSION; IN_UNIV; LEMMA_2_4]);;
