(* ========================================================================= *)
(* Inclusion-exclusion principle, the usual and generalized forms.           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Simple set theory lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let SUBSET_INSERT_EXISTS = prove
 (`!s x:A t. s SUBSET (x INSERT t) <=>
                s SUBSET t \/ ?u. u SUBSET t /\ s = x INSERT u`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(a /\ ~b ==> c) ==> a ==> b \/ c`) THEN
  DISCH_TAC THEN EXISTS_TAC `s DELETE (x:A)` THEN ASM SET_TAC[]);;

let FINITE_SUBSETS_RESTRICT = prove
 (`!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Versions for additive real functions, where the additivity applies only   *)
(* to some specific subsets (e.g. cardinality of finite sets, measurable     *)
(* sets with bounded measure).                                               *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED = prove
 (`!P (f:(A->bool)->real) (A:I->bool) (x:I->(A->bool)).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> f(s UNION t) = f(s) + f(t)) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(x a))
        ==> f(UNIONS(IMAGE x A)) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS(IMAGE x B)))`,
  let lemma = prove
   (`{t | t SUBSET (a INSERT s) /\ P t} =
     {t | t SUBSET s /\ P t} UNION
     {a INSERT t |t| t SUBSET s /\ P(a INSERT t)}`,
    REWRITE_TAC[SUBSET_INSERT_EXISTS] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[HAS_SIZE]
   `(!n s. s HAS_SIZE n ==> P s) ==> (!s. FINITE s ==> P s)`) THEN
  MATCH_MP_TAC num_WF THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES; LEFT_IMP_EXISTS_THM] THEN CONJ_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[UNIONS_0; IMAGE_CLAUSES; SUBSET_EMPTY; TAUT `~(p /\ ~p)`] THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; SUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`{}:A->bool`; `{}:A->bool`])) THEN
    ASM_SIMP_TAC[UNION_EMPTY; DISJOINT_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`A0:I->bool`; `a:I`; `A:I->bool`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN X_GEN_TAC  `x:I->A->bool` THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(f(x a) + f(UNIONS (IMAGE (x:I->(A->bool)) A))) -
              f(x a INTER UNIONS (IMAGE x A)):real` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `P(x a) /\ P(UNIONS(IMAGE (x:I->(A->bool)) A))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!b. b IN A ==> P((x:I->(A->bool)) b)` THEN
      SUBGOAL_THEN `FINITE(A:I->bool)` MP_TAC THENL
       [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
      SPEC_TAC(`A:I->bool`,`u:I->bool`) THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      ASM_SIMP_TAC[IMAGE_CLAUSES; UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT];
      SPEC_TAC(`UNIONS(IMAGE (x:I->(A->bool)) A)`,`t:A->bool`) THEN
      SPEC_TAC(`(x:I->(A->bool)) a`,`s:A->bool`) THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `!s t:A->bool. P s /\ P t /\ DISJOINT s t
                                 ==> f(s UNION t):real = f(s) + f(t)` THEN
      DISCH_THEN(fun th ->
     MP_TAC(ISPECL [`s INTER t:A->bool`; `t DIFF s:A->bool`] th) THEN
     MP_TAC(ISPECL [`s:A->bool`; `t DIFF s:A->bool`] th)) THEN
     ASM_SIMP_TAC[SET_RULE `s UNION (t DIFF s) = s UNION t`;
                  SET_RULE `(s INTER t) UNION (t DIFF s) = t`] THEN
     REPEAT(ANTS_TAC THENL [SET_TAC[]; DISCH_TAC]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
  DISCH_THEN(MP_TAC o SPEC `A:I->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(ISPEC `\s. (x:I->(A->bool)) a INTER x s` th) THEN
    MP_TAC(ISPEC `x:I->(A->bool)` th)) THEN
  ASM_SIMP_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [HAS_SIZE]) THEN
  REWRITE_TAC[lemma] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; FINITE_IMAGE] THEN
    REWRITE_TAC[GSYM SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IN_DISJOINT; EXISTS_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; REAL_ARITH
   `(fa + s) - fas:real = s + s' <=> fa - fas = s'`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `f((x:I->(A->bool)) a) +
              sum {B | B SUBSET A /\ ~(B = {})}
                  (\B. --(&1) pow (CARD B) *
                       f(INTERS(IMAGE x (a INSERT B))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x - a:real = x + b <=> b = --a`] THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT; o_DEF; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
    REWRITE_TAC[REAL_NEG_NEG; REAL_MUL_RID] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[INTERS_IMAGE] THEN ASM SET_TAC[];
    REWRITE_TAC[SET_RULE `{s | P s /\ ~(s = e)} = {s | P s} DELETE e`] THEN
    ASM_SIMP_TAC[SUM_DELETE_CASES; GSYM DELETE; FINITE_POWERSET] THEN
    REWRITE_TAC[IN_ELIM_THM; EMPTY_SUBSET; IMAGE_CLAUSES] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SIMPLE_IMAGE_GEN] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_DEF; INTERS_1; CARD_CLAUSES; real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_SUB_ADD2] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[FORALL_IN_GSPEC; REAL_POW_ADD; REAL_POW_1] THEN
    X_GEN_TAC `B:I->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(B:I->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; REAL_POW_ADD; real_pow] THEN
    COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; real_pow] THEN REAL_ARITH_TAC]);;

let INCLUSION_EXCLUSION_REAL_RESTRICTED = prove
 (`!P (f:(A->bool)->real) (A:(A->bool)->bool).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> f(s UNION t) = f(s) + f(t)) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(a))
        ==> f(UNIONS A) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS B))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:(A->bool)->bool`; `f:(A->bool)->real`;
                 `A:(A->bool)->bool`; `\x:A->bool. x`]
        INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED) THEN
  ASM_REWRITE_TAC[IMAGE_ID]);;

(* ------------------------------------------------------------------------- *)
(* Versions for unrestrictedly additive functions.                           *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_REAL_INDEXED = prove
 (`!(f:(A->bool)->real) (A:I->bool) (x:I->(A->bool)).
        (!s t. DISJOINT s t ==> f(s UNION t) = f(s) + f(t)) /\ FINITE A
        ==> f(UNIONS(IMAGE x A)) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS(IMAGE x B)))`,
  MP_TAC(ISPEC
   `\x:A->bool. T` INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED) THEN
  REWRITE_TAC[]);;

let INCLUSION_EXCLUSION_REAL = prove
 (`!(f:(A->bool)->real) (A:(A->bool)->bool).
        (!s t. DISJOINT s t ==> f(s UNION t) = f(s) + f(t)) /\ FINITE A
        ==> f(UNIONS A) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS B))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(A->bool)->real`; `A:(A->bool)->bool`; `\x:A->bool. x`]
        INCLUSION_EXCLUSION_REAL_INDEXED) THEN
  ASM_REWRITE_TAC[IMAGE_ID]);;

(* ------------------------------------------------------------------------- *)
(* Special case of cardinality, the most common case.                        *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION = prove
 (`!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum {t | t SUBSET s /\ ~(t = {})}
                    (\t. (-- &1) pow (CARD t + 1) * &(CARD(INTERS t)))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\s:A->bool. FINITE s`; `\s:A->bool. &(CARD s)`;
    `s:(A->bool)->bool`] INCLUSION_EXCLUSION_REAL_RESTRICTED) THEN
  ASM_SIMP_TAC[FINITE_INTER; FINITE_UNION; FINITE_DIFF; FINITE_EMPTY] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[CARD_UNION; DISJOINT; REAL_OF_NUM_ADD]);;

(* ------------------------------------------------------------------------- *)
(* A more conventional form.                                                 *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_USUAL = prove
 (`!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum (1..CARD s) (\n. (-- &1) pow (n + 1) *
                                     sum {t | t SUBSET s /\ t HAS_SIZE n}
                                         (\t. &(CARD(INTERS t))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INCLUSION_EXCLUSION] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) (ISPEC `CARD` SUM_IMAGE_GEN) o
     lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(MESON[] `s = t /\ sum t f = sum t g ==> sum s f = sum t g`) THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; IN_ELIM_THM] THEN
    REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
    ASM_MESON_TAC[CHOOSE_SUBSET; CARD_SUBSET; FINITE_SUBSET; CARD_EQ_0;
                  HAS_SIZE];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[CARD_EQ_0; ARITH_RULE `~(1 <= 0)`; FINITE_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* A combinatorial lemma about subsets of a finite set.                      *)
(* ------------------------------------------------------------------------- *)

let FINITE_SUBSETS_RESTRICT = prove
 (`!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

let CARD_ADJUST_LEMMA = prove
 (`!f:A->B s x y.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        x = y + CARD (IMAGE f s)
        ==> x = y + CARD s`,
  MESON_TAC[CARD_IMAGE_INJ]);;

let CARD_SUBSETS_STEP = prove
 (`!x:A s. FINITE s /\ ~(x IN s) /\ u SUBSET s
           ==> CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ ODD(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} /\
               CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ EVEN(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:A`,`:B`] CARD_ADJUST_LEMMA) THEN
  EXISTS_TAC `\u. (x:A) INSERT u` THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
   ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; FINITE_INSERT] THEN CONJ_TAC THENL
    [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
     REWRITE_TAC[TAUT `~(a /\ b) <=> b ==> ~a`; FORALL_IN_IMAGE] THEN
     ASM SET_TAC[];
     ALL_TAC] THEN
   GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:A->bool` THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNION; SUBSET_INSERT_EXISTS] THEN
   REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
   REWRITE_TAC[RIGHT_OR_DISTRIB; LEFT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN
   AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
   X_GEN_TAC `v:A->bool` THEN
   ASM_CASES_TAC `t = (x:A) INSERT v` THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `(v:A->bool) SUBSET s` THEN ASM_REWRITE_TAC[] THEN
   BINOP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; SUBSET] THEN
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; SUBSET]));;

let CARD_SUBSUPERSETS_EVEN_ODD = prove
 (`!s u:A->bool.
        FINITE u /\ s PSUBSET u
        ==> CARD {t | s SUBSET t /\ t SUBSET u /\ EVEN(CARD t)} =
            CARD {t | s SUBSET t /\ t SUBSET u /\ ODD(CARD t)}`,
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `CARD(u:A->bool)` THEN
  REWRITE_TAC[PSUBSET_MEMBER] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  MP_TAC(SET_RULE `~((x:A) IN (u DELETE x))`) THEN
  ABBREV_TAC `v:A->bool = u DELETE x` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE v /\ (s:A->bool) SUBSET v` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[FINITE_INSERT]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_SUBSETS_STEP] THEN ASM_CASES_TAC `s:A->bool = v` THENL
   [REWRITE_TAC[CONJ_ASSOC; SUBSET_ANTISYM_EQ] THEN MATCH_ACCEPT_TAC ADD_SYM;
    ASM_SIMP_TAC[CARD_CLAUSES; LT; PSUBSET]]);;

let SUM_ALTERNATING_CANCELS = prove
 (`!s:A->bool f.
        FINITE s /\
        CARD {x | x IN s /\ EVEN(f x)} = CARD {x | x IN s /\ ODD(f x)}
        ==> sum s (\x. (-- &1) pow (f x)) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x | x IN s /\ EVEN(f x)} (\x. (-- &1) pow (f x)) +
              sum {x:A | x IN s /\ ODD(f x)} (\x. (-- &1) pow (f x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_EVEN; SUM_CONST;
               FINITE_RESTRICT; REAL_ARITH `x * &1 + x * -- &1 = &0`]);;

(* ------------------------------------------------------------------------- *)
(* Hence a general "Moebius inversion" inclusion-exclusion principle.        *)
(* This "symmetric" form is from Ira Gessel: "Symmetric Inclusion-Exclusion" *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_SYMMETRIC = prove
 (`!f g:(A->bool)->real.
    (!s. FINITE s
         ==> g(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * f(t)))
    ==> !s. FINITE s
            ==> f(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * g(t))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {t:A->bool | t SUBSET s}
                  (\t. (-- &1) pow (CARD t) *
                       sum {u | u IN {u | u SUBSET s} /\ u SUBSET t}
                           (\u. (-- &1) pow (CARD u) * f(u)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; SET_RULE
     `s SUBSET t ==> (u SUBSET t /\ u SUBSET s <=> u SUBSET s)`] THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_RESTRICT o lhs o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_RMUL; IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum {u | u SUBSET s} (\u:A->bool. if u = s then f(s) else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_DELTA; IN_ELIM_THM; SUBSET_REFL]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SUBSET_ANTISYM_EQ; SET_RULE `{x | x = a} = {a}`] THEN
    REWRITE_TAC[SUM_SING; REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; REAL_POW_ONE; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN REPEAT DISJ1_TAC THEN
  MATCH_MP_TAC SUM_ALTERNATING_CANCELS THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
  MATCH_MP_TAC CARD_SUBSUPERSETS_EVEN_ODD THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The more typical non-symmetric version.                                   *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_MOBIUS = prove
 (`!f g:(A->bool)->real.
        (!s. FINITE s ==> g(s) = sum {t | t SUBSET s} f)
        ==> !s. FINITE s
                ==> f(s) = sum {t | t SUBSET s}
                               (\t. (-- &1) pow (CARD s - CARD t) * g(t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. -- &1 pow CARD(t:A->bool) * f t`; `g:(A->bool)->real`]
                INCLUSION_EXCLUSION_SYMMETRIC) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[EVEN_ADD; REAL_POW_ONE; REAL_POW_NEG; REAL_MUL_LID; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) ((-- &1) pow (CARD(s:A->bool)))`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD; GSYM MULT_2] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `u:A->bool` THEN REWRITE_TAC[IN_ELIM_THM; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_POW_SUB; REAL_ARITH `~(-- &1 = &0)`; CARD_SUBSET] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A related principle for real functions.                                   *)
(* ------------------------------------------------------------------------- *)

(*** Not clear how useful this is

needs "Library/products.ml";;

let INCLUSION_EXCLUSION_REAL_FUNCTION = prove
 (`!f s:A->bool.
        FINITE s
        ==> product s (\x. &1 - f x) =
            sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * product t f)`,
  let lemma = prove
   (`{t | ?u. u SUBSET s /\ t = x INSERT u} =
     IMAGE (\s. x INSERT s) {t | t SUBSET s}`,
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    MESON_TAC[]) in
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; SUBSET_EMPTY; SUM_SING; CARD_CLAUSES; real_pow;
           SET_RULE `{x | x = a} = {a}`; REAL_MUL_RID] THEN
  REWRITE_TAC[SUBSET_INSERT_EXISTS] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `{t | p t \/ q t} = {t | p t} UNION {t | q t}`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET; lemma; FINITE_IMAGE] THEN
    REWRITE_TAC[GSYM lemma] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; REAL_SUB_RDISTRIB; REAL_MUL_LID; real_sub] THEN
  AP_TERM_TAC THEN REWRITE_TAC[lemma] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC[o_THM; IN_ELIM_THM] THEN X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(t:A->bool) /\ ~(x IN t)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; CARD_CLAUSES; real_pow] THEN REAL_ARITH_TAC);;

***)
