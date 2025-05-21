(* ========================================================================= *)
(* Axiomatic approach to independence. This is matroid-like but without      *)
(* any finiteness assumptions, closely following Pete Clark's "Field Theory" *)
(* notes (http://alpha.math.uga.edu/~pete/FieldTheory.pdf), section 11.4.    *)
(* ========================================================================= *)

needs "Library/card.ml";;

(* ------------------------------------------------------------------------- *)
(* Basic finitary matroid type definition.                                   *)
(* ------------------------------------------------------------------------- *)

let matroid_tybij =
  let eth = prove
   (`?m. (!s:A->bool. s SUBSET FST m ==> SND m s SUBSET FST m) /\
         (!s:A->bool. s SUBSET FST m ==> s SUBSET SND m s) /\
         (!s t. s SUBSET t /\ t SUBSET FST m ==> SND m s SUBSET SND m t) /\
         (!s. s SUBSET FST m ==> SND m (SND m s) = SND m s) /\
         (!s x. s SUBSET FST m /\ x IN SND m s
                ==> ?s'. FINITE s' /\ s' SUBSET s /\ x IN SND m (s')) /\
         (!s x y. s SUBSET FST m /\ x IN FST m /\
                  y IN SND m (x INSERT s) /\ ~(y IN SND m s)
                  ==> x IN SND m (y INSERT s))`,
    EXISTS_TAC `({}:A->bool,(\x:A->bool. x))` THEN SET_TAC[]) in
  new_type_definition "matroid" ("matroid","dest_matroid") eth;;

let matroid_set = new_definition
 `matroid_set:A matroid->A->bool = \m. FST(dest_matroid m)`;;

let matroid_span = new_definition
 `matroid_span = \m:A matroid. SND(dest_matroid m)`;;

let [MATROID_SPAN_SUBSET; MATROID_SPAN_SUPERSET; MATROID_SPAN_MONO;
     MATROID_SPAN_SPAN; MATROID_SPAN_FINITARY; MATROID_SPAN_EXCHANGE] =
   (map (GEN `m:A matroid`) o CONJUNCTS)
   (REWRITE_RULE(CONJUNCT1 matroid_tybij::
                 map (REWRITE_RULE[] o ONCE_REWRITE_RULE[FUN_EQ_THM] o SYM)
                     [matroid_set; matroid_span])
  (SPEC `dest_matroid(m:A matroid)` (CONJUNCT2 matroid_tybij)));;

let MATROID_SPAN_INC = prove
 (`!(m:A matroid) s x.
        s SUBSET matroid_set m /\ x IN s ==> x IN matroid_span m s`,
  MESON_TAC[MATROID_SPAN_SUPERSET; SUBSET]);;

let SUBSET_MATROID_SPAN = prove
 (`!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> (matroid_span m s SUBSET matroid_span m t <=>
             s SUBSET matroid_span m t)`,
  MESON_TAC[MATROID_SPAN_MONO; MATROID_SPAN_SPAN; MATROID_SPAN_SUBSET;
            MATROID_SPAN_SUPERSET; SUBSET_TRANS]);;

let MATROID_SPAN_MINIMAL = prove
 (`!(m:A matroid) s t.
        t SUBSET matroid_set m /\
        s SUBSET matroid_span m t
        ==> matroid_span m s SUBSET matroid_span m t`,
  MESON_TAC[SUBSET_MATROID_SPAN; MATROID_SPAN_SUBSET; SUBSET_TRANS]);;

let MATROID_SPAN_SET = prove
 (`!(m:A matroid). matroid_span m (matroid_set m) = matroid_set m`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  MESON_TAC[MATROID_SPAN_SUPERSET; SUBSET_REFL; MATROID_SPAN_SUBSET]);;

let MATROID_SPAN_EQ = prove
 (`!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> (matroid_span m s = matroid_span m t <=>
             s SUBSET matroid_span m t /\ t SUBSET matroid_span m s)`,
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_MATROID_SPAN]);;

let MATROID_SPAN_EQ_SET = prove
 (`!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> (matroid_span m s = matroid_set m <=>
             matroid_set m SUBSET matroid_span m s)`,
  MESON_TAC[MATROID_SPAN_EQ; SUBSET_REFL; MATROID_SPAN_SET]);;

let MATROID_SPAN_SUBSET_EQ = prove
 (`!(m:A matroid) s t.
        s SUBSET t /\ t SUBSET matroid_set m
        ==> (matroid_span m s = matroid_span m t <=>
             t SUBSET matroid_span m s)`,
  MESON_TAC[MATROID_SPAN_EQ; SUBSET_TRANS; MATROID_SPAN_SUPERSET]);;

let MATROID_SPAN_INTER_SUBSET = prove
 (`!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (s INTER t) SUBSET
            matroid_span m s INTER matroid_span m t`,
  REWRITE_TAC[SUBSET_INTER] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[]);;

let MATROID_SPAN_UNION = prove
 (`!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (s UNION t) =
            matroid_span m (matroid_span m s UNION matroid_span m t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC MATROID_SPAN_MONO;
    MATCH_MP_TAC MATROID_SPAN_MINIMAL] THEN
  ASM_SIMP_TAC[MATROID_SPAN_SUPERSET; SET_RULE
   `s SUBSET s' /\ t SUBSET t' ==> s UNION t SUBSET s' UNION t'`] THEN
  ASM_SIMP_TAC[UNION_SUBSET; MATROID_SPAN_SUBSET;
               MATROID_SPAN_MONO; SUBSET_UNION]);;

let MATROID_SPAN_UNION_LEFT = prove
 (`!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (s UNION t) =
            matroid_span m (matroid_span m s UNION t)`,
  ASM_MESON_TAC[MATROID_SPAN_UNION; MATROID_SPAN_SPAN; MATROID_SPAN_SUBSET]);;

let MATROID_SPAN_UNION_RIGHT = prove
 (`!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (s UNION t) =
            matroid_span m (s UNION matroid_span m t)`,
  ASM_MESON_TAC[MATROID_SPAN_UNION; MATROID_SPAN_SPAN; MATROID_SPAN_SUBSET]);;

let MATROID_SPAN_UNION_SUBSET = prove
 (`!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m s UNION matroid_span m t SUBSET
            matroid_span m (s UNION t)`,
  REWRITE_TAC[UNION_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[]);;

let MATROID_SPAN_EXCHANGE_DELETE = prove
 (`!(m:A matroid) a b s.
        s SUBSET matroid_set m /\
        b IN matroid_set m /\
        a IN matroid_span m s /\
        ~(a IN matroid_span m (s DELETE b))
        ==> b IN matroid_span m (a INSERT (s DELETE b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_SPAN_EXCHANGE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s SUBSET t ==> x IN t`)) THEN
  MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[]);;

let MATROID_SPAN_UNION_EQ = prove
 (`!m s t:A->bool.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> (matroid_span m (s UNION t) = matroid_span m t <=>
             s SUBSET matroid_span m t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `t:A->bool`; `s UNION t:A->bool`]
        MATROID_SPAN_SUBSET_EQ) THEN
  ASM_REWRITE_TAC[UNION_SUBSET; SUBSET_UNION] THEN
  ASM_MESON_TAC[MATROID_SPAN_SUPERSET]);;

let MATROID_SPAN_INSERT_EQ = prove
 (`!(m:A matroid) s x.
        s SUBSET matroid_set m /\ x IN matroid_set m
        ==> (matroid_span m (x INSERT s) = matroid_span m s <=>
             x IN matroid_span m s)`,
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  MESON_TAC[GSYM SING_SUBSET; MATROID_SPAN_UNION_EQ]);;

let MATROID_SPAN_DELETE_EQ = prove
 (`!(m:A matroid) s x.
        x IN s /\ s SUBSET matroid_set m
        ==> (matroid_span m (s DELETE x) = matroid_span m s <=>
             x IN matroid_span m (s DELETE x))`,
  SIMP_TAC[MATROID_SPAN_SUBSET_EQ; DELETE_SUBSET] THEN
  ASM_MESON_TAC[MATROID_SPAN_SUPERSET; SET_RULE
   `x IN s ==> (s SUBSET t <=> x IN t /\ s DELETE x SUBSET t)`]);;

let MATROID_SPAN_TRANS = prove
 (`!(m:A matroid) x y s.
        s SUBSET matroid_set m /\
        x IN matroid_span m s /\
        y IN matroid_span m (x INSERT s)
        ==> y IN matroid_span m s`,
  MESON_TAC[SUBSET; MATROID_SPAN_SUBSET; MATROID_SPAN_INSERT_EQ]);;

let MATROID_SPAN_FINITARY_GEN = prove
 (`!(m:A matroid) s k.
        s SUBSET matroid_set m /\
        FINITE k /\ k SUBSET matroid_span m s
        ==> exists s'. FINITE s' /\ s' SUBSET s /\ k SUBSET matroid_span m s'`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[EMPTY_SUBSET; INSERT_SUBSET; IMP_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THENL [MESON_TAC[FINITE_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `k:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `x:A`] MATROID_SPAN_FINITARY) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `t UNION u:A->bool` THEN
  ASM_REWRITE_TAC[FINITE_UNION; UNION_SUBSET] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`));
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS))] THEN
  MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[]);;

let MATROID_SPAN_FINITARY_MINIMAL = prove
 (`!(m:A matroid) s x.
         s SUBSET matroid_set m /\
         x IN matroid_span m s
         ==> ?t. FINITE t /\ t SUBSET s /\ x IN matroid_span m t /\
                 !t'. t' PSUBSET t ==> ~(x IN matroid_span m t')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `x:A`] MATROID_SPAN_FINITARY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WF_PSUBSET) THEN REWRITE_TAC[WF] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\s. s SUBSET u /\ (x:A) IN matroid_span m s`) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_REFL]; MATCH_MP_TAC MONO_EXISTS] THEN
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Definitions of linear algebra notions in terms of span.                   *)
(* We build in the assumption that they are subsets of the overall set.      *)
(* ------------------------------------------------------------------------- *)

let matroid_spanning = new_definition
 `matroid_spanning (m:A matroid) s <=>
        s SUBSET matroid_set m /\ matroid_span m s = matroid_set m`;;

let matroid_independent = new_definition
  `matroid_independent (m:A matroid) s <=>
        s SUBSET matroid_set m /\
        !x. x IN s ==> ~(x IN matroid_span m (s DELETE x))`;;

let matroid_basis = new_definition
 `matroid_basis (m:A matroid) s <=>
        matroid_spanning m s /\ matroid_independent m s`;;

let matroid_dependent = define
 `matroid_dependent (m:A matroid) s <=>
        s SUBSET matroid_set m /\ ~matroid_independent m s`;;

let MATROID_SPANNING_IMP_SUBSET = prove
 (`!(m:A matroid) s. matroid_spanning m s ==> s SUBSET matroid_set m`,
  SIMP_TAC[matroid_spanning]);;

let MATROID_INDEPENDENT_IMP_SUBSET = prove
 (`!(m:A matroid) s. matroid_independent m s ==> s SUBSET matroid_set m`,
  SIMP_TAC[matroid_independent]);;

let MATROID_DEPENDENT_IMP_SUBSET = prove
 (`!(m:A matroid) s. matroid_dependent m s ==> s SUBSET matroid_set m`,
  SIMP_TAC[matroid_dependent]);;

let MATROID_BASIS_IMP_SUBSET = prove
 (`!(m:A matroid) s. matroid_basis m s ==> s SUBSET matroid_set m`,
  SIMP_TAC[matroid_basis; matroid_spanning]);;

let MATROID_SPANNING_ALT = prove
 (`!(m:A matroid) s.
        matroid_spanning m s <=>
        s SUBSET matroid_set m /\
        matroid_set m SUBSET matroid_span m s`,
  REWRITE_TAC[matroid_spanning] THEN MESON_TAC[MATROID_SPAN_EQ_SET]);;

let MATROID_SPANNING_SET = prove
 (`!(m:A matroid).
        matroid_spanning m (matroid_set m)`,
  SIMP_TAC[matroid_spanning; SUBSET_REFL; MATROID_SPAN_SET]);;

let MATROID_INDEPENDENT = prove
 (`!(m:A matroid) s.
        matroid_independent m s <=>
        s SUBSET matroid_set m /\ ~matroid_dependent m s`,
  REWRITE_TAC[matroid_dependent; matroid_independent] THEN SET_TAC[]);;

let MATROID_DEPENDENT = prove
 (`!(m:A matroid) s.
        matroid_dependent m s <=>
        s SUBSET matroid_set m /\
        ?x. x IN s /\ x IN matroid_span m (s DELETE x)`,
  REWRITE_TAC[matroid_dependent; matroid_independent] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Properties of independent sets (which in other formulations could         *)
(* be the matroid axioms).                                                   *)
(* ------------------------------------------------------------------------- *)

let MATROID_INDEPENDENT_EMPTY = prove
 (`!m:A matroid. matroid_independent m {}`,
  REWRITE_TAC[matroid_independent; NOT_IN_EMPTY; EMPTY_SUBSET]);;

let MATROID_INDEPENDENT_MONO = prove
 (`!(m:A matroid) s t.
        matroid_independent m t /\ s SUBSET t ==> matroid_independent m s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matroid_independent] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  MP_TAC(ISPECL
   [`m:A matroid`; `s DELETE (x:A)`; `t DELETE (x:A)`] MATROID_SPAN_MONO) THEN
  ASM SET_TAC[]);;

let MATROID_INDEPENDENT_FINITARY = prove
 (`!(m:A matroid) s.
        matroid_independent m s <=>
        s SUBSET matroid_set m /\
        !t. FINITE t /\ t SUBSET s ==> matroid_independent m t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[MATROID_INDEPENDENT_MONO; MATROID_INDEPENDENT_IMP_SUBSET];
    ASM_REWRITE_TAC[matroid_independent] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`m:A matroid`; `s DELETE (x:A)`; `x:A`] MATROID_SPAN_FINITARY) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `t:A->bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:A) INSERT t`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT] THEN ASM SET_TAC[];
    DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[IN_INSERT; CONTRAPOS_THM] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let MATROID_DEPENDENT_FINITARY = prove
 (`!(m:A matroid) s.
         matroid_dependent m s <=>
         s SUBSET matroid_set m /\
         ?t. FINITE t /\ t SUBSET s /\ matroid_dependent m t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matroid_dependent] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [MATROID_INDEPENDENT_FINITARY] THEN
  SET_TAC[]);;

let MATROID_INDEPENDENT_INSERT = prove
 (`!(m:A matroid) s a.
        matroid_independent m (a INSERT s) <=>
        if a IN s then matroid_independent m s
        else a IN matroid_set m /\
             matroid_independent m s /\
             ~(a IN matroid_span m s)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> a INSERT s = s`] THEN
  REWRITE_TAC[matroid_independent; INSERT_SUBSET; FORALL_IN_INSERT] THEN
  ASM_CASES_TAC `(a:A) IN matroid_set m` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(s:A->bool) SUBSET matroid_set m` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> (a INSERT s) DELETE a = s`] THEN
  REWRITE_TAC[TAUT `(~p /\ q <=> q' /\ ~p) <=> ~p ==> (q <=> q')`] THEN
  DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. p x ==> (q x <=> r x))
    ==> ((!x. p x ==> ~q x) <=> (!x. p x ==> ~r x))`) THEN
  X_GEN_TAC `b:A` THEN DISCH_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> a IN s ==> a IN t`) THEN
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[]] THEN
  ASM_CASES_TAC `b:A = a` THEN
  ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> (a INSERT s) DELETE a = s`] THEN
  ASM_SIMP_TAC[SET_RULE
    `~(a IN s) /\ ~(b = a)
     ==> ((a INSERT s) DELETE b = a INSERT (s DELETE b))`] THEN
  MP_TAC(ISPECL [`m:A matroid`; `s DELETE (b:A)`; `a:A`; `b:A`]
        MATROID_SPAN_EXCHANGE) THEN
  ASM_SIMP_TAC[SET_RULE `b IN s ==> b INSERT (s DELETE b) = s`] THEN
  ASM SET_TAC[]);;

let MATROID_SPAN_PSUBSET_INDEPENDENT = prove
 (`!(m:A matroid) s t.
        s PSUBSET t /\ matroid_independent m t
        ==> matroid_span m s PSUBSET matroid_span m t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`)  o
    GEN_REWRITE_RULE I [matroid_independent]) THEN
  ASM_SIMP_TAC[PSUBSET_ALT; MATROID_SPAN_MONO] THEN
  DISCH_TAC THEN EXISTS_TAC `(x:A)` THEN
  MP_TAC(SPECL [`m:A matroid`; `s:A->bool`; `t DELETE (x:A)`]
        MATROID_SPAN_MONO) THEN
  ASM SET_TAC[MATROID_SPAN_INC]);;

let MATROID_SPAN_PSUBSET_EXPLICIT = prove
 (`!(m:A matroid) s t.
        s PSUBSET t /\ matroid_independent m t
        ==> ?a. a IN t /\ ~(a IN matroid_span m s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `t:A->bool`]
        MATROID_SPAN_PSUBSET_INDEPENDENT) THEN
  MP_TAC(ISPECL [`m:A matroid`; `t:A->bool`; `s:A->bool`]
    SUBSET_MATROID_SPAN) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
  ASM SET_TAC[]);;

let MATROID_SPANNING_SUBSET_INDEPENDENT = prove
 (`!(m:A matroid) s t.
        t SUBSET s /\ matroid_independent m s /\ s SUBSET matroid_span m t
        ==> s = t`,
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [matroid_independent]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `a:A`)) THEN
  MP_TAC(ISPECL [`m:A matroid`; `t:A->bool`; `s DELETE (a:A)`]
    MATROID_SPAN_MONO) THEN
  ASM SET_TAC[]);;

let MATROID_SPANNING_PSUBSET_INDEPENDENT = prove
 (`!(m:A matroid) s t.
        ~(s PSUBSET t /\ matroid_spanning m s /\ matroid_independent m t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `t:A->bool`]
        MATROID_SPAN_PSUBSET_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> ~(t PSUBSET s)`) THEN
  ASM_MESON_TAC[MATROID_SPAN_SUBSET; matroid_spanning; matroid_independent]);;

let MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN = prove
 (`!(m:A matroid) s t.
        s SUBSET t /\ t SUBSET matroid_set m /\
        matroid_independent m s /\
        (!s'. s PSUBSET s' /\ s' SUBSET t ==> ~matroid_independent m s')
        ==> matroid_span m s = matroid_span m t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC[MATROID_SPAN_MONO] THEN
  ASM_SIMP_TAC[SUBSET_MATROID_SPAN] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:A) INSERT s`) THEN
  ASM_REWRITE_TAC[MATROID_INDEPENDENT_INSERT] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SET_RULE `s PSUBSET x INSERT s <=> ~(x IN s)`] THEN
  ASM_MESON_TAC[SUBSET; INSERT_SUBSET; MATROID_SPAN_SUPERSET]);;

let MATROID_BASIS_EQ_MAXIMAL_INDEPENDENT = prove
 (`!(m:A matroid) s.
        matroid_basis m s <=>
        matroid_independent m s /\
        !s'. s PSUBSET s' ==> ~matroid_independent m s'`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[MATROID_SPANNING_PSUBSET_INDEPENDENT; matroid_basis];
    STRIP_TAC THEN ASM_REWRITE_TAC[matroid_basis]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
  ASM_REWRITE_TAC[matroid_spanning] THEN
  ONCE_REWRITE_TAC[GSYM MATROID_SPAN_SET] THEN
  MATCH_MP_TAC MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN THEN
  ASM_SIMP_TAC[SUBSET_REFL]);;

let MATROID_BASIS_EQ_MINIMAL_SPANNING = prove
 (`!(m:A matroid) s.
        matroid_basis m s <=>
        matroid_spanning m s /\
        !s'. s' PSUBSET s ==> ~matroid_spanning m s'`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[MATROID_SPANNING_PSUBSET_INDEPENDENT; matroid_basis];
    STRIP_TAC THEN ASM_REWRITE_TAC[matroid_basis]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MATROID_SPANNING_IMP_SUBSET) THEN
  ASM_REWRITE_TAC[matroid_independent] THEN
  X_GEN_TAC `x:A` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (x:A)`) THEN
  REWRITE_TAC[matroid_spanning; NOT_IMP] THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  ASM_MESON_TAC[MATROID_SPAN_DELETE_EQ; matroid_spanning]);;

let MATROID_INDEPENDENT_CHAIN = prove
 (`!(m:A matroid) c.
        (!s. s IN c ==> matroid_independent m s) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> matroid_independent m (UNIONS c)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c:(A->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; MATROID_INDEPENDENT_EMPTY] THEN
  ONCE_REWRITE_TAC[MATROID_INDEPENDENT_FINITARY] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[matroid_independent]) THEN ASM SET_TAC[];
    X_GEN_TAC `s:A->bool` THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(A->bool)->bool`; `s:A->bool`]
    FINITE_SUBSET_UNIONS_CHAIN) THEN
  ASM_MESON_TAC[MATROID_INDEPENDENT_MONO]);;

let MATROID_SPAN_CHAIN = prove
 (`!(m:A matroid) c.
        ~(c = {}) /\
        (!s. s IN c ==> s SUBSET matroid_set m) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> matroid_span m (UNIONS c) = UNIONS {matroid_span m s | s IN c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:A` THEN DISCH_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_SPAN_MONO THEN
    ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        MATROID_SPAN_FINITARY)) THEN
  ASM_REWRITE_TAC[UNIONS_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(A->bool)->bool`; `t:A->bool`]
    FINITE_SUBSET_UNIONS_CHAIN) THEN
  ASM SET_TAC[MATROID_SPAN_MONO]);;

let MATROID_INTERMEDIATE_SPAN = prove
 (`!(m:A matroid) s t.
        matroid_independent m s /\
        t SUBSET matroid_set m /\
        s SUBSET matroid_span m t
        ==> ?b. s SUBSET b /\ b SUBSET (s UNION t) /\
                matroid_independent m b /\
                matroid_span m b = matroid_span m t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\u:A->bool. s SUBSET u /\ u SUBSET (s UNION t) /\
                            matroid_independent m u`
    ZL_SUBSETS_UNIONS_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [EXISTS_TAC `s:A->bool` THEN ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `c:(A->bool)->bool` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATROID_INDEPENDENT_CHAIN; UNION_SUBSET] THEN ASM SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:A->bool`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC MATROID_SPAN_MINIMAL THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THENL
   [TRANS_TAC SUBSET_TRANS `s UNION t:A->bool` THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN ASM_SIMP_TAC[MATROID_SPAN_SUPERSET];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(x:A) INSERT b`) THEN
    ASM_REWRITE_TAC[MATROID_INDEPENDENT_INSERT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[MATROID_SPAN_INC]; ASM SET_TAC[]]]);;

let MATROID_INTERMEDIATE_BASIS = prove
 (`!(m:A matroid) s t.
        matroid_independent m s /\ matroid_spanning m t
        ==> ?b. s SUBSET b /\ b SUBSET (s UNION t) /\ matroid_basis m b`,
  REWRITE_TAC[matroid_spanning; matroid_basis] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `t:A->bool`]
        MATROID_INTERMEDIATE_SPAN) THEN
  ASM_MESON_TAC[matroid_independent]);;

let MATROID_INDEPENDENT_EXTENDS_TO_BASIS = prove
 (`!(m:A matroid) s.
        matroid_independent m s ==> ?b. s SUBSET b /\ matroid_basis m b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `matroid_set m:A->bool`]
        MATROID_INTERMEDIATE_BASIS) THEN
  ASM_REWRITE_TAC[MATROID_SPANNING_SET] THEN MESON_TAC[]);;

let MATROID_BASIS_EXISTS = prove
 (`!(m:A matroid). ?b. matroid_basis m b`,
  MESON_TAC[MATROID_INDEPENDENT_EXTENDS_TO_BASIS; MATROID_INDEPENDENT_EMPTY]);;

let MATROID_SPANNING_CONTAINS_BASIS = prove
 (`!(m:A matroid) s.
        matroid_spanning m s ==> ?b. b SUBSET s /\ matroid_basis m b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `{}:A->bool`; `s:A->bool`]
        MATROID_INTERMEDIATE_BASIS) THEN
  ASM_REWRITE_TAC[MATROID_INDEPENDENT_EMPTY; UNION_EMPTY] THEN MESON_TAC[]);;

let MATROID_SPAN_DEPENDENCE = prove
 (`!(m:A matroid) s x.
        x IN matroid_set m /\ s SUBSET matroid_set m
        ==> (x IN matroid_span m s <=>
             x IN s \/
             ?t. t SUBSET s /\
                 matroid_independent m t /\
                 matroid_dependent m (x INSERT t))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATROID_INDEPENDENT_INSERT; matroid_dependent] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> ~(q ==> ~(p /\ r))`] THEN
  SIMP_TAC[MESON[] `~(if p then T else ~x) <=> ~p /\ x`] THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[MATROID_SPAN_MONO; MATROID_SPAN_INC; SUBSET]] THEN
  ASM_CASES_TAC `(x:A) IN s` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:A matroid`; `{}:A->bool`; `s:A->bool`]
        MATROID_INTERMEDIATE_SPAN) THEN
  ASM_REWRITE_TAC[MATROID_INDEPENDENT_EMPTY; EMPTY_SUBSET; UNION_EMPTY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let MATROID_STEINITZ_EXCHANGE = prove
 (`!(m:A matroid) s t.
      t SUBSET matroid_set m /\
      FINITE s /\ matroid_independent m s /\ s SUBSET matroid_span m t
      ==> ?t'. t' SUBSET t /\ t' HAS_SIZE (CARD s) /\
               matroid_span m ((t DIFF t') UNION s) = matroid_span m t`,
  GEN_TAC THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `{}:A->bool` THEN
    REWRITE_TAC[HAS_SIZE; FINITE_EMPTY; EMPTY_SUBSET] THEN
    AP_TERM_TAC THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN REWRITE_TAC[IMP_IMP]] THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[MATROID_INDEPENDENT_MONO; SET_RULE `s SUBSET x INSERT s`];
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`m:A matroid`; `t DIFF u UNION s:A->bool`; `x:A`]
        MATROID_SPAN_FINITARY_MINIMAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM SET_TAC[MATROID_SPAN_SUBSET];
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `v:A->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN MP_TAC o MATCH_MP (SET_RULE
   `v SUBSET t UNION s ==> v SUBSET s \/ ?a. a IN v /\ a IN t`))
  THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [matroid_independent]) THEN
    REWRITE_TAC[FORALL_IN_INSERT; INSERT_SUBSET] THEN
    ASM_SIMP_TAC[SET_RULE `~(x IN s) ==> (x INSERT s) DELETE x = s`] THEN
    ASM_MESON_TAC[MATROID_SPAN_MONO; SUBSET];
    REWRITE_TAC[IN_DIFF; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN EXISTS_TAC `(y:A) INSERT u` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HAS_SIZE]) THEN
  ABBREV_TAC `n = CARD(s:A->bool)` THEN
  ASM_SIMP_TAC[INSERT_SUBSET; HAS_SIZE; CARD_CLAUSES; FINITE_INSERT] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC MATROID_SPAN_MINIMAL THENL
   [ASM SET_TAC[MATROID_SPAN_SUPERSET]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[MATROID_SPAN_SUBSET]; ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS `matroid_span (m:A matroid) (t DIFF u UNION s)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[MATROID_SPAN_SUPERSET]; ALL_TAC] THEN
  MATCH_MP_TAC MATROID_SPAN_MINIMAL THEN
  CONJ_TAC THENL [ASM SET_TAC[MATROID_SPAN_SUBSET]; ALL_TAC] THEN
  TRANS_TAC SUBSET_TRANS
   `{y:A} UNION (t DIFF (y INSERT u) UNION (x INSERT s))` THEN CONJ_TAC
  THENL [SET_TAC[]; ONCE_REWRITE_TAC[UNION_SUBSET]] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MATROID_SPAN_SUPERSET THEN
    ASM SET_TAC[MATROID_SPAN_SUBSET]] THEN
  TRANS_TAC SUBSET_TRANS `matroid_span m ((x:A) INSERT (v DELETE y))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SING_SUBSET];
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[MATROID_SPAN_SUBSET]] THEN
  MATCH_MP_TAC MATROID_SPAN_EXCHANGE THEN
  ASM_SIMP_TAC[SET_RULE `y IN v ==> y INSERT (v DELETE y) = v`] THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[MATROID_SPAN_SUBSET]; ALL_TAC]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE = prove
 (`!(m:A matroid) s t.
        FINITE t /\ t SUBSET matroid_set m /\
        matroid_independent m s /\ s SUBSET matroid_span m t
        ==> FINITE s /\ CARD s <= CARD t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  REWRITE_TAC[ARITH_RULE `~(a <= b) <=> b + 1 <= a`] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[HAS_SIZE] o MATCH_MP CHOOSE_SUBSET_STRONG) THEN
  MP_TAC(ISPECL [`m:A matroid`; `u:A->bool`; `t:A->bool`]
        MATROID_STEINITZ_EXCHANGE) THEN
  ASM_REWRITE_TAC[NOT_IMP; HAS_SIZE] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MATROID_INDEPENDENT_MONO];
    ASM SET_TAC[];
    ASM_MESON_TAC[FINITE_SUBSET; CARD_SUBSET;
                  ARITH_RULE `m <= n ==> ~(n + 1 = m)`]]);;

let MATROID_EQ_SPANS_FINITE = prove
 (`!(m:A matroid) s t.
        matroid_independent m s /\ matroid_independent m t /\
        matroid_span m s = matroid_span m t
        ==> (FINITE s <=> FINITE t)`,
  MESON_TAC[SUBSET_MATROID_SPAN; SUBSET_REFL; matroid_independent;
            MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE]);;

let MATROID_EQ_SPANS_SIZE = prove
 (`!(m:A matroid) s t n.
        matroid_independent m s /\ matroid_independent m t /\
        matroid_span m s = matroid_span m t
        ==> (s HAS_SIZE n <=> t HAS_SIZE n)`,
  REWRITE_TAC[HAS_SIZE] THEN
  MESON_TAC[SUBSET_MATROID_SPAN; SUBSET_REFL; matroid_independent;
            MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE; LE_ANTISYM]);;

let MATROID_BASES_FINITE = prove
 (`!(m:A matroid) s t.
        matroid_basis m s /\ matroid_basis m t ==> (FINITE s <=> FINITE t)`,
  REWRITE_TAC[matroid_basis; matroid_spanning] THEN
  MESON_TAC[MATROID_EQ_SPANS_FINITE]);;

let MATROID_BASES_SIZE = prove
 (`!(m:A matroid) s t n.
        matroid_basis m s /\ matroid_basis m t
        ==> (s HAS_SIZE n <=> t HAS_SIZE n)`,
  REWRITE_TAC[matroid_basis; matroid_spanning] THEN
  MESON_TAC[MATROID_EQ_SPANS_SIZE]);;

let MATROID_INDEPENDENT_CARD_LE_SPAN = prove
 (`!(m:A matroid) s t.
        t SUBSET matroid_set m /\
        matroid_independent m s /\ s SUBSET matroid_span m t
        ==> s <=_c t`,
  let lemma = prove
   (`!(m:A matroid) s t.
          matroid_independent m s /\
          INFINITE t /\ t SUBSET matroid_set m /\
          matroid_span m t = matroid_span m s
          ==> s <=_c t`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!x:A. x IN t
            ==> ?k. FINITE k /\ k SUBSET s /\ x IN matroid_span m k`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_SPAN_FINITARY THEN
      ASM_MESON_TAC[MATROID_SPAN_SUPERSET; matroid_independent; SUBSET];
      REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:A->A->bool`) THEN
    MP_TAC(ISPECL
     [`m:A matroid`; `UNIONS {(k:A->A->bool) x | x IN t}`; `s:A->bool`]
          MATROID_SPAN_PSUBSET_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
     `t SUBSET s /\ (t SUBSET s ==> s' SUBSET t' /\ (s SUBSET t ==> P))
      ==> (t PSUBSET s ==> t' PSUBSET s') ==> P`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC[MATROID_SPAN_SUPERSET; SUBSET];
      STRIP_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MATROID_SPAN_MINIMAL THEN
      CONJ_TAC THENL [ASM SET_TAC[matroid_independent]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN t ==> t SUBSET s ==> x IN s`)) THEN
      MATCH_MP_TAC MATROID_SPAN_MONO THEN
      RULE_ASSUM_TAC(REWRITE_RULE[matroid_independent]) THEN ASM SET_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_TRANS) THEN
      MATCH_MP_TAC CARD_LE_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; CARD_LE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[CARD_LE_FINITE_INFINITE]]) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `FINITE(t:A->bool)` THENL
   [ASM_MESON_TAC[MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE;
                  CARD_LE_CARD];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INFINITE])] THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `t:A->bool`]
        MATROID_INTERMEDIATE_SPAN) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:A->bool` THEN STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `b:A->bool` THEN
  ASM_SIMP_TAC[CARD_LE_SUBSET] THEN MATCH_MP_TAC lemma THEN ASM_MESON_TAC[]);;

let MATROID_INDEPENDENT_CARD_LE_SPANNING = prove
 (`!(m:A matroid) s t.
        matroid_independent m s /\ matroid_spanning m t
        ==> s <=_c t`,
  REWRITE_TAC[matroid_spanning] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_INDEPENDENT_CARD_LE_SPAN THEN
  ASM_MESON_TAC[matroid_independent]);;

let MATROID_EQ_SPANS_CARD_EQ = prove
 (`!(m:A matroid) s t.
        matroid_independent m s /\ matroid_independent m t /\
        matroid_span m s = matroid_span m t
        ==> s =_c t`,
  GEN_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN
  MESON_TAC[MATROID_INDEPENDENT_CARD_LE_SPAN; matroid_independent;
            MATROID_SPAN_SUPERSET]);;

let MATROID_BASES_CARD_EQ = prove
 (`!(m:A matroid) s t.
        matroid_basis m s /\ matroid_basis m t ==> s =_c t`,
  REWRITE_TAC[matroid_basis; matroid_spanning] THEN
  MESON_TAC[MATROID_EQ_SPANS_CARD_EQ]);;

let MATROID_INDEPENDENT_SPANNING_FINITE = prove
 (`!(m:A matroid) s t.
        matroid_independent m s /\ matroid_spanning m t /\ FINITE t
        ==> FINITE s`,
  MESON_TAC[CARD_LE_FINITE; MATROID_INDEPENDENT_CARD_LE_SPANNING]);;

let MATROID_DEPENDENT_FINITARY_MINIMAL = prove
 (`!(m:A matroid) s.
        matroid_dependent m s
        ==> ?t. FINITE t /\ t SUBSET s /\ matroid_dependent m t /\
                forall t'. t' PSUBSET t ==> matroid_independent m t'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`] MATROID_DEPENDENT_FINITARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
    ASSUME_TAC (X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WF_PSUBSET) THEN REWRITE_TAC[WF] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\s:A->bool. s SUBSET u /\ matroid_dependent m s`) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_REFL]; MATCH_MP_TAC MONO_EXISTS] THEN
  GEN_TAC THEN STRIP_TAC THEN
  REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC]) THEN
  X_GEN_TAC `v:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:A->bool`) THEN
  REWRITE_TAC[matroid_dependent] THEN ASM SET_TAC[]);;

let MATROID_MINIMALLY_DEPENDENT = prove
 (`!(m:A matroid) s.
        (!t. t PSUBSET s ==> matroid_independent m t)
        ==> (matroid_dependent m s <=>
             ~(s = {}) /\ s SUBSET matroid_set m /\
             !a. a IN s ==> a IN matroid_span m (s DELETE a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATROID_DEPENDENT] THEN
  ASM_CASES_TAC  `(s:A->bool) SUBSET matroid_set m` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  EQ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC  `a:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `a:A = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`m:A matroid`; `s DIFF {a:A,b}`; `a:A`; `b:A`] MATROID_SPAN_EXCHANGE) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A)`) THEN
  ASM_REWRITE_TAC[matroid_independent; SET_RULE
    `s DELETE a PSUBSET s <=> a IN s`] THEN
  DISCH_THEN(MP_TAC o SPEC `b:A` o CONJUNCT2) THEN
  ASM_SIMP_TAC[IN_DELETE; SET_RULE
   `a IN s /\ b IN s /\ ~(a = b)
    ==> a INSERT (s DIFF {a, b}) = s DELETE b /\
        b INSERT  (s DIFF {a, b}) = s DELETE a`] THEN
  REWRITE_TAC[SET_RULE `s DELETE a DELETE b = s DIFF {a,b}`] THEN
  ASM SET_TAC[]);;

let MATROID_MINIMALLY_DEPENDENT_SUBSET = prove
 (`!(m:A matroid) s.
        matroid_dependent m s
        ==> ?t. FINITE t /\ t SUBSET s /\
                matroid_dependent m t /\ ~(t = {}) /\
                !a. a IN t ==> a IN matroid_span m (t DELETE a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_DEPENDENT_FINITARY_MINIMAL) THEN
  MESON_TAC[MATROID_MINIMALLY_DEPENDENT]);;

(* ------------------------------------------------------------------------- *)
(* Subspaces, i.e. sets closed under the matroid span operation.             *)
(* ------------------------------------------------------------------------- *)

let matroid_subspace = new_definition
 `matroid_subspace (m:A matroid) s <=>
        s SUBSET matroid_set m /\ matroid_span m s = s`;;

let MATROID_SUBSPACE_IMP_SUBSET = prove
 (`!(m:A matroid) s. matroid_subspace m s ==> s SUBSET matroid_set m`,
  SIMP_TAC[matroid_subspace]);;

let MATROID_SUBSPACE_SET = prove
 (`!m:A matroid. matroid_subspace m (matroid_set m)`,
  REWRITE_TAC[matroid_subspace; SUBSET_REFL; MATROID_SPAN_SET]);;

let MATROID_SUBSPACE_SPAN = prove
 (`!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> matroid_subspace m (matroid_span m s)`,
  SIMP_TAC[matroid_subspace; MATROID_SPAN_SUBSET; MATROID_SPAN_SPAN]);;

let MATROID_SUBSPACE = prove
 (`!(m:A matroid) s.
        matroid_subspace m s <=>
        s SUBSET matroid_set m /\ matroid_span m s SUBSET s`,
  REWRITE_TAC[matroid_subspace; GSYM SUBSET_ANTISYM_EQ] THEN
  MESON_TAC[MATROID_SPAN_SUPERSET]);;

let MATROID_SUBSPACE_INTERS = prove
 (`!(m:A matroid) f.
        ~(f = {}) /\ (!s. s IN f ==> matroid_subspace m s)
        ==> matroid_subspace m (INTERS f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATROID_SUBSPACE; SUBSET_INTERS] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[matroid_subspace]) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `s:A->bool` THEN STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC  `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[]);;

let MATROID_SUBSPACE_INTER = prove
 (`!(m:A matroid) s t.
        matroid_subspace m s /\ matroid_subspace m t
        ==> matroid_subspace m (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC MATROID_SUBSPACE_INTERS THEN ASM SET_TAC[]);;

let MATROID_SPAN_INTER_SPANS = prove
 (`!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (matroid_span m s INTER matroid_span m t) =
            matroid_span m s INTER matroid_span m t`,
  MESON_TAC[matroid_subspace; MATROID_SPAN_SPAN; MATROID_SPAN_SUBSET;
          MATROID_SUBSPACE_INTER]);;

let MATROID_SUBSPACE_CHAIN = prove
 (`!(m:A matroid) c.
        ~(c = {}) /\
        (!s. s IN c ==> matroid_subspace m s) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> matroid_subspace m (UNIONS c)`,
  REWRITE_TAC[matroid_subspace] THEN
  ASM_SIMP_TAC[MATROID_SPAN_CHAIN] THEN SET_TAC[]);;

let MATROID_SPAN_SUBSPACE = prove
 (`!(m:A matroid) s b.
        b SUBSET s /\ s SUBSET matroid_span m b /\ matroid_subspace m s
        ==> matroid_span m b = s`,
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  MESON_TAC[MATROID_SPAN_MINIMAL; matroid_subspace]);;

let MATROID_SPAN_EQ_SELF = prove
 (`!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> (matroid_span m s = s <=> matroid_subspace m s)`,
  SIMP_TAC[matroid_subspace]);;

let MATROID_SPAN_OF_SUBSPACE = prove
 (`!(m:A matroid) s.
        matroid_subspace m s ==> matroid_span m s = s`,
  SIMP_TAC[matroid_subspace]);;

let MATROID_SPAN_SUBSET_SUBSPACE = prove
 (`!(m:A matroid) s t.
        s SUBSET t /\ matroid_subspace m t ==> matroid_span m s SUBSET t`,
  MESON_TAC[matroid_subspace; MATROID_SPAN_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Sub-matroids                                                              *)
(* ------------------------------------------------------------------------- *)

let submatroid = new_definition
 `submatroid (m:A matroid) s =
        matroid(matroid_span m (matroid_set m INTER s),matroid_span m)`;;

let SUBMATROID_GEN = prove
 (`(!m s:A->bool. matroid_set (submatroid m s) =
                  matroid_span m (matroid_set m INTER s)) /\
   (!m s:A->bool. matroid_span (submatroid m s) = matroid_span m)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [matroid_set; matroid_span] THEN
  REWRITE_TAC[GSYM PAIR_EQ; submatroid] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 matroid_tybij)] THEN
  MP_TAC(ISPECL [`m:A matroid`; `matroid_set m INTER s:A->bool`]
        MATROID_SPAN_SUBSET) THEN
  REWRITE_TAC[INTER_SUBSET] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MATROID_SPAN_MINIMAL;
    MATCH_MP_TAC MATROID_SPAN_SUPERSET;
    MATCH_MP_TAC MATROID_SPAN_MONO;
    MATCH_MP_TAC MATROID_SPAN_SPAN;
    MATCH_MP_TAC MATROID_SPAN_FINITARY;
    MATCH_MP_TAC MATROID_SPAN_EXCHANGE] THEN
  ASM SET_TAC[]);;

let SUBMATROID = prove
 (`(!m s:A->bool.
        matroid_subspace m s ==> matroid_set (submatroid m s) = s) /\
   (!m s:A->bool. matroid_span (submatroid m s) = matroid_span m)`,
  REWRITE_TAC[SUBMATROID_GEN] THEN
  SIMP_TAC[matroid_subspace; SET_RULE `s SUBSET u ==> u INTER s = s`]);;

let SUBMATROID_SPAN = prove
 (`!m s:A->bool.
        s SUBSET matroid_set m
        ==> submatroid m (matroid_span m s) = submatroid m s`,
  SIMP_TAC[submatroid; MATROID_SPAN_SPAN; MATROID_SPAN_SUBSET;
           SET_RULE `t SUBSET s ==> s INTER t = t`]);;

let SUBMATROID_SUBSET = prove
 (`(!m s:A->bool.
        s SUBSET matroid_set m
        ==> matroid_set (submatroid m s) = matroid_span m s) /\
   (!m s:A->bool. matroid_span (submatroid m s) = matroid_span m)`,
  MESON_TAC[SUBMATROID_SPAN; SUBMATROID; MATROID_SUBSPACE_SPAN]);;

let SUBMATROID_SET = prove
 (`!m:A matroid. submatroid m (matroid_set m) = m`,
  REWRITE_TAC[submatroid; INTER_IDEMPOT; MATROID_SPAN_SET] THEN
  REWRITE_TAC[matroid_set; matroid_span; PAIR; CONJUNCT1 matroid_tybij]);;

let MATROID_INDEPENDENT_SUBMATROID = prove
 (`!(m:A matroid) s b.
        s SUBSET matroid_set m
        ==> (matroid_independent (submatroid m s) b <=>
             b SUBSET matroid_span m s /\ matroid_independent m b)`,
  SIMP_TAC[matroid_independent; SUBMATROID_SUBSET] THEN
  MESON_TAC[MATROID_SPAN_SUBSET; SUBSET_TRANS]);;

let MATROID_SPANNING_SUBMATROID = prove
 (`!(m:A matroid) s b.
       s SUBSET matroid_set m
       ==> (matroid_spanning (submatroid m s) b <=>
            b SUBSET matroid_span m s /\ matroid_span m b = matroid_span m s)`,
  SIMP_TAC[matroid_spanning; SUBMATROID_SUBSET]);;

let MATROID_SPANNING_SUBMATROID_SELF = prove
 (`!(m:A matroid) s.
       s SUBSET matroid_set m ==> matroid_spanning (submatroid m s) s`,
  SIMP_TAC[MATROID_SPANNING_SUBMATROID; MATROID_SPAN_SUPERSET]);;

let MATROID_BASIS_SUBMATROID = prove
 (`!(m:A matroid) s b.
       s SUBSET matroid_set m
       ==> (matroid_basis (submatroid m s) b <=>
            b SUBSET matroid_span m s /\
            matroid_independent m b /\
            matroid_span m b = matroid_span m s)`,
  REWRITE_TAC[matroid_basis] THEN
  SIMP_TAC[MATROID_INDEPENDENT_SUBMATROID; MATROID_SPANNING_SUBMATROID] THEN
  MESON_TAC[]);;

let MATROID_SUBSET_CONTAINS_BASIS = prove
 (`!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> ?b. b SUBSET s /\
                matroid_independent m b /\
                matroid_span m b = matroid_span m s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_SPANNING_SUBMATROID_SELF) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATROID_SPANNING_CONTAINS_BASIS) THEN
  ASM_SIMP_TAC[MATROID_BASIS_SUBMATROID] THEN MESON_TAC[]);;

let MATROID_STEINITZ_EXCHANGE_FINITE = prove
 (`!(m:A matroid) s t.
        FINITE t /\ t SUBSET matroid_set m /\
        matroid_independent m s /\ s SUBSET matroid_span m t
        ==> ?t'. t' HAS_SIZE (CARD t) /\
                 s SUBSET t' /\
                 t' SUBSET (s UNION t) /\
                 matroid_span m t' = matroid_span m t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`submatroid m (t:A->bool)`; `s:A->bool`; `t:A->bool`]
        MATROID_INTERMEDIATE_BASIS) THEN
  ASM_SIMP_TAC[MATROID_INDEPENDENT_SUBMATROID; SUBMATROID; matroid_basis;
               MATROID_SPANNING_SUBMATROID; MATROID_SPAN_SUPERSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`CARD(t:A->bool)`; `b:A->bool`; `s UNION t:A->bool`]
        CHOOSE_SUBSET_BETWEEN) THEN
  ASM_SIMP_TAC[CARD_SUBSET; SUBSET_UNION] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:A->bool` THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `t:A->bool`]
     MATROID_SPAN_UNION_EQ) THEN
    ASM_SIMP_TAC[MATROID_INDEPENDENT_IMP_SUBSET] THEN
    DISCH_THEN(SUBST1_TAC o SYM);
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th])] THEN
  MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[MATROID_SPAN_SUBSET]);;

let MATROID_STEINITZ_EXCHANGE_ALT = prove
 (`!(m:A matroid) s t.
        FINITE t /\ t SUBSET matroid_set m /\
        matroid_independent m s /\ s SUBSET matroid_span m t
        ==> ?t'. t' SUBSET t /\ CARD(t') + CARD s = CARD t /\
                 matroid_span m (s UNION t') = matroid_span m t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(A)matroid`; `s:A->bool`;`t:A->bool`]
   MATROID_STEINITZ_EXCHANGE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE];
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `t DIFF u:A->bool` THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[SUBSET_DIFF; CARD_DIFF; FINITE_DIFF] THEN
  MATCH_MP_TAC SUB_ADD THEN ASM_MESON_TAC[CARD_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Finite-dimensionality and dimension, both of whole matroid and a subset.  *)
(* ------------------------------------------------------------------------- *)

let matroid_finite_dimensional = define
 `matroid_finite_dimensional (m:A matroid) <=>
        ?b. FINITE b /\ matroid_spanning m b`;;

let matroid_dimension = define
 `matroid_dimension (m:A matroid) =
        @n. !b. matroid_basis m b ==> b HAS_SIZE n`;;

let matroid_finite_dim = define
 `matroid_finite_dim (m:A matroid) s <=>
        s SUBSET matroid_set m /\
        matroid_finite_dimensional(submatroid m s)`;;

let matroid_dim = define
 `matroid_dim (m:A matroid) s = matroid_dimension(submatroid m s)`;;

let MATROID_FINITE_DIM_IMP_SUBSET = prove
 (`!(m:A matroid) s. matroid_finite_dim m s ==> s SUBSET matroid_set m`,
  SIMP_TAC[matroid_finite_dim]);;

let MATROID_FINITE_DIM_SET = prove
 (`!(m:A matroid).
    matroid_finite_dim m (matroid_set m) = matroid_finite_dimensional m`,
  REWRITE_TAC[matroid_finite_dim; SUBMATROID_SET; SUBSET_REFL]);;

let MATROID_DIM_SET = prove
 (`!(m:A matroid).
      matroid_dim m (matroid_set m) = matroid_dimension m`,
  REWRITE_TAC[matroid_dim; SUBMATROID_SET]);;

let MATROID_FINITE_DIM_SPAN_EQ = prove
 (`!(m:A matroid) s.
        matroid_finite_dim m s <=>
        s SUBSET matroid_set m /\ matroid_finite_dim m (matroid_span m s)`,
  REWRITE_TAC[matroid_finite_dim] THEN
  MESON_TAC[SUBMATROID_SPAN; MATROID_SPAN_SUBSET]);;

let MATROID_FINITE_DIM_SPAN = prove
 (`!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> (matroid_finite_dim m (matroid_span m s) <=>
             matroid_finite_dim m s)`,
  MESON_TAC[MATROID_FINITE_DIM_SPAN_EQ]);;

let MATROID_DIM_SPAN = prove
 (`!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> matroid_dim m (matroid_span m s) = matroid_dim m s`,
  SIMP_TAC[matroid_dim; SUBMATROID_SPAN]);;

let MATROID_FINITE_DIMENSIONAL = prove
 (`!(m:A matroid).
        matroid_finite_dimensional m <=>
        ?b. FINITE b /\
            b SUBSET matroid_set m /\
            matroid_set m SUBSET matroid_span m b`,
  REWRITE_TAC[matroid_finite_dimensional; matroid_spanning] THEN
  MESON_TAC[MATROID_SPAN_EQ_SET]);;

let MATROID_FINITE_DIMENSIONAL_BASIS = prove
 (`!(m:A matroid).
        matroid_finite_dimensional m <=>
        ?b. FINITE b /\ matroid_basis m b`,
  REWRITE_TAC[matroid_finite_dimensional] THEN
  MESON_TAC[MATROID_SPANNING_CONTAINS_BASIS; FINITE_SUBSET;
            matroid_basis]);;

let MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS = prove
 (`!(m:A matroid) s.
        matroid_finite_dimensional m /\ matroid_spanning m s
        ==> ?b. FINITE b /\ b SUBSET s /\ matroid_basis m b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_SPANNING_CONTAINS_BASIS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATROID_FINITE_DIMENSIONAL_BASIS]) THEN
  ASM_MESON_TAC[MATROID_BASES_FINITE]);;

let MATROID_FINITE_DIMENSIONAL_ANY = prove
 (`!(m:A matroid) b.
        matroid_basis m b
        ==> (matroid_finite_dimensional (m:A matroid) <=> FINITE b)`,
  MESON_TAC[MATROID_FINITE_DIMENSIONAL_BASIS; MATROID_BASES_FINITE;
             MATROID_BASIS_EXISTS]);;

let [MATROID_FINITE_DIM; MATROID_FINITE_DIM_SUBSET; MATROID_FINITE_DIM_BASIS] =
    (CONJUNCTS o prove)
 (`(!(m:A matroid) s.
        matroid_finite_dim m s <=>
        ?b. FINITE b /\ b SUBSET matroid_set m /\ s SUBSET matroid_span m b) /\
   (!(m:A matroid) s.
        matroid_finite_dim m s <=>
        s SUBSET matroid_set m /\
        ?b. FINITE b /\ b SUBSET s /\ s SUBSET matroid_span m b) /\
   (!(m:A matroid) s.
        matroid_finite_dim m s <=>
        s SUBSET matroid_set m /\
        ?b. FINITE b /\
            b SUBSET s /\
            matroid_independent m b /\
            matroid_span m b = matroid_span m s)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(s ==> r) /\ (r ==> p) /\ (p ==> q) /\ (q ==> s)
    ==> (p <=> q) /\ (p <=> r) /\ (p <=> s)`) THEN
  CONJ_TAC THENL [ASM SET_TAC[MATROID_SPAN_SUPERSET]; ALL_TAC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[TAUT `p /\ q <=> ~(p ==> ~q)`]
    matroid_finite_dim] THEN
  SIMP_TAC[matroid_finite_dimensional; SUBMATROID_SUBSET;
           MATROID_SPANNING_SUBMATROID] THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    MESON_TAC[MATROID_SPAN_MINIMAL; MATROID_SPAN_SUPERSET; SUBSET_TRANS];
    MESON_TAC[SUBSET_MATROID_SPAN; MATROID_SPAN_SUBSET; SUBSET];
    DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM SET_TAC[MATROID_SPAN_SUBSET]; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_SUBSET_CONTAINS_BASIS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:A matroid`; `b:A->bool`; `c:A->bool`]
        MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE) THEN
  ASM SET_TAC[MATROID_SPAN_SUBSET; MATROID_SPAN_SUPERSET]);;

let MATROID_FINITE_DIMENSIONAL_DIM = prove
 (`!(m:A matroid) s.
        matroid_finite_dimensional m /\ s SUBSET matroid_set m
        ==> matroid_finite_dim m s`,
  REWRITE_TAC[matroid_finite_dimensional; matroid_spanning;
              MATROID_FINITE_DIM] THEN
  SET_TAC[]);;

let FINITE_IMP_MATROID_FINITE_DIM = prove
 (`!(m:A matroid) s.
        FINITE s /\ s SUBSET matroid_set m ==> matroid_finite_dim m s`,
  REWRITE_TAC[MATROID_FINITE_DIM] THEN MESON_TAC[MATROID_SPAN_SUPERSET]);;

let MATROID_FINITE_DIM_FINITE = prove
 (`!m s:A->bool.
        FINITE s ==> (matroid_finite_dim m s <=> s SUBSET matroid_set m)`,
  MESON_TAC[matroid_finite_dim; FINITE_IMP_MATROID_FINITE_DIM]);;

let MATROID_FINITE_DIM_EMPTY = prove
 (`!m:A matroid. matroid_finite_dim m {}`,
  SIMP_TAC[FINITE_IMP_MATROID_FINITE_DIM; EMPTY_SUBSET; FINITE_EMPTY]);;

let MATROID_FINITE_DIM_MONO = prove
 (`!(m:A matroid) s t.
        matroid_finite_dim m t /\ s SUBSET t ==> matroid_finite_dim m s`,
  REWRITE_TAC[MATROID_FINITE_DIM] THEN SET_TAC[]);;

let MATROID_FINITE_DIM_UNION = prove
 (`!m s t:A->bool.
        matroid_finite_dim m (s UNION t) <=>
        matroid_finite_dim m s /\ matroid_finite_dim m t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[MATROID_FINITE_DIM_MONO; SUBSET_UNION];
    REWRITE_TAC[MATROID_FINITE_DIM]] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `b UNION c:A->bool` THEN
  ASM_REWRITE_TAC[UNION_SUBSET; FINITE_UNION] THEN CONJ_TAC THEN
  ASM_MESON_TAC[MATROID_SPAN_MONO; UNION_SUBSET; SUBSET_TRANS; SUBSET_UNION]);;

let MATROID_FINITE_DIM_INSERT = prove
 (`!m s x:A.
        matroid_finite_dim m (x INSERT s) <=>
        x IN matroid_set m /\ matroid_finite_dim m s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE`a INSERT s = {a} UNION s`] THEN
  SIMP_TAC[MATROID_FINITE_DIM_UNION; MATROID_FINITE_DIM_FINITE; FINITE_SING;
           SING_SUBSET]);;

let MATROID_DIMENSION_ALT = prove
 (`!m:A matroid.
        matroid_dimension m = @n. ?b. matroid_basis m b /\ b HAS_SIZE n`,
  GEN_TAC THEN REWRITE_TAC[matroid_dimension] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  MESON_TAC[MATROID_BASES_SIZE; MATROID_BASIS_EXISTS]);;

let MATROID_DIM_BASIS = prove
 (`!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> (matroid_dim m s =
             @n. ?b. b SUBSET s /\
                     matroid_independent m b /\
                     matroid_span m b = matroid_span m s /\
                     b HAS_SIZE n)`,
  REWRITE_TAC[matroid_dim; MATROID_DIMENSION_ALT] THEN
  SIMP_TAC[MATROID_BASIS_SUBMATROID] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_SUBSET_CONTAINS_BASIS) THEN
  ASM_MESON_TAC[MATROID_EQ_SPANS_SIZE; MATROID_SPAN_SUPERSET; SUBSET_TRANS]);;

let MATROID_DIM_ALT = prove
 (`!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> (matroid_dim m s =
             @n. ?b. b SUBSET s /\
                     matroid_independent m b /\
                     s SUBSET matroid_span m b /\
                     b HAS_SIZE n)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATROID_DIM_BASIS] THEN
  REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC) THEN
  ASM_MESON_TAC[MATROID_SPAN_EQ; MATROID_SPAN_MINIMAL; SUBSET_TRANS]);;

let MATROID_DIMENSION_UNIQUE = prove
 (`!(m:A matroid) b n.
        matroid_basis m b /\ b HAS_SIZE n ==> matroid_dimension m = n`,
  REWRITE_TAC[matroid_dimension] THEN
  MESON_TAC[MATROID_BASES_SIZE; HAS_SIZE]);;

let MATROID_DIMENSION_EQ_CARD = prove
 (`!(m:A matroid) b.
        matroid_basis m b /\ FINITE b ==> matroid_dimension m = CARD b`,
  MESON_TAC[MATROID_DIMENSION_UNIQUE; HAS_SIZE]);;

let MATROID_DIM_UNIQUE_ALT = prove
 (`!(m:A matroid) s b n.
        s SUBSET matroid_set m /\ b SUBSET matroid_set m /\ b HAS_SIZE n /\
        matroid_independent m b /\ matroid_span m b = matroid_span m s
        ==> matroid_dim m s = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[matroid_dim] THEN
  MATCH_MP_TAC MATROID_DIMENSION_UNIQUE THEN EXISTS_TAC `b:A->bool` THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET matroid_set m` ASSUME_TAC THENL
   [ASM_MESON_TAC[MATROID_SPAN_SUBSET; SUBSET_TRANS];
    ASM_SIMP_TAC[MATROID_BASIS_SUBMATROID]] THEN
  ASM_MESON_TAC[MATROID_SPAN_SUPERSET]);;

let MATROID_DIM_UNIQUE = prove
 (`!(m:A matroid) s b n.
        b SUBSET s /\ b HAS_SIZE n /\
        matroid_independent m b /\ s SUBSET matroid_span m b
        ==> matroid_dim m s = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_DIM_UNIQUE_ALT THEN
  EXISTS_TAC `b:A->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
  ASM_MESON_TAC[MATROID_SPAN_EQ; MATROID_SPAN_SUBSET; SUBSET_TRANS]);;

let MATROID_SPAN_DIM_EQ = prove
 (`!m s t:A->bool.
        s SUBSET matroid_set m /\
        t SUBSET matroid_set m /\
        matroid_span m s = matroid_span m t
        ==> matroid_dim m s = matroid_dim m t`,
  MESON_TAC[MATROID_DIM_SPAN]);;

let MATROID_SPAN_INSERT_REFL = prove
 (`!m s x:A.
        s SUBSET matroid_set m /\ x IN matroid_span m s
        ==> matroid_span m (x INSERT s) = matroid_span m s`,
  MESON_TAC[MATROID_SPAN_INSERT_EQ; MATROID_SPAN_SUBSET; SUBSET]);;

let MATROID_BASIS_EXISTS_DIMENSION = prove
 (`!m:A matroid.
        matroid_finite_dimensional m <=>
        ?b. b HAS_SIZE matroid_dimension m /\ matroid_basis m b`,
  REWRITE_TAC[MATROID_FINITE_DIMENSIONAL_BASIS; HAS_SIZE] THEN
  MESON_TAC[MATROID_DIMENSION_UNIQUE; HAS_SIZE]);;

let MATROID_BASIS_EXISTS_DIM = prove
 (`!m s:A->bool.
        matroid_finite_dim m s <=>
        s SUBSET matroid_set m /\
        ?b. b HAS_SIZE matroid_dim m s /\
            b SUBSET matroid_span m s /\
            matroid_independent m b /\
            matroid_span m b = matroid_span m s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matroid_finite_dim] THEN
  ASM_CASES_TAC `(s:A->bool) SUBSET matroid_set m` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MATROID_BASIS_EXISTS_DIMENSION; MATROID_BASIS_SUBMATROID] THEN
  MESON_TAC[matroid_dim]);;

let MATROID_CONTAINS_BASIS_DIM = prove
 (`!m s:A->bool.
        matroid_finite_dim m s <=>
        s SUBSET matroid_set m /\
        ?b. b HAS_SIZE matroid_dim m s /\
            b SUBSET s /\
            matroid_independent m b /\
            matroid_span m b = matroid_span m s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATROID_FINITE_DIM_BASIS; HAS_SIZE] THEN
  ASM_CASES_TAC `(s:A->bool) SUBSET matroid_set m` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MATROID_DIM_UNIQUE_ALT; HAS_SIZE; SUBSET]);;

let MATROID_DIM_EQ_CARD_GEN = prove
 (`!(m:A matroid) s b.
        b SUBSET s /\ FINITE b /\
        matroid_independent m b /\ s SUBSET matroid_span m b
        ==> matroid_dim m s = CARD b`,
  MESON_TAC[MATROID_DIM_UNIQUE; HAS_SIZE]);;

let MATROID_DIM_EQ_CARD = prove
 (`!(m:A matroid) b.
        FINITE b /\ matroid_independent m b
        ==> matroid_dim m b = CARD b`,
  MESON_TAC[MATROID_DIM_EQ_CARD_GEN; MATROID_INDEPENDENT_IMP_SUBSET;
            SUBSET_REFL; MATROID_SPAN_SUPERSET]);;

let MATROID_DIMENSION_LE = prove
 (`!(m:A matroid) b n.
        b SUBSET matroid_set m /\ matroid_set m SUBSET matroid_span m b /\
        FINITE b /\ CARD b <= n
        ==> matroid_dimension m <= n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_SUBSET_CONTAINS_BASIS) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
  TRANS_TAC LE_TRANS `CARD(c:A->bool)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE; ASM_MESON_TAC[CARD_SUBSET; LE_TRANS]] THEN
  MATCH_MP_TAC MATROID_DIMENSION_UNIQUE THEN
  EXISTS_TAC `c:A->bool` THEN ASM_REWRITE_TAC[matroid_basis; HAS_SIZE] THEN
  ASM_REWRITE_TAC[MATROID_SPANNING_ALT] THEN
  ASM_MESON_TAC[FINITE_SUBSET; SUBSET_TRANS]);;

let MATROID_DIMENSION_FINITE_LE = prove
 (`!(m:A matroid) b n.
        b SUBSET matroid_set m /\ matroid_set m SUBSET matroid_span m b /\
        FINITE b /\ CARD b <= n
        ==> matroid_finite_dimensional m /\ matroid_dimension m <= n`,
  MESON_TAC[MATROID_DIMENSION_LE; MATROID_FINITE_DIMENSIONAL]);;

let MATROID_DIM_LE = prove
 (`!(m:A matroid) s b n.
        FINITE b /\ CARD b <= n /\
        b SUBSET matroid_set m /\ s SUBSET matroid_span m b
        ==> matroid_dim m s <= n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET matroid_set m` ASSUME_TAC THENL
   [ASM_MESON_TAC[MATROID_SPAN_SUBSET; SUBSET_TRANS];
    FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_SUBSET_CONTAINS_BASIS)] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:A matroid`; `c:A->bool`; `b:A->bool`]
          MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `c:A->bool`]
         MATROID_DIM_EQ_CARD_GEN) THEN
  ASM_SIMP_TAC[MATROID_SPAN_SUPERSET] THEN ASM_ARITH_TAC);;

let MATROID_DIM_FINITE_LE = prove
 (`!(m:A matroid) s b n.
        FINITE b /\ CARD b <= n /\
        b SUBSET matroid_set m /\ s SUBSET matroid_span m b
        ==> matroid_finite_dim m s /\ matroid_dim m s <= n`,
  MESON_TAC[MATROID_DIM_LE; MATROID_FINITE_DIM]);;

let MATROID_DIM_LE_CARD_GEN = prove
 (`!(m:A matroid) s b.
        FINITE b /\
        b SUBSET matroid_set m /\ s SUBSET matroid_span m b
        ==> matroid_dim m s <= CARD b`,
  MESON_TAC[MATROID_DIM_LE; LE_REFL; HAS_SIZE]);;

let MATROID_DIM_LE_CARD = prove
 (`!(m:A matroid) s.
        FINITE s /\ s SUBSET matroid_set m ==> matroid_dim m s <= CARD s`,
  MESON_TAC[MATROID_DIM_LE_CARD_GEN; MATROID_SPAN_SUPERSET]);;

let MATROID_DIMENSION_GE_FINITE_CARD = prove
 (`!(m:A matroid) b.
        matroid_finite_dimensional m /\
        matroid_independent m b
        ==> FINITE b /\ CARD b <= matroid_dimension m`,
  ASM_MESON_TAC[MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE; matroid_basis;
                MATROID_FINITE_DIMENSIONAL_BASIS; matroid_spanning;
                MATROID_INDEPENDENT_IMP_SUBSET; MATROID_DIMENSION_EQ_CARD]);;

let MATROID_DIMENSION_GE = prove
 (`!(m:A matroid) b n.
        matroid_finite_dimensional m /\
        matroid_independent m b /\
        n <= CARD b
        ==> n <= matroid_dimension m`,
  MESON_TAC[MATROID_DIMENSION_GE_FINITE_CARD; LE_TRANS]);;

let MATROID_DIMENSION_GE_CARD = prove
 (`!(m:A matroid) b.
        matroid_finite_dimensional m /\ matroid_independent m b
        ==> CARD b <= matroid_dimension m`,
  MESON_TAC[MATROID_DIMENSION_GE_FINITE_CARD]);;

let MATROID_DIM_GE_FINITE_CARD = prove
 (`!(m:A matroid) s b.
        matroid_finite_dim m s /\ matroid_independent m b /\ b SUBSET s
        ==> FINITE b /\ CARD b <= matroid_dim m s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[matroid_dim] THEN
  MATCH_MP_TAC MATROID_DIMENSION_GE_FINITE_CARD THEN
  ASM_MESON_TAC[matroid_finite_dim; MATROID_INDEPENDENT_SUBMATROID;
                MATROID_SPAN_SUPERSET; SUBSET_TRANS]);;

let MATROID_DIM_GE = prove
 (`!(m:A matroid) s b n.
        matroid_finite_dim m s /\ matroid_independent m b /\
        b SUBSET s /\ n <= CARD b
        ==> n <= matroid_dim m s`,
  MESON_TAC[MATROID_DIM_GE_FINITE_CARD; LE_TRANS]);;

let MATROID_DIM_GE_CARD_GEN = prove
 (`!(m:A matroid) s b.
        matroid_finite_dim m s /\ matroid_independent m b /\ b SUBSET s
        ==> CARD b <= matroid_dim m s`,
  MESON_TAC[MATROID_DIM_GE_FINITE_CARD; LE_TRANS]);;

let MATROID_DIM_GE_CARD = prove
 (`!(m:A matroid) s.
        matroid_finite_dim m s /\ matroid_independent m s
        ==> CARD s <= matroid_dim m s`,
  MESON_TAC[MATROID_DIM_GE_CARD_GEN; SUBSET_REFL]);;

let FINITE_IMP_MATROID_FINITE_DIM_SPAN = prove
 (`!(m:A matroid) s.
        FINITE s /\ s SUBSET matroid_set m
        ==> matroid_finite_dim m (matroid_span m s)`,
  MESON_TAC[MATROID_FINITE_DIM_SPAN; FINITE_IMP_MATROID_FINITE_DIM]);;

let MATROID_INDEPENDENT_IMP_FINITE = prove
 (`!(m:A matroid) s.
        matroid_finite_dim m s /\ matroid_independent m s
        ==> FINITE s`,
  MESON_TAC[MATROID_DIM_GE_FINITE_CARD; SUBSET_REFL]);;

let MATROID_DIM_EQ_FINITE_CARD_EQ,MATROID_DIM_GE_FINITE_CARD_EQ =
 (CONJ_PAIR o prove)
 (`(!m s:A->bool.
        s SUBSET matroid_set m /\ FINITE s /\ matroid_dim m s = CARD s <=>
        matroid_finite_dim m s /\ matroid_independent m s) /\
   (!m s:A->bool.
        s SUBSET matroid_set m /\ FINITE s /\ CARD s <= matroid_dim m s <=>
        matroid_finite_dim m s /\ matroid_independent m s)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (r ==> p) /\ (q ==> r) ==> (p <=> r) /\ (q <=> r)`) THEN
  SIMP_TAC[LE_REFL] THEN CONJ_TAC THENL
   [MESON_TAC[MATROID_FINITE_DIM_IMP_SUBSET; MATROID_INDEPENDENT_IMP_FINITE;
              SUBSET_REFL; MATROID_DIM_EQ_CARD];
    STRIP_TAC THEN ASM_SIMP_TAC[FINITE_IMP_MATROID_FINITE_DIM]] THEN
  MP_TAC(ISPECL [`submatroid m (s:A->bool)`; `s:A->bool`]
        MATROID_BASIS_EQ_MINIMAL_SPANNING) THEN
  ASM_SIMP_TAC[MATROID_BASIS_SUBMATROID; MATROID_SPANNING_SUBMATROID;
               MATROID_SPAN_SUPERSET] THEN
  DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `t:A->bool` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `t:A->bool`]
    MATROID_DIM_LE_CARD_GEN) THEN
  ASM_MESON_TAC[MATROID_SPAN_SUPERSET; SUBSET; PSUBSET; FINITE_SUBSET;
                CARD_PSUBSET; NOT_LT; LE_TRANS]);;

let MATROID_DIM_EMPTY = prove
 (`!m:A matroid. matroid_dim m {} = 0`,
  GEN_TAC THEN MATCH_MP_TAC MATROID_DIM_UNIQUE THEN
  EXISTS_TAC `{}:A->bool` THEN
  REWRITE_TAC[MATROID_INDEPENDENT_EMPTY; HAS_SIZE; FINITE_RULES; CARD_CLAUSES;
              EMPTY_SUBSET]);;

let MATROID_DIM_INSERT = prove
 (`!m s x:A.
        matroid_finite_dim m s /\ x IN matroid_set m
        ==> matroid_dim m (x INSERT s) =
            if x IN matroid_span m s then matroid_dim m s
            else matroid_dim m s + 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MATROID_FINITE_DIM_IMP_SUBSET) THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[MATROID_SPAN_INSERT_REFL; MATROID_SPAN_DIM_EQ;
                  INSERT_SUBSET; MATROID_SPAN_SUBSET; SUBSET];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATROID_CONTAINS_BASIS_DIM])] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; HAS_SIZE] THEN
  X_GEN_TAC `b:A->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC MATROID_DIM_UNIQUE THEN EXISTS_TAC `(x:A) INSERT b` THEN
  ASM_REWRITE_TAC[HAS_SIZE; FINITE_INSERT; MATROID_INDEPENDENT_INSERT] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; INSERT_SUBSET] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[MATROID_SPAN_SUPERSET; SUBSET]; REWRITE_TAC[ADD1]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MATROID_SPAN_INC THEN ASM SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC SUBSET_TRANS `matroid_span m b:A->bool` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[MATROID_SPAN_SUPERSET];
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC[]]);;

let MATROID_DIM_SUBSET = prove
 (`!m s t:A->bool.
        s SUBSET t /\ matroid_finite_dim m t
        ==> matroid_dim m s <= matroid_dim m t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATROID_FINITE_DIM_BASIS]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `b:A->bool` (STRIP_ASSUME_TAC o GSYM))) THEN
  MP_TAC(ISPECL [`m:A matroid`; `s:A->bool`; `b:A->bool`; `CARD(b:A->bool)`]
        MATROID_DIM_FINITE_LE) THEN
  MP_TAC(ISPECL [`m:A matroid`; `b:A->bool`] MATROID_DIM_EQ_CARD) THEN
  MP_TAC(ISPECL [`m:A matroid`; `t:A->bool`] MATROID_DIM_SPAN) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  ASM SET_TAC[MATROID_DIM_SPAN; MATROID_SPAN_SUPERSET]);;

let MATROID_DIM_SUBSET_ALT = prove
 (`!m s t:A->bool.
        s SUBSET matroid_span m t /\ matroid_finite_dim m t
        ==> matroid_dim m s <= matroid_dim m t`,
  MESON_TAC[MATROID_DIM_SUBSET; MATROID_FINITE_DIM_SPAN; MATROID_DIM_SPAN;
            MATROID_FINITE_DIM_IMP_SUBSET]);;

let MATROID_DIM_SPAN_SUBSET = prove
 (`!m s t:A->bool.
        s SUBSET matroid_set m /\
        matroid_span m s SUBSET matroid_span m t /\
        matroid_finite_dim m t
        ==> matroid_dim m s <= matroid_dim m t`,
  MESON_TAC[MATROID_SPAN_MINIMAL; MATROID_DIM_SPAN; MATROID_DIM_SUBSET_ALT;
            MATROID_FINITE_DIM_IMP_SUBSET]);;

let MATROID_DIM_SPAN_PSUBSET = prove
 (`!m s t:A->bool.
        s SUBSET matroid_set m /\
        matroid_span m s PSUBSET matroid_span m t /\
        matroid_finite_dim m t
        ==> matroid_dim m s < matroid_dim m t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MATROID_FINITE_DIM_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `matroid_finite_dim m (s:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MATROID_FINITE_DIM_SPAN; MATROID_FINITE_DIM_MONO];
    ALL_TAC] THEN
  ASM_CASES_TAC `(a:A) IN matroid_set m` THENL
   [ALL_TAC; ASM_MESON_TAC[MATROID_SPAN_SUBSET; SUBSET]] THEN
  TRANS_TAC LTE_TRANS `matroid_dim m ((a:A) INSERT s)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MATROID_DIM_INSERT; ARITH_RULE `n < n + 1`]; ALL_TAC] THEN
  TRANS_TAC LE_TRANS `matroid_dim m (matroid_span m t:A->bool)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[MATROID_DIM_SPAN; LE_REFL]] THEN
  MATCH_MP_TAC MATROID_DIM_SUBSET THEN
  ASM_SIMP_TAC[MATROID_FINITE_DIM_SPAN; INSERT_SUBSET] THEN
  ASM_MESON_TAC[MATROID_SPAN_SUPERSET; SUBSET_TRANS]);;

let MATROID_DIM_SPAN_EQ_GEN = prove
 (`!m s t:A->bool.
        s SUBSET matroid_set m /\ matroid_finite_dim m t /\
        matroid_span m s SUBSET matroid_span m t /\
        matroid_dim m t <= matroid_dim m s
        ==> matroid_span m s = matroid_span m t`,
  MESON_TAC[MATROID_DIM_SPAN_PSUBSET; PSUBSET; NOT_LT]);;

let MATROID_DIM_SPAN_EQ = prove
 (`!m s t:A->bool.
        s SUBSET matroid_set m /\ matroid_finite_dim m t /\
        matroid_span m s SUBSET matroid_span m t /\
        matroid_dim m s = matroid_dim m t
        ==> matroid_span m s = matroid_span m t`,
  MESON_TAC[MATROID_DIM_SPAN_PSUBSET; PSUBSET; LT_REFL]);;

let MATROID_DIM_EQ_SPAN = prove
 (`!m s t:A->bool.
     matroid_finite_dim m t /\ s SUBSET t /\ matroid_dim m t <= matroid_dim m s
     ==> matroid_span m s = matroid_span m t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_DIM_SPAN_EQ_GEN THEN
  ASM_MESON_TAC[MATROID_SPAN_MONO; MATROID_FINITE_DIM_IMP_SUBSET; SUBSET]);;

let MATROID_CHOOSE_SUBSET = prove
 (`!(m:A matroid) s n.
        s SUBSET matroid_set m /\
        (matroid_finite_dim m s ==> n <= matroid_dim m s)
        ==> ?t. t SUBSET s /\ matroid_independent m t /\ t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC o MATCH_MP
    MATROID_SUBSET_CONTAINS_BASIS) THEN
  MP_TAC(ISPECL [`n:num`; `b:A->bool`] CHOOSE_SUBSET_STRONG) THEN ANTS_TAC
  THENL [DISCH_TAC; ASM_MESON_TAC[MATROID_INDEPENDENT_MONO; SUBSET]] THEN
  ASM_SIMP_TAC[GSYM MATROID_DIM_EQ_CARD] THEN
  ASM_MESON_TAC[MATROID_FINITE_DIM_BASIS; MATROID_SPAN_DIM_EQ; SUBSET]);;

let MATROID_CHOOSE_SUBSPACE = prove
 (`!(m:A matroid) s n.
        s SUBSET matroid_set m /\
        (matroid_finite_dim m s ==> n <= matroid_dim m s)
        ==> ?t. matroid_subspace m t /\ t SUBSET matroid_span m s /\
                matroid_finite_dim m t /\ matroid_dim m t = n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[HAS_SIZE] o MATCH_MP MATROID_CHOOSE_SUBSET) THEN
  EXISTS_TAC `matroid_span m b:A->bool` THEN
  SUBGOAL_THEN `(b:A->bool) SUBSET matroid_set m` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATROID_SUBSPACE_SPAN; MATROID_SPAN_MONO; MATROID_DIM_EQ_CARD;
   MATROID_FINITE_DIM_SPAN; MATROID_DIM_SPAN; FINITE_IMP_MATROID_FINITE_DIM]);;

let MATROID_LOWDIM_EXPAND_BASIS = prove
 (`!m (s:A->bool) n.
        matroid_finite_dim m s /\ matroid_dim m s <= n /\
        (matroid_finite_dimensional m ==> n <= matroid_dimension m)
        ==> ?b. b HAS_SIZE n /\ matroid_independent m b /\
                matroid_span m s SUBSET matroid_span m b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o
    GEN_REWRITE_RULE I [MATROID_FINITE_DIM_BASIS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d:A->bool` STRIP_ASSUME_TAC o
        MATCH_MP MATROID_INDEPENDENT_EXTENDS_TO_BASIS) THEN
  MP_TAC(ISPECL [`n:num`; `b:A->bool`; `d:A->bool`]
        CHOOSE_SUBSET_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[MATROID_DIM_EQ_CARD; MATROID_SPAN_DIM_EQ; SUBSET];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[matroid_finite_dimensional; matroid_basis];
      ASM_MESON_TAC[MATROID_DIMENSION_UNIQUE; HAS_SIZE]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:A->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[matroid_basis; MATROID_INDEPENDENT_MONO];
      ASM_MESON_TAC[MATROID_SPAN_MONO; SUBSET; MATROID_BASIS_IMP_SUBSET]]]);;

let MATROID_LOWDIM_EXPAND_DIMENSION = prove
 (`!m (s:A->bool) n.
        matroid_finite_dim m s /\ matroid_dim m s <= n /\
        (matroid_finite_dimensional m ==> n <= matroid_dimension m)
        ==> ?t. matroid_finite_dim m t /\ matroid_dim m t = n /\
                matroid_span m s SUBSET matroid_span m t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATROID_LOWDIM_EXPAND_BASIS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:A->bool` THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATROID_DIM_EQ_CARD; FINITE_IMP_MATROID_FINITE_DIM;
               MATROID_INDEPENDENT_IMP_SUBSET]);;
