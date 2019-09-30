(* ========================================================================= *)
(* Propositional logic as subsystem of FOL, leading to compactness.          *)
(* ========================================================================= *)

let pholds = new_recursive_definition form_RECURSION
  `(pholds v False <=> F) /\
   (pholds v (Atom p l) <=> v (Atom p l)) /\
   (pholds v (q --> r) <=> pholds v q ==> pholds v r) /\
   (pholds v (!!x q) <=> v (!!x q))`;;

let PHOLDS = prove
 (`(pholds v False <=> F) /\
   (pholds v True <=> T) /\
   (pholds v (Atom p l) <=> v (Atom p l)) /\
   (pholds v (Not q) <=> ~(pholds v q)) /\
   (pholds v (q || r) <=> pholds v q \/ pholds v r) /\
   (pholds v (q && r) <=> pholds v q /\ pholds v r) /\
   (pholds v (q --> r) <=> pholds v q ==> pholds v r) /\
   (pholds v (q <-> r) <=> (pholds v q = pholds v r))`,
  REWRITE_TAC
   [True_DEF; Not_DEF; Or_DEF; And_DEF; Iff_DEF; Exists_DEF; pholds] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Propositional satisfaction.                                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("psatisfies",(10,"right"));;

let psatisfies = new_definition
  `v psatisfies s <=> !p. p IN s ==> pholds v p`;;

let psatisfiable = new_definition
  `psatisfiable s <=> ?v. !p. p IN s ==> pholds v p`;;

let PSATISFIABLE_MONO = prove
 (`!A B. psatisfiable A /\ B SUBSET A ==> psatisfiable B`,
  REWRITE_TAC[psatisfiable] THEN MESON_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Extensibility of finitely satisfiable set.                                *)
(* ------------------------------------------------------------------------- *)

let finsat = new_definition
  `finsat A <=> !B. B SUBSET A /\ FINITE(B) ==> psatisfiable B`;;

let FINSAT_MONO = prove
 (`!A B. finsat A /\ B SUBSET A ==> finsat B`,
  REWRITE_TAC[finsat] THEN MESON_TAC[SUBSET_TRANS; FINITE_SUBSET]);;

let SATISFIABLE_MONO = prove
 (`!A B. psatisfiable A /\ B SUBSET A ==> psatisfiable B`,
  REWRITE_TAC[psatisfiable] THEN MESON_TAC[SUBSET]);;

let FINSAT_SATISFIABLE = prove
 (`psatisfiable B ==> finsat B`,
  REWRITE_TAC[finsat] THEN
  MESON_TAC[SATISFIABLE_MONO; SUBSET_TRANS; FINITE_SUBSET]);;

let FINSAT_MAX = prove
 (`!A. finsat(A) ==> ?B. A SUBSET B /\ finsat(B) /\
                         !C. B SUBSET C /\ finsat(C) ==> (C = B)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\B C. A SUBSET B /\ B SUBSET C /\ finsat(C)` ZL) THEN
  PBETA_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `poset (\B C. A SUBSET B /\ B SUBSET C /\ finsat(C))`
  ASSUME_TAC THENL
   [REWRITE_TAC[poset; fl] THEN PBETA_TAC THEN
    MESON_TAC[SUBSET_TRANS; SUBSET_REFL; FINSAT_MONO; SUBSET_ANTISYM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `fl(\B C. A SUBSET B /\ B SUBSET C /\ finsat(C)) =
                 \B. A SUBSET B /\ finsat(B)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; fl] THEN PBETA_TAC THEN
    MESON_TAC[SUBSET_TRANS; FINSAT_MONO; SUBSET_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ALL_TAC; MESON_TAC[SUBSET_TRANS]] THEN
  X_GEN_TAC `C:(form->bool)->bool` THEN
  REWRITE_TAC[chain] THEN PBETA_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `C:(form->bool)->bool = EMPTY` THENL
   [EXISTS_TAC `A:form->bool` THEN ASM_REWRITE_TAC[EMPTY; SUBSET_REFL];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS (C:(form->bool)->bool)` THEN
  FIRST_ASSUM(X_CHOOSE_THEN `u:form->bool` MP_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN REWRITE_TAC[IN] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `A:form->bool SUBSET (UNIONS C)` ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET; IN];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `!B:form->bool. FINITE B ==> B SUBSET (UNIONS C)
                               ==> ?U. U IN C /\ B SUBSET U`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[EMPTY_SUBSET] THEN ASM_MESON_TAC[IN]; ALL_TAC] THEN
    X_GEN_TAC `p:form` THEN X_GEN_TAC `W:form->bool` THEN
    ASM_CASES_TAC `(p:form INSERT W) SUBSET (UNIONS C)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `W:form->bool SUBSET (UNIONS C)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_INSERT; IN]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[IN; SUBSET; INSERT; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:form->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `p:form INSERT W SUBSET UNIONS C` THEN
    REWRITE_TAC[IN_INSERT; SUBSET; UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:form`) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[IN] THEN
    DISCH_THEN(X_CHOOSE_THEN `v2:form->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v1:form->bool`; `v2:form->bool`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `v2:form->bool` THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN]) THEN ASM_MESON_TAC[];
      EXISTS_TAC `v1:form->bool` THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `finsat (UNIONS C :form->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[finsat] THEN X_GEN_TAC `B:form->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `B:form->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:form->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:form->bool`; `v:form->bool`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[finsat];
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:form->bool` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; UNIONS; IN_ELIM_THM; IN] THEN
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Compactness.                                                              *)
(* ------------------------------------------------------------------------- *)

let FINSAT_EXTEND = prove
 (`finsat(B) ==> finsat(p INSERT B) \/ finsat(Not p INSERT B)`,
  REWRITE_TAC[finsat] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~ p`] THEN DISCH_THEN
   (MP_TAC o REWRITE_RULE[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `C:form->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `D:form->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(C DELETE p) UNION (D DELETE Not p)`) THEN
  ASM_REWRITE_TAC[NOT_IMP; FINITE_UNION; FINITE_DELETE] THEN CONJ_TAC THENL
   [ASSUM_LIST SET_TAC;
    UNDISCH_TAC `~(psatisfiable C)` THEN UNDISCH_TAC `~(psatisfiable D)` THEN
    REWRITE_TAC[psatisfiable; IN_DELETE; IN_UNION] THEN
    REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP] THEN
    REPEAT DISCH_TAC THEN X_GEN_TAC `v:form->bool` THEN
    UNDISCH_TAC `!v. ?p. p IN C /\ ~pholds v p` THEN
    DISCH_THEN(MP_TAC o SPEC `v:form->bool`) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:form` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `p:form = q` THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:form->bool`) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:form` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:form` THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~pholds v (Not q)` THEN ASM_REWRITE_TAC[PHOLDS]]);;

let FINSAT_MAX_COMPLETE = prove
 (`finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. p IN B \/ Not(p) IN B`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP FINSAT_EXTEND) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  REWRITE_TAC[ABSORPTION] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let FINSAT_MAX_COMPLETE_STRONG = prove
 (`finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. Not(p) IN B <=> ~(p IN B)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(a \/ b) /\ ~(a /\ b) ==> (b <=> ~a)`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FINSAT_MAX_COMPLETE]; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `finsat B` THEN
  REWRITE_TAC[finsat] THEN
  DISCH_THEN(MP_TAC o SPEC `{ p, (Not p) }`) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[psatisfiable; IN_INSERT; SUBSET; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
  REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2; PHOLDS] THEN
  CONV_TAC TAUT);;

let FINSAT_DEDUCTION = prove
 (`finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. p IN B <=> ?A. FINITE(A) /\ A SUBSET B /\
                        !v. (!q. q IN A ==> pholds v q) ==> pholds v p`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `{p:form}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN
    REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    STRIP_TAC THEN REWRITE_TAC[ABSORPTION] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `finsat B` THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[finsat; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `A1:form->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(A:form->bool) UNION (A1 DELETE p)` THEN
    ASM_REWRITE_TAC[FINITE_UNION; FINITE_DELETE] THEN
    CONJ_TAC THENL [ASSUM_LIST SET_TAC; ALL_TAC] THEN
    UNDISCH_TAC `!v. (!q. q IN A ==> pholds v q) ==> pholds v p` THEN
    UNDISCH_TAC `~(psatisfiable A1)` THEN
    REWRITE_TAC[psatisfiable; IN_UNION; IN_DELETE] THEN
    MESON_TAC[]]);;

let FINSAT_MAX_CONSISTENT = prove
 (`finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> ~(False IN B)`,
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[finsat] THEN
  DISCH_THEN(MP_TAC o SPEC `{False}`) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_RULES; psatisfiable] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_IMP; NOT_FORALL_THM; NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[PHOLDS]);;

let FINSAT_MAX_HOMO = prove
 (`finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p q. (p --> q) IN B <=> p IN B ==> q IN B`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FINSAT_DEDUCTION th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `A1:form->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `A2:form->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(A1:form->bool) UNION A2` THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN
    CONJ_TAC THENL [ASSUM_LIST SET_TAC; ALL_TAC] THEN
    UNDISCH_TAC `!v. (!q. q IN A2 ==> pholds v q) ==> pholds v p` THEN
    UNDISCH_TAC `!v. (!q. q IN A1 ==> pholds v q) ==> pholds v (p --> q)` THEN
    REWRITE_TAC[entails; IN_UNION; PHOLDS] THEN MESON_TAC[];
    GEN_REWRITE_TAC LAND_CONV [TAUT `p ==> q <=> ~p \/ q`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC
     [GSYM(MATCH_MP FINSAT_MAX_COMPLETE_STRONG th)]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FINSAT_DEDUCTION th]) THEN
    STRIP_TAC THEN EXISTS_TAC `A:form->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
    REWRITE_TAC[PHOLDS] THEN MESON_TAC[]]);;

let COMPACT_PROP = prove
 (`(!B. FINITE(B) /\ B SUBSET A
        ==> ?d. !r. r IN B ==> pholds(d) r)
   ==> ?d. !r. r IN A ==> pholds(d) r`,
  STRIP_TAC THEN
  SUBGOAL_THEN `finsat(A)` (MP_TAC o MATCH_MP FINSAT_MAX) THENL
   [REWRITE_TAC[finsat; psatisfiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:form->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  EXISTS_TAC `\p:form. p IN B` THEN
  SUBGOAL_THEN `!r. pholds (\p. p IN B) r <=> r IN B`
   (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[pholds] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FINSAT_MAX_CONSISTENT th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FINSAT_MAX_HOMO th]) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Important variant used in proving Uniformity for FOL.                     *)
(* ------------------------------------------------------------------------- *)

let COMPACT_PROP_ALT = prove
 (`!A. (!d. ?p. p IN A /\ pholds d p)
       ==> ?B. FINITE(B) /\ B SUBSET A /\ (!d. ?p. p IN B /\ pholds d p)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(?d. !r. r IN { Not q | q IN A } ==> pholds(d) r)`
  MP_TAC THENL
   [REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP] THEN
    REWRITE_TAC[IN_ELIM_THM; Not_DEF] THEN ASM_MESON_TAC[pholds]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM] COMPACT_PROP)) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:form->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{ r | Not r IN B }` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[Not_DEF; form_INJ];
    UNDISCH_TAC `B SUBSET {Not q | q IN A}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      REWRITE_TAC[Not_DEF; form_INJ] THEN MESON_TAC[];
      ASM_MESON_TAC[el 3 (CONJUNCTS PHOLDS)]]]);;

let FINITE_DISJ_LEMMA = prove
 (`!A. FINITE(A) ==> ?ps. ALL (\p. p IN A) ps /\
                          !d. pholds(d) (ITLIST (||) ps False) <=>
                              ?p. p IN A /\ pholds d p`,
  MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [EXISTS_TAC `[] :form list` THEN REWRITE_TAC[ALL; ITLIST] THEN
    REWRITE_TAC[pholds; NOT_IN_EMPTY];
    X_GEN_TAC `q:form` THEN X_GEN_TAC `s:form->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `ps:form list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `CONS (q:form) ps` THEN REWRITE_TAC[ALL; ITLIST] THEN
    ASM_REWRITE_TAC[PHOLDS; IN_INSERT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\p:form. p IN s` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MESON_TAC[]]]);;

let COMPACT_DISJ = prove
 (`!A. (!d. ?p. p IN A /\ pholds d p)
       ==> ?ps. ALL (\p. p IN A) ps /\
                !d. pholds(d) (ITLIST (||) ps False)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_PROP_ALT) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:form->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `ps:form list` STRIP_ASSUME_TAC o
    MATCH_MP FINITE_DISJ_LEMMA) THEN
  EXISTS_TAC `ps:form list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\p:form. p IN B` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]);;
