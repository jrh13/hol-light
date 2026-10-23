(* ========================================================================= *)
(* Soundness and completeness of first-order logic for the language of set   *)
(* theory, and the syntactic consistency of ZFC + GCH, ZFC + CH, ZFC + not   *)
(* CH, ZFC + not GCH and ZF + not AC relative to ZF.                         *)
(*                                                                           *)
(* godel_gch.ml, godel_forcing.ml and godel_notac.ml prove semantic          *)
(* results: any model of ZF yields models of ZFC + GCH, ZFC + CH, ZFC + not  *)
(* CH, ZFC + not GCH and ZF + not AC.                                        *)
(* Here we set up a Hilbert-style proof system for their object language,    *)
(* following Enderton, "A Mathematical Introduction to Logic", 2.4-2.5, and  *)
(* prove it sound and complete by Henkin's method. Since the language has    *)
(* no constants, the Henkin witnesses are variables, chosen via a Godel      *)
(* numbering so that they are fresh. Completeness turns the semantic results *)
(* into statements about formal derivations, for example                     *)
(*                                                                           *)
(*   |- consistent ZF_AX                                                     *)
(*      ==> consistent (gch_ax INSERT choice_ax INSERT ZF_AX)                *)
(*                                                                           *)
(* where a set of formulas is consistent if the set of their universal       *)
(* closures does not derive False (the ZF schemes have parameters, which as  *)
(* axioms are read universally). We also get the independence of CH and of   *)
(* GCH from ZFC, and of AC from ZF, assuming the consistency of ZF.          *)
(* ========================================================================= *)

needs "Autoformalization/godel_notac.ml";;

(* ------------------------------------------------------------------------- *)
(* Substitution of the variable y for the free occurrences of x, without any *)
(* renaming of bound variables, and Enderton's condition for this to be      *)
(* faithful: y is substitutable for x in p if no free occurrence of x lies   *)
(* within the scope of a quantifier binding y. All variables of a formula,   *)
(* free or bound, are collected by formvars from godel_gch.ml.               *)
(* ------------------------------------------------------------------------- *)

let fsubst = new_recursive_definition form_RECURSION
  `(fsubst y x False = False) /\
   (fsubst y x (i %% j) =
        (if i = x then y else i) %% (if j = x then y else j)) /\
   (fsubst y x (Eq i j) =
        Eq (if i = x then y else i) (if j = x then y else j)) /\
   (fsubst y x (p --> q) = fsubst y x p --> fsubst y x q) /\
   (fsubst y x (!! z p) = if z = x then !! z p else !! z (fsubst y x p))`;;

let substitutable = new_recursive_definition form_RECURSION
  `(substitutable y x False <=> T) /\
   (substitutable y x (i %% j) <=> T) /\
   (substitutable y x (Eq i j) <=> T) /\
   (substitutable y x (p --> q) <=>
        substitutable y x p /\ substitutable y x q) /\
   (substitutable y x (!! z p) <=>
        ~(x IN FV(!! z p)) \/ ~(z = y) /\ substitutable y x p)`;;

let FSUBST_TRIVIAL = prove
 (`!p x y. ~(x IN FV p) ==> fsubst y x p = p`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[fsubst; FV; IN_INSERT; IN_UNION; IN_DELETE; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let FSUBST_NOT = prove
 (`!x y p. fsubst y x (Not p) = Not(fsubst y x p)`,
  REWRITE_TAC[Not_DEF; fsubst]);;

let FV_FSUBST = prove
 (`!p x y. FV(fsubst y x p) SUBSET y INSERT (FV p DELETE x)`,
  MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[fsubst; FV] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN REWRITE_TAC[FV]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`])) THEN
  ASM SET_TAC[]);;

let FV_SUBSET_FORMVARS = prove
 (`!p. FV p SUBSET formvars p`,
  MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[FV; formvars] THEN SET_TAC[]);;

let FDEPTH_FSUBST = prove
 (`!p x y. fdepth(fsubst y x p) = fdepth p`,
  MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[fsubst; fdepth] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[fdepth]);;

let SUBSTITUTABLE_FRESH = prove
 (`!p x y. ~(y IN formvars p) ==> substitutable y x p`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[substitutable; formvars; IN_INSERT; IN_UNION] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Substituting a fresh variable and then substituting back is the identity, *)
(* and the second substitution is faithful. This is what makes a change of   *)
(* bound variable derivable (PROVES_RELETTER below).                         *)
(* ------------------------------------------------------------------------- *)

let FSUBST_INVERSE = prove
 (`!p x y. ~(y IN formvars p) ==> fsubst x y (fsubst y x p) = p`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[fsubst; formvars; IN_INSERT; IN_UNION; NOT_IN_EMPTY;
              DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_SIMP_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[fsubst] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC FSUBST_TRIVIAL THEN
  ASM_MESON_TAC[FV_SUBSET_FORMVARS; SUBSET]);;

let SUBSTITUTABLE_INVERSE = prove
 (`!p x y. ~(y IN formvars p) ==> substitutable x y (fsubst y x p)`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[fsubst; substitutable; formvars; IN_INSERT; IN_UNION;
              DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[substitutable] THEN
  ASM_MESON_TAC[FV_SUBSET_FORMVARS; SUBSET; formvars; IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* The semantic substitution lemma, as in Enderton 2.5.                      *)
(* ------------------------------------------------------------------------- *)

let HOLDS_FSUBST = prove
 (`!D (E:A->A->bool) p x y v.
        substitutable y x p
        ==> (holds D E v (fsubst y x p) <=> holds D E ((x |-> v y) v) p)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC form_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[fsubst; holds];
    REWRITE_TAC[fsubst; holds; VALMOD] THEN MESON_TAC[];
    REWRITE_TAC[fsubst; holds; VALMOD] THEN MESON_TAC[];
    SIMP_TAC[substitutable; fsubst; holds];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:num`; `p:form`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `v:num->A`] THEN
  ASM_CASES_TAC `x IN FV(!! z p)` THENL
   [SUBGOAL_THEN `~(z:num = x)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FV; IN_DELETE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[substitutable; fsubst; holds] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[VALMOD_OTHER; VALMOD_SWAP];
    DISCH_THEN(K ALL_TAC) THEN ASM_SIMP_TAC[FSUBST_TRIVIAL] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC HOLDS_VALUATION THEN
    REWRITE_TAC[VALMOD] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* An injective Godel numbering of formulas, which bounds all the variables  *)
(* in a formula. It provides both the fresh Henkin witnesses and the         *)
(* enumeration of formulas used in Lindenbaum's lemma.                       *)
(* ------------------------------------------------------------------------- *)

let gnum = new_recursive_definition form_RECURSION
  `(gnum False = NUMPAIR 0 0) /\
   (gnum (i %% j) = NUMPAIR 1 (NUMPAIR i j)) /\
   (gnum (Eq i j) = NUMPAIR 2 (NUMPAIR i j)) /\
   (gnum (p --> q) = NUMPAIR 3 (NUMPAIR (gnum p) (gnum q))) /\
   (gnum (!! x p) = NUMPAIR 4 (NUMPAIR x (gnum p)))`;;

let NUMPAIR_LT = prove
 (`!x y. x < NUMPAIR x y /\ y < NUMPAIR x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUMPAIR] THEN
  MP_TAC(SPEC `x:num` LT_POW2_REFL) THEN
  SPEC_TAC(`2 EXP x`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n * 1 <= n * (2 * y + 1) /\ 1 * (2 * y + 1) <= n * (2 * y + 1)`
  MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL; LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GNUM_INJ = prove
 (`!p q. gnum p = gnum q <=> p = q`,
  SUBGOAL_THEN `!p q. gnum p = gnum q ==> p = q` (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC form_INDUCT THEN REPEAT CONJ_TAC THEN
  TRY(GEN_TAC THEN GEN_TAC) THEN TRY DISCH_TAC THEN
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[gnum; NUMPAIR_INJ; ARITH_EQ; distinctness "form";
              injectivity "form"] THEN
  ASM_MESON_TAC[]);;

let GNUM_FORMVARS = prove
 (`!p x. x IN formvars p ==> x < gnum p`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[formvars; gnum; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
  MESON_TAC[NUMPAIR_LT; LT_TRANS]);;

let GNUM_FORALL = prove
 (`!x p. x < gnum(!! x p) /\ !z. z IN formvars p ==> z < gnum(!! x p)`,
  MESON_TAC[GNUM_FORMVARS; formvars; IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* Universal closure. Since satisfaction in a model quantifies over all      *)
(* valuations, a formula and its closure hold in the same models.            *)
(* ------------------------------------------------------------------------- *)

let uclose = new_definition
  `uclose p = ITLIST (!!) (list_of_set(FV p)) p`;;

let FV_ITLIST_FORALL = prove
 (`!l p. FV(ITLIST (!!) l p) = FV p DIFF set_of_list l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; set_of_list; FV] THEN
  SET_TAC[]);;

let FV_UCLOSE = prove
 (`!p. FV(uclose p) = {}`,
  SIMP_TAC[uclose; FV_ITLIST_FORALL; SET_OF_LIST_OF_SET; FV_FINITE;
           DIFF_EQ_EMPTY]);;

let VALID_FORALL = prove
 (`!D (E:A->A->bool) x p.
        (!v. valuation D v ==> holds D E v (!! x p)) <=>
        (!v. valuation D v ==> holds D E v p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holds] THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VALUATION_VALMOD] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:num->A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(v:num->A) x`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[valuation]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VALMOD] THEN MESON_TAC[]);;

let VALID_UCLOSE = prove
 (`!D (E:A->A->bool) p.
        (!v. valuation D v ==> holds D E v (uclose p)) <=>
        (!v. valuation D v ==> holds D E v p)`,
  REWRITE_TAC[uclose] THEN GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
   `!l p. (!v. valuation D v
               ==> holds D (E:A->A->bool) v (ITLIST (!!) l p)) <=>
          (!v. valuation D v ==> holds D E v p)`
   (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; VALID_FORALL]);;

let MODEL_UCLOSE = prove
 (`!D (E:A->A->bool) s. model D E (IMAGE uclose s) <=> model D E s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[model; satisfies] THEN
  SUBGOAL_THEN
   `!t. (!v p. valuation D v /\ p IN t ==> holds D (E:A->A->bool) v p) <=>
        (!p. p IN t ==> !v. valuation D v ==> holds D E v p)`
   (fun th -> REWRITE_TAC[th]) THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; VALID_UCLOSE]);;

(* ------------------------------------------------------------------------- *)
(* The proof system (Enderton 2.4): modus ponens is the only rule, and the   *)
(* logical axioms are all generalizations of instances of the propositional  *)
(* axioms A1-A3, the quantifier axioms and the equality axioms. There is no  *)
(* generalization rule, so free variables in hypotheses behave like          *)
(* constants.                                                                *)
(* ------------------------------------------------------------------------- *)

let axiom_RULES,axiom_INDUCT,axiom_CASES = new_inductive_definition
 `(!p q. axiom(p --> q --> p)) /\
  (!p q r. axiom((p --> q --> r) --> (p --> q) --> (p --> r))) /\
  (!p. axiom(((p --> False) --> False) --> p)) /\
  (!x y p. substitutable y x p ==> axiom(!! x p --> fsubst y x p)) /\
  (!x p q. axiom(!! x (p --> q) --> !! x p --> !! x q)) /\
  (!x p. ~(x IN FV p) ==> axiom(p --> !! x p)) /\
  (!x. axiom(Eq x x)) /\
  (!x y z. axiom(Eq x y --> Eq x z --> Eq y z)) /\
  (!x y z. axiom(Eq x y --> (x %% z) --> (y %% z))) /\
  (!x y z. axiom(Eq x y --> (z %% x) --> (z %% y))) /\
  (!x p. axiom p ==> axiom(!! x p))`;;

parse_as_infix("|--",(11,"right"));;

let proves_RULES,proves_INDUCT,proves_CASES = new_inductive_definition
  `(!p. axiom p \/ p IN s ==> s |-- p) /\
   (!p q. s |-- p --> q /\ s |-- p ==> s |-- q)`;;

(* ------------------------------------------------------------------------- *)
(* Soundness.                                                                *)
(* ------------------------------------------------------------------------- *)

let AXIOM_VALID = prove
 (`!p. axiom p ==> !D (E:A->A->bool) v. valuation D v ==> holds D E v p`,
  MATCH_MP_TAC axiom_INDUCT THEN REWRITE_TAC[holds] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MESON_TAC[];
    MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HOLDS_FSUBST] THEN
    ASM_MESON_TAC[valuation];
    MESON_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `holds D (E:A->A->bool) ((x |-> a) v) p <=> holds D E v p`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC HOLDS_VALUATION THEN ASM_MESON_TAC[VALMOD_OTHER];
    MESON_TAC[];
    MESON_TAC[];
    MESON_TAC[];
    MESON_TAC[VALUATION_VALMOD]]);;

let SOUNDNESS = prove
 (`!s p. s |-- p
         ==> !D (E:A->A->bool) v.
                valuation D v /\ (!q. q IN s ==> holds D E v q)
                ==> holds D E v p`,
  GEN_TAC THEN MATCH_MP_TAC proves_INDUCT THEN
  REWRITE_TAC[holds] THEN MESON_TAC[AXIOM_VALID]);;

(* ------------------------------------------------------------------------- *)
(* Basic derived rules, the deduction theorem and the finiteness of proofs.  *)
(* ------------------------------------------------------------------------- *)

let PROVES_AXIOM = prove
 (`!s p. axiom p ==> s |-- p`,
  MESON_TAC[proves_RULES]);;

let PROVES_ASSUME = prove
 (`!s p. p IN s ==> s |-- p`,
  MESON_TAC[proves_RULES]);;

let PROVES_MP = prove
 (`!s p q. s |-- p --> q /\ s |-- p ==> s |-- q`,
  MESON_TAC[proves_RULES]);;

let PROVES_MONO = prove
 (`!s t p. s SUBSET t /\ s |-- p ==> t |-- p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC proves_INDUCT THEN ASM_MESON_TAC[proves_RULES; SUBSET]);;

let PROVES_FINITE = prove
 (`!s p. s |-- p ==> ?t. FINITE t /\ t SUBSET s /\ t |-- p`,
  GEN_TAC THEN MATCH_MP_TAC proves_INDUCT THEN CONJ_TAC THENL
   [X_GEN_TAC `p:form` THEN STRIP_TAC THENL
     [EXISTS_TAC `{}:form->bool` THEN
      ASM_SIMP_TAC[FINITE_EMPTY; EMPTY_SUBSET; PROVES_AXIOM];
      EXISTS_TAC `{p:form}` THEN
      ASM_SIMP_TAC[FINITE_SING; SING_SUBSET; PROVES_ASSUME; IN_SING]];
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `t1:form->bool`)
                               (X_CHOOSE_TAC `t2:form->bool`)) THEN
    EXISTS_TAC `t1 UNION t2:form->bool` THEN
    ASM_REWRITE_TAC[FINITE_UNION; UNION_SUBSET] THEN
    MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `p:form` THEN
    ASM_MESON_TAC[PROVES_MONO; SUBSET_UNION]]);;

let PROVES_IMP_REFL = prove
 (`!s p. s |-- p --> p`,
  MESON_TAC[PROVES_MP; PROVES_AXIOM; axiom_RULES]);;

let DEDUCTION = prove
 (`!s p q. s |-- p --> q <=> p INSERT s |-- q`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `p:form` THEN
    ASM_MESON_TAC[PROVES_MONO; PROVES_ASSUME; IN_INSERT; SET_RULE
     `(s:form->bool) SUBSET p INSERT s`];
    SPEC_TAC(`q:form`,`q:form`) THEN MATCH_MP_TAC proves_INDUCT THEN
    REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
     [X_GEN_TAC `q:form` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[PROVES_IMP_REFL] THEN
      MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `q:form` THEN
      ASM_MESON_TAC[PROVES_AXIOM; PROVES_ASSUME; axiom_RULES];
      MAP_EVERY X_GEN_TAC [`q:form`; `r:form`] THEN STRIP_TAC THEN
      MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `p --> q` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `p --> q --> r` THEN
      ASM_MESON_TAC[PROVES_AXIOM; axiom_RULES]]]);;

let PROVES_DNEG = prove
 (`!s p. s |-- Not(Not p) --> p`,
  REWRITE_TAC[Not_DEF] THEN MESON_TAC[PROVES_AXIOM; axiom_RULES]);;

let PROVES_EXFALSO = prove
 (`!s p q. s |-- Not p --> p --> q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DEDUCTION] THEN
  MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `Not(Not q)` THEN
  REWRITE_TAC[PROVES_DNEG] THEN REWRITE_TAC[Not_DEF; DEDUCTION] THEN
  MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `p:form` THEN
  CONJ_TAC THEN MATCH_MP_TAC PROVES_ASSUME THEN REWRITE_TAC[IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* The generalization theorem, and a change of bound variable to a fresh one *)
(* ("relettering"), both as in Enderton 2.4.                                 *)
(* ------------------------------------------------------------------------- *)

let PROVES_GEN = prove
 (`!s x p. (!q. q IN s ==> ~(x IN FV q)) /\ s |-- p ==> s |-- !! x p`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`p:form`,`p:form`) THEN MATCH_MP_TAC proves_INDUCT THEN
  CONJ_TAC THENL
   [X_GEN_TAC `p:form` THEN STRIP_TAC THENL
     [ASM_MESON_TAC[PROVES_AXIOM; axiom_RULES];
      MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `p:form` THEN
      ASM_MESON_TAC[PROVES_AXIOM; PROVES_ASSUME; axiom_RULES]];
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN STRIP_TAC THEN
    MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `!! x p` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `!! x (p --> q)` THEN
    ASM_MESON_TAC[PROVES_AXIOM; axiom_RULES]]);;

let PROVES_RELETTER = prove
 (`!s x y p. ~(y IN formvars p) ==> s |-- !! y (fsubst y x p) --> !! x p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PROVES_MONO THEN
  EXISTS_TAC `{}:form->bool` THEN
  REWRITE_TAC[EMPTY_SUBSET; DEDUCTION] THEN
  MATCH_MP_TAC PROVES_GEN THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2; FV] THEN
    MP_TAC(SPECL [`p:form`; `x:num`; `y:num`] FV_FSUBST) THEN SET_TAC[];
    MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `!! y (fsubst y x p)` THEN
    SIMP_TAC[PROVES_ASSUME; IN_INSERT] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [GSYM(SPEC `x:num` (MATCH_MP FSUBST_INVERSE th))]) THEN
    MATCH_MP_TAC PROVES_AXIOM THEN
    ASM_SIMP_TAC[axiom_RULES; SUBSTITUTABLE_INVERSE]]);;

(* ------------------------------------------------------------------------- *)
(* The Henkin axiom henkinax x p says that if !! x p fails, then p fails at  *)
(* the witness variable gnum(!! x p), which is larger than all variables of  *)
(* !! x p. Adding one Henkin axiom whose witness is not free in the          *)
(* hypotheses preserves consistency, so adding them in the order of their    *)
(* witnesses gives a consistent chain whose union contains them all.         *)
(* ------------------------------------------------------------------------- *)

let henkinax = new_definition
  `henkinax x p = Not(!! x p) --> Not(fsubst (gnum(!! x p)) x p)`;;

let FV_HENKINAX = prove
 (`!x p z. z IN FV(henkinax x p) ==> z <= gnum(!! x p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[henkinax; FV; FV_CLAUSES; IN_UNION] THEN
  MP_TAC(SPECL [`p:form`; `x:num`; `gnum(!! x p)`] FV_FSUBST) THEN
  MP_TAC(SPEC `p:form` FV_SUBSET_FORMVARS) THEN
  MP_TAC(SPECL [`x:num`; `p:form`] GNUM_FORALL) THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_DELETE] THEN
  MESON_TAC[LT_IMP_LE; LE_REFL]);;

let HENKIN_STEP = prove
 (`!s x y p.
        ~(y IN formvars p) /\ (!q. q IN s ==> ~(y IN FV q)) /\
        ~(s |-- False)
        ==> ~((Not(!! x p) --> Not(fsubst y x p)) INSERT s |-- False)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM DEDUCTION] THEN
  ABBREV_TAC `h = Not(!! x p) --> Not(fsubst y x p)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s |-- fsubst y x p` ASSUME_TAC THENL
   [MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `Not(Not(fsubst y x p))` THEN
    REWRITE_TAC[PROVES_DNEG] THEN
    GEN_REWRITE_TAC RAND_CONV [Not_DEF] THEN
    REWRITE_TAC[DEDUCTION] THEN
    MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `h:form` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[PROVES_MONO; SET_RULE `(s:form->bool) SUBSET a INSERT s`];
      EXPAND_TAC "h" THEN MATCH_MP_TAC PROVES_MP THEN
      EXISTS_TAC `Not(fsubst y x p)` THEN
      SIMP_TAC[PROVES_ASSUME; IN_INSERT; PROVES_AXIOM; axiom_RULES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s |-- !! x p` ASSUME_TAC THENL
   [MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `!! y (fsubst y x p)` THEN
    ASM_SIMP_TAC[PROVES_RELETTER; PROVES_GEN];
    ALL_TAC] THEN
  UNDISCH_TAC `~(s |-- False)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `h:form` THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "h" THEN REWRITE_TAC[DEDUCTION] THEN
  MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `!! x p` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `Not(!! x p)` THEN
    SIMP_TAC[PROVES_EXFALSO; PROVES_ASSUME; IN_INSERT];
    ASM_MESON_TAC[PROVES_MONO; SET_RULE `(s:form->bool) SUBSET a INSERT s`]]);;

let CHAIN_CONSISTENT = prove
 (`!t:num->form->bool.
        (!n. t n SUBSET t (SUC n)) /\ (!n. ~(t n |-- False))
        ==> ~(UNIONS (IMAGE t (:num)) |-- False)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PROVES_FINITE) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:form->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. u SUBSET (t:num->form->bool) n` STRIP_ASSUME_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[PROVES_MONO]] THEN
  MP_TAC(ISPECL [`IMAGE (t:num->form->bool) (:num)`; `u:form->bool`]
                FINITE_SUBSET_UNIONS_CHAIN) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; UNIV_NOT_EMPTY; FORALL_IN_IMAGE_2;
                  EXISTS_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `\m n. (t:num->form->bool) m SUBSET t n`
                TRANSITIVE_STEPWISE_LE) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  ANTS_TAC THENL [MESON_TAC[SUBSET_TRANS]; MESON_TAC[LE_CASES]]);;

let HENKIN_CONSISTENT = prove
 (`!s. (!p. p IN s ==> FV p = {}) /\ ~(s |-- False)
       ==> ~(s UNION {henkinax x p | x,p | T} |-- False)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\n. s UNION {henkinax x p | x,p | gnum(!! x p) < n}`
               CHAIN_CONSISTENT) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(t:form->bool) SUBSET u ==> s UNION t SUBSET s UNION u`) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[LT];
    ALL_TAC;
    MATCH_MP_TAC PROVES_MONO THEN
    EXISTS_TAC `s UNION {henkinax x p | x,p | T}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_UNION;
                IN_ELIM_THM] THEN
    MESON_TAC[LT_SUC_LE; LE_REFL]] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[LT] THEN
    SUBGOAL_THEN `s UNION {henkinax x p | x,p | F} = s`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM];
    ALL_TAC] THEN
  UNDISCH_TAC
   `~(s UNION {henkinax x p | x,p | gnum(!! x p) < n} |-- False)` THEN
  ASM_CASES_TAC `?x p. gnum(!! x p) = n` THENL
   [ALL_TAC;
    REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC PROVES_MONO THEN
    EXISTS_TAC `s UNION {henkinax x p | x,p | gnum(!! x p) < SUC n}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; LT] THEN ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:num` (X_CHOOSE_THEN `q:form`
    (SUBST_ALL_TAC o SYM))) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`s UNION {henkinax x p | x,p | gnum(!! x p) < gnum(!! y q)}`;
    `y:num`; `gnum(!! y q)`; `q:form`] HENKIN_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MESON_TAC[GNUM_FORALL; LT_REFL];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[FV_HENKINAX; NOT_IN_EMPTY; NOT_LT]];
    REWRITE_TAC[CONTRAPOS_THM; GSYM henkinax] THEN DISCH_TAC THEN
    MATCH_MP_TAC PROVES_MONO THEN
    EXISTS_TAC
     `s UNION {henkinax x p | x,p | gnum(!! x p) < SUC(gnum(!! y q))}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_INSERT; IN_ELIM_THM; LT] THEN
    MESON_TAC[GNUM_INJ; injectivity "form"]]);;

(* ------------------------------------------------------------------------- *)
(* Lindenbaum's lemma: a consistent set extends to a maximal consistent one, *)
(* by considering each formula in turn, in the order of the Godel numbering. *)
(* ------------------------------------------------------------------------- *)

let maxcons = new_definition
  `maxcons h <=> ~(h |-- False) /\ !p. p IN h \/ Not p IN h`;;

let lindenbaum = new_recursive_definition num_RECURSION
 `(lindenbaum s 0 = s) /\
  (!n. lindenbaum s (SUC n) =
         lindenbaum s n UNION
         {p | gnum p = n /\ ~(p INSERT lindenbaum s n |-- False)})`;;

let LINDENBAUM = prove
 (`!s. ~(s |-- False) ==> ?h. s SUBSET h /\ maxcons h`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `UNIONS (IMAGE (lindenbaum s) (:num))` THEN
  SUBGOAL_THEN `!n. ~(lindenbaum s n |-- False)` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[lindenbaum] THEN
    ASM_CASES_TAC `?p. gnum p = n /\ ~(p INSERT lindenbaum s n |-- False)`
    THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `p:form` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(p INSERT lindenbaum s n |-- False)` THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC PROVES_MONO THEN
      EXISTS_TAC
       `lindenbaum s n UNION
        {p | gnum p = n /\ ~(p INSERT lindenbaum s n |-- False)}` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_INSERT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[GNUM_INJ];
      SUBGOAL_THEN
       `lindenbaum s n UNION
        {p | gnum p = n /\ ~(p INSERT lindenbaum s n |-- False)} =
        lindenbaum s n`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS (IMAGE (lindenbaum s) (:num)) |-- False)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CHAIN_CONSISTENT THEN
    ASM_REWRITE_TAC[lindenbaum; SUBSET_UNION];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[maxcons] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[lindenbaum];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN UNIONS (IMAGE (lindenbaum s) (:num)) \/
        p INSERT UNIONS (IMAGE (lindenbaum s) (:num)) |-- False`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:form` THEN
    ASM_CASES_TAC `p INSERT lindenbaum s (gnum p) |-- False` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC PROVES_MONO THEN
      EXISTS_TAC `p INSERT lindenbaum s (gnum p)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `(s:form->bool) SUBSET t ==> p INSERT s SUBSET p INSERT t`);
      DISJ1_TAC THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
      EXISTS_TAC `SUC(gnum p)`] THEN
    ASM_REWRITE_TAC[lindenbaum; IN_UNION; IN_ELIM_THM] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `p:form` THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `p:form` th) THEN
                          MP_TAC(SPEC `Not p` th)) THEN
  REWRITE_TAC[GSYM DEDUCTION] THEN
  ASM_MESON_TAC[PROVES_MP; Not_DEF]);;

let MAXCONS_PROVES = prove
 (`!h p. maxcons h ==> (h |-- p <=> p IN h)`,
  REWRITE_TAC[maxcons] THEN MESON_TAC[PROVES_ASSUME; PROVES_MP; Not_DEF]);;

let MAXCONS_AXIOM = prove
 (`!h p. maxcons h /\ axiom p ==> p IN h`,
  MESON_TAC[MAXCONS_PROVES; PROVES_AXIOM]);;

let MAXCONS_FALSE = prove
 (`!h. maxcons h ==> ~(False IN h)`,
  REWRITE_TAC[maxcons] THEN MESON_TAC[PROVES_ASSUME]);;

let MAXCONS_NOT = prove
 (`!h p. maxcons h ==> (Not p IN h <=> ~(p IN h))`,
  REWRITE_TAC[maxcons] THEN MESON_TAC[PROVES_ASSUME; PROVES_MP; Not_DEF]);;

let MAXCONS_IMP = prove
 (`!h p q. maxcons h ==> ((p --> q) IN h <=> p IN h ==> q IN h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MAXCONS_PROVES th)]) THEN
  EQ_TAC THENL [MESON_TAC[PROVES_MP]; ALL_TAC] THEN
  ASM_CASES_TAC `h |-- p` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `q:form` THEN
    ASM_MESON_TAC[PROVES_AXIOM; axiom_RULES];
    MATCH_MP_TAC PROVES_MP THEN EXISTS_TAC `Not p` THEN
    REWRITE_TAC[PROVES_EXFALSO] THEN
    ASM_MESON_TAC[MAXCONS_PROVES; MAXCONS_NOT]]);;

(* ------------------------------------------------------------------------- *)
(* The canonical model of a maximal consistent set h containing all Henkin   *)
(* axioms: the elements are the classes of variables under provable          *)
(* equality, and membership is read off from h. The Henkin axioms also give  *)
(* arbitrarily large members of each class, so that a member can be found    *)
(* that is substitutable in any given formula.                               *)
(* ------------------------------------------------------------------------- *)

let canonval = new_definition
  `canonval h z = {w | Eq z w IN h}`;;

let canonmem = new_definition
  `canonmem h a b <=>
        ?i j. a = canonval h i /\ b = canonval h j /\ (i %% j) IN h`;;

let CANONVAL_EQ = prove
 (`!h x y. maxcons h ==> (canonval h x = canonval h y <=> Eq x y IN h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[canonval; EXTENSION; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `(!x. Eq x x IN h) /\
    (!x y z. Eq x y IN h /\ Eq x z IN h ==> Eq y z IN h)`
  MP_TAC THENL
   [ASM_MESON_TAC[MAXCONS_AXIOM; MAXCONS_IMP; axiom_RULES]; MESON_TAC[]]);;

let CANONMEM = prove
 (`!h x y. maxcons h
           ==> (canonmem h (canonval h x) (canonval h y) <=> (x %% y) IN h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[canonmem] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; CANONVAL_EQ] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Eq i x IN h /\ Eq j y IN h` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CANONVAL_EQ]; ALL_TAC] THEN
  ASM_MESON_TAC[MAXCONS_AXIOM; MAXCONS_IMP; axiom_RULES]);;

let MAXCONS_EQ_UNBOUNDED = prove
 (`!h z n. maxcons h /\ (!x p. henkinax x p IN h)
           ==> ?y. n <= y /\ Eq z y IN h`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `x = z + n + 1` THEN
  SUBGOAL_THEN `~(z:num = x)` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `gnum(!! x (Not(Eq z x)))` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`x:num`; `Not(Eq z x)`] GNUM_FORALL) THEN
    EXPAND_TAC "x" THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `Not(Eq z x)`]) THEN
  MP_TAC(ISPECL [`h:form->bool`; `Eq z z`] MAXCONS_AXIOM) THEN
  MP_TAC(ISPECL [`h:form->bool`;
                 `!! x (Not(Eq z x)) --> fsubst z x (Not(Eq z x))`]
                MAXCONS_AXIOM) THEN
  ASM_SIMP_TAC[axiom_RULES; substitutable; Not_DEF] THEN
  ASM_SIMP_TAC[henkinax; MAXCONS_IMP; MAXCONS_NOT; GSYM Not_DEF] THEN
  ASM_REWRITE_TAC[fsubst; FSUBST_NOT] THEN
  ASM_SIMP_TAC[MAXCONS_NOT] THEN MESON_TAC[]);;

let CANONICAL_TRUTH = prove
 (`!h. maxcons h /\ (!x p. henkinax x p IN h)
       ==> !p. holds (IMAGE (canonval h) (:num)) (canonmem h) (canonval h) p
               <=> p IN h`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND; MEASURE] (ISPEC `fdepth` WF_MEASURE)) THEN
  MATCH_MP_TAC form_INDUCT THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[holds; MAXCONS_FALSE];
    ASM_SIMP_TAC[holds; CANONMEM];
    ASM_SIMP_TAC[holds; CANONVAL_EQ];
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[fdepth] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[holds; MAXCONS_IMP;
                 ARITH_RULE `a < MAX a b + 1 /\ b < MAX a b + 1`];
    MAP_EVERY X_GEN_TAC [`x:num`; `p:form`] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[fdepth] THEN DISCH_TAC] THEN
  REWRITE_TAC[holds; FORALL_IN_IMAGE; IN_UNIV] THEN
  SUBGOAL_THEN
   `!y. ~(y IN formvars p)
        ==> (holds (IMAGE (canonval h) (:num)) (canonmem h)
                   ((x |-> canonval h y) (canonval h)) p <=>
             fsubst y x p IN h)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `fsubst y x p`) THEN
    ASM_SIMP_TAC[FDEPTH_FSUBST; ARITH_RULE `n < n + 1`; HOLDS_FSUBST;
                 SUBSTITUTABLE_FRESH];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `p:form`]) THEN
    ASM_SIMP_TAC[henkinax; MAXCONS_IMP; MAXCONS_NOT] THEN
    MATCH_MP_TAC(TAUT `b ==> (~a ==> ~b) ==> a`) THEN
    ASM_MESON_TAC[GNUM_FORALL; LT_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `z:num` THEN
  MP_TAC(ISPECL [`h:form->bool`; `z:num`; `gnum p`] MAXCONS_EQ_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(y IN formvars p)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GNUM_FORMVARS; NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `canonval h z = canonval h y` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CANONVAL_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`h:form->bool`; `!! x p --> fsubst y x p`]
                MAXCONS_AXIOM) THEN
  ASM_SIMP_TAC[axiom_RULES; SUBSTITUTABLE_FRESH; MAXCONS_IMP]);;

(* ------------------------------------------------------------------------- *)
(* Model existence, and hence completeness. A set of formulas is consistent  *)
(* if the universal closures of its members do not derive False; this is     *)
(* equivalent to having a model, which can always be taken to be countable   *)
(* and over the type num->bool.                                              *)
(* ------------------------------------------------------------------------- *)

let MODEL_EXISTENCE = prove
 (`!s. (!p. p IN s ==> FV p = {}) /\ ~(s |-- False)
       ==> ?D (E:(num->bool)->(num->bool)->bool). COUNTABLE D /\ model D E s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s UNION {henkinax x p | x,p | T}` LINDENBAUM) THEN
  ASM_SIMP_TAC[HENKIN_CONSISTENT; UNION_SUBSET; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:form->bool` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (canonval h) (:num)`; `canonmem h`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COUNTABLE; GE_C; IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[model; satisfies; IMAGE_EQ_EMPTY; UNIV_NOT_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`v:num->num->bool`; `p:form`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (canonval h) (:num)`; `canonmem h`; `p:form`;
                 `canonval h`; `v:num->num->bool`] HOLDS_VALUATION) THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_MESON_TAC[CANONICAL_TRUTH]);;

let consistent = new_definition
  `consistent s <=> ~(IMAGE uclose s |-- False)`;;

let THEORY_SOUNDNESS = prove
 (`!s p. IMAGE uclose s |-- p
         ==> !D (E:A->A->bool) v.
                model D E s /\ valuation D v ==> holds D E v p`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP SOUNDNESS) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[MODEL_UCLOSE; MODEL_HOLDS; FUN_IN_IMAGE]);;

let MODEL_IMP_CONSISTENT = prove
 (`!D (E:A->A->bool) s. model D E s ==> consistent s`,
  REWRITE_TAC[consistent] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `v:num->A` o MATCH_MP VALUATION_EXISTS o
              MATCH_MP MODEL_NONEMPTY) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP THEORY_SOUNDNESS) THEN
  REWRITE_TAC[holds] THEN ASM_MESON_TAC[]);;

let CONSISTENT_IMP_MODEL = prove
 (`!s. consistent s
       ==> ?D (E:(num->bool)->(num->bool)->bool). COUNTABLE D /\ model D E s`,
  REWRITE_TAC[consistent] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE uclose s` MODEL_EXISTENCE) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; FV_UCLOSE; MODEL_UCLOSE]);;

let CONSISTENT_EQ_MODEL = prove
 (`!s. consistent s <=> ?D (E:(num->bool)->(num->bool)->bool). model D E s`,
  MESON_TAC[CONSISTENT_IMP_MODEL; MODEL_IMP_CONSISTENT]);;

let COMPLETENESS = prove
 (`!s p. IMAGE uclose s |-- uclose p <=>
         !D (E:(num->bool)->(num->bool)->bool) v.
                model D E s /\ valuation D v ==> holds D E v p`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o INST_TYPE [`:num->bool`,`:A`] o
               MATCH_MP THEORY_SOUNDNESS) THEN
    MESON_TAC[VALID_UCLOSE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `Not(uclose p) INSERT IMAGE uclose s` MODEL_EXISTENCE) THEN
  REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE; FV_CLAUSES; FV_UCLOSE] THEN
  REWRITE_TAC[GSYM DEDUCTION; GSYM Not_DEF; NOT_IMP; NOT_EXISTS_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PROVES_MP; PROVES_DNEG]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`D:(num->bool)->bool`; `E:(num->bool)->(num->bool)->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `v:num->num->bool` o MATCH_MP VALUATION_EXISTS o
              MATCH_MP MODEL_NONEMPTY) THEN
  SUBGOAL_THEN `model D (E:(num->bool)->(num->bool)->bool) s` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MODEL_UCLOSE] THEN
    UNDISCH_TAC `model D (E:(num->bool)->(num->bool)->bool)
                       (Not(uclose p) INSERT IMAGE uclose s)` THEN
    REWRITE_TAC[model; satisfies; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `holds D (E:(num->bool)->(num->bool)->bool) v (uclose p)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`D:(num->bool)->bool`; `E:(num->bool)->(num->bool)->bool`;
                   `p:form`] VALID_UCLOSE) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[GSYM HOLDS_NOT] THEN
    ASM_MESON_TAC[MODEL_HOLDS; IN_INSERT]]);;

let MODEL_INSERT = prove
 (`!D (E:A->A->bool) p s.
        model D E (p INSERT s) <=>
        model D E s /\ !v. valuation D v ==> holds D E v p`,
  REWRITE_TAC[model; satisfies; IN_INSERT] THEN MESON_TAC[]);;

let CONSISTENT_INSERT = prove
 (`!s p. (consistent (p INSERT s) ==> ~(IMAGE uclose s |-- Not p)) /\
         (consistent (Not p INSERT s) ==> ~(IMAGE uclose s |-- p))`,
  REWRITE_TAC[CONSISTENT_EQ_MODEL; MODEL_INSERT; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `v:num->num->bool` o MATCH_MP VALUATION_EXISTS o
              MATCH_MP MODEL_NONEMPTY) THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
   [`D:(num->bool)->bool`; `E:(num->bool)->(num->bool)->bool`;
    `v:num->num->bool`] o MATCH_MP THEORY_SOUNDNESS) THEN
  ASM_MESON_TAC[HOLDS_NOT]);;

(* ------------------------------------------------------------------------- *)
(* The payoff: syntactic versions of the relative consistency results of     *)
(* godel_gch.ml, godel_forcing.ml and godel_notac.ml. The axioms added to    *)
(* ZF are sentences, so taking universal closures affects only the ZF        *)
(* schemes.                                                                  *)
(* ------------------------------------------------------------------------- *)

let FV_CHOICE_CH_GCH_AX = prove
 (`FV choice_ax = {} /\ FV ch_ax = {} /\ FV gch_ax = {}`,
  REWRITE_TAC[choice_ax; ch_ax; gch_ax; infcard_form; succard_form;
              iscard_form; pow_form; bijform; Forallmem_DEF; Existsmem_DEF;
              FV; FV_CLAUSES; FV_OMEGA_FORM; FV_ORDINAL_FORM; FV_SUBSET_FORM;
              FV_APPLY_FORM] THEN
  REWRITE_TAC[MAX] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_UNION; IN_INSERT; IN_DELETE] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:num` THEN
  MAP_EVERY (fun n -> ASM_CASES_TAC (mk_eq(`x:num`,mk_small_numeral n)) THEN
                      ASM_REWRITE_TAC[ARITH_EQ])
            (0--8));;

let CON_ZF_IMP_CON_ZFC_GCH = prove
 (`consistent ZF_AX ==> consistent (gch_ax INSERT choice_ax INSERT ZF_AX)`,
  REWRITE_TAC[CONSISTENT_EQ_MODEL] THEN MESON_TAC[ZF_MODEL_GCH_MODEL]);;

let CON_ZF_IMP_CON_ZFC_CH = prove
 (`consistent ZF_AX ==> consistent (ch_ax INSERT choice_ax INSERT ZF_AX)`,
  REWRITE_TAC[CONSISTENT_EQ_MODEL] THEN MESON_TAC[ZF_MODEL_CH_MODEL]);;

let CON_ZF_IMP_CON_ZFC_NOT_CH = prove
 (`consistent ZF_AX
   ==> consistent (Not ch_ax INSERT choice_ax INSERT ZF_AX)`,
  REWRITE_TAC[CONSISTENT_EQ_MODEL; GSYM not_ch_ax] THEN
  MESON_TAC[ZF_MODEL_NOT_CH_MODEL]);;

let CON_ZF_IMP_CON_ZFC_NOT_GCH = prove
 (`consistent ZF_AX
   ==> consistent (Not gch_ax INSERT choice_ax INSERT ZF_AX)`,
  REWRITE_TAC[CONSISTENT_EQ_MODEL] THEN MESON_TAC[ZF_MODEL_NOT_GCH_MODEL]);;

let CON_ZF_IMP_CON_ZFC = prove
 (`consistent ZF_AX ==> consistent (choice_ax INSERT ZF_AX)`,
  REWRITE_TAC[CONSISTENT_EQ_MODEL] THEN MESON_TAC[ZF_MODEL_AC_MODEL]);;

let CON_ZF_IMP_CON_ZF_NOT_AC = prove
 (`consistent ZF_AX ==> consistent (Not choice_ax INSERT ZF_AX)`,
  REWRITE_TAC[CONSISTENT_EQ_MODEL] THEN MESON_TAC[ZF_MODEL_NOT_AC_MODEL]);;

(* ------------------------------------------------------------------------- *)
(* Hence if ZF is consistent, ZFC decides neither CH nor GCH, and ZF does    *)
(* not decide AC.                                                            *)
(* ------------------------------------------------------------------------- *)

let CON_ZF_IMP_INDEPENDENT_CH = prove
 (`consistent ZF_AX
   ==> ~(IMAGE uclose (choice_ax INSERT ZF_AX) |-- ch_ax) /\
       ~(IMAGE uclose (choice_ax INSERT ZF_AX) |-- Not ch_ax)`,
  MESON_TAC[CONSISTENT_INSERT; CON_ZF_IMP_CON_ZFC_CH;
            CON_ZF_IMP_CON_ZFC_NOT_CH]);;

let CON_ZF_IMP_INDEPENDENT_GCH = prove
 (`consistent ZF_AX
   ==> ~(IMAGE uclose (choice_ax INSERT ZF_AX) |-- gch_ax) /\
       ~(IMAGE uclose (choice_ax INSERT ZF_AX) |-- Not gch_ax)`,
  MESON_TAC[CONSISTENT_INSERT; CON_ZF_IMP_CON_ZFC_GCH;
            CON_ZF_IMP_CON_ZFC_NOT_GCH]);;

let CON_ZF_IMP_INDEPENDENT_AC = prove
 (`consistent ZF_AX
   ==> ~(IMAGE uclose ZF_AX |-- choice_ax) /\
       ~(IMAGE uclose ZF_AX |-- Not choice_ax)`,
  MESON_TAC[CONSISTENT_INSERT; CON_ZF_IMP_CON_ZFC;
            CON_ZF_IMP_CON_ZF_NOT_AC]);;
