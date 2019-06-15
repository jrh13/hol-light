(* ========================================================================= *)
(* Canonical models in FOL and their use to derive classic metatheorems.     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Domain of a canonical model for given language.                           *)
(* ------------------------------------------------------------------------- *)

let terms_RULES,terms_INDUCT,terms_CASES = new_inductive_definition
  `(!x. terms fns (V x)) /\
   (!f l. (f,LENGTH l) IN fns /\ ALL (terms fns) l
          ==> terms fns (Fn f l))`;;

(* ------------------------------------------------------------------------- *)
(* A few obvious lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)

let STUPID_CANONDOM_LEMMA = prove
 (`!t. t IN terms(FST L) ==> functions_term t SUBSET (FST L)`,
  let lemma0 = prove
   (`a SUBSET s /\ b SUBSET s ==> (a UNION b) SUBSET s`,SET_TAC[]) in
  let lemma1 = prove
   (`a IN s /\ b SUBSET s ==> (a INSERT b) SUBSET s`,SET_TAC[]) in
  let lemma2 = prove
   (`!l. ALL (\x. x SUBSET s) l ==> LIST_UNION l SUBSET s`,
    LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LIST_UNION; EMPTY_SUBSET] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma0 THEN ASM_MESON_TAC[]) in
  REWRITE_TAC[IN] THEN MATCH_MP_TAC terms_INDUCT THEN
  REWRITE_TAC[functions_term; EMPTY_SUBSET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lemma2 THEN
  ASM_REWRITE_TAC[ALL_MAP; o_DEF]);;

let FINITE_SUBSET_INSTANCE = prove
 (`!t'. FINITE(t')
        ==> t' SUBSET { formsubst v p | P(v) /\ p IN s}
            ==> ?t. FINITE(t) /\ t SUBSET s /\
                    t' SUBSET {formsubst v p | P(v) /\ p IN t}`,
  let lemma = prove
   (`(a INSERT s) SUBSET t <=> a IN t /\ s SUBSET t`,SET_TAC[]) in
  MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[EMPTY_SUBSET] THEN
    EXISTS_TAC `EMPTY:form->bool` THEN
    REWRITE_TAC[FINITE_RULES; EMPTY_SUBSET];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[lemma] THEN
    DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
                         ANTE_RES_THEN MP_TAC (CONJUNCT2 th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:form->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(@p. ?v. (P v /\ p IN s) /\ (x = formsubst v p)) INSERT t0` THEN
    ASM_REWRITE_TAC[FINITE_INSERT; lemma] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN]) THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[IN_ELIM_THM]) THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:num->term` MP_TAC) THEN
    SPEC_TAC(`@p. ?v. (P v /\ p IN s) /\ (x = formsubst v p)`,`q:form`) THEN
    UNDISCH_TAC `s' SUBSET {formsubst v p | P v /\ p IN t0}` THEN
    UNDISCH_TAC `x IN {formsubst v p | P v /\ p IN s}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[]]);;

let FINITE_SUBSET_SKOLEM = prove
 (`!s u. FINITE(u)
        ==> u SUBSET { SKOLEM p | p IN s}
            ==> ?t. FINITE(t) /\ t SUBSET s /\
                    (u = {SKOLEM p | p IN t})`,
  let lemma = prove
   (`(a INSERT s) SUBSET t <=> a IN t /\ s SUBSET t`,SET_TAC[]) in
  let lemma2 = prove
   (`{SKOLEM p | p IN x INSERT s} =
     (SKOLEM x) INSERT {SKOLEM p | p IN s}`,
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN SET_TAC[]) in
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[EMPTY_SUBSET] THEN
    EXISTS_TAC `EMPTY:form->bool` THEN
    REWRITE_TAC[FINITE_RULES; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[lemma] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
                       ANTE_RES_THEN MP_TAC (CONJUNCT2 th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:form->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(@p. p IN s /\ (x = SKOLEM p)) INSERT t0` THEN
  ASM_REWRITE_TAC[FINITE_INSERT; lemma] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN]) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[IN_ELIM_THM]) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[lemma2] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN REFL_TAC);;

let VALUATION_EXISTS = prove
 (`!M. ~(Dom(M) = EMPTY) ==> ?v:num->A. valuation(M) v`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
  EXISTS_TAC `\x:num. a:A` THEN
  ASM_REWRITE_TAC[valuation]);;

let HOLDS_ITLIST_EXISTS = prove
 (`!M xs v. holds M v (ITLIST ?? xs p) <=>
            ?as. (LENGTH as = LENGTH xs) /\
                 ALL (Dom M) as /\
                 holds M
                   (ITLIST valmod (REVERSE (MAP2 (\x a:A. (x,a)) xs as)) v)
                   p`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[HOLDS; LENGTH; ITLIST; MAP2_DEF; HD;
                  TL; REVERSE; APPEND] THENL
   [MESON_TAC[ALL; LENGTH]; REWRITE_TAC[ITLIST_EXTRA; IN]] THEN
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `as:A list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `CONS (a:A) as` THEN ASM_REWRITE_TAC[ALL; TL; HD; LENGTH];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
    REWRITE_TAC[ALL; SUC_INJ; HD; TL] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Canonical model based on the language of a set of formulas.               *)
(* ------------------------------------------------------------------------- *)

let canonical = new_definition
  `canonical (L:(num#num->bool)#(num#num->bool)) M <=>
       (Dom M = terms (FST L)) /\
       (!f. Fun(M) f = Fn f)`;;

(* ------------------------------------------------------------------------- *)
(* Mappings between models and propositional valuations.                     *)
(* ------------------------------------------------------------------------- *)

let prop_of_model = new_definition
  `prop_of_model M v (Atom p l) <=> holds M v (Atom p l)`;;

let canon_of_prop = new_definition
  `canon_of_prop (L:((num#num)->bool)#((num#num)->bool)) (d:form->bool) =
   terms(FST L),Fn,\p l. d(Atom p l)`;;

let PHOLDS_PROP_OF_MODEL = prove
 (`!p. qfree(p) ==> (pholds (prop_of_model M v) p <=> holds M v p)`,
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[qfree; holds; pholds] THEN CONJ_TAC THENL
   [REWRITE_TAC[prop_of_model; holds];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN REFL_TAC]);;

let PROP_OF_CANON_OF_PROP = prove
 (`!p l. prop_of_model (canon_of_prop L d) V (Atom p l) = d (Atom p l)`,
  REWRITE_TAC[prop_of_model; canon_of_prop; holds; Pred_DEF] THEN
  REPEAT GEN_TAC THEN REPEAT AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN
  SPEC_TAC(`l:term list`,`l:term list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  SPEC_TAC(`h:term`,`t:term`) THEN
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termval; Fun_DEF] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN ASM_REWRITE_TAC[]);;

let HOLDS_CANON_OF_PROP = prove
 (`!p. qfree p ==> (holds (canon_of_prop L d) V p <=> pholds d p)`,
  GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC th THEN
   REWRITE_TAC[GSYM(MATCH_MP PHOLDS_PROP_OF_MODEL th)]) THEN
  SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[pholds; qfree; PROP_OF_CANON_OF_PROP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN REFL_TAC);;

let HOLDS_CANON_OF_PROP_GENERAL = prove
 (`qfree p ==> (holds (canon_of_prop L d) v p <=> pholds d (formsubst v p))`,
  DISCH_THEN(fun th -> MP_TAC th THEN
   REWRITE_TAC[GSYM(MATCH_MP PHOLDS_PROP_OF_MODEL th)]) THEN
  SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[formsubst; pholds; qfree; PROP_OF_CANON_OF_PROP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN
    REFL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[prop_of_model; canon_of_prop; holds] THEN
  REWRITE_TAC[Pred_DEF] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN SIMP_TAC[GSYM TERMSUBST_TERMVAL; Fun_DEF]);;

let CANONICAL_CANON_OF_PROP = prove
 (`!d. canonical L (canon_of_prop L d)`,
  REWRITE_TAC[canonical; canon_of_prop; Dom_DEF; Fun_DEF; FUN_EQ_THM]);;

let INTERPRETATION_CANON_OF_PROP = prove
 (`!L d. interpretation L (canon_of_prop L d)`,
  REWRITE_TAC[FORALL_PAIR_THM; IN; ETA_AX;
              interpretation; canon_of_prop; Fun_DEF; Dom_DEF] THEN
  MESON_TAC[terms_RULES; IN]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence theorems for tautologies.                                     *)
(* ------------------------------------------------------------------------- *)

let PROP_VALID_IMP_FOL_VALID = prove
 (`!p. qfree(p) /\ (!d. pholds d p) ==> !M v. holds M v p`,
  MESON_TAC[PHOLDS_PROP_OF_MODEL]);;

let FOL_VALID_IMP_PROP_VALID = prove
 (`!p. qfree(p) /\
       (!C (v:num->term). canonical(language {p}) C ==> holds C v p)
       ==> !d. pholds d p`,
  MESON_TAC[CANONICAL_CANON_OF_PROP; HOLDS_CANON_OF_PROP]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for satisfiability.                                            *)
(* ------------------------------------------------------------------------- *)

let SATISFIES_PSATISFIES = prove
 (`(!p. p IN s ==> qfree p) /\ M satisfies s /\ valuation(M) v
   ==> (prop_of_model M v) psatisfies s`,
  REWRITE_TAC[satisfies; psatisfies] THEN MESON_TAC[PHOLDS_PROP_OF_MODEL]);;

let PSATISFIES_INSTANCES = prove
 (`(!p. p IN s ==> qfree p) /\
   d psatisfies {formsubst v p | (!x. v x IN terms(FST L)) /\ p IN s}
   ==> (canon_of_prop L d) satisfies s`,
  REWRITE_TAC[satisfies; psatisfies; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  STRIP_TAC THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [canon_of_prop; Dom_DEF; valuation] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL[`formsubst v p`; `v:num->term`; `p:form`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `holds (canon_of_prop L d) V (formsubst v p)` MP_TAC THENL
   [ASM_MESON_TAC[HOLDS_CANON_OF_PROP; QFREE_FORMSUBST]; ALL_TAC] THEN
  SUBGOAL_THEN `holds (canon_of_prop L d) V (formsubst v p) <=>
                holds (canon_of_prop L d) (termval (canon_of_prop L d) V o v)
                      p`
  SUBST1_TAC THENL
   [REWRITE_TAC[HOLDS_FORMSUBST] THEN
    ASM_MESON_TAC[INTER_EMPTY; QFREE_BV_EMPTY];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    GEN_TAC THEN SPEC_TAC(`(v:num->term) x`,`t:term`) THEN
    MATCH_MP_TAC TERMVAL_TRIV THEN
    REWRITE_TAC[canon_of_prop; Fun_DEF]]);;

let SATISFIES_INSTANCES = prove
 (`!M:(A->bool)#(num->A list->A)#(num->A list->bool) s t.
        interpretation(language t) M
        ==> (M satisfies
             {formsubst i p | p IN s /\
                              (!x. i x IN terms(FST(language t)))} <=>
             M satisfies s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[satisfies; IN_ELIM_THM] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[FORMSUBST_TRIV; terms_RULES; IN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[HOLDS_FORMSUBST] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[valuation; o_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
  EXISTS_TAC `predicates t` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `interpretation (language t)
                (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
  REWRITE_TAC[language] THEN MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
  SUBGOAL_THEN `functions t = FST(language t)` SUBST1_TAC THENL
   [REWRITE_TAC[language]; ALL_TAC] THEN
  MATCH_MP_TAC STUPID_CANONDOM_LEMMA THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* So we have compactness in a strong form.                                  *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CANON_QFREE = prove
 (`(!p. p IN s ==> qfree p) /\
   (!t. FINITE t /\ t SUBSET s ==> ?M. interpretation(language ss) M /\
                                       ~(Dom(M):A->bool = EMPTY) /\
                                       M satisfies t)
   ==> ?C. interpretation (language ss) C /\
           canonical (language ss) C /\
           C satisfies s`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `psatisfiable {formsubst v p | (!x. v x IN terms(FST(language ss))) /\
                                  p IN s}`
  MP_TAC THENL
   [REWRITE_TAC[psatisfiable] THEN MATCH_MP_TAC COMPACT_PROP THEN
    REWRITE_TAC[GSYM psatisfiable] THEN
    X_GEN_TAC `u:form->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?t. FINITE(t) /\ t SUBSET s /\
          u SUBSET {formsubst v p |
                              (!x. v x IN terms (FST (language ss))) /\
                                    p IN t}`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[TAUT `(a ==> b ==> c) <=> a /\ b ==> c`]
        (GEN_ALL FINITE_SUBSET_INSTANCE)) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SATISFIABLE_MONO THEN
    EXISTS_TAC `{formsubst v p |
                          (!x. v x IN terms (FST (language ss))) /\
                          p IN t}` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:form->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(CHOOSE_TAC o MATCH_MP VALUATION_EXISTS) THEN
    MP_TAC(SPEC `ss:form->bool` (SPEC `t:form->bool`
     (snd(SPEC_VAR SATISFIES_INSTANCES)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!p. p IN t ==> qfree p` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN DISCH_TAC THEN
    REWRITE_TAC[psatisfiable] THEN
    EXISTS_TAC `prop_of_model M (v:num->A)` THEN
    REWRITE_TAC[GSYM psatisfies] THEN
    MATCH_MP_TAC SATISFIES_PSATISFIES THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[QFREE_FORMSUBST] THEN
      ASM_MESON_TAC[SUBSET];
      RULE_ASSUM_TAC(REWRITE_RULE[CONJ_ACI]) THEN
      ASM_REWRITE_TAC[CONJ_ACI]]; ALL_TAC] THEN
  REWRITE_TAC[psatisfiable; GSYM psatisfies] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:form->bool` ASSUME_TAC) THEN
  EXISTS_TAC `canon_of_prop (language ss) d` THEN
  REWRITE_TAC[CANONICAL_CANON_OF_PROP; INTERPRETATION_CANON_OF_PROP] THEN
  MATCH_MP_TAC PSATISFIES_INSTANCES THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tedious lemma about sublanguage.                                          *)
(* ------------------------------------------------------------------------- *)

let INTERPRETATION_RESTRICTLANGUAGE = prove
 (`!M s t. t SUBSET s /\ interpretation(language s) M
         ==> interpretation(language t) M`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_TAC THEN
  REWRITE_TAC[language] THEN
  MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
  REWRITE_TAC[functions] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN MESON_TAC[]);;

let INTERPRETATION_EXTENDLANGUAGE = prove
 (`!M s t.
        interpretation (language t) M /\
        ~(Dom M :A->bool = EMPTY) /\
        M satisfies t
        ==> ?M'. (Dom M' = Dom M) /\
                 (Pred M' = Pred M) /\
                 interpretation(language s) M' /\
                 M' satisfies t`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `Dom(M):A->bool,
              (\g zs. if (g,LENGTH zs) IN functions t then Fun(M) g zs
                      else @a. a IN Dom(M)),
              Pred(M)` THEN
  REWRITE_TAC[Dom_DEF; Fun_DEF; Pred_DEF; interpretation; language] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE [language; interpretation]) THEN
      ASM_REWRITE_TAC[];
      CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [satisfies]) THEN
    REWRITE_TAC[satisfies] THEN
    REWRITE_TAC[valuation; Dom_DEF] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
    STRIP_TAC THEN SPEC_TAC(`v:num->A`,`v:num->A`) THEN
    MATCH_MP_TAC HOLDS_FUNCTIONS THEN
    REWRITE_TAC[Dom_DEF; Fun_DEF; Pred_DEF] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[functions; IN_UNIONS; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Generalize to any formulas, via Skolemization.                            *)
(* ------------------------------------------------------------------------- *)

let COMPACT_LS = prove
 (`(!t. FINITE t /\ t SUBSET s ==> ?M. interpretation(language s) M /\
                                       ~(Dom(M):A->bool = EMPTY) /\
                                       M satisfies t)
   ==> ?C. interpretation (language s) C /\
           ~(Dom(C):term->bool = EMPTY) /\
           C satisfies s`,
  let lemma = prove
   (`(!y. p y ==> p' y)
     ==> (?x. p x) ==> (?x. p' x)`,
    MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. FINITE u /\ u SUBSET {SKOLEM p | p IN s}
        ==> ?M. interpretation(language {SKOLEM p | p IN s}) M /\
                ~(Dom(M):A->bool = EMPTY) /\
                M satisfies u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?t. (u = {SKOLEM p | p IN t}) /\
                      FINITE t /\ t SUBSET s`
    (CHOOSE_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THENL
     [MP_TAC(SPECL [`s:form->bool`; `u:form->bool`] FINITE_SUBSET_SKOLEM) THEN
      ASM_REWRITE_TAC[CONJ_ACI]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:form->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN
     `M:(A->bool)#(num->A list->A)#(num->A list->bool)`
     STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(?M. ~(Dom M:A->bool = EMPTY) /\
           interpretation(language t) M /\
           M satisfies t)`
    (MP_TAC o GEN_REWRITE_RULE I [SKOLEM_SATISFIABLE]) THENL
     [EXISTS_TAC `M:(A->bool)#(num->A list->A)#(num->A list->bool)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTERPRETATION_RESTRICTLANGUAGE THEN
      EXISTS_TAC `s:form->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN
     `M0:(A->bool)#(num->A list->A)#(num->A list->bool)`
     STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `M0:(A->bool)#(num->A list->A)#(num->A list->bool)`
      INTERPRETATION_EXTENDLANGUAGE) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`{SKOLEM p | p IN s}`; `{SKOLEM p | p IN t}`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN
     `M1:(A->bool)#(num->A list->A)#(num->A list->bool)`
     STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `M1:(A->bool)#(num->A list->A)#(num->A list->bool)` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(INST [`{SKOLEM p | p IN s}`,`s:form->bool`;
               `{SKOLEM p | p IN s}`,`ss:form->bool`]
              COMPACT_CANON_QFREE) THEN
  ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SKOLEM_QFREE]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[AC CONJ_ACI `a /\ b /\ c <=> b /\ a /\ c`] THEN
  GEN_REWRITE_TAC RAND_CONV [SKOLEM_SATISFIABLE] THEN
  MATCH_MP_TAC lemma THEN REWRITE_TAC[canonical] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN] THEN
  MESON_TAC[terms_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Split away the compactness argument.                                      *)
(* ------------------------------------------------------------------------- *)

let CANON = prove
 (`!M:(A->bool)#(num->A list->A)#(num->A list->bool) s.
        interpretation (language s) M /\
        ~(Dom(M) = EMPTY) /\
        (!p. p IN s ==> qfree p) /\ M satisfies s
        ==> ?C. interpretation (language s) C /\
                ~(Dom C :term->bool = EMPTY) /\
                C satisfies s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_LS THEN
  ASM_MESON_TAC[satisfies; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Conventional form of the LS theorem.                                      *)
(* ------------------------------------------------------------------------- *)

let term_of_num = new_definition
  `term_of_num n = (@t. num_of_term t = n)`;;

let TERM_OF_NUM = prove
 (`term_of_num(num_of_term t) = t`,
  REWRITE_TAC[term_of_num; NUM_OF_TERM_INJ]);;

let LOWMOD = new_definition
  `LOWMOD M = {num_of_term t | t IN Dom(M)},
              (\g zs. num_of_term (Fun(M) g (MAP term_of_num zs))),
              (\p zs. Pred(M) p (MAP term_of_num zs))`;;

let LOWMOD_DOM_EMPTY = prove
 (`(Dom(LOWMOD M) = EMPTY) <=> (Dom(M) = EMPTY)`,
  REWRITE_TAC[Dom_DEF; LOWMOD; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let LOWMOD_TERMVAL = prove
 (`!v. valuation (LOWMOD M) v
       ==> !t. termval (LOWMOD M) v t =
               num_of_term (termval M (term_of_num o v) t)`,
  GEN_TAC THEN DISCH_THEN
   (ASSUME_TAC o REWRITE_RULE[valuation; LOWMOD; Dom_DEF; IN_ELIM_THM]) THEN
  MATCH_MP_TAC term_INDUCT THEN  REWRITE_TAC[termval; o_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[TERM_OF_NUM]; ALL_TAC] THEN
  REWRITE_TAC[LOWMOD; Fun_DEF] THEN REWRITE_TAC[GSYM LOWMOD] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  MATCH_MP_TAC ALL_IMP THEN
  FIRST_ASSUM(EXISTS_TAC o lhand o concl) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[o_THM; TERM_OF_NUM]);;

let LOWMOD_HOLDS = prove
 (`!p v. valuation (LOWMOD M) v
         ==> (holds (LOWMOD M) v p <=> holds M (term_of_num o v) p)`,
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[holds] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LOWMOD; Pred_DEF] THEN
    REWRITE_TAC[GSYM LOWMOD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM MAP_o] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    ASM_SIMP_TAC[LOWMOD_TERMVAL; TERM_OF_NUM];
    MESON_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[Dom_DEF; LOWMOD] THEN REWRITE_TAC[GSYM LOWMOD] THEN
    SUBGOAL_THEN `!a. a IN {num_of_term t | t IN Dom M}
                      ==> valuation (LOWMOD M) (valmod (a0:num,a) v)`
    MP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[valuation; valmod; LOWMOD; Dom_DEF] THEN
      CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[valuation; LOWMOD; Dom_DEF; IN_ELIM_THM]) THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    SUBGOAL_THEN `!P. (!a. a IN {num_of_term t | t IN Dom(M)} ==> P(a)) <=>
                      (!a. a IN Dom(M) ==> P(num_of_term a))`
     (fun th -> REWRITE_TAC[th])
    THENL [REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[valmod; FUN_EQ_THM; o_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[TERM_OF_NUM]]);;

let LOWMOD_INTERPRETATION = prove
 (`!L M. interpretation L (LOWMOD M) = interpretation L M`,
  REWRITE_TAC[FORALL_PAIR_THM; interpretation] THEN
  REWRITE_TAC[Fun_DEF; Dom_DEF; LOWMOD] THEN
  SUBGOAL_THEN `!P x. num_of_term x IN {num_of_term y | P y} <=> x IN P`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_ELIM_THM; IN; NUM_OF_TERM_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  EQ_TAC THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; LENGTH] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `[] :num list`) THEN
    ASM_REWRITE_TAC[ALL; MAP; LENGTH] THEN
    REWRITE_TAC[IN] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV);
    STRIP_TAC THEN FIRST_X_ASSUM
     (MP_TAC o SPEC `CONS (num_of_term h) (MAP num_of_term t)`) THEN
    ASM_REWRITE_TAC[ALL; MAP; LENGTH; LENGTH_MAP] THEN
    REWRITE_TAC[ALL_MAP; IN_ELIM_THM] THEN
    W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC ALL_IMP THEN
      FIRST_ASSUM(EXISTS_TAC o lhand o concl) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[o_THM; NUM_OF_TERM_INJ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[TERM_OF_NUM; GSYM MAP_o; o_DEF] THEN
    SIMP_TAC[MAP_EQ_DEGEN; ALL_T];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `[] :term list`) THEN
    ASM_REWRITE_TAC[ALL; MAP; LENGTH] THEN
    REWRITE_TAC[IN] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV);
    STRIP_TAC THEN FIRST_X_ASSUM
     (MP_TAC o SPEC `CONS (term_of_num h) (MAP term_of_num t)`) THEN
    ASM_REWRITE_TAC[ALL; MAP; LENGTH; LENGTH_MAP] THEN
    W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
     [CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
        ASM_MESON_TAC[TERM_OF_NUM]; ALL_TAC] THEN
      REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC ALL_IMP THEN
      FIRST_ASSUM(EXISTS_TAC o lhand o concl) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_ELIM_THM; o_THM] THEN MESON_TAC[TERM_OF_NUM];
      ALL_TAC] THEN
    REWRITE_TAC[IN] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV)]);;

let LS = prove
 (`!M:(A->bool)#(num->A list->A)#(num->A list->bool) s.
        interpretation (language s) M /\
        ~(Dom(M) = EMPTY) /\
        (!p. p IN s ==> qfree p) /\ M satisfies s
        ==> ?N. interpretation (language s) N /\
                ~(Dom N :num->bool = EMPTY) /\
                N satisfies s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CANON) THEN
  EXISTS_TAC `LOWMOD C` THEN
  ASM_REWRITE_TAC[LOWMOD_DOM_EMPTY; LOWMOD_INTERPRETATION] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [satisfies]) THEN
  REWRITE_TAC[satisfies] THEN SIMP_TAC[LOWMOD_HOLDS] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [valuation]) THEN
  ASM_REWRITE_TAC[valuation] THEN REWRITE_TAC[LOWMOD; Dom_DEF] THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
  MESON_TAC[TERM_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Now the Uniformity Lemma.                                                 *)
(* ------------------------------------------------------------------------- *)

let UNIFORMITY = prove
 (`qfree p /\ (!C v. ~(Dom C = EMPTY) /\
                     valuation(C) v ==> holds C (v:num->term) (ITLIST ?? xs p))
   ==> ?is. (!i x. MEM i is ==> terms(FST(language {p})) (i x)) /\
            !d. pholds(d) (ITLIST (||) (MAP (\i. formsubst i p) is) False)`,
  STRIP_TAC THEN
  MP_TAC(SPEC `{formsubst i q | q IN {p} /\
                                (!x. i x IN terms(FST(language {p})))}`
              COMPACT_DISJ) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ALL_TAC;
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `ps:form list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `MAP (\q. @i. (!x. i x IN terms (FST (language {p}))) /\
                             (q = formsubst i p)) ps` THEN
    REWRITE_TAC[GSYM MAP_o; o_DEF] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      FIRST_ASSUM
       (UNDISCH_TAC o check ((=) `ps:form list` o rand) o concl) THEN
      SPEC_TAC(`ps:form list`,`ps:form list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; MEM] THEN
      DISCH_TAC THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [ALL_TAC; FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
      FIRST_ASSUM(ASSUME_TAC o SELECT_RULE o CONJUNCT1) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
      FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o SPEC_ALL);
      X_GEN_TAC `d:form->bool` THEN
      FIRST_ASSUM(MP_TAC o SPEC `d:form->bool`) THEN
      MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(GSYM MAP_EQ_DEGEN) THEN
      FIRST_ASSUM
       (UNDISCH_TAC o check ((=) `ps:form list` o rand) o concl) THEN
      SPEC_TAC(`ps:form list`,`ps:form list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; MEM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SELECT_RULE) ASSUME_TAC) THEN
      CONJ_TAC THENL [FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT2); ALL_TAC] THEN
      MATCH_MP_TAC ALL_IMP THEN
      FIRST_ASSUM(fun th -> EXISTS_TAC(lhand(concl th)) THEN
                       CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC]) THEN
      X_GEN_TAC `r:form` THEN REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SELECT_RULE o CONJUNCT2) THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT2)]] THEN
  X_GEN_TAC `d:form->bool` THEN
  SUBGOAL_THEN `~((canon_of_prop (language {p}) d) satisfies {(Not p)})`
  ASSUME_TAC THENL
   [REWRITE_TAC[satisfies; IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `canon_of_prop (language {p}) d`) THEN
    REWRITE_TAC[HOLDS_ITLIST_EXISTS; NOT_FORALL_THM; NOT_IMP] THEN
    SUBGOAL_THEN `?v:num->term. valuation (canon_of_prop (language {p}) d) v`
    CHOOSE_TAC THENL
     [MATCH_MP_TAC VALUATION_EXISTS THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      REWRITE_TAC[Dom_DEF; canon_of_prop; IN] THEN
      MESON_TAC[terms_RULES]; ALL_TAC] THEN
    EXISTS_TAC `v:num->term` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[canon_of_prop; Dom_DEF] THEN
      REWRITE_TAC[language; EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
      EXISTS_TAC `V 0` THEN REWRITE_TAC[IN] THEN MESON_TAC[terms_CASES];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
    REWRITE_TAC[GSYM HOLDS] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[valuation; IN] THEN GEN_TAC THEN
    UNDISCH_TAC `valuation (canon_of_prop (language {p}) d) (v:num->term)` THEN
    SPEC_TAC(`v:num->term`,`v:num->term`) THEN
    UNDISCH_TAC `ALL (Dom (canon_of_prop (language {p}) d)) as` THEN
    UNDISCH_TAC `LENGTH (as:term list) = LENGTH (xs:num list)` THEN
    SPEC_TAC(`as:term list`,`as:term list`) THEN
    SPEC_TAC(`xs:num list`,`xs:num list`) THEN
    LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC; MAP2; REVERSE; ITLIST; ALL] THENL
     [REWRITE_TAC[valuation; IN] THEN MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUC_INJ; ITLIST_EXTRA] THEN
    DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[valuation; valmod] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[valuation]) THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[IN]; ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN {(Not p)} ==> qfree q` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[QFREE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM] PSATISFIES_INSTANCES)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[psatisfies; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[Not_DEF; formsubst] THEN REWRITE_TAC[GSYM Not_DEF] THEN
  MESON_TAC[el 3 (CONJUNCTS PHOLDS)]);;
