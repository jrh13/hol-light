(* ========================================================================= *)
(* Refinement of canonical model theorem to consider ground terms only.      *)
(* ========================================================================= *)

let herbase_RULES,herbase_INDUCT,herbase_CASES = new_inductive_definition
  `(~(?c. (c,0) IN fns) ==> herbase fns (V 0)) /\
   (!f l. (f,LENGTH l) IN fns /\ ALL (herbase fns) l
          ==> herbase fns (Fn f l))`;;

(* ------------------------------------------------------------------------- *)
(* Canonical model based on the language of a set of formulas.               *)
(* ------------------------------------------------------------------------- *)

let herbrand = new_definition
  `herbrand (L:(num#num->bool)#(num#num->bool)) M <=>
       (Dom M = herbase (FST L)) /\
       (!f. Fun(M) f = Fn f)`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let HERBRAND_INTERPRETATION = prove
 (`!L M. herbrand L M ==> interpretation L M`,
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  SIMP_TAC[herbrand; interpretation] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[IN] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  ASM_SIMP_TAC[herbase_RULES]);;

let HERBASE_FUNCTIONS = prove
 (`!fns t. t IN herbase fns ==> (functions_term t) SUBSET fns`,
  GEN_TAC THEN REWRITE_TAC[IN] THEN MATCH_MP_TAC herbase_INDUCT THEN
  REWRITE_TAC[functions_term; EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_LIST_UNION; GSYM ALL_MEM; GSYM EX_MEM;
              MEM_MAP] THEN
  MESON_TAC[]);;

let HERBASE_NONEMPTY = prove
 (`!fns. ?t. t IN herbase fns`,
  GEN_TAC THEN REWRITE_TAC[IN] THEN ONCE_REWRITE_TAC[herbase_CASES] THEN
  MESON_TAC[ALL; LENGTH]);;

let HERBRAND_NONEMPTY = prove
 (`!L M. herbrand L M ==> ~(Dom M = {})`,
  SIMP_TAC[herbrand; Dom_DEF; EXTENSION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM; HERBASE_NONEMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Mappings between models and propositional valuations.                     *)
(* ------------------------------------------------------------------------- *)

let herbrand_of_prop = new_definition
  `herbrand_of_prop (L:((num#num)->bool)#((num#num)->bool)) (d:form->bool) =
   herbase(FST L),Fn,\p l. d(Atom p l)`;;

let PROP_OF_HERBRAND_OF_PROP = prove
 (`!p l. prop_of_model (herbrand_of_prop L d) V (Atom p l) = d (Atom p l)`,
  REWRITE_TAC[prop_of_model; herbrand_of_prop; holds; Pred_DEF] THEN
  REPEAT GEN_TAC THEN REPEAT AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN
  SPEC_TAC(`l:term list`,`l:term list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  SPEC_TAC(`h:term`,`t:term`) THEN
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termval; Fun_DEF] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN ASM_REWRITE_TAC[]);;

let HOLDS_HERBRAND_OF_PROP = prove
 (`!p. qfree p ==> (holds (herbrand_of_prop L d) V p <=> pholds d p)`,
  GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC th THEN
   REWRITE_TAC[GSYM(MATCH_MP PHOLDS_PROP_OF_MODEL th)]) THEN
  SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[pholds; qfree; PROP_OF_HERBRAND_OF_PROP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN REFL_TAC);;

let HOLDS_HERBRAND_OF_PROP_GENERAL = prove
 (`qfree p ==> (holds (herbrand_of_prop L d) v p <=> pholds d (formsubst v p))`,
  DISCH_THEN(fun th -> MP_TAC th THEN
   REWRITE_TAC[GSYM(MATCH_MP PHOLDS_PROP_OF_MODEL th)]) THEN
  SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[formsubst; pholds; qfree; PROP_OF_HERBRAND_OF_PROP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN
    REFL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[prop_of_model; herbrand_of_prop; holds] THEN
  REWRITE_TAC[Pred_DEF] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN SIMP_TAC[GSYM TERMSUBST_TERMVAL; Fun_DEF]);;

let HERBRAND_HERBRAND_OF_PROP = prove
 (`!d. herbrand L (herbrand_of_prop L d)`,
  REWRITE_TAC[herbrand; herbrand_of_prop; Dom_DEF; Fun_DEF; FUN_EQ_THM]);;

let INTERPRETATION_HERBRAND_OF_PROP = prove
 (`!L d. interpretation L (herbrand_of_prop L d)`,
  REWRITE_TAC[FORALL_PAIR_THM; interpretation; herbrand_of_prop; Fun_DEF;
              Dom_DEF; IN; ETA_AX] THEN
  MESON_TAC[herbase_RULES; IN]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for satisfiability.                                            *)
(* ------------------------------------------------------------------------- *)

let PSATISFIES_HERBRAND_INSTANCES = prove
 (`(!p. p IN s ==> qfree p) /\
   d psatisfies {formsubst v p | (!x. v x IN herbase(FST L)) /\ p IN s}
   ==> (herbrand_of_prop L d) satisfies s`,
  REWRITE_TAC[satisfies; psatisfies; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  STRIP_TAC THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [herbrand_of_prop; Dom_DEF; valuation] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL[`formsubst v p`; `v:num->term`; `p:form`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `holds (herbrand_of_prop L d) V (formsubst v p)` MP_TAC THENL
   [ASM_MESON_TAC[HOLDS_HERBRAND_OF_PROP; QFREE_FORMSUBST]; ALL_TAC] THEN
  SUBGOAL_THEN `holds (herbrand_of_prop L d) V (formsubst v p) <=>
                holds (herbrand_of_prop L d)
                      (termval (herbrand_of_prop L d) V o v)
                      p`
  SUBST1_TAC THENL
   [REWRITE_TAC[HOLDS_FORMSUBST] THEN
    ASM_MESON_TAC[INTER_EMPTY; QFREE_BV_EMPTY];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    GEN_TAC THEN SPEC_TAC(`(v:num->term) x`,`t:term`) THEN
    MATCH_MP_TAC TERMVAL_TRIV THEN
    REWRITE_TAC[herbrand_of_prop; Fun_DEF]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the Herbrand theorem.                                               *)
(* ------------------------------------------------------------------------- *)

let SATISFIES_SUBSET = prove
 (`!M s t. s SUBSET t /\ M satisfies t ==> M satisfies s`,
  REWRITE_TAC[satisfies; SUBSET] THEN MESON_TAC[]);;

let HERBASE_SUBSET_TERMS = prove
 (`!t. t IN herbase fns ==> t IN terms fns`,
  REWRITE_TAC[IN] THEN MATCH_MP_TAC herbase_INDUCT THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[terms_RULES]);;

let HERBRAND_THEOREM = prove
 (`!s. (!p. p IN s ==> qfree p)
       ==> ((?M:(term->bool)#(num->term list->term)#(num->term list->bool).
                 interpretation (language s) M /\ ~(Dom M = {}) /\
                 M satisfies s) <=>
            (?d. d psatisfies
                 {formsubst v p | (!x. v x IN herbase(functions s)) /\
                                  p IN s}))`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `v:num->term` o MATCH_MP VALUATION_EXISTS) THEN
    EXISTS_TAC `prop_of_model M (v:num->term)` THEN
    MATCH_MP_TAC SATISFIES_PSATISFIES THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; QFREE_FORMSUBST];
      FIRST_ASSUM(MP_TAC o MATCH_MP SATISFIES_INSTANCES) THEN
      DISCH_THEN(MP_TAC o SPEC `s:form->bool`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
                   SATISFIES_SUBSET) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; language] THEN
      MESON_TAC[HERBASE_SUBSET_TERMS; SUBSET]];
    EXISTS_TAC `herbrand_of_prop (language s) d` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INTERPRETATION_HERBRAND_OF_PROP];
      REWRITE_TAC[herbrand_of_prop; Dom_DEF; language;
                  EXTENSION; NOT_IN_EMPTY] THEN
      REWRITE_TAC[IN] THEN MESON_TAC[herbase_RULES; ALL; LENGTH];
      ASM_SIMP_TAC[PSATISFIES_HERBRAND_INSTANCES; language]]]);;
