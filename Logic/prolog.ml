(* ========================================================================= *)
(* Prolog-style backchaining for definite and Horn clauses.                  *)
(* ========================================================================= *)

let SATISFIES_IMAGE = prove
 (`M satisfies (IMAGE f s) <=>
   !x v. valuation(M) v /\ x IN s ==> holds M v (f x)`,
  REWRITE_TAC[satisfies; IN_IMAGE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Definitions of definite and Horn clauses.                                 *)
(* ------------------------------------------------------------------------- *)

let definite = new_definition
  `definite(cl) <=> clause(cl) /\ (CARD {p | p IN cl /\ positive p} = 1)`;;

let horn = new_definition
  `horn(cl) <=> clause(cl) /\ CARD {p | p IN cl /\ positive p} <= 1`;;

(* ------------------------------------------------------------------------- *)
(* Trivially, definite is a special case of Horn.                            *)
(* ------------------------------------------------------------------------- *)

let DEFINITE_IMP_HORN = prove
 (`!cl. definite(cl) ==> horn(cl)`,
  SIMP_TAC[definite; horn; LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Show first how to reduce the Horn case to the definite case.              *)
(* ------------------------------------------------------------------------- *)

let falsify = new_definition
  `falsify ff cl = if definite(cl) then cl else ff INSERT cl`;;

let FALSIFY_FINITE = prove
 (`FINITE(cl) ==> FINITE(falsify ff cl)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[falsify] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[FINITE_RULES]);;

let FALSIFY_DEFINITE = prove
 (`horn(cl) ==> definite(falsify (Atom P args) cl)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[falsify] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(definite cl)` THEN
  REWRITE_TAC[horn; definite] THEN
  ASM_CASES_TAC `clause cl` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{p | p IN Atom P args INSERT cl /\ positive p} =
                (Atom P args) INSERT {p | p IN cl /\ positive p}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
    SUBGOAL_THEN `positive(Atom P args)` (fun th -> MESON_TAC[th]) THEN
    REWRITE_TAC[positive; negative; ATOM] THEN
    REWRITE_TAC[Not_DEF; form_DISTINCT]; ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[clause; IN_INSERT; FINITE_INSERT] THEN
    ASM_MESON_TAC[clause; literal; ATOM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p | p IN cl /\ positive p}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cl:form->bool` THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[clause]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(ARITH_RULE `x <= 1 /\ ~(x = 1) ==> (SUC x = 1)`) THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `Atom P args IN {p | p IN cl /\ positive p}` THEN
  SUBGOAL_THEN `{p | p IN cl /\ positive p} = {}`
   (fun th -> REWRITE_TAC[th; NOT_IN_EMPTY]) THEN
  ONCE_REWRITE_TAC[GSYM HAS_SIZE_0] THEN ASM_REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC(ARITH_RULE `x <= 1 /\ ~(x = 1) ==> (x = 0)`) THEN
  ASM_REWRITE_TAC[]);;

let HOLDS_FALSIFY = prove
 (`FINITE(cl) /\ holds M v (interp cl)
   ==> holds M v (interp(falsify ff cl))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[FALSIFY_FINITE; HOLDS_INTERP] THEN
  REWRITE_TAC[falsify] THEN COND_CASES_TAC THEN SIMP_TAC[IN_INSERT] THEN
  MESON_TAC[]);;

let REDUCE_HORN_DEFINITE = prove
 (`(!c. c IN s ==> clause c) /\
   ~((Atom ff []) IN UNIONS s) /\ ~(Not(Atom ff []) IN UNIONS s)
   ==> (~(satisfiable (U:A->bool) (IMAGE interp s)) <=>
        !M. ~(Dom M = {}) /\
            M satisfies (IMAGE interp (IMAGE (falsify (Atom ff [])) s))
            ==> !v:num->A. valuation(M) v ==> holds M v (Atom ff []))`,
  REWRITE_TAC[satisfiable] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[NOT_EXISTS_THM; GSYM IMAGE_o] THEN
  REWRITE_TAC[SATISFIES_IMAGE] THEN EQ_TAC THENL
   [MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    ASM_CASES_TAC `(Dom M):A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`cl:form->bool`; `v:num->A`] THEN
    REWRITE_TAC[NOT_IMP] THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`cl:form->bool`; `v:num->A`]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[o_THM; falsify] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `holds M (v:num->A) (interp (Atom ff [] INSERT cl)) <=>
                  holds M v (Atom ff []) \/ holds M v (interp cl)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `FINITE (cl:form->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[clause]; ALL_TAC] THEN
      UNDISCH_TAC `~(holds M (v:num->A) (interp cl))` THEN
      ASM_SIMP_TAC[HOLDS_INTERP; FINITE_INSERT; IN_INSERT] THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC HOLDS_VALUATION THEN
    REWRITE_TAC[FV; NOT_IN_EMPTY; MAP; LIST_UNION]; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o SPEC
   `((Dom M):A->bool),Fun M,
    (\p args. if (p = ff) /\ (args = []) then F else Pred M p args)`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[holds; Pred_DEF; MAP; NOT_FORALL_THM] THEN
    MATCH_MP_TAC VALUATION_EXISTS THEN ASM_REWRITE_TAC[Dom_DEF]] THEN
  ASM_REWRITE_TAC[Dom_DEF] THEN
  MAP_EVERY X_GEN_TAC [`cl:form->bool`; `v:num->A`] THEN
  SUBGOAL_THEN
   `valuation(Dom M,Fun M,
         (\p args. if (p = ff) /\ (args = []) then F else Pred M p args)) v =
    valuation M (v:num->A)`
  SUBST1_TAC THENL [REWRITE_TAC[valuation; Dom_DEF]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPECL [`cl:form->bool`; `v:num->A`])) THEN
  SUBGOAL_THEN `FINITE (cl:form->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[clause]; ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM; HOLDS_INTERP; FINITE_INSERT; IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:form` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HOLDS_FALSIFY THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[HOLDS_INTERP] THEN EXISTS_TAC `p:form` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `holds M (v:num->A) p` THEN
  MATCH_MP_TAC EQ_IMP THEN
  SPEC_TAC(`v:num->A`,`v:num->A`) THEN
  MATCH_MP_TAC HOLDS_PREDICATES THEN
  REWRITE_TAC[Fun_DEF; Dom_DEF; Pred_DEF] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `zs:(A)list`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
  MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
  SUBGOAL_THEN `~((Atom ff []) IN cl) /\ ~(Not(Atom ff []) IN cl)` MP_TAC THENL
   [UNDISCH_TAC `~((Atom ff []) IN UNIONS s)` THEN
    UNDISCH_TAC `~(Not(Atom ff []) IN UNIONS s)` THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TAUT `~a /\ ~b ==> ~c <=> c ==> a \/ b`] THEN
  SUBGOAL_THEN `literal p` MP_TAC THENL
   [ASM_MESON_TAC[clause]; ALL_TAC] THEN
  REWRITE_TAC[literal; ATOM] THEN
  STRIP_TAC THEN UNDISCH_TAC `p:form IN cl` THEN
  ASM_REWRITE_TAC[predicates_form; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ;
                  Not_DEF; IN_UNION; NOT_IN_EMPTY] THEN
  MESON_TAC[LENGTH_EQ_NIL]);;

(* ------------------------------------------------------------------------- *)
(* Minimal model.                                                            *)
(* ------------------------------------------------------------------------- *)

let minmodel = new_definition
  `minmodel s =
     herbase(functions s),
     Fn,
     (\p zs. !H. (Dom(H) = herbase(functions s)) /\
                 (Fun(H) = Fn) /\
                 H satisfies s
                 ==> Pred(H) p zs)`;;

(* ------------------------------------------------------------------------- *)
(* Is minimal w.r.t. deduction of atomic formulas.                           *)
(* ------------------------------------------------------------------------- *)

let MINMODEL_MINIMAL = prove
 (`!p v s.
        atom p
        ==> (holds (minmodel s) v p <=>
             !H. (Dom(H) = herbase(functions s)) /\
                 (Fun(H) = Fn) /\ H satisfies s
                 ==> holds H v p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ATOM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `args:term list`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[holds; minmodel; Pred_DEF; Fun_DEF] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC
   `H:(term->bool)#((num->((term)list->term))#(num->((term)list->bool)))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `termval
    (herbase (functions s),
     Fn,
     (\p zs.
          !H. (Dom H = herbase (functions s)) /\ (Fun H = Fn) /\ H satisfies s
              ==> Pred H p zs)) =
    termval H`
   (fun th -> REWRITE_TAC[th]) THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `v:num->term` THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `t:term` THEN
  SPEC_TAC(`v:num->term`,`v:num->term`) THEN
  MATCH_MP_TAC TERMVAL_FUNCTIONS THEN ASM_REWRITE_TAC[Fun_DEF]);;

(* ------------------------------------------------------------------------- *)
(* And_DEF is indeed a model of the original clauses.                            *)
(* ------------------------------------------------------------------------- *)

let HOLDS_ITLIST_IMP = prove
 (`!M v asm c.
        holds M v (ITLIST (-->) asm c) <=>
        (?p. MEM p asm /\ ~(holds M v p)) \/ holds M v c`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; ITLIST; HOLDS] THEN
  MESON_TAC[]);;

let breakhorn = new_definition
  `breakhorn(cl) =
        if definite cl then
          let p = @p. p IN cl /\ positive p in
          MAP (~~) (list_of_set(cl DELETE p)),p
        else MAP (~~) (list_of_set cl),False`;;

let hypotheses = new_definition
  `hypotheses cl = FST(breakhorn cl)`;;

let conclusion = new_definition
  `conclusion cl = SND(breakhorn cl)`;;

let HOLDS_HORN = prove
 (`!cl. horn(cl)
        ==> ALL atom (hypotheses cl) /\
            (if definite(cl) then atom(conclusion cl)
             else (conclusion cl = False)) /\
            !M (v:num->A).
                holds M v (interp cl) <=>
                holds M v (ITLIST (-->) (hypotheses cl) (conclusion cl))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[horn] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `x <= 1 ==> (x = 0) \/ (x = 1)`)) THEN
  ASM_REWRITE_TAC[definite; ARITH; conclusion; hypotheses; breakhorn] THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `ALL (\p. literal p /\ negative p) (list_of_set cl)`
      MP_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[clause]) THEN
        ASM_SIMP_TAC[GSYM ALL_MEM; MEM_LIST_OF_SET] THEN
        SUBGOAL_THEN `{p | p IN cl /\ positive p} = {}` MP_TAC THENL
         [ONCE_REWRITE_TAC[GSYM HAS_SIZE_0] THEN
          ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `cl:form->bool` THEN ASM_REWRITE_TAC[] THEN
          SIMP_TAC[SUBSET; IN_ELIM_THM];
          REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
          MESON_TAC[positive]];
        REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC(ONCE_REWRITE_RULE
         [IMP_CONJ] ALL_IMP) THEN
        SIMP_TAC[o_THM; negate] THEN X_GEN_TAC `p:form` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(X_CHOOSE_THEN `q:form` SUBST_ALL_TAC o
                      GEN_REWRITE_RULE I [negative]) THEN
        REWRITE_TAC[Not_DEF; form_INJ] THEN
        UNDISCH_TAC `literal (Not q)` THEN
        SIMP_TAC[literal; ATOM; Not_DEF; form_DISTINCT; form_INJ] THEN
        MESON_TAC[]];
      REPEAT GEN_TAC THEN REWRITE_TAC[interp] THEN
      SPEC_TAC(`list_of_set(cl:form->bool)`,`l:form list`) THEN
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC[ITLIST; HOLDS; MAP; HOLDS_NEGATE] THEN
      CONV_TAC TAUT]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p | p IN cl /\ positive p}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cl:form->bool` THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[clause]; ALL_TAC] THEN
  SUBGOAL_THEN `{p | p IN cl /\ positive p} HAS_SIZE (SUC 0)` MP_TAC THENL
   [ASM_REWRITE_TAC[ARITH; HAS_SIZE]; ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE_SUC] THEN STRIP_TAC THEN LET_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `p IN cl /\ positive p` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN CONV_TAC SELECT_CONV THEN
    UNDISCH_TAC `~({p | p IN cl /\ positive p} = {})` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:form`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE_0] THEN
  REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `ALL (\p. literal p /\ negative p)
                      (list_of_set(cl DELETE p))`
    MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[clause]) THEN
      ASM_SIMP_TAC[GSYM ALL_MEM; MEM_LIST_OF_SET; FINITE_DELETE] THEN
      SUBGOAL_THEN `!q. q IN (cl DELETE p) ==> literal q /\ ~(positive q)`
       (fun th -> MESON_TAC[th; positive]) THEN
      REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC(ONCE_REWRITE_RULE
     [IMP_CONJ] ALL_IMP) THEN
    SIMP_TAC[o_THM; negate] THEN X_GEN_TAC `r:form` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:form` SUBST_ALL_TAC o
                  GEN_REWRITE_RULE I [negative]) THEN
    REWRITE_TAC[Not_DEF; form_INJ] THEN
    UNDISCH_TAC `literal (Not q)` THEN
    SIMP_TAC[literal; ATOM; Not_DEF; form_DISTINCT; form_INJ] THEN
    MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `literal p` MP_TAC THENL
     [ASM_MESON_TAC[clause]; ALL_TAC] THEN
    REWRITE_TAC[literal] THEN STRIP_TAC THEN
    UNDISCH_TAC `positive p` THEN ASM_REWRITE_TAC[positive; negative] THEN
    REWRITE_TAC[Not_DEF; form_INJ; GSYM EXISTS_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[clause]) THEN
  ASM_SIMP_TAC[HOLDS_INTERP] THEN
  REWRITE_TAC[HOLDS_ITLIST_IMP; MEM_MAP] THEN
  ASM_SIMP_TAC[MEM_LIST_OF_SET; FINITE_DELETE] THEN
  REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[HOLDS_NEGATE]);;

let MINMODEL_MODEL = prove
 (`(!cl. cl IN s ==> definite(cl))
   ==> minmodel(IMAGE interp s) satisfies (IMAGE interp s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[satisfies] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ_ALT; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `cl:form->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `definite cl` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `horn cl` ASSUME_TAC THENL
   [ASM_MESON_TAC[DEFINITE_IMP_HORN]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o INST_TYPE [`:term`,`:A`] o MATCH_MP HOLDS_HORN) THEN
  MAP_EVERY ABBREV_TAC [`asm = hypotheses cl`; `c = conclusion cl`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:num->term` THEN DISCH_TAC THEN
  REWRITE_TAC[HOLDS_ITLIST_IMP] THEN
  ONCE_REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ ~b) <=> a ==> b`] THEN
  REWRITE_TAC[ALL_MEM] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  ASM_SIMP_TAC[MINMODEL_MINIMAL] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ALL (\c. !H. (Dom H = herbase (functions (IMAGE interp s))) /\
                 (Fun H = Fn) /\
                 H satisfies IMAGE interp s
                 ==> holds H v c) asm`
  MP_TAC THENL
   [MATCH_MP_TAC ALL_IMP THEN
    EXISTS_TAC `holds (minmodel (IMAGE interp s)) v` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ALL_MEM; MINMODEL_MINIMAL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM FORALL_ALL] THEN
  MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC
   `H:(term->bool)#((num->((term)list->term))#(num->((term)list->bool)))` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `holds H (v:num->term) (ITLIST (-->) asm c)` MP_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[satisfies; IN_IMAGE]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    UNDISCH_TAC `valuation (minmodel (IMAGE interp s)) v` THEN
    ASM_REWRITE_TAC[valuation; Dom_DEF; minmodel]; ALL_TAC] THEN
  REWRITE_TAC[HOLDS_ITLIST_IMP] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let CONCLUSION_DEFINITE = prove
 (`!cl p. definite cl /\ p IN cl /\ positive p
          ==> (conclusion cl = p)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[conclusion; breakhorn] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[SND] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `q:form` THEN
  REWRITE_TAC[] THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `definite cl` THEN REWRITE_TAC[definite] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b <=> ~b ==> ~a`] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= a ==> ~(a = 1)`) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {p, (q:form)}` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_SING; NOT_IN_EMPTY; ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cl:form->bool` THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[clause]);;

let CONCLUSION_DEFINITE_ALT = prove
 (`!cl p. clause cl /\ p IN cl /\ positive p /\
          (!q. q IN cl /\ ~(q = p) ==> negative q)
          ==> (conclusion cl = p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONCLUSION_DEFINITE THEN
  ASM_REWRITE_TAC[definite] THEN
  SUBGOAL_THEN `{p | p IN cl /\ positive p} = {p}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    ASM_MESON_TAC[positive];
    SIMP_TAC[CARD_CLAUSES; NOT_IN_EMPTY; FINITE_RULES; ARITH]]);;

let HYPOTHESES_CONCLUSION = prove
 (`!cl. definite cl
        ==> (set_of_list(hypotheses cl) =
             IMAGE (~~) (cl DELETE (conclusion cl)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[hypotheses; breakhorn; conclusion] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[IN_IMAGE; EXTENSION; IN_SET_OF_LIST; IN_DELETE] THEN
  REWRITE_TAC[MEM_MAP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[definite; clause]) THEN
  ASM_SIMP_TAC[MEM_LIST_OF_SET; FINITE_DELETE] THEN
  REWRITE_TAC[IN_DELETE] THEN REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Backchaining.                                                             *)
(* ------------------------------------------------------------------------- *)

let gbackchain_RULES,gbackchain_INDUCT,gbackchain_CASES =
   new_inductive_definition
    `!cl i ns. cl IN s /\
               (!x. i(x) IN herbase(functions(IMAGE interp s))) /\
               ALL2 (gbackchain s) ns (MAP (formsubst i) (hypotheses cl))
               ==> gbackchain s (ITLIST (+) ns 1)
                                (formsubst i (conclusion cl))`;;

let ALL2_TRIV = prove
 (`!l1 l2. ALL2 (\n. P) l1 l2 <=> (LENGTH l1 = LENGTH l2) /\ ALL P l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL; LENGTH; NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[CONJ_ACI]);;

let GBACKCHAIN_SOUND = prove
 (`(!cl. cl IN s ==> definite(cl)) /\ valuation (minmodel (IMAGE interp s)) v
   ==> !n p. gbackchain s n p ==> holds (minmodel(IMAGE interp s)) v p`,
  STRIP_TAC THEN MATCH_MP_TAC gbackchain_INDUCT THEN
  REWRITE_TAC[ALL2_TRIV] THEN
  MAP_EVERY X_GEN_TAC [`cl:form->bool`; `i:num->term`; `ns:num list`] THEN
  REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MINMODEL_MODEL) THEN
  REWRITE_TAC[satisfies] THEN
  DISCH_THEN(MP_TAC o SPEC
   `termval (minmodel (IMAGE interp s)) (v:num->term) o (i:num->term)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `interp cl`) THEN ANTS_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `horn cl` MP_TAC THENL
     [ASM_MESON_TAC[DEFINITE_IMP_HORN]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o INST_TYPE [`:term`,`:A`] o MATCH_MP HOLDS_HORN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HOLDS_ITLIST_IMP] THEN
    REWRITE_TAC[GSYM HOLDS_FORMSUBST] THEN
    UNDISCH_TAC `ALL (holds (minmodel (IMAGE interp s)) v)
                     (MAP (formsubst i) (hypotheses cl))` THEN
    REWRITE_TAC[ALL_MAP] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REWRITE_TAC[o_THM] THEN MESON_TAC[]] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[IN_IMAGE]] THEN
  REWRITE_TAC[valuation; o_THM] THEN X_GEN_TAC `x:num` THEN
  SUBGOAL_THEN `i(x:num) IN herbase (functions (IMAGE interp s))` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`(i:num->term) x`,`t:term`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
  W(EXISTS_TAC o fst o dest_exists o snd) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `interpretation (functions(IMAGE interp s),predicates(IMAGE interp s))
                   (minmodel (IMAGE interp s))`
  MP_TAC THENL
   [MATCH_MP_TAC HERBRAND_INTERPRETATION THEN
    REWRITE_TAC[herbrand; minmodel; Dom_DEF; Fun_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
  ASM_SIMP_TAC[HERBASE_FUNCTIONS]);;

let GBACKCHAIN_COMPLETE = prove
 (`(!cl. cl IN s ==> definite(cl)) /\
   atom(p) /\ (FV p = {}) /\ (!v. holds (minmodel (IMAGE interp s)) v p)
   ==> ?n. gbackchain s n p`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MINMODEL_MINIMAL th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `v:num->term`) THEN
  DISCH_THEN(MP_TAC o SPEC
   `herbase(functions(IMAGE interp s)),Fn,
    (\p tms. ?n. gbackchain s n (Atom p tms))`) THEN
  REWRITE_TAC[Dom_DEF; Fun_DEF] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `P:num` MP_TAC o GEN_REWRITE_RULE I [ATOM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `tms:term list` SUBST_ALL_TAC) THEN
  REWRITE_TAC[holds; Pred_DEF] THEN
  MATCH_MP_TAC(TAUT `(b <=> c) /\ a ==> (a ==> b) ==> c`) THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
    UNDISCH_TAC `FV(Atom P tms) = {}` THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FV; IN_LIST_UNION] THEN
    REWRITE_TAC[EX_MAP] THEN REWRITE_TAC[GSYM ALL_MEM; GSYM EX_MEM] THEN
    REWRITE_TAC[o_THM; NOT_EXISTS_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `t:term` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `termval(herbase (functions (IMAGE interp s)),
                        Fn,(\p tms. ?n. gbackchain s n (Atom p tms))) V t` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TERMVAL_VALUATION THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`t:term`,`t:term`) THEN MATCH_MP_TAC TERMVAL_TRIV THEN
    REWRITE_TAC[Fun_DEF]; ALL_TAC] THEN
  REWRITE_TAC[satisfies] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[valuation; Dom_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `cl:form->bool`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `horn cl` MP_TAC THENL
   [ASM_MESON_TAC[DEFINITE_IMP_HORN]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o INST_TYPE [`:term`,`:A`] o MATCH_MP HOLDS_HORN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HOLDS_ITLIST_IMP] THEN
  REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ ~b) <=> a ==> b`] THEN
  REWRITE_TAC[ALL_MEM] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  ABBREV_TAC `gbmod = herbase (functions (IMAGE interp s)),
                      Fn,
                      (\p tms. ?n. gbackchain s n (Atom p tms))` THEN
  SUBGOAL_THEN
   `!p. atom p ==> (holds gbmod v p <=>
                    ?n. gbackchain s n (formsubst v p))`
  ASSUME_TAC THENL
   [SIMP_TAC[ATOM; LEFT_IMP_EXISTS_THM] THEN
    EXPAND_TAC "gbmod" THEN REWRITE_TAC[HOLDS] THEN
    REWRITE_TAC[Pred_DEF; formsubst] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `t:term` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN
    SPEC_TAC(`t:term`,`t:term`) THEN SPEC_TAC(`v:num->term`,`v:num->term`) THEN
    MATCH_MP_TAC TERMSUBST_TERMVAL THEN REWRITE_TAC[Fun_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `holds gbmod v (conclusion cl) <=>
    ?n. gbackchain s n (formsubst v (conclusion cl))`
  SUBST1_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (holds gbmod v) (hypotheses cl) <=>
    ALL (\p. ?n. gbackchain s n (formsubst v p)) (hypotheses cl)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `ALL atom (hypotheses cl)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `!b. (a ==> b) /\ (b ==> c) ==> a ==> c`) THEN EXISTS_TAC
   `?ns. ALL2 (gbackchain s) ns (MAP (formsubst v) (hypotheses cl))` THEN
  CONJ_TAC THENL
   [SPEC_TAC(`hypotheses cl`,`l:form list`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[ALL; MAP] THENL
     [EXISTS_TAC `[]:num list` THEN REWRITE_TAC[ALL2]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC) THEN
    FIRST_ASSUM(UNDISCH_TAC o check is_imp o concl) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `ns:num list`) THEN
    EXISTS_TAC `CONS (n:num) ns` THEN ASM_REWRITE_TAC[ALL2]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ns:num list`) THEN
  EXISTS_TAC `ITLIST (+) ns 1` THEN
  MATCH_MP_TAC gbackchain_RULES THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combine these results.                                                    *)
(* ------------------------------------------------------------------------- *)

let GBACKCHAIN_MINIMAL = prove
 (`!s p. (!cl. cl IN s ==> definite cl) /\ atom p /\ (FV p = {})
         ==> !v. holds (minmodel (IMAGE interp s)) v p <=> ?n. gbackchain s n p`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC GBACKCHAIN_COMPLETE THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    ASM_SIMP_TAC[HOLDS_VALUATION; NOT_IN_EMPTY];
    DISCH_TAC THEN
    SUBGOAL_THEN `?w. valuation (minmodel (IMAGE interp s)) w`
      (X_CHOOSE_TAC `w:num->term`)
    THENL
     [MATCH_MP_TAC VALUATION_EXISTS THEN
      MATCH_MP_TAC HERBRAND_NONEMPTY THEN
      REWRITE_TAC[herbrand; minmodel; Dom_DEF; Fun_DEF] THEN
      EXISTS_TAC `functions(IMAGE interp s),predicates summat` THEN
      REWRITE_TAC[FST]; ALL_TAC] THEN
    SUBGOAL_THEN `holds (minmodel (IMAGE interp s)) w p` MP_TAC THENL
     [UNDISCH_TAC `?n. gbackchain s n p` THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      SPEC_TAC(`p:form`,`p:form`) THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      MATCH_MP_TAC GBACKCHAIN_SOUND THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HOLDS_VALUATION; NOT_IN_EMPTY]]);;

(* ------------------------------------------------------------------------- *)
(* A free-variable version, also considering valuation restriction.          *)
(* (This doesn't really matter for the ground case, above.)                  *)
(* ------------------------------------------------------------------------- *)

let iminmodel = new_definition
  `iminmodel s =
     terms(functions s),
     Fn,
     (\p zs. !C. (Dom(C) = terms(functions s)) /\
                 (Fun(C) = Fn) /\
                 (!v p. p IN s /\ valuation C v ==> holds C v p)
                 ==> Pred(C) p zs)`;;

let IMINMODEL_MINIMAL = prove
 (`!p v s.
      atom p
      ==> (holds (iminmodel s) v p <=>
           !C. (Dom(C) = terms(functions s)) /\
               (Fun(C) = Fn) /\
               (!v q. q IN s /\ valuation C v ==> holds C v q)
               ==> holds C v p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ATOM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `args:term list`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[holds; iminmodel; Pred_DEF; Fun_DEF] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC
   `C:(term->bool)#((num->((term)list->term))#(num->((term)list->bool)))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `termval
    (terms (functions s),
     Fn,
     (\p zs.
          !C. (Dom C = terms (functions s)) /\ (Fun C = Fn) /\
              (!v p. p IN s /\ valuation C v ==> holds C v p)
              ==> Pred C p zs)) =
    termval C`
   (fun th -> REWRITE_TAC[th]) THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `w:num->term` THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `t:term` THEN
  SPEC_TAC(`w:num->term`,`w:num->term`) THEN
  MATCH_MP_TAC TERMVAL_FUNCTIONS THEN ASM_REWRITE_TAC[Fun_DEF]);;

let IMINMODEL_MODEL = prove
 (`(!cl. cl IN s ==> definite(cl))
   ==> !v p. p IN s /\ (!x. v(x) IN terms(functions(IMAGE interp s)))
             ==> holds (iminmodel(IMAGE interp s)) v (interp p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  X_GEN_TAC `cl:form->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `definite cl` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `horn cl` ASSUME_TAC THENL
   [ASM_MESON_TAC[DEFINITE_IMP_HORN]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o INST_TYPE [`:term`,`:A`] o MATCH_MP HOLDS_HORN) THEN
  MAP_EVERY ABBREV_TAC [`asm = hypotheses cl`; `c = conclusion cl`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:num->term` THEN DISCH_TAC THEN
  REWRITE_TAC[HOLDS_ITLIST_IMP] THEN
  ONCE_REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ ~b) <=> a ==> b`] THEN
  REWRITE_TAC[ALL_MEM] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  ASM_SIMP_TAC[IMINMODEL_MINIMAL] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ALL (\c. !C. (Dom C = terms (functions (IMAGE interp s))) /\
                 (Fun C = Fn) /\
                 (!v p. p IN (IMAGE interp s) /\ valuation C v ==> holds C v p)
                 ==> holds C v c) asm`
  MP_TAC THENL
   [MATCH_MP_TAC ALL_IMP THEN
    EXISTS_TAC `holds (iminmodel (IMAGE interp s)) v` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:form` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN `atom p`
     (fun th -> REWRITE_TAC[MATCH_MP IMINMODEL_MINIMAL th]) THEN
    ASM_MESON_TAC[ALL_MEM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM FORALL_ALL] THEN
  MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC
   `C:(term->bool)#((num->((term)list->term))#(num->((term)list->bool)))` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `holds C (v:num->term) (ITLIST (-->) asm c)` MP_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[valuation; Dom_DEF] THEN ASM_MESON_TAC[IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[HOLDS_ITLIST_IMP] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let IMINMODEL_INTERPRETATION = prove
 (`!s. interpretation(language s) (iminmodel s)`,
  GEN_TAC THEN REWRITE_TAC[interpretation; iminmodel; language; Dom_DEF] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[Fun_DEF; IN] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  ASM_SIMP_TAC[terms_RULES]);;

let ibackchain_RULES,ibackchain_INDUCT,ibackchain_CASES =
   new_inductive_definition
    `!cl i ns. cl IN s /\ (!x. i(x) IN terms(functions(IMAGE interp s))) /\
               ALL2 (ibackchain s) ns (MAP (formsubst i) (hypotheses cl))
               ==> ibackchain s (ITLIST (+) ns 1)
                                (formsubst i (conclusion cl))`;;

let IBACKCHAIN_SOUND = prove
 (`(!cl. cl IN s ==> definite(cl))
   ==> !v n p. ibackchain s n p /\
               (!x. v(x) IN terms(functions(IMAGE interp s)))
               ==> holds (iminmodel(IMAGE interp s)) v p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC ibackchain_INDUCT THEN REWRITE_TAC[ALL2_TRIV] THEN
  MAP_EVERY X_GEN_TAC [`cl:form->bool`; `i:num->term`; `ns:num list`] THEN
  REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN STRIP_TAC THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IMINMODEL_MODEL) THEN
  DISCH_THEN(MP_TAC o SPEC
   `termval (iminmodel (IMAGE interp s)) (v:num->term) o (i:num->term)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `cl:form->bool`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `horn cl` MP_TAC THENL
   [ASM_MESON_TAC[DEFINITE_IMP_HORN]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o INST_TYPE [`:term`,`:A`] o MATCH_MP HOLDS_HORN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HOLDS_ITLIST_IMP] THEN
  REWRITE_TAC[GSYM HOLDS_FORMSUBST] THEN
  MATCH_MP_TAC(TAUT `a /\ ~b ==> ((a ==> b \/ c) ==> c)`) THEN CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `termval(iminmodel (IMAGE interp s)) v (i(x:num)) IN
                  Dom(iminmodel (IMAGE interp s))`
    MP_TAC THENL [ALL_TAC; REWRITE_TAC[iminmodel; Dom_DEF]] THEN
    MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
    EXISTS_TAC `{}:(num#num)->bool` THEN CONJ_TAC THENL
     [MP_TAC(SPEC `IMAGE interp s` IMINMODEL_INTERPRETATION) THEN
      REWRITE_TAC[language] THEN MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
      SUBGOAL_THEN `i(x:num) IN terms(FST(language(IMAGE interp s)))`
      MP_TAC THENL [ASM_REWRITE_TAC[language; FST]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP STUPID_CANONDOM_LEMMA) THEN
      REWRITE_TAC[language; FST];
      ASM_REWRITE_TAC[valuation; iminmodel; Dom_DEF]];
    ALL_TAC] THEN
  UNDISCH_TAC `ALL
       (\p. (!x. v x IN terms (functions (IMAGE interp s)))
            ==> holds (iminmodel (IMAGE interp s)) v p)
       (MAP (formsubst i) (hypotheses cl))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL_MAP] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REWRITE_TAC[o_THM] THEN MESON_TAC[]);;

let IBACKCHAIN_COMPLETE = prove
 (`(!cl. cl IN s ==> definite(cl)) /\
   atom(p) /\
   (!v. (!x. v(x) IN terms(functions(IMAGE interp s)))
        ==> holds (iminmodel (IMAGE interp s)) v p)
   ==> ?n. ibackchain s n p`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP IMINMODEL_MINIMAL th]) THEN
  DISCH_THEN(MP_TAC o SPEC `V`) THEN ANTS_TAC THENL
   [REWRITE_TAC[terms_RULES; IN]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
   `terms(functions(IMAGE interp s)),Fn,
    (\p tms. ?n. ibackchain s n (Atom p tms))`) THEN
  REWRITE_TAC[Dom_DEF; Fun_DEF] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `P:num` MP_TAC o GEN_REWRITE_RULE I [ATOM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `tms:term list` SUBST_ALL_TAC) THEN
  REWRITE_TAC[holds; Pred_DEF] THEN
  MATCH_MP_TAC(TAUT `(b <=> c) /\ a ==> (a ==> b) ==> c`) THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
    REWRITE_TAC[GSYM ALL_MEM; GSYM EX_MEM] THEN
    X_GEN_TAC `t:term` THEN DISCH_TAC THEN
    SPEC_TAC(`t:term`,`t:term`) THEN MATCH_MP_TAC TERMVAL_TRIV THEN
    REWRITE_TAC[Fun_DEF]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `cl:form->bool`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `horn cl` MP_TAC THENL
   [ASM_MESON_TAC[DEFINITE_IMP_HORN]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o INST_TYPE [`:term`,`:A`] o MATCH_MP HOLDS_HORN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HOLDS_ITLIST_IMP] THEN
  REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ ~b) <=> a ==> b`] THEN
  REWRITE_TAC[ALL_MEM] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  ABBREV_TAC `gbmod = terms (functions (IMAGE interp s)),
                      Fn,
                      (\p tms. ?n. ibackchain s n (Atom p tms))` THEN
  SUBGOAL_THEN
   `!p. atom p ==> (holds gbmod v p <=>
                    ?n. ibackchain s n (formsubst v p))`
  ASSUME_TAC THENL
   [SIMP_TAC[ATOM; LEFT_IMP_EXISTS_THM] THEN
    EXPAND_TAC "gbmod" THEN REWRITE_TAC[HOLDS] THEN
    REWRITE_TAC[Pred_DEF; formsubst] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `t:term` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN
    SPEC_TAC(`t:term`,`t:term`) THEN SPEC_TAC(`v:num->term`,`v:num->term`) THEN
    MATCH_MP_TAC TERMSUBST_TERMVAL THEN REWRITE_TAC[Fun_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `holds gbmod v (conclusion cl) <=>
    ?n. ibackchain s n (formsubst v (conclusion cl))`
  SUBST1_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (holds gbmod v) (hypotheses cl) <=>
    ALL (\p. ?n. ibackchain s n (formsubst v p)) (hypotheses cl)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `ALL atom (hypotheses cl)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `!b. (a ==> b) /\ (b ==> c) ==> a ==> c`) THEN EXISTS_TAC
   `?ns. ALL2 (ibackchain s) ns (MAP (formsubst v) (hypotheses cl))` THEN
  CONJ_TAC THENL
   [SPEC_TAC(`hypotheses cl`,`l:form list`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[ALL; MAP] THENL
     [EXISTS_TAC `[]:num list` THEN REWRITE_TAC[ALL2]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC) THEN
    FIRST_ASSUM(UNDISCH_TAC o check is_imp o concl) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `ns:num list`) THEN
    EXISTS_TAC `CONS (n:num) ns` THEN ASM_REWRITE_TAC[ALL2]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ns:num list`) THEN
  EXISTS_TAC `ITLIST (+) ns 1` THEN
  MATCH_MP_TAC ibackchain_RULES THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `valuation gbmod (v:num->term)` THEN
  EXPAND_TAC "gbmod" THEN REWRITE_TAC[valuation; Dom_DEF]);;

let IBACKCHAIN_MINIMAL = prove
 (`!s p. (!cl. cl IN s ==> definite cl) /\ atom p
         ==> ((!v. (!x. v(x) IN terms(functions(IMAGE interp s)))
                   ==> holds (iminmodel(IMAGE interp s)) v p) <=>
              ?n. ibackchain s n p)`,
  MESON_TAC[IBACKCHAIN_SOUND; IBACKCHAIN_COMPLETE]);;
