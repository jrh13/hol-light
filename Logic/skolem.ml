(* ========================================================================= *)
(* Conversion to Skolem normal form.                                         *)
(* ========================================================================= *)

let HOLDS_EXISTS_LEMMA = prove
 (`!p t x M v preds:num#num->bool.
        interpretation (functions_term t,preds) M /\
        valuation(M) (v:num->A) /\
        holds M v (formsubst (valmod (x,t) V) p)
        ==> holds M v (??x p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOLDS_FORMSUBST1] THEN
  REWRITE_TAC[HOLDS] THEN DISCH_TAC THEN
  EXISTS_TAC `termval M (v:num->A) t` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
  EXISTS_TAC `preds:num#num->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One-step Skolemization of ??x p using new function f.                     *)
(* ------------------------------------------------------------------------- *)

let Skolem1_DEF = new_definition
  `Skolem1 f x p =
     formsubst (valmod (x,Fn f (MAP V (list_of_set(FV(??x p))))) V) p`;;

let HOLDS_SKOLEM1 = prove
 (`!f x p.
     prenex(??x p) /\
     ~((f,CARD(FV(??x p))) IN functions_form(??x p))
     ==> prenex(Skolem1 f x p) /\
         (FV(Skolem1 f x p) = FV(??x p)) /\
         size(Skolem1 f x p) < size(??x p) /\
         (predicates_form (Skolem1 f x p) = predicates_form(??x p)) /\
         (functions_form(??x p) SUBSET functions_form (Skolem1 f x p)) /\
         (functions_form (Skolem1 f x p) SUBSET ((f,CARD(FV(??x p))) INSERT
                                  functions_form(??x p))) /\
         (!M. interpretation (language {p}) M /\
              ~(Dom(M) = EMPTY) /\
              (!v:num->A. valuation(M) v ==> holds M v (??x p))
              ==> ?M'. (Dom(M') = Dom(M)) /\
                       (Pred(M') = Pred(M)) /\
                       (!g zs. ~(g = f) \/ ~(LENGTH zs = CARD(FV(??x p)))
                               ==> (Fun(M') g zs = Fun(M) g zs)) /\
                       interpretation (language {(Skolem1 f x p)}) M' /\
                       (!v. valuation(M') v ==> holds M' v (Skolem1 f x p))) /\
         (!N. interpretation (language {(Skolem1 f x p)}) N /\
              ~(Dom(N) = EMPTY)
              ==> !v:num->A. valuation(N) (v:num->A) /\
                             holds N v (Skolem1 f x p) ==> holds N v (??x p))`,
  let lemma1 = prove
   (`!l. LIST_UNION (MAP (\x. {x}) l) = set_of_list l`,
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[set_of_list; LIST_UNION; MAP] THEN
    SET_TAC[]) in
  let lemma2 = prove
   (`!s. FINITE(s) ==> (LIST_UNION (MAP (\x. {x}) (list_of_set s)) = s)`,
    GEN_TAC THEN REWRITE_TAC[lemma1; SET_OF_LIST_OF_SET]) in
  let lemma3 = prove
   (`holds M v p /\
     (Dom M = Dom M') /\
     (!P zs. Pred M P zs = Pred M' P zs) /\
     (!f zs.
          f,LENGTH zs IN functions_form p ==> (Fun M f zs = Fun M' f zs))
     ==> holds M' v p`,
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOLDS_FUNCTIONS) THEN
    ASM_MESON_TAC[]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `x IN FV(p)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `Skolem1 f x p = p` SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM FORMSUBST_TRIV] THEN
      REWRITE_TAC[Skolem1_DEF] THEN MATCH_MP_TAC FORMSUBST_VALUATION THEN
      GEN_TAC THEN REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[PRENEX]) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(x IN FV(p))` THEN
      REWRITE_TAC[FV; Exists_DEF; Not_DEF; EXTENSION; IN_UNION; IN_DELETE;
                  NOT_IN_EMPTY] THEN MESON_TAC[];
      REWRITE_TAC[SIZE] THEN ARITH_TAC;
      REWRITE_TAC[Exists_DEF; Not_DEF; predicates_form; UNION_EMPTY];
      REWRITE_TAC[Exists_DEF; Not_DEF; functions_form; UNION_EMPTY; SUBSET_REFL];
      REWRITE_TAC[Exists_DEF; Not_DEF; functions_form; UNION_EMPTY] THEN SET_TAC[];
      W(EXISTS_TAC o rand o rand o lhand o snd o dest_exists o snd) THEN
      ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      REWRITE_TAC[HOLDS] THEN
      DISCH_THEN(CHOOSE_THEN (MP_TAC o CONJUNCT2)) THEN
      MATCH_MP_TAC EQ_IMP THEN
      MATCH_MP_TAC HOLDS_VALUATION THEN
      REWRITE_TAC[valmod] THEN UNDISCH_TAC `~(x IN FV(p))` THEN
      CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN MESON_TAC[];
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN REWRITE_TAC[HOLDS] THEN
      EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `holds N (v:num->A) p` THEN
      MATCH_MP_TAC EQ_IMP THEN
      MATCH_MP_TAC HOLDS_VALUATION THEN
      REWRITE_TAC[valmod] THEN UNDISCH_TAC `~(x IN FV(p))` THEN
      CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN MESON_TAC[]]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PRENEX]) THEN REWRITE_TAC[Skolem1_DEF] THEN
  ASM_REWRITE_TAC[PRENEX_FORMSUBST] THEN
  ASM_REWRITE_TAC[SIZE_FORMSUBST; SIZE; ARITH_RULE `x < 3 + x`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORMSUBST_FV] THEN
    REWRITE_TAC[valmod] THEN CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
    REWRITE_TAC[FVT; NOT_IN_EMPTY; IN_INSERT] THEN
    REWRITE_TAC[GSYM MAP_o; o_DEF] THEN REWRITE_TAC[FVT] THEN
    REWRITE_TAC[MATCH_MP lemma2 (SPEC `??x p` FV_FINITE)] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    UNDISCH_TAC `x IN FV p` THEN
    REWRITE_TAC[FV; Exists_DEF; Not_DEF; UNION_EMPTY; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORMSUBST_PREDICATES] THEN CONJ_TAC THENL
   [REWRITE_TAC[predicates_form; Exists_DEF; Not_DEF; UNION_EMPTY]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP FORMSUBST_FUNCTIONS_FORM_1 th]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[Exists_DEF; Not_DEF; functions_form; UNION_EMPTY; SUBSET_UNION];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[functions_term] THEN
    SUBGOAL_THEN `!l. LIST_UNION (MAP functions_term (MAP V l)) = EMPTY`
      (fun th -> REWRITE_TAC[th]) THENL
     [LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC[LIST_UNION; MAP; functions_term] THEN
      SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LENGTH_MAP] THEN
    SUBGOAL_THEN `LENGTH(list_of_set(FV(??x p))) = CARD(FV(??x p))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LENGTH_LIST_OF_SET THEN REWRITE_TAC[FV_FINITE];
      ALL_TAC] THEN
    REWRITE_TAC[Exists_DEF; Not_DEF; functions_form] THEN
    REWRITE_TAC[SUBSET; IN_INSERT; IN_UNION; NOT_IN_EMPTY; DISJ_ACI];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `Dom(M):A->bool,
                 (\g zs. if (g = f) /\ (LENGTH zs = CARD(FV(??x p)))
                         then @a. a IN Dom(M) /\
                                  holds M
                                   (valmod (x,a)
                                      (ITLIST valmod
                                              (MAP2 (\x a. (x,a))
                                                    (list_of_set(FV(??x p)))
                                                    zs)
                                              (\z. @c. c IN Dom(M)))) p
                         else Fun(M) g zs),
                Pred(M)` THEN
    ASM_REWRITE_TAC[Dom_DEF; Pred_DEF; Fun_DEF] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[language; interpretation] THEN
      SUBGOAL_THEN
       `functions
         {(formsubst(valmod (x,Fn f (MAP V (list_of_set(FV(??x p))))) V) p)}
        = ((f,CARD(FV(??x p))) INSERT functions_form p)`
      SUBST1_TAC THENL
       [MP_TAC(SPECL [`x:num`; `Fn f (MAP V (list_of_set(FV(??x p))))`;
                      `p:form`] FORMSUBST_FUNCTIONS_FORM_1) THEN
        ASM_REWRITE_TAC[FVT] THEN
        SUBGOAL_THEN `LIST_UNION(MAP FVT (MAP V (list_of_set(FV(??x p))))) =
                      FV(??x p)`
        (fun th -> ASM_REWRITE_TAC[th]) THENL
         [SUBGOAL_THEN `FV(??x p) = set_of_list(list_of_set(FV(??x p)))`
          (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
           [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SET_OF_LIST_OF_SET THEN
            REWRITE_TAC[FV_FINITE]; ALL_TAC] THEN
          SPEC_TAC(`list_of_set(FV(??x p))`,`l:num list`) THEN
          LIST_INDUCT_TAC THEN
          ASM_REWRITE_TAC[LIST_UNION; MAP; FVT; set_of_list] THEN
          SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[functions; IN_INSERT; NOT_IN_EMPTY] THEN
        SUBGOAL_THEN `!p. UNIONS {functions_form q | q = p } =
                           functions_form p`
        (fun th -> REWRITE_TAC[th]) THENL
         [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
          REWRITE_TAC[GSYM EXTENSION] THEN MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; IN_UNION] THEN
        X_GEN_TAC `fa:num#num` THEN
        GEN_REWRITE_TAC RAND_CONV [DISJ_SYM] THEN
        AP_TERM_TAC THEN REWRITE_TAC[functions_term] THEN
        SUBGOAL_THEN `!l. LIST_UNION (MAP functions_term (MAP V l)) = EMPTY`
        (fun th -> REWRITE_TAC[th]) THENL
         [LIST_INDUCT_TAC THEN
          ASM_REWRITE_TAC[LIST_UNION; MAP; functions_term] THEN
          SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[LENGTH_MAP] THEN
        MATCH_MP_TAC LENGTH_LIST_OF_SET THEN REWRITE_TAC[FV_FINITE];
        ALL_TAC] THEN
      REWRITE_TAC[Dom_DEF; Fun_DEF] THEN
      X_GEN_TAC `g:num` THEN X_GEN_TAC `zs:A list` THEN
      REWRITE_TAC[IN_INSERT; PAIR_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `?a:A. a IN Dom M /\
                            holds M (valmod (x,a)
                             (ITLIST valmod (MAP2 (\x a. x,a)
                               (list_of_set (FV (?? x p))) zs)
                                  (\z. @c. c IN Dom(M)))) p`
        (fun th -> REWRITE_TAC[SELECT_RULE th]) THEN
        UNDISCH_TAC `!v. valuation M v ==> holds M (v:num->A) (??x p)` THEN
        REWRITE_TAC[HOLDS] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[valuation] THEN
        UNDISCH_TAC `ALL (\x:A. x IN Dom M) zs` THEN
        SUBGOAL_THEN `LENGTH(list_of_set(FV(??x p))) = LENGTH (zs:A list)`
        MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LENGTH_LIST_OF_SET THEN
          REWRITE_TAC[FV_FINITE]; ALL_TAC] THEN
        SPEC_TAC(`list_of_set(FV(??x p))`,`xs:num list`) THEN
        SPEC_TAC(`zs:A list`,`zs:A list`) THEN
        LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; ITLIST; MAP2; LENGTH] THENL
         [GEN_TAC THEN
          REWRITE_TAC[LENGTH_EQ_NIL] THEN
          DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[MAP2; ITLIST] THEN
          CONV_TAC SELECT_CONV THEN
          ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
        LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
        REWRITE_TAC[SUC_INJ] THEN
        DISCH_THEN(fun th -> DISCH_TAC THEN ANTE_RES_THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        REWRITE_TAC[MAP2; ITLIST] THEN
        GEN_TAC THEN REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[interpretation; language]) THEN
        STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[functions; IN_INSERT; NOT_IN_EMPTY] THEN
        SUBGOAL_THEN `!p. UNIONS {functions_form q | q = p } =
                           functions_form p`
        (fun th -> ASM_REWRITE_TAC[th]) THEN
        GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
        REWRITE_TAC[GSYM EXTENSION] THEN MESON_TAC[]]; ALL_TAC] THEN
    REWRITE_TAC[HOLDS_FORMSUBST1] THEN
    X_GEN_TAC `v:num->A` THEN DISCH_TAC THEN REWRITE_TAC[termval] THEN
    REWRITE_TAC[GSYM MAP_o] THEN REWRITE_TAC[o_DEF; termval] THEN
    REWRITE_TAC[Fun_DEF; LENGTH_MAP] THEN
    SUBGOAL_THEN `LENGTH(list_of_set(FV(??x p))) = CARD(FV (??x p))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LENGTH_LIST_OF_SET THEN
      REWRITE_TAC[FV_FINITE]; ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC lemma3 THEN
    REWRITE_TAC[Dom_DEF; Pred_DEF; Fun_DEF] THEN CONJ_TAC THENL
     [ALL_TAC;
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `(f',LENGTH (zs:A list)) IN functions_form p` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(f,CARD (FV (?? x p)) IN functions_form (?? x p))` THEN
      REWRITE_TAC[Exists_DEF; functions_form; Not_DEF; UNION_EMPTY] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    SUBGOAL_THEN
     `!a. holds M (valmod (x,a)
                         (ITLIST valmod
                            (MAP2 (\x a. x,a) (list_of_set (FV (??x p)))
                                     (MAP (\y. v y) (list_of_set(FV(??x p)))))
                  (\z. @c. c IN Dom(M)))) p = holds M (valmod (x,a:A) v) p`
    (fun th -> REWRITE_TAC[th]) THENL
     [ALL_TAC;
      SUBGOAL_THEN
       `(@a:A. a IN Dom M /\ holds M (valmod (x,a) v) p) IN Dom(M) /\
        holds M (valmod (x,(@a. a IN Dom M /\ holds M (valmod (x,a) v) p)) v) p`
      (ACCEPT_TAC o CONJUNCT2) THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[HOLDS]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[valuation; Dom_DEF]) THEN
      ASM_REWRITE_TAC[valuation]] THEN
    X_GEN_TAC `a:A` THEN MATCH_MP_TAC HOLDS_VALUATION THEN
    X_GEN_TAC `z:num` THEN DISCH_TAC THEN REWRITE_TAC[valmod] THEN
    ASM_CASES_TAC `z:num = x` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MEM z (list_of_set (FV (??x p)))` MP_TAC THENL
     [SUBGOAL_THEN `z IN FV(??x p)`
       (fun th -> MESON_TAC[th; MEM_LIST_OF_SET; FV_FINITE]) THEN
      ASM_REWRITE_TAC[Exists_DEF; Not_DEF; FV; IN_DELETE; IN_UNION; NOT_IN_EMPTY];
      ALL_TAC] THEN
    SPEC_TAC(`list_of_set(FV(??x p))`,`l:num list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
    REWRITE_TAC[ITLIST; MAP2; MAP; valmod] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];

    MATCH_MP_TAC HOLDS_EXISTS_LEMMA THEN
    EXISTS_TAC `Fn f (MAP V (list_of_set (FV (?? x p))))` THEN
    EXISTS_TAC `predicates_form (formsubst
           (valmod (x,Fn f (MAP V (list_of_set(FV(??x p))))) V) p)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `interpretation
       (language
       (formsubst (valmod (x,Fn f (MAP V (list_of_set (FV (?? x p))))) V)
        p INSERT
        EMPTY))
       (N:(A->bool)#((num->((A)list->A))#(num->((A)list->bool))))` THEN
    REWRITE_TAC[LANGUAGE_1] THEN
    MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP FORMSUBST_FUNCTIONS_FORM_1 th]) THEN
    REWRITE_TAC[SUBSET_UNION]]);;

(* ------------------------------------------------------------------------- *)
(* Multiple Skolemization of a prenex formula.                               *)
(* ------------------------------------------------------------------------- *)

let Skolems_EXISTENCE = prove
 (`!J. ?Skolems. !r.
    Skolems r = \k. PPAT (\x q. !!x (Skolems q k))
                         (\x q. Skolems (Skolem1 (NUMPAIR J k) x q) (SUC k))
                         (\p. p) r`,
  GEN_TAC THEN MATCH_MP_TAC SIZE_REC THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[PPAT_DEF] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `?x p. r = !!x p` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
      REWRITE_TAC[form_DISTINCT; form_INJ] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL; GSYM EXISTS_REFL;
              SELECT_REFL; CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
                                (SPEC_ALL SELECT_REFL)] THEN
    AP_THM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[size] THEN ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
  REWRITE_TAC[PRENEX_DISTINCT] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL; GSYM EXISTS_REFL;
            SELECT_REFL; CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
                              (SPEC_ALL SELECT_REFL)] THEN
  AP_THM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[Skolem1_DEF; SIZE_FORMSUBST] THEN
  REWRITE_TAC[SIZE] THEN ARITH_TAC);;

let Skolems_SPECIFICATION = prove
 (`?Skolems. !J r k.
        Skolems J r k =
          PPAT (\x q. !!x (Skolems J q k))
               (\x q. Skolems J (Skolem1 (NUMPAIR J k) x q) (SUC k))
               (\p. p) r`,
  REWRITE_TAC[REWRITE_RULE[SKOLEM_THM; FUN_EQ_THM] Skolems_EXISTENCE]);;

let Skolems_DEF = new_specification ["Skolems"] Skolems_SPECIFICATION;;

let HOLDS_SKOLEMS_INDUCTION = prove
 (`!n J k p.
           (size(p) = n) /\
           prenex(p) /\
           (!l m. (NUMPAIR J l,m) IN functions_form p ==> l < k)
           ==> universal((Skolems J p k)) /\
               (FV((Skolems J p k)) = FV(p)) /\
               (predicates_form (Skolems J p k) = predicates_form p) /\
                functions_form p SUBSET functions_form (Skolems J p k) /\
                functions_form (Skolems J p k) SUBSET
                 {NUMPAIR j l,m | j,l,m | (j = J) /\ k <= l} UNION
                 functions_form p /\
                (!M. interpretation (language {p}) M /\
                     ~(Dom M = EMPTY) /\
                     (!v:num->A. valuation M v ==> holds M v p)
                     ==> ?M'. (Dom M' = Dom M) /\
                              (Pred M' = Pred M) /\
                              (!g zs. ~(Fun(M') g zs = Fun(M) g zs)
                                    ==> ?l. k <= l /\ (g = NUMPAIR J l)) /\
                              interpretation (language {(Skolems J p k)}) M' /\
                              (!v. valuation M' v
                                   ==> holds M' v (Skolems J p k))) /\
               (!N. interpretation (language {(Skolems J p k)}) N /\
                ~(Dom(N) = EMPTY)
                ==> !v:num->A. valuation(N) v /\ holds N v (Skolems J p k)
                               ==> holds N v p)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[prenex_CASES]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [SUBGOAL_THEN `Skolems J p k = p` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[Skolems_DEF] THEN
      SUBGOAL_THEN `~(?x q. p = !!x q) /\ ~(?x q. p = ??x q)` MP_TAC THENL
       [REPEAT STRIP_TAC THEN UNDISCH_TAC `qfree p` THEN
        ASM_REWRITE_TAC[QFREE]; ALL_TAC] THEN
      SIMP_TAC[PPAT]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_UNION; SUBSET_REFL] THEN
    ONCE_REWRITE_TAC[universal_CASES] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    W(EXISTS_TAC o rand o rand o lhand o body o rand o snd) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN
  (X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `r:form`
  (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  REWRITE_TAC[SIZE] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl) o SPEC `size r`) THEN
    REWRITE_TAC[ARITH_RULE `r < 1 + r`] THEN
    DISCH_THEN(MP_TAC o SPECL [`J:num`; `k:num`; `r:form`]) THEN
    W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[functions_form]) THEN
      DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `Skolems J (!!x r) k = !!x (Skolems J r k)` SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [Skolems_DEF] THEN
      SUBGOAL_THEN `?z s. !!x r = !!z s` (fun th -> SIMP_TAC[th; PPAT]) THEN
      MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `q = Skolems J r k` THEN
    ASM_REWRITE_TAC[functions_form; FV] THEN
    REWRITE_TAC[predicates_form; functions_form; LANGUAGE_1] THEN
    REWRITE_TAC[GSYM LANGUAGE_1] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[universal_CASES]; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
       `interpretation (language (r INSERT EMPTY)) M /\
        ~(Dom M = EMPTY) /\
        (!v:num->A. valuation M v ==> holds M v r)`
      (ANTE_RES_THEN MP_TAC) THENL
       [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
        DISCH_THEN(fun th -> ASSUME_TAC th THEN ANTE_RES_THEN MP_TAC th) THEN
        REWRITE_TAC[HOLDS] THEN
        DISCH_THEN(MP_TAC o SPEC `(v:num->A) x`) THEN
        REWRITE_TAC[VALMOD_TRIV] THEN DISCH_THEN MATCH_MP_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[valuation]) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(prove(`(!x. p x ==> q x) ==> (?x. p x) ==> ?x. q x`,
                           MESON_TAC[])) THEN
        GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[holds] THEN
        ASM_MESON_TAC[VALUATION_VALMOD]];
      UNDISCH_TAC `holds N (v:num->A) (!!x q)` THEN
      REWRITE_TAC[HOLDS] THEN ASM_MESON_TAC[VALUATION_VALMOD]]; ALL_TAC] THEN

  MP_TAC(SPECL [`NUMPAIR J k`; `x:num`; `r:form`] HOLDS_SKOLEM1) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_REWRITE_TAC[PRENEX] THEN ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  STRIP_TAC THEN ABBREV_TAC `q = Skolem1 (NUMPAIR J k) x r` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl) o SPEC `size q`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SIZE]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`J:num`; `SUC k`; `q:form`]) THEN
  ASM_REWRITE_TAC[LT] THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [REPEAT GEN_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    REWRITE_TAC[IN_INSERT; NUMPAIR_INJ; PAIR_EQ] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `Skolems J (?? x r) k = Skolems J q (SUC k)` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN GEN_REWRITE_TAC LAND_CONV [Skolems_DEF] THEN
    REWRITE_TAC[PPAT];
    ABBREV_TAC `s = Skolems J q (SUC k)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    UNDISCH_TAC `functions_form s SUBSET
                 {NUMPAIR j l,m | j,l,m | (j = J) /\ SUC k <= l} UNION
                 functions_form q` THEN
    UNDISCH_TAC `functions_form q SUBSET
          (NUMPAIR J k,CARD (FV (?? x r))) INSERT functions_form (?? x r)` THEN
    REWRITE_TAC[SUBSET; IN_INSERT; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[NUMPAIR_INJ; ARITH_RULE `SUC k <= l ==> k <= l`; LE_REFL];
    REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `interpretation (language {r}) M /\
      ~(Dom M = EMPTY) /\
      !v:num->A. valuation M v ==> holds M v (?? x r)`
    (ANTE_RES_THEN MP_TAC) THENL
     [ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [LANGUAGE_1; Not_DEF; Exists_DEF; functions_form;
        predicates_form; UNION_EMPTY]) THEN
      ASM_REWRITE_TAC[LANGUAGE_1]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M0:(A->bool)#(num->A list->A)#(num->A
                                  list->bool)` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `interpretation (language {q}) M0 /\
      ~(Dom M0 = EMPTY) /\
      (!v:num->A. valuation M0 v ==> holds M0 v q)`
    (ANTE_RES_THEN MP_TAC) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M1:(A->bool)#(num->A list->A)#(num->A
                                  list->bool)` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `M1:(A->bool)#(num->A list->A)#(num->A list->bool)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(Fun M1 g (zs:A list) = Fun M0 g zs) \/
                  ~(Fun M0 g zs = Fun M g zs)`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (ANTE_RES_THEN MP_TAC) MP_TAC) THENL
     [MESON_TAC[ARITH_RULE `SUC k <= l ==> k <= l`]; ALL_TAC] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    MESON_TAC[LE_REFL];
    GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
    GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    MP_TAC(ASSUME `valuation N (v:num->A)`) THEN
    REWRITE_TAC[IMP_IMP] THEN
    SPEC_TAC(`v:num->A`,`v:num->A`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `interpretation (language {s})
     (N:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
    REWRITE_TAC[LANGUAGE_1] THEN
    MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
    ASM_REWRITE_TAC[]]);;

let HOLDS_SKOLEMS_PRENEX = prove
 (`!p.
    prenex(p)
    ==> !K. (!l m. ~(NUMPAIR K l,m IN functions_form p))
            ==> universal(Skolems K p 0) /\
                (FV(Skolems K p 0) = FV(p)) /\
                (predicates_form (Skolems K p 0) = predicates_form p) /\
                functions_form p SUBSET functions_form (Skolems K p 0) /\
                functions_form (Skolems K p 0) SUBSET
                 {NUMPAIR k l,m | k,l,m | k = K} UNION functions_form p /\
                (!M. interpretation (language {p}) M /\
                     ~(Dom M = EMPTY) /\
                     (!v:num->A. valuation M v ==> holds M v p)
                     ==> ?M'. (Dom M' = Dom M) /\
                              (Pred M' = Pred M) /\
                              (!g zs. ~(Fun M' g zs = Fun M g zs)
                                      ==> (?l. g =
                                              NUMPAIR K l)) /\
                              interpretation (language {(Skolems K p 0)}) M' /\
                              (!v. valuation M' v
                                   ==> holds M' v (Skolems K p 0))) /\
                (!N. interpretation (language {(Skolems K p 0)}) N /\
                     ~(Dom N = EMPTY)
                     ==> !v:num->A. valuation(N) v /\ holds N v (Skolems K p 0)
                                    ==> holds N v p)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`size p`; `K:num`; `0`; `p:form`] HOLDS_SKOLEMS_INDUCTION) THEN
  ASM_REWRITE_TAC[LE_0]);;

(* ------------------------------------------------------------------------- *)
(* Now Skolemize an arbitrary (non-prenex) formula.                          *)
(* ------------------------------------------------------------------------- *)

let Skopre_DEF = new_definition
  `Skopre K p = Skolems K (Prenex p) 0`;;

let SKOPRE = prove
 (`!p K.
      (!l m. ~(NUMPAIR K l,m IN functions_form p))
       ==> universal(Skopre K p) /\
           (FV(Skopre K p) = FV(p)) /\
           (predicates_form (Skopre K p) = predicates_form p) /\
           functions_form p SUBSET functions_form (Skopre K p) /\
           functions_form (Skopre K p) SUBSET
            {NUMPAIR k l,m | k,l,m | k = K} UNION functions_form p /\
           (!M. interpretation (language {p}) M /\
                ~(Dom M = EMPTY) /\
                (!v:num->A. valuation M v ==> holds M v p)
                ==> ?M'. (Dom M' = Dom M) /\
                         (Pred M' = Pred M) /\
                         (!g zs. ~(Fun M' g zs = Fun M g zs)
                                 ==> (?l. g =
                                         NUMPAIR K l)) /\
                         interpretation (language {(Skopre K p)}) M' /\
                         (!v. valuation M' v ==> holds M' v (Skopre K p))) /\
           (!N. interpretation (language {(Skopre K p)}) N /\
                ~(Dom(N) = EMPTY)
                ==> !v:num->A. valuation(N) v /\ holds N v (Skopre K p)
                               ==> holds N v p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[Skopre_DEF] THEN
  MP_TAC(SPEC `p:form` PRENEX_THM) THEN
  ABBREV_TAC `r = Prenex p` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(functions_form r = functions_form p) /\
                (predicates_form r = predicates_form p)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LANGUAGE_1; PAIR_EQ]) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  W(fun (_,w) -> SUBGOAL_THEN (subst [`r:form`,`p:form`] w) MP_TAC) THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP HOLDS_SKOLEMS_PRENEX) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(AP_TERM_TAC ORELSE ABS_TAC) THEN
  BINOP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(MATCH_MP_TAC(TAUT `(a ==> (b = c)) ==> (a ==> b <=> a ==> c)`) THEN
         DISCH_TAC) THEN TRY BINOP_TAC THEN
  REPEAT((FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) ORELSE
         (FIRST_ASSUM(MATCH_MP_TAC o GSYM) THEN ASM_REWRITE_TAC[]) ORELSE
         AP_TERM_TAC ORELSE ABS_TAC) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bumping up function indices to leave room for Skolem functions.           *)
(* ------------------------------------------------------------------------- *)

let bumpmod = new_definition
  `bumpmod(M) = Dom(M),(\k zs. Fun(M) (NUMSND k) zs),Pred(M)`;;

let bumpterm = new_recursive_definition term_RECURSION
  `(bumpterm (V x) = V x) /\
   (bumpterm (Fn k l) = Fn (NUMPAIR 0 k) (MAP bumpterm l))`;;

let bumpform = new_recursive_definition form_RECURSION
  `(bumpform False = False) /\
   (bumpform (Atom p l) = Atom p (MAP bumpterm l)) /\
   (bumpform (q --> r) = bumpform q --> bumpform r) /\
   (bumpform (!!x r) = !!x (bumpform r))`;;

let BUMPTERM = prove
 (`!M v t. termval M v t = termval (bumpmod M) v (bumpterm t)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termval; bumpterm] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[bumpmod; Fun_DEF; NUMPAIR_DEST] THEN
  REWRITE_TAC[GSYM bumpmod] THEN REWRITE_TAC[GSYM MAP_o] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  ASM_REWRITE_TAC[o_THM]);;

let BUMPFORM = prove
 (`!M p v. holds M v p = holds (bumpmod M) v (bumpform p)`,
  GEN_TAC THEN MATCH_MP_TAC form_INDUCTION THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[Dom_DEF; bumpmod; bumpform; holds; Pred_DEF] THEN
  REWRITE_TAC[GSYM bumpmod; GSYM MAP_o] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[o_THM; GSYM BUMPTERM; ALL_T]);;

let FUNCTIONS_FORM_BUMPFORM = prove
 (`!p f m.
        f,m IN functions_form(bumpform p)
        ==> ?k. (f = NUMPAIR 0 k) /\ k,m IN functions_form p`,
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[functions_form; bumpform; IN_UNION; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_UNION] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`] THEN
  REWRITE_TAC[EXISTS_OR_THM] THEN POP_ASSUM(K ALL_TAC) THEN
  DISCH_TAC THEN DISJ1_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:term`,`t:term`) THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[bumpterm; functions_term; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; PAIR_EQ; LENGTH_MAP] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`] THEN
  REWRITE_TAC[EXISTS_OR_THM] THEN DISJ2_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`l:term list`,`l:term list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LIST_UNION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_UNION; ALL] THEN ASM_MESON_TAC[]);;

let BUMPFORM_INTERPRETATION = prove
 (`interpretation (language {p}) M
   ==> interpretation (language {(bumpform p)}) (bumpmod M)`,
  REWRITE_TAC[LANGUAGE_1; interpretation] THEN
  REWRITE_TAC[Dom_DEF; bumpmod; Fun_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FUNCTIONS_FORM_BUMPFORM; NUMPAIR_DEST]);;

let unbumpterm = new_recursive_definition term_RECURSION
  `(unbumpterm (V x) = V x) /\
   (unbumpterm (Fn k l) = Fn (NUMSND k) (MAP unbumpterm l))`;;

let unbumpform = new_recursive_definition form_RECURSION
  `(unbumpform False = False) /\
   (unbumpform (Atom p l) = Atom p (MAP unbumpterm l)) /\
   (unbumpform (q --> r) = unbumpform q --> unbumpform r) /\
   (unbumpform (!!x r) = !!x (unbumpform r))`;;

let UNBUMPTERM = prove
 (`!t. unbumpterm(bumpterm t) = t`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[unbumpterm; bumpterm; NUMPAIR_DEST] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MAP_o] THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN
  ASM_REWRITE_TAC[o_THM]);;

let UNBUMPFORM = prove
 (`!p. unbumpform (bumpform p) = p`,
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[unbumpform; bumpform] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF; UNBUMPTERM] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
  REWRITE_TAC[ALL_T]);;

let unbumpmod = new_definition
  `unbumpmod(M) = Dom(M),(\k zs. Fun(M) (NUMPAIR 0 k) zs),Pred(M)`;;

let UNBUMPMOD_TERM = prove
 (`!M v t. termval M v (bumpterm t) = termval (unbumpmod M) v t`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termval; bumpterm] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[unbumpmod; Fun_DEF; NUMPAIR_DEST] THEN
  REWRITE_TAC[GSYM unbumpmod] THEN REWRITE_TAC[GSYM MAP_o] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  ASM_REWRITE_TAC[o_THM]);;

let UNBUMPMOD = prove
 (`!M p (v:num->A). holds M v (bumpform p) = holds (unbumpmod M) v p`,
  GEN_TAC THEN MATCH_MP_TAC form_INDUCTION THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[Dom_DEF; unbumpmod; bumpform; holds; Pred_DEF] THEN
  REWRITE_TAC[GSYM unbumpmod; GSYM MAP_o] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[o_THM; GSYM UNBUMPMOD_TERM; ALL_T]);;

(* ------------------------------------------------------------------------- *)
(* Mapping terms and formulas into terms for unique Skolem functions.        *)
(* ------------------------------------------------------------------------- *)

let NUMLIST = new_recursive_definition list_RECURSION
  `(NUMLIST [] = 0) /\
   (NUMLIST (CONS h t) = NUMPAIR h (NUMLIST t) + 1)`;;

let NUMLIST_INJ = prove
 (`!l1 l2. (NUMLIST l1 = NUMLIST l2) = (l1 = l2)`,
  REPEAT(LIST_INDUCT_TAC ORELSE STRIP_TAC) THEN
  ASM_REWRITE_TAC[NUMLIST; GSYM ADD1; SUC_INJ; NOT_SUC;
    CONS_11; NOT_CONS_NIL; NUMPAIR_INJ]);;

let num_of_term = new_nested_recursive_definition term_RECURSION
  `(!x. num_of_term (V x) = NUMPAIR 0 x) /\
   (!f l. num_of_term (Fn f l) =
            NUMPAIR 1 (NUMPAIR f (NUMLIST(MAP num_of_term l))))`;;

let NUM_OF_TERM_INJ = prove
 (`!s t. (num_of_term s = num_of_term t) = (s = t)`,
  REPEAT(MATCH_MP_TAC term_INDUCT ORELSE STRIP_TAC) THEN
  ASM_REWRITE_TAC[num_of_term; NUMPAIR_INJ; NUMLIST_INJ; ARITH] THEN
  REWRITE_TAC[term_INJ; term_DISTINCT] THEN
  AP_TERM_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  UNDISCH_TAC
   `ALL (\s. !t. (num_of_term s = num_of_term t) = (s = t)) l` THEN
  POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN
  SPEC_TAC(`l':term list`,`l':term list`) THEN
  SPEC_TAC(`l:term list`,`l:term list`) THEN
  REPEAT(LIST_INDUCT_TAC ORELSE GEN_TAC) THEN
  REWRITE_TAC[NOT_CONS_NIL; MAP; NUMLIST; num_of_term; CONS_11; ALL] THEN
  REWRITE_TAC[num_of_term] THEN ASM_MESON_TAC[]);;

let num_of_form = new_recursive_definition form_RECURSION
  `(num_of_form False = NUMPAIR 0 0) /\
   (num_of_form (Atom p l) =
        NUMPAIR 1 (NUMPAIR p (NUMLIST(MAP num_of_term l)))) /\
   (num_of_form (q --> r) =
        NUMPAIR 2 (NUMPAIR (num_of_form q) (num_of_form r))) /\
   (num_of_form (!!x q) = NUMPAIR 3 (NUMPAIR x (num_of_form q)))`;;

let NUMLIST_NUM_OF_TERM = prove
 (`!l1 l2. (NUMLIST (MAP num_of_term l1) = NUMLIST (MAP num_of_term l2)) =
           (l1 = l2)`,
  REPEAT(LIST_INDUCT_TAC ORELSE GEN_TAC) THEN
  REWRITE_TAC[NOT_CONS_NIL; MAP; NUMLIST; num_of_term; CONS_11; ALL] THEN
  ASM_REWRITE_TAC[GSYM ADD1; NOT_SUC; SUC_INJ; NUMPAIR_INJ; NUM_OF_TERM_INJ]);;

let NUM_OF_FORM_INJ = prove
 (`!q r. (num_of_form q = num_of_form r) = (q = r)`,
  MATCH_MP_TAC form_INDUCTION THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN GEN_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC] THEN
  MATCH_MP_TAC form_INDUCTION THEN
  ASM_REWRITE_TAC[num_of_form; NUMPAIR_INJ; ARITH; form_DISTINCT;
    form_INJ; NUMLIST_NUM_OF_TERM]);;

let form_of_num = new_definition
  `form_of_num x = @p. num_of_form p = x`;;

let FORM_OF_NUM = prove
 (`form_of_num(num_of_form p) = p`,
  REWRITE_TAC[form_of_num; NUM_OF_FORM_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Skolemization function.                                                   *)
(* ------------------------------------------------------------------------- *)

let SKOLEMIZE = new_definition
  `SKOLEMIZE p = Skopre (num_of_form(bumpform p) + 1) (bumpform p)`;;

let SKOLEMIZE_WORKS = prove
 (`!p. universal(SKOLEMIZE p) /\
       (FV(SKOLEMIZE p) = FV(bumpform p)) /\
       (predicates_form (SKOLEMIZE p) = predicates_form (bumpform p)) /\
       functions_form (bumpform p) SUBSET functions_form (SKOLEMIZE p) /\
       functions_form (SKOLEMIZE p) SUBSET
        {NUMPAIR k l,m | k,l,m | k = num_of_form(bumpform p) + 1} UNION
        functions_form (bumpform p) /\
       (!M. interpretation (language {(bumpform p)}) M /\
            ~(Dom M = EMPTY) /\
            (!v:num->A. valuation M v ==> holds M v (bumpform p))
            ==> ?M'. (Dom M' = Dom M) /\
                     (Pred M' = Pred M) /\
                     (!g zs. ~(Fun M' g zs = Fun M g zs)
                             ==> (?l. g =
                                     NUMPAIR (num_of_form(bumpform p) + 1)
                                             l)) /\
                     interpretation (language {(SKOLEMIZE p)}) M' /\
                     (!v. valuation M' v ==> holds M' v (SKOLEMIZE p))) /\
       (!N. interpretation (language {(SKOLEMIZE p)}) N /\
            ~(Dom(N) = EMPTY)
            ==> !v:num->A. valuation(N) v /\ holds N v (SKOLEMIZE p)
                           ==> holds N v (bumpform p))`,
  GEN_TAC THEN REWRITE_TAC[SKOLEMIZE] THEN MATCH_MP_TAC SKOPRE THEN
  SPEC_TAC(`num_of_form(bumpform p)`,`x:num`) THEN
  SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[bumpform; functions_form] THEN
  REWRITE_TAC[IN_UNION; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM MAP_o] THEN
  SPEC_TAC(`x:num`,`x:num`) THEN SPEC_TAC(`l:num`,`y:num`) THEN
  SPEC_TAC(`m:num`,`z:num`) THEN SPEC_TAC(`a1:term list`,`l:term list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LIST_UNION; NOT_IN_EMPTY; MAP] THEN
  ASM_REWRITE_TAC[IN_UNION] THEN
  SPEC_TAC(`h:term`,`t:term`) THEN POP_ASSUM(K ALL_TAC) THEN
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[functions_term; bumpterm; o_THM; NOT_IN_EMPTY] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LIST_UNION; NOT_IN_EMPTY; IN_INSERT; ALL] THEN
  REWRITE_TAC[PAIR_EQ; NUMPAIR_INJ; ARITH_RULE `~(x + 1 = 0)`] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN MESON_TAC[]);;

let FUNCTIONS_FORM_SKOLEMIZE = prove
 (`!p f m.
        f,m IN functions_form(SKOLEMIZE p)
        ==> (?k. (f = NUMPAIR 0 k) /\ k,m IN functions_form p) \/
            (?l. (f = NUMPAIR (num_of_form (bumpform p) + 1) l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL SKOLEMIZE_WORKS) THEN
  DISCH_THEN(MP_TAC o el 4 o CONJUNCTS) THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN
  DISCH_THEN(fun ith -> FIRST_ASSUM(MP_TAC o MATCH_MP ith)) THEN
  MATCH_MP_TAC(TAUT `(a ==> a') /\ (b ==> b') ==> a \/ b ==> b' \/ a'`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; NUMPAIR_INJ; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(K ALL_TAC) THEN
  SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[functions_form; bumpform; IN_UNION; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_UNION] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`] THEN
  REWRITE_TAC[EXISTS_OR_THM] THEN POP_ASSUM(K ALL_TAC) THEN
  DISCH_TAC THEN DISJ1_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:term`,`t:term`) THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[bumpterm; functions_term; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; PAIR_EQ; LENGTH_MAP] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`] THEN
  REWRITE_TAC[EXISTS_OR_THM] THEN DISJ2_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`l:term list`,`l:term list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LIST_UNION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_UNION; ALL] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Construction of Skolem model for a formula.                               *)
(* ------------------------------------------------------------------------- *)

let SKOMOD1 = new_definition
  `SKOMOD1 p M =
     if (!v. valuation M v ==> holds M v p)
     then @M'. (Dom M' = Dom (bumpmod M)) /\
               (Pred M' = Pred (bumpmod M)) /\
               (!g zs.
                    ~(Fun M' g zs = Fun (bumpmod M) g zs)
                    ==> (?l. g =
                             NUMPAIR (num_of_form (bumpform p) + 1) l)) /\
               interpretation (language {(SKOLEMIZE p)}) M' /\
               (!v:num->A. valuation M' v
                           ==> holds M' v (SKOLEMIZE p))
     else (Dom M,(\g zs. @a:A. a IN Dom(M)),Pred M)`;;

let SKOMOD1_WORKS = prove
 (`!M p.
      interpretation (language {p}) M /\
      ~(Dom M = EMPTY)
      ==> (Dom (SKOMOD1 p M) = Dom (bumpmod M)) /\
          (Pred (SKOMOD1 p M) = Pred (bumpmod M)) /\
          interpretation (language {(SKOLEMIZE p)}) (SKOMOD1 p M) /\
          ((!v:num->A. valuation M v ==> holds M v p)
           ==> (!g zs.
                    ~(Fun (SKOMOD1 p M) g zs = Fun (bumpmod M) g zs)
                    ==> (?l. g =
                             NUMPAIR (num_of_form (bumpform p) + 1) l)) /\
               (!v:num->A. valuation (SKOMOD1 p M) v
                 ==> holds (SKOMOD1 p M) v (SKOLEMIZE p)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SKOMOD1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THENL
   [ONCE_REWRITE_TAC[AC CONJ_ACI `d /\ p /\ i /\ g /\ v <=>
                                  d /\ p /\ g /\ i /\ v`] THEN
    CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC(el 5 (CONJUNCTS (SPEC_ALL SKOLEMIZE_WORKS))) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BUMPFORM_INTERPRETATION THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[Dom_DEF; bumpmod];
      REWRITE_TAC[GSYM BUMPFORM] THEN
      REWRITE_TAC[valuation; Dom_DEF; bumpmod] THEN
      ASM_REWRITE_TAC[GSYM valuation]];
    REWRITE_TAC[Dom_DEF; Pred_DEF; Fun_DEF; bumpmod] THEN
    REWRITE_TAC[interpretation; Dom_DEF; LANGUAGE_1; Fun_DEF] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SELECT_CONV THEN
    ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]]);;

let SKOMOD = new_definition
  `SKOMOD M =
     (Dom M,
      (\g zs. if NUMFST g = 0 then Fun M (NUMSND g) zs
              else Fun (SKOMOD1 (unbumpform(form_of_num (PRE(NUMFST g)))) M)
                       g zs),
      Pred M)`;;

let SKOMOD_INTERPRETATION = prove
 (`interpretation (language {p}) M /\
   ~(Dom M :A->bool = EMPTY)
   ==> interpretation (language {(SKOLEMIZE p)}) (SKOMOD M)`,
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC (CONJUNCT1 th)) THEN
  REWRITE_TAC[LANGUAGE_1; interpretation] THEN
  REWRITE_TAC[Dom_DEF; SKOMOD; Fun_DEF] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUNCTIONS_FORM_SKOLEMIZE) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST; ARITH_RULE `~(x + 1 = 0)`] THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ADD1; PRE; FORM_OF_NUM; UNBUMPFORM] THEN
  REWRITE_TAC[ADD1] THEN
  MP_TAC(SPEC_ALL SKOMOD1_WORKS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o el 1 o CONJUNCTS)) THEN
  REWRITE_TAC[LANGUAGE_1; interpretation] THEN
  ASM_REWRITE_TAC[bumpmod; Dom_DEF] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let SKOMOD_WORKS = prove
 (`interpretation(language {p}) M /\
   ~(Dom M = EMPTY)
   ==> ((!v:num->A. valuation(M) v ==> holds M v p) <=>
        (!v:num->A. valuation(SKOMOD M) v
                    ==> holds (SKOMOD M) v (SKOLEMIZE p)))`,
  STRIP_TAC THEN REWRITE_TAC[SKOMOD; valuation; Dom_DEF] THEN
  REWRITE_TAC[GSYM valuation] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `v:num->A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `holds (SKOMOD1 p M) (v:num->A) (SKOLEMIZE p)`
    MP_TAC THENL
     [SUBGOAL_THEN `valuation (SKOMOD1 p M) (v:num->A)` MP_TAC THENL
       [MP_TAC(SPEC_ALL SKOMOD1_WORKS) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
        UNDISCH_TAC `valuation M (v:num->A)` THEN
        ASM_REWRITE_TAC[Dom_DEF; valuation; bumpmod]; ALL_TAC] THEN
      SPEC_TAC(`v:num->A`,`v:num->A`) THEN
      MP_TAC(SPEC_ALL SKOMOD1_WORKS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN
    SPEC_TAC(`v:num->A`,`v:num->A`) THEN
    MATCH_MP_TAC HOLDS_FUNCTIONS THEN
    MP_TAC(SPEC_ALL SKOMOD1_WORKS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[Dom_DEF; Pred_DEF; bumpmod] THEN
    REWRITE_TAC[Fun_DEF] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP FUNCTIONS_FORM_SKOLEMIZE) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[NUMPAIR_DEST] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`NUMPAIR 0 k`; `zs:A list`]) THEN
      REWRITE_TAC[bumpmod; Fun_DEF; NUMPAIR_DEST] THEN
      REWRITE_TAC[NUMPAIR_INJ; ARITH_RULE `~(0 = x + 1)`];
      REWRITE_TAC[ARITH_RULE `~(x + 1 = 0)`] THEN
      REWRITE_TAC[GSYM ADD1; PRE; FORM_OF_NUM; UNBUMPFORM]];
    DISCH_TAC THEN SUBGOAL_THEN
     `!v. valuation (bumpmod M) (v:num->A)
          ==> holds (bumpmod M) v (bumpform p)`
    MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[GSYM BUMPFORM; valuation] THEN
      REWRITE_TAC[Dom_DEF; bumpmod]] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM SKOMOD]) THEN
    GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(INST [`@x:A. T`,`ty:A`]
     (last (CONJUNCTS(SPEC_ALL SKOLEMIZE_WORKS)))) THEN
    DISCH_THEN(MP_TAC o SPEC
     `SKOMOD (M:(A->bool)#(num->A list->A)#(num->A list->bool))`) THEN
    W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SKOMOD_INTERPRETATION THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SKOMOD; Dom_DEF]]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `holds (SKOMOD M) (v:num->A) (bumpform p)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[SKOMOD; valuation; Dom_DEF] THEN
        ASM_REWRITE_TAC[GSYM valuation] THEN
        UNDISCH_TAC `valuation (bumpmod M) (v:num->A)` THEN
        REWRITE_TAC[bumpmod; Dom_DEF; valuation];
        FIRST_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `valuation (bumpmod M) (v:num->A)` THEN
        REWRITE_TAC[bumpmod; Dom_DEF; valuation]];
      MATCH_MP_TAC EQ_IMP THEN
      SPEC_TAC(`v:num->A`,`v:num->A`) THEN
      MATCH_MP_TAC HOLDS_FUNCTIONS THEN
      REWRITE_TAC[SKOMOD; Dom_DEF; Fun_DEF; Pred_DEF; bumpmod] THEN
      REPEAT GEN_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP FUNCTIONS_FORM_BUMPFORM) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NUMPAIR_DEST]]]);;

let SKOLEMIZE_SATISFIABLE = prove
 (`(?M. ~(Dom M :A->bool = EMPTY) /\
        interpretation (language s) M /\
        M satisfies s) <=>
   (?M. ~(Dom M :A->bool = EMPTY) /\
        interpretation (language {SKOLEMIZE p | p IN s}) M /\
        M satisfies {SKOLEMIZE p | p IN s})`,
  REWRITE_TAC[satisfies; IN_ELIM_THM] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `SKOMOD (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[Dom_DEF; SKOMOD];
      REWRITE_TAC[interpretation; language; functions] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC(SPEC_ALL SKOMOD_INTERPRETATION) THEN
      W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `interpretation (language s)
         (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
        REWRITE_TAC[interpretation; language] THEN
        REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `functions {p} SUBSET functions s`
         (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `p:form IN s` THEN
        REWRITE_TAC[functions] THEN
        REWRITE_TAC[SUBSET; IN_UNIONS; IN_INSERT;
          NOT_IN_EMPTY; IN_ELIM_THM] THEN
        MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[interpretation; language] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; functions] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `interpretation (language {p'}) M /\
                    ~(Dom M :A->bool = EMPTY)`
      (MP_TAC o MATCH_MP SKOMOD_WORKS) THENL
       [ALL_TAC; ASM_MESON_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `interpretation (language s)
       (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
      REWRITE_TAC[language] THEN
      MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
      REWRITE_TAC[functions; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `p':form IN s` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC
    `unbumpmod (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
  REWRITE_TAC[GSYM UNBUMPMOD] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[unbumpmod; Dom_DEF];
    ALL_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `interpretation (language ({(SKOLEMIZE p)})) M /\
      ~(Dom M :A->bool = EMPTY)`
    (MATCH_MP_TAC o MATCH_MP (last(CONJUNCTS(SPEC_ALL SKOLEMIZE_WORKS)))) THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> UNDISCH_TAC (concl th) THEN
        REWRITE_TAC[language] THEN
        MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE) THEN
      REWRITE_TAC[functions; SUBSET; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_UNIONS; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      CONJ_TAC THENL
       [UNDISCH_TAC `valuation (unbumpmod M) (v:num->A)` THEN
        REWRITE_TAC[valuation; Dom_DEF; unbumpmod];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `valuation (unbumpmod M) (v:num->A)` THEN
        REWRITE_TAC[valuation; Dom_DEF; unbumpmod] THEN
        ASM_MESON_TAC[]]]] THEN
  SUBGOAL_THEN
   `interpretation (language {bumpform p | p IN s})
     (M:(A->bool)#(num->A list->A)#(num->A list->bool))`
  MP_TAC THENL
   [FIRST_ASSUM(fun th -> UNDISCH_TAC (concl th) THEN
        REWRITE_TAC[language] THEN
        MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE) THEN
    REWRITE_TAC[functions; SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
    MP_TAC(GEN `p:form` (el 3
     (CONJUNCTS (SPEC `p:form`
        (INST [`@x:A. T`,`ty:A`] SKOLEMIZE_WORKS))))) THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. interpretation (language {(bumpform p)})
                      (M:(A->bool)#(num->A list->A)#(num->A list->bool))
                    ==> interpretation (language {p}) (unbumpmod M)`
  MP_TAC THENL
   [REWRITE_TAC[LANGUAGE_1; interpretation] THEN
    REWRITE_TAC[Dom_DEF; unbumpmod; Fun_DEF] THEN
    MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC[functions_form; bumpform] THEN
    REWRITE_TAC[NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_UNION] THEN
    SPEC_TAC(`\x:A. x IN Dom M`,`P:A->bool`) THEN
    GEN_TAC THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `f,LENGTH(l:A list) IN LIST_UNION (MAP functions_term a1)` THEN
    SPEC_TAC(`LENGTH(l:A list)`,`k:num`) THEN
    SPEC_TAC(`a1:term list`,`l:term list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_UNION] THEN REPEAT STRIP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    DISJ1_TAC THEN UNDISCH_TAC `f,k IN functions_term h` THEN
    SPEC_TAC(`h:term`,`t:term`) THEN
    MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC[bumpterm; functions_term; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_INSERT; NUMPAIR_INJ; PAIR_EQ; LENGTH_MAP] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`l:term list`,`l:term list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[ALL; IN_UNION] THEN
    POP_ASSUM MP_TAC THEN
    W((fun t -> SPEC_TAC(t,`P:term->bool`)) o find_term is_abs o snd) THEN
    MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[interpretation; language; functions] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[Dom_DEF; unbumpmod] THEN REWRITE_TAC[GSYM unbumpmod] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!p. p IN s ==> interpretation (language {p}) (unbumpmod
        (M:(A->bool)#(num->A list->A)#(num->A list->bool)))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:form`) THEN
    W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[interpretation; language; functions] THEN
      REWRITE_TAC[Dom_DEF; unbumpmod] THEN REWRITE_TAC[GSYM unbumpmod] THEN
      REWRITE_TAC[IN_UNIONS; IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY]];
    REWRITE_TAC[interpretation; language; functions] THEN
    REWRITE_TAC[IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIONS] THEN
    REWRITE_TAC[Dom_DEF; unbumpmod] THEN REWRITE_TAC[GSYM unbumpmod] THEN
    DISCH_THEN(MP_TAC o SPEC `f':form`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Skolemization right down to quantifier-free formula.                      *)
(* ------------------------------------------------------------------------- *)

let specialize = new_recursive_definition form_RECURSION
  `(specialize False = False) /\
   (specialize (Atom p l) = Atom p l) /\
   (specialize (q --> r) = q --> r) /\
   (specialize (!!x r) = specialize r)`;;

let SPECIALIZE_SATISFIES = prove
 (`!M s. ~(Dom M:A->bool = EMPTY)
         ==> (M satisfies s <=> M satisfies {specialize p | p IN s})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[satisfies; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!p. (!v:num->A. valuation M v ==> holds M v p) <=>
        (!v:num->A. valuation M v ==> holds M v (specialize p))`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[specialize] THEN
  ASM_REWRITE_TAC[HOLDS_UCLOSE]);;

let SPECIALIZE_QFREE = prove
 (`!p. universal p ==> qfree(specialize p)`,
  MATCH_MP_TAC universal_INDUCT THEN REWRITE_TAC[specialize] THEN
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[qfree; specialize]);;

let SPECIALIZE_LANGUAGE = prove
 (`!s. language {specialize p | p IN s} = language s`,
  REWRITE_TAC[language; functions; predicates; PAIR_EQ] THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `(!p. functions_form(specialize p) = functions_form p) /\
    (!p. predicates_form(specialize p) = predicates_form p)`
  (fun th -> GEN_MESON_TAC 16 40 1[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[specialize; predicates_form; functions_form]);;

let SKOLEM = new_definition
  `SKOLEM p = specialize(SKOLEMIZE p)`;;

let SKOLEM_QFREE = prove
 (`!p. qfree(SKOLEM p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SKOLEM] THEN
  MATCH_MP_TAC SPECIALIZE_QFREE THEN
  REWRITE_TAC[SKOLEMIZE_WORKS]);;

let SKOLEM_SATISFIABLE = prove
 (`(?M. ~(Dom M :A->bool = EMPTY) /\
        interpretation (language s) M /\
        M satisfies s) =
   (?M. ~(Dom M :A->bool = EMPTY) /\
        interpretation (language {SKOLEM p | p IN s}) M /\
        M satisfies {SKOLEM p | p IN s})`,
  GEN_REWRITE_TAC LAND_CONV [SKOLEMIZE_SATISFIABLE] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> (b = c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN BINOP_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM SPECIALIZE_LANGUAGE] THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; SKOLEM] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[SKOLEM] THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC LAND_CONV [MATCH_MP SPECIALIZE_SATISFIES th]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; SKOLEM] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;
