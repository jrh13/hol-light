(* ========================================================================= *)
(* Derived properties of provability.                                        *)
(* ========================================================================= *)

let negativef = new_definition
  `negativef p = ?q. p = q --> False`;;

let negatef = new_definition
  `negatef p = if negativef p then @q. p = q --> False else p --> False`;;

(* ------------------------------------------------------------------------- *)
(* The primitive basis, separated into its named components.                 *)
(* ------------------------------------------------------------------------- *)

let axiom_addimp = prove
 (`!A p q. A |-- p --> (q --> p)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_distribimp = prove
 (`!A p q r. A |-- (p --> q --> r) --> (p --> q) --> (p --> r)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_doubleneg = prove
 (`!A p. A |-- ((p --> False) --> False) --> p`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_allimp = prove
 (`!A x p q. A |-- (!!x (p --> q)) --> (!!x p) --> (!!x q)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_impall = prove
 (`!A x p. ~(x IN FV p) ==> A |-- p --> !!x p`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_existseq = prove
 (`!A x t. ~(x IN FVT t) ==> A |-- ??x (V x === t)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_eqrefl = prove
 (`!A t. A |-- t === t`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_funcong = prove
 (`(!A s t. A |-- s === t --> Suc s === Suc t) /\
   (!A s t u v. A |-- s === t --> u === v --> s ++ u === t ++ v) /\
   (!A s t u v. A |-- s === t --> u === v --> s ** u === t ** v)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_predcong = prove
 (`(!A s t u v. A |-- s === t --> u === v --> s === u --> t === v) /\
   (!A s t u v. A |-- s === t --> u === v --> s << u --> t << v) /\
   (!A s t u v. A |-- s === t --> u === v --> s <<= u --> t <<= v)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_iffimp1 = prove
 (`!A p q. A |-- (p <-> q) --> p --> q`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_iffimp2 = prove
 (`!A p q. A |-- (p <-> q) --> q --> p`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_impiff = prove
 (`!A p q. A |-- (p --> q) --> (q --> p) --> (p <-> q)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_true = prove
 (`A |-- True <-> (False --> False)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_not = prove
 (`!A p. A |-- Not p <-> (p --> False)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_and = prove
 (`!A p q. A |-- (p && q) <-> (p --> q --> False) --> False`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_or = prove
 (`!A p q. A |-- (p || q) <-> Not(Not p && Not q)`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let axiom_exists = prove
 (`!A x p. A |-- (??x p) <-> Not(!!x (Not p))`,
  MESON_TAC[proves_RULES; axiom_RULES]);;

let assume = prove
 (`!A p. p IN A ==> A |-- p`,
  MESON_TAC[proves_RULES]);;

let modusponens = prove
 (`!A p. A |-- (p --> q) /\ A |-- p ==> A |-- q`,
  MESON_TAC[proves_RULES]);;

let gen = prove
 (`!A p x. A |-- p ==> A |-- !!x p`,
  MESON_TAC[proves_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Now some theorems corresponding to derived rules.                         *)
(* ------------------------------------------------------------------------- *)

let iff_imp1 = prove
 (`!A p q. A |-- p <-> q ==> A |-- p --> q`,
  MESON_TAC[modusponens; axiom_iffimp1]);;

let iff_imp2 = prove
 (`!A p q. A |-- p <-> q ==> A |-- q --> p`,
  MESON_TAC[modusponens; axiom_iffimp2]);;

let imp_antisym = prove
 (`!A p q. A |-- p --> q /\ A |-- q --> p ==> A |-- p <-> q`,
  MESON_TAC[modusponens; axiom_impiff]);;

let add_assum = prove
 (`!A p q. A |-- q ==> A |-- p --> q`,
  MESON_TAC[modusponens; axiom_addimp]);;

let imp_refl = prove
 (`!A p. A |-- p --> p`,
  MESON_TAC[modusponens; axiom_distribimp; axiom_addimp]);;

let imp_add_assum = prove
 (`!A p q r. A |-- q --> r ==> A |-- (p --> q) --> (p --> r)`,
  MESON_TAC[modusponens; axiom_distribimp; add_assum]);;

let imp_unduplicate = prove
 (`!A p q. A |-- p --> p --> q ==> A |-- p --> q`,
  MESON_TAC[modusponens; axiom_distribimp; imp_refl]);;

let imp_trans = prove
 (`!A p q. A |-- p --> q /\ A |-- q --> r ==> A |-- p --> r`,
  MESON_TAC[modusponens; imp_add_assum]);;

let imp_swap = prove
 (`!A p q r. A |-- p --> q --> r ==> A |-- q --> p --> r`,
  MESON_TAC[imp_trans; axiom_addimp; modusponens; axiom_distribimp]);;

let imp_trans_chain_2 = prove
 (`!A p q1 q2 r. A |-- p --> q1 /\ A |-- p --> q2 /\ A |-- q1 --> q2 --> r
                 ==> A |-- p --> r`,
  ASM_MESON_TAC[imp_trans; imp_swap; imp_unduplicate]);;



(*****

let imp_trans_chain = prove
 (`!A p qs r. ALL (\q. A |-- p --> q) qs /\
              A |-- ITLIST (-->) qs r
              ==> A |-- p --> r`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; ITLIST] THENL
   [ASM_MESON_TAC[add_assum]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC


ASM_MESON_TAC[imp_trans; imp_swap; imp_unduplicate; axiom_distribimp;
              modusponens; add_assum]

add_assum] THEN
  ... needs more thought. Maybe the REV

 *****)


let imp_trans_th = prove
 (`!A p q r. A |-- (q --> r) --> (p --> q) --> (p --> r)`,
  MESON_TAC[imp_trans; axiom_addimp; axiom_distribimp]);;

let imp_add_concl = prove
 (`!A p q r. A |-- p --> q ==> A |-- (q --> r) --> (p --> r)`,
  MESON_TAC[modusponens; imp_swap; imp_trans_th]);;

let imp_trans2 = prove
 (`!A p q r s. A |-- p --> q --> r /\ A |-- r --> s ==> A |-- p --> q --> s`,
  MESON_TAC[imp_add_assum; modusponens; imp_trans_th]);;

let imp_swap_th = prove
 (`!A p q r. A |-- (p --> q --> r) --> (q --> p --> r)`,
  MESON_TAC[imp_trans; axiom_distribimp; imp_add_concl; axiom_addimp]);;

let contrapos = prove
 (`!A p q. A |-- p --> q ==> A |-- Not q --> Not p`,
  MESON_TAC[imp_trans; iff_imp1; axiom_not; imp_add_concl; iff_imp2]);;

let imp_truefalse = prove
 (`!p q. A |-- (q --> False) --> p --> (p --> q) --> False`,
  MESON_TAC[imp_trans; imp_trans_th; imp_swap_th]);;

let imp_insert = prove
 (`!A p q r. A |-- p --> r ==> A |-- p --> q --> r`,
  MESON_TAC[imp_trans; axiom_addimp]);;

let ex_falso = prove
 (`!A p. A |-- False --> p`,
  MESON_TAC[imp_trans; axiom_addimp; axiom_doubleneg]);;

let imp_contr = prove
 (`!A p q. A |-- (p --> False) --> (p --> r)`,
  MESON_TAC[imp_add_assum; ex_falso]);;

let imp_contrf = prove
 (`!A p r. A |-- p --> negatef p --> r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[negatef; negativef] THEN
  COND_CASES_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[form_INJ] THEN
  ASM_MESON_TAC[imp_contr; imp_swap]);;

let contrad = prove
 (`!A p. A |-- (p --> False) --> p ==> A |-- p`,
  MESON_TAC[modusponens; axiom_distribimp; imp_refl; axiom_doubleneg]);;

let bool_cases = prove
 (`!p q. A |-- p --> q /\ A |-- (p --> False) --> q ==> A |-- q`,
  MESON_TAC[contrad; imp_trans; imp_add_concl]);;

(****

let imp_front = prove
 (`...` a bi more structure);;

****)

(*** This takes about a minute, but it does work ***)

let imp_false_rule = prove
 (`!p q r. A |-- (q --> False) --> p --> r
           ==> A |-- ((p --> q) --> False) --> r`,
  MESON_TAC[imp_add_concl; imp_add_assum; ex_falso; axiom_addimp; imp_swap;
            imp_trans; axiom_doubleneg; imp_unduplicate]);;

let imp_true_rule = prove
 (`!A p q r. A |-- (p --> False) --> r /\ A |-- q --> r
             ==> A |-- (p --> q) --> r`,
  MESON_TAC[imp_insert; imp_swap; modusponens; imp_trans_th; bool_cases]);;

let iff_def = prove
 (`!A p q. A |-- (p <-> q) <-> (p --> q) && (q --> p)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC imp_antisym THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `A |-- ((p --> q) --> (q --> p) --> False) --> (p <-> q) --> False`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[imp_add_concl; imp_trans; axiom_distribimp; modusponens;
                    imp_swap; axiom_iffimp1; axiom_iffimp2];
      ALL_TAC] THEN
    ASM_MESON_TAC[imp_add_concl; imp_trans; imp_swap; imp_refl;
                   iff_imp2; axiom_and];
    SUBGOAL_THEN
     `A |-- (((p --> q) --> (q --> p) --> False) --> False)
            --> ((p <-> q) --> False) --> False`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[imp_swap; imp_trans_th; modusponens; imp_add_assum;
                    axiom_impiff; imp_add_concl];
      ALL_TAC] THEN
    ASM_MESON_TAC[imp_trans; iff_imp1; axiom_and; axiom_doubleneg]]);;

(* ------------------------------------------------------------------------- *)
(* Equality rules.                                                           *)
(* ------------------------------------------------------------------------- *)

let eq_sym = prove
 (`!A s t. A |-- s === t --> t === s`,
  MESON_TAC[axiom_eqrefl; modusponens; imp_swap; axiom_predcong]);;

let icongruence_general = prove
 (`!A p x s t tm.
     A |-- s === t -->
           termsubst ((x |-> s) v) tm === termsubst ((x |-> t) v) tm`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[termsubst] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[axiom_eqrefl; add_assum];
    GEN_TAC THEN REWRITE_TAC[valmod] THEN
    COND_CASES_TAC THEN REWRITE_TAC[imp_refl] THEN
    MESON_TAC[axiom_eqrefl; add_assum];
    MESON_TAC[imp_trans; axiom_funcong];
    MESON_TAC[imp_trans; axiom_funcong; imp_swap; imp_unduplicate];
    MESON_TAC[imp_trans; axiom_funcong; imp_swap; imp_unduplicate]]);;

let icongruence = prove
 (`!A x s t tm.
     A |-- s === t --> termsubst (x |=> s) tm === termsubst (x |=> t) tm`,
  REWRITE_TAC[assign; icongruence_general]);;

let icongruence_var = prove
 (`!A x t tm.
     A |-- V x === t --> tm === termsubst (x |=> t) tm`,
  MESON_TAC[icongruence; TERMSUBST_TRIV; ASSIGN_TRIV]);;

(* ------------------------------------------------------------------------- *)
(* First-order rules.                                                        *)
(* ------------------------------------------------------------------------- *)

let gen_right = prove
 (`!A x p q. ~(x IN FV(p)) /\ A |-- p --> q
             ==> A |-- p --> !!x q`,
  MESON_TAC[axiom_allimp; modusponens; gen; imp_trans; axiom_impall]);;

let genimp = prove
 (`!x p q. A |-- p --> q ==> A |-- (!!x p) --> (!!x q)`,
  MESON_TAC[modusponens; axiom_allimp; gen]);;

let eximp = prove
 (`!x p q. A |-- p --> q ==> A |-- (??x p) --> (??x q)`,
  MESON_TAC[contrapos; genimp; contrapos; imp_trans; iff_imp1; iff_imp2;
            axiom_exists]);;

let exists_imp = prove
 (`!A x p q. A |-- ??x (p --> q) /\ ~(x IN FV(q)) ==> A |-- (!!x p) --> q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `A |-- (q --> False) --> !!x (p --> Not(p --> q))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC gen_right THEN
    ASM_REWRITE_TAC[FV; IN_UNION; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[iff_imp2; axiom_not; imp_trans2; imp_truefalse];
    ALL_TAC] THEN
  SUBGOAL_THEN `A |-- (q --> False) --> !!x p --> !!x (Not(p --> q))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[imp_trans; axiom_allimp]; ALL_TAC] THEN
  SUBGOAL_THEN `A |-- ((q --> False) --> !!x (Not(p --> q)))
                      --> (q --> False) --> False`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[modusponens; iff_imp1; axiom_exists; axiom_not; imp_trans_th];
    ALL_TAC] THEN
  ASM_MESON_TAC[imp_trans; imp_swap; axiom_doubleneg]);;

let subspec = prove
 (`!A x t p q. ~(x IN FVT(t)) /\ ~(x IN FV(q)) /\ A |-- V x === t --> p --> q
               ==> A |-- (!!x p) --> q`,
  MESON_TAC[exists_imp; modusponens; eximp; axiom_existseq]);;

let subalpha = prove
 (`!A x y p q. ((x = y) \/ ~(x IN FV(q)) /\ ~(y IN FV(p))) /\
               A |-- V x === V y --> p --> q
               ==> A |-- (!!x p) --> (!!y q)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = y:num` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_MESON_TAC[genimp; modusponens; axiom_eqrefl];
    ALL_TAC] THEN
  MATCH_MP_TAC gen_right THEN ASM_REWRITE_TAC[FV; IN_DELETE] THEN
  MATCH_MP_TAC subspec THEN EXISTS_TAC `V y` THEN
  ASM_REWRITE_TAC[FVT; IN_SING]);;

let imp_mono_th = prove
 (`A |-- (p' --> p) --> (q --> q') --> (p --> q) --> (p' --> q')`,
  MESON_TAC[imp_trans; imp_swap; imp_trans_th]);;

(* ------------------------------------------------------------------------- *)
(* We'll perform induction on this measure.                                  *)
(* ------------------------------------------------------------------------- *)

let complexity = new_recursive_definition form_RECURSION
  `(complexity False = 1) /\
   (complexity True = 1) /\
   (!s t. complexity (s === t) = 1) /\
   (!s t. complexity (s << t) = 1) /\
   (!s t. complexity (s <<= t) = 1) /\
   (!p. complexity (Not p) = complexity p + 3) /\
   (!p q. complexity (p && q) = complexity p + complexity q + 6) /\
   (!p q. complexity (p || q) = complexity p + complexity q + 16) /\
   (!p q. complexity (p --> q) = complexity p + complexity q + 1) /\
   (!p q. complexity (p <-> q) = 2 * (complexity p + complexity q) + 9) /\
   (!x p. complexity (!!x p) = complexity p + 1) /\
   (!x p. complexity (??x p) = complexity p + 8)`;;

let COMPLEXITY_FORMSUBST = prove
 (`!p i. complexity(formsubst i p) = complexity p`,
  MATCH_MP_TAC form_INDUCT THEN
  SIMP_TAC[formsubst; complexity; LET_DEF; LET_END_DEF]);;

let isubst_general = prove
 (`!A p x v s t. A |-- s === t
                       --> formsubst ((x |-> s) v) p
                           --> formsubst ((x |-> t) v) p`,
  GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `complexity p` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[formsubst; complexity] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[imp_refl; add_assum];
    MESON_TAC[imp_refl; add_assum];
    MESON_TAC[imp_trans_chain_2; axiom_predcong; icongruence_general];
    MESON_TAC[imp_trans_chain_2; axiom_predcong; icongruence_general];
    MESON_TAC[imp_trans_chain_2; axiom_predcong; icongruence_general];
    X_GEN_TAC `p:form` THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `p --> False`) THEN
    REWRITE_TAC[complexity] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[formsubst] THEN
    MESON_TAC[axiom_not; iff_imp1; iff_imp2; imp_swap; imp_trans; imp_trans2];
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `(p --> q --> False) --> False`) THEN
    REWRITE_TAC[complexity] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[formsubst] THEN
    MESON_TAC[axiom_and; iff_imp1; iff_imp2; imp_swap; imp_trans; imp_trans2];
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `Not(Not p && Not q)`) THEN
    REWRITE_TAC[complexity] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[formsubst] THEN
    MESON_TAC[axiom_or; iff_imp1; iff_imp2; imp_swap; imp_trans; imp_trans2];
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `p:form` th) THEN
                         MP_TAC(SPEC `q:form` th)) THEN
    REWRITE_TAC[ARITH_RULE `p < p + q + 1 /\ q < p + q + 1`] THEN
    MESON_TAC[imp_mono_th; eq_sym; imp_trans; imp_trans_chain_2];
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `(p --> q) && (q --> p)`) THEN
    REWRITE_TAC[complexity] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[formsubst] THEN
    MESON_TAC[iff_def; iff_imp1; iff_imp2; imp_swap; imp_trans; imp_trans2];
    ALL_TAC;
    MAP_EVERY X_GEN_TAC [`x:num`; `p:form`] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `Not(!!x (Not p))`) THEN
    REWRITE_TAC[complexity] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[formsubst] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC[FV] THEN REPEAT LET_TAC THEN
    ASM_MESON_TAC[axiom_exists; iff_imp1; iff_imp2; imp_swap; imp_trans;
                  imp_trans2]] THEN
  MAP_EVERY X_GEN_TAC [`u:num`; `p:form`] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `a < b + 1 <=> a <= b`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`v:num`; `i:num->term`; `s:term`; `t:term`] THEN
  MAP_EVERY ABBREV_TAC
   [`x = if ?y. y IN FV (!! u p) /\ u IN FVT ((v |-> s) i y)
         then VARIANT (FV (formsubst ((u |-> V u) ((v |-> s) i)) p))
         else u`;
    `y = if ?y. y IN FV (!! u p) /\ u IN FVT ((v |-> t) i y)
         then VARIANT (FV (formsubst ((u |-> V u) ((v |-> t) i)) p))
         else u`] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `~(x IN FV(formsubst ((v |-> s) i) (!!u p))) /\
                ~(y IN FV(formsubst ((v |-> t) i) (!!u p)))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN CONJ_TAC THEN
    (COND_CASES_TAC THENL
       [ALL_TAC; ASM_REWRITE_TAC[FORMSUBST_FV; IN_ELIM_THM]] THEN
      MATCH_MP_TAC NOT_IN_VARIANT THEN REWRITE_TAC[FV_FINITE] THEN
      REWRITE_TAC[SUBSET; FORMSUBST_FV; IN_ELIM_THM; FV; IN_DELETE] THEN
      REWRITE_TAC[valmod] THEN MESON_TAC[FVT; IN_SING]);
    ALL_TAC] THEN
  ASM_CASES_TAC `v:num = u` THENL
   [ASM_REWRITE_TAC[VALMOD_VALMOD_BASIC] THEN
    MATCH_MP_TAC add_assum THEN MATCH_MP_TAC subalpha THEN
    ASM_SIMP_TAC[LE_REFL] THEN
    ASM_CASES_TAC `y:num = x` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(x IN FV (formsubst ((v |-> s) i) (!! u p)))`;
      UNDISCH_TAC `~(y IN FV (formsubst ((v |-> t) i) (!! u p)))`] THEN
    ASM_REWRITE_TAC[FORMSUBST_FV; FV; IN_ELIM_THM; IN_DELETE] THEN
    MATCH_MP_TAC MONO_NOT THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `w:num` THEN ASM_CASES_TAC `w:num = u` THEN
    ASM_REWRITE_TAC[VALMOD_BASIC; FVT; IN_SING] THEN
    ASM_REWRITE_TAC[valmod; FVT; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?z. ~(z IN FVT s) /\ ~(z IN FVT t) /\
        A |-- !!x (formsubst ((u |-> V x) ((v |-> s) i)) p)
              --> !!z (formsubst ((u |-> V z) ((v |-> s) i)) p) /\
        A |-- !!z (formsubst ((u |-> V z) ((v |-> t) i)) p)
              --> !!y (formsubst ((u |-> V y) ((v |-> t) i)) p)`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC imp_trans THEN
    EXISTS_TAC `(!!z (formsubst ((v |-> s) ((u |-> V z) i)) p))
                     --> (!!z (formsubst ((v |-> t) ((u |-> V z) i)) p))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC imp_trans THEN
      EXISTS_TAC `!!z (formsubst ((v |-> s) ((u |-> V z) i)) p
                       --> formsubst ((v |-> t) ((u |-> V z) i)) p)` THEN
      REWRITE_TAC[axiom_allimp] THEN
      ASM_SIMP_TAC[complexity; LE_REFL; FV; IN_UNION; gen_right];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP VALMOD_SWAP th]) THEN
    ASM_MESON_TAC[imp_mono_th; modusponens]] THEN
  MP_TAC(SPEC
   `FVT(s) UNION FVT(t) UNION
    FV(formsubst ((u |-> V x) ((v |-> s) i)) p) UNION
    FV(formsubst ((u |-> V y) ((v |-> t) i)) p)` VARIANT_FINITE) THEN
  REWRITE_TAC[FINITE_UNION; FV_FINITE; FVT_FINITE] THEN
  W(fun (_,w) -> ABBREV_TAC(mk_comb(`(=) (z:num)`,lhand(rand(lhand w))))) THEN
  REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC subalpha THEN ASM_SIMP_TAC[LE_REFL] THENL
   [ASM_CASES_TAC `z:num = x` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(x IN FV (formsubst ((v |-> s) i) (!! u p)))`;
    ASM_CASES_TAC `z:num = y` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(y IN FV (formsubst ((v |-> t) i) (!! u p)))`] THEN
  ASM_REWRITE_TAC[FORMSUBST_FV; FV; IN_ELIM_THM; IN_DELETE] THEN
  MATCH_MP_TAC MONO_NOT THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `w:num` THEN ASM_CASES_TAC `w:num = u` THEN
  ASM_REWRITE_TAC[VALMOD_BASIC; FVT; IN_SING] THEN
  ASM_REWRITE_TAC[valmod; FVT; IN_SING]);;

let isubst = prove
 (`!A p x s t. A |-- s === t
                     --> formsubst (x |=> s) p --> formsubst (x |=> t) p`,
  REWRITE_TAC[assign; isubst_general]);;

let isubst_var = prove
 (`!A p x t. A |-- V x === t --> p --> formsubst (x |=> t) p`,
  MESON_TAC[FORMSUBST_TRIV; ASSIGN_TRIV; isubst]);;

let alpha = prove
 (`!A x z p. ~(z IN FV p) ==> A |-- (!!x p) --> !!z (formsubst (x |=> V z) p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC subalpha THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[isubst_var]] THEN
  REWRITE_TAC[FORMSUBST_FV; IN_ELIM_THM; ASSIGN] THEN
  ASM_MESON_TAC[IN_SING; FVT]);;

(* ------------------------------------------------------------------------- *)
(* To conclude cleanly, useful to have all variables.                        *)
(* ------------------------------------------------------------------------- *)

let VARS = new_recursive_definition form_RECURSION
 `(VARS False = {}) /\
  (VARS True = {}) /\
  (VARS (s === t) = FVT s UNION FVT t) /\
  (VARS (s << t) = FVT s UNION FVT t) /\
  (VARS (s <<= t) = FVT s UNION FVT t) /\
  (VARS (Not p) = VARS p) /\
  (VARS (p && q) = VARS p UNION VARS q) /\
  (VARS (p || q) = VARS p UNION VARS q) /\
  (VARS (p --> q) = VARS p UNION VARS q) /\
  (VARS (p <-> q) = VARS p UNION VARS q) /\
  (VARS (!! x p) = x INSERT VARS p) /\
  (VARS (?? x p) = x INSERT VARS p)`;;

let VARS_FINITE = prove
 (`!p. FINITE(VARS p)`,
  MATCH_MP_TAC form_INDUCT THEN
  ASM_SIMP_TAC[VARS; FINITE_RULES; FVT_FINITE; FINITE_UNION; FINITE_DELETE]);;

let FV_SUBSET_VARS = prove
 (`!p. FV(p) SUBSET VARS(p)`,
  REWRITE_TAC[SUBSET] THEN
  MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[FV; VARS] THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; IN_DELETE] THEN MESON_TAC[]);;

let TERMSUBST_TWICE_GENERAL = prove
 (`!x z t v s. ~(z IN FVT s)
               ==> (termsubst ((x |-> t) v) s =
                    termsubst ((z |-> t) v) (termsubst (x |=> V z) s))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termsubst; ASSIGN; valmod; FVT; IN_SING; IN_UNION] THEN
  MESON_TAC[termsubst; ASSIGN]);;

let TERMSUBST_TWICE = prove
 (`!x z t s. ~(z IN FVT s)
             ==> (termsubst (x |=> t) s =
                  termsubst (z |=> t) (termsubst (x |=> V z) s))`,
  MESON_TAC[assign; TERMSUBST_TWICE_GENERAL]);;

let FORMSUBST_TWICE_GENERAL = prove
 (`!z p x t v. ~(z IN VARS p)
               ==> (formsubst ((z |-> t) v) (formsubst (x |=> V z) p) =
                    formsubst ((x |-> t) v) p)`,
  GEN_TAC THEN MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[CONJ_ASSOC] THEN
  GEN_REWRITE_TAC I [GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [REWRITE_TAC[formsubst; ASSIGN; VARS; IN_UNION; DE_MORGAN_THM] THEN
    MESON_TAC[TERMSUBST_TWICE_GENERAL];
    ALL_TAC] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`y:num`; `p:form`] THEN
  (REWRITE_TAC[VARS; IN_INSERT; DE_MORGAN_THM] THEN
   DISCH_THEN(fun th -> REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [formsubst] THEN
   COND_CASES_TAC THENL
    [FIRST_X_ASSUM(CHOOSE_THEN MP_TAC) THEN
     REWRITE_TAC[ASSIGN; FV; IN_DELETE] THEN
     ASM_MESON_TAC[FVT; IN_SING];
     ALL_TAC] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   ASM_CASES_TAC `x:num = y` THENL
    [ASM_REWRITE_TAC[assign; VALMOD_VALMOD_BASIC; VALMOD_REPEAT;
                     FORMSUBST_TRIV] THEN
     MATCH_MP_TAC FORMSUBST_EQ THEN
     ASM_REWRITE_TAC[valmod; FV; IN_DELETE] THEN
     ASM_MESON_TAC[FV_SUBSET_VARS; SUBSET];
     ALL_TAC] THEN
   SUBGOAL_THEN
    `(!t. (y |-> V y) (x |=> t) = x |=> t) /\
     (!t. (y |-> V y) (z |=> t) = z |=> t)`
   STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[assign] THEN ASM_MESON_TAC[VALMOD_SWAP; VALMOD_REPEAT];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC BINOP_CONV [formsubst] THEN
   ASM_REWRITE_TAC[FV] THEN
   SUBGOAL_THEN
    `(?u. u IN (FV(formsubst (x |=> V z) p) DELETE y) /\
          y IN FVT ((z |-> t) v u)) =
     (?u. u IN (FV p DELETE y) /\ y IN FVT ((x |-> t) v u))`
   SUBST1_TAC THENL
    [REWRITE_TAC[FV; FORMSUBST_FV; IN_ELIM_THM; IN_DELETE; valmod; ASSIGN] THEN
     ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
     REWRITE_TAC[FVT; IN_SING] THEN
     ASM_MESON_TAC[SUBSET; FV_SUBSET_VARS; FVT; IN_SING];
     ALL_TAC] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [ALL_TAC;
     REWRITE_TAC[LET_DEF; LET_END_DEF; form_INJ] THEN
     ASM_MESON_TAC[VALMOD_SWAP]] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF; form_INJ] THEN
   MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
    [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
   REPEAT AP_TERM_TAC THEN ASM_MESON_TAC[VALMOD_SWAP]));;

let FORMSUBST_TWICE = prove
 (`!z p x t. ~(z IN VARS p)
             ==> (formsubst (z |=> t) (formsubst (x |=> V z) p) =
                  formsubst (x |=> t) p)`,
  MESON_TAC[assign; FORMSUBST_TWICE_GENERAL]);;

let ispec_lemma = prove
 (`!A x p t. ~(x IN FVT(t)) ==> A |-- !!x p --> formsubst (x |=> t) p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC subspec THEN
  EXISTS_TAC `t:term` THEN ASM_REWRITE_TAC[isubst_var] THEN
  ASM_REWRITE_TAC[FORMSUBST_FV; IN_ELIM_THM; ASSIGN] THEN
  ASM_MESON_TAC[FVT; IN_SING]);;

let ispec = prove
 (`!A x p t. A |-- !!x p --> formsubst (x |=> t) p`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x IN FVT(t)` THEN
  ASM_SIMP_TAC[ispec_lemma] THEN
  ABBREV_TAC `z = VARIANT (FVT t UNION VARS p)` THEN
  MATCH_MP_TAC imp_trans THEN
  EXISTS_TAC `!!z (formsubst (x |=> V z) p)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC alpha THEN EXPAND_TAC "z" THEN
    MATCH_MP_TAC NOT_IN_VARIANT THEN
    REWRITE_TAC[FINITE_UNION; SUBSET; IN_UNION] THEN
    MESON_TAC[SUBSET; FVT_FINITE; VARS_FINITE; FV_SUBSET_VARS];
    SUBGOAL_THEN
     `formsubst (x |=> t) p =
      formsubst (z |=> t) (formsubst (x |=> V z) p)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(GSYM FORMSUBST_TWICE); MATCH_MP_TAC ispec_lemma] THEN
    EXPAND_TAC "z" THEN MATCH_MP_TAC NOT_IN_VARIANT THEN
    REWRITE_TAC[VARS_FINITE; FVT_FINITE; FINITE_UNION] THEN
    SIMP_TAC[SUBSET; IN_UNION]]);;

let spec = prove
 (`!A x p t. A |-- !!x p ==> A |-- formsubst (x |=> t) p`,
  MESON_TAC[ispec; modusponens]);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity and the deduction theorem.                                   *)
(* ------------------------------------------------------------------------- *)

let PROVES_MONO = prove
 (`!A B p. A SUBSET B /\ A |-- p ==> B |-- p`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC proves_INDUCT THEN  ASM_MESON_TAC[proves_RULES; SUBSET]);;

let DEDUCTION_LEMMA = prove
 (`!A p q. p INSERT A |-- q /\ closed p ==> A |-- p --> q`,
  GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC proves_INDUCT THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `r:form` THENL
   [REWRITE_TAC[IN_INSERT] THEN MESON_TAC[proves_RULES; add_assum; imp_refl];
    MESON_TAC[modusponens; axiom_distribimp];
    ASM_MESON_TAC[gen_right; closed; NOT_IN_EMPTY]]);;

let DEDUCTION = prove
 (`!A p q. closed p ==> (A |-- p --> q <=> p INSERT A |-- q)`,
  MESON_TAC[DEDUCTION_LEMMA; modusponens; IN_INSERT; proves_RULES;
            PROVES_MONO; SUBSET]);;
