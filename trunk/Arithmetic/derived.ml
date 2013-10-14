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
(* Some purely propositional schemas and derived rules.                      *)
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

let imp_mono_th = prove
 (`A |-- (p' --> p) --> (q --> q') --> (p --> q) --> (p' --> q')`,
  MESON_TAC[imp_trans; imp_swap; imp_trans_th]);;

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

let imp_false_rule = prove
 (`!p q r. A |-- (q --> False) --> p --> r
           ==> A |-- ((p --> q) --> False) --> r`,
  MESON_TAC[imp_add_concl; imp_add_assum; ex_falso; axiom_addimp; imp_swap;
            imp_trans; axiom_doubleneg; imp_unduplicate]);;

let imp_true_rule = prove
 (`!A p q r. A |-- (p --> False) --> r /\ A |-- q --> r
             ==> A |-- (p --> q) --> r`,
  MESON_TAC[imp_insert; imp_swap; modusponens; imp_trans_th; bool_cases]);;

let truth = prove
 (`!A. A |-- True`,
  MESON_TAC[modusponens; axiom_true; imp_refl; iff_imp2]);;

let and_left = prove
 (`!A p q. A |-- p && q --> p`,
  MESON_TAC[imp_add_assum; axiom_addimp; imp_trans; imp_add_concl;
            axiom_doubleneg; imp_trans; iff_imp1; axiom_and]);;

let and_right = prove
 (`!A p q. A |-- p && q --> q`,
  MESON_TAC[axiom_addimp; imp_trans; imp_add_concl; axiom_doubleneg;
            iff_imp1; axiom_and]);;

let and_pair = prove
 (`!A p q. A |-- p --> q --> p && q`,
  MESON_TAC[iff_imp2; axiom_and; imp_swap_th; imp_add_assum; imp_trans2;
            modusponens; imp_swap; imp_refl]);;

let META_AND = prove
 (`!A p q. A |-- p && q <=> A |-- p /\ A |-- q`,
  MESON_TAC[and_left; and_right; and_pair; modusponens]);;

let shunt = prove
 (`!A p q r. A |-- p && q --> r ==> A |-- p --> q --> r`,
  MESON_TAC[modusponens; imp_add_assum; and_pair]);;

let ante_conj = prove
 (`!A p q r. A |-- p --> q --> r ==> A |-- p && q --> r`,
  MESON_TAC[imp_trans_chain_2; and_left; and_right]);;

let not_not_false = prove
 (`!A p. A |-- (p --> False) --> False <-> p`,
  MESON_TAC[imp_antisym; axiom_doubleneg; imp_swap; imp_refl]);;

let iff_sym = prove
 (`!A p q. A |-- p <-> q <=> A |-- q <-> p`,
  MESON_TAC[iff_imp1; iff_imp2; imp_antisym]);;

let iff_trans = prove
 (`!A p q r. A |-- p <-> q /\ A |-- q <-> r ==> A |-- p <-> r`,
  MESON_TAC[iff_imp1; iff_imp2; imp_trans; imp_antisym]);;

let not_not = prove
 (`!A p. A |-- Not(Not p) <-> p`,
  MESON_TAC[iff_trans; not_not_false; axiom_not; imp_antisym; imp_add_concl;
            iff_imp1; iff_imp2]);;

let contrapos_eq = prove
 (`!A p q. A |-- Not p --> Not q <=> A |-- q --> p`,
  MESON_TAC[contrapos; not_not; iff_imp1; iff_imp2; imp_trans]);;

let or_left = prove
 (`!A p q. A |-- q --> p || q`,
  MESON_TAC[imp_trans; not_not; iff_imp2; and_right; contrapos; axiom_or]);;

let or_right = prove
 (`!A p q. A |-- p --> p || q`,
  MESON_TAC[imp_trans; not_not; iff_imp2; and_left; contrapos; axiom_or]);;

let ante_disj = prove
 (`!A p q r. A |-- p --> r /\ A |-- q --> r
             ==> A |-- p || q --> r`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM contrapos_eq] THEN
  MESON_TAC[imp_trans; imp_trans_chain_2; and_pair; contrapos_eq; not_not;
            axiom_or; iff_imp1; iff_imp2; imp_trans]);;

let iff_def = prove
 (`!A p q. A |-- (p <-> q) <-> (p --> q) && (q --> p)`,
  MESON_TAC[imp_antisym; imp_trans_chain_2; axiom_iffimp1; axiom_iffimp2;
            and_pair; axiom_impiff; imp_trans_chain_2; and_left; and_right]);;

let iff_refl = prove
 (`!A p. A |-- p <-> p`,
  MESON_TAC[imp_antisym; imp_refl]);;

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
 (`!p i j.
        (!x. x IN VARS p ==> safe_for x i)
        ==> formsubst j (formsubst i p) = formsubst (termsubst j o i) p`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[VARS; FORALL_IN_INSERT; IN_UNION; NOT_IN_EMPTY; FORALL_AND_THM;
              TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  SIMP_TAC[FORMSUBST_SAFE_FOR] THEN
  REWRITE_TAC[formsubst; TERMSUBST_TERMSUBST] THEN SIMP_TAC[] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`; `p:form`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`i:num->term`; `j:num->term`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[FV; FORMSUBST_FV; TERMSUBST_FVT; o_THM;
              IN_ELIM_THM; IN_DELETE] THEN
 (SUBGOAL_THEN
   `(?y. ((?y'. y' IN FV p /\ y IN FVT ((x |-> V x) i y')) /\ ~(y = x)) /\
          x IN FVT (j y)) <=>
    (?y. (y IN FV p /\ ~(y = x)) /\
         (?y'. y' IN FVT (i y) /\ x IN FVT (j y')))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `y:num` THEN
    ASM_CASES_TAC `y IN FV p` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `y:num = x` THEN ASM_REWRITE_TAC[] THENL
     [ASM_REWRITE_TAC[VALMOD; FVT; IN_SING] THEN MESON_TAC[]; ALL_TAC] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `z:num` THEN
    ASM_CASES_TAC `x IN FVT(j(z:num))` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VALMOD] THEN ASM_MESON_TAC[safe_for];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `{x' | ?y. (?y'. y' IN FV p /\ y IN FVT ((x |-> V x) i y')) /\
                x' IN FVT ((x |-> V x) j y)} =
      {x' | ?y. y IN FV p /\ x' IN FVT ((x |-> V x) (termsubst j o i) y)}`
     (fun th -> REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:num` THEN
      REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `y:num` THEN
      ASM_CASES_TAC `y IN FV p` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `y:num = x` THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[VALMOD; FVT; IN_SING; UNWIND_THM2] THEN
      REWRITE_TAC[o_THM; TERMSUBST_FVT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[safe_for];
      ABBREV_TAC `z = VARIANT
       {x' | ?y. y IN FV p /\ x' IN FVT ((x |-> V x) (termsubst j o i) y)}`];
      ALL_TAC]) THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (lhs o rand) th o lhs o snd)) THEN
  ASM_SIMP_TAC[SAFE_FOR_VALMOD; FVT; IN_SING] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FORMSUBST_EQ THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  REWRITE_TAC[VALMOD; o_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[termsubst; VALMOD] THEN
  MATCH_MP_TAC TERMSUBST_EQ THEN
  X_GEN_TAC `w:num` THEN REWRITE_TAC[VALMOD] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[safe_for]);;

let FORMSUBST_TWICE = prove
 (`!z p x t. ~(z IN VARS p)
             ==> (formsubst (z |=> t) (formsubst (x |=> V z) p) =
                  formsubst (x |=> t) p)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) FORMSUBST_TWICE_GENERAL o lhs o snd) THEN
  REWRITE_TAC[SAFE_FOR_ASSIGN; FVT; IN_SING] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC FORMSUBST_EQ THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[o_THM; VALMOD; ASSIGN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[termsubst; ASSIGN] THEN
  ASM_MESON_TAC[FV_SUBSET_VARS; SUBSET]);;

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

let spec_var = prove
 (`!A x p. A |-- !!x p ==> A |-- p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `V x` o MATCH_MP spec) THEN
  SIMP_TAC[ASSIGN_TRIV; FORMSUBST_TRIVIAL]);;

let instantiation = prove
 (`!A v p. A |-- p ==> A |-- formsubst v p`,
  let lemma = prove
   (`!A p v. (!x y. x IN FV p /\ y IN FV p /\ x IN FVT(v y)
                    ==> x = y /\ v x = V x) /\
             A |-- p
             ==> A |-- formsubst v p`,
    REPEAT GEN_TAC THEN
    WF_INDUCT_TAC `CARD {x | x IN FV(p) /\ ~(v x = V x)}` THEN
    ASM_CASES_TAC `!x. x IN FV p ==> v x = V x` THEN
    ASM_SIMP_TAC[FORMSUBST_TRIVIAL] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:num` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:form`; `(x |-> V x) v`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CARD_PSUBSET THEN SIMP_TAC[FINITE_RESTRICT; FV_FINITE] THEN
      REWRITE_TAC[PSUBSET_ALT] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; VALMOD; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[VALMOD; IN_ELIM_THM] THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[VALMOD] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[FVT; IN_SING] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `formsubst v p = formsubst ((x |-> v x) v) p`
    SUBST1_TAC THENL [SIMP_TAC[VALMOD_TRIVIAL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num` o MATCH_MP gen) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] modusponens) THEN
    MATCH_MP_TAC exists_imp THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[FORMSUBST_FV; IN_ELIM_THM; NOT_EXISTS_THM; VALMOD] THEN
      ASM SET_TAC[]] THEN
    MATCH_MP_TAC modusponens THEN EXISTS_TAC `??x (V x === v x)` THEN
    SIMP_TAC[eximp; isubst_general] THEN ASM_MESON_TAC[axiom_existseq]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?n. !x. x IN VARS p \/ x IN FV(formsubst v p) ==> x < n`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `SUC(SETMAX(VARS p UNION FV(formsubst v p)))` THEN
    REWRITE_TAC[GSYM IN_UNION; LT_SUC_LE] THEN MATCH_MP_TAC SETMAX_MEMBER THEN
    REWRITE_TAC[FINITE_UNION; VARS_FINITE; FV_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `formsubst v p =
    formsubst (\i. v(i - n)) (formsubst (\i. V(i + n)) p)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhs o rand) FORMSUBST_TWICE_GENERAL o
      rand o snd) THEN
    REWRITE_TAC[safe_for; FVT; IN_SING] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `~(x + n:num < n)`];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[o_DEF; termsubst; ADD_SUB; ETA_AX]];
    MATCH_MP_TAC lemma THEN REWRITE_TAC[FVT] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORMSUBST_FV; FVT; IN_SING] THEN
      REWRITE_TAC[SET_RULE `{x | ?y. y IN s /\ x = f y} = IMAGE f s`] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD_SUB; FVT] THEN
      X_GEN_TAC `y:num` THEN REPEAT DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x + n:num`) THEN
      MATCH_MP_TAC(TAUT `~p /\ q ==> (r \/ q ==> p) ==> s`) THEN
      CONJ_TAC THENL [ARITH_TAC; REWRITE_TAC[FORMSUBST_FV; IN_ELIM_THM]] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC lemma THEN REWRITE_TAC[FVT; IN_SING] THEN
      ASM_MESON_TAC[ARITH_RULE `x < n /\ y < n ==> ~(x = y + n)`;
                    FV_SUBSET_VARS; SUBSET]]]);;

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

(* ------------------------------------------------------------------------- *)
(* A few more derived rules.                                                 *)
(* ------------------------------------------------------------------------- *)

let eq_trans = prove
 (`!A s t u. A |-- s === t --> t === u --> s === u`,
  MESON_TAC[axiom_predcong; modusponens; imp_swap; axiom_eqrefl; imp_trans;
            eq_sym]);;

let spec_right = prove
 (`!A p q x. A |-- p --> !!x q ==> A |-- p --> formsubst (x |=> t) q`,
  MESON_TAC[imp_trans; ispec]);;

let eq_trans_rule = prove
 (`!A s t u. A |-- s === t /\ A |-- t === u ==> A |-- s === u`,
  MESON_TAC[modusponens; eq_trans]);;

let eq_sym_rule = prove
 (`!A s t. A |-- s === t <=> A |-- t === s`,
  MESON_TAC[modusponens; eq_sym]);;

let allimp = prove
 (`!A x p q. A |-- p --> q ==> A |-- !!x p --> !!x q`,
  MESON_TAC[axiom_allimp; modusponens; gen]);;

let alliff = prove
 (`!A x p q. A |-- p <-> q ==> A |-- !!x p <-> !!x q`,
  MESON_TAC[allimp; iff_imp1; iff_imp2; imp_antisym]);;

let exiff = prove
 (`!A x p q. A |-- p <-> q ==> A |-- ??x p <-> ??x q`,
  MESON_TAC[eximp; iff_imp1; iff_imp2; imp_antisym]);;

let cong_suc = prove
 (`!A s t. A |-- s === t ==> A |-- Suc s === Suc t`,
  MESON_TAC[modusponens; axiom_funcong]);;

let cong_add = prove
 (`!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s ++ u === t ++ v`,
  MESON_TAC[modusponens; axiom_funcong]);;

let cong_mul = prove
 (`!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s ** u === t ** v`,
  MESON_TAC[modusponens; axiom_funcong]);;

let cong_eq = prove
 (`!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s === u <-> t === v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC imp_antisym THEN
  ASM_MESON_TAC[modusponens; axiom_predcong; eq_sym]);;

let cong_le = prove
 (`!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s <<= u <-> t <<= v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC imp_antisym THEN
  ASM_MESON_TAC[modusponens; axiom_predcong; eq_sym]);;

let cong_lt = prove
 (`!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s << u <-> t << v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC imp_antisym THEN
  ASM_MESON_TAC[modusponens; axiom_predcong; eq_sym]);;

let iexists = prove
 (`!A x t p. A |-- formsubst (x |=> t) p --> ??x p`,
  REPEAT GEN_TAC THEN TRANS_TAC imp_trans `Not(!!x (Not p))` THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[axiom_exists; iff_imp2]] THEN
  TRANS_TAC imp_trans `Not(formsubst (x |=> t) (Not p))` THEN
  REWRITE_TAC[contrapos_eq; ispec] THEN REWRITE_TAC[formsubst] THEN
  MESON_TAC[not_not; iff_imp2]);;

let exists_intro = prove
 (`!A x t p. A |-- formsubst (x |=> t) p ==> A |-- ??x p`,
  MESON_TAC[iexists; modusponens]);;

let impex = prove
 (`!A x p. ~(x IN FV p) ==> A |-- (??x p) --> p`,
  REPEAT STRIP_TAC THEN TRANS_TAC imp_trans `Not(Not p)` THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[not_not; iff_imp1]] THEN
  TRANS_TAC imp_trans `Not(!!x (Not p))` THEN
  ASM_SIMP_TAC[contrapos_eq; axiom_impall; FV] THEN
  MESON_TAC[axiom_exists; iff_imp1]);;

let ichoose = prove
 (`!A x p q. A |-- !!x (p --> q) /\ ~(x IN FV q) ==> A |-- (??x p) --> q`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP spec_var) THEN
  DISCH_THEN(MP_TAC o SPEC `x:num` o MATCH_MP eximp) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] imp_trans) THEN
  ASM_SIMP_TAC[impex]);;

let eq_trans_imp = prove
 (`A |-- s === s' /\ A |-- t === t' ==> A |-- s === t --> s' === t'`,
  MESON_TAC[axiom_predcong; modusponens]);;

(* ------------------------------------------------------------------------- *)
(* Some conversions for performing explicit substitution operations in what  *)
(* we hope is the common case where no variable renaming occurs.             *)
(* ------------------------------------------------------------------------- *)

let fv_theorems = ref
 [FV; FV_AXIOM; FV_DIAGONALIZE; FV_DIVIDES; FV_FINITE; FV_FIXPOINT; FV_FORM;
  FV_FORM1; FV_FREEFORM; FV_FREEFORM1; FV_FREETERM; FV_FREETERM1;
  FV_GNUMERAL; FV_GNUMERAL1; FV_GNUMERAL1'; FV_GSENTENCE;
  FV_HSENTENCE; FV_PRIME; FV_PRIMEPOW; FV_PRIMREC; FV_PRIMRECSTEP; FV_PROV;
  FV_PROV1; FV_QDIAG; FV_QSUBST; FV_RTC; FV_RTCP; FV_SUBSET_VARS; FV_TERM;
  FV_TERM1; FVT; FVT_NUMERAL];;

let IN_FV_RULE ths tm =
  try EQT_ELIM
       ((GEN_REWRITE_CONV TOP_DEPTH_CONV
             ([IN_UNION; IN_DELETE; NOT_IN_EMPTY; IN_INSERT] @
              ths @ !fv_theorems) THENC
         NUM_REDUCE_CONV) tm)
  with Failure _ -> ASSUME tm;;

let rec SAFE_FOR_RULE tm =
  try PART_MATCH I SAFE_FOR_V tm
  with Failure _ ->
  try let th1 = PART_MATCH lhand SAFE_FOR_ASSIGN tm in
      let th2 = IN_FV_RULE [] (rand(concl th1)) in
      EQ_MP (SYM th1) th2
  with Failure _ ->
      let th1 = PART_MATCH rand SAFE_FOR_VALMOD tm in
      let l,r = dest_conj(lhand(concl th1)) in
      let th2 = CONJ (SAFE_FOR_RULE l) (IN_FV_RULE [] r) in
      MP th1 th2;;

let VALMOD_CONV =
  GEN_REWRITE_CONV TOP_DEPTH_CONV [ASSIGN; VALMOD] THENC NUM_REDUCE_CONV;;

let TERMSUBST_NUMERAL = prove
 (`!v n. termsubst v (numeral n) = numeral n`,
  SIMP_TAC[TERMSUBST_TRIVIAL; FVT_NUMERAL; NOT_IN_EMPTY]);;

let rec TERMSUBST_CONV tm =
  (GEN_REWRITE_CONV I [CONJ TERMSUBST_NUMERAL (CONJUNCT1 termsubst)] ORELSEC
   (GEN_REWRITE_CONV I [el 1 (CONJUNCTS termsubst)] THENC
    VALMOD_CONV) ORELSEC
   (GEN_REWRITE_CONV I [el 2 (CONJUNCTS termsubst)] THENC
    RAND_CONV TERMSUBST_CONV) ORELSEC
   (GEN_REWRITE_CONV I [funpow 3 CONJUNCT2 termsubst] THENC
    BINOP_CONV TERMSUBST_CONV)) tm;;

let rec FORMSUBST_CONV tm =
  (GEN_REWRITE_CONV I
    [el 0 (CONJUNCTS formsubst); el 1 (CONJUNCTS formsubst)] ORELSEC
   (GEN_REWRITE_CONV I
    [el 2 (CONJUNCTS formsubst); el 3 (CONJUNCTS formsubst);
     el 4 (CONJUNCTS formsubst)] THENC BINOP_CONV TERMSUBST_CONV) ORELSEC
   (GEN_REWRITE_CONV I [el 5 (CONJUNCTS formsubst)] THENC
    RAND_CONV FORMSUBST_CONV) ORELSEC
   (GEN_REWRITE_CONV I
     [el 6 (CONJUNCTS formsubst); el 7 (CONJUNCTS formsubst);
      el 8 (CONJUNCTS formsubst); el 9 (CONJUNCTS formsubst)] THENC
    BINOP_CONV FORMSUBST_CONV) ORELSEC
   ((fun tm ->
     let th =
       try PART_MATCH (lhand o rand) (CONJUNCT1 FORMSUBST_SAFE_FOR) tm
       with Failure _ ->
           PART_MATCH (lhand o rand) (CONJUNCT2 FORMSUBST_SAFE_FOR) tm in
     MP th (SAFE_FOR_RULE (lhand(concl th)))) THENC
    RAND_CONV FORMSUBST_CONV)) tm;;

(* ------------------------------------------------------------------------- *)
(* Hence a more convenient specialization rule.                              *)
(* ------------------------------------------------------------------------- *)

let spec_var_rule th = MATCH_MP spec_var th;;

let spec_all_rule = repeat spec_var_rule;;

let instantiate_rule ilist th =
  let v_tm = `(|->):num->term->(num->term)->(num->term)` in
  let v = itlist (fun (t,x) v ->
        mk_comb(mk_comb(mk_comb(v_tm,mk_small_numeral x),t),v)) ilist `V` in
  CONV_RULE (RAND_CONV FORMSUBST_CONV)
            (SPEC v (MATCH_MP instantiation th));;

let specl_rule tms th =
  let avs = striplist (dest_binop `!!`) (rand(concl th)) in
  let vs = fst(chop_list(length tms) avs) in
  let ilist = map2 (fun t v -> (t,dest_small_numeral v)) tms vs in
  instantiate_rule ilist (funpow (length vs) spec_var_rule th);;

let spec_rule t th = specl_rule [t] th;;

let gen_rule t th = SPEC (mk_small_numeral t) (MATCH_MP gen th);;

let gens_tac ns (asl,w) =
  let avs,bod = nsplit dest_forall ns w in
  let nvs = map (curry mk_comb `V` o mk_small_numeral) ns in
  let bod' = subst (zip nvs avs) bod in
  let th = GENL avs (instantiate_rule (zip avs ns) (ASSUME bod')) in
  MATCH_MP_TAC (DISCH_ALL th) (asl,w);;

let gen_tac n = gens_tac [n];;
