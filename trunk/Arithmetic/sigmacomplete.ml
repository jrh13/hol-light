(* ========================================================================= *)
(* Sigma_1 completeness of Robinson's axioms Q.                              *)
(* ========================================================================= *)

let robinson = new_definition
 `robinson =
        (!!0 (!!1 (Suc(V 0) === Suc(V 1) --> V 0 === V 1))) &&
        (!!1 (Not(V 1 === Z) <-> ??0 (V 1 === Suc(V 0)))) &&
        (!!1 (Z ++ V 1 === V 1)) &&
        (!!0 (!!1 (Suc(V 0) ++ V 1 === Suc(V 0 ++ V 1)))) &&
        (!!1 (Z ** V 1 === Z)) &&
        (!!0 (!!1 (Suc(V 0) ** V 1 === V 1 ++ V 0 ** V 1))) &&
        (!!0 (!!1 (V 0 <<= V 1 <-> ??2 (V 0 ++ V 2 === V 1)))) &&
        (!!0 (!!1 (V 0 << V 1 <-> Suc(V 0) <<= V 1)))`;;

(* ------------------------------------------------------------------------- *)
(* Individual "axioms" and their instances.                                  *)
(* ------------------------------------------------------------------------- *)

let [suc_inj; num_cases; add_0; add_suc; mul_0; mul_suc; le_def; lt_def] =
  CONJUNCTS(REWRITE_RULE[META_AND] (GEN_REWRITE_RULE RAND_CONV [robinson]
  (MATCH_MP assume (SET_RULE `robinson IN {robinson}`))));;

let suc_inj' = prove
 (`!s t. {robinson} |-- Suc(s) === Suc(t) --> s === t`,
  REWRITE_TAC[specl_rule [`s:term`; `t:term`] suc_inj]);;

let num_cases' = prove
 (`!t z. ~(z IN FVT t)
           ==> {robinson} |--  (Not(t === Z) <-> ??z (t === Suc(V z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:term` (MATCH_MP spec num_cases)) THEN
  REWRITE_TAC[formsubst] THEN
  CONV_TAC(ONCE_DEPTH_CONV TERMSUBST_CONV) THEN
  REWRITE_TAC[FV; FVT; SET_RULE `({1} UNION {0}) DELETE 0 = {1} DIFF {0}`] THEN
  REWRITE_TAC[IN_DIFF; IN_SING; UNWIND_THM2; GSYM CONJ_ASSOC; ASSIGN] THEN
  REWRITE_TAC[ARITH_EQ] THEN LET_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] iff_trans) THEN
  SUBGOAL_THEN `~(z' IN FVT t)` ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[SET_RULE `a IN s ==> s UNION {a} = s`;
                 VARIANT_FINITE; FVT_FINITE];
    MATCH_MP_TAC imp_antisym THEN
    ASM_CASES_TAC `z':num = z` THEN ASM_REWRITE_TAC[imp_refl] THEN
    CONJ_TAC THEN MATCH_MP_TAC ichoose THEN
    ASM_REWRITE_TAC[FV; IN_DELETE; IN_UNION; IN_SING; FVT] THEN
    MATCH_MP_TAC gen THEN MATCH_MP_TAC imp_trans THENL
     [EXISTS_TAC `formsubst (z |=> V z') (t === Suc(V z))`;
      EXISTS_TAC `formsubst (z' |=> V z) (t === Suc(V z'))`] THEN
    REWRITE_TAC[iexists] THEN REWRITE_TAC[formsubst] THEN
    ASM_REWRITE_TAC[termsubst; ASSIGN] THEN
    MATCH_MP_TAC(MESON[imp_refl] `p = q ==> A |-- p --> q`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC TERMSUBST_TRIVIAL THEN REWRITE_TAC[ASSIGN] THEN
    ASM_MESON_TAC[]]);;

let add_0' = prove
 (`!t. {robinson} |--  Z ++ t === t`,
  REWRITE_TAC[spec_rule `t:term` add_0]);;

let add_suc' = prove
 (`!s t. {robinson} |--  Suc(s) ++ t === Suc(s ++ t)`,
  REWRITE_TAC[specl_rule [`s:term`; `t:term`] add_suc]);;

let mul_0' = prove
 (`!t. {robinson} |--  Z ** t === Z`,
  REWRITE_TAC[spec_rule `t:term` mul_0]);;

let mul_suc' = prove
 (`!s t. {robinson} |--  Suc(s) ** t === t ++ s ** t`,
  REWRITE_TAC[specl_rule [`s:term`; `t:term`] mul_suc]);;

let lt_def' = prove
 (`!s t. {robinson} |--  (s << t <-> Suc(s) <<= t)`,
  REWRITE_TAC[specl_rule [`s:term`; `t:term`] lt_def]);;

(* ------------------------------------------------------------------------- *)
(* All ground terms can be evaluated by proof.                               *)
(* ------------------------------------------------------------------------- *)

let SIGMA1_COMPLETE_ADD = prove
 (`!m n. {robinson} |-- numeral m ++ numeral n === numeral(m + n)`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; numeral] THEN
  ASM_MESON_TAC[add_0'; add_suc'; axiom_funcong; eq_trans; modusponens]);;

let SIGMA1_COMPLETE_MUL = prove
 (`!m n. {robinson} |-- (numeral m ** numeral n === numeral(m * n))`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; numeral] THENL
   [ASM_MESON_TAC[mul_0']; ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC eq_trans_rule THEN
  EXISTS_TAC `numeral(n) ++ numeral(m * n)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[mul_suc'; eq_trans_rule; axiom_funcong; imp_trans;
                  modusponens; imp_swap;add_assum; axiom_eqrefl];
    ASM_MESON_TAC[SIGMA1_COMPLETE_ADD; ADD_SYM; eq_trans_rule]]);;

let SIGMA1_COMPLETE_TERM = prove
 (`!v t n. FVT t = {} /\ termval v t = n
           ==> {robinson} |-- (t === numeral n)`,
  let lemma = prove(`(!n. p /\ (x = n) ==> P n) <=> p ==> P x`,MESON_TAC[]) in
  GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termval;FVT; NOT_INSERT_EMPTY] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[numeral] THEN
    MESON_TAC[axiom_eqrefl; add_assum];
    ALL_TAC] THEN
  REWRITE_TAC[lemma] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EMPTY_UNION]) THEN ASM_REWRITE_TAC[numeral] THEN
  MESON_TAC[SIGMA1_COMPLETE_ADD; SIGMA1_COMPLETE_MUL;
            cong_suc; cong_add; cong_mul; eq_trans_rule]);;

(* ------------------------------------------------------------------------- *)
(* Convenient stepping theorems for atoms and other useful lemmas.           *)
(* ------------------------------------------------------------------------- *)

let canonize_clauses =
  let lemma0 = MESON[imp_refl; imp_swap; modusponens; axiom_doubleneg]
    `!A p. A |-- (p --> False) --> False <=> A |-- p`
  and lemma1 = MESON[iff_imp1; iff_imp2; modusponens; imp_trans]
   `A |-- p <-> q
    ==> (A |-- p <=> A |-- q) /\ (A |-- p --> False <=> A |-- q --> False)` in
  itlist (CONJ o MATCH_MP lemma1 o SPEC_ALL)
         [axiom_true; axiom_not; axiom_and; axiom_or; iff_def; axiom_exists]
         lemma0
and false_imp = MESON[imp_truefalse; modusponens]
  `A |-- p /\ A |-- q --> False ==> A |-- (p --> q) --> False`
and true_imp = MESON[axiom_addimp; modusponens; ex_falso; imp_trans]
 `A |-- p --> False \/ A |-- q ==> A |-- p --> q`;;

let CANONIZE_TAC =
  REWRITE_TAC[canonize_clauses; imp_refl] THEN
  REPEAT((MATCH_MP_TAC false_imp THEN CONJ_TAC) ORELSE
         MATCH_MP_TAC true_imp THEN
         REWRITE_TAC[canonize_clauses; imp_refl]);;

let suc_inj_eq = prove
 (`!s t. {robinson} |-- Suc s === Suc t <-> s === t`,
  MESON_TAC[suc_inj'; axiom_funcong; imp_antisym]);;

let suc_le_eq = prove
 (`!s t. {robinson} |-- Suc s <<= Suc t <-> s <<= t`,
  gens_tac [0;1] THEN
  TRANS_TAC iff_trans `??2 (Suc(V 0) ++ V 2 === Suc(V 1))` THEN
  REWRITE_TAC[itlist spec_rule [`Suc(V 1)`; `Suc(V 0)`] le_def] THEN
  TRANS_TAC iff_trans `??2 (V 0 ++ V 2 === V 1)` THEN
  GEN_REWRITE_TAC RAND_CONV [iff_sym] THEN
  REWRITE_TAC[itlist spec_rule [`V 1`; `V 0`] le_def] THEN
  MATCH_MP_TAC exiff THEN
  TRANS_TAC iff_trans `Suc(V 0 ++ V 2) === Suc(V 1)` THEN
  REWRITE_TAC[suc_inj_eq] THEN MATCH_MP_TAC cong_eq THEN
  REWRITE_TAC[axiom_eqrefl; add_suc']);;

let le_iff_lt = prove
 (`!s t. {robinson} |-- s <<= t <-> s << Suc t`,
  REPEAT GEN_TAC THEN TRANS_TAC iff_trans `Suc s <<= Suc t` THEN
  ONCE_REWRITE_TAC[iff_sym] THEN
  REWRITE_TAC[suc_le_eq; lt_def']);;

let suc_lt_eq = prove
 (`!s t. {robinson} |-- Suc s << Suc t <-> s << t`,
  MESON_TAC[iff_sym; iff_trans; le_iff_lt; lt_def']);;

let not_suc_eq_0 = prove
 (`!t. {robinson} |-- Suc t === Z --> False`,
  gen_tac 1 THEN
  SUBGOAL_THEN `{robinson} |-- Not(Suc(V 1) === Z)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[canonize_clauses]] THEN
  SUBGOAL_THEN `{robinson} |-- ?? 0 (Suc(V 1) === Suc(V 0))` MP_TAC THENL
   [MATCH_MP_TAC exists_intro THEN EXISTS_TAC `V 1` THEN
    CONV_TAC(RAND_CONV FORMSUBST_CONV) THEN REWRITE_TAC[axiom_eqrefl];
    MESON_TAC[iff_imp2; modusponens; spec_rule `Suc(V 1)` num_cases]]);;

let not_suc_le_0 = prove
 (`!t. {robinson} |-- Suc t <<= Z --> False`,
  X_GEN_TAC `s:term` THEN
  SUBGOAL_THEN `{robinson} |-- !!0 (Suc(V 0) <<= Z --> False)` MP_TAC THENL
   [ALL_TAC; DISCH_THEN(ACCEPT_TAC o spec_rule `s:term`)] THEN
  MATCH_MP_TAC gen THEN
  SUBGOAL_THEN `{robinson} |-- ?? 2 (Suc (V 0) ++ V 2 === Z) --> False`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] imp_trans) THEN
    MATCH_MP_TAC iff_imp1 THEN
    ACCEPT_TAC(itlist spec_rule [`Z`; `Suc(V 0)`] le_def)] THEN
  MATCH_MP_TAC ichoose THEN REWRITE_TAC[FV; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC gen THEN TRANS_TAC imp_trans `Suc(V 0 ++ V 2) === Z` THEN
  REWRITE_TAC[not_suc_eq_0] THEN MATCH_MP_TAC iff_imp1 THEN
  MATCH_MP_TAC cong_eq THEN REWRITE_TAC[axiom_eqrefl] THEN
  REWRITE_TAC[add_suc']);;

let not_lt_0 = prove
 (`!t. {robinson} |-- t << Z --> False`,
  MESON_TAC[not_suc_le_0; lt_def'; imp_trans; iff_imp1]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation of atoms built from numerals by proof.                         *)
(* ------------------------------------------------------------------------- *)

let add_0_right = prove
 (`!n. {robinson} |-- numeral n ++ Z === numeral n`,
  GEN_TAC THEN MP_TAC(ISPECL [`n:num`; `0`] SIGMA1_COMPLETE_ADD) THEN
  REWRITE_TAC[numeral; ADD_CLAUSES]);;

let ATOM_EQ_FALSE = prove
 (`!m n. ~(m = n) ==> {robinson} |-- numeral m === numeral n --> False`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MESON_TAC[eq_sym; imp_trans]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN INDUCT_TAC THEN
  REWRITE_TAC[numeral; not_suc_eq_0; LT_SUC; SUC_INJ] THEN
  ASM_MESON_TAC[suc_inj_eq; imp_trans; iff_imp1; iff_imp2]);;

let ATOM_LE_FALSE = prove
 (`!m n. n < m ==> {robinson} |-- numeral m <<= numeral n --> False`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[numeral; not_suc_le_0; LT_SUC] THEN
  ASM_MESON_TAC[suc_le_eq; imp_trans; iff_imp1; iff_imp2]);;

let ATOM_LT_FALSE = prove
 (`!m n. n <= m ==> {robinson} |-- numeral m << numeral n --> False`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LT_SUC_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ATOM_LE_FALSE) THEN
  REWRITE_TAC[numeral] THEN
  ASM_MESON_TAC[lt_def'; imp_trans; iff_imp1; iff_imp2]);;

let ATOM_EQ_TRUE = prove
 (`!m n. m = n ==> {robinson} |-- numeral m === numeral n`,
  MESON_TAC[axiom_eqrefl]);;

let ATOM_LE_TRUE = prove
 (`!m n. m <= n ==> {robinson} |-- numeral m <<= numeral n`,
  SUBGOAL_THEN `!m n. {robinson} |-- numeral m <<= numeral(m + n)`
  MP_TAC THENL [ALL_TAC; MESON_TAC[LE_EXISTS]] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC modusponens THEN
  EXISTS_TAC `?? 2 (numeral m ++ V 2 === numeral(m + n))` THEN
  CONJ_TAC THENL
   [MP_TAC(itlist spec_rule [`numeral(m + n)`; `numeral m`] le_def) THEN
    MESON_TAC[iff_imp2];
    MATCH_MP_TAC exists_intro THEN EXISTS_TAC `numeral n` THEN
    CONV_TAC(RAND_CONV FORMSUBST_CONV) THEN
    REWRITE_TAC[SIGMA1_COMPLETE_ADD]]);;

let ATOM_LT_TRUE = prove
 (`!m n. m < n ==> {robinson} |-- numeral m << numeral n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LE_SUC_LT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ATOM_LE_TRUE) THEN
  REWRITE_TAC[numeral] THEN
  ASM_MESON_TAC[lt_def'; modusponens; iff_imp1; iff_imp2]);;

(* ------------------------------------------------------------------------- *)
(* A kind of case analysis rule; might make it induction in case of PA.      *)
(* ------------------------------------------------------------------------- *)

let FORMSUBST_FORMSUBST_SAME_NONE = prove
 (`!s t x p.
        FVT t = {x} /\ FVT s = {}
        ==> formsubst (x |=> s) (formsubst (x |=> t) p) =
            formsubst (x |=> termsubst (x |=> s) t) p`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. safe_for y (x |=> termsubst (x |=> s) t)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[SAFE_FOR_ASSIGN; TERMSUBST_FVT; ASSIGN] THEN
    ASM SET_TAC[FVT];
    ALL_TAC] THEN
  MATCH_MP_TAC form_INDUCT THEN
  ASM_SIMP_TAC[FORMSUBST_SAFE_FOR; SAFE_FOR_ASSIGN; IN_SING; NOT_IN_EMPTY] THEN
  SIMP_TAC[formsubst] THEN
  MATCH_MP_TAC(TAUT `(p /\ q /\ r) /\ s ==> p /\ q /\ r /\ s`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[TERMSUBST_TERMSUBST] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[o_DEF; FUN_EQ_THM] THEN X_GEN_TAC `y:num` THEN
    REWRITE_TAC[ASSIGN] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[termsubst; ASSIGN];
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`y:num`; `p:form`] THEN DISCH_TAC THEN
    (ASM_CASES_TAC `y:num = x` THENL
     [ASM_REWRITE_TAC[assign; VALMOD_VALMOD_BASIC] THEN
      SIMP_TAC[VALMOD_TRIVIAL; FORMSUBST_TRIV];
      SUBGOAL_THEN `!u. (y |-> V y) (x |=> u) = (x |=> u)`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      GEN_TAC THEN MATCH_MP_TAC VALMOD_TRIVIAL THEN
      ASM_REWRITE_TAC[ASSIGN]])]);;

let num_cases_rule = prove
 (`!p x. {robinson} |-- formsubst (x |=> Z) p /\
         {robinson} |-- formsubst (x |=> Suc(V x)) p
         ==> {robinson} |-- p`,
  let lemma = prove
   (`!A p x t. A |-- formsubst (x |=> t) p ==> A |-- V x === t --> p`,
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] modusponens) THEN
    MATCH_MP_TAC imp_swap THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM FORMSUBST_TRIV] THEN
    CONV_TAC(funpow 3 RAND_CONV(SUBS_CONV[SYM(SPEC `x:num` ASSIGN_TRIV)])) THEN
    TRANS_TAC imp_trans `t === V x` THEN REWRITE_TAC[isubst; eq_sym]) in
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM FORMSUBST_TRIV] THEN
  CONV_TAC(RAND_CONV(SUBS_CONV[SYM(SPEC `x:num` ASSIGN_TRIV)])) THEN
  SUBGOAL_THEN `?z. ~(z = x) /\ ~(z IN VARS p)` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `VARIANT(x INSERT VARS p)` THEN
    REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM IN_INSERT] THEN
    MATCH_MP_TAC NOT_IN_VARIANT THEN
    SIMP_TAC[VARS_FINITE; FINITE_INSERT; SUBSET_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
   ONCE_REWRITE_TAC[GSYM(MATCH_MP FORMSUBST_TWICE th)]) THEN
  SUBGOAL_THEN `~(x IN FV(formsubst (x |=> V z) p))` MP_TAC THENL
   [REWRITE_TAC[FORMSUBST_FV; IN_ELIM_THM; ASSIGN; NOT_EXISTS_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FVT] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`formsubst (x |=> V z) p`,`p:form`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC spec THEN MATCH_MP_TAC gen THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP lemma) THEN
  DISCH_THEN(MP_TAC o SPEC `x:num` o MATCH_MP gen) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] ichoose)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP lemma) THEN ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ante_disj) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] modusponens) THEN
  MP_TAC(ISPECL [`V z`; `x:num`] num_cases') THEN
  ASM_REWRITE_TAC[FVT; IN_SING] THEN
  DISCH_THEN(MP_TAC o MATCH_MP iff_imp1) THEN
  REWRITE_TAC[canonize_clauses] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] imp_trans) THEN
  MESON_TAC[imp_swap; axiom_not; iff_imp1; imp_trans]);;

(* ------------------------------------------------------------------------- *)
(* Now full Sigma-1 completeness.                                            *)
(* ------------------------------------------------------------------------- *)

let SIGMAPI1_COMPLETE = prove
 (`!v p b. sigmapi b 1 p /\ closed p
           ==> (b /\ holds v p ==> {robinson} |-- p) /\
               (~b /\ ~holds v p ==> {robinson} |-- p --> False)`,
  let lemma1 = prove
   (`!x n p. (!m. m < n ==> {robinson} |-- formsubst (x |=> numeral m) p)
             ==> {robinson} |-- !!x (V x << numeral n --> p)`,
    GEN_TAC THEN INDUCT_TAC THEN X_GEN_TAC `p:form` THEN DISCH_TAC THEN
    REWRITE_TAC[numeral] THENL
     [ASM_MESON_TAC[gen; imp_trans; ex_falso; not_lt_0]; ALL_TAC] THEN
    MATCH_MP_TAC gen THEN MATCH_MP_TAC num_cases_rule THEN
    EXISTS_TAC `x:num`  THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[formsubst] THEN MATCH_MP_TAC add_assum THEN
      REWRITE_TAC[GSYM numeral] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[formsubst; termsubst; TERMSUBST_NUMERAL; ASSIGN] THEN
    TRANS_TAC imp_trans `V x << numeral n` THEN
    CONJ_TAC THENL [MESON_TAC[suc_lt_eq; iff_imp1]; ALL_TAC] THEN
    MATCH_MP_TAC spec_var THEN EXISTS_TAC `x:num` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
    ASM_REWRITE_TAC[LT_SUC] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (lhs o rand) FORMSUBST_FORMSUBST_SAME_NONE o
      rand o snd) THEN
    REWRITE_TAC[FVT; FVT_NUMERAL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[termsubst; ASSIGN; numeral]) in
  let lemma2 = prove
   (`!x n p. (!m. m <= n ==> {robinson} |-- formsubst (x |=> numeral m) p)
             ==> {robinson} |-- !!x (V x <<= numeral n --> p)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`x:num`; `SUC n`; `p:form`] lemma1) THEN
    ASM_REWRITE_TAC[LT_SUC_LE] THEN DISCH_TAC THEN MATCH_MP_TAC gen THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP spec_var) THEN REWRITE_TAC[numeral] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] imp_trans) THEN
    MESON_TAC[iff_imp1; le_iff_lt]) in
  let lemma3 = prove
   (`!v x t p.
          FVT t = {} /\
          (!m. m < termval v t
               ==> {robinson} |-- formsubst (x |=> numeral m) p)
          ==> {robinson} |-- !!x (V x << t --> p)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC gen THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP spec_var o MATCH_MP lemma1) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] imp_trans) THEN
    MATCH_MP_TAC iff_imp1 THEN MATCH_MP_TAC cong_lt THEN
    REWRITE_TAC[axiom_eqrefl] THEN MATCH_MP_TAC SIGMA1_COMPLETE_TERM THEN
    ASM_MESON_TAC[])
  and lemma4 = prove
   (`!v x t p.
          FVT t = {} /\
          (!m. m <= termval v t
               ==> {robinson} |-- formsubst (x |=> numeral m) p)
          ==> {robinson} |-- !!x (V x <<= t --> p)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC gen THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP spec_var o MATCH_MP lemma2) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] imp_trans) THEN
    MATCH_MP_TAC iff_imp1 THEN MATCH_MP_TAC cong_le THEN
    REWRITE_TAC[axiom_eqrefl] THEN MATCH_MP_TAC SIGMA1_COMPLETE_TERM THEN
    ASM_MESON_TAC[])
  and lemma5 = prove
   (`!A x p q. A |-- !!x (p --> Not q) ==> A |-- !!x (Not(p && q))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC gen THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP spec_var) THEN
    REWRITE_TAC[canonize_clauses] THEN
    MESON_TAC[imp_trans; axiom_not; iff_imp1; iff_imp2]) in
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[closed] THEN
  WF_INDUCT_TAC `complexity p` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[SIGMAPI_CLAUSES; complexity; ARITH] THEN
  REWRITE_TAC[MESON[] `(if p then q else F) <=> p /\ q`] THEN
  ONCE_REWRITE_TAC
   [TAUT `a /\ b /\ c /\ d /\ e /\ f /\ g /\ h /\ i /\ j /\ k /\ l <=>
       (a /\ b) /\ (c /\ d /\ e) /\ f /\ (g /\ h /\ i /\ j) /\ (k /\ l)`] THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[holds] THEN
    MESON_TAC[imp_refl; truth];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`s:term`; `t:term`] THEN
    DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `b:bool` THEN
    REWRITE_TAC[FV; EMPTY_UNION] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`v:num->num`; `t:term`; `termval v t`]
        SIGMA1_COMPLETE_TERM) THEN
    MP_TAC(ISPECL [`v:num->num`; `s:term`; `termval v s`]
        SIGMA1_COMPLETE_TERM) THEN
    ASM_REWRITE_TAC[IMP_IMP] THENL
     [DISCH_THEN(MP_TAC o MATCH_MP cong_eq);
      DISCH_THEN(MP_TAC o MATCH_MP cong_lt);
      DISCH_THEN(MP_TAC o MATCH_MP cong_le)] THEN
    STRIP_TAC THEN REWRITE_TAC[holds; NOT_LE; NOT_LT] THEN
    (REPEAT STRIP_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o
         MATCH_MP(REWRITE_RULE[IMP_CONJ] modusponens) o MATCH_MP iff_imp2);
       FIRST_X_ASSUM(MATCH_MP_TAC o
         MATCH_MP(REWRITE_RULE[IMP_CONJ] imp_trans) o MATCH_MP iff_imp1)]) THEN
    ASM_SIMP_TAC[ATOM_EQ_FALSE; ATOM_EQ_TRUE; ATOM_LT_FALSE; ATOM_LT_TRUE;
                 ATOM_LE_FALSE; ATOM_LE_TRUE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `p:form` THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `p:form`) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    X_GEN_TAC `b:bool` THEN REWRITE_TAC[FV] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `~b`) THEN ASM_REWRITE_TAC[holds] THEN
    BOOL_CASES_TAC `b:bool` THEN CANONIZE_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_TAC THEN  X_GEN_TAC `b:bool` THEN REWRITE_TAC[FV; EMPTY_UNION] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
     MP_TAC(SPEC `p:form` th) THEN MP_TAC(SPEC `q:form` th)) THEN
    (ANTS_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
    (ANTS_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[IMP_IMP]]) THEN
    ASM_REWRITE_TAC[holds; canonize_clauses] THENL
     [DISCH_THEN(CONJUNCTS_THEN(MP_TAC o SPEC `b:bool`));
      DISCH_THEN(CONJUNCTS_THEN(MP_TAC o SPEC `b:bool`));
      DISCH_THEN(CONJUNCTS_THEN2
       (MP_TAC o SPEC `~b`) (MP_TAC o SPEC `b:bool`));
      DISCH_THEN(CONJUNCTS_THEN(fun th ->
        MP_TAC(SPEC `~b` th) THEN MP_TAC(SPEC `b:bool` th)))] THEN
    ASM_REWRITE_TAC[] THEN BOOL_CASES_TAC `b:bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CANONIZE_TAC THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT
         `~(p <=> q) ==> (p /\ ~q ==> r) /\ (~p /\ q ==> s) ==> r \/ s`)) THEN
        REPEAT STRIP_TAC THEN CANONIZE_TAC) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`; `p:form`] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[canonize_clauses; holds] THEN
  DISCH_TAC THEN X_GEN_TAC `b:bool` THENL
   [BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; FV] THEN
      ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`q:form`; `t:term`] THEN DISCH_THEN
       (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC) ASSUME_TAC) THEN
      REWRITE_TAC[SIGMAPI_CLAUSES; FV; holds] THEN
      (ASM_CASES_TAC `FVT t = {}` THENL [ALL_TAC; ASM SET_TAC[]]) THEN
      (ASM_CASES_TAC `FV(q) SUBSET {x}` THENL [ALL_TAC; ASM SET_TAC[]]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2)) THEN
      ABBREV_TAC `n = termval v t` THEN
      ASM_SIMP_TAC[TERMVAL_VALMOD_OTHER; termval; VALMOD] THENL
       [DISCH_TAC THEN MATCH_MP_TAC lemma3;
        DISCH_TAC THEN MATCH_MP_TAC lemma4] THEN
      EXISTS_TAC `v:num->num` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `formsubst (x |=> numeral m) q`) THEN
      REWRITE_TAC[complexity; COMPLEXITY_FORMSUBST] THEN
      (ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `T`)]) THEN
      REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SIGMAPI_FORMSUBST] THEN
      REWRITE_TAC[FORMSUBST_FV; ASSIGN] THEN
      REPLICATE_TAC 2 (ONCE_REWRITE_TAC[COND_RAND]) THEN
      REWRITE_TAC[FVT_NUMERAL; NOT_IN_EMPTY; FVT; IN_SING] THEN
      (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[HOLDS_FORMSUBST] THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOLDS_VALUATION THEN
      X_GEN_TAC `y:num` THEN
      (ASM_CASES_TAC `y:num = x` THENL [ALL_TAC; ASM SET_TAC[]]) THEN
      ASM_REWRITE_TAC[o_DEF; ASSIGN; VALMOD; TERMVAL_NUMERAL];
      STRIP_TAC THEN REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC imp_trans THEN
      EXISTS_TAC `formsubst (x |=> numeral n) p` THEN REWRITE_TAC[ispec] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `formsubst (x |=> numeral n) p`) THEN
      REWRITE_TAC[COMPLEXITY_FORMSUBST; ARITH_RULE `n < n + 1`] THEN
      DISCH_THEN(MP_TAC o SPEC `F`) THEN
      ASM_SIMP_TAC[SIGMAPI_FORMSUBST; IMP_IMP] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `FV (!! x p) = {}` THEN
        REWRITE_TAC[FV; FORMSUBST_FV; SET_RULE
         `s DELETE a = {} <=> s = {} \/ s = {a}`] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[NOT_IN_EMPTY; IN_SING; EMPTY_GSPEC;
                        ASSIGN; UNWIND_THM2; FVT_NUMERAL];
        UNDISCH_TAC `~holds((x |-> n) v) p` THEN
        REWRITE_TAC[HOLDS_FORMSUBST; CONTRAPOS_THM] THEN
        MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOLDS_VALUATION THEN
        RULE_ASSUM_TAC(REWRITE_RULE[FV]) THEN X_GEN_TAC `y:num` THEN
        ASM_CASES_TAC `y:num = x` THENL [ALL_TAC; ASM SET_TAC[]] THEN
        ASM_REWRITE_TAC[o_THM; ASSIGN; VALMOD; TERMVAL_NUMERAL]]];
    BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[FV] THEN STRIP_TAC THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `formsubst (x |=> numeral n) (Not p)`) THEN
      REWRITE_TAC[COMPLEXITY_FORMSUBST; complexity] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `F`)] THEN
      ASM_SIMP_TAC[IMP_IMP; SIGMAPI_CLAUSES; SIGMAPI_FORMSUBST] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FORMSUBST_FV; ASSIGN] THEN
        REPLICATE_TAC 2 (ONCE_REWRITE_TAC[COND_RAND]) THEN
        REWRITE_TAC[FVT_NUMERAL; NOT_IN_EMPTY; FVT; FV; IN_SING] THEN
        (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
        UNDISCH_TAC `holds ((x |-> n) v) p` THEN
        REWRITE_TAC[formsubst; holds; HOLDS_FORMSUBST] THEN
        MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOLDS_VALUATION THEN
        RULE_ASSUM_TAC(REWRITE_RULE[FV]) THEN X_GEN_TAC `y:num` THEN
        ASM_CASES_TAC `y:num = x` THENL [ALL_TAC; ASM SET_TAC[]] THEN
        ASM_REWRITE_TAC[o_THM; ASSIGN; VALMOD; TERMVAL_NUMERAL];
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] imp_trans) THEN
        REWRITE_TAC[ispec]];
      REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; FV] THEN
      ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`q:form`; `t:term`] THEN DISCH_THEN
       (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC) ASSUME_TAC) THEN
      REWRITE_TAC[SIGMAPI_CLAUSES; FV; holds] THEN
      (ASM_CASES_TAC `FVT t = {}` THENL [ALL_TAC; ASM SET_TAC[]]) THEN
      (ASM_CASES_TAC `FV(q) SUBSET {x}` THENL [ALL_TAC; ASM SET_TAC[]]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2)) THEN
      ABBREV_TAC `n = termval v t` THEN
      ASM_SIMP_TAC[TERMVAL_VALMOD_OTHER; termval; VALMOD] THEN
      REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
      DISCH_TAC THEN MATCH_MP_TAC lemma5 THENL
       [MATCH_MP_TAC lemma3; MATCH_MP_TAC lemma4] THEN
      EXISTS_TAC `v:num->num` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `formsubst (x |=> numeral m) (Not q)`) THEN
      REWRITE_TAC[complexity; COMPLEXITY_FORMSUBST] THEN
      (ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `T`)]) THEN
      REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SIGMAPI_FORMSUBST; SIGMAPI_CLAUSES] THEN
      REWRITE_TAC[FORMSUBST_FV; FV; ASSIGN] THEN
      REPLICATE_TAC 2 (ONCE_REWRITE_TAC[COND_RAND]) THEN
      REWRITE_TAC[FVT_NUMERAL; NOT_IN_EMPTY; FVT; IN_SING] THEN
      (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[HOLDS_FORMSUBST; holds; CONTRAPOS_THM] THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOLDS_VALUATION THEN
      X_GEN_TAC `y:num` THEN
      (ASM_CASES_TAC `y:num = x` THENL [ALL_TAC; ASM SET_TAC[]]) THEN
      ASM_REWRITE_TAC[o_DEF; ASSIGN; VALMOD; TERMVAL_NUMERAL]]]);;

(* ------------------------------------------------------------------------- *)
(* Hence a nice alternative form of Goedel's theorem for any consistent      *)
(* sigma_1-definable axioms A that extend (i.e. prove) the Robinson axioms.  *)
(* ------------------------------------------------------------------------- *)

let G1_ROBINSON = prove
 (`!A. definable_by (SIGMA 1) (IMAGE gform A) /\
       consistent A /\ A |-- robinson
       ==> ?G. PI 1 G /\
               closed G /\
               true G /\
               ~(A |-- G) /\
               (sound_for (SIGMA 1 INTER closed) A ==> ~(A |-- Not G))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC G1_TRAD THEN
  ASM_REWRITE_TAC[complete_for; INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `p:form` THEN REWRITE_TAC[IN; true_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC modusponens THEN EXISTS_TAC `robinson` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROVES_MONO THEN
  EXISTS_TAC `{}:form->bool` THEN REWRITE_TAC[EMPTY_SUBSET] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) DEDUCTION o snd) THEN
  MP_TAC(ISPECL [`I:num->num`; `p:form`; `T`] SIGMAPI1_COMPLETE) THEN
  ASM_REWRITE_TAC[GSYM SIGMA] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[robinson; closed; FV; FVT] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More metaproperties of axioms systems now we have some derived rules.     *)
(* ------------------------------------------------------------------------- *)

let complete = new_definition
  `complete A <=> !p. closed p ==> A |-- p \/ A |-- Not p`;;

let sound = new_definition
  `sound A <=> !p. A |-- p ==> true p`;;

let semcomplete = new_definition
  `semcomplete A <=> !p. true p ==> A |-- p`;;

let generalize = new_definition
  `generalize vs p = ITLIST (!!) vs p`;;

let closure = new_definition
  `closure p = generalize (list_of_set(FV p)) p`;;

let TRUE_GENERALIZE = prove
 (`!vs p. true(generalize vs p) <=> true p`,
  REWRITE_TAC[generalize; true_def] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; holds] THEN GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MESON_TAC[VALMOD_REPEAT]);;

let PROVABLE_GENERALIZE = prove
 (`!A p vs. A |-- generalize vs p <=> A |-- p`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[generalize] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MESON_TAC[spec; gen; FORMSUBST_TRIV; ASSIGN_TRIV]);;

let FV_GENERALIZE = prove
 (`!p vs. FV(generalize vs p) = FV(p) DIFF (set_of_list vs)`,
  GEN_TAC THEN REWRITE_TAC[generalize] THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[set_of_list; DIFF_EMPTY; ITLIST] THEN
   ASM_REWRITE_TAC[FV] THEN SET_TAC[]);;

let CLOSED_CLOSURE = prove
 (`!p. closed(closure p)`,
  REWRITE_TAC[closed; closure; FV_GENERALIZE] THEN
  SIMP_TAC[SET_OF_LIST_OF_SET; FV_FINITE; DIFF_EQ_EMPTY]);;

let TRUE_CLOSURE = prove
 (`!p. true(closure p) <=> true p`,
  REWRITE_TAC[closure; TRUE_GENERALIZE]);;

let PROVABLE_CLOSURE = prove
 (`!A p. A |-- closure p <=> A |-- p`,
  REWRITE_TAC[closure; PROVABLE_GENERALIZE]);;

let DEFINABLE_DEFINABLE_BY = prove
 (`definable = definable_by (\x. T)`,
  REWRITE_TAC[FUN_EQ_THM; definable; definable_by]);;

let DEFINABLE_ONEVAR = prove
 (`definable s <=> ?p x. (FV p = {x}) /\ !v. holds v p <=> (v x) IN s`,
  REWRITE_TAC[definable] THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:form` (X_CHOOSE_TAC `x:num`)) THEN
  EXISTS_TAC `(V x === V x) && formsubst (\y. if y = x then V x else Z) p` THEN
  EXISTS_TAC `x:num` THEN
  ASM_REWRITE_TAC[HOLDS_FORMSUBST; FORMSUBST_FV; FV; holds] THEN
  REWRITE_TAC[COND_RAND; EXTENSION; IN_ELIM_THM; IN_SING; FVT; IN_UNION;
              COND_EXPAND; NOT_IN_EMPTY; o_THM; termval] THEN
  MESON_TAC[]);;

let CLOSED_TRUE_OR_FALSE = prove
 (`!p. closed p ==> true p \/ true(Not p)`,
  REWRITE_TAC[closed; true_def; holds] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[HOLDS_VALUATION; NOT_IN_EMPTY]);;

let SEMCOMPLETE_IMP_COMPLETE = prove
 (`!A. semcomplete A ==> complete A`,
  REWRITE_TAC[semcomplete; complete] THEN MESON_TAC[CLOSED_TRUE_OR_FALSE]);;

let SOUND_CLOSED = prove
 (`sound A <=> !p. closed p /\ A |-- p ==> true p`,
  REWRITE_TAC[sound] THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MESON_TAC[TRUE_CLOSURE; PROVABLE_CLOSURE; CLOSED_CLOSURE]);;

let SOUND_IMP_CONSISTENT = prove
 (`!A. sound A ==> consistent A`,
  REWRITE_TAC[sound; consistent; CONSISTENT_ALT] THEN
  SUBGOAL_THEN `~(true False)` (fun th -> MESON_TAC[th]) THEN
  REWRITE_TAC[true_def; holds]);;

let SEMCOMPLETE_SOUND_EQ_CONSISTENT = prove
 (`!A. semcomplete A ==> (sound A <=> consistent A)`,
  REWRITE_TAC[semcomplete] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[SOUND_IMP_CONSISTENT] THEN
  REWRITE_TAC[consistent; SOUND_CLOSED] THEN
  ASM_MESON_TAC[CLOSED_TRUE_OR_FALSE]);;
