(* ========================================================================= *)
(* Linear refutations.                                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Some clause-preservation lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let RESOLVE_CLAUSE = prove
 (`!c1 c2 p. clause c1 /\ clause c2 ==> clause(resolve p c1 c2)`,
  REWRITE_TAC[clause; resolve; FINITE_UNION; IN_UNION; IN_DELETE] THEN
  MESON_TAC[DELETE_SUBSET; FINITE_SUBSET]);;

let PRESPROOF_CLAUSE = prove
 (`!hyps cl. (!c. c IN hyps ==> clause c) /\ presproof hyps cl ==> clause cl`,
  REWRITE_TAC[IMP_CONJ] THEN
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC presproof_INDUCT THEN ASM_MESON_TAC[RESOLVE_CLAUSE]);;

let RESOLVE_MONO = prove
 (`!c1 c2 c1' c2' p.
        c1 SUBSET c1' /\ c2 SUBSET c2'
        ==> (resolve p c1 c2) SUBSET (resolve p c1' c2')`,
  REWRITE_TAC[SUBSET; resolve; IN_UNION; IN_DELETE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More refined provability predicate, tracking participating hypotheses.    *)
(* ------------------------------------------------------------------------- *)

let ppresproof_RULES,ppresproof_INDUCT,ppresproof_CASES =
  new_inductive_definition
   `(!c. clause(c) ==> ppresproof {c} c) /\
    (!p asm1 asm2 c1 c2.
            ppresproof asm1 c1 /\ ppresproof asm2 c2 /\
            p IN c1 /\ ~~ p IN c2
                ==> ppresproof (asm1 UNION asm2) (resolve p c1 c2))`;;

let PPRESPROOF = prove
 (`!hyps. (!c. c IN hyps ==> clause c)
          ==> !c. presproof hyps c <=>
                        ?asm. asm SUBSET hyps /\ ppresproof asm c`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`c:form->bool`,`c:form->bool`) THEN
    MATCH_MP_TAC presproof_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC `c:form->bool` THEN DISCH_TAC THEN
      EXISTS_TAC `{c:form->bool}` THEN
      ASM_SIMP_TAC[ppresproof_RULES] THEN
      UNDISCH_TAC `c:form->bool IN hyps` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[ppresproof_RULES; IN_UNION];
    DISCH_THEN(X_CHOOSE_THEN `asm:(form->bool)->bool` MP_TAC) THEN
    ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
    MAP_EVERY (fun s -> SPEC_TAC(s,s))
     [`c:form->bool`; `asm:(form->bool)->bool`] THEN
    MATCH_MP_TAC ppresproof_INDUCT THEN
    REWRITE_TAC[SUBSET; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
    MESON_TAC[presproof_RULES]]);;

let PPRESPROOF_CLAUSE = prove
 (`!asm cl. ppresproof asm cl ==> clause cl /\ (!c. c IN asm ==> clause c)`,
  MATCH_MP_TAC ppresproof_INDUCT THEN SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[IN_UNION; RESOLVE_CLAUSE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A kind of soundness used later to pick the set-of-support.                *)
(* ------------------------------------------------------------------------- *)

let PPRESPROOF_CONSEQUENCE = prove
 (`!asm cl. ppresproof asm cl
            ==> !d. d psatisfies (IMAGE interp asm) ==> pholds d (interp cl)`,
  SUBGOAL_THEN
   `!asm cl. ppresproof asm cl
            ==> !d. (!c. c IN asm ==> ?p. p IN c /\ pholds d p)
                    ==> ?p. p IN cl /\ pholds d p`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    ASM_CASES_TAC `ppresproof asm cl` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[psatisfies] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    SIMP_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    ASM_MESON_TAC[PHOLDS_INTERP; clause; PPRESPROOF_CLAUSE]] THEN
  MATCH_MP_TAC ppresproof_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE; IN_INSERT; NOT_IN_EMPTY; psatisfies; IN_ELIM_THM] THEN
    MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`p:form`; `asm1:(form->bool)->bool`; `asm2:(form->bool)->bool`;
    `c1:form->bool`; `c2:form->bool`] THEN
  REWRITE_TAC[IMAGE_UNION] THEN
  REWRITE_TAC[psatisfies; IN_UNION] THEN
  DISCH_THEN(fun th -> GEN_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[CONJ_ASSOC; AND_FORALL_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `d:form->bool`) MP_TAC) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `q:form` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `r:form` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[resolve; IN_UNION; IN_DELETE] THEN
  ASM_MESON_TAC[PHOLDS_NEGATE]);;

let PPRESPROOF_SOUND = prove
 (`!asm. ppresproof asm {} ==> ~(psatisfiable (IMAGE interp asm))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PPRESPROOF_CONSEQUENCE) THEN
  REWRITE_TAC[psatisfiable] THEN
  SIMP_TAC[PHOLDS_INTERP; FINITE_RULES; NOT_IN_EMPTY] THEN
  REWRITE_TAC[psatisfies] THEN MESON_TAC[]);;

let PPRESPROOF_ALLNEGATIVE = prove
 (`!asm. ppresproof asm {} ==> ?c. c IN asm /\ !p. p IN c ==> negative p`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PPRESPROOF_SOUND) THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[psatisfiable] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  EXISTS_TAC `\x:form. T` THEN
  SIMP_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN X_GEN_TAC `c:form->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE(c:form->bool)`
   (fun th -> SIMP_TAC[th; PHOLDS_INTERP])
  THENL [ASM_MESON_TAC[PPRESPROOF_CLAUSE; clause]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:form->bool`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:form` THEN
  SIMP_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `literal q` MP_TAC THENL
   [ASM_MESON_TAC[PPRESPROOF_CLAUSE; clause]; ALL_TAC] THEN
  REWRITE_TAC[literal; ATOM] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `~(negative q)` THEN
  ASM_REWRITE_TAC[pholds] THEN
  REWRITE_TAC[negative; Not_DEF; form_INJ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Linear propositional proof.                                               *)
(* ------------------------------------------------------------------------- *)

let lpresproof_RULES,lpresproof_INDUCT,lpresproof_CASES =
  new_inductive_definition
   `(!cl. cl IN hyps ==> lpresproof hyps [cl]) /\
    (!c1 c2 lis p.
        lpresproof hyps (CONS c1 lis) /\
        (c2 IN hyps \/ MEM c2 lis) /\
        p IN c1 /\ ~~p IN c2
        ==> lpresproof hyps (CONS (resolve p c1 c2) (CONS c1 lis)))`;;

let LPRESPROOF_MONO = prove
 (`!hyps hyps' c.
        hyps SUBSET hyps' /\ lpresproof hyps c ==> lpresproof hyps' c`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`c:(form->bool)list`,`c:(form->bool)list`) THEN
  MATCH_MP_TAC lpresproof_INDUCT THEN
  ASM_MESON_TAC[lpresproof_RULES; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Resolution where one argument is a tautology.                             *)
(* ------------------------------------------------------------------------- *)

let RESOLVE_SYM = prove
 (`!c1 c2 p. literal p ==> (resolve (~~p) c1 c2 = resolve p c2 c1)`,
  SIMP_TAC[resolve; NEGATE_NEGATE; UNION_ACI]);;

let RESOLVE_TAUT_L = prove
 (`!c1 c2 p. clause c1 /\ tautologous c1
             ==> tautologous(resolve p c1 c2) \/ c2 SUBSET (resolve p c1 c2)`,
  REWRITE_TAC[tautologous; SUBSET; resolve; IN_DELETE; IN_UNION; clause] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:form` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(p = q) \/ (p = ~~q)` THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC); ALL_TAC] THEN
  ASM_MESON_TAC[NEGATE_REFL; NEGATE_NEGATE]);;

let RESOLVE_TAUT_R = prove
 (`!c1 c2 p. clause c2 /\ tautologous c2 /\ literal p
             ==> tautologous(resolve p c1 c2) \/ c1 SUBSET (resolve p c1 c2)`,
  REWRITE_TAC[tautologous; SUBSET; resolve; IN_DELETE; IN_UNION; clause] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:form` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(p = q) \/ (p = ~~q)` THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC); ALL_TAC] THEN
  ASM_MESON_TAC[NEGATE_REFL; NEGATE_NEGATE]);;

let SUBSET_TAUT = prove
 (`!c1 c2. tautologous c1 /\ c1 SUBSET c2 ==> tautologous c2`,
  REWRITE_TAC[tautologous; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary concept about preserving the branch.                            *)
(* ------------------------------------------------------------------------- *)

let suffix = new_recursive_definition list_RECURSION
  `(suffix lis [] <=> (lis = [])) /\
   (suffix lis (CONS s cs) <=> (lis = CONS s cs) \/ suffix lis cs)`;;

let SUFFIX_REFL = prove
 (`!lis. suffix lis lis`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[suffix]);;

let SUFFIX_BUTLAST = prove
 (`!l1 l2. suffix l1 l2 /\ ~(l1 = []) ==> (LAST l1 :A = LAST l2)`,
  GEN_TAC THEN ASM_CASES_TAC `l1:(A)list = []` THEN ASM_REWRITE_TAC[] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[suffix; LAST] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[LAST] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[suffix]);;

let SUFFIX_TRANS = prove
 (`!l1 l2 l3. suffix l1 l2 /\ suffix l2 l3 ==> suffix l1 l3`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[suffix] THEN
  ASM_MESON_TAC[suffix]);;

let SUFFIX_MEM = prove
 (`!x:A l lis. suffix (CONS x l) lis ==> MEM x lis`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; suffix; NOT_CONS_NIL; CONS_11] THEN ASM_MESON_TAC[]);;

let SUFFIX_CONS = prove
 (`!x l1 l2. suffix l1 l2 ==> suffix l1 (CONS x l2)`,
  MESON_TAC[suffix]);;

let SUFFIX_LENGTH = prove
 (`!l1 l2. suffix l1 l2 ==> LENGTH l1 <= LENGTH l2`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[suffix; LENGTH; NOT_CONS_NIL; LE_0] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH; LE_SUC; LE_REFL] THEN
  ASM_MESON_TAC[ARITH_RULE `x <= y ==> x <= SUC y`]);;

let NOT_SUFFIX_TAIL = prove
 (`!x l. ~(suffix (CONS x l) l)`,
  MESON_TAC[SUFFIX_LENGTH; LENGTH; ARITH_RULE `~(SUC n <= n)`]);;

let SUFFIX_ANTISYM = prove
 (`!l1 l2. suffix l1 l2 /\ suffix l2 l1 ==> (l1 = l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[suffix; NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[NOT_SUFFIX_TAIL; SUFFIX_TRANS; SUFFIX_CONS]);;

(* ------------------------------------------------------------------------- *)
(* Main linearization theorem.                                               *)
(* ------------------------------------------------------------------------- *)

let NEGATE_LITERAL = prove
 (`!q. literal q ==> literal(~~q)`,
  REWRITE_TAC[literal; ATOM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[ATOM; NEGATE_ATOM; NEGATE_NEG]);;

let SYMMETRY_LEMMA_1 = prove
  (`(!q basm B casm C c.
        literal q
        ==> (P q basm B casm C c = P (~~q) casm C basm B c)) /\
    (!q basm B casm C. literal q
        ==> (Q q basm B casm C = Q (~~q) casm C basm B)) /\
    (!q basm B casm C.
        Q q basm B casm C
        ==> literal q ==> !c. c IN basm ==> P q basm B casm C c)
    ==> !q basm B casm C.
        Q q basm B casm C
        ==> literal q ==> !c. c IN basm UNION casm ==> P q basm B casm C c`,
  REWRITE_TAC[IN_UNION] THEN MESON_TAC[NEGATE_LITERAL; NEGATE_NEGATE]);;

let SYMMETRY_LEMMA_2 = prove
  (`(!p q basm B casm C main aasm A.
        literal q
        ==> (P p q basm B casm C main aasm A =
             P p (~~q) casm C basm B main aasm A)) /\
    (!p q basm B casm C main aasm A.
        ~~p IN B ==> literal q ==> P p q basm B casm C main aasm A)
    ==> !p q basm B casm C main aasm A.
            ~~p IN B \/ ~~p IN C ==> literal q
            ==> P p q basm B casm C main aasm A`,
  REWRITE_TAC[IN_UNION] THEN MESON_TAC[NEGATE_LITERAL; NEGATE_NEGATE]);;

let LINEARIZATION = prove
 (`!asm cl. ppresproof asm cl
            ==> !c. c IN asm
                    ==> ?cl' lis. lpresproof asm (CONS cl' lis) /\
                                  cl' SUBSET cl /\
                                  (LAST (CONS cl' lis) = c)`,
  SUBGOAL_THEN
   `!asm cl. ppresproof asm cl
             ==> (!c. c IN asm ==> clause c) /\ clause cl /\
                 (!c. c IN asm
                      ==> ?cl' lis. lpresproof asm (CONS cl' lis) /\
                                    cl' SUBSET cl /\
                                    (LAST (CONS cl' lis) = c)) /\
                 (!c lis p asm'.
                        clause c /\
                        lpresproof asm' (CONS c lis) /\ p IN c /\ ~~p IN cl
                        ==> ?c' lis'. suffix (CONS c lis) (CONS c' lis') /\
                                      lpresproof (asm UNION asm')
                                                 (CONS c' lis') /\
                                      c' SUBSET (resolve p c cl))`
   (fun th -> SIMP_TAC[th]) THEN
  MATCH_MP_TAC ppresproof_INDUCT THEN CONJ_TAC THENL
   [X_GEN_TAC `cl:form->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      MAP_EVERY EXISTS_TAC [`cl:form->bool`; `[]:(form->bool)list`] THEN
      REWRITE_TAC[LAST; SUBSET_REFL] THEN
      SIMP_TAC[lpresproof_RULES; IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC
     [`c:form->bool`; `lis:(form->bool)list`; `p:form`;
      `hyp:(form->bool)->bool`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`resolve p c cl`; `CONS (c:form->bool) lis`] THEN
    REWRITE_TAC[SUBSET_REFL; suffix; SUFFIX_REFL] THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC_ALL lpresproof_RULES)) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_INSERT] THEN
    ASM_MESON_TAC[IN_UNION; SUBSET; LPRESPROOF_MONO]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`q:form`; `basm:(form->bool)->bool`; `casm:(form->bool)->bool`;
    `B:form->bool`; `C:form->bool`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[RESOLVE_CLAUSE] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_UNION];
    ASM_SIMP_TAC[RESOLVE_CLAUSE] THEN
    SUBGOAL_THEN `literal q` MP_TAC THENL [ASM_MESON_TAC[clause]; ALL_TAC] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    MAP_EVERY (fun s -> SPEC_TAC(s,s))
     [`C:form->bool`; `casm:(form->bool)->bool`;
      `B:form->bool`; `basm:(form->bool)->bool`; `q:form`] THEN
    MATCH_MP_TAC SYMMETRY_LEMMA_1 THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[resolve; NEGATE_NEGATE; UNION_ACI];
      SIMP_TAC[CONJ_ACI; NEGATE_NEGATE];
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_TAC THEN X_GEN_TAC `c:form->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!c. c IN basm
           ==> (?cl' lis.
                    lpresproof basm (CONS cl' lis) /\
                    cl' SUBSET B /\
                    (LAST (CONS cl' lis) = c))` THEN
    DISCH_THEN(MP_TAC o SPEC `c:form->bool`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`B1:form->bool`; `main:(form->bool)list`] THEN
    STRIP_TAC THEN ASM_CASES_TAC `q:form IN B1` THENL
     [UNDISCH_TAC
       `!c lis p asm'.
           clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN C
           ==> (?c' lis'.
                    suffix (CONS c lis) (CONS c' lis') /\
                    lpresproof (casm UNION asm') (CONS c' lis') /\
                    c' SUBSET resolve p c C)` THEN
      DISCH_THEN(MP_TAC o SPECL
       [`B1:form->bool`; `main:(form->bool)list`; `q:form`;
        `basm:(form->bool)->bool`]) THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[CLAUSE_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `D:form->bool` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `final:(form->bool)list` THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[RESOLVE_MONO; SUBSET_TRANS; SUBSET_REFL];
        ASM_MESON_TAC[SUFFIX_BUTLAST; NOT_CONS_NIL]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`B1:form->bool`; `main:(form->bool)list`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[LPRESPROOF_MONO; IN_UNION; SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `B1:(form->bool) SUBSET B` THEN
    UNDISCH_TAC `~(q:form IN B1)` THEN
    REWRITE_TAC[resolve; SUBSET; IN_UNION; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`A:form->bool`; `main:(form->bool)list`;
                       `p:form`; `aasm:(form->bool)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~~p IN B \/ ~~p IN C`
   (fun th1 ->
      SUBGOAL_THEN `literal q`
        (fun th2 -> POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
                    MP_TAC th2 THEN MP_TAC th1)
      THENL [ASM_MESON_TAC[clause]; ALL_TAC])
  THENL
   [UNDISCH_TAC `~~p IN resolve q B C` THEN
    REWRITE_TAC[resolve; IN_UNION; IN_DELETE] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun s -> SPEC_TAC(s,s))
    [`A:form->bool`; `aasm:(form->bool)->bool`; `main:(form->bool)list`;
     `C:form->bool`; `casm:(form->bool)->bool`;
     `B:form->bool`; `basm:(form->bool)->bool`; `q:form`; `p:form`] THEN
  MATCH_MP_TAC SYMMETRY_LEMMA_2 THEN CONJ_TAC THENL
   [SIMP_TAC[resolve; NEGATE_NEGATE] THEN
    REWRITE_TAC[UNION_ACI] THEN REWRITE_TAC[CONJ_ACI]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`p:form`; `q:form`; `basm:(form->bool)->bool`; `B:form->bool`;
    `casm:(form->bool)->bool`; `C:form->bool`; `main:(form->bool)list`;
    `aasm:(form->bool)->bool`; `A:form->bool`] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `p:form = q` THENL
   [UNDISCH_THEN `p:form = q` SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `!c lis p asm'.
           clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN C
           ==> (?c' lis'.
                    suffix (CONS c lis) (CONS c' lis') /\
                    lpresproof (casm UNION asm') (CONS c' lis') /\
                    c' SUBSET resolve p c C)` THEN
    DISCH_THEN(MP_TAC o SPECL
     [`A:form->bool`; `main:(form->bool)list`; `q:form`;
      `aasm:(form->bool)->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `D:form->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `final:(form->bool)list` THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC LPRESPROOF_MONO THEN
      EXISTS_TAC `casm:(form->bool)->bool UNION aasm` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNION] THEN
      GEN_TAC THEN CONV_TAC TAUT;
      SUBGOAL_THEN `C SUBSET (resolve q B C)` (fun th ->
        ASM_MESON_TAC[SUBSET_TRANS; RESOLVE_MONO; SUBSET_REFL; th]) THEN
      UNDISCH_TAC `~~q IN B` THEN
      REWRITE_TAC[SUBSET; resolve; IN_UNION; IN_DELETE] THEN
      MESON_TAC[NEGATE_REFL]]; ALL_TAC] THEN
  ASM_CASES_TAC `p = ~~q` THENL
   [UNDISCH_THEN `p = ~~q` SUBST_ALL_TAC THEN
    UNDISCH_TAC
      `!c lis p asm'.
           clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN B
           ==> (?c' lis'.
                    suffix (CONS c lis) (CONS c' lis') /\
                    lpresproof (basm UNION asm') (CONS c' lis') /\
                    c' SUBSET resolve p c B)` THEN
    DISCH_THEN(MP_TAC o SPECL
     [`A:form->bool`; `main:(form->bool)list`; `~~q`;
      `aasm:(form->bool)->bool`]) THEN
    SUBST_ALL_TAC(MATCH_MP NEGATE_NEGATE (ASSUME `literal q`)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `D:form->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `final:(form->bool)list` THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC LPRESPROOF_MONO THEN
      EXISTS_TAC `basm:(form->bool)->bool UNION aasm` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNION] THEN
      GEN_TAC THEN CONV_TAC TAUT;
      SUBGOAL_THEN `B SUBSET (resolve q B C)` (fun th ->
        ASM_MESON_TAC[SUBSET_TRANS; RESOLVE_MONO; SUBSET_REFL; th]) THEN
      SUBGOAL_THEN `q:form IN C` MP_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[SUBSET; resolve; IN_UNION; IN_DELETE] THEN
        MESON_TAC[NEGATE_REFL]] THEN
      UNDISCH_TAC `q IN resolve q B C` THEN
      REWRITE_TAC[resolve; IN_UNION; IN_DELETE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `!c lis p asm'.
           clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN B
           ==> (?c' lis'.
                    suffix (CONS c lis) (CONS c' lis') /\
                    lpresproof (basm UNION asm') (CONS c' lis') /\
                    c' SUBSET resolve p c B)` THEN
  DISCH_THEN(MP_TAC o SPECL
   [`A:form->bool`; `main:(form->bool)list`; `p:form`;
    `aasm:(form->bool)->bool`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`D:form->bool`; `middle:(form->bool)list`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?c' lis'.
       suffix (CONS D middle) (CONS c' lis') /\
       suffix (CONS A main) (CONS c' lis') /\
       lpresproof ((basm UNION casm) UNION aasm) (CONS c' lis') /\
       c' SUBSET resolve q (resolve p A B) C`
  MP_TAC THENL
   [ASM_CASES_TAC `q:form IN D` THENL
     [UNDISCH_TAC
       `!c lis p asm'.
               clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN C
               ==> (?c' lis'.
                        suffix (CONS c lis) (CONS c' lis') /\
                        lpresproof (casm UNION asm') (CONS c' lis') /\
                        c' SUBSET resolve p c C)` THEN
      DISCH_THEN(MP_TAC o SPECL
       [`D:form->bool`; `middle:(form->bool)list`;
        `q:form`; `basm:(form->bool)->bool UNION aasm`]) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[RESOLVE_CLAUSE; CLAUSE_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `E:form->bool` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `final:(form->bool)list` THEN
      SIMP_TAC[UNION_ACI] THEN REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[SUFFIX_TRANS]; ALL_TAC] THEN
      ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`D:form->bool`; `middle:(form->bool)list`] THEN
    ASM_REWRITE_TAC[SUFFIX_REFL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[LPRESPROOF_MONO; SUBSET; IN_UNION]; ALL_TAC] THEN
    UNDISCH_TAC `D SUBSET resolve p A B` THEN
    UNDISCH_TAC `~(q:form IN D)` THEN
    REWRITE_TAC[resolve; SUBSET; IN_UNION; IN_DELETE] THEN
    MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`E:form->bool`; `final:(form->bool)list`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `~~p IN E` THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`E:form->bool`; `final:(form->bool)list`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`E SUBSET resolve q (resolve p A B) C`;
      `~(~~ p IN E)`; `~(p = ~~ q)`; `~(p:form = q)`;
      `q:form IN B`; `~~q IN C`; `~~p IN resolve q B C`;
      `~~p IN B`] THEN
    REWRITE_TAC[resolve; IN_UNION; IN_DELETE; SUBSET] THEN
    MESON_TAC[]] THEN
  ASM_CASES_TAC `CONS (A:form->bool) main = CONS E final` THENL
   [ALL_TAC;
    EXISTS_TAC `resolve (~~p) E A` THEN
    EXISTS_TAC `CONS (E:form->bool) final` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[suffix];
      MATCH_MP_TAC(CONJUNCT2(SPEC_ALL lpresproof_RULES)) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISJ2_TAC THEN
        UNDISCH_TAC `suffix (CONS (A:form->bool) main) (CONS E final)` THEN
        ASM_REWRITE_TAC[suffix] THEN MESON_TAC[SUFFIX_MEM];
        SUBGOAL_THEN `~~(~~p) = p` (fun th -> ASM_REWRITE_TAC[th]) THEN
        MATCH_MP_TAC NEGATE_NEGATE THEN ASM_MESON_TAC[clause]];
      SUBGOAL_THEN `(~~(~~p) = p) /\ (~~(~~q) = q)` MP_TAC THENL
       [ASM_MESON_TAC[NEGATE_NEGATE; clause]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`~~ p IN E`;
        `E SUBSET resolve q (resolve p A B) C`;
        `~(p = ~~ q)`; `~(p:form = q)`; `q:form IN B`;
        `~~q IN C`; `p:form IN A`; `~~p IN resolve q B C`;
        `~~p IN B`] THEN
      REWRITE_TAC[resolve; IN_UNION; IN_DELETE; SUBSET] THEN
      MESON_TAC[]]] THEN
  UNDISCH_TAC `CONS (A:form->bool) main = CONS E final` THEN
  REWRITE_TAC[CONS_11] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `CONS (D:form->bool) middle = CONS A main` MP_TAC THENL
   [ASM_MESON_TAC[SUFFIX_ANTISYM]; ALL_TAC] THEN
  REWRITE_TAC[CONS_11] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  MAP_EVERY EXISTS_TAC [`A:form->bool`; `main:(form->bool)list`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `A SUBSET resolve p A B` THEN
  UNDISCH_TAC `A SUBSET resolve q (resolve p A B) C` THEN
  REWRITE_TAC[SUBSET; resolve; IN_UNION; IN_DELETE] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Linear resolution at the first order level.                               *)
(* ------------------------------------------------------------------------- *)

let lresproof_RULES,lresproof_INDUCT,lresproof_CASES =
  new_inductive_definition
   `(!cl. cl IN hyps ==> lresproof hyps [cl]) /\
    (!c1 c2 lis cl.
        lresproof hyps (CONS c1 lis) /\ (c2 IN hyps \/ MEM c2 lis) /\
        isaresolvent cl (c1,c2)
        ==> lresproof hyps (CONS cl (CONS c1 lis)))`;;

(* ------------------------------------------------------------------------- *)
(* Completeness of linear resolution.                                        *)
(* ------------------------------------------------------------------------- *)

let ALL2_BUTLAST = prove
 (`!P:(A->A->bool) l1 l2.
       ~(l1 = []) /\ ALL2 P l1 l2 ==> P (LAST l1) (LAST l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[LAST] THEN
  ASM_CASES_TAC `t:A list = []` THEN ASM_REWRITE_TAC[] THENL
   [SPEC_TAC(`t':A list`,`t':A list`) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; NOT_CONS_NIL];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `~(t:A list = [])` THEN
  SPEC_TAC(`t:A list`,`t:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; NOT_CONS_NIL]);;

let ALL2_MEM = prove
 (`!l1 l2. ALL2 P l1 l2 /\ MEM x l1 ==> ?y. MEM y l2 /\ P x y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; MEM] THEN ASM_MESON_TAC[]);;

let LRESPROOF_CLAUSE = prove
 (`!hyps. (!c. c IN hyps ==> clause c)
          ==> !lis. lresproof hyps lis ==> ALL clause lis`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC lresproof_INDUCT THEN
  REWRITE_TAC[ALL] THEN ASM_MESON_TAC[ISARESOLVENT_CLAUSE; ALL_MEM]);;

let LINEAR_RESOLUTION_COMPLETE = prove
 (`(!cl. cl IN hyps ==> clause cl) /\
   ~(?M:(term->bool)#(num->term list->term)#(num->term list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp hyps))
   ==> ?lis. lresproof hyps (CONS {} lis) /\
             (!p. p IN (LAST (CONS {} lis)) ==> negative p)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `IMAGE interp hyps` HERBRAND_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[QFREE_INTERP]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `~(psatisfiable
        {interp cl |
         cl IN {IMAGE(formsubst v) cl | cl,v | cl IN hyps}})`
  MP_TAC THENL
   [REWRITE_TAC[psatisfiable] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN
      MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> ~b`)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:form->bool` THEN
    REWRITE_TAC[psatisfies] THEN
    SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM;
             RIGHT_AND_EXISTS_THM; IN_IMAGE] THEN
    ASM_SIMP_TAC[PHOLDS_INTERP_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT]
                PRESPROOF_REFUTATION_COMPLETE)) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    ASM_SIMP_TAC[IMAGE_FORMSUBST_CLAUSE]; ALL_TAC] THEN
  MP_TAC(SPEC `{IMAGE (formsubst v) cl | cl,v | cl IN hyps}` PPRESPROOF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[IMAGE_FORMSUBST_CLAUSE]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `asm:(form->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PPRESPROOF_ALLNEGATIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sos:form->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEARIZATION) THEN
  DISCH_THEN(MP_TAC o SPEC `sos:form->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `emptyclause:form->bool` MP_TAC) THEN
  REWRITE_TAC[SUBSET_EMPTY] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `qlist:(form->bool)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!plis. lpresproof asm plis
           ==> ?lis. lresproof hyps lis /\ ALL2 (instance_of) plis lis`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `CONS {} (qlist:(form->bool)list)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL2] THEN
    MAP_EVERY X_GEN_TAC [`emp:form->bool`; `lis:(form->bool)list`] THEN
    DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN
    SUBGOAL_THEN `emp:form->bool = {}` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `{} instance_of emp` THEN
      REWRITE_TAC[instance_of; EXTENSION; IN_IMAGE; NOT_IN_EMPTY] THEN
      MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `lis:(form->bool)list` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:form` THEN
    SUBGOAL_THEN `sos instance_of (LAST (CONS {} lis))` MP_TAC THENL
     [EXPAND_TAC "sos" THEN MATCH_MP_TAC ALL2_BUTLAST THEN
      ASM_REWRITE_TAC[ALL2; NOT_CONS_NIL]; ALL_TAC] THEN
    REWRITE_TAC[instance_of] THEN
    DISCH_THEN(X_CHOOSE_THEN `jj:num->term` SUBST_ALL_TAC) THEN
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `formsubst jj p`) THEN
    REWRITE_TAC[NEGATIVE_FORMSUBST] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN
   `!plis. lpresproof asm plis
           ==> (!c. MEM c plis ==> clause c) /\
               ?lis. lresproof hyps lis /\ ALL2 (instance_of) plis lis`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC lpresproof_INDUCT THEN CONJ_TAC THENL
   [X_GEN_TAC `cl:form->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `clause cl` (fun th -> ASM_MESON_TAC[MEM; th]) THEN
      UNDISCH_TAC `asm SUBSET {IMAGE (formsubst v) cl | cl,v | cl IN hyps}` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `cl:form->bool`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
      ASM_MESON_TAC[IMAGE_FORMSUBST_CLAUSE]; ALL_TAC] THEN
    UNDISCH_TAC `asm SUBSET {IMAGE (formsubst v) cl | cl,v | cl IN hyps}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `cl:form->bool`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`cl0:form->bool`; `jj:num->term`] THEN
    STRIP_TAC THEN EXISTS_TAC `[cl0:form->bool]` THEN
    ASM_SIMP_TAC[lresproof_RULES; ALL2] THEN
    REWRITE_TAC[instance_of] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`A':form->bool`; `B':form->bool`; `lis':(form->bool)list`; `p:form`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `alist:(form->bool)list` STRIP_ASSUME_TAC))
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `clause A'` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `clause B'` ASSUME_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[MEM]] THEN
    UNDISCH_TAC `asm SUBSET {IMAGE (formsubst v) cl | cl,v | cl IN hyps}` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `B':form->bool`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[IMAGE_FORMSUBST_CLAUSE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[RESOLVE_CLAUSE];
    ALL_TAC] THEN
  UNDISCH_TAC `lresproof hyps alist` THEN
  UNDISCH_TAC `ALL2 (instance_of) (CONS A' lis') alist` THEN
  SPEC_TAC(`alist:(form->bool)list`,`alist:(form->bool)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL2] THEN
  MAP_EVERY X_GEN_TAC [`A:form->bool`; `lis:(form->bool)list`] THEN
  DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `clause A /\ !c. MEM c lis ==> clause c` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ALL_MEM; GSYM(CONJUNCT2 ALL)] THEN
    ASM_MESON_TAC[LRESPROOF_CLAUSE]; ALL_TAC] THEN
  SUBGOAL_THEN `?B. B' instance_of B /\ (B IN hyps \/ MEM B lis)` MP_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [UNDISCH_TAC `asm SUBSET {IMAGE (formsubst v) cl | cl,v | cl IN hyps}` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `B':form->bool`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
      REWRITE_TAC[instance_of] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[ALL2_MEM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:form->bool` (CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `clause B` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL
   [`A:form->bool`; `IMAGE (formsubst (rename B (FVS A))) B`;
    `A':form->bool`; `B':form->bool`; `resolve p A' B'`; `p:form`]
   LIFTING_LEMMA) THEN
  ABBREV_TAC `C = IMAGE (formsubst (rename B (FVS A))) B` THEN
  MP_TAC(SPECL [`B:form->bool`; `FVS(A)`] rename) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FVS_CLAUSE_FINITE; RESPROOF_CLAUSE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[renaming] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [FUN_EQ_THM; o_THM; I_DEF; BETA_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num->term` (ASSUME_TAC o CONJUNCT1)) THEN
  ANTS_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IMAGE_FORMSUBST_CLAUSE; RESPROOF_CLAUSE];
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `B' instance_of B` THEN REWRITE_TAC[instance_of] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num->term` SUBST1_TAC) THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    EXISTS_TAC `termsubst k o (j:num->term)` THEN
    SUBGOAL_THEN
     `termsubst k = termsubst (termsubst k o j) o termsubst (rename B (FVS A))`
    MP_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[termsubst; GSYM TERMSUBST_TERMSUBST; o_THM];
        SIMP_TAC[termsubst; term_INJ; o_THM; GSYM MAP_o] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC[o_THM]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM FORMSUBST_TERMSUBST_LEMMA] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
    ASM_MESON_TAC[RESPROOF_CLAUSE; clause; QFREE_LITERAL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:form->bool` (X_CHOOSE_THEN `B1:form->bool`
      MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `mgu (A1 UNION {~~ l | l IN B1})`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC ISMGU_MGU THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[RESPROOF_CLAUSE; clause; FINITE_SUBSET];
      SUBGOAL_THEN `{~~l | l IN B1} = IMAGE (~~) B1` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[RESPROOF_CLAUSE; clause; FINITE_SUBSET; FINITE_IMAGE];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[RESPROOF_CLAUSE; clause; QFREE_LITERAL; SUBSET;
                    IMAGE_FORMSUBST_CLAUSE; QFREE_NEGATE]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `CONS (IMAGE (formsubst (mgu (A1 UNION {~~ l | l IN B1})))
                          (A DIFF A1 UNION C DIFF B1))
                   (CONS A lis)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC (CONJUNCT2(SPEC_ALL lresproof_RULES)) THEN
    EXISTS_TAC `B:form->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[isaresolvent] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    MAP_EVERY EXISTS_TAC [`A1:form->bool`; `B1:form->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ALL2]);;
