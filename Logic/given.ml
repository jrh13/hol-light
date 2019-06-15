(* ========================================================================= *)
(* Applying forward subsumption and back replacement in given clause alg.    *)
(* ========================================================================= *)

let FIRSTN = new_recursive_definition num_RECURSION
  `(FIRSTN 0 l = []) /\
   (FIRSTN (SUC n) l = if l = [] then [] else CONS (HD l) (FIRSTN n (TL l)))`;;

let FIRSTN_TRIVIAL = prove
 (`!n l. LENGTH l <= n ==> (FIRSTN n l = l)`,
  INDUCT_TAC THEN SIMP_TAC[LE; FIRSTN; LENGTH_EQ_NIL] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  REWRITE_TAC[HD; TL; LENGTH; CONS_11; SUC_INJ] THEN
  ASM_MESON_TAC[ARITH_RULE `SUC x <= y ==> x <= y`; LE_REFL]);;

let FIRSTN_EMPTY = prove
 (`!n. FIRSTN n [] = []`,
  MESON_TAC[FIRSTN_TRIVIAL; LENGTH; LE_0]);;

let FIRSTN_SUBLIST = prove
 (`!x n l. MEM x (FIRSTN n l) ==> MEM x l`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[FIRSTN; MEM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL; HD; TL; MEM] THEN
  ASM_MESON_TAC[]);;

let FIRSTN_SUC = prove
 (`!x n l. MEM x (FIRSTN (SUC n) l)
           ==> MEM x (APPEND (FIRSTN n l) [EL n l])`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FIRSTN] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM; APPEND; EL];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[FIRSTN] THEN
  REWRITE_TAC[NOT_CONS_NIL; MEM] THEN
  REWRITE_TAC[HD; TL; EL; MEM; APPEND] THEN ASM_MESON_TAC[]);;

let FIRSTN_SHORT = prove
 (`!n l. LENGTH l <= n ==> (FIRSTN (SUC n) l = FIRSTN n l)`,
  MESON_TAC[FIRSTN_TRIVIAL; ARITH_RULE `x <= n ==> x <= SUC n`]);;

(* ------------------------------------------------------------------------- *)
(* Tautologousness.                                                          *)
(* ------------------------------------------------------------------------- *)

let tautologous = new_definition
  `tautologous cl <=> ?p. p IN cl /\ ~~p IN cl`;;

(* ------------------------------------------------------------------------- *)
(* Definition of subsumption.                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("subsumes",(12,"right"));;

let subsumes = new_definition
  `cl subsumes cl' <=> ?i. IMAGE (formsubst i) cl SUBSET cl'`;;

let subsumes_REFL = prove
 (`!cl. cl subsumes cl`,
  GEN_TAC THEN REWRITE_TAC [subsumes] THEN
  EXISTS_TAC `V` THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; FORMSUBST_TRIV] THEN MESON_TAC[]);;

let subsumes_TRANS = prove
 (`!cl1 cl2 cl3. clause cl1 /\ cl1 subsumes cl2 /\ cl2 subsumes cl3
                 ==> cl1 subsumes cl3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subsumes; clause] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:num->term`) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num->term`) THEN
  EXISTS_TAC `termsubst j o (i:num->term)` THEN
  UNDISCH_TAC `IMAGE (formsubst i) cl1 SUBSET cl2` THEN
  UNDISCH_TAC `IMAGE (formsubst j) cl2 SUBSET cl3` THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN
  SUBGOAL_THEN
   `!p. p IN cl1
        ==> (formsubst (termsubst j o i) p = formsubst j (formsubst i p))`
   (fun th -> MESON_TAC[th]) THEN
  SUBGOAL_THEN
   `!p. qfree(p)
        ==> (formsubst (termsubst j o i) p = formsubst j (formsubst i p))`
   (fun th -> ASM_MESON_TAC[th; QFREE_LITERAL]) THEN
  MATCH_MP_TAC form_INDUCTION THEN
  SIMP_TAC[qfree; formsubst; o_THM; GSYM TERMSUBST_TERMSUBST] THEN
  REWRITE_TAC[GSYM MAP_o] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; TERMSUBST_TERMSUBST; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Lifting subsumption to a whole set.                                       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("SUBSUMES",(12,"right"));;

let SUBSUMES = new_definition
  `s SUBSUMES s' <=> !cl'. cl' IN s' ==> ?cl. cl IN s /\ cl subsumes cl'`;;

(* ------------------------------------------------------------------------- *)
(* Simple lemmas.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUBSUMES_REFL = prove
 (`!s. s SUBSUMES s`,
  REWRITE_TAC[SUBSUMES] THEN MESON_TAC[subsumes_REFL]);;

let SUBSUMES_UNION = prove
 (`s SUBSUMES s' /\ t SUBSUMES t' ==> (s UNION t) SUBSUMES (s' UNION t')`,
  REWRITE_TAC[SUBSUMES; IN_UNION] THEN MESON_TAC[]);;

let SUBSUMES_TRANS = prove
 (`!s t u. (!c. c IN s ==> clause c) /\ s SUBSUMES t /\ t SUBSUMES u
           ==> s SUBSUMES u`,
  REWRITE_TAC[SUBSUMES] THEN MESON_TAC[subsumes_TRANS]);;

let SUBSUMES_SUBSET = prove
 (`!s t u. s SUBSUMES t /\ s SUBSET u ==> u SUBSUMES t`,
  REWRITE_TAC[SUBSUMES; SUBSET] THEN MESON_TAC[]);;

let SUBSUMES_CLAUSES = prove
 (`(!s. s SUBSUMES {}) /\
   (!s. s SUBSUMES (x INSERT t) <=> s SUBSUMES {x} /\ s SUBSUMES t)`,
  REWRITE_TAC[SUBSUMES; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let SUBSUMES_SUBSET_REFL = prove
 (`!s t. s SUBSET t ==> t SUBSUMES s`,
  MESON_TAC[SUBSUMES_SUBSET; SUBSUMES_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Set of all resolvents of a pair of clauses.                               *)
(* ------------------------------------------------------------------------- *)

let allresolvents = new_definition
  `allresolvents s1 s2 =
        {c | ?c1 c2. c1 IN s1 /\ c2 IN s2 /\ isaresolvent c (c1,c2)}`;;

(* ------------------------------------------------------------------------- *)
(* Non-tautological resolvents.                                              *)
(* ------------------------------------------------------------------------- *)

let allntresolvents = new_definition
  `allntresolvents s1 s2 =
        {r | r IN allresolvents s1 s2 /\ ~(tautologous r)}`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let TERMSUBST_TERMSUBST_o = prove
 (`termsubst (termsubst j o i) = termsubst j o termsubst i`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; TERMSUBST_TERMSUBST]);;

let FORMSUBST_FORMSUBST = prove
 (`!p i j. qfree(p)
           ==> (formsubst j (formsubst i p) = formsubst (termsubst j o i) p)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`p:form`,`p:form`) THEN
  MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC[formsubst; qfree] THEN
  REWRITE_TAC[GSYM MAP_o; TERMSUBST_TERMSUBST_o]);;

let ISARESOLVENT_SYM = prove
 (`!c1 c2 cl.
        clause c1 /\ clause c2 /\ isaresolvent cl (c2,c1)
        ==> ?cl'. isaresolvent cl' (c1,c2) /\ cl' subsumes cl`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `isaresolvent cl (c2,c1)` THEN
  REWRITE_TAC[isaresolvent] THEN
  ABBREV_TAC `r1 = rename c1 (FVS c2)` THEN
  ABBREV_TAC `c1' = IMAGE (formsubst r1) c1` THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV let_CONV)) THEN
  DISCH_THEN(X_CHOOSE_THEN `ps2:form->bool`
        (X_CHOOSE_THEN `ps1:form->bool` MP_TAC)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV let_CONV)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  ABBREV_TAC `r2 = rename c2 (FVS c1)` THEN
  ABBREV_TAC `c2' = IMAGE (formsubst r2) c2` THEN
  MP_TAC(SPECL [`c1:form->bool`; `FVS c2`] rename) THEN
  ASM_SIMP_TAC[FVS_CLAUSE_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [renaming] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:num->term` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`c2:form->bool`; `FVS c1`] rename) THEN
  ASM_SIMP_TAC[FVS_CLAUSE_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [renaming] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:num->term` STRIP_ASSUME_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `IMAGE (formsubst s1) ps1` THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `IMAGE (formsubst r2) ps2` THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN
  W(EXISTS_TAC o funpow 6 rand o lhand o snd o dest_exists o snd) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a /\ b /\ c /\ d /\ e) /\ (e ==> f)
                     ==> (a /\ b /\ c /\ d /\ e) /\ f`) THEN
  CONJ_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ps1 SUBSET c1':form->bool` THEN EXPAND_TAC "c1'" THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN
      SUBGOAL_THEN `!p. p IN c1 ==> (formsubst s1 (formsubst r1 p) = p)`
        (fun th -> MESON_TAC[th]) THEN
      SUBGOAL_THEN
       `!p. qfree p
            ==> (formsubst V p = formsubst s1 (formsubst r1 p))`
       (fun th -> ASM_MESON_TAC[th; FORMSUBST_TRIV;
                                clause; QFREE_LITERAL]) THEN
      ASM_REWRITE_TAC[FORMSUBST_TERMSUBST_LEMMA] THEN
      REWRITE_TAC[FUN_EQ_THM; TERMSUBST_TRIV; I_DEF];
      UNDISCH_TAC `ps2 SUBSET c2:form->bool` THEN EXPAND_TAC "c2'" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
      UNDISCH_TAC `~(ps1:form->bool = {})` THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_IMAGE] THEN MESON_TAC[];
      UNDISCH_TAC `~(ps2:form->bool = {})` THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_IMAGE] THEN MESON_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `i:num->term` MP_TAC) THEN
      REWRITE_TAC[UNIFIES; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
      REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
      SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN REWRITE_TAC[FORALL_AND_THM] THEN
      X_GEN_TAC `P:form` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(MP_TAC o GEN `p:form` o SPECL [`~~p`; `p:form`]) THEN
      REWRITE_TAC[] THEN DISCH_TAC THEN
      EXISTS_TAC `\x. if x IN FVS(IMAGE (formsubst s1) ps1)
                      then termsubst i (r1 x)
                      else termsubst i (s2 x)` THEN
      EXISTS_TAC `~~P` THEN CONJ_TAC THENL
       [X_GEN_TAC `rrr:form` THEN X_GEN_TAC `p:form` THEN
        DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `formsubst (\x. termsubst i (r1 x)) (formsubst s1 p)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC FORMSUBST_VALUATION THEN X_GEN_TAC `x:num` THEN
          DISCH_TAC THEN REWRITE_TAC[] THEN
          SUBGOAL_THEN `x IN FVS(IMAGE (formsubst s1) ps1)`
            (fun th -> REWRITE_TAC[th]) THEN
          REWRITE_TAC[IN_UNIONS; FVS; IN_ELIM_THM; IN_IMAGE] THEN
          ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `P = formsubst i (~~p)` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `literal p` MP_TAC THENL
         [UNDISCH_TAC `ps1 SUBSET c1':form->bool` THEN
          EXPAND_TAC "c1'" THEN REWRITE_TAC[IN_IMAGE; SUBSET] THEN
          DISCH_THEN(MP_TAC o SPEC `p:form`) THEN
          ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; FORMSUBST_LITERAL] THEN
          ASM_MESON_TAC[clause]; ALL_TAC] THEN
        SIMP_TAC[GSYM FORMSUBST_NEGATE; NEGATE_NEGATE] THEN
        DISCH_THEN(MP_TAC o MATCH_MP QFREE_LITERAL) THEN
        SIMP_TAC[FORMSUBST_FORMSUBST; GSYM o_DEF] THEN
        UNDISCH_TAC `ps1 SUBSET c1':form->bool` THEN
        EXPAND_TAC "c1'" THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN
        DISCH_THEN(MP_TAC o SPEC `p:form`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `q:form`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
        SIMP_TAC[QFREE_FORMSUBST; FORMSUBST_FORMSUBST] THEN
        SPEC_TAC(`q:form`,`q:form`) THEN
        MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC[formsubst; qfree] THEN
        REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[TERMSUBST_TERMSUBST_o] THEN
        ASM_REWRITE_TAC[GSYM o_ASSOC] THEN REWRITE_TAC[o_DEF; I_DEF];
        ALL_TAC] THEN
      X_GEN_TAC `rrr:form` THEN X_GEN_TAC `p:form` THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(X_CHOOSE_THEN `q:form`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      REWRITE_TAC[FORMSUBST_NEGATE] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `formsubst (\x. termsubst i (s2 x)) (formsubst r2 q)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FORMSUBST_VALUATION THEN X_GEN_TAC `x:num` THEN
        DISCH_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(x IN FVS(IMAGE (formsubst s1) ps1))`
          (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `FVS c2' INTER FVS c1 = {}` THEN EXPAND_TAC "c2'" THEN
        REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
        DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
        UNDISCH_TAC `x IN FV(formsubst r2 q)` THEN
        MATCH_MP_TAC(TAUT
         `(a ==> a') /\ (b ==> b') ==> a ==> ~(a' /\ b') ==> ~b`) THEN
        CONJ_TAC THENL
         [REWRITE_TAC[FVS; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
          ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
        REWRITE_TAC[FVS; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
        UNDISCH_TAC `ps1 SUBSET c1':form->bool` THEN
        REWRITE_TAC[SUBSET] THEN
        EXPAND_TAC "c1'" THEN REWRITE_TAC[IN_IMAGE] THEN
        SUBGOAL_THEN `!p. p IN c1 ==> (formsubst s1 (formsubst r1 p) = p)`
          (fun th -> MESON_TAC[th]) THEN
        SUBGOAL_THEN `!p. qfree(p) ==> (formsubst s1 (formsubst r1 p) = p)`
          (fun th -> ASM_MESON_TAC[th; clause; QFREE_LITERAL]) THEN
        SIMP_TAC[FORMSUBST_FORMSUBST] THEN
        MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC[formsubst; qfree] THEN
        REPEAT GEN_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
        ASM_REWRITE_TAC[TERMSUBST_TERMSUBST_o] THEN
        REWRITE_TAC[I_THM; ALL_T]; ALL_TAC] THEN
      SUBGOAL_THEN `qfree q` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET; clause; QFREE_LITERAL]; ALL_TAC] THEN
      SIMP_TAC[FORMSUBST_FORMSUBST] THEN
      SUBGOAL_THEN `formsubst i q = P` (SUBST1_TAC o SYM) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM o_DEF] THEN
      SPEC_TAC(`q:form`,`q:form`) THEN
      MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC[formsubst; qfree] THEN
      REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[TERMSUBST_TERMSUBST_o] THEN
      ASM_REWRITE_TAC[GSYM o_ASSOC] THEN REWRITE_TAC[o_DEF; I_DEF] THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ps0. ps0 SUBSET c1 /\ ~(ps0 = {}) /\
                      (ps1 = IMAGE (formsubst r1) ps0)`
  MP_TAC THENL
   [EXISTS_TAC `{p | p IN c1 /\ (formsubst r1 p) IN ps1}` THEN
    UNDISCH_TAC `~(ps1:form->bool = {})` THEN
    UNDISCH_TAC `ps1 SUBSET c1':form->bool` THEN EXPAND_TAC "c1'" THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_ELIM_THM; NOT_IN_EMPTY;
                IN_IMAGE] THEN
    MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ps0:form->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN SUBST_ALL_TAC THEN EXPAND_TAC "c2'" THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  SUBGOAL_THEN `IMAGE (formsubst s1 o formsubst r1) ps0 = ps0` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
    X_GEN_TAC `p:form` THEN
    SUBGOAL_THEN `!p. p IN ps0 ==> (formsubst s1 (formsubst r1 p) = p)`
        (fun th -> MESON_TAC[th]) THEN
    SUBGOAL_THEN `!p. qfree p ==> (formsubst s1 (formsubst r1 p) = p)`
        (fun th -> ASM_MESON_TAC[clause; SUBSET; QFREE_LITERAL; th]) THEN
    MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC[formsubst; qfree] THEN
    ASM_REWRITE_TAC[GSYM MAP_o] THEN
    SIMP_TAC[MAP_EQ_DEGEN; I_DEF; ALL_T]; ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `i = mgu (ps0 UNION {~~p | p IN IMAGE (formsubst r2) ps2})` THEN
  ABBREV_TAC `j = mgu (ps2 UNION {~~p | p IN IMAGE (formsubst r1) ps0})` THEN
  EXPAND_TAC "c1'" THEN
  MP_TAC(SPEC `ps0 UNION {~~p | p IN IMAGE (formsubst r2) ps2}` MGU) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `{~~ p | p IN IMAGE (formsubst r2) ps2} =
                    IMAGE (~~) (IMAGE (formsubst r2) ps2)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC FINITE_IMAGE) THEN
      ASM_MESON_TAC[FINITE_SUBSET; clause]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[QFREE_NEGATE; QFREE_FORMSUBST] THEN
    ASM_MESON_TAC[SUBSET; clause; QFREE_LITERAL]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `ps2 UNION {~~ p | p IN IMAGE (formsubst r1) ps0}` MGU) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `{~~ p | p IN IMAGE (formsubst r1) ps0} =
                    IMAGE (~~) (IMAGE (formsubst r1) ps0)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC FINITE_IMAGE) THEN
      ASM_MESON_TAC[FINITE_SUBSET; clause]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[QFREE_NEGATE; QFREE_FORMSUBST] THEN
    ASM_MESON_TAC[SUBSET; clause; QFREE_LITERAL]; ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC
   `!i'. Unifies i' (ps0 UNION {~~ p | p IN IMAGE (formsubst r2) ps2})
            ==> (!p. qfree p
                     ==> (formsubst i' p = formsubst i' (formsubst i p)))` THEN
  DISCH_THEN(MP_TAC o SPEC
    `\x. if x IN FVS(c1) then termsubst j (r1 x)
         else termsubst j (s2 x)`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC
     `Unifies j (ps2 UNION {~~ p | p IN IMAGE (formsubst r1) ps0})` THEN
    REWRITE_TAC[UNIFIES] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:form` MP_TAC) THEN
    REWRITE_TAC[UNIFIES; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN REWRITE_TAC[FORALL_AND_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o GEN `p:form` o SPECL [`~~p`; `p:form`]) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o GEN `p:form` o SPECL [`formsubst r1 p`; `p:form`]) THEN
    ASM_REWRITE_TAC[FORMSUBST_NEGATE] THEN DISCH_TAC THEN
    EXISTS_TAC `~~P` THEN CONJ_TAC THENL
     [X_GEN_TAC `p:form` THEN DISCH_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `formsubst (termsubst j o r1) p` THEN CONJ_TAC THENL
       [MATCH_MP_TAC FORMSUBST_VALUATION THEN
        X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        SUBGOAL_THEN `x IN FVS(c1)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[FVS; IN_UNIONS; IN_ELIM_THM] THEN
        ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `P = ~~(formsubst j (formsubst r1 p))` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~~(~~(formsubst j (formsubst r1 p))) =
                    formsubst j (formsubst r1 p)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC NEGATE_NEGATE THEN
        REWRITE_TAC[FORMSUBST_LITERAL] THEN
        ASM_MESON_TAC[SUBSET; clause]; ALL_TAC] THEN
      MATCH_MP_TAC(GSYM FORMSUBST_FORMSUBST) THEN
      ASM_MESON_TAC[SUBSET; clause; QFREE_LITERAL]; ALL_TAC] THEN
    X_GEN_TAC `rrr:form` THEN X_GEN_TAC `p:form` THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `q:form` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `formsubst j q = P` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `formsubst (termsubst j o s2) (formsubst r2 q)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FORMSUBST_VALUATION THEN
      X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(x IN FVS(c1))` (fun th -> REWRITE_TAC[o_THM; th]) THEN
      UNDISCH_TAC `FVS c2' INTER FVS c1 = {}` THEN EXPAND_TAC "c2'" THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
      MATCH_MP_TAC(TAUT `a ==> ~(a /\ b) ==> ~b`) THEN
      UNDISCH_TAC `x IN FV (formsubst r2 q)` THEN
      UNDISCH_TAC `q:form IN ps2` THEN
      UNDISCH_TAC `ps2 SUBSET c2:form->bool` THEN
      REWRITE_TAC[SUBSET; FVS; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `qfree q` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; clause; QFREE_LITERAL]; ALL_TAC] THEN
    SIMP_TAC[FORMSUBST_FORMSUBST] THEN
    SPEC_TAC(`q:form`,`q:form`) THEN MATCH_MP_TAC form_INDUCTION THEN
    SIMP_TAC[qfree; formsubst] THEN REPEAT GEN_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[TERMSUBST_TERMSUBST_o] THEN
    ASM_REWRITE_TAC[GSYM o_ASSOC] THEN REWRITE_TAC[o_DEF; I_DEF; ALL_T];
    ALL_TAC] THEN
  ABBREV_TAC `k = \x. if x IN FVS(c1) then termsubst j (r1 x)
                      else termsubst j (s2 x)` THEN
  DISCH_TAC THEN REWRITE_TAC[subsumes] THEN
  EXISTS_TAC `k:num->term` THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  SUBGOAL_THEN
   `IMAGE (formsubst k o formsubst i)
          (c1 DIFF ps0 UNION c2' DIFF IMAGE (formsubst r2) ps2) =
    IMAGE (formsubst k)
          (c1 DIFF ps0 UNION c2' DIFF IMAGE (formsubst r2) ps2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    SUBGOAL_THEN
     `!p. p IN (c1 DIFF ps0 UNION c2' DIFF IMAGE (formsubst r2) ps2)
          ==> qfree p`
     (fun th -> ASM_MESON_TAC[o_THM; th]) THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_DIFF] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[QFREE_LITERAL; clause]; ALL_TAC] THEN
    UNDISCH_TAC `p:form IN c2'` THEN EXPAND_TAC "c2'" THEN
    SIMP_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM; QFREE_FORMSUBST] THEN
    ASM_MESON_TAC[QFREE_LITERAL; clause]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `p:form` THEN
  DISCH_THEN(X_CHOOSE_THEN `q:form` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [EXISTS_TAC `formsubst r1 q` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `qfree q` MP_TAC THENL
       [ASM_MESON_TAC[IN_DIFF; clause; QFREE_LITERAL]; ALL_TAC] THEN
      SIMP_TAC[FORMSUBST_FORMSUBST] THEN DISCH_TAC THEN
      MATCH_MP_TAC FORMSUBST_VALUATION THEN
      X_GEN_TAC `x:num` THEN DISCH_TAC THEN EXPAND_TAC "k" THEN
      SUBGOAL_THEN `x IN FVS(c1)` (fun th -> REWRITE_TAC[th; o_THM]) THEN
      REWRITE_TAC[FVS; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[IN_DIFF];
      ALL_TAC] THEN
    DISJ2_TAC THEN EXPAND_TAC "c1'" THEN
    UNDISCH_TAC `q:form IN c1 DIFF ps0` THEN
    REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:form` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `formsubst s1`) THEN
    SUBGOAL_THEN `(formsubst s1 (formsubst r1 q) = q) /\
                  (formsubst s1 (formsubst r1 r) = r)`
      (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `!p. qfree p ==> (formsubst s1 (formsubst r1 p) = p)`
      (fun th -> ASM_MESON_TAC[th; SUBSET; clause; QFREE_LITERAL]) THEN
    GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o RAND_CONV)
     [GSYM FORMSUBST_TRIV] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[FORMSUBST_TERMSUBST_LEMMA] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM; TERMSUBST_TRIV; I_DEF];
    ALL_TAC] THEN
  EXISTS_TAC `formsubst s2 q` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `qfree q` MP_TAC THENL
     [UNDISCH_TAC `q IN c2' DIFF IMAGE (formsubst r2) ps2` THEN
      EXPAND_TAC "c2'" THEN REWRITE_TAC[IN_DIFF] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[IN_IMAGE] THEN
      ASM_MESON_TAC[clause; QFREE_LITERAL; QFREE_FORMSUBST]; ALL_TAC] THEN
    SIMP_TAC[FORMSUBST_FORMSUBST] THEN DISCH_TAC THEN
    MATCH_MP_TAC FORMSUBST_VALUATION THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN EXPAND_TAC "k" THEN
    SUBGOAL_THEN `~(x IN FVS(c1))` (fun th -> REWRITE_TAC[th; o_THM]) THEN
    UNDISCH_TAC `FVS c2' INTER FVS c1 = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    MATCH_MP_TAC(TAUT `a ==> ~(a /\ b) ==> ~b`) THEN
    REWRITE_TAC[FVS; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[IN_DIFF];
    ALL_TAC] THEN
  DISJ1_TAC THEN
  UNDISCH_TAC `q IN c2' DIFF IMAGE (formsubst r2) ps2` THEN
  EXPAND_TAC "c2'" THEN
  REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
  MATCH_MP_TAC(TAUT `(a ==> a') /\ (b ==> b') ==> a /\ b ==> a' /\ b'`) THEN
  CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:form` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `formsubst s2 (formsubst r2 r) = r`
     (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `qfree r` MP_TAC THENL
     [ASM_MESON_TAC[clause; QFREE_LITERAL]; ALL_TAC] THEN
    SPEC_TAC(`r:form`,`r:form`) THEN
    GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o RAND_CONV)
     [GSYM FORMSUBST_TRIV] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[FORMSUBST_TERMSUBST_LEMMA] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM; TERMSUBST_TRIV; I_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
  DISCH_TAC THEN
  EXISTS_TAC `formsubst s2 q` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN GEN_REWRITE_TAC RAND_CONV [GSYM FORMSUBST_TRIV] THEN
  SUBGOAL_THEN `qfree q` MP_TAC THENL
   [ASM_MESON_TAC[QFREE_FORMSUBST; SUBSET; clause; QFREE_LITERAL];
    ALL_TAC] THEN
  SPEC_TAC(`q:form`,`q:form`) THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[FORMSUBST_TERMSUBST_LEMMA] THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; TERMSUBST_TRIV; I_DEF]);;

let ALLRESOLVENTS_SYM = prove
 (`(!c. c IN A ==> clause c) /\ (!c. c IN B ==> clause c)
   ==> (allresolvents A B) SUBSUMES (allresolvents B A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSUMES; allresolvents; IN_ELIM_THM] THEN
  X_GEN_TAC `cl:form->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:form->bool`
        (X_CHOOSE_THEN `c1:form->bool` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `c1:form->bool` THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `c2:form->bool` THEN
  ASM_SIMP_TAC[ISARESOLVENT_SYM]);;

let ALLRESOLVENTS_UNION = prove
 (`(allresolvents (A UNION B) C =
        (allresolvents A C) UNION (allresolvents B C)) /\
   (allresolvents A (B UNION C) =
        (allresolvents A B) UNION (allresolvents A C))`,
  REWRITE_TAC[EXTENSION; allresolvents; IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[]);;

let ALLRESOLVENTS_STEP = prove
 (`(!c. c IN B ==> clause(c)) /\
   (!c. c IN C ==> clause(c))
   ==> ((allresolvents B (A UNION B)) UNION
        (allresolvents C (A UNION B UNION C)))
       SUBSUMES (allresolvents(B UNION C) (A UNION B UNION C))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ALLRESOLVENTS_UNION; UNION_ASSOC] THEN
  ONCE_REWRITE_TAC[AC UNION_ACI
   `a UNION b UNION c UNION d UNION e UNION f =
    a UNION b UNION d UNION (c UNION e) UNION f`] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV) [AC UNION_ACI
   `A UNION B = (A UNION A) UNION B`] THEN
  REPEAT(MATCH_MP_TAC SUBSUMES_UNION THEN ASM_REWRITE_TAC[SUBSUMES_REFL]) THEN
  ASM_SIMP_TAC[ALLRESOLVENTS_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Asymmetric list-based version used in algorithm.                          *)
(* ------------------------------------------------------------------------- *)

let resolvents = new_definition
  `resolvents cl cls = list_of_set(allresolvents {cl} (set_of_list cls))`;;

(* ------------------------------------------------------------------------- *)
(* Trivial lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

let CLAUSE_UNION = prove
 (`!c1 c2. clause(c1 UNION c2) <=> clause(c1) /\ clause(c2)`,
  REWRITE_TAC[clause; FINITE_UNION; IN_UNION] THEN MESON_TAC[]);;

let CLAUSE_SUBSET = prove
 (`!c1 c2. clause c2 /\ c1 SUBSET c2 ==> clause c1`,
  REWRITE_TAC[clause] THEN MESON_TAC[SUBSET; FINITE_SUBSET]);;

let CLAUSE_DIFF = prove
 (`!c1 c2. clause c1 ==> clause (c1 DIFF c2)`,
  MESON_TAC[CLAUSE_SUBSET; IN_DIFF; SUBSET]);;

let ISARESOLVENT_CLAUSE = prove
 (`!p q r. clause p /\ clause q /\ isaresolvent r (p,q) ==> clause r`,
  REWRITE_TAC[isaresolvent] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_FORMSUBST_CLAUSE THEN
  ASM_SIMP_TAC[IMAGE_FORMSUBST_CLAUSE; CLAUSE_UNION; CLAUSE_DIFF]);;

let ALLRESOLVENTS_CLAUSE = prove
 (`(!c. c IN s ==> clause c) /\ (!c. c IN t ==> clause c)
   ==> !c. c IN allresolvents s t ==> clause c`,
  REWRITE_TAC[allresolvents; IN_ELIM_THM; isaresolvent] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_FORMSUBST_CLAUSE THEN
  ASM_SIMP_TAC[IMAGE_FORMSUBST_CLAUSE; CLAUSE_UNION; CLAUSE_DIFF]);;

let ISARESOLVENT_FINITE = prove
 (`!c1 c2. clause(c1) /\ clause(c2)
           ==> FINITE {c | isaresolvent c (c1,c2)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isaresolvent] THEN
  LET_TAC THEN
  SUBGOAL_THEN `clause cl2'` ASSUME_TAC THENL
   [EXPAND_TAC "cl2'" THEN ASM_SIMP_TAC[IMAGE_FORMSUBST_CLAUSE];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\pss. let i = mgu (FST(pss) UNION {~~ p | p IN SND(pss)}) in
                     IMAGE (formsubst i)
                           (c1 DIFF (FST pss) UNION cl2' DIFF (SND pss)))
          {ps1,ps2 | ps1 IN {ps1 | ps1 SUBSET c1} /\
                     ps2 IN {ps2 | ps2 SUBSET cl2'}}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `c:form->bool` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`ps1:form->bool`; `ps2:form->bool`] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    EXISTS_TAC `ps1:form->bool,ps2:form->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_PRODUCT THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clause]) THEN ASM_SIMP_TAC[FINITE_POWERSET]);;

let ALLRESOLVENTS_FINITE = prove
 (`!s t. FINITE(s) /\ FINITE(t) /\
         (!c. c IN s ==> clause c) /\
         (!c. c IN t ==> clause c)
         ==> FINITE(allresolvents s t)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `allresolvents s t =
        UNIONS (IMAGE (\cs. {c | isaresolvent c cs})
                      {c1,c2 | c1 IN s /\ c2 IN t})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; allresolvents; IN_UNIONS; IN_IMAGE;
                IN_ELIM_THM] THEN
    X_GEN_TAC `c:form->bool` THEN
    EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    STRIP_TAC THEN EXISTS_TAC `{c | isaresolvent c (c1,c2)}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FINITE_PRODUCT] THEN
  REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC `u:(form->bool)->bool` THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [IN_ELIM_THM; BETA_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[ISARESOLVENT_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* Replacement.                                                              *)
(* ------------------------------------------------------------------------- *)

let replace = new_recursive_definition list_RECURSION
  `(replace cl [] = [cl]) /\
   (replace cl (CONS c cls) =
        if cl subsumes c then CONS cl cls else CONS c (replace cl cls))`;;

let REPLACE = prove
 (`!cl lis. (!c. MEM c lis ==> clause c) /\ clause cl
            ==> (!c. MEM c (replace cl lis) ==> clause c) /\
                set_of_list(replace cl lis) SUBSUMES set_of_list(CONS cl lis)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  SIMP_TAC[replace; SUBSUMES_REFL; MEM] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_imp o concl) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[MEM; set_of_list] THENL
   [UNDISCH_TAC `set_of_list(replace cl t) SUBSUMES
                    set_of_list(CONS cl t)`;
    UNDISCH_TAC
     `set_of_list(replace cl t) SUBSUMES set_of_list(CONS cl t)`] THEN
  REWRITE_TAC[SUBSUMES; IN_INSERT; set_of_list] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN ASM_MESON_TAC[subsumes_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Incorporation.                                                            *)
(* ------------------------------------------------------------------------- *)

let incorporate = new_definition
  `incorporate gcl cl current =
        if tautologous cl \/ EX (\c. c subsumes cl) (CONS gcl current)
        then current else replace cl current`;;

let INCORPORATE = prove
 (`!gcl cl current.
        (!c. MEM c current ==> clause c) /\ clause gcl /\ clause cl
        ==> (!c. MEM c (incorporate gcl cl current) ==> clause c) /\
            set_of_list(incorporate gcl cl current)
                SUBSUMES set_of_list(current) /\
            (tautologous cl \/
             (gcl INSERT set_of_list(incorporate gcl cl current))
                SUBSUMES set_of_list(CONS cl current))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[incorporate] THEN
  ASM_CASES_TAC `tautologous cl` THEN ASM_REWRITE_TAC[SUBSUMES_REFL] THEN
  ASM_CASES_TAC `EX (\c. c subsumes cl) (CONS gcl current)` THEN
  ASM_REWRITE_TAC[SUBSUMES_REFL] THENL
   [REWRITE_TAC[set_of_list] THEN ONCE_REWRITE_TAC[SUBSUMES_CLAUSES] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 set_of_list)] THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUBSUMES_SUBSET THEN
      EXISTS_TAC `set_of_list(current:(form->bool)list)` THEN
      REWRITE_TAC[SUBSUMES_REFL] THEN
      SIMP_TAC[SUBSET; set_of_list; IN_INSERT]] THEN
    UNDISCH_TAC `EX (\c. c subsumes cl) (CONS gcl current)` THEN
    SPEC_TAC(`CONS (gcl:form->bool) current`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[EX] THEN
    ASM_REWRITE_TAC[set_of_list] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSUMES_SUBSET THENL
     [EXISTS_TAC `{h:form->bool}`;
      EXISTS_TAC `set_of_list(t:(form->bool)list)`] THEN
    ASM_SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[SUBSUMES; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cl:form->bool`; `current:(form->bool)list`] REPLACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `set_of_list(replace cl current) SUBSUMES
               set_of_list (CONS cl current)` THEN
  REWRITE_TAC[SUBSUMES; set_of_list; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set insertion.                                                            *)
(* ------------------------------------------------------------------------- *)

let insert_def = new_definition
  `insert x l = if MEM x l then l else CONS x l`;;

(* ------------------------------------------------------------------------- *)
(* Basic given clause algorithm.                                             *)
(* ------------------------------------------------------------------------- *)

let step = new_definition
  `step (used,unused) =
        if unused = [] then (used,unused) else
        let new = resolvents (HD unused) (CONS (HD unused) used) in
        (insert (HD unused) used,
         ITLIST (incorporate (HD unused)) new (TL unused))`;;

let STEP = prove
 (`(step(used,[]) = (used,[])) /\
   (step(used,CONS cl cls) =
        let new = resolvents cl (CONS cl used) in
        insert cl used,ITLIST (incorporate cl) new cls)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [step] THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL]);;

let given = new_recursive_definition num_RECURSION
  `(given 0 p = p) /\
   (given (SUC n) p = step(given n p))`;;

(* ------------------------------------------------------------------------- *)
(* Separation into bits simplifies things a bit.                             *)
(* ------------------------------------------------------------------------- *)

let Used_DEF = new_definition
  `Used init n = set_of_list(FST(given n init))`;;

let Unused_DEF = new_definition
  `Unused init n = set_of_list(SND(given n init))`;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary concept actually has the cleanest recursion equations.          *)
(* ------------------------------------------------------------------------- *)

let Sub_DEF = new_recursive_definition num_RECURSION
  `(Sub init 0 = {}) /\
   (Sub init (SUC n) = if SND(given n init) = [] then Sub init n
                       else HD(SND(given n init)) INSERT (Sub init n))`;;

(* ------------------------------------------------------------------------- *)
(* The main invariant.                                                       *)
(* ------------------------------------------------------------------------- *)

let TAUTOLOGOUS_INSTANCE = prove
 (`!i cl. tautologous cl ==> tautologous (IMAGE (formsubst i) cl)`,
  REWRITE_TAC[tautologous; IN_IMAGE] THEN
  MESON_TAC[FORMSUBST_NEGATE]);;

let NONTAUTOLOGOUS_SUBSUMES = prove
 (`cl subsumes cl' /\ ~(tautologous cl') ==> ~(tautologous cl)`,
  REWRITE_TAC[subsumes; SUBSET; tautologous; IN_IMAGE] THEN
  MESON_TAC[FORMSUBST_NEGATE]);;

let ALLNTRESOLVENTS_STEP = prove
 (`(!c. c IN B ==> clause(c)) /\
   (!c. c IN C ==> clause(c))
   ==> ((allntresolvents B (A UNION B)) UNION
        (allntresolvents C (A UNION B UNION C)))
       SUBSUMES (allntresolvents(B UNION C) (A UNION B UNION C))`,
  STRIP_TAC THEN MP_TAC ALLRESOLVENTS_STEP THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSUMES; allntresolvents; IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[NONTAUTOLOGOUS_SUBSUMES]);;

let ALLNTRESOLVENTS_UNION = prove
 (`(allntresolvents (A UNION B) C =
        (allntresolvents A C) UNION (allntresolvents B C)) /\
   (allntresolvents A (B UNION C) =
        (allntresolvents A B) UNION (allntresolvents A C))`,
  REWRITE_TAC[EXTENSION; allntresolvents; allresolvents;
              IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[]);;

let SET_OF_LIST_INSERT = prove
 (`!x s. set_of_list(insert x s) = x INSERT set_of_list(s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[insert_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[set_of_list] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN SET_TAC[]);;

let SET_OF_LIST_FILTER = prove
 (`!P l. set_of_list(FILTER P l) = {x | x IN set_of_list l /\ P x}`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; set_of_list] THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[set_of_list] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN
  ASM_MESON_TAC[]);;

let USED_SUB = prove
 (`!used unused n.
        Used(used,unused) n = set_of_list(used) UNION Sub(used,unused) n`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[Used_DEF; Unused_DEF] THEN INDUCT_TAC THEN
  REWRITE_TAC[Sub_DEF; given; UNION_EMPTY] THEN
  ABBREV_TAC `ppp = given n (used,unused)` THEN
  SUBST1_TAC(SYM(ISPEC `ppp:(form->bool)list#(form->bool)list` PAIR)) THEN
  PURE_REWRITE_TAC[step] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SET_OF_LIST_INSERT] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let GIVEN_INVARIANT = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n. (!c. c IN Used(used,unused) n ==> clause c) /\
                (!c. c IN Unused(used,unused) n ==> clause c) /\
                (!c. c IN Sub(used,unused) n ==> clause c) /\
                (Sub(used,unused) n UNION Unused(used,unused) n) SUBSUMES
                allntresolvents
                        (Sub(used,unused) n)
                        (set_of_list(used) UNION Sub(used,unused) n)`,
  let lemma1 = prove(`x INSERT s = s UNION {x}`,SET_TAC[])
  and lemma2 = prove
   (`(x INSERT s) UNION t = (s UNION (t UNION {x})) UNION (t UNION {x})`,
    SET_TAC[])
  and lemma3 = prove
   (`s UNION t = (s UNION t) UNION t`,SET_TAC[])
  and lemma4 = prove
   (`s UNION {x} = (x INSERT s) UNION {x}`,SET_TAC[])
  and lemma5 = prove
   (`(h INSERT s) UNION t = (s UNION t) UNION {h}`,SET_TAC[]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[Sub_DEF; UNION_EMPTY] THEN
    ASM_REWRITE_TAC[Unused_DEF; given; Used_DEF; IN_SET_OF_LIST; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC `allresolvents {} (Used (used,unused) 0)` THEN
    ASM_REWRITE_TAC[Unused_DEF; given; Used_DEF; IN_SET_OF_LIST] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `allresolvents {} (set_of_list used) = {}`
      SUBST1_TAC THENL
       [REWRITE_TAC[allresolvents; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY];
        REWRITE_TAC[SUBSUMES; NOT_IN_EMPTY]];
      MATCH_MP_TAC SUBSUMES_SUBSET THEN
      EXISTS_TAC `allntresolvents {} (set_of_list used)` THEN
      REWRITE_TAC[SUBSUMES_REFL] THEN
      SIMP_TAC[SUBSET; allntresolvents; IN_ELIM_THM]];
    ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_conj o concl) THEN
  REWRITE_TAC[Sub_DEF; Unused_DEF; Used_DEF; given] THEN
  ABBREV_TAC `ppp = given n (used,unused)` THEN
  SUBST1_TAC(SYM(ISPEC `ppp:(form->bool)list#(form->bool)list` PAIR)) THEN
  ABBREV_TAC `used0 = FST(ppp:(form->bool)list#(form->bool)list)` THEN
  ABBREV_TAC `unused0 = SND(ppp:(form->bool)list#(form->bool)list)` THEN
  REWRITE_TAC[FST; SND] THEN
  ABBREV_TAC `sub0 = Sub (used,unused) n` THEN STRIP_TAC THEN
  REWRITE_TAC[step] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC
   (ISPEC `unused0:(form->bool)list` list_CASES)
  THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[set_of_list; NOT_IN_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cl:form->bool`
        (X_CHOOSE_THEN `cls:(form->bool)list`
                SUBST_ALL_TAC)) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL] THEN LET_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN `clause cl` ASSUME_TAC THENL
   [UNDISCH_TAC `!c. c IN set_of_list (CONS cl cls) ==> clause c` THEN
    REWRITE_TAC[set_of_list; IN_INSERT] THEN MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[insert_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[set_of_list; IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ a /\ c ==> a /\ b /\ c`) THEN CONJ_TAC THENL
   [REWRITE_TAC[set_of_list; IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. MEM c new ==> clause c` ASSUME_TAC THENL
   [EXPAND_TAC "new" THEN REWRITE_TAC[resolvents; set_of_list] THEN
    SUBGOAL_THEN `!c. MEM c (list_of_set (allresolvents {cl}
                                (cl INSERT set_of_list used0))) <=>
                      c IN (allresolvents {cl} (cl INSERT set_of_list used0))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [MATCH_MP_TAC MEM_LIST_OF_SET THEN
      MATCH_MP_TAC ALLRESOLVENTS_FINITE THEN
      SIMP_TAC[FINITE_RULES; FINITE_SET_OF_LIST];
      MATCH_MP_TAC ALLRESOLVENTS_CLAUSE] THEN
    ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_SET_OF_LIST] THEN
    UNDISCH_TAC `!c. MEM c new ==> clause c` THEN
    SPEC_TAC(`new:(form->bool)list`,`more:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MEM] THENL
     [UNDISCH_TAC `!c. c IN set_of_list (CONS cl cls) ==> clause c` THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[INCORPORATE]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC
   `allntresolvents sub0 (set_of_list(used) UNION sub0) UNION
    allntresolvents {cl} (set_of_list(used) UNION sub0 UNION {cl})` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC;
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lemma1] THEN
    MATCH_MP_TAC ALLNTRESOLVENTS_STEP THEN
    ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY]] THEN
  GEN_REWRITE_TAC LAND_CONV [lemma2] THEN
  MATCH_MP_TAC SUBSUMES_UNION THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM lemma1] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC `sub0 UNION set_of_list(CONS (cl:form->bool) cls)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNION; IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC[SUBSUMES_REFL] THEN
    REWRITE_TAC[set_of_list] THEN ONCE_REWRITE_TAC[lemma1] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC[SUBSUMES_REFL] THEN
    UNDISCH_TAC `!c. MEM c new ==> clause c` THEN
    UNDISCH_TAC `!c. c IN set_of_list (ITLIST (incorporate cl) new cls)
                     ==> clause c` THEN
    MATCH_MP_TAC(TAUT `(b ==> a /\ c) ==> a ==> b ==> c`) THEN
    SPEC_TAC(`new:(form->bool)list`,`added:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MEM; SUBSUMES_REFL] THENL
     [UNDISCH_TAC `!c. c IN set_of_list (CONS cl cls) ==> clause c` THEN
      REWRITE_TAC[set_of_list; IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`cl:form->bool`; `h:form->bool`;
                  `ITLIST (incorporate cl) t cls`]
                 INCORPORATE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
    SIMP_TAC[IN_SET_OF_LIST] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC `set_of_list(ITLIST (incorporate cl) t cls)` THEN
    ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
  REWRITE_TAC[GSYM UNION_ASSOC] THEN
  SUBGOAL_THEN `set_of_list(used:(form->bool)list) UNION sub0 =
                set_of_list(used0)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sub0"; "used0"; "ppp"] THEN
    REWRITE_TAC[GSYM Used_DEF] THEN REWRITE_TAC[USED_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN
   `allntresolvents {cl} (set_of_list used0 UNION {cl}) =
    set_of_list(FILTER (\c. ~(tautologous c)) new)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SET_OF_LIST_FILTER] THEN EXPAND_TAC "new" THEN
    REWRITE_TAC[resolvents] THEN
    SUBGOAL_THEN `set_of_list(list_of_set
                        (allresolvents {cl}
                                       (set_of_list(CONS cl used0)))) =
                  allresolvents {cl} (set_of_list(CONS cl used0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[set_of_list] THEN
      MATCH_MP_TAC SET_OF_LIST_OF_SET THEN
      MATCH_MP_TAC ALLRESOLVENTS_FINITE THEN
      SIMP_TAC[FINITE_RULES; FINITE_SET_OF_LIST] THEN
      ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; allntresolvents; IN_ELIM_THM; set_of_list] THEN
    REWRITE_TAC[GSYM lemma1]; ALL_TAC] THEN
  UNDISCH_TAC `!c. MEM c new ==> clause c` THEN
  UNDISCH_TAC `!c. c IN set_of_list (ITLIST (incorporate cl) new cls)
                     ==> clause c` THEN
  MATCH_MP_TAC(TAUT `(b ==> a /\ c) ==> a ==> b ==> c`) THEN
  SPEC_TAC(`new:(form->bool)list`,`added:(form->bool)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MEM; FILTER] THENL
   [REWRITE_TAC[set_of_list; SUBSUMES; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `!c. c IN set_of_list (CONS cl cls) ==> clause c` THEN
    REWRITE_TAC[set_of_list; IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `tautologous h` THEN ASM_SIMP_TAC[] THENL
   [MP_TAC(SPECL [`cl:form->bool`; `h:form->bool`;
                  `ITLIST (incorporate cl) t cls`]
                 INCORPORATE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC `set_of_list (ITLIST (incorporate cl) t cls) UNION {cl}` THEN
    ASM_SIMP_TAC[SUBSUMES_UNION; SUBSUMES_REFL] THEN
    REWRITE_TAC[IN_UNION; NOT_IN_EMPTY; IN_INSERT; IN_ELIM_THM;
                IN_SET_OF_LIST] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cl:form->bool`; `h:form->bool`;
                `ITLIST (incorporate cl) t cls`]
               INCORPORATE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC
    `set_of_list(CONS h (ITLIST (incorporate cl) t cls)) UNION {cl}` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[IN_SET_OF_LIST];
    GEN_REWRITE_TAC LAND_CONV [lemma4] THEN
    ASM_SIMP_TAC[SUBSUMES_UNION; SUBSUMES_REFL];
    REWRITE_TAC[set_of_list] THEN ONCE_REWRITE_TAC[lemma5] THEN
    GEN_REWRITE_TAC RAND_CONV [lemma1] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC[SUBSUMES_REFL] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* More useful lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let SUB_MONO_SUBSET = prove
 (`!init m n. m <= n ==> (Sub init m) SUBSET (Sub init n)`,
  REPEAT GEN_TAC THEN SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
  REWRITE_TAC[Sub_DEF] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET_TRANS; SUBSET; IN_INSERT]);;

let SUB_MONO = prove
 (`!init m n. m <= n ==> (Sub init n) SUBSUMES (Sub init m)`,
  MESON_TAC[SUBSUMES_SUBSET_REFL; SUB_MONO_SUBSET]);;

let LENGTH_REPLACE = prove
 (`!cl current. LENGTH current <= LENGTH(replace cl current)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[replace] THEN
  REWRITE_TAC[LENGTH; LE_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; LE_SUC; LE_REFL]);;

let LENGTH_INCORPORATE = prove
 (`!gcl cl current. LENGTH current <= LENGTH(incorporate gcl cl current)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[incorporate] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LE_REFL; LENGTH_REPLACE]);;

let LENGTH_UNUSED_CHANGE = prove
 (`!init m n.
        LENGTH(SND(given m init)) <= LENGTH (SND(given (m + n) init)) + n`,
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`used:(form->bool)list`; `unused:(form->bool)list`] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
  REWRITE_TAC[given] THEN
  SUBST1_TAC(SYM(ISPEC `given (m + n) (used,unused)` PAIR)) THEN
  PURE_REWRITE_TAC[step] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[SND] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> m <= SUC n`] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `LENGTH (SND (given (m + n) (used,unused))) + n` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(SND (given (m + n) (used,unused)) = [])` THEN
  SPEC_TAC(`SND (given (m + n) (used,unused))`,`l:(form->bool)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TL; LENGTH] THEN
  MATCH_MP_TAC(ARITH_RULE `x <= y ==> SUC x + n <= SUC(y + n)`) THEN
  SPEC_TAC(`(resolvents (HD (CONS h t))
                (CONS (HD (CONS h t)) (FST (given (m + n) (used,unused)))))`,
           `k:(form->bool)list`) THEN
  REWRITE_TAC[HD] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; LE_REFL] THEN
  ASM_MESON_TAC[LENGTH_INCORPORATE; LE_TRANS]);;

let LENGTH_UNUSED_ZERO = prove
 (`!used unused m n.
        (SND (given m (used,unused)) = [])
        ==> (SND (given (m + n) (used,unused)) = [])`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN SIMP_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[given] THEN
  SUBST1_TAC(SYM(ISPEC `given (m + n) (used,unused)` PAIR)) THEN
  PURE_REWRITE_TAC[step] THEN ASM_SIMP_TAC[]);;

let REPLACE_SUBSUMES_SELF = prove
 (`!cl current n.
        n < LENGTH current
        ==> (EL n (replace cl current)) subsumes (EL n current)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[replace; LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[HD; TL; EL; subsumes_REFL; LT_SUC]);;

let INCORPORATE_SUBSUMES_SELF = prove
 (`!gcl cl current n.
        n < LENGTH current
        ==> (EL n (incorporate gcl cl current)) subsumes (EL n current)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[incorporate] THEN
  COND_CASES_TAC THEN REWRITE_TAC[subsumes_REFL; REPLACE_SUBSUMES_SELF]);;

let REPLACE_CLAUSE = prove
 (`!cl current.
        (!c. MEM c current ==> clause c) /\ clause cl
        ==> !c. MEM c (replace cl current) ==> clause c`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP_TAC[replace; MEM] THEN
  STRIP_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let INCORPORATE_CLAUSE = prove
 (`(!c. MEM c current ==> clause c) /\ clause cl
   ==> !c. MEM c (incorporate gcl cl current) ==> clause c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[incorporate] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REPLACE_CLAUSE]);;

let INCORPORATE_CLAUSE_EL = prove
 (`(!c. MEM c current ==> clause c) /\ clause cl /\ p < LENGTH current
   ==> clause (EL p (incorporate gcl cl current))`,
  MESON_TAC[MEM_EL; INCORPORATE_CLAUSE; LENGTH_INCORPORATE;
            LTE_TRANS]);;

let UNUSED_SUBSUMES_SELF = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !k m n. n + k < LENGTH(SND(given m (used,unused)))
                    ==> (EL n (SND(given (m + k) (used,unused))))
                    subsumes (EL (n + k) (SND(given m (used,unused))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; subsumes_REFL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SUC m`; `n:num`]) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ANTS_TAC THENL
   [MP_TAC(SPECL [`(used:(form->bool)list,unused:(form->bool)list)`;
                  `m:num`; `1`] LENGTH_UNUSED_CHANGE) THEN
    REWRITE_TAC[ADD1] THEN
    MATCH_MP_TAC(ARITH_RULE
     `SUC x < lm ==> lm <= lm1 + 1 ==> x < lm1`) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[TAUT
   `a /\ b /\ c ==> d <=> a /\ c ==> b ==> d`] subsumes_TRANS) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(EL n (SND (given (SUC (m + k)) (used,unused)))) IN
                  Unused(used,unused) (SUC(m + k))`
     (fun th -> ASM_MESON_TAC[th; GIVEN_INVARIANT]) THEN
    REWRITE_TAC[Unused_DEF; IN_SET_OF_LIST] THEN
    MATCH_MP_TAC MEM_EL THEN
    MP_TAC(SPECL [`(used:(form->bool)list,unused:(form->bool)list)`;
                  `m:num`; `SUC k`] LENGTH_UNUSED_CHANGE) THEN
    UNDISCH_TAC `SUC (n + k) < LENGTH (SND (given m (used,unused)))` THEN
    REWRITE_TAC[ADD_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[given] THEN
  SUBST1_TAC(SYM(ISPEC `given m (used,unused)` PAIR)) THEN
  PURE_REWRITE_TAC[step] THEN LET_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[SND] THENL
   [UNDISCH_TAC `SUC (n + k) < LENGTH (SND (given m (used,unused)))` THEN
    ASM_REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  UNDISCH_TAC `SUC (n + k) < LENGTH (SND (given m (used,unused)))` THEN
  SUBGOAL_THEN `!c. MEM c (SND (given m (used,unused))) ==> clause c`
  MP_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST; GSYM Unused_DEF] THEN
    ASM_MESON_TAC[GIVEN_INVARIANT]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. MEM c new ==> clause c` MP_TAC THENL
   [EXPAND_TAC "new" THEN REWRITE_TAC[resolvents; set_of_list] THEN
    ABBREV_TAC `gcl = HD (SND (given m (used,unused)))` THEN
    REWRITE_TAC[GSYM Used_DEF] THEN
    SUBGOAL_THEN `!c. MEM c (list_of_set (allresolvents {gcl}
                          (gcl INSERT Used (used,unused) m))) <=>
                      c IN (allresolvents {gcl}
                           (gcl INSERT Used (used,unused) m))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [MATCH_MP_TAC MEM_LIST_OF_SET THEN
      MATCH_MP_TAC ALLRESOLVENTS_FINITE THEN
      SIMP_TAC[FINITE_RULES; FINITE_SET_OF_LIST] THEN
      ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[FINITE_INSERT] THEN
      REWRITE_TAC[Used_DEF; FINITE_SET_OF_LIST] THEN
      REWRITE_TAC[GSYM Used_DEF];
      MATCH_MP_TAC ALLRESOLVENTS_CLAUSE THEN
      ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY]] THEN
    SUBGOAL_THEN `clause gcl`
      (fun th -> ASM_MESON_TAC[th; GIVEN_INVARIANT]) THEN
    SUBGOAL_THEN `gcl IN Unused(used,unused) m`
      (fun th -> ASM_MESON_TAC[th; GIVEN_INVARIANT]) THEN
    REWRITE_TAC[Unused_DEF; IN_SET_OF_LIST] THEN
    EXPAND_TAC "gcl" THEN
    UNDISCH_TAC `~(SND(given m (used,unused)) = [])` THEN
    SPEC_TAC(`SND(given m (used,unused))`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD]; ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `~(SND (given m (used,unused)) = [])` THEN
  SPEC_TAC(`SND(given m (used,unused))`,`l:(form->bool)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; EL; HD; TL] THEN
  REWRITE_TAC[LENGTH; LT_SUC] THEN
  UNDISCH_TAC `!c. MEM c new ==> clause c` THEN
  SPEC_TAC(`n + k:num`,`p:num`) THEN
  SPEC_TAC(`new:(form->bool)list`,`new:(form->bool)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; subsumes_REFL] THEN
  X_GEN_TAC `p:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[TAUT
   `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] subsumes_TRANS) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INCORPORATE_SUBSUMES_SELF THEN
    UNDISCH_TAC `p < LENGTH(t:(form->bool)list)` THEN
    SPEC_TAC(`t':(form->bool)list`,`k:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST] THEN
    ASM_MESON_TAC[LENGTH_INCORPORATE; LTE_TRANS]] THEN
  MATCH_MP_TAC INCORPORATE_CLAUSE_EL THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!gcl current lis.
        LENGTH(current) <= LENGTH(ITLIST (incorporate gcl) lis current)`
     (fun th -> ASM_MESON_TAC[LTE_TRANS; th]) THEN
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[ITLIST; LE_REFL] THEN
    ASM_MESON_TAC[LE_TRANS; LENGTH_INCORPORATE]] THEN
  SUBGOAL_THEN
   `!current gcl new.
        (!c. MEM c current ==> clause c) /\
        (!c. MEM c new ==> clause c)
        ==> !c. MEM c (ITLIST (incorporate gcl) new current)
                ==> clause c`
  MATCH_MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[MEM]] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST; MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[INCORPORATE_CLAUSE]);;

let SUB_SUBSUMES_UNUSED = prove
 (`(!c. MEM c used ==> clause c) /\
   (!c. MEM c unused ==> clause c)
   ==> !n. Sub(used,unused)
              (n + LENGTH(SND(given n (used,unused))))
           SUBSUMES (Sub (used,unused) n UNION Unused(used,unused) n)`,
  let lemma = prove(`x INSERT s = {x} UNION s`,SET_TAC[]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m n. Sub(used,unused) (m + n) SUBSUMES
          Sub(used,unused) m UNION
          set_of_list(FIRSTN n (SND(given m (used,unused))))`
  MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[LE_REFL; FIRSTN_TRIVIAL; Unused_DEF]] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THENL
   [REWRITE_TAC[FIRSTN; set_of_list; UNION_EMPTY; SUBSUMES_REFL]; ALL_TAC] THEN
  REWRITE_TAC[Sub_DEF] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `FIRSTN (SUC n) (SND(given m (used,unused))) =
                  FIRSTN n (SND(given m (used,unused)))`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `LENGTH(SND (given m (used,unused))) <= n`
     (fun th -> MESON_TAC[th; FIRSTN_TRIVIAL; LE_REFL;
                          ARITH_RULE `x <= n ==> x <= SUC n`]) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `LENGTH(SND (given (m + n) (used,unused))) + n` THEN
    ASM_REWRITE_TAC[LENGTH_UNUSED_CHANGE; LENGTH; ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[FIRSTN] THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[LENGTH_UNUSED_ZERO]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC
   `HD(SND (given (m + n) (used,unused))) INSERT
    (Sub (used,unused) m UNION
     set_of_list (FIRSTN n (SND (given m (used,unused)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN
     `HD(SND(given (m + n) (used,unused))) IN Unused (used,unused) (m + n)`
    MP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[GIVEN_INVARIANT]] THEN
    UNDISCH_TAC `~(SND(given (m + n) (used,unused)) = [])` THEN
    REWRITE_TAC[Unused_DEF; IN_SET_OF_LIST] THEN
    SPEC_TAC(`SND(given(m + n) (used,unused))`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUBSUMES_UNION THEN
    ASM_REWRITE_TAC[SUBSUMES_REFL]; ALL_TAC] THEN
  REWRITE_TAC[set_of_list] THEN ONCE_REWRITE_TAC[lemma] THEN
  GEN_REWRITE_TAC LAND_CONV [AC UNION_ACI
   `s UNION t UNION u = t UNION u UNION s`] THEN
  MATCH_MP_TAC SUBSUMES_UNION THEN ASM_REWRITE_TAC[SUBSUMES_REFL] THEN
  SUBGOAL_THEN
   `{(HD (SND (given m (used,unused))))} UNION
    set_of_list(FIRSTN n (TL (SND (given m (used,unused))))) =
    set_of_list(FIRSTN (SUC n) (SND (given m (used,unused))))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FIRSTN] THEN
    UNDISCH_TAC `~(SND (given m (used,unused)) = [])` THEN
    REWRITE_TAC[set_of_list] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `LENGTH(SND (given m (used,unused))) <= n`
  THENL
   [ASM_SIMP_TAC[FIRSTN_SHORT] THEN
    MATCH_MP_TAC SUBSUMES_SUBSET THEN
    EXISTS_TAC `set_of_list(FIRSTN n (SND (given m (used,unused))))` THEN
    REWRITE_TAC[SUBSUMES_REFL] THEN SIMP_TAC[SUBSET; IN_UNION]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC
   `set_of_list(FIRSTN n (SND (given m (used,unused)))) UNION
    {(EL n (SND (given m (used,unused))))}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[GSYM Unused_DEF] THEN
    REWRITE_TAC[IN_SET_OF_LIST] THEN
    X_GEN_TAC `c:form->bool` THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(MP_TAC o MATCH_MP FIRSTN_SUBLIST) THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST; GSYM Unused_DEF] THEN
      ASM_MESON_TAC[GIVEN_INVARIANT]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `(HD(SND (given (m + n) (used,unused)))) IN
      Unused(used,unused) (m + n)`
     (fun th -> ASM_MESON_TAC[th; GIVEN_INVARIANT]) THEN
    REWRITE_TAC[Unused_DEF; IN_SET_OF_LIST] THEN
    UNDISCH_TAC `~(SND (given (m + n) (used,unused)) = [])` THEN
    SPEC_TAC(`SND (given (m + n) (used,unused))`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUBSUMES_SUBSET THEN
    EXISTS_TAC `set_of_list (FIRSTN (SUC n) (SND (given m (used,unused))))` THEN
    REWRITE_TAC[SUBSUMES_REFL] THEN
    MP_TAC(GEN `x:form->bool`
     (ISPECL [`x:form->bool`; `n:num`; `SND (given m (used,unused))`]
            FIRSTN_SUC)) THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; SET_OF_LIST_APPEND; set_of_list] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_INSERT; NOT_IN_EMPTY]] THEN
  MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC[SUBSUMES_REFL] THEN
  REWRITE_TAC[SUBSUMES; IN_INSERT; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN
   `HD(SND(given (m + n) (used,unused))) subsumes
    (EL n (SND (given m (used,unused))))`
   (fun th -> MESON_TAC[th]) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT1 EL)] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ARITH_RULE `n = 0 + n`] THEN
  MP_TAC(SPECL [`used:(form->bool)list`; `unused:(form->bool)list`]
        UNUSED_SUBSUMES_SELF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `~(LENGTH (SND (given m (used,unused))) <= n)` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Separation into levels.                                                   *)
(* ------------------------------------------------------------------------- *)

let break = new_recursive_definition num_RECURSION
  `(break init 0 = LENGTH(SND(given 0 init))) /\
   (break init (SUC n) =
        break init n + LENGTH(SND(given (break init n) init)))`;;

let level = new_definition
  `level init n = Sub init (break init n)`;;

let LEVEL_0 = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> level(used,unused) 0 SUBSUMES set_of_list(unused)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUB_SUBSUMES_UNUSED) THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ADD_CLAUSES; Sub_DEF; UNION_EMPTY] THEN
  REWRITE_TAC[Unused_DEF; given; level; Sub_DEF; break]);;

let LEVEL_STEP = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n. level(used,unused) (SUC n) SUBSUMES
                allntresolvents (level(used,unused) (n))
                                (set_of_list(used) UNION
                                 level(used,unused) (n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC `Sub(used,unused) (break(used,unused) n) UNION
              Unused(used,unused) (break(used,unused) n)` THEN
  REWRITE_TAC[level] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[GIVEN_INVARIANT];
    ALL_TAC;
    ASM_MESON_TAC[GIVEN_INVARIANT]] THEN
  REWRITE_TAC[break] THEN
  ASM_SIMP_TAC[SUB_SUBSUMES_UNUSED]);;

let level_CLAUSE = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n c. c IN (level(used,unused) n) ==> clause c`,
  REWRITE_TAC[level] THEN MESON_TAC[GIVEN_INVARIANT]);;

let BREAK_MONO = prove
 (`!init m n. m <= n ==> break init m <= break init n`,
  SUBGOAL_THEN `!init m d. break init m <= break init (m + d)`
   (fun th -> MESON_TAC[th; LE_EXISTS]) THEN
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; break; LE_REFL] THEN
  ASM_MESON_TAC[LE_TRANS; LE_ADD]);;

let level_MONO_SUBSET = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !m n. m <= n
                  ==> level(used,unused) m SUBSET level(used,unused) n`,
  REWRITE_TAC[level] THEN MESON_TAC[SUB_MONO_SUBSET; BREAK_MONO]);;

let level_MONO = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !m n. m <= n
                  ==> level(used,unused) n SUBSUMES level(used,unused) m`,
  REWRITE_TAC[level] THEN MESON_TAC[SUB_MONO; BREAK_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Show how subsumption propagates through resolvents.                       *)
(* ------------------------------------------------------------------------- *)

let IMAGE_CLAUSE_EQ = prove
 (`clause p /\ (!q. qfree(q) ==> (f q = g q))
   ==> (IMAGE f p = IMAGE g p)`,
  REWRITE_TAC[clause; EXTENSION; IN_IMAGE] THEN
  MESON_TAC[QFREE_LITERAL]);;

let FORMSUBST_TERMSUBST_EQ = prove
 (`(!p. qfree(p) ==> (formsubst i p = formsubst j p)) <=>
   (termsubst i = termsubst j)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `t:term` THEN FIRST_X_ASSUM(MP_TAC o SPEC `Atom p [t]`) THEN
    REWRITE_TAC[qfree; formsubst; MAP; form_INJ; CONS_11];
    MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[qfree] THEN
    SIMP_TAC[formsubst] THEN REWRITE_TAC[form_INJ; GSYM MAP_o] THEN
    GEN_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC[o_THM; ALL_T]]);;

let ISARESOLVENT_SUBSUME_L = prove
 (`!p p' q r.
        clause p /\ clause p' /\ clause q /\
        p' subsumes p /\ isaresolvent r (p,q)
        ==> p' subsumes r \/ ?r'. isaresolvent r' (p',q) /\ r' subsumes r`,
  let lemma = prove
   (`a SUBSET a' /\ b SUBSET b' ==> (a UNION b) SUBSET (a' UNION b')`,
    SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `isaresolvent r (p,q)` THEN
  GEN_REWRITE_TAC LAND_CONV [isaresolvent] THEN
  ABBREV_TAC `q' = IMAGE (formsubst (rename q (FVS p))) q` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p1:form->bool`; `q1':form->bool`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  LET_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `ri = rename q (FVS p)` THEN
  UNDISCH_TAC `p' subsumes p` THEN REWRITE_TAC[subsumes] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num->term`) THEN
  ASM_CASES_TAC `(IMAGE (formsubst j) p') INTER p1 = {}` THENL
   [DISJ1_TAC THEN EXISTS_TAC `termsubst i o (j:num->term)` THEN
    SUBGOAL_THEN
     `IMAGE (formsubst (termsubst i o j)) p' =
      IMAGE (formsubst i o formsubst j) p'`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
      ASM_MESON_TAC[FORMSUBST_FORMSUBST; clause; QFREE_LITERAL]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN
    EXPAND_TAC "r" THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(p:form->bool) DIFF p1` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    UNDISCH_TAC `IMAGE (formsubst j) p' SUBSET p` THEN
    UNDISCH_TAC `IMAGE (formsubst j) p' INTER p1 = {}` THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_DIFF; IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[]; ALL_TAC] THEN
  DISJ2_TAC THEN
  ABBREV_TAC `p1' = {x | x IN p' /\ (formsubst j x IN p1)}` THEN
  SUBGOAL_THEN `(IMAGE (formsubst j) p1') SUBSET p1 /\ ~(p1' = {})`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p1'" THEN
    UNDISCH_TAC `~(p1:form->bool = {})` THEN
    UNDISCH_TAC `IMAGE (formsubst j) p' SUBSET p` THEN
    UNDISCH_TAC `~(IMAGE (formsubst j) p' INTER p1 = {})` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; SUBSET;
                IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `si = rename q (FVS p')` THEN
  ABBREV_TAC `q'' = IMAGE (formsubst si) q` THEN
  MP_TAC(SPECL [`q:form->bool`; `FVS(p)`] rename) THEN
  ASM_SIMP_TAC[FVS_CLAUSE_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[renaming] THEN
  DISCH_THEN(X_CHOOSE_THEN `ri':num->term` MP_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM; I_DEF; o_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`q:form->bool`; `FVS(p')`] rename) THEN
  ASM_SIMP_TAC[FVS_CLAUSE_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[renaming] THEN
  DISCH_THEN(X_CHOOSE_THEN `si':num->term` MP_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM; I_DEF; o_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `q1'' = IMAGE (formsubst si o formsubst ri') q1'` THEN
  SUBGOAL_THEN `(q1'':form->bool) SUBSET q''` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q''"; "q1''"] THEN
    UNDISCH_TAC `q1':form->bool SUBSET q'` THEN EXPAND_TAC "q'" THEN
    DISCH_THEN(MP_TAC o ISPEC `formsubst si o formsubst ri'` o
               MATCH_MP IMAGE_SUBSET) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC IMAGE_CLAUSE_EQ THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[o_THM; FORMSUBST_FORMSUBST] THEN
    REWRITE_TAC[FORMSUBST_TERMSUBST_EQ] THEN
    REWRITE_TAC[FUN_EQ_THM; GSYM TERMSUBST_TERMSUBST] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `i' = \x. if x IN FVS(q'')
                       then termsubst i (termsubst ri (si' x))
                       else termsubst i (j x)` THEN
  SUBGOAL_THEN `Unifies i' (p1' UNION {~~p | p IN q1''})` ASSUME_TAC THENL
   [UNDISCH_THEN
     `(\x. if x IN FVS q''
            then termsubst i (termsubst ri (si' x))
            else termsubst i (j x)) =
       i'` (SUBST_ALL_TAC o SYM) THEN
    MP_TAC(SPEC `p1 UNION {~~ p | p IN q1'}` MGU) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_UNION] THEN
      SUBGOAL_THEN `{~~p | p IN q1'} = IMAGE (~~) q1'` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET; clause; IMAGE_FORMSUBST_CLAUSE;
                      FINITE_IMAGE];
        REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[QFREE_NEGATE] THEN
        ASM_MESON_TAC[clause; SUBSET; QFREE_LITERAL;
                      IMAGE_FORMSUBST_CLAUSE]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[UNIFIES] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `P:form` THEN
    REWRITE_TAC[IN_UNION] THEN
    REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    MATCH_MP_TAC(TAUT `(a ==> a') /\ (b ==> b') ==> a /\ b ==> a' /\ b'`) THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC `x:form` THEN EXPAND_TAC "p1'" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `formsubst (termsubst i o j) x` THEN CONJ_TAC THENL
       [ALL_TAC;
        SUBGOAL_THEN `qfree x` MP_TAC THENL
         [ASM_MESON_TAC[clause; QFREE_LITERAL]; ALL_TAC] THEN
        SIMP_TAC[GSYM FORMSUBST_FORMSUBST] THEN ASM_SIMP_TAC[]] THEN
      MATCH_MP_TAC FORMSUBST_VALUATION THEN
      X_GEN_TAC `z:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(z IN FVS q'')`
        (fun th -> REWRITE_TAC[th; o_THM]) THEN
      UNDISCH_TAC `FVS q'' INTER FVS p' = {}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `z:num`) THEN
      MATCH_MP_TAC(TAUT `b ==> ~(a /\ b) ==> ~a`) THEN
      REWRITE_TAC[FVS; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:form` THEN REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:form` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
    EXPAND_TAC "q1''" THEN REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `u:form` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN DISCH_TAC THEN
    REWRITE_TAC[FORMSUBST_NEGATE] THEN
    SUBGOAL_THEN `formsubst i (~~u) = P` (SUBST1_TAC o SYM) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORMSUBST_NEGATE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `qfree u` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; clause; IMAGE_FORMSUBST_CLAUSE; QFREE_LITERAL];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `formsubst (termsubst i o termsubst ri o si')
                          (formsubst si (formsubst ri' u))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[FORMSUBST_FORMSUBST] THEN
      UNDISCH_TAC `qfree u` THEN SPEC_TAC(`u:form`,`u:form`) THEN
      ONCE_REWRITE_TAC[FORMSUBST_TERMSUBST_EQ] THEN
      REWRITE_TAC[o_ASSOC] THEN REWRITE_TAC[GSYM TERMSUBST_TERMSUBST_o] THEN
      REWRITE_TAC[TERMSUBST_TERMSUBST_o] THEN
      ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]] THEN
    MATCH_MP_TAC FORMSUBST_VALUATION THEN X_GEN_TAC `z:num` THEN
    DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `z IN FVS q''` (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(formsubst si (formsubst ri' u)) IN q''` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[FVS; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]] THEN
    EXPAND_TAC "q''" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `formsubst ri' u` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `u:form IN q'` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "q'" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:form` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `formsubst ri' (formsubst ri x) = formsubst V x`
     (fun th -> ASM_REWRITE_TAC[th; FORMSUBST_TRIV]) THEN
    SUBGOAL_THEN `qfree x` MP_TAC THENL
     [ASM_MESON_TAC[clause; QFREE_LITERAL]; ALL_TAC] THEN
    SPEC_TAC(`x:form`,`x:form`) THEN
    SIMP_TAC[FORMSUBST_FORMSUBST] THEN
    ONCE_REWRITE_TAC[FORMSUBST_TERMSUBST_EQ] THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; GSYM TERMSUBST_TERMSUBST; TERMSUBST_TRIV];
    ALL_TAC] THEN
  MP_TAC(SPEC `p1' UNION {~~p | p IN q1''}` MGU) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONJ_ASSOC] THEN
    CONJ_TAC THENL
     [ALL_TAC; EXISTS_TAC `i':num->term` THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN
    SUBGOAL_THEN `{~~p | p IN q1''} = IMAGE (~~) q1''` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL
       [ALL_TAC;
        ASM_MESON_TAC[FINITE_SUBSET; clause; IMAGE_FORMSUBST_CLAUSE;
                    IMAGE_o; FINITE_IMAGE]] THEN
      SUBGOAL_THEN `p1':form->bool SUBSET p'`
        (fun th ->
           ASM_MESON_TAC[th; FINITE_SUBSET; clause; QFREE_LITERAL]) THEN
      EXPAND_TAC "p1'" THEN SIMP_TAC[SUBSET; IN_ELIM_THM];
      ALL_TAC] THEN
    EXPAND_TAC "p1'" THEN REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[QFREE_NEGATE] THEN
    ASM_MESON_TAC[clause; SUBSET; QFREE_LITERAL;
                  IMAGE_FORMSUBST_CLAUSE];
    ALL_TAC] THEN
  ABBREV_TAC `k = mgu (p1' UNION {~~p | p IN q1''})` THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (formsubst k) ((p' DIFF p1') UNION (q'' DIFF q1''))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[isaresolvent] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    MAP_EVERY EXISTS_TAC [`p1':form->bool`; `q1'':form->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "p1'" THEN SIMP_TAC[IN_ELIM_THM; SUBSET];
      EXPAND_TAC "q1''" THEN UNDISCH_TAC `~(q1':form->bool = {})` THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_IMAGE] THEN MESON_TAC[];
      EXISTS_TAC `i':num->term` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "r" THEN EXISTS_TAC `i':num->term` THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (formsubst i') (p' DIFF p1' UNION q'' DIFF q1'')` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i':num->term`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!x. x IN (p' DIFF p1' UNION q'' DIFF q1'') ==> qfree x`
     (fun th -> REWRITE_TAC[SUBSET; IN_IMAGE; o_THM] THEN MESON_TAC[th]) THEN
    REWRITE_TAC[IN_DIFF; IN_UNION] THEN
    ASM_MESON_TAC[IMAGE_FORMSUBST_CLAUSE; clause; QFREE_LITERAL]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION] THEN MATCH_MP_TAC lemma THEN CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (formsubst i') (p' DIFF p1') =
                  IMAGE (formsubst (termsubst i o j)) (p' DIFF p1')`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `!x. x IN p' ==> (formsubst i' x = formsubst (termsubst i o j) x)`
       (fun th -> REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF] THEN
                  MESON_TAC[th]) THEN
      X_GEN_TAC `x:form` THEN
      DISCH_TAC THEN MATCH_MP_TAC FORMSUBST_VALUATION THEN
      X_GEN_TAC `z:num` THEN DISCH_TAC THEN EXPAND_TAC "i'" THEN
      SUBGOAL_THEN `~(z IN FVS q'')` (fun th -> REWRITE_TAC[th; o_THM]) THEN
      UNDISCH_TAC `FVS q'' INTER FVS p' = {}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `z:num`) THEN
      MATCH_MP_TAC(TAUT `b ==> ~(a /\ b) ==> ~a`) THEN
      REWRITE_TAC[FVS; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (formsubst (termsubst i o j)) (p' DIFF p1') =
                  IMAGE (formsubst i o formsubst j) (p' DIFF p1')`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; o_THM] THEN
      ASM_MESON_TAC[FORMSUBST_FORMSUBST; clause; QFREE_LITERAL]; ALL_TAC] THEN
    EXPAND_TAC "p1'" THEN UNDISCH_TAC `IMAGE (formsubst j) p' SUBSET p` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_DIFF; IN_ELIM_THM; o_THM] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (formsubst i') (q'' DIFF q1'') =
    IMAGE (formsubst (termsubst i o termsubst ri o si')) (q'' DIFF q1'')`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `!x. x IN q''
          ==> (formsubst i' x = formsubst (termsubst i o termsubst ri o si') x)`
     (fun th -> REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF] THEN
                MESON_TAC[th]) THEN
    X_GEN_TAC `x:form` THEN
    DISCH_TAC THEN MATCH_MP_TAC FORMSUBST_VALUATION THEN
    X_GEN_TAC `z:num` THEN DISCH_TAC THEN EXPAND_TAC "i'" THEN
    SUBGOAL_THEN `z IN FVS q''` (fun th -> REWRITE_TAC[th; o_THM]) THEN
    REWRITE_TAC[FVS; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (formsubst (termsubst i o termsubst ri o si')) (q'' DIFF q1'') =
    IMAGE (formsubst i o formsubst ri o formsubst si') (q'' DIFF q1'')`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    SUBGOAL_THEN
     `(!q. qfree q ==> (formsubst (termsubst i o termsubst ri o si') q =
                        (formsubst i o formsubst ri o formsubst si') q)) /\
      (!q. q IN (q'' DIFF q1'') ==> qfree q)`
     (fun th -> MESON_TAC[th]) THEN
    CONJ_TAC THENL
     [SIMP_TAC[o_THM; FORMSUBST_FORMSUBST] THEN
      ONCE_REWRITE_TAC[FORMSUBST_TERMSUBST_EQ] THEN
      REWRITE_TAC[o_ASSOC] THEN REWRITE_TAC[GSYM TERMSUBST_TERMSUBST_o] THEN
      REWRITE_TAC[TERMSUBST_TERMSUBST_o];
      ALL_TAC] THEN
    ASM_MESON_TAC[IN_DIFF; IMAGE_FORMSUBST_CLAUSE; clause; QFREE_LITERAL];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  MAP_EVERY EXPAND_TAC ["q''"; "q1''"; "q'"] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_DIFF; o_THM] THEN
  X_GEN_TAC `u:form` THEN
  DISCH_THEN(X_CHOOSE_THEN `v:form` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:form`
   (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `formsubst si' (formsubst si w) = formsubst V w`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `qfree w` MP_TAC THENL
     [ASM_MESON_TAC[clause; QFREE_LITERAL]; ALL_TAC] THEN
    SPEC_TAC(`w:form`,`w:form`) THEN
    SIMP_TAC[FORMSUBST_FORMSUBST] THEN
    ONCE_REWRITE_TAC[FORMSUBST_TERMSUBST_EQ] THEN
    ASM_REWRITE_TAC[GSYM TERMSUBST_TERMSUBST; FUN_EQ_THM; TERMSUBST_TRIV];
    ALL_TAC] THEN
  REWRITE_TAC[FORMSUBST_TRIV] THEN
  MATCH_MP_TAC(TAUT `b /\ (c ==> a) ==> ~a ==> b /\ ~c`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `formsubst ri w` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM FORMSUBST_TRIV] THEN
  SUBGOAL_THEN `qfree w` MP_TAC THENL
   [ASM_MESON_TAC[clause; QFREE_LITERAL]; ALL_TAC] THEN
  SPEC_TAC(`w:form`,`w:form`) THEN
  SIMP_TAC[FORMSUBST_FORMSUBST] THEN
  ONCE_REWRITE_TAC[FORMSUBST_TERMSUBST_EQ] THEN
  ASM_REWRITE_TAC[GSYM TERMSUBST_TERMSUBST; FUN_EQ_THM] THEN
  REWRITE_TAC[TERMSUBST_TRIV]);;

let ISARESOLVENT_SUBSUME_R = prove
 (`!p q q' r.
        clause p /\ clause q /\ clause q' /\
        q' subsumes q /\ isaresolvent r (p,q)
        ==> q' subsumes r \/ ?r'. isaresolvent r' (p,q') /\ r' subsumes r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:form->bool`; `p:form->bool`; `r:form->bool`]
               ISARESOLVENT_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':form->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`q:form->bool`; `q':form->bool`; `p:form->bool`;
                `r':form->bool`] ISARESOLVENT_SUBSUME_L) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [DISJ1_TAC THEN MATCH_MP_TAC subsumes_TRANS THEN
    EXISTS_TAC `r':form->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r'':form->bool` STRIP_ASSUME_TAC) THEN
  DISJ2_TAC THEN
  MP_TAC(SPECL [`p:form->bool`; `q':form->bool`; `r'':form->bool`]
               ISARESOLVENT_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  ASM MESON_TAC[ISARESOLVENT_CLAUSE; subsumes_TRANS]);;

let ISARESOLVENT_SUBSUME = prove
 (`!p p' q q' r.
        clause p /\ clause p' /\ clause q /\ clause q' /\
        p' subsumes p /\ q' subsumes q /\ isaresolvent r (p,q)
        ==> p' subsumes r \/ q' subsumes r \/
            ?r'. isaresolvent r' (p',q') /\ r' subsumes r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:form->bool`; `q:form->bool`;
                `q':form->bool`; `r:form->bool`] ISARESOLVENT_SUBSUME_R) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':form->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`p:form->bool`; `p':form->bool`;
                `q':form->bool`; `r':form->bool`] ISARESOLVENT_SUBSUME_L) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[subsumes_TRANS; ISARESOLVENT_CLAUSE]);;

let ALLRESOLVENTS_SUBSUME_L = prove
 (`!s t u.
      (!c. c IN s ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN u ==> clause c) /\
      s SUBSUMES t
      ==> (s UNION (allresolvents s u)) SUBSUMES (allresolvents t u)`,
  REWRITE_TAC[SUBSUMES; IN_UNION; allresolvents; IN_ELIM_THM] THEN
  MESON_TAC[ISARESOLVENT_SUBSUME_L; subsumes_REFL]);;

let ALLRESOLVENTS_SUBSUME_R = prove
 (`!s t u.
      (!c. c IN s ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN u ==> clause c) /\
      t SUBSUMES u
      ==> (t UNION (allresolvents s t)) SUBSUMES (allresolvents s u)`,
  REWRITE_TAC[SUBSUMES; IN_UNION; allresolvents; IN_ELIM_THM] THEN
  MESON_TAC[ISARESOLVENT_SUBSUME_R; subsumes_REFL]);;

let ALLRESOLVENTS_SUBSUME = prove
 (`!s t s' t'.
      (!c. c IN s ==> clause c) /\
      (!c. c IN s' ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN t' ==> clause c) /\
      s SUBSUMES s' /\ t SUBSUMES t'
      ==> (s UNION t UNION (allresolvents s t)) SUBSUMES
          (allresolvents s' t')`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC `s UNION (allresolvents s t')` THEN
  ASM_SIMP_TAC[ALLRESOLVENTS_SUBSUME_L; ALLRESOLVENTS_SUBSUME_R;
               SUBSUMES_UNION; SUBSUMES_REFL; IN_UNION] THEN
  ASM_MESON_TAC[ALLRESOLVENTS_CLAUSE]);;

(* ------------------------------------------------------------------------- *)
(* Show how the tautology elimination doesn't hurt us.                       *)
(* ------------------------------------------------------------------------- *)

let ISARESOLVENT_TAUTOLOGY_L = prove
 (`!p q r.
      clause p /\ clause q /\
      tautologous(p) /\ isaresolvent r (p,q)
      ==> tautologous(r) \/ q subsumes r`,
  let lemma = prove
   (`{~~p | p IN s} = IMAGE (~~) s`,
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[tautologous; isaresolvent] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `x:form` STRIP_ASSUME_TAC) MP_TAC) THEN
  ABBREV_TAC `q' = IMAGE (formsubst (rename q (FVS p))) q` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p1:form->bool`; `q1':form->bool`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  LET_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  ASM_CASES_TAC `x IN (p DIFF p1) /\ ~~x IN (p DIFF p1)` THENL
   [DISJ1_TAC THEN EXISTS_TAC `formsubst i x` THEN
    EXPAND_TAC "r" THEN REWRITE_TAC[GSYM FORMSUBST_NEGATE] THEN
    REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNION] THEN
    ASM_MESON_TAC[IN_DIFF]; ALL_TAC] THEN
  ABBREV_TAC `k = rename q (FVS p)` THEN
  DISJ2_TAC THEN ASM_CASES_TAC `x:form IN p1` THENL
   [REWRITE_TAC[subsumes] THEN
    EXISTS_TAC `termsubst i o (k:num->term)` THEN
    MP_TAC(SPEC `p1 UNION {~~p | p IN q1'}` MGU) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[lemma; FINITE_UNION] THEN
        ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET; clause; SUBSET; IN_DIFF];
        REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[QFREE_NEGATE] THEN
        ASM_MESON_TAC[QFREE_LITERAL; clause; SUBSET; IN_IMAGE;
                        IMAGE_FORMSUBST_CLAUSE]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[Unifies_DEF; IN_UNION; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      MP_TAC(SPECL [`x:form`; `~~x`] th)) THEN
    REWRITE_TAC[FORMSUBST_NEGATE; NEGATE_REFL; ASSUME `x:form IN p1`] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!y. y IN q1' ==> (formsubst i (~~y) = formsubst i x)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE(formsubst (termsubst i o k)) q =
      IMAGE (formsubst i o formsubst k) q`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
      ASM_MESON_TAC[clause; FORMSUBST_FORMSUBST; QFREE_LITERAL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `!y. y IN q1' ==> (formsubst i y = formsubst i (~~x))`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC `!y. y IN q1' ==> (formsubst i (~~ y) = formsubst i x)` THEN
      DISCH_THEN(MP_TAC o SPEC `y:form`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `(~~)`) THEN
      REWRITE_TAC[GSYM FORMSUBST_NEGATE] THEN
      ASM_MESON_TAC[NEGATE_NEGATE; clause; IMAGE_FORMSUBST_CLAUSE; SUBSET];
      ALL_TAC] THEN
    EXPAND_TAC "r" THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_DIFF; IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~~x IN p1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_DIFF]; ALL_TAC] THEN
  REWRITE_TAC[subsumes] THEN
  EXISTS_TAC `termsubst i o (k:num->term)` THEN
  MP_TAC(SPEC `p1 UNION {~~p | p IN q1'}` MGU) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[lemma; FINITE_UNION] THEN
      ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET; clause; SUBSET; IN_DIFF];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[QFREE_NEGATE] THEN
      ASM_MESON_TAC[QFREE_LITERAL; clause; SUBSET; IN_IMAGE;
                      IMAGE_FORMSUBST_CLAUSE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[Unifies_DEF; IN_UNION; IN_ELIM_THM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(SPECL [`~~x`; `x:form`] th)) THEN
  REWRITE_TAC[FORMSUBST_NEGATE; NEGATE_REFL; ASSUME `~~x IN p1`] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN q1' ==> (formsubst i (~~y) = formsubst i (~~x))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE(formsubst (termsubst i o k)) q =
    IMAGE (formsubst i o formsubst k) q`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
    ASM_MESON_TAC[clause; FORMSUBST_FORMSUBST; QFREE_LITERAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  SUBGOAL_THEN `!y. y IN q1' ==> (formsubst i y = formsubst i x)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!y. y IN q1' ==> (formsubst i (~~y) = formsubst i (~~x))` THEN
    DISCH_THEN(MP_TAC o SPEC `y:form`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(~~)`) THEN
    REWRITE_TAC[GSYM FORMSUBST_NEGATE] THEN
    SUBGOAL_THEN `literal x /\ literal y`
      (fun th -> MESON_TAC[NEGATE_NEGATE; th]) THEN
    ASM_MESON_TAC[clause; IMAGE_FORMSUBST_CLAUSE; SUBSET];
    ALL_TAC] THEN
  EXPAND_TAC "r" THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_DIFF; IN_UNION] THEN ASM_MESON_TAC[]);;

let TAUTOLOGOUS_SUBSUMES = prove
 (`!p q. p subsumes q /\ tautologous(p) ==> tautologous(q)`,
  MESON_TAC[subsumes; tautologous; SUBSET; TAUTOLOGOUS_INSTANCE]);;

let ISARESOLVENT_TAUTOLOGY_R = prove
 (`!p q r.
      clause p /\ clause q /\
      tautologous(p) /\ isaresolvent r (q,p)
      ==> tautologous(r) \/ q subsumes r`,
  MESON_TAC[ISARESOLVENT_SYM; ISARESOLVENT_TAUTOLOGY_L; subsumes_TRANS;
            TAUTOLOGOUS_SUBSUMES]);;

(* ------------------------------------------------------------------------- *)
(* Show that everything in the levels comes from initial unused or one of    *)
(* the new resolvents generated. Hence, unless it was in the initial unused, *)
(* it will be detected if we just scan the new resolvents each cycle.        *)
(* ------------------------------------------------------------------------- *)

let REPLACE_FROMNEW = prove
 (`!cl lis c. MEM c (replace cl lis) ==> MEM c lis \/ (c = cl)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[replace] THEN
  SIMP_TAC[MEM] THEN GEN_TAC THEN COND_CASES_TAC THEN
  SIMP_TAC[MEM] THEN ASM_MESON_TAC[]);;

let INCORPORATE_FROMNEW = prove
 (`!gcl cl lis c.
        MEM c (incorporate gcl cl lis) ==> MEM c lis \/ (c = cl)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[incorporate] THEN COND_CASES_TAC THEN
  MESON_TAC[REPLACE_FROMNEW]);;

let ITLIST_INCORPORATE_FROMNEW = prove
 (`!gcl lis new c.
        MEM c (ITLIST (incorporate gcl) new lis)
        ==> MEM c new \/ MEM c lis`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST; MEM] THEN ASM_MESON_TAC[INCORPORATE_FROMNEW]);;

let UNUSED_FROMNEW = prove
 (`!used unused c n.
        MEM c (SND(given n (used,unused)))
        ==> MEM c unused \/
            ?m. m < n /\
                MEM c (resolvents
                         (HD(SND(given m (used,unused))))
                         (CONS (HD(SND(given m (used,unused))))
                               (FST(given m (used,unused)))))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[given] THEN
  SUBST1_TAC(SYM(ISPEC `given n (used,unused)` PAIR)) THEN
  PURE_REWRITE_TAC[step] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [ASM_MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]; ALL_TAC] THEN
  LET_TAC THEN REWRITE_TAC[SND] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ITLIST_INCORPORATE_FROMNEW) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[LT]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM c (SND (given n (used,unused)))`
   (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th))
  THENL
   [UNDISCH_TAC `MEM c (TL (SND (given n (used,unused))))` THEN
    UNDISCH_TAC `~(SND (given n (used,unused)) = [])` THEN
    SPEC_TAC(`SND (given n (used,unused))`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN SIMP_TAC[MEM; TL]; ALL_TAC] THEN
  MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]);;

let SUB_FROMNEW = prove
 (`!used unused c n.
        c IN Sub(used,unused) n
        ==> MEM c unused \/
            ?m. m < n /\
                MEM c (resolvents
                         (HD(SND(given m (used,unused))))
                         (CONS (HD(SND(given m (used,unused))))
                               (FST(given m (used,unused)))))`,
  let lemma = prove
   (`!l. ~(l = []) ==> MEM (HD l) l`,
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD]) in
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[Sub_DEF; NOT_IN_EMPTY] THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]] THEN
  SUBGOAL_THEN `MEM c (SND(given n (used,unused)))`
   (fun th -> MP_TAC(MATCH_MP UNUSED_FROMNEW th))
  THENL [ALL_TAC; MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]] THEN
  UNDISCH_TAC `~(SND (given n (used,unused)) = [])` THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`SND (given n (used,unused))`,`l:(form->bool)list`) THEN
  LIST_INDUCT_TAC THEN SIMP_TAC[MEM; TL; HD]);;

let LEVEL_FROMNEW = prove
 (`!used unused c n.
        c IN level(used,unused) n
        ==> MEM c unused \/
            ?m. MEM c (resolvents
                         (HD(SND(given m (used,unused))))
                         (CONS (HD(SND(given m (used,unused))))
                               (FST(given m (used,unused)))))`,
  REWRITE_TAC[level] THEN MESON_TAC[SUB_FROMNEW]);;
