(* ========================================================================= *)
(* Trivial adaptation of given clause algorithm to semantic resolution.      *)
(* ========================================================================= *)

let HOLDS_INTERP_SUBSUME = prove
 (`clause cl /\ clause cl' /\ (!v. holds M v (interp cl)) /\ cl subsumes cl'
   ==> !v:num->A. holds M v (interp cl')`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [subsumes]) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num->term` MP_TAC) THEN
  UNDISCH_TAC `!v:num->A. holds M v (interp cl)` THEN
  ASM_SIMP_TAC[CLAUSE_FINITE; HOLDS_INTERP] THEN
  MESON_TAC[IN_IMAGE; SUBSET; HOLDS_FORMSUBST]);;

(* ------------------------------------------------------------------------- *)
(* Following is tied to particular model domain for simplicity (only).       *)
(* ------------------------------------------------------------------------- *)

let isaresolvent_sem = new_definition
  `isaresolvent_sem M cl (c1,c2) <=>
        isaresolvent cl (c1,c2) /\
        (~(!v:num->num. holds M v (interp c1)) \/
         ~(!v. holds M v (interp c2)))`;;

(* ------------------------------------------------------------------------- *)
(* Set of all semantic resolvents.                                           *)
(* ------------------------------------------------------------------------- *)

let allresolvents_sem = new_definition
  `allresolvents_sem M s1 s2 =
        {c | ?c1 c2. c1 IN s1 /\ c2 IN s2 /\ isaresolvent_sem M c (c1,c2)}`;;

(* ------------------------------------------------------------------------- *)
(* Non-tautological semantic resolvents.                                     *)
(* ------------------------------------------------------------------------- *)

let allntresolvents_sem = new_definition
  `allntresolvents_sem M s1 s2 =
        {r | r IN allresolvents_sem M s1 s2 /\ ~(tautologous r)}`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let ISARESOLVENT_SEM_SYM = prove
 (`!c1 c2 cl.
        clause c1 /\ clause c2 /\ isaresolvent_sem M cl (c2,c1)
        ==> ?cl'. isaresolvent_sem M cl' (c1,c2) /\ cl' subsumes cl`,
  REWRITE_TAC[isaresolvent_sem] THEN MESON_TAC[ISARESOLVENT_SYM]);;

let ALLRESOLVENTS_SEM_SYM = prove
 (`(!c. c IN A ==> clause c) /\ (!c. c IN B ==> clause c)
   ==> (allresolvents_sem M A B) SUBSUMES (allresolvents_sem M B A)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSUMES; allresolvents_sem; IN_ELIM_THM] THEN
  X_GEN_TAC `cl:form->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:form->bool`
        (X_CHOOSE_THEN `c1:form->bool` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `c1:form->bool` THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `c2:form->bool` THEN
  ASM_SIMP_TAC[ISARESOLVENT_SEM_SYM]);;

let ALLRESOLVENTS_SEM_UNION = prove
 (`(allresolvents_sem M (A UNION B) C =
        (allresolvents_sem M A C) UNION (allresolvents_sem M B C)) /\
   (allresolvents_sem M A (B UNION C) =
        (allresolvents_sem M A B) UNION (allresolvents_sem M A C))`,
  REWRITE_TAC[EXTENSION; allresolvents_sem; IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[]);;

let ALLRESOLVENTS_SEM_STEP = prove
 (`(!c. c IN B ==> clause(c)) /\
   (!c. c IN C ==> clause(c))
   ==> ((allresolvents_sem M B (A UNION B)) UNION
        (allresolvents_sem M C (A UNION B UNION C)))
       SUBSUMES (allresolvents_sem M(B UNION C) (A UNION B UNION C))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ALLRESOLVENTS_SEM_UNION; UNION_ASSOC] THEN
  ONCE_REWRITE_TAC[AC UNION_ACI
   `a UNION b UNION c UNION d UNION e UNION f =
    a UNION b UNION d UNION (c UNION e) UNION f`] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV) [AC UNION_ACI
   `A UNION B = (A UNION A) UNION B`] THEN
  REPEAT(MATCH_MP_TAC SUBSUMES_UNION THEN ASM_REWRITE_TAC[SUBSUMES_REFL]) THEN
  ASM_SIMP_TAC[ALLRESOLVENTS_SEM_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Asymmetric list-based version used in algorithm.                          *)
(* ------------------------------------------------------------------------- *)

let resolvents_sem = new_definition
  `resolvents_sem M cl cls =
        list_of_set(allresolvents_sem M {cl} (set_of_list cls))`;;

(* ------------------------------------------------------------------------- *)
(* Trivial lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

let ISARESOLVENT_SEM_CLAUSE = prove
 (`!p q r. clause p /\ clause q /\ isaresolvent_sem M r (p,q) ==> clause r`,
  MESON_TAC[isaresolvent_sem; ISARESOLVENT_CLAUSE]);;

let ALLRESOLVENTS_SEM_CLAUSE = prove
 (`(!c. c IN s ==> clause c) /\ (!c. c IN t ==> clause c)
   ==> !c. c IN allresolvents_sem M s t ==> clause c`,
  REWRITE_TAC[allresolvents_sem; IN_ELIM_THM] THEN
  MESON_TAC[ISARESOLVENT_SEM_CLAUSE]);;

let ISARESOLVENT_SEM_FINITE = prove
 (`!c1 c2. clause(c1) /\ clause(c2)
           ==> FINITE {c | isaresolvent_sem M c (c1,c2)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c | isaresolvent c (c1,c2)}` THEN
  ASM_SIMP_TAC[ISARESOLVENT_FINITE] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; isaresolvent_sem]);;

let ALLRESOLVENTS_SEM_FINITE = prove
 (`!s t. FINITE(s) /\ FINITE(t) /\
         (!c. c IN s ==> clause c) /\
         (!c. c IN t ==> clause c)
         ==> FINITE(allresolvents_sem M s t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `allresolvents s t` THEN
  ASM_SIMP_TAC[ALLRESOLVENTS_FINITE] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; isaresolvent_sem;
           allresolvents_sem; allresolvents] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic given clause algorithm.                                             *)
(* ------------------------------------------------------------------------- *)

let step_sem = new_definition
  `step_sem M (used,unused) =
        if unused = [] then (used,unused) else
        let new = resolvents_sem M (HD unused) (CONS (HD unused) used) in
        (insert (HD unused) used,
         ITLIST (incorporate (HD unused)) new (TL unused))`;;

let STEP_SEM = prove
 (`(step_sem M(used,[]) = (used,[])) /\
   (step_sem M(used,CONS cl cls) =
        let new = resolvents_sem M cl (CONS cl used) in
        insert cl used,ITLIST (incorporate cl) new cls)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [step_sem] THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL]);;

let given_sem = new_recursive_definition num_RECURSION
  `(given_sem M 0 p = p) /\
   (given_sem M (SUC n) p = step_sem M (given_sem M n p))`;;

(* ------------------------------------------------------------------------- *)
(* Separation into bits simplifies things a bit.                             *)
(* ------------------------------------------------------------------------- *)

let Used_SEM = new_definition
  `Used_SEM M init n = set_of_list(FST(given_sem M n init))`;;

let Unused_SEM = new_definition
  `Unused_SEM M init n = set_of_list(SND(given_sem M n init))`;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary concept actually has the cleanest recursion equations.          *)
(* ------------------------------------------------------------------------- *)

let Sub_SEM = new_recursive_definition num_RECURSION
  `(Sub_SEM M init 0 = {}) /\
   (Sub_SEM M init (SUC n) =
        if SND(given_sem M n init) = [] then Sub_SEM M init n
        else HD(SND(given_sem M n init)) INSERT (Sub_SEM M init n))`;;

(* ------------------------------------------------------------------------- *)
(* The main invariant.                                                       *)
(* ------------------------------------------------------------------------- *)

let ALLNTRESOLVENTS_SEM_STEP = prove
 (`(!c. c IN B ==> clause(c)) /\
   (!c. c IN C ==> clause(c))
   ==> ((allntresolvents_sem M B (A UNION B)) UNION
        (allntresolvents_sem M C (A UNION B UNION C)))
       SUBSUMES (allntresolvents_sem M (B UNION C) (A UNION B UNION C))`,
  STRIP_TAC THEN MP_TAC ALLRESOLVENTS_SEM_STEP THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSUMES; allntresolvents_sem; IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[NONTAUTOLOGOUS_SUBSUMES]);;

let ALLNTRESOLVENTS_SEM_UNION = prove
 (`(allntresolvents_sem M (A UNION B) C =
        (allntresolvents_sem M A C) UNION (allntresolvents_sem M B C)) /\
   (allntresolvents_sem M A (B UNION C) =
        (allntresolvents_sem M A B) UNION (allntresolvents_sem M A C))`,
  REWRITE_TAC[EXTENSION; allntresolvents_sem; allresolvents_sem;
              IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[]);;

let USED_SUB = prove
 (`!used unused n.
        Used_SEM M(used,unused) n =
        set_of_list(used) UNION Sub_SEM M (used,unused) n`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[Used_SEM; Unused_SEM] THEN INDUCT_TAC THEN
  REWRITE_TAC[Sub_SEM; given_sem; UNION_EMPTY] THEN
  ABBREV_TAC `ppp = given_sem M n (used,unused)` THEN
  SUBST1_TAC(SYM(ISPEC `ppp:(form->bool)list#(form->bool)list` PAIR)) THEN
  PURE_REWRITE_TAC[step_sem] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SET_OF_LIST_INSERT] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let GIVEN_INVARIANT = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n. (!c. c IN Used_SEM M(used,unused) n ==> clause c) /\
                (!c. c IN Unused_SEM M(used,unused) n ==> clause c) /\
                (!c. c IN Sub_SEM M (used,unused) n ==> clause c) /\
                (Sub_SEM M (used,unused) n UNION Unused_SEM M(used,unused) n)
                 SUBSUMES
                 allntresolvents_sem M
                         (Sub_SEM M (used,unused) n)
                         (set_of_list(used) UNION Sub_SEM M (used,unused) n)`,
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
   [REWRITE_TAC[Sub_SEM; UNION_EMPTY] THEN
    ASM_REWRITE_TAC[Unused_SEM; given_sem; Used_SEM;
                    IN_SET_OF_LIST; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC `allresolvents_sem M {} (Used_SEM M (used,unused) 0)` THEN
    ASM_REWRITE_TAC[Unused_SEM; given_sem; Used_SEM; IN_SET_OF_LIST] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `allresolvents_sem M {} (set_of_list used) = {}`
      SUBST1_TAC THENL
       [REWRITE_TAC[allresolvents_sem; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY];
        REWRITE_TAC[SUBSUMES; NOT_IN_EMPTY]];
      MATCH_MP_TAC SUBSUMES_SUBSET THEN
      EXISTS_TAC `allntresolvents_sem M {} (set_of_list used)` THEN
      REWRITE_TAC[SUBSUMES_REFL] THEN
      SIMP_TAC[SUBSET; allntresolvents_sem; IN_ELIM_THM]];
    ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_conj o concl) THEN
  REWRITE_TAC[Sub_SEM; Unused_SEM; Used_SEM; given_sem] THEN
  ABBREV_TAC `ppp = given_sem M n (used,unused)` THEN
  SUBST1_TAC(SYM(ISPEC `ppp:(form->bool)list#(form->bool)list` PAIR)) THEN
  ABBREV_TAC `used0 = FST(ppp:(form->bool)list#(form->bool)list)` THEN
  ABBREV_TAC `unused0 = SND(ppp:(form->bool)list#(form->bool)list)` THEN
  REWRITE_TAC[FST; SND] THEN
  ABBREV_TAC `sub0 = Sub_SEM M (used,unused) n` THEN STRIP_TAC THEN
  REWRITE_TAC[step_sem] THEN
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
   [EXPAND_TAC "new" THEN REWRITE_TAC[resolvents_sem; set_of_list] THEN
    SUBGOAL_THEN `!c. MEM c (list_of_set (allresolvents_sem M {cl}
                                (cl INSERT set_of_list used0))) <=>
                      c IN (allresolvents_sem M {cl}
                             (cl INSERT set_of_list used0))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [MATCH_MP_TAC MEM_LIST_OF_SET THEN
      MATCH_MP_TAC ALLRESOLVENTS_SEM_FINITE THEN
      SIMP_TAC[FINITE_RULES; FINITE_SET_OF_LIST];
      MATCH_MP_TAC ALLRESOLVENTS_SEM_CLAUSE] THEN
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
   `allntresolvents_sem M sub0 (set_of_list(used) UNION sub0) UNION
    allntresolvents_sem M {cl} (set_of_list(used) UNION sub0 UNION {cl})` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC;
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lemma1] THEN
    MATCH_MP_TAC ALLNTRESOLVENTS_SEM_STEP THEN
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
    REWRITE_TAC[GSYM Used_SEM] THEN REWRITE_TAC[USED_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN
   `allntresolvents_sem M {cl} (set_of_list used0 UNION {cl}) =
    set_of_list(FILTER (\c. ~(tautologous c)) new)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SET_OF_LIST_FILTER] THEN EXPAND_TAC "new" THEN
    REWRITE_TAC[resolvents_sem] THEN
    SUBGOAL_THEN `set_of_list(list_of_set
                        (allresolvents_sem M {cl}
                                       (set_of_list(CONS cl used0)))) =
                  allresolvents_sem M {cl} (set_of_list(CONS cl used0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[set_of_list] THEN
      MATCH_MP_TAC SET_OF_LIST_OF_SET THEN
      MATCH_MP_TAC ALLRESOLVENTS_SEM_FINITE THEN
      SIMP_TAC[FINITE_RULES; FINITE_SET_OF_LIST] THEN
      ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; allntresolvents_sem; IN_ELIM_THM; set_of_list] THEN
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
 (`!init m n. m <= n ==> (Sub_SEM M init m) SUBSET (Sub_SEM M init n)`,
  REPEAT GEN_TAC THEN SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
  REWRITE_TAC[Sub_SEM] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET_TRANS; SUBSET; IN_INSERT]);;

let SUB_MONO = prove
 (`!init m n. m <= n ==> (Sub_SEM M init n) SUBSUMES (Sub_SEM M init m)`,
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
        LENGTH(SND(given_sem M m init))
        <= LENGTH (SND(given_sem M (m + n) init)) + n`,
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`used:(form->bool)list`; `unused:(form->bool)list`] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
  REWRITE_TAC[given_sem] THEN
  SUBST1_TAC(SYM(ISPEC `given_sem M (m + n) (used,unused)` PAIR)) THEN
  PURE_REWRITE_TAC[step_sem] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[SND] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> m <= SUC n`] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `LENGTH (SND (given_sem M (m + n) (used,unused))) + n` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(SND (given_sem M (m + n) (used,unused)) = [])` THEN
  SPEC_TAC(`SND (given_sem M (m + n) (used,unused))`,`l:(form->bool)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TL; LENGTH] THEN
  MATCH_MP_TAC(ARITH_RULE `x <= y ==> SUC x + n <= SUC(y + n)`) THEN
  SPEC_TAC(`(resolvents_sem M (HD (CONS h t))
                (CONS (HD (CONS h t))
                      (FST (given_sem M (m + n) (used,unused)))))`,
           `k:(form->bool)list`) THEN
  REWRITE_TAC[HD] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; LE_REFL] THEN
  ASM_MESON_TAC[LENGTH_INCORPORATE; LE_TRANS]);;

let LENGTH_UNUSED_ZERO = prove
 (`!used unused m n.
        (SND (given_sem M m (used,unused)) = [])
        ==> (SND (given_sem M (m + n) (used,unused)) = [])`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN SIMP_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[given_sem] THEN
  SUBST1_TAC(SYM(ISPEC `given_sem M (m + n) (used,unused)` PAIR)) THEN
  PURE_REWRITE_TAC[step_sem] THEN ASM_SIMP_TAC[]);;

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
        ==> !k m n. n + k < LENGTH(SND(given_sem M m (used,unused)))
                    ==> (EL n (SND(given_sem M (m + k) (used,unused))))
                    subsumes (EL (n + k) (SND(given_sem M m (used,unused))))`,
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
   [SUBGOAL_THEN `(EL n (SND (given_sem M (SUC (m + k)) (used,unused)))) IN
                  Unused_SEM M(used,unused) (SUC(m + k))`
     (fun th -> ASM_MESON_TAC[th; GIVEN_INVARIANT]) THEN
    REWRITE_TAC[Unused_SEM; IN_SET_OF_LIST] THEN
    MATCH_MP_TAC MEM_EL THEN
    MP_TAC(SPECL [`(used:(form->bool)list,unused:(form->bool)list)`;
                  `m:num`; `SUC k`] LENGTH_UNUSED_CHANGE) THEN
    UNDISCH_TAC `SUC (n + k) < LENGTH (SND (given_sem M m (used,unused)))` THEN
    REWRITE_TAC[ADD_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[given_sem] THEN
  SUBST1_TAC(SYM(ISPEC `given_sem M m (used,unused)` PAIR)) THEN
  PURE_REWRITE_TAC[step_sem] THEN LET_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[SND] THENL
   [UNDISCH_TAC `SUC (n + k) < LENGTH (SND (given_sem M m (used,unused)))` THEN
    ASM_REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  UNDISCH_TAC `SUC (n + k) < LENGTH (SND (given_sem M m (used,unused)))` THEN
  SUBGOAL_THEN `!c. MEM c (SND (given_sem M m (used,unused))) ==> clause c`
  MP_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST; GSYM Unused_SEM] THEN
    ASM_MESON_TAC[GIVEN_INVARIANT]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. MEM c new ==> clause c` MP_TAC THENL
   [EXPAND_TAC "new" THEN REWRITE_TAC[resolvents_sem; set_of_list] THEN
    ABBREV_TAC `gcl = HD (SND (given_sem M m (used,unused)))` THEN
    REWRITE_TAC[GSYM Used_SEM] THEN
    SUBGOAL_THEN `!c. MEM c (list_of_set (allresolvents_sem M {gcl}
                          (gcl INSERT Used_SEM M (used,unused) m))) <=>
                      c IN (allresolvents_sem M {gcl}
                           (gcl INSERT Used_SEM M (used,unused) m))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [MATCH_MP_TAC MEM_LIST_OF_SET THEN
      MATCH_MP_TAC ALLRESOLVENTS_SEM_FINITE THEN
      SIMP_TAC[FINITE_RULES; FINITE_SET_OF_LIST] THEN
      ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[FINITE_INSERT] THEN
      REWRITE_TAC[Used_SEM; FINITE_SET_OF_LIST] THEN
      REWRITE_TAC[GSYM Used_SEM];
      MATCH_MP_TAC ALLRESOLVENTS_SEM_CLAUSE THEN
      ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY]] THEN
    SUBGOAL_THEN `clause gcl`
      (fun th -> ASM_MESON_TAC[th; GIVEN_INVARIANT]) THEN
    SUBGOAL_THEN `gcl IN Unused_SEM M(used,unused) m`
      (fun th -> ASM_MESON_TAC[th; GIVEN_INVARIANT]) THEN
    REWRITE_TAC[Unused_SEM; IN_SET_OF_LIST] THEN
    EXPAND_TAC "gcl" THEN
    UNDISCH_TAC `~(SND(given_sem M m (used,unused)) = [])` THEN
    SPEC_TAC(`SND(given_sem M m (used,unused))`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD]; ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `~(SND (given_sem M m (used,unused)) = [])` THEN
  SPEC_TAC(`SND(given_sem M m (used,unused))`,`l:(form->bool)list`) THEN
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
   ==> !n. Sub_SEM M (used,unused)
              (n + LENGTH(SND(given_sem M n (used,unused))))
           SUBSUMES (Sub_SEM M (used,unused) n UNION
                     Unused_SEM M(used,unused) n)`,
  let lemma = prove(`x INSERT s = {x} UNION s`,SET_TAC[]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m n. Sub_SEM M (used,unused) (m + n) SUBSUMES
          Sub_SEM M (used,unused) m UNION
          set_of_list(FIRSTN n (SND(given_sem M m (used,unused))))`
  MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[LE_REFL; FIRSTN_TRIVIAL; Unused_SEM]] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THENL
   [REWRITE_TAC[FIRSTN; set_of_list; UNION_EMPTY; SUBSUMES_REFL]; ALL_TAC] THEN
  REWRITE_TAC[Sub_SEM] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `FIRSTN (SUC n) (SND(given_sem M m (used,unused))) =
                  FIRSTN n (SND(given_sem M m (used,unused)))`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `LENGTH(SND (given_sem M m (used,unused))) <= n`
     (fun th -> MESON_TAC[th; FIRSTN_TRIVIAL; LE_REFL;
                          ARITH_RULE `x <= n ==> x <= SUC n`]) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `LENGTH(SND (given_sem M (m + n) (used,unused))) + n` THEN
    ASM_REWRITE_TAC[LENGTH_UNUSED_CHANGE; LENGTH; ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[FIRSTN] THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[LENGTH_UNUSED_ZERO]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC
   `HD(SND (given_sem M (m + n) (used,unused))) INSERT
    (Sub_SEM M (used,unused) m UNION
     set_of_list (FIRSTN n (SND (given_sem M m (used,unused)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN
     `HD(SND(given_sem M (m + n) (used,unused))) IN
      Unused_SEM M (used,unused) (m + n)`
    MP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[GIVEN_INVARIANT]] THEN
    UNDISCH_TAC `~(SND(given_sem M (m + n) (used,unused)) = [])` THEN
    REWRITE_TAC[Unused_SEM; IN_SET_OF_LIST] THEN
    SPEC_TAC(`SND(given_sem M(m + n) (used,unused))`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUBSUMES_UNION THEN
    ASM_REWRITE_TAC[SUBSUMES_REFL]; ALL_TAC] THEN
  REWRITE_TAC[set_of_list] THEN ONCE_REWRITE_TAC[lemma] THEN
  GEN_REWRITE_TAC LAND_CONV [AC UNION_ACI
   `s UNION t UNION u = t UNION u UNION s`] THEN
  MATCH_MP_TAC SUBSUMES_UNION THEN ASM_REWRITE_TAC[SUBSUMES_REFL] THEN
  SUBGOAL_THEN
   `{(HD (SND (given_sem M m (used,unused))))} UNION
    set_of_list(FIRSTN n (TL (SND (given_sem M m (used,unused))))) =
    set_of_list(FIRSTN (SUC n) (SND (given_sem M m (used,unused))))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FIRSTN] THEN
    UNDISCH_TAC `~(SND (given_sem M m (used,unused)) = [])` THEN
    REWRITE_TAC[set_of_list] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `LENGTH(SND (given_sem M m (used,unused))) <= n`
  THENL
   [ASM_SIMP_TAC[FIRSTN_SHORT] THEN
    MATCH_MP_TAC SUBSUMES_SUBSET THEN
    EXISTS_TAC `set_of_list(FIRSTN n (SND (given_sem M m (used,unused))))` THEN
    REWRITE_TAC[SUBSUMES_REFL] THEN SIMP_TAC[SUBSET; IN_UNION]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC
   `set_of_list(FIRSTN n (SND (given_sem M m (used,unused)))) UNION
    {(EL n (SND (given_sem M m (used,unused))))}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[GSYM Unused_SEM] THEN
    REWRITE_TAC[IN_SET_OF_LIST] THEN
    X_GEN_TAC `c:form->bool` THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(MP_TAC o MATCH_MP FIRSTN_SUBLIST) THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST; GSYM Unused_SEM] THEN
      ASM_MESON_TAC[GIVEN_INVARIANT]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `(HD(SND (given_sem M (m + n) (used,unused)))) IN
      Unused_SEM M(used,unused) (m + n)`
     (fun th -> ASM_MESON_TAC[th; GIVEN_INVARIANT]) THEN
    REWRITE_TAC[Unused_SEM; IN_SET_OF_LIST] THEN
    UNDISCH_TAC `~(SND (given_sem M (m + n) (used,unused)) = [])` THEN
    SPEC_TAC(`SND (given_sem M (m + n) (used,unused))`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUBSUMES_SUBSET THEN
    EXISTS_TAC
     `set_of_list (FIRSTN (SUC n) (SND (given_sem M m (used,unused))))` THEN
    REWRITE_TAC[SUBSUMES_REFL] THEN
    MP_TAC(GEN `x:form->bool`
     (ISPECL [`x:form->bool`; `n:num`; `SND (given_sem M m (used,unused))`]
            FIRSTN_SUC)) THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; SET_OF_LIST_APPEND; set_of_list] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_INSERT; NOT_IN_EMPTY]] THEN
  MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC[SUBSUMES_REFL] THEN
  REWRITE_TAC[SUBSUMES; IN_INSERT; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN
   `HD(SND(given_sem M (m + n) (used,unused))) subsumes
    (EL n (SND (given_sem M m (used,unused))))`
   (fun th -> MESON_TAC[th]) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT1 EL)] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ARITH_RULE `n = 0 + n`] THEN
  MP_TAC(SPECL [`used:(form->bool)list`; `unused:(form->bool)list`]
        UNUSED_SUBSUMES_SELF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `~(LENGTH (SND (given_sem M m (used,unused))) <= n)` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Separation into levels.                                                   *)
(* ------------------------------------------------------------------------- *)

let break_sem = new_recursive_definition num_RECURSION
  `(break_sem M init 0 = LENGTH(SND(given_sem M 0 init))) /\
   (break_sem M init (SUC n) =
        break_sem M init n +
        LENGTH(SND(given_sem M (break_sem M init n) init)))`;;

let level_sem = new_definition
  `level_sem M init n = Sub_SEM M init (break_sem M init n)`;;

let LEVEL_0 = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> level_sem M (used,unused) 0 SUBSUMES set_of_list(unused)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUB_SUBSUMES_UNUSED) THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ADD_CLAUSES; Sub_SEM; UNION_EMPTY] THEN
  REWRITE_TAC[Unused_SEM; given_sem; level_sem; Sub_SEM; break_sem]);;

let LEVEL_STEP = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n. level_sem M (used,unused) (SUC n) SUBSUMES
                allntresolvents_sem M (level_sem M (used,unused) (n))
                                (set_of_list(used) UNION
                                 level_sem M (used,unused) (n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC `Sub_SEM M (used,unused) (break_sem M(used,unused) n) UNION
              Unused_SEM M(used,unused) (break_sem M(used,unused) n)` THEN
  REWRITE_TAC[level_sem] THEN
(**** why does ASM_SIMP_TAC[GIVEN_INVARIANT] seem to loop??? ***)
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[GIVEN_INVARIANT];
    ALL_TAC;
    ASM_MESON_TAC[GIVEN_INVARIANT]] THEN
  REWRITE_TAC[break_sem] THEN
  ASM_SIMP_TAC[SUB_SUBSUMES_UNUSED]);;

let level_CLAUSE = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n c. c IN (level_sem M (used,unused) n) ==> clause c`,
  REWRITE_TAC[level_sem] THEN MESON_TAC[GIVEN_INVARIANT]);;

let BREAK_MONO = prove
 (`!init m n. m <= n ==> break_sem M init m <= break_sem M init n`,
  SUBGOAL_THEN `!init m d. break_sem M init m <= break_sem M init (m + d)`
   (fun th -> MESON_TAC[th; LE_EXISTS]) THEN
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; break_sem; LE_REFL] THEN
  ASM_MESON_TAC[LE_TRANS; LE_ADD]);;

let level_MONO_SUBSET = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !m n. m <= n
                  ==> level_sem M (used,unused) m SUBSET level_sem M (used,unused) n`,
  REWRITE_TAC[level_sem] THEN MESON_TAC[SUB_MONO_SUBSET; BREAK_MONO]);;

let level_MONO = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !m n. m <= n
                  ==> level_sem M (used,unused) n SUBSUMES level_sem M (used,unused) m`,
  REWRITE_TAC[level_sem] THEN MESON_TAC[SUB_MONO; BREAK_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Show how subsumption propagates through resolvents_sem.                    *)
(* ------------------------------------------------------------------------- *)

let ISARESOLVENT_SEM_SUBSUME_L = prove
 (`!p p' q r.
        clause p /\ clause p' /\ clause q /\
        p' subsumes p /\ isaresolvent_sem M r (p,q)
        ==> p' subsumes r \/
            ?r'. isaresolvent_sem M r' (p',q) /\ r' subsumes r`,
  REWRITE_TAC[isaresolvent_sem] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[HOLDS_INTERP_SUBSUME; ISARESOLVENT_SUBSUME_L]);;

let ISARESOLVENT_SEM_SUBSUME_R = prove
 (`!p q q' r.
        clause p /\ clause q /\ clause q' /\
        q' subsumes q /\ isaresolvent_sem M r (p,q)
        ==> q' subsumes r \/
            ?r'. isaresolvent_sem M r' (p,q') /\ r' subsumes r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:form->bool`; `p:form->bool`; `r:form->bool`]
               ISARESOLVENT_SEM_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':form->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`q:form->bool`; `q':form->bool`; `p:form->bool`;
                `r':form->bool`] ISARESOLVENT_SEM_SUBSUME_L) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [DISJ1_TAC THEN MATCH_MP_TAC subsumes_TRANS THEN
    EXISTS_TAC `r':form->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r'':form->bool` STRIP_ASSUME_TAC) THEN
  DISJ2_TAC THEN
  MP_TAC(SPECL [`p:form->bool`; `q':form->bool`; `r'':form->bool`]
               ISARESOLVENT_SEM_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  ASM MESON_TAC[ISARESOLVENT_SEM_CLAUSE; subsumes_TRANS]);;

let ISARESOLVENT_SEM_SUBSUME = prove
 (`!p p' q q' r.
        clause p /\ clause p' /\ clause q /\ clause q' /\
        p' subsumes p /\ q' subsumes q /\ isaresolvent_sem M r (p,q)
        ==> p' subsumes r \/ q' subsumes r \/
            ?r'. isaresolvent_sem M r' (p',q') /\ r' subsumes r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:form->bool`; `q:form->bool`;
                `q':form->bool`; `r:form->bool`]
               ISARESOLVENT_SEM_SUBSUME_R) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':form->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`p:form->bool`; `p':form->bool`;
                `q':form->bool`; `r':form->bool`]
               ISARESOLVENT_SEM_SUBSUME_L) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[subsumes_TRANS; ISARESOLVENT_SEM_CLAUSE]);;

let ALLRESOLVENTS_SEM_SUBSUME_L = prove
 (`!s t u.
      (!c. c IN s ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN u ==> clause c) /\
      s SUBSUMES t
      ==> (s UNION (allresolvents_sem M s u)) SUBSUMES
          (allresolvents_sem M t u)`,
  REWRITE_TAC[SUBSUMES; IN_UNION; allresolvents_sem; IN_ELIM_THM] THEN
  MESON_TAC[ISARESOLVENT_SEM_SUBSUME_L; subsumes_REFL]);;

let ALLRESOLVENTS_SEM_SUBSUME_R = prove
 (`!s t u.
      (!c. c IN s ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN u ==> clause c) /\
      t SUBSUMES u
      ==> (t UNION (allresolvents_sem M s t)) SUBSUMES
          (allresolvents_sem M s u)`,
  REWRITE_TAC[SUBSUMES; IN_UNION; allresolvents_sem; IN_ELIM_THM] THEN
  MESON_TAC[ISARESOLVENT_SEM_SUBSUME_R; subsumes_REFL]);;

let ALLRESOLVENTS_SEM_SUBSUME = prove
 (`!s t s' t'.
      (!c. c IN s ==> clause c) /\
      (!c. c IN s' ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN t' ==> clause c) /\
      s SUBSUMES s' /\ t SUBSUMES t'
      ==> (s UNION t UNION (allresolvents_sem M s t)) SUBSUMES
          (allresolvents_sem M s' t')`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSUMES_TRANS THEN
  EXISTS_TAC `s UNION (allresolvents_sem M s t')` THEN
  ASM_SIMP_TAC[ALLRESOLVENTS_SEM_SUBSUME_L; ALLRESOLVENTS_SEM_SUBSUME_R;
               SUBSUMES_UNION; SUBSUMES_REFL; IN_UNION] THEN
  ASM_MESON_TAC[ALLRESOLVENTS_SEM_CLAUSE]);;

(* ------------------------------------------------------------------------- *)
(* Show how the tautology elimination doesn't hurt us.                       *)
(* ------------------------------------------------------------------------- *)

let ISARESOLVENT_SEM_TAUTOLOGY_L = prove
 (`!p q r.
      clause p /\ clause q /\
      tautologous(p) /\ isaresolvent_sem M r (p,q)
      ==> tautologous(r) \/ q subsumes r`,
  MESON_TAC[isaresolvent_sem; ISARESOLVENT_TAUTOLOGY_L]);;

let TAUTOLOGOUS_SUBSUMES = prove
 (`!p q. p subsumes q /\ tautologous(p) ==> tautologous(q)`,
  MESON_TAC[subsumes; tautologous; SUBSET; TAUTOLOGOUS_INSTANCE]);;

let ISARESOLVENT_SEM_TAUTOLOGY_R = prove
 (`!p q r.
      clause p /\ clause q /\
      tautologous(p) /\ isaresolvent_sem M r (q,p)
      ==> tautologous(r) \/ q subsumes r`,
  MESON_TAC[ISARESOLVENT_SEM_SYM; ISARESOLVENT_SEM_TAUTOLOGY_L; subsumes_TRANS;
            TAUTOLOGOUS_SUBSUMES]);;

(* ------------------------------------------------------------------------- *)
(* Show that everything in the levels comes from initial unused or one of    *)
(* the new resolvents generated. Hence, unless it was in the initial unused, *)
(* it will be detected if we just scan the new resolvents each cycle.        *)
(* ------------------------------------------------------------------------- *)

let UNUSED_FROMNEW = prove
 (`!used unused c n.
        MEM c (SND(given_sem M n (used,unused)))
        ==> MEM c unused \/
            ?m. m < n /\
                MEM c (resolvents_sem M
                         (HD(SND(given_sem M m (used,unused))))
                         (CONS (HD(SND(given_sem M m (used,unused))))
                               (FST(given_sem M m (used,unused)))))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN SIMP_TAC[given_sem] THEN
  SUBST1_TAC(SYM(ISPEC `given_sem M n (used,unused)` PAIR)) THEN
  PURE_REWRITE_TAC[step_sem] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [ASM_MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]; ALL_TAC] THEN
  LET_TAC THEN REWRITE_TAC[SND] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ITLIST_INCORPORATE_FROMNEW) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[LT]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM c (SND (given_sem M n (used,unused)))`
   (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th))
  THENL
   [UNDISCH_TAC `MEM c (TL (SND (given_sem M n (used,unused))))` THEN
    UNDISCH_TAC `~(SND (given_sem M n (used,unused)) = [])` THEN
    SPEC_TAC(`SND (given_sem M n (used,unused))`,`l:(form->bool)list`) THEN
    LIST_INDUCT_TAC THEN SIMP_TAC[MEM; TL]; ALL_TAC] THEN
  MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]);;

let SUB_FROMNEW = prove
 (`!used unused c n.
        c IN Sub_SEM M (used,unused) n
        ==> MEM c unused \/
            ?m. m < n /\
                MEM c (resolvents_sem M
                         (HD(SND(given_sem M m (used,unused))))
                         (CONS (HD(SND(given_sem M m (used,unused))))
                               (FST(given_sem M m (used,unused)))))`,
  let lemma = prove
   (`!l. ~(l = []) ==> MEM (HD l) l`,
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD]) in
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[Sub_SEM; NOT_IN_EMPTY] THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]] THEN
  SUBGOAL_THEN `MEM c (SND(given_sem M n (used,unused)))`
   (fun th -> MP_TAC(MATCH_MP UNUSED_FROMNEW th))
  THENL [ALL_TAC; MESON_TAC[ARITH_RULE `x < n ==> x < SUC n`]] THEN
  UNDISCH_TAC `~(SND (given_sem M n (used,unused)) = [])` THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`SND (given_sem M n (used,unused))`,`l:(form->bool)list`) THEN
  LIST_INDUCT_TAC THEN SIMP_TAC[MEM; TL; HD]);;

let LEVEL_FROMNEW = prove
 (`!used unused c n.
        c IN level_sem M (used,unused) n
        ==> MEM c unused \/
            ?m. MEM c (resolvents_sem M
                         (HD(SND(given_sem M m (used,unused))))
                         (CONS (HD(SND(given_sem M m (used,unused))))
                               (FST(given_sem M m (used,unused)))))`,
  REWRITE_TAC[level_sem] THEN MESON_TAC[SUB_FROMNEW]);;
