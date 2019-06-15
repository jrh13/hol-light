(* ========================================================================= *)
(* Set-of-support resolution.                                                *)
(* ========================================================================= *)

let NEGATE_LITERAL = prove
 (`!q. literal q ==> literal(~~q)`,
  REWRITE_TAC[literal; ATOM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[ATOM; NEGATE_ATOM; NEGATE_NEG]);;

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
(* We need induction on size of proof; hence incorporate sizes.              *)
(* ------------------------------------------------------------------------- *)

let npresproof_RULES,npresproof_INDUCT,npresproof_CASES =
  new_inductive_definition
   `(!cl. cl IN hyps ==> npresproof hyps cl 1) /\
    (!p n1 n2 cl1 cl2.
                npresproof hyps cl1 n1 /\
                npresproof hyps cl2 n2 /\
                p IN cl1 /\
                ~~ p IN cl2
                ==> npresproof hyps (resolve p cl1 cl2) (n1 + n2 + 1))`;;

let NPRESPROOF = prove
 (`!hyps cl. presproof hyps cl <=> ?n. npresproof hyps cl n`,
  GEN_TAC THEN REWRITE_TAC[TAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`] THEN
  REWRITE_TAC[FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC presproof_INDUCT THEN MESON_TAC[npresproof_RULES];
    MATCH_MP_TAC npresproof_INDUCT THEN MESON_TAC[presproof_RULES]]);;

let NPRESPROOF_CLAUSE = prove
  (`!hyps cl n. (!c. c IN hyps ==> clause c) /\ npresproof hyps cl n
                ==> clause cl`,
   MESON_TAC[NPRESPROOF; PRESPROOF_CLAUSE]);;

(* ------------------------------------------------------------------------- *)
(* Proofs with a given set of support.                                       *)
(* ------------------------------------------------------------------------- *)

let psresproof_RULES,psresproof_INDUCT,psresproof_CASES =
  new_inductive_definition
   `(!c. c IN hyps /\ ~(tautologous c)
         ==> psresproof hyps sos (c IN sos) c) /\
    (!c1 c2 s1 s2 p.
        psresproof hyps sos s1 c1 /\
        psresproof hyps sos s2 c2 /\
        p IN c1 /\ ~~p IN c2 /\ (s1 \/ s2) /\ ~tautologous(resolve p c1 c2)
        ==> psresproof hyps sos T (resolve p c1 c2))`;;

(* ------------------------------------------------------------------------- *)
(* Transformation theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let PSRESPROOF_CLAUSE = prove
 (`!hyps sos. (!c. c IN hyps ==> clause(c))
              ==> !s cl. psresproof hyps sos s cl ==> clause cl`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC psresproof_INDUCT THEN ASM_SIMP_TAC[RESOLVE_CLAUSE]);;

let SUPPORT_ASYMMETRIC = prove
 (`!hyps sos A B C p q nb nc.
      (!c. c IN hyps ==> clause c /\ ~tautologous c) /\
      ~tautologous(resolve p A (resolve q B C)) /\
      psresproof hyps sos T A /\
      npresproof (hyps DIFF sos) B nb /\
      npresproof (hyps DIFF sos) C nc /\
      p IN A /\ ~~p IN (resolve q B C) /\ q IN B /\ ~~ q IN C /\
      ~~p IN B /\ ~(q = ~~p) /\
      (!m. m < nb + nc + 1
              ==> (!c1 c2 p.
                       psresproof hyps sos T c1 /\
                       npresproof (hyps DIFF sos) c2 m /\
                       p IN c1 /\
                       ~~ p IN c2 /\
                       ~tautologous (resolve p c1 c2)
                       ==> (?cl'. cl' SUBSET resolve p c1 c2 /\
                                  (psresproof hyps sos T cl' \/
                                   (?m'. m' < m /\
                                         npresproof (hyps DIFF sos) cl' m')))))
      ==> ?cl'. cl' SUBSET resolve p A (resolve q B C) /\
                (psresproof hyps sos T cl' \/
                 ?m. m < nb + nc + 1 /\ npresproof (hyps DIFF sos) cl' m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `clause A /\ clause B /\ clause C` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PSRESPROOF_CLAUSE; NPRESPROOF_CLAUSE; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `literal p /\ literal q` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[clause]; ALL_TAC] THEN
  ASM_CASES_TAC `tautologous (resolve q B C)` THENL
   [ASM_MESON_TAC[RESOLVE_TAUT_R; RESOLVE_CLAUSE; clause]; ALL_TAC] THEN
  ASM_CASES_TAC `p:form = q` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(resolve q A C) SUBSET (resolve q A (resolve q B C))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RESOLVE_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      ASM_MESON_TAC[RESOLVE_TAUT_L; tautologous]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `nc < nb + nc + 1`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`A:form->bool`; `C:form->bool`; `q:form`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_TAUT]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET_TRANS; ARITH_RULE `x < c ==> x < b + c + 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(~~p IN C)
    ==> (resolve q (resolve p A B) C) SUBSET (resolve p A (resolve q B C))`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`p:form IN A`; `~~p IN B`; `~~p IN resolve q B C`;
      `q:form IN B`; `~~q IN C`] THEN
    REWRITE_TAC[resolve; IN_UNION; IN_DELETE; SUBSET] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~~p IN C ==> (resolve p A (resolve q (resolve p A B) C)) SUBSET
                 (resolve p A (resolve q B C))`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`p:form IN A`; `~~p IN B`; `~~p IN resolve q B C`;
      `q:form IN B`; `~~q IN C`] THEN
    REWRITE_TAC[resolve; IN_UNION; IN_DELETE; SUBSET] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~~p IN C ==> ~~p IN (resolve q (resolve p A B) C)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`p:form IN A`; `~~p IN B`; `~~p IN resolve q B C`;
      `q:form IN B`; `~~q IN C`; `~(q = ~~ p)`; `~(p:form = q)`] THEN
    REWRITE_TAC[resolve; IN_UNION; IN_DELETE; SUBSET] THEN
    ASM_MESON_TAC[NEGATE_NEGATE]; ALL_TAC] THEN
  ASM_CASES_TAC `tautologous(resolve q (resolve p A B) C)` THENL
   [SUBGOAL_THEN `~~p IN C`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ASM_MESON_TAC[RESOLVE_TAUT_R; SUBSET_TRANS; RESOLVE_CLAUSE; SUBSET_TAUT];
    ALL_TAC] THEN
  ASM_CASES_TAC `tautologous(resolve p A B)` THENL
   [ASM_CASES_TAC `~~p IN C` THENL
     [REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `~~p IN C`))) THEN
      SUBGOAL_THEN `(resolve p A C) SUBSET (resolve p A (resolve q B C))`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS;
                      RESOLVE_TAUT_L; RESOLVE_CLAUSE]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `nc < nb + nc + 1`)) THEN
      DISCH_THEN(MP_TAC o
        SPECL [`A:form->bool`; `C:form->bool`; `p:form`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[SUBSET_TAUT]; ALL_TAC] THEN
      ASM_MESON_TAC[SUBSET_TRANS; ARITH_RULE `x < nc ==> x < nb + nc + 1`];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `~(~~p IN C)`))) THEN
    ASM_MESON_TAC[SUBSET_TRANS; RESOLVE_TAUT_L; RESOLVE_CLAUSE; ARITH_RULE
        `nc < nb + nc + 1`];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `nb:num`) THEN
  REWRITE_TAC[ARITH_RULE `nb < nb + nc + 1`] THEN
  DISCH_THEN(MP_TAC o SPECL [`A:form->bool`; `B:form->bool`; `p:form`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:form->bool` (CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_CASES_TAC `q:form IN D` THENL
   [ALL_TAC;
    EXISTS_TAC `D:form->bool` THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`D SUBSET resolve p A B`; `~(q:form IN D)`;
        `~(~~ p IN C)
         ==> resolve q (resolve p A B) C SUBSET
             resolve p A (resolve q B C)`] THEN
      REWRITE_TAC[resolve; SUBSET; IN_UNION; IN_DELETE] THEN
      MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[ARITH_RULE `x < nb ==> x < nb + nc + 1`]] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `nd:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `~~p IN C` THENL
     [REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `~~p IN C`))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `nd + nc + 1`) THEN
      REWRITE_TAC[LT_ADD_RCANCEL] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL
       [`A:form->bool`; `resolve q D C`; `p:form`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC(CONJUNCT2(SPEC_ALL npresproof_RULES)) THEN
          ASM_REWRITE_TAC[];
          SUBGOAL_THEN `~(~~p = ~~q)` MP_TAC THENL
           [ASM_MESON_TAC[NEGATE_NEGATE]; ALL_TAC] THEN
          UNDISCH_TAC `~~p IN C` THEN
          REWRITE_TAC[resolve; IN_UNION; IN_DELETE] THEN MESON_TAC[];
          ASM_MESON_TAC[SUBSET_TAUT; RESOLVE_MONO; SUBSET_REFL;
                        SUBSET_TRANS]];
        ALL_TAC] THEN
      ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS;
                    ARITH_RULE `d < b /\ m < d + c ==> m < b + c`];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `~(~~p IN C)`))) THEN
    EXISTS_TAC `resolve q D C` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS]; ALL_TAC] THEN
    DISJ2_TAC THEN EXISTS_TAC `nd + nc + 1` THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC_ALL npresproof_RULES)) THEN
    ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `nc < nb + nc + 1`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`D:form->bool`; `C:form->bool`; `q:form`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET_TAUT; RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:form->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN MP_TAC)) THENL
   [DISCH_TAC THEN
    ASM_CASES_TAC `~~p IN C` THENL
     [ALL_TAC;
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o
       C MATCH_MP (ASSUME `~(~~p IN C)`))) THEN
      EXISTS_TAC `E:form->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS]] THEN
    ASM_CASES_TAC `~~p IN E` THENL
     [EXISTS_TAC `resolve p A E` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS]; ALL_TAC] THEN
      DISJ1_TAC THEN MATCH_MP_TAC(CONJUNCT2(SPEC_ALL psresproof_RULES)) THEN
      REPEAT(EXISTS_TAC `T`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET_TAUT; RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS];
      ALL_TAC] THEN
    EXISTS_TAC `E:form->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `resolve p A E` THEN
    CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS]] THEN
    UNDISCH_TAC `~(~~p IN E)` THEN
    REWRITE_TAC[resolve; SUBSET; IN_UNION; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `~~p IN C` THENL
   [ALL_TAC;
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `~(~~p IN C)`))) THEN
    EXISTS_TAC `E:form->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS;
                  ARITH_RULE `ne < nc ==> ne < nb + nc + 1`]] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `~~p IN C`))) THEN
  ASM_CASES_TAC `~~p IN E` THENL
   [ALL_TAC;
    EXISTS_TAC `E:form->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `resolve p A E` THEN
      CONJ_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS]] THEN
      UNDISCH_TAC `~(~~p IN E)` THEN
      REWRITE_TAC[resolve; SUBSET; IN_UNION; IN_DELETE] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[ARITH_RULE `ne < nc ==> ne < nb + nc + 1`]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ne:num`) THEN
  ASM_SIMP_TAC[ARITH_RULE `ne < nc ==> ne < nb + nc + 1`] THEN
  DISCH_THEN(MP_TAC o SPECL [`A:form->bool`; `E:form->bool`; `p:form`]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET_TAUT; RESOLVE_MONO; SUBSET_REFL; SUBSET_TRANS;
                ARITH_RULE `m < ne /\ ne < nc ==> m < nb + nc + 1`]);;

let SUPPORT_SYMMETRIC = prove
 (`!hyps sos A B C p q nb nc.
      (!c. c IN hyps ==> clause c /\ ~tautologous c) /\
      ~tautologous(resolve p A (resolve q B C)) /\
      psresproof hyps sos T A /\
      npresproof (hyps DIFF sos) B nb /\
      npresproof (hyps DIFF sos) C nc /\
      p IN A /\ ~~p IN (resolve q B C) /\ q IN B /\ ~~ q IN C /\
      (!m. m < nb + nc + 1
              ==> (!c1 c2 p.
                       psresproof hyps sos T c1 /\
                       npresproof (hyps DIFF sos) c2 m /\
                       p IN c1 /\
                       ~~ p IN c2 /\
                       ~tautologous (resolve p c1 c2)
                       ==> (?cl'. cl' SUBSET resolve p c1 c2 /\
                                  (psresproof hyps sos T cl' \/
                                   (?m'. m' < m /\
                                         npresproof (hyps DIFF sos) cl' m')))))
      ==> ?cl'. cl' SUBSET resolve p A (resolve q B C) /\
                (psresproof hyps sos T cl' \/
                 ?m. m < nb + nc + 1 /\ npresproof (hyps DIFF sos) cl' m)`,
  REPEAT STRIP_TAC THEN MP_TAC(ASSUME `~~p IN (resolve q B C)`) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[resolve; IN_UNION; IN_DELETE]) THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`;
                  `A:form->bool`; `B:form->bool`; `C:form->bool`;
                  `p:form`; `q:form`; `nb:num`; `nc:num`]
                 SUPPORT_ASYMMETRIC) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`;
                  `A:form->bool`; `C:form->bool`; `B:form->bool`;
                  `p:form`; `~~q`; `nc:num`; `nb:num`]
                 SUPPORT_ASYMMETRIC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `clause A /\ clause B /\ clause C` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PSRESPROOF_CLAUSE; NPRESPROOF_CLAUSE; IN_DIFF];
      ALL_TAC] THEN
    SUBGOAL_THEN `literal q` ASSUME_TAC THENL
     [ASM_MESON_TAC[clause]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [ARITH_RULE `a + b + 1 = b + a + 1`] THEN
    ASM_SIMP_TAC[RESOLVE_SYM; NEGATE_NEGATE]]);;

let SUPPORT_LEMMA = prove
 (`!hyps sos.
        (!c. c IN hyps ==> clause c /\ ~tautologous c)
        ==> !n c1 c2 p.
                psresproof hyps sos T c1 /\
                npresproof (hyps DIFF sos) c2 n /\
                p IN c1 /\ ~~p IN c2 /\
                ~(tautologous(resolve p c1 c2))
                ==> ?cl'. cl' SUBSET (resolve p c1 c2) /\
                          (psresproof hyps sos T cl' \/
                           ?m. m < n /\ npresproof (hyps DIFF sos) cl' m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`A:form->bool`; `Z:form->bool`; `p:form`] THEN
  STRIP_TAC THEN
  MP_TAC(ASSUME `npresproof (hyps DIFF sos) Z n`) THEN
  GEN_REWRITE_TAC LAND_CONV [npresproof_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    EXISTS_TAC `resolve p A Z` THEN REWRITE_TAC[SUBSET_REFL] THEN
    DISJ1_TAC THEN MATCH_MP_TAC(CONJUNCT2(SPEC_ALL psresproof_RULES)) THEN
    MAP_EVERY EXISTS_TAC [`T`; `F`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`]
                 psresproof_RULES) THEN
    DISCH_THEN(MP_TAC o SPEC `Z:form->bool` o CONJUNCT1) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`q:form`; `nb:num`; `nc:num`; `B:form->bool`; `C:form->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`;
                  `A:form->bool`; `B:form->bool`; `C:form->bool`;
                  `p:form`; `q:form`; `nb:num`; `nc:num`]
               SUPPORT_SYMMETRIC) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Old stuff; should be able to recycle it.                                  *)
(* ------------------------------------------------------------------------- *)

let SUPPORT_INDUCT_LEMMA = prove
 (`!hyps sos p c1 c2.
        (!c. c IN hyps ==> clause c /\ ~tautologous c) /\
        psresproof hyps sos T c1 /\
        presproof (hyps DIFF sos) c2 /\
        p IN c1 /\ ~~p IN c2 /\ ~(tautologous(resolve p c1 c2))
        ==> ?cl'. cl' SUBSET (resolve p c1 c2) /\
                  (presproof (hyps DIFF sos) cl' \/
                   psresproof hyps sos T cl')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`]
               SUPPORT_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NPRESPROOF]) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`n:num`; `c1:form->bool`; `c2:form->bool`; `p:form`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[NPRESPROOF]);;

let SUPPORT_INDUCT = prove
 (`!hyps sos.
     (!c. c IN hyps ==> clause c /\ ~(tautologous c))
     ==> !cl. presproof hyps cl
              ==> clause cl /\
                  (~(tautologous cl)
                   ==> ?cl'. cl' SUBSET cl /\
                                 (presproof (hyps DIFF sos) cl' \/
                                  psresproof hyps sos T cl'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC presproof_INDUCT THEN CONJ_TAC THENL
   [X_GEN_TAC `cl:form->bool` THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    EXISTS_TAC `cl:form->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
    ASM_CASES_TAC `cl:form->bool IN sos` THENL
     [ALL_TAC; ASM_MESON_TAC[presproof_RULES; IN_DIFF]] THEN
    DISJ2_TAC THEN
    MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`]
                 psresproof_RULES) THEN
    DISCH_THEN(MP_TAC o SPEC `cl:form->bool` o CONJUNCT1) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:form`; `c1:form->bool`; `c2:form->bool`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[RESOLVE_CLAUSE] THEN DISCH_TAC THEN
  ASM_CASES_TAC `tautologous c1` THENL
   [SUBGOAL_THEN `~(tautologous c2)` ASSUME_TAC THENL
     [ASM_MESON_TAC[RESOLVE_TAUT_L; SUBSET_TAUT]; ALL_TAC] THEN
    ASM_MESON_TAC[RESOLVE_TAUT_L; SUBSET_TRANS; SUBSET_UNION]; ALL_TAC] THEN
  ASM_CASES_TAC `tautologous c2` THENL
   [ASM_MESON_TAC[RESOLVE_TAUT_R; clause; SUBSET_TRANS; SUBSET_UNION];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `~(tautologous c2)`)) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `~(tautologous c1)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1':form->bool`
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2':form->bool`
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_CASES_TAC `p:form IN c1'` THENL
   [ALL_TAC;
    EXISTS_TAC `c1':form->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; resolve; IN_UNION; IN_DELETE] THEN
    ASM_MESON_TAC[SUBSET]] THEN
  ASM_CASES_TAC `~~p IN c2'` THENL
   [ALL_TAC;
    EXISTS_TAC `c2':form->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; resolve; IN_UNION; IN_DELETE] THEN
    ASM_MESON_TAC[SUBSET]] THEN
  UNDISCH_THEN
   `presproof (hyps DIFF sos) c1' \/ psresproof hyps sos T c1'`
   DISJ_CASES_TAC THEN FIRST_X_ASSUM DISJ_CASES_TAC
  THENL
   [ASM_MESON_TAC[presproof_RULES; RESOLVE_MONO];
    MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`;
                  `~~p`; `c2':form->bool`; `c1':form->bool`]
                 SUPPORT_INDUCT_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[NEGATE_NEGATE; SUBSET_TAUT; RESOLVE_MONO;
                    clause; SUBSET; RESOLVE_SYM];
      ASM_MESON_TAC[RESOLVE_MONO; SUBSET_TRANS; SUBSET_TAUT;
                    clause; SUBSET; RESOLVE_SYM]];
    MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`;
                  `p:form`; `c1':form->bool`; `c2':form->bool`]
                 SUPPORT_INDUCT_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RESOLVE_MONO; SUBSET_TRANS; SUBSET_TAUT];
    EXISTS_TAC `resolve p c1' c2'` THEN ASM_SIMP_TAC[RESOLVE_MONO] THEN
    DISJ2_TAC THEN MATCH_MP_TAC(CONJUNCT2(SPEC_ALL psresproof_RULES)) THEN
    REPEAT(EXISTS_TAC `T`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TAUT; RESOLVE_MONO]]);;

let SUPPORT = prove
 (`!sos hyps cl.
     (!c. c IN hyps ==> clause c /\ ~(tautologous c)) /\
     presproof hyps cl /\ ~(tautologous cl)
     ==> ?cl'. cl' SUBSET cl /\
               (presproof (hyps DIFF sos) cl' \/ psresproof hyps sos T cl')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`]
               SUPPORT_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Slightly different formulation of the propositional case.                 *)
(* ------------------------------------------------------------------------- *)

let spresproof_RULES,spresproof_INDUCT,spresproof_CASES =
  new_inductive_definition
   `(!c. c IN hyps /\ c IN sos /\ ~(tautologous c)
         ==> spresproof hyps sos c) /\
    (!c1 c2 p.
             spresproof hyps sos c1 /\
             (spresproof hyps sos c2 \/ c2 IN hyps) /\
             p IN c1 /\ ~~p IN c2 /\
             ~(tautologous(resolve p c1 c2))
             ==> spresproof hyps sos (resolve p c1 c2))`;;

(* ------------------------------------------------------------------------- *)
(* Relation to previous version.                                             *)
(* ------------------------------------------------------------------------- *)

let SPRESPROOF_PSRESPROOF = prove
 (`!hyps sos. (!c. c IN hyps ==> clause c /\ ~(tautologous c))
              ==> !cl. spresproof hyps sos cl = psresproof hyps sos T cl`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC spresproof_INDUCT THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`hyps:(form->bool)->bool`; `sos:(form->bool)->bool`]
                   psresproof_RULES) THEN
      DISCH_THEN(MP_TAC o SPEC `c:form->bool` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC_ALL psresproof_RULES)) THENL
     [REPEAT(EXISTS_TAC `T`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`T`; `c2:form->bool IN sos`] THEN
    ASM_SIMP_TAC[psresproof_RULES] THEN
    MATCH_MP_TAC(CONJUNCT1(SPEC_ALL psresproof_RULES)) THEN
    ASM_MESON_TAC[IN_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s cl. psresproof hyps sos s cl
           ==> (if s then spresproof hyps sos cl
                else cl IN hyps /\ ~(cl IN sos) /\ ~(tautologous cl))`
   (fun th -> MP_TAC(SPEC `T` th) THEN REWRITE_TAC[]) THEN
  MATCH_MP_TAC psresproof_INDUCT THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[spresproof_RULES]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MAP_EVERY BOOL_CASES_TAC [`s1:bool`; `s2:bool`] THEN
  ASM_REWRITE_TAC[] THENL
   [MESON_TAC[spresproof_RULES];
    MESON_TAC[spresproof_RULES; IN_DIFF];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `resolve p c1 c2 = resolve (~~p) c2 c1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[RESOLVE_SYM; clause]; ALL_TAC] THEN
  MATCH_MP_TAC(CONJUNCT2(SPEC_ALL spresproof_RULES)) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[NEGATE_NEGATE; clause]);;

let SPRESPROOF_CLAUSE_NONTAUT = prove
 (`!hyps sos.
        (!c. c IN hyps ==> clause c /\ ~(tautologous c))
        ==> !c. spresproof hyps sos c ==> clause c /\ ~(tautologous c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC spresproof_INDUCT THEN
  ASM_SIMP_TAC[RESOLVE_CLAUSE; IN_DIFF] THEN ASM_MESON_TAC[RESOLVE_CLAUSE]);;

let SPRESPROOF_CLAUSE = prove
 (`!hyps sos.
        (!c. c IN hyps ==> clause c)
        ==> !c. spresproof hyps sos c ==> clause c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC spresproof_INDUCT THEN
  ASM_SIMP_TAC[RESOLVE_CLAUSE; IN_DIFF] THEN ASM_MESON_TAC[RESOLVE_CLAUSE]);;

let SPRESPROOF_MONO = prove
 (`!hyps1 hyps2 sos cl.
      spresproof hyps1 sos cl /\ hyps1 SUBSET hyps2
      ==> spresproof hyps2 sos cl`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
  REWRITE_TAC[SUBSET; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC spresproof_INDUCT THEN
  ASM_MESON_TAC[IN_DIFF; spresproof_RULES]);;

let SPRESPROOF_MONO_SOS = prove
 (`!hyps1 hyps2 sos1 sos2 cl.
      spresproof hyps1 sos1 cl /\ hyps1 SUBSET hyps2 /\ sos1 SUBSET sos2
      ==> spresproof hyps2 sos2 cl`,
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b /\ c ==> a ==> d`] THEN
  REWRITE_TAC[SUBSET; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN MATCH_MP_TAC spresproof_INDUCT THEN
  ASM_MESON_TAC[spresproof_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Nicer statement of completeness.                                          *)
(* ------------------------------------------------------------------------- *)

let TAUTOLOGOUS_SATISFIED = prove
 (`!c d. clause c /\ tautologous c ==> pholds d (interp c)`,
  SIMP_TAC[clause; tautologous; PHOLDS_INTERP] THEN MESON_TAC[PHOLDS_NEGATE]);;

let PRESPROOF_SOUND = prove
 (`!asm. (!c. c IN asm ==> clause c) /\ presproof asm {}
         ==> ~psatisfiable (IMAGE interp asm)`,
  MESON_TAC[PSATISFIABLE_MONO; PPRESPROOF_SOUND; IMAGE_SUBSET; PPRESPROOF]);;

let SPRESPROOF_REFUTATION_COMPLETE = prove
 (`!hyps sos.
        (!c. c IN hyps ==> clause c) /\
        ~(psatisfiable {interp cl | cl IN hyps}) /\
        psatisfiable {interp cl | cl IN (hyps DIFF sos)}
        ==> spresproof hyps sos {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sos:(form->bool)->bool`;
                `{c | c IN hyps /\ ~(tautologous c)}`;
                `{}:(form->bool)`] SUPPORT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[IN_ELIM_THM];
      MATCH_MP_TAC PRESPROOF_REFUTATION_COMPLETE THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      UNDISCH_TAC `~psatisfiable {interp cl | cl IN hyps}` THEN
      REWRITE_TAC[TAUT `~b ==> ~a <=> a ==> b`; psatisfiable] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:form->bool` THEN
      SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:form` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `cl:form->bool` THEN
      ASM_CASES_TAC `tautologous cl` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[TAUTOLOGOUS_SATISFIED];
      REWRITE_TAC[tautologous; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET_EMPTY; UNWIND_THM2] THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT]
                   PRESPROOF_SOUND)) THEN
    UNDISCH_TAC `psatisfiable {interp cl | cl IN hyps DIFF sos}` THEN
    MATCH_MP_TAC(TAUT `(a ==> c) /\ b ==> a ==> (b ==> ~c) ==> d`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[IN_ELIM_THM; IN_DIFF]] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
                PSATISFIABLE_MONO) THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `spresproof {c | c IN hyps /\ ~tautologous c} sos {}`
  MP_TAC THENL
   [UNDISCH_TAC `psresproof {c | c IN hyps /\ ~tautologous c} sos T {}` THEN
    MATCH_MP_TAC(TAUT `(b <=> a) ==> a ==> b`) THEN
    SPEC_TAC(`{}:form->bool`,`cl:form->bool`) THEN
    MATCH_MP_TAC SPRESPROOF_PSRESPROOF THEN ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[TAUT `(a /\ b ==> c) <=> b ==> a ==> c`]
                SPRESPROOF_MONO) THEN
  SIMP_TAC[IN_ELIM_THM; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* First order set-of-support resolution with no tautologies.                *)
(* ------------------------------------------------------------------------- *)

let sresproof_RULES,sresproof_INDUCT,sresproof_CASES =
  new_inductive_definition
   `(!c. c IN hyps /\ c IN sos /\ ~(tautologous c)
         ==> sresproof hyps sos c) /\
    (!cl1 cl2 cl2' ps1 ps2 i.
       sresproof hyps sos cl1 /\
       (sresproof hyps sos cl2 \/ cl2 IN hyps) /\
       (IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2') /\
       ps1 SUBSET cl1 /\
       ps2 SUBSET cl2' /\
       ~(ps1 = {}) /\
       ~(ps2 = {}) /\
       (?i. Unifies i (ps1 UNION {~~ p | p IN ps2})) /\
       (mgu (ps1 UNION {~~ p | p IN ps2}) = i) /\
       ~(tautologous(IMAGE (formsubst i) (cl1 DIFF ps1 UNION cl2' DIFF ps2)))
       ==> sresproof hyps sos
           (IMAGE (formsubst i) (cl1 DIFF ps1 UNION cl2' DIFF ps2)))`;;

let SRESPROOF_CLAUSE = prove
 (`!hyps sos.
     (!c. c IN hyps ==> clause c)
     ==> !c. sresproof hyps sos c ==> clause c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC sresproof_INDUCT THEN
  ASM_MESON_TAC[CLAUSE_UNION; CLAUSE_DIFF; IMAGE_FORMSUBST_CLAUSE]);;

(* ------------------------------------------------------------------------- *)
(* Lifting to first order level.                                             *)
(* ------------------------------------------------------------------------- *)

let PSATISFIES_IMAGE_LEMMA = prove
 (`(!c. c IN s ==> clause c)
   ==> !d. d psatisfies {formsubst v p | prop v /\ p IN IMAGE interp s} <=>
           d psatisfies {interp cl | cl IN
                       {IMAGE (formsubst v) c | prop v /\ c IN s}}`,
  STRIP_TAC THEN REWRITE_TAC[psatisfies; IN_ELIM_THM] THEN
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[IN_IMAGE; PHOLDS_INTERP_IMAGE]);;

let SOS_RESOLUTION_COMPLETE = prove
 (`(!cl. cl IN hyps ==> clause cl) /\ sos SUBSET hyps /\
   ~(?M:(term->bool)#(num->term list->term)#(num->term list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp hyps)) /\
   (?M:(A->bool)#(num->A list->A)#(num->A list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp (hyps DIFF sos)))
   ==> sresproof hyps sos {}`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE interp hyps` HERBRAND_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[QFREE_INTERP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. d psatisfies
          {formsubst v p | v,p | 
               (!x. v x IN herbase (functions (IMAGE interp hyps))) /\
               p IN IMAGE interp (hyps DIFF sos)}`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SATISFIES_INSTANCES) THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE interp (hyps DIFF sos)`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE
     [TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
     (GEN_ALL SATISFIES_PSATISFIES))) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `v:num->A` o MATCH_MP VALUATION_EXISTS) THEN
    DISCH_THEN(MP_TAC o SPEC `v:num->A`) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DIFF] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[QFREE_FORMSUBST; QFREE_INTERP; clause]; ALL_TAC] THEN
    DISCH_THEN(fun th -> EXISTS_TAC (lhand(concl th)) THEN MP_TAC th) THEN
    REWRITE_TAC[psatisfies] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:form` THEN
    MATCH_MP_TAC(TAUT `(a ==> b) ==> (b ==> c) ==> (a ==> c)`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; language] THEN
    MESON_TAC[HERBASE_SUBSET_TERMS]; ALL_TAC] THEN
  ASM_SIMP_TAC[PSATISFIES_IMAGE_LEMMA; IMAGE_FORMSUBST_CLAUSE; IN_DIFF] THEN
  REWRITE_TAC[GSYM IN_DIFF; psatisfies; GSYM psatisfiable] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `spresproof {IMAGE (formsubst v) cl | v,cl | cl IN hyps}
               {IMAGE (formsubst v) cl | v,cl | cl IN sos} {}`
  MP_TAC THENL
   [MATCH_MP_TAC SPRESPROOF_MONO_SOS THEN
    EXISTS_TAC
     `{IMAGE (formsubst v) c | v,c |
         (!x. v x IN herbase(functions(IMAGE interp hyps))) /\
         c IN hyps}` THEN
    EXISTS_TAC
     `{IMAGE (formsubst v) c | v,c |
         (!x. v x IN herbase(functions(IMAGE interp hyps))) /\
         c IN sos}` THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]] THEN
    MATCH_MP_TAC SPRESPROOF_REFUTATION_COMPLETE THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[IMAGE_FORMSUBST_CLAUSE];
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE
     [IMP_CONJ] PSATISFIABLE_MONO)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!cl0. spresproof {IMAGE (formsubst v) cl | v,cl | cl IN hyps}
           {IMAGE (formsubst v) cl | v,cl | cl IN sos} cl0
           ==> ?cl. sresproof hyps sos cl /\ cl0 instance_of cl`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `{}:form->bool`) THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    MESON_TAC[INSTANCE_OF_EMPTY]] THEN
  MATCH_MP_TAC spresproof_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; instance_of; IN_ELIM_THM] THEN
    ASM_MESON_TAC[sresproof_RULES; TAUTOLOGOUS_INSTANCE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`A':form->bool`; `B':form->bool`; `p:form`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `A:form->bool` STRIP_ASSUME_TAC)
                             MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SWAP_EXISTS_THM] THEN
  REWRITE_TAC[OR_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:form->bool` MP_TAC) THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[GSYM instance_of] THEN
  REWRITE_TAC[TAUT `a /\ c \/ b /\ c <=> (a \/ b) /\ c`] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL
   [`A:form->bool`; `IMAGE (formsubst (rename B (FVS A))) B`;
    `A':form->bool`; `B':form->bool`; `resolve p A' B'`; `p:form`]
   LIFTING_LEMMA) THEN
  ABBREV_TAC `C = IMAGE (formsubst (rename B (FVS A))) B` THEN
  MP_TAC(SPECL [`B:form->bool`; `FVS(A)`] rename) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FVS_CLAUSE_FINITE; SRESPROOF_CLAUSE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[renaming] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [FUN_EQ_THM; o_THM; I_DEF; BETA_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num->term` (ASSUME_TAC o CONJUNCT1)) THEN
  ANTS_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SRESPROOF_CLAUSE];
    ASM_MESON_TAC[IMAGE_FORMSUBST_CLAUSE; SRESPROOF_CLAUSE];
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
    ASM_MESON_TAC[SRESPROOF_CLAUSE; clause; QFREE_LITERAL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:form->bool` (X_CHOOSE_THEN `B1:form->bool`
      MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `mgu (A1 UNION {~~ l | l IN B1})`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC ISMGU_MGU THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SRESPROOF_CLAUSE; clause; FINITE_SUBSET];
      SUBGOAL_THEN `{~~l | l IN B1} = IMAGE (~~) B1` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[SRESPROOF_CLAUSE; clause; FINITE_SUBSET; FINITE_IMAGE];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[SRESPROOF_CLAUSE; clause; QFREE_LITERAL; SUBSET;
                    IMAGE_FORMSUBST_CLAUSE; QFREE_NEGATE]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN EXISTS_TAC (rand(concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(CONJUNCT2(SPEC_ALL sresproof_RULES)) THEN
  EXISTS_TAC `B:form->bool` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP TAUTOLOGOUS_INSTANCE) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [instance_of]) THEN
  REWRITE_TAC[NOT_IMP; NOT_FORALL_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence show that the given clause algorithm will find refutations.         *)
(* ------------------------------------------------------------------------- *)

let SOS_GIVEN_GENERAL = prove
 (`!used unused cl.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c) /\
        sresproof (set_of_list(used) UNION set_of_list(unused))
                  (set_of_list unused) cl
        ==> clause cl /\
            ?n cl'. cl' subsumes cl /\ cl' IN level(used,unused) n`,
  GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC sresproof_INDUCT THEN CONJ_TAC THENL
   [X_GEN_TAC `c:form->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN FIRST_ASSUM(MP_TAC o MATCH_MP LEVEL_0) THEN
    REWRITE_TAC[SUBSUMES; IN_UNION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`c1:form->bool`; `c2:form->bool`; `c2':form->bool`;
    `ps1:form->bool`; `ps2:form->bool`; `i:num->term`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `n1:num`)) MP_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?n2. c2 IN set_of_list(used) \/
         ?cl'. cl' subsumes c2 /\ (cl' IN level (used,unused) n2)`
  MP_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
     [REWRITE_TAC[IN_UNION] THEN MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [ASM_MESON_TAC[subsumes_REFL]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN FIRST_ASSUM(MP_TAC o MATCH_MP LEVEL_0) THEN
    REWRITE_TAC[SUBSUMES] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n2:num`) THEN
  SUBGOAL_THEN
   `?n cl1 cl2. cl1 subsumes c1 /\ cl2 subsumes c2 /\
                cl1 IN level(used,unused) n /\
                ((cl2 = c2) /\ c2 IN set_of_list(used) \/
                 cl2 IN level(used,unused) n)`
  MP_TAC THENL
   [EXISTS_TAC `n1 + n2:num` THEN REWRITE_TAC[IN_UNION] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> (a /\ c) /\ (b /\ d)`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[level_MONO_SUBSET; SUBSET; LE_ADD]; ALL_TAC] THEN
    UNDISCH_TAC
     `c2 IN set_of_list used \/
      (?cl'. cl' subsumes c2 /\ cl' IN level (used,unused) n2)` THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
    ASM_MESON_TAC[subsumes_REFL; level_MONO_SUBSET; SUBSET;
                  ARITH_RULE `n <= m + n:num`];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `cl1:form->bool`; `cl2:form->bool`] THEN
  SUBGOAL_THEN `clause c2` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SET_OF_LIST; IN_UNION]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> c ==> b) ==> c ==> a /\ b`) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[IMAGE_FORMSUBST_CLAUSE; CLAUSE_UNION; CLAUSE_DIFF];
    ALL_TAC] THEN
  DISCH_TAC THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`c1:form->bool`; `cl1:form->bool`; `c2:form->bool`;
                  `IMAGE (formsubst i) (c1 DIFF ps1 UNION c2' DIFF ps2)`]
                 ISARESOLVENT_SUBSUME_L) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[level_CLAUSE]; ALL_TAC] THEN
      ASM_REWRITE_TAC[isaresolvent] THEN
      CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
      MAP_EVERY EXISTS_TAC [`ps1:form->bool`; `ps2:form->bool`] THEN
      CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:form->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `SUC n` THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP LEVEL_STEP) THEN
    REWRITE_TAC[SUBSUMES; allntresolvents; IN_ELIM_THM; allresolvents] THEN
    DISCH_THEN(MP_TAC o SPEC `r:form->bool`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ALL_TAC;
        ASM_MESON_TAC[TAUTOLOGOUS_INSTANCE; SUBSET_TAUT; subsumes]] THEN
      MAP_EVERY EXISTS_TAC [`cl1:form->bool`; `c2:form->bool`] THEN
      ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    ASM_MESON_TAC[subsumes_TRANS; level_CLAUSE]; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:form->bool`; `cl1:form->bool`; `c2:form->bool`;
                `cl2:form->bool`;
                `IMAGE (formsubst i) (c1 DIFF ps1 UNION c2' DIFF ps2)`]
               ISARESOLVENT_SUBSUME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[level_CLAUSE]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[level_CLAUSE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[isaresolvent] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    MAP_EVERY EXISTS_TAC [`ps1:form->bool`; `ps2:form->bool`] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:form->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `SUC n` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP LEVEL_STEP) THEN
  REWRITE_TAC[SUBSUMES; allntresolvents; IN_ELIM_THM; allresolvents] THEN
  DISCH_THEN(MP_TAC o SPEC `r:form->bool`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      ASM_MESON_TAC[TAUTOLOGOUS_INSTANCE; SUBSET_TAUT; subsumes]] THEN
    MAP_EVERY EXISTS_TAC [`cl1:form->bool`; `cl2:form->bool`] THEN
    ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  ASM_MESON_TAC[subsumes_TRANS; level_CLAUSE]);;

let SUBSUMES_EMPTY = prove
 (`!c. (c subsumes {}) = (c = {})`,
  REWRITE_TAC[subsumes; IN_IMAGE; NOT_IN_EMPTY; EXTENSION; SUBSET] THEN
  MESON_TAC[]);;

let SOS_GIVEN = prove
 (`!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c) /\
        sresproof (set_of_list(used) UNION set_of_list(unused))
                  (set_of_list unused) {}
        ==> ?n. {} IN level(used,unused) n`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SOS_GIVEN_GENERAL) THEN
  SIMP_TAC[SUBSUMES_EMPTY; UNWIND_THM2]);;
