(* ========================================================================= *)
(* Formal semantics of HOL inside itself.                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Semantics of types.                                                       *)
(* ------------------------------------------------------------------------- *)

let typeset = new_recursive_definition type_RECURSION
  `(typeset tau (Tyvar s) = tau(s)) /\
   (typeset tau Bool = boolset) /\
   (typeset tau Ind = indset) /\
   (typeset tau (Fun a b) = funspace (typeset tau a) (typeset tau b))`;;

(* ------------------------------------------------------------------------- *)
(* Semantics of terms.                                                       *)
(* ------------------------------------------------------------------------- *)

let semantics = new_recursive_definition term_RECURSION
  `(semantics sigma tau (Var n ty) = sigma(n,ty)) /\
   (semantics sigma tau (Equal ty) =
        abstract (typeset tau ty) (typeset tau (Fun ty Bool))
                 (\x. abstract (typeset tau ty) (typeset tau Bool)
                               (\y. boolean(x = y)))) /\
   (semantics sigma tau (Select ty) =
        abstract (typeset tau (Fun ty Bool)) (typeset tau ty)
                 (\s. if ?x. x <: ((typeset tau ty) suchthat (holds s))
                      then ch ((typeset tau ty) suchthat (holds s))
                      else ch (typeset tau ty))) /\
   (semantics sigma tau (Comb s t) =
        apply (semantics sigma tau s) (semantics sigma tau t)) /\
   (semantics sigma tau (Abs n ty t) =
        abstract (typeset tau ty) (typeset tau (typeof t))
                 (\x. semantics (((n,ty) |-> x) sigma) tau t))`;;

(* ------------------------------------------------------------------------- *)
(* Valid type and term valuations.                                           *)
(* ------------------------------------------------------------------------- *)

let type_valuation = new_definition
  `type_valuation tau <=> !x. (?y. y <: tau x)`;;

let term_valuation = new_definition
  `term_valuation tau sigma <=> !n ty. sigma(n,ty) <: typeset tau ty`;;

let TERM_VALUATION_VALMOD = prove
 (`!sigma taut n ty x.
        term_valuation tau sigma /\ x <: typeset tau ty
        ==> term_valuation tau (((n,ty) |-> x) sigma)`,
  REWRITE_TAC[term_valuation; valmod; PAIR_EQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* All the typesets are nonempty.                                            *)
(* ------------------------------------------------------------------------- *)

let TYPESET_INHABITED = prove
 (`!tau ty. type_valuation tau ==> ?x. x <: typeset tau ty`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC type_INDUCT THEN REWRITE_TAC[typeset] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[type_valuation];
    ASM_MESON_TAC[BOOLEAN_IN_BOOLSET; INDSET_INHABITED; FUNSPACE_INHABITED]]);;

(* ------------------------------------------------------------------------- *)
(* Semantics maps into the right place.                                      *)
(* ------------------------------------------------------------------------- *)

let SEMANTICS_TYPESET_INDUCT = prove
 (`!tm ty. tm has_type ty
           ==> tm has_type ty /\
               !sigma tau. type_valuation tau /\ term_valuation tau sigma
                           ==> (semantics sigma tau tm) <: (typeset tau ty)`,
  MATCH_MP_TAC has_type_INDUCT THEN
  ASM_SIMP_TAC[semantics; typeset; has_type_RULES] THEN
  CONJ_TAC THENL [MESON_TAC[term_valuation]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC ABSTRACT_IN_FUNSPACE THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSTRACT_IN_FUNSPACE THEN
    REWRITE_TAC[BOOLEAN_IN_BOOLSET];
    MATCH_MP_TAC ABSTRACT_IN_FUNSPACE THEN
    ASM_MESON_TAC[ch; SUCHTHAT; TYPESET_INHABITED];
    ASM_MESON_TAC[has_type_RULES];
    MATCH_MP_TAC APPLY_IN_RANSPACE THEN ASM_MESON_TAC[];
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP WELLTYPED_LEMMA) THEN
    MATCH_MP_TAC ABSTRACT_IN_FUNSPACE THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[TERM_VALUATION_VALMOD]]);;

let SEMANTICS_TYPESET = prove
 (`!sigma tau tm ty.
        type_valuation tau /\ term_valuation tau sigma /\ tm has_type ty
        ==> (semantics sigma tau tm) <: (typeset tau ty)`,
  MESON_TAC[SEMANTICS_TYPESET_INDUCT]);;

(* ------------------------------------------------------------------------- *)
(* Semantics of equations.                                                   *)
(* ------------------------------------------------------------------------- *)

let SEMANTICS_EQUATION = prove
 (`!sigma tau s t.
        s has_type (typeof s) /\ t has_type (typeof s) /\
        type_valuation tau /\ term_valuation tau sigma
        ==> (semantics sigma tau (s === t) =
             boolean(semantics sigma tau s = semantics sigma tau t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[equation; semantics] THEN
  ASM_SIMP_TAC[APPLY_ABSTRACT; typeset; SEMANTICS_TYPESET;
               ABSTRACT_IN_FUNSPACE; BOOLEAN_IN_BOOLSET]);;

let SEMANTICS_EQUATION_ALT = prove
 (`!sigma tau s t.
        (s === t) has_type Bool /\
        type_valuation tau /\ term_valuation tau sigma
        ==> (semantics sigma tau (s === t) =
             boolean(semantics sigma tau s = semantics sigma tau t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SEMANTICS_EQUATION THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `welltyped(s === t)` MP_TAC THENL
   [ASM_MESON_TAC[welltyped]; ALL_TAC] THEN
  REWRITE_TAC[equation; WELLTYPED_CLAUSES; typeof; codomain] THEN
  MESON_TAC[welltyped; type_INJ; WELLTYPED; WELLTYPED_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Quick sanity check.                                                       *)
(* ------------------------------------------------------------------------- *)

let SEMANTICS_SELECT = prove
 (`p has_type (Fun ty Bool) /\
   type_valuation tau /\ term_valuation tau sigma
   ==> (semantics sigma tau (Comb (Select ty) p) =
        if ?x. x <: (typeset tau ty) suchthat (holds (semantics sigma tau p))
        then ch((typeset tau ty) suchthat (holds (semantics sigma tau p)))
        else ch(typeset tau ty))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[semantics] THEN
  W(fun (asl,w) ->
        let t = find_term (fun t ->
           can (PART_MATCH (lhs o rand) APPLY_ABSTRACT) t) w in
        MP_TAC(PART_MATCH (lhs o rand) APPLY_ABSTRACT t)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[SEMANTICS_TYPESET; typeset];
      REWRITE_TAC[SUCHTHAT] THEN
      ASM_MESON_TAC[ch; SUCHTHAT; TYPESET_INHABITED]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Semantics of a sequent.                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("|=",(11,"right"));;

let sequent = new_definition
  `asms |= p <=> ALL (\a. a has_type Bool) (CONS p asms) /\
                 !sigma tau. type_valuation tau /\
                             term_valuation tau sigma /\
                              ALL (\a. semantics sigma tau a = true) asms
                              ==> (semantics sigma tau p = true)`;;

(* ------------------------------------------------------------------------- *)
(* Invariance of semantics under alpha-conversion.                           *)
(* ------------------------------------------------------------------------- *)

let SEMANTICS_RACONV = prove
 (`!env tp.
        RACONV env tp
        ==> !sigma1 sigma2 tau.
                type_valuation tau /\
                term_valuation tau sigma1 /\ term_valuation tau sigma2 /\
                (!x1 ty1 x2 ty2.
                        ALPHAVARS env (Var x1 ty1,Var x2 ty2)
                        ==> (semantics sigma1 tau (Var x1 ty1) =
                             semantics sigma2 tau (Var x2 ty2)))
                ==> welltyped(FST tp) /\ welltyped(SND tp)
                    ==> (semantics sigma1 tau (FST tp) =
                         semantics sigma2 tau (SND tp))`,
  MATCH_MP_TAC RACONV_INDUCT THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[semantics; WELLTYPED_CLAUSES] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    BINOP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC ABSTRACT_EQ THEN
  ASM_SIMP_TAC[TYPESET_INHABITED] THEN
  X_GEN_TAC `x:V` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SEMANTICS_TYPESET THEN
    ASM_SIMP_TAC[TERM_VALUATION_VALMOD; GSYM WELLTYPED];
    MATCH_MP_TAC SEMANTICS_TYPESET THEN
    ASM_SIMP_TAC[TERM_VALUATION_VALMOD; GSYM WELLTYPED];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP]) THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN
  REWRITE_TAC[ALPHAVARS; PAIR_EQ; term_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VALMOD; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let SEMANTICS_ACONV = prove
 (`!sigma tau s t.
        type_valuation tau /\ term_valuation tau sigma /\
         welltyped s /\ welltyped t /\ ACONV s t
        ==> (semantics sigma tau s = semantics sigma tau t)`,
  REWRITE_TAC[ACONV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM; FORALL_PAIR_THM]
               SEMANTICS_RACONV) THEN
  EXISTS_TAC `[]:(term#term)list` THEN
  ASM_SIMP_TAC[ALPHAVARS; term_INJ; PAIR_EQ]);;

(* ------------------------------------------------------------------------- *)
(* General semantic lemma about binary inference rules.                      *)
(* ------------------------------------------------------------------------- *)

let BINARY_INFERENCE_RULE = prove
 (`(p1 has_type Bool /\ p2 has_type Bool
   ==> q has_type Bool /\
       !sigma tau. type_valuation tau /\ term_valuation tau sigma /\
                   (semantics sigma tau p1 = true) /\
                   (semantics sigma tau p2 = true)
                  ==> (semantics sigma tau q = true))
   ==> (asl1 |= p1 /\ asl2 |= p2 ==> TERM_UNION asl1 asl2 |= q)`,
  REWRITE_TAC[sequent; ALL] THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ALL_BOOL_TERM_UNION] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC
    `ALL (\a. semantics sigma tau a = true) (TERM_UNION asl1 asl2)` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM])) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  DISCH_THEN(fun th -> X_GEN_TAC `r:term` THEN DISCH_TAC THEN MP_TAC th) THEN
  MP_TAC(SPECL [`asl1:term list`; `asl2:term list`; `r:term`]
    TERM_UNION_THM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `s:term`) THEN
  DISCH_THEN(MP_TAC o SPEC `s:term`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SEMANTICS_ACONV; welltyped; TERM_UNION_NONEW]);;

(* ------------------------------------------------------------------------- *)
(* Semantics only depends on valuations of free variables.                   *)
(* ------------------------------------------------------------------------- *)

let TERM_VALUATION_VFREE_IN = prove
 (`!tau sigma1 sigma2 t.
        type_valuation tau /\
        term_valuation tau sigma1 /\ term_valuation tau sigma2 /\
        welltyped t /\
        (!x ty. VFREE_IN (Var x ty) t ==> (sigma1(x,ty) = sigma2(x,ty)))
        ==> (semantics sigma1 tau t = semantics sigma2 tau t)`,
  GEN_TAC THEN GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[semantics; VFREE_IN; term_DISTINCT; term_INJ] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    BINOP_TAC THEN ASM_MESON_TAC[WELLTYPED_CLAUSES];
    ALL_TAC] THEN
  MATCH_MP_TAC ABSTRACT_EQ THEN ASM_SIMP_TAC[TYPESET_INHABITED] THEN
  X_GEN_TAC `x:V` THEN DISCH_TAC THEN REPEAT(CONJ_TAC THENL
   [ASM_MESON_TAC[TERM_VALUATION_VALMOD; WELLTYPED; WELLTYPED_CLAUSES;
                  SEMANTICS_TYPESET];
    ALL_TAC]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[WELLTYPED_CLAUSES]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`] THEN DISCH_TAC THEN
  REWRITE_TAC[VALMOD; PAIR_EQ] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Prove some inference rules correct.                                       *)
(* ------------------------------------------------------------------------- *)

let ASSUME_correct = prove
 (`!p. p has_type Bool ==> [p] |= p`,
  SIMP_TAC[sequent; ALL]);;

let REFL_correct = prove
 (`!t. welltyped t ==> [] |= t === t`,
  SIMP_TAC[sequent; SEMANTICS_EQUATION; ALL; WELLTYPED] THEN
  REWRITE_TAC[boolean; equation] THEN MESON_TAC[has_type_RULES]);;

let TRANS_correct = prove
 (`!asl1 asl2 l m1 m2 r.
        asl1 |= l === m1 /\ asl2 |= m2 === r /\ ACONV m1 m2
        ==> TERM_UNION asl1 asl2 |= l === r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC BINARY_INFERENCE_RULE THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[EQUATION_HAS_TYPE_BOOL; ACONV_TYPE];
    ASM_SIMP_TAC[SEMANTICS_EQUATION_ALT; IMP_CONJ; boolean] THEN
    ASM_MESON_TAC[SEMANTICS_ACONV; TRUE_NE_FALSE; EQUATION_HAS_TYPE_BOOL]]);;

let MK_COMB_correct = prove
 (`!asl1 l1 r1 asl2 l2 r2.
        asl1 |= l1 === r1 /\ asl2 |= l2 === r2 /\
        (?rty. typeof l1 = Fun (typeof l2) rty)
        ==> TERM_UNION asl1 asl2 |= Comb l1 l2 === Comb r1 r2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC BINARY_INFERENCE_RULE THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[EQUATION_HAS_TYPE_BOOL; WELLTYPED_CLAUSES; typeof] THEN
    MESON_TAC[codomain];
    ASM_SIMP_TAC[SEMANTICS_EQUATION_ALT; IMP_CONJ; boolean] THEN
    REWRITE_TAC[semantics] THEN
    ASM_MESON_TAC[SEMANTICS_ACONV; TRUE_NE_FALSE; EQUATION_HAS_TYPE_BOOL]]);;

let EQ_MP_correct = prove
 (`!asl1 asl2 p q p'.
        asl1 |= p === q /\ asl2 |= p' /\ ACONV p p'
        ==> TERM_UNION asl1 asl2 |= q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC BINARY_INFERENCE_RULE THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[EQUATION_HAS_TYPE_BOOL; WELLTYPED_LEMMA; WELLTYPED;
                  ACONV_TYPE];
    ASM_SIMP_TAC[SEMANTICS_EQUATION_ALT; IMP_CONJ; boolean] THEN
    ASM_MESON_TAC[EQUATION_HAS_TYPE_BOOL; TRUE_NE_FALSE; SEMANTICS_ACONV;
                  welltyped]]);;

let BETA_correct = prove
 (`!x ty t. welltyped t ==> [] |= Comb (Abs x ty t) (Var x ty) === t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sequent; ALL] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[EQUATION_HAS_TYPE_BOOL; typeof; WELLTYPED_CLAUSES] THEN
    REWRITE_TAC[codomain; type_INJ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SEMANTICS_EQUATION_ALT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[BOOLEAN_EQ_TRUE; semantics] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `semantics (((x,ty) |-> sigma(x,ty)) sigma) tau t` THEN
  CONJ_TAC THENL [MATCH_MP_TAC APPLY_ABSTRACT; ALL_TAC] THEN
  REWRITE_TAC[VALMOD_REPEAT] THEN
  ASM_MESON_TAC[term_valuation; SEMANTICS_TYPESET; WELLTYPED]);;

let ABS_correct = prove
 (`!asl x ty l r.
        ~(EX (VFREE_IN (Var x ty)) asl) /\ asl |= l === r
        ==> asl |= (Abs x ty l) === (Abs x ty r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sequent; ALL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(l === r) has_type Bool` THEN
    SIMP_TAC[EQUATION_HAS_TYPE_BOOL; WELLTYPED_CLAUSES; typeof];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[SEMANTICS_EQUATION_ALT; BOOLEAN_EQ_TRUE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[semantics] THEN
  SUBGOAL_THEN `typeof r = typeof l` SUBST1_TAC THENL
   [ASM_MESON_TAC[EQUATION_HAS_TYPE_BOOL]; ALL_TAC] THEN
  MATCH_MP_TAC ABSTRACT_EQ THEN ASM_SIMP_TAC[TYPESET_INHABITED] THEN
  X_GEN_TAC `x:V` THEN DISCH_TAC THEN
  REPEAT(CONJ_TAC THENL
   [ASM_MESON_TAC[SEMANTICS_TYPESET; TERM_VALUATION_VALMOD;
                  WELLTYPED; EQUATION_HAS_TYPE_BOOL];
    ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  ASM_SIMP_TAC[SEMANTICS_EQUATION_ALT; BOOLEAN_EQ_TRUE] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN
  SUBGOAL_THEN `ALL (\a. a has_type Bool) asl /\
                ALL (\a. ~(VFREE_IN (Var x ty) a)) asl /\
                ALL (\a. semantics sigma tau a = true) asl`
  MP_TAC THENL [ASM_REWRITE_TAC[GSYM NOT_EX; ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[AND_ALL] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
  X_GEN_TAC `p:term` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC TERM_VALUATION_VFREE_IN THEN
  ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[welltyped]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VALMOD; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let DEDUCT_ANTISYM_RULE_correct = prove
 (`!asl1 asl2 p q.
        asl1 |= c1 /\ asl2 |= c2
        ==> let asl1' = FILTER((~) o ACONV c2) asl1
            and asl2' = FILTER((~) o ACONV c1) asl2 in
            (TERM_UNION asl1' asl2') |= c1 === c2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sequent; o_DEF; LET_DEF; LET_END_DEF; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `
    (a1 /\ b1 ==> c1) /\ (a1 /\ b1 /\ c1 ==> a2 /\ b2 ==> c2)
    ==> a1 /\ a2 /\ b1 /\ b2 ==> c1 /\ c2`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[EQUATION_HAS_TYPE_BOOL] THEN
    ASM_MESON_TAC[MEM_FILTER; TERM_UNION_NONEW; welltyped; WELLTYPED_LEMMA];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; AND_FORALL_THM] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[SEMANTICS_EQUATION_ALT; BOOLEAN_EQ_TRUE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOOLEAN_EQ THEN
  REPEAT(CONJ_TAC THENL
   [ASM_MESON_TAC[typeset; SEMANTICS_TYPESET]; ALL_TAC]) THEN
  EQ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  X_GEN_TAC `a:term` THEN DISCH_TAC THENL
   [ASM_CASES_TAC `ACONV c1 a` THENL
     [ASM_MESON_TAC[SEMANTICS_ACONV; welltyped]; ALL_TAC];
    ASM_CASES_TAC `ACONV c2 a` THENL
     [ASM_MESON_TAC[SEMANTICS_ACONV; welltyped]; ALL_TAC]] THEN
  (SUBGOAL_THEN
    `MEM a (FILTER (\x. ~ACONV c2 x) asl1) \/
     MEM a (FILTER (\x. ~ACONV c1 x) asl2)`
   MP_TAC THENL
    [REWRITE_TAC[MEM_FILTER] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o MATCH_MP TERM_UNION_THM) THEN
   ASM_MESON_TAC[SEMANTICS_ACONV; welltyped]));;

(* ------------------------------------------------------------------------- *)
(* Correct semantics for term substitution.                                  *)
(* ------------------------------------------------------------------------- *)

let DEST_VAR = new_recursive_definition term_RECURSION
 `DEST_VAR (Var x ty) = (x,ty)`;;

let TERM_VALUATION_ITLIST = prove
 (`!ilist sigma tau.
    type_valuation tau /\ term_valuation tau sigma /\
    (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty)
    ==> term_valuation tau
         (ITLIST (\(t,x). DEST_VAR x |-> semantics sigma tau t) ilist sigma)`,
  MATCH_MP_TAC list_INDUCT THEN SIMP_TAC[ITLIST] THEN
  REWRITE_TAC[FORALL_PAIR_THM; MEM; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; FORALL_AND_THM] THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DEST_VAR] THEN
  ASM_SIMP_TAC[TERM_VALUATION_VALMOD; SEMANTICS_TYPESET]);;

let ITLIST_VALMOD_FILTER = prove
 (`!ilist sigma sem x ty y yty.
     (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty)
     ==> (ITLIST (\(t,x). DEST_VAR x |-> sem x t)
           (FILTER (\(s',s). ~(s = Var x ty)) ilist) sigma (y,yty) =
          if (y = x) /\ (yty = ty) then sigma(y,yty)
          else ITLIST (\(t,x). DEST_VAR x |-> sem x t) ilist sigma (y,yty))`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[FILTER; ITLIST; COND_ID] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[MEM; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; PAIR_EQ] THEN
  REWRITE_TAC[WELLTYPED_CLAUSES; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  MAP_EVERY X_GEN_TAC [`t:term`; `pp:term`; `ilist:(term#term)list`] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:string` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `sty:type` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RATOR] THEN
  ASM_REWRITE_TAC[ITLIST] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[DEST_VAR] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RATOR] THEN
  REWRITE_TAC[VALMOD] THEN REWRITE_TAC[term_INJ] THEN
  ASM_CASES_TAC `(s:string = x) /\ (sty:type = ty)` THEN
  ASM_SIMP_TAC[PAIR_EQ] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let ITLIST_VALMOD_EQ = prove
 (`!l. (!t x. MEM (t,x) l /\ (f x = a) ==> (g x t = h x t)) /\ (i a = j a)
       ==> (ITLIST (\(t,x). f(x) |-> g x t) l i a =
            ITLIST (\(t,x). f(x) |-> h x t) l j a)`,
  MATCH_MP_TAC list_INDUCT THEN SIMP_TAC[MEM; ITLIST; FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ; VALMOD] THEN MESON_TAC[]);;

let SEMANTICS_VSUBST = prove
 (`!tm sigma tau ilist.
       welltyped tm /\
       (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty)
       ==> !sigma tau. type_valuation tau /\ term_valuation tau sigma
                       ==> (semantics sigma tau (VSUBST ilist tm) =
                            semantics
                             (ITLIST
                                (\(t,x). DEST_VAR x |-> semantics sigma tau t)
                                ilist sigma)
                             tau tm)`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[VSUBST; semantics] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`] THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[MEM; REV_ASSOCD; ITLIST; semantics; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:term`; `s:term`; `ilist:(term#term)list`] THEN
    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; PAIR_EQ] THEN
    REWRITE_TAC[WELLTYPED_CLAUSES; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
    DISCH_THEN(fun th ->
      DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:string` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `tty:type` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[DEST_VAR; VALMOD; term_INJ; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WELLTYPED_CLAUSES] THEN REPEAT STRIP_TAC THEN
    BINOP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN
  REWRITE_TAC[WELLTYPED_CLAUSES] THEN
  ASM_CASES_TAC `welltyped t` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN LET_TAC THEN LET_TAC THEN
  SUBGOAL_THEN
   `!s s'. MEM (s',s) ilist' ==> (?x ty. (s = Var x ty) /\ s' has_type ty)`
  ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN ASM_SIMP_TAC[MEM_FILTER]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REPEAT LET_TAC THEN
    SUBGOAL_THEN
     `!s s'. MEM (s',s) ilist'' ==> (?x ty. (s = Var x ty) /\ s' has_type ty)`
    ASSUME_TAC THENL
     [EXPAND_TAC "ilist''" THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
      ASM_MESON_TAC[has_type_RULES];
      ALL_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[semantics] THEN
  MATCH_MP_TAC ABSTRACT_EQ THEN ASM_SIMP_TAC[TYPESET_INHABITED] THEN
  X_GEN_TAC `a:V` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SEMANTICS_TYPESET) THEN
  ASM_SIMP_TAC[TERM_VALUATION_VALMOD; TERM_VALUATION_ITLIST] THEN
  EXPAND_TAC "t'" THEN
  ASM_SIMP_TAC[VSUBST_WELLTYPED; GSYM WELLTYPED; TERM_VALUATION_VALMOD] THEN
  MATCH_MP_TAC TERM_VALUATION_VFREE_IN THEN
  ASM_SIMP_TAC[TERM_VALUATION_VALMOD; TERM_VALUATION_ITLIST] THEN
  MAP_EVERY X_GEN_TAC [`u:string`; `uty:type`] THEN DISCH_TAC THENL
   [EXPAND_TAC "ilist''" THEN REWRITE_TAC[ITLIST] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[DEST_VAR; VALMOD; PAIR_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[semantics; VALMOD];
    ALL_TAC] THEN
  EXPAND_TAC "ilist'" THEN ASM_SIMP_TAC[ITLIST_VALMOD_FILTER] THEN
  REWRITE_TAC[VALMOD] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ITLIST_VALMOD_EQ THEN ASM_REWRITE_TAC[VALMOD; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`s':term`; `s:term`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP
     (ASSUME `MEM (s':term,s:term) ilist`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:string` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `wty:type` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    UNDISCH_TAC `DEST_VAR (Var w wty) = u,uty` THEN
    REWRITE_TAC[DEST_VAR; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    MATCH_MP_TAC TERM_VALUATION_VFREE_IN THEN
    ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[welltyped]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`v:string`; `vty:type`] THEN
    DISCH_TAC THEN REWRITE_TAC[VALMOD; PAIR_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EX]) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(MP_TAC o SPEC `(s':term,Var u uty)`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "ilist'" THEN
    REWRITE_TAC[MEM_FILTER] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_REWRITE_TAC[term_INJ]] THEN
  MP_TAC(ISPECL [`t':term`; `x:string`; `ty:type`] VARIANT) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "t'" THEN
  REWRITE_TAC[VFREE_IN_VSUBST] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) = b ==> ~a`] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:string`; `uty:type`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `REV_ASSOCD (Var u uty) ilist' (Var u uty) =
    REV_ASSOCD (Var u uty) ilist (Var u uty)`
  SUBST1_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[REV_ASSOCD_FILTER] THEN
    ASM_REWRITE_TAC[term_INJ];
    ALL_TAC] THEN
  UNDISCH_TAC
   `!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty` THEN
  SPEC_TAC(`ilist:(term#term)list`,`l:(term#term)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[REV_ASSOCD; ITLIST; VFREE_IN; VALMOD; term_INJ] THEN
  SIMP_TAC[PAIR_EQ] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[VALMOD; REV_ASSOCD; MEM] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; PAIR_EQ] THEN
  REWRITE_TAC[WELLTYPED_CLAUSES; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  MAP_EVERY X_GEN_TAC [`t1:term`; `t2:term`; `i:(term#term)list`] THEN
  DISCH_THEN(fun th ->
   DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN MP_TAC th) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:string` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `vty:type` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[DEST_VAR; term_INJ; PAIR_EQ] THEN
  SUBGOAL_THEN `(v:string = u) /\ (vty:type = uty) <=> (u = v) /\ (uty = vty)`
  SUBST1_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TERM_VALUATION_VFREE_IN THEN
  ASM_SIMP_TAC[TERM_VALUATION_VALMOD; VALMOD] THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[welltyped; term_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Hence correctness of INST.                                                *)
(* ------------------------------------------------------------------------- *)

let INST_correct = prove
 (`!ilist asl p.
        (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty)
        ==> asl |= p ==> MAP (VSUBST ilist) asl |= VSUBST ilist p`,
  REWRITE_TAC[sequent] THEN REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `ALL (\a. a has_type Bool) (CONS p asl)` THEN
    REWRITE_TAC[ALL; ALL_MAP] THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_THM]] THEN
    DISCH_TAC THEN MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped p` ASSUME_TAC THENL
   [ASM_MESON_TAC[welltyped; ALL]; ALL_TAC] THEN
  ASM_SIMP_TAC[SEMANTICS_VSUBST] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[TERM_VALUATION_ITLIST] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ALL_MAP]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
  X_GEN_TAC `a:term` THEN DISCH_TAC THEN
  SUBGOAL_THEN `welltyped a` MP_TAC THENL
   [ASM_MESON_TAC[ALL_MEM; MEM; welltyped]; ALL_TAC] THEN
  ASM_SIMP_TAC[SEMANTICS_VSUBST; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Lemma about typesets to simplify some later goals.                        *)
(* ------------------------------------------------------------------------- *)

let TYPESET_LEMMA = prove
 (`!ty tau tyin.
      typeset (\s. typeset tau (REV_ASSOCD (Tyvar s) tyin (Tyvar s))) ty =
      typeset tau (TYPE_SUBST tyin ty)`,
  MATCH_MP_TAC type_INDUCT THEN SIMP_TAC[typeset; TYPE_SUBST]);;

(* ------------------------------------------------------------------------- *)
(* Semantics of type instantiation core.                                     *)
(* ------------------------------------------------------------------------- *)

let SEMANTICS_INST_CORE = prove
 (`!n tm env tyin.
        welltyped tm /\ (sizeof tm = n) /\
        (!s s'. MEM (s,s') env
                ==> ?x ty. (s = Var x ty) /\
                           (s' = Var x (TYPE_SUBST tyin ty)))
        ==> (?x ty. (INST_CORE env tyin tm =
                     Clash(Var x (TYPE_SUBST tyin ty))) /\
                    VFREE_IN (Var x ty) tm /\
                    ~(REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                                 env (Var x ty) = Var x ty)) \/
            (!x ty. VFREE_IN (Var x ty) tm
                    ==> (REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                                 env (Var x ty) = Var x ty)) /\
            (?tm'. (INST_CORE env tyin tm = Result tm') /\
                   tm' has_type (TYPE_SUBST tyin (typeof tm)) /\
                   (!u uty. VFREE_IN (Var u uty) tm' <=>
                                ?oty. VFREE_IN (Var u oty) tm /\
                                      (uty = TYPE_SUBST tyin oty)) /\
                   !sigma tau.
                       type_valuation tau /\ term_valuation tau sigma
                       ==> (semantics sigma tau tm' =
                            semantics
                               (\(x,ty). sigma(x,TYPE_SUBST tyin ty))
                               (\s. typeset tau (TYPE_SUBST tyin (Tyvar s)))
                               tm))`,
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC term_INDUCT THEN
  ONCE_REWRITE_TAC[INST_CORE] THEN REWRITE_TAC[semantics] THEN
  REPEAT CONJ_TAC THENL
   [POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[REV_ASSOCD; LET_DEF; LET_END_DEF] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[result_DISTINCT; result_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[typeof; has_type_RULES] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[RESULT; semantics; VFREE_IN; term_INJ] THEN ASM_MESON_TAC[];
    POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[TYPE_SUBST; RESULT; VFREE_IN; term_DISTINCT] THEN
    ASM_REWRITE_TAC[result_DISTINCT; result_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[typeof; has_type_RULES; TYPE_SUBST; VFREE_IN] THEN
    REWRITE_TAC[semantics; typeset; TYPESET_LEMMA; TYPE_SUBST; term_DISTINCT];
    POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[TYPE_SUBST; RESULT; VFREE_IN; term_DISTINCT] THEN
    ASM_REWRITE_TAC[result_DISTINCT; result_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[typeof; has_type_RULES; TYPE_SUBST; VFREE_IN] THEN
    REWRITE_TAC[semantics; typeset; TYPESET_LEMMA; TYPE_SUBST; term_DISTINCT];
    MAP_EVERY X_GEN_TAC [`s:term`; `t:term`] THEN DISCH_THEN(K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN ASM_CASES_TAC `n = sizeof(Comb s t)` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `sizeof t` th) THEN
                         MP_TAC(SPEC `sizeof s` th)) THEN
    REWRITE_TAC[sizeof; ARITH_RULE `s < 1 + s + t /\ t < 1 + s + t`] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `t:term`) THEN
                         MP_TAC(SPEC `s:term` th)) THEN
    REWRITE_TAC[IMP_IMP; AND_FORALL_THM; WELLTYPED_CLAUSES] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN MP_TAC th) THEN
      DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; IS_CLASH; VFREE_IN];
      ALL_TAC] THEN
    REWRITE_TAC[TYPE_SUBST] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `s':term` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; IS_CLASH; VFREE_IN];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t':term` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[VFREE_IN] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `Comb s' t'` THEN
    ASM_SIMP_TAC[LET_DEF; LET_END_DEF; IS_CLASH; semantics; RESULT] THEN
    ASM_REWRITE_TAC[VFREE_IN] THEN
    ASM_REWRITE_TAC[typeof] THEN ONCE_REWRITE_TAC[has_type_CASES] THEN
    REWRITE_TAC[term_DISTINCT; term_INJ; codomain] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN
  DISCH_THEN(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `n = sizeof (Abs x ty t)` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN REPEAT LET_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `sizeof t`) THEN
  REWRITE_TAC[sizeof; ARITH_RULE `t < 2 + t`] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`t:term`; `env':(term#term)list`; `tyin:(type#type)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [EXPAND_TAC "env'" THEN REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ALL_TAC;
    FIRST_X_ASSUM(K ALL_TAC o SPEC `0`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t':term` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[IS_RESULT] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th ->
       MP_TAC th THEN MATCH_MP_TAC MONO_FORALL THEN
       GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
       DISCH_THEN(MP_TAC o check (is_imp o concl))) THEN
       EXPAND_TAC "env'" THEN
      REWRITE_TAC[VFREE_IN; REV_ASSOCD; term_INJ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[term_INJ] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[result_INJ; UNWIND_THM1; RESULT] THEN
    MATCH_MP_TAC(TAUT `a /\ b /\ (b ==> c) ==> b /\ a /\ c`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[VFREE_IN; term_INJ] THEN
      MAP_EVERY X_GEN_TAC [`u:string`; `uty:type`] THEN
      ASM_CASES_TAC `u:string = x` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_THEN `u:string = x` SUBST_ALL_TAC THEN
      REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `oty:type` THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `uty = TYPE_SUBST tyin oty` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `VFREE_IN (Var x oty) t` THEN ASM_REWRITE_TAC[] THEN
      EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      FIRST_X_ASSUM(fun th ->
       MP_TAC(SPECL [`x:string`; `oty:type`] th) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
      EXPAND_TAC "env'" THEN REWRITE_TAC[REV_ASSOCD] THEN
      ASM_MESON_TAC[term_INJ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[typeof; TYPE_SUBST] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[has_type_RULES];
      ALL_TAC] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[semantics] THEN
    ASM_REWRITE_TAC[TYPE_SUBST; TYPESET_LEMMA] THEN
    MATCH_MP_TAC ABSTRACT_EQ THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[TYPESET_INHABITED]; ALL_TAC] THEN
    X_GEN_TAC `a:V` THEN REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEMANTICS_TYPESET THEN
      ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN
      ASM_MESON_TAC[welltyped; WELLTYPED];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN CONJ_TAC THENL
     [DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SEMANTICS_TYPESET THEN
      ASM_SIMP_TAC[TERM_VALUATION_VALMOD];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(x,ty' |-> a) (sigma:(string#type)->V)`; `tau:string->V`]) THEN
    ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM(CONJUNCT1 TYPE_SUBST)] THEN
    MATCH_MP_TAC TERM_VALUATION_VFREE_IN THEN CONJ_TAC THENL
     [REWRITE_TAC[type_valuation] THEN ASM_SIMP_TAC[TYPESET_INHABITED];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[term_valuation] THEN
      MAP_EVERY X_GEN_TAC [`y:string`; `yty:type`] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[VALMOD; PAIR_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[TYPE_SUBST; TYPESET_LEMMA] THEN
      ASM_MESON_TAC[term_valuation];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[term_valuation] THEN
      MAP_EVERY X_GEN_TAC [`y:string`; `yty:type`] THEN
      REWRITE_TAC[VALMOD] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[VALMOD; PAIR_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[TYPE_SUBST; TYPESET_LEMMA] THEN
      ASM_MESON_TAC[term_valuation];
      ALL_TAC] THEN
    UNDISCH_THEN
     `!u uty.
         VFREE_IN (Var u uty) t' <=>
         (?oty. VFREE_IN (Var u oty) t /\ (uty = TYPE_SUBST tyin oty))`
     (K ALL_TAC) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y:string`; `yty:type`] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[VALMOD] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_CASES_TAC `y:string = x` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    ASM_CASES_TAC `yty:type = ty` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `y:string = x` SUBST_ALL_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:string`; `yty:type`]) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "env'" THEN
    ASM_REWRITE_TAC[REV_ASSOCD; term_INJ]] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:string` (X_CHOOSE_THEN `zty:type`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC))) THEN
  EXPAND_TAC "w" THEN REWRITE_TAC[CLASH; IS_RESULT; term_INJ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(K ALL_TAC o SPEC `0`) THEN
    DISCH_THEN(fun th ->
      DISJ1_TAC THEN REWRITE_TAC[result_INJ] THEN
      MAP_EVERY EXISTS_TAC [`z:string`; `zty:type`] THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[VFREE_IN; term_INJ] THEN
    EXPAND_TAC "env'" THEN ASM_REWRITE_TAC[REV_ASSOCD; term_INJ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[INST_CORE] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[letlemma] THEN
  ABBREV_TAC `env'' = CONS (Var x' ty,Var x' ty') env` THEN
  ONCE_REWRITE_TAC[letlemma] THEN
  ABBREV_TAC
   `ures = INST_CORE env'' tyin (VSUBST[Var x' ty,Var x ty] t)` THEN
  ONCE_REWRITE_TAC[letlemma] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sizeof t`) THEN
  REWRITE_TAC[sizeof; ARITH_RULE `t < 2 + t`] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`VSUBST [Var x' ty,Var x ty] t`;
                  `env'':(term#term)list`; `tyin:(type#type)list`] th) THEN
    MP_TAC(SPECL [`t:term`; `[]:(term#term)list`; `tyin:(type#type)list`]
       th)) THEN
  REWRITE_TAC[MEM; REV_ASSOCD] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':term` MP_TAC) THEN STRIP_TAC THEN
  UNDISCH_TAC `VARIANT (RESULT (INST_CORE [] tyin t)) x ty' = x'` THEN
  ASM_REWRITE_TAC[RESULT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t':term`; `x:string`; `ty':type`] VARIANT) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN DISCH_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      ASM_MESON_TAC[has_type_RULES];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SIZEOF_VSUBST THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[has_type_RULES];
      ALL_TAC] THEN
    EXPAND_TAC "env''" THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:string` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `vty:type` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[IS_RESULT; CLASH] THEN
    ONCE_REWRITE_TAC[letlemma] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[VFREE_IN_VSUBST] THEN EXPAND_TAC "env''" THEN
      REWRITE_TAC[REV_ASSOCD] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[term_INJ] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN MP_TAC) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[VFREE_IN; term_INJ] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [term_INJ]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    EXPAND_TAC "env''" THEN REWRITE_TAC[REV_ASSOCD] THEN
    ASM_CASES_TAC `vty:type = ty` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[VFREE_IN_VSUBST; NOT_EXISTS_THM; REV_ASSOCD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VFREE_IN; term_INJ] THEN
    MAP_EVERY X_GEN_TAC [`k:string`; `kty:type`] THEN
    MP_TAC(SPECL [`t':term`; `x:string`; `ty':type`] VARIANT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t'':term` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IS_RESULT; result_INJ; UNWIND_THM1; result_DISTINCT] THEN
  REWRITE_TAC[RESULT] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> c /\ a /\ d) ==> a /\ b /\ c /\ d`) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[typeof; TYPE_SUBST] THEN
    MATCH_MP_TAC(last(CONJUNCTS has_type_RULES)) THEN
    SUBGOAL_THEN `(VSUBST [Var x' ty,Var x ty] t) has_type (typeof t)`
      (fun th -> ASM_MESON_TAC[th; WELLTYPED_LEMMA]) THEN
    MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[GSYM WELLTYPED] THEN
    REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[has_type_RULES];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[VFREE_IN] THEN
    MAP_EVERY X_GEN_TAC [`k:string`; `kty:type`]  THEN
    ASM_REWRITE_TAC[VFREE_IN_VSUBST; REV_ASSOCD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VFREE_IN; term_INJ] THEN
    SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `x /\ (if p then a /\ b else c /\ b) <=>
                      b /\ x /\ (if p then a else c)`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    REWRITE_TAC[TAUT `x /\ (if p /\ q then a else b) <=>
                      p /\ q /\ a /\ x \/ b /\ ~(p /\ q) /\ x`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM1; UNWIND_THM2] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:string`; `kty:type`] THEN
    REWRITE_TAC[VFREE_IN] THEN STRIP_TAC THEN
    UNDISCH_TAC `!x'' ty'.
           VFREE_IN (Var x'' ty') (VSUBST [Var x' ty,Var x ty] t)
           ==> (REV_ASSOCD (Var x'' (TYPE_SUBST tyin ty')) env''
                           (Var x'' ty') = Var x'' ty')` THEN
    DISCH_THEN(MP_TAC o SPECL [`k:string`; `kty:type`]) THEN
    REWRITE_TAC[VFREE_IN_VSUBST; REV_ASSOCD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VFREE_IN] THEN
    REWRITE_TAC[VFREE_IN; term_INJ] THEN
    SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `x /\ (if p then a /\ b else c /\ b) <=>
                      b /\ x /\ (if p then a else c)`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    REWRITE_TAC[TAUT `x /\ (if p /\ q then a else b) <=>
                      p /\ q /\ a /\ x \/ b /\ ~(p /\ q) /\ x`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM1; UNWIND_THM2] THEN
    UNDISCH_TAC `~(Var x ty = Var k kty)` THEN
    REWRITE_TAC[term_INJ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "env''" THEN REWRITE_TAC[REV_ASSOCD] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[semantics] THEN
  REWRITE_TAC[TYPE_SUBST; TYPESET_LEMMA] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ABSTRACT_EQ THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[TYPESET_INHABITED]; ALL_TAC] THEN
  X_GEN_TAC `a:V` THEN REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SEMANTICS_TYPESET THEN
    ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN
    ASM_MESON_TAC[welltyped; WELLTYPED];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN CONJ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SEMANTICS_TYPESET THEN
    ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN
    SUBGOAL_THEN `(VSUBST [Var x' ty,Var x ty] t) has_type (typeof t)`
      (fun th -> ASM_MESON_TAC[th; WELLTYPED_LEMMA]) THEN
    MATCH_MP_TAC VSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[GSYM WELLTYPED] THEN
    REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[has_type_RULES];
    ALL_TAC] THEN
  W(fun (asl,w) -> FIRST_X_ASSUM(fun th ->
        MP_TAC(PART_MATCH (lhand o rand) th (lhand w)))) THEN
  ASM_SIMP_TAC[TERM_VALUATION_VALMOD] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM(CONJUNCT1 TYPE_SUBST)] THEN
  MP_TAC SEMANTICS_VSUBST THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  DISCH_THEN(fun th ->
   W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) th (lhand w)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN CONJ_TAC THENL
     [MESON_TAC[has_type_RULES]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[type_valuation] THEN ASM_SIMP_TAC[TYPESET_INHABITED];
      ALL_TAC] THEN
    REWRITE_TAC[term_valuation] THEN
    MAP_EVERY X_GEN_TAC [`y:string`; `yty:type`] THEN
    REWRITE_TAC[VALMOD] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[VALMOD; PAIR_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[TYPE_SUBST; TYPESET_LEMMA] THEN
    ASM_MESON_TAC[term_valuation];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM(CONJUNCT1 TYPE_SUBST)] THEN
  MATCH_MP_TAC TERM_VALUATION_VFREE_IN THEN CONJ_TAC THENL
   [REWRITE_TAC[type_valuation] THEN ASM_SIMP_TAC[TYPESET_INHABITED];
    ALL_TAC] THEN
  REWRITE_TAC[ITLIST] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[DEST_VAR] THEN REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REWRITE_TAC[term_valuation; semantics] THEN
    MAP_EVERY X_GEN_TAC [`k:string`; `kty:type`] THEN
    REWRITE_TAC[VALMOD] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[TYPESET_LEMMA; TYPE_SUBST] THEN
    SIMP_TAC[PAIR_EQ] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[term_valuation];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:string`; `kty:type`] THEN DISCH_TAC THEN
  REWRITE_TAC[VALMOD; semantics] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP_TAC[PAIR_EQ] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* So in particular, we get key properties of INST itself.                   *)
(* ------------------------------------------------------------------------- *)

let SEMANTICS_INST = prove
 (`!tyin tm.
        welltyped tm
        ==> (INST tyin tm) has_type (TYPE_SUBST tyin (typeof tm)) /\
            (!u uty. VFREE_IN (Var u uty) (INST tyin tm) <=>
                         ?oty. VFREE_IN (Var u oty) tm /\
                               (uty = TYPE_SUBST tyin oty)) /\
            !sigma tau.
                type_valuation tau /\ term_valuation tau sigma
                ==> (semantics sigma tau (INST tyin tm) =
                     semantics
                        (\(x,ty). sigma(x,TYPE_SUBST tyin ty))
                        (\s. typeset tau (TYPE_SUBST tyin (Tyvar s))) tm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`sizeof tm`; `tm:term`; `[]:(term#term)list`;
                `tyin:(type#type)list`] SEMANTICS_INST_CORE) THEN
  ASM_REWRITE_TAC[MEM; INST_DEF; REV_ASSOCD] THEN MESON_TAC[RESULT]);;

(* ------------------------------------------------------------------------- *)
(* Hence soundness of the INST_TYPE rule.                                    *)
(* ------------------------------------------------------------------------- *)

let INST_TYPE_correct = prove
 (`!tyin asl p. asl |= p ==> MAP (INST tyin) asl |= INST tyin p`,
  REWRITE_TAC[sequent] THEN REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `ALL (\a. a has_type Bool) (CONS p asl)` THEN
    REWRITE_TAC[ALL; ALL_MAP] THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_THM]] THEN
      ASM_MESON_TAC[SEMANTICS_INST; TYPE_SUBST; welltyped; WELLTYPED;
                    WELLTYPED_LEMMA];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped p` ASSUME_TAC THENL
   [ASM_MESON_TAC[welltyped; ALL]; ALL_TAC] THEN
  ASM_SIMP_TAC[SEMANTICS_INST] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[type_valuation] THEN ASM_MESON_TAC[TYPESET_INHABITED];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[term_valuation] THEN
    REWRITE_TAC[TYPE_SUBST; TYPESET_LEMMA] THEN
    ASM_MESON_TAC[term_valuation];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ALL_MAP]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
  X_GEN_TAC `a:term` THEN DISCH_TAC THEN
  SUBGOAL_THEN `welltyped a` MP_TAC THENL
   [ASM_MESON_TAC[ALL_MEM; MEM; welltyped]; ALL_TAC] THEN
  ASM_SIMP_TAC[SEMANTICS_INST; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Soundness.                                                                *)
(* ------------------------------------------------------------------------- *)

let HOL_IS_SOUND = prove
 (`!asl p. asl |- p ==> asl |= p`,
  MATCH_MP_TAC proves_INDUCT THEN
  REWRITE_TAC[REFL_correct; TRANS_correct; ABS_correct;
              BETA_correct; ASSUME_correct; EQ_MP_correct; INST_TYPE_correct;
              REWRITE_RULE[LET_DEF; LET_END_DEF] DEDUCT_ANTISYM_RULE_correct;
              REWRITE_RULE[IMP_IMP] INST_correct] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MK_COMB_correct THEN
  ASM_MESON_TAC[WELLTYPED_CLAUSES; MK_COMB_correct]);;

(* ------------------------------------------------------------------------- *)
(* Consistency.                                                              *)
(* ------------------------------------------------------------------------- *)

let HOL_IS_CONSISTENT = prove
 (`?p. p has_type Bool /\ ~([] |- p)`,
  SUBGOAL_THEN `?p. p has_type Bool /\ ~([] |= p)`
    (fun th -> MESON_TAC[th; HOL_IS_SOUND]) THEN
  EXISTS_TAC `Var x Bool === Var (VARIANT (Var x Bool) x Bool) Bool` THEN
  SIMP_TAC[EQUATION_HAS_TYPE_BOOL; WELLTYPED_CLAUSES; typeof;
           sequent; ALL; SEMANTICS_EQUATION; has_type_RULES; semantics;
           BOOLEAN_EQ_TRUE] THEN
  MP_TAC(SPECL [`Var x Bool`; `x:string`; `Bool`] VARIANT) THEN
  ABBREV_TAC `y = VARIANT (Var x Bool) x Bool` THEN
  REWRITE_TAC[VFREE_IN; term_INJ; NOT_FORALL_THM] THEN DISCH_TAC THEN
  EXISTS_TAC `((x:string,Bool) |-> false) (((y,Bool) |-> true)
                        (\(x,ty). @a. a <: typeset (\x. boolset) ty))` THEN
  EXISTS_TAC `\x:string. boolset` THEN
  ASM_REWRITE_TAC[type_valuation; VALMOD; PAIR_EQ; TRUE_NE_FALSE] THEN
  CONJ_TAC THENL [MESON_TAC[IN_BOOL]; ALL_TAC] THEN
  REWRITE_TAC[term_valuation] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[VALMOD; PAIR_EQ] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[typeset; IN_BOOL]) THEN
  CONV_TAC SELECT_CONV THEN MATCH_MP_TAC TYPESET_INHABITED THEN
  REWRITE_TAC[type_valuation] THEN MESON_TAC[IN_BOOL]);;
