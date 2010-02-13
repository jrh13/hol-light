(* ========================================================================= *)
(* Syntactic definitions for "core HOL", including provability.              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* HOL types. Just do the primitive ones for now.                            *)
(* ------------------------------------------------------------------------- *)

let type_INDUCT,type_RECURSION = define_type
  "type = Tyvar string
            | Bool
            | Ind
            | Fun type type";;

let type_DISTINCT = distinctness "type";;

let type_INJ = injectivity "type";;

let domain = define
  `domain (Fun s t) = s`;;

let codomain = define
  `codomain (Fun s t) = t`;;

(* ------------------------------------------------------------------------- *)
(* HOL terms. To avoid messing round with specification of the language,     *)
(* we just put "=" and "@" in as the only constants. For now...              *)
(* ------------------------------------------------------------------------- *)

let term_INDUCT,term_RECURSION = define_type
 "term = Var string type
       | Equal type | Select type
       | Comb term term
       | Abs string type term";;

let term_DISTINCT = distinctness "term";;

let term_INJ = injectivity "term";;

(* ------------------------------------------------------------------------- *)
(* Typing judgements.                                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_type",(12,"right"));;

let has_type_RULES,has_type_INDUCT,has_type_CASES = new_inductive_definition
  `(!n ty. (Var n ty) has_type ty) /\
   (!ty. (Equal ty) has_type (Fun ty (Fun ty Bool))) /\
   (!ty. (Select ty) has_type (Fun (Fun ty Bool) ty)) /\
   (!s t dty rty. s has_type (Fun dty rty) /\ t has_type dty
                  ==> (Comb s t) has_type rty) /\
   (!n dty t rty. t has_type rty ==> (Abs n dty t) has_type (Fun dty rty))`;;

let welltyped = new_definition
  `welltyped tm <=> ?ty. tm has_type ty`;;

let typeof = define
 `(typeof (Var n ty) = ty) /\
  (typeof (Equal ty) = Fun ty (Fun ty Bool)) /\
  (typeof (Select ty) = Fun (Fun ty Bool) ty) /\
  (typeof (Comb s t) = codomain (typeof s)) /\
  (typeof (Abs n ty t) = Fun ty (typeof t))`;;

let WELLTYPED_LEMMA = prove
 (`!tm ty. tm has_type ty ==> (typeof tm = ty)`,
  MATCH_MP_TAC has_type_INDUCT THEN
  SIMP_TAC[typeof; has_type_RULES; codomain]);;

let WELLTYPED = prove
 (`!tm. welltyped tm <=> tm has_type (typeof tm)`,
  REWRITE_TAC[welltyped] THEN MESON_TAC[WELLTYPED_LEMMA]);;

let WELLTYPED_CLAUSES = prove
 (`(!n ty. welltyped(Var n ty)) /\
   (!ty. welltyped(Equal ty)) /\
   (!ty. welltyped(Select ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!n ty t. welltyped (Abs n ty t) = welltyped t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[welltyped] THEN
  (GEN_REWRITE_TAC BINDER_CONV [has_type_CASES] ORELSE
   GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [has_type_CASES]) THEN
  REWRITE_TAC[term_INJ; term_DISTINCT] THEN
  MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Since equations are important, a bit of derived syntax.                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("===",(18,"right"));;

let equation = new_definition
 `(s === t) = Comb (Comb (Equal(typeof s)) s) t`;;

let EQUATION_HAS_TYPE_BOOL = prove
 (`!s t. (s === t) has_type Bool
         <=> welltyped s /\ welltyped t /\ (typeof s = typeof t)`,
  REWRITE_TAC[equation] THEN
  ONCE_REWRITE_TAC[has_type_CASES] THEN
  REWRITE_TAC[term_DISTINCT; term_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM1] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV) [has_type_CASES] THEN
  REWRITE_TAC[term_DISTINCT; term_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2(BINDER_CONV o LAND_CONV))
    [has_type_CASES] THEN
  REWRITE_TAC[term_DISTINCT; term_INJ; type_INJ] THEN
  MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Alpha-conversion.                                                         *)
(* ------------------------------------------------------------------------- *)

let ALPHAVARS = define
  `(ALPHAVARS [] tmp <=> (FST tmp = SND tmp)) /\
   (ALPHAVARS (CONS tp oenv) tmp <=>
        (tmp = tp) \/
        ~(FST tp = FST tmp) /\ ~(SND tp = SND tmp) /\ ALPHAVARS oenv tmp)`;;

let RACONV_RULES,RACONV_INDUCT,RACONV_CASES = new_inductive_definition
 `(!env x1 ty1 x2 ty2.
       ALPHAVARS env (Var x1 ty1,Var x2 ty2)
       ==> RACONV env (Var x1 ty1,Var x2 ty2)) /\
  (!env ty. RACONV env (Equal ty,Equal ty)) /\
  (!env ty. RACONV env (Select ty,Select ty)) /\
  (!env s1 t1 s2 t2.
       RACONV env (s1,s2) /\ RACONV env (t1,t2)
       ==> RACONV env (Comb s1 t1,Comb s2 t2)) /\
  (!env x1 ty1 t1 x2 ty2 t2.
       (ty1 = ty2) /\ RACONV (CONS ((Var x1 ty1),(Var x2 ty2)) env) (t1,t2)
       ==> RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2))`;;

let RACONV = prove
 (`(RACONV env (Var x1 ty1,Var x2 ty2) <=>
        ALPHAVARS env (Var x1 ty1,Var x2 ty2)) /\
   (RACONV env (Var x1 ty1,Equal ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Select ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1 ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Equal ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Equal ty1,Equal ty2) <=> (ty1 = ty2)) /\
   (RACONV env (Equal ty1,Select ty2) <=> F) /\
   (RACONV env (Equal ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Equal ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Select ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Select ty1,Equal ty2) <=> F) /\
   (RACONV env (Select ty1,Select ty2) <=> (ty1 = ty2)) /\
   (RACONV env (Select ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Select ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Equal ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Select ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Var x2 ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Equal ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Select ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Comb l2 r2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2) <=>
        (ty1 = ty2) /\ RACONV (CONS (Var x1 ty1,Var x2 ty2) env) (t1,t2))`,
  REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RACONV_CASES] THEN
  REWRITE_TAC[term_INJ; term_DISTINCT; PAIR_EQ] THEN MESON_TAC[]);;

let ACONV = new_definition
 `ACONV t1 t2 <=> RACONV [] (t1,t2)`;;

(* ------------------------------------------------------------------------- *)
(* Reflexivity.                                                              *)
(* ------------------------------------------------------------------------- *)

let ALPHAVARS_REFL = prove
 (`!env t. ALL (\(s,t). s = t) env ==> ALPHAVARS env (t,t)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL; ALPHAVARS] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[PAIR_EQ]);;

let RACONV_REFL = prove
 (`!t env. ALL (\(s,t). s = t) env ==> RACONV env (t,t)`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[RACONV] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[ALPHAVARS_REFL];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[]]);;

let ACONV_REFL = prove
 (`!t. ACONV t t`,
  REWRITE_TAC[ACONV] THEN SIMP_TAC[RACONV_REFL; ALL]);;

(* ------------------------------------------------------------------------- *)
(* Alpha-convertible terms have the same type (if welltyped).                *)
(* ------------------------------------------------------------------------- *)

let ALPHAVARS_TYPE = prove
 (`!env s t. ALPHAVARS env (s,t) /\
             ALL (\(x,y). welltyped x /\ welltyped y /\
                          (typeof x = typeof y)) env /\
             welltyped s /\ welltyped t
           ==> (typeof s = typeof t)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; ALPHAVARS; ALL; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let RACONV_TYPE = prove
 (`!env p. RACONV env p
           ==> ALL (\(x,y). welltyped x /\ welltyped y /\
                        (typeof x = typeof y)) env /\
               welltyped (FST p) /\ welltyped (SND p)
               ==> (typeof (FST p) = typeof (SND p))`,
  MATCH_MP_TAC RACONV_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; typeof] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[typeof; ALPHAVARS_TYPE];
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[WELLTYPED_CLAUSES];
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[typeof] THEN ASM_MESON_TAC[WELLTYPED_CLAUSES]]);;

let ACONV_TYPE = prove
 (`!s t. ACONV s t ==> welltyped s /\ welltyped t ==> (typeof s = typeof t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`[]:(term#term)list`; `(s:term,t:term)`] RACONV_TYPE) THEN
  REWRITE_TAC[ACONV; ALL] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* HOL version of "term_union".                                              *)
(* ------------------------------------------------------------------------- *)

let TERM_UNION = define
 `(TERM_UNION [] l2 = l2) /\
  (TERM_UNION (CONS h t) l2 =
        let subun = TERM_UNION t l2 in
        if EX (ACONV h) subun then subun else CONS h subun)`;;

let TERM_UNION_NONEW = prove
 (`!l1 l2 x. MEM x (TERM_UNION l1 l2) ==> MEM x l1 \/ MEM x l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TERM_UNION; MEM] THEN
  LET_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[MEM] THEN ASM_MESON_TAC[ACONV_REFL]);;

let TERM_UNION_THM = prove
 (`!l1 l2 x. MEM x l1 \/ MEM x l2
             ==> ?y. MEM y (TERM_UNION l1 l2) /\ ACONV x y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TERM_UNION; MEM; GSYM EX_MEM] THENL
   [MESON_TAC[ACONV_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN LET_TAC THEN COND_CASES_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MEM] THEN  ASM_MESON_TAC[ACONV_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Handy lemma for using it in a sequent.                                    *)
(* ------------------------------------------------------------------------- *)

let ALL_BOOL_TERM_UNION = prove
 (`ALL (\a. a has_type Bool) l1 /\ ALL (\a. a has_type Bool) l2
   ==> ALL (\a. a has_type Bool) (TERM_UNION l1 l2)`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[TERM_UNION_NONEW]);;

(* ------------------------------------------------------------------------- *)
(* Whether a variable/constant is free in a term.                            *)
(* ------------------------------------------------------------------------- *)

let VFREE_IN = define
  `(VFREE_IN v (Var x ty) <=> (Var x ty = v)) /\
   (VFREE_IN v (Equal ty) <=> (Equal ty = v)) /\
   (VFREE_IN v (Select ty) <=> (Select ty = v)) /\
   (VFREE_IN v (Comb s t) <=> VFREE_IN v s \/ VFREE_IN v t) /\
   (VFREE_IN v (Abs x ty t) <=> ~(Var x ty = v) /\ VFREE_IN v t)`;;

let VFREE_IN_RACONV = prove
 (`!env p. RACONV env p
           ==> !x ty. VFREE_IN (Var x ty) (FST p) /\
                      ~(?y. MEM (Var x ty,y) env) <=>
                      VFREE_IN (Var x ty) (SND p) /\
                      ~(?y. MEM (y,Var x ty) env)`,
  MATCH_MP_TAC RACONV_INDUCT THEN REWRITE_TAC[VFREE_IN; term_DISTINCT] THEN
  REWRITE_TAC[PAIR_EQ; term_INJ; MEM] THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALPHAVARS] THEN
  REWRITE_TAC[MEM; FORALL_PAIR_THM; term_INJ; PAIR_EQ] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MESON_TAC[]);;

let VFREE_IN_ACONV = prove
 (`!s t x t. ACONV s t ==> (VFREE_IN (Var x ty) s <=> VFREE_IN (Var x ty) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ACONV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP VFREE_IN_RACONV) THEN
  SIMP_TAC[MEM; FST; SND]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary association list function.                                      *)
(* ------------------------------------------------------------------------- *)

let REV_ASSOCD = define
  `(REV_ASSOCD a [] d = d) /\
   (REV_ASSOCD a (CONS (x,y) t) d =
        if y = a then x else REV_ASSOCD a t d)`;;

(* ------------------------------------------------------------------------- *)
(* Substition of types in types.                                             *)
(* ------------------------------------------------------------------------- *)

let TYPE_SUBST = define
 `(TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) /\
  (TYPE_SUBST i Bool = Bool) /\
  (TYPE_SUBST i Ind = Ind) /\
  (TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2))`;;

(* ------------------------------------------------------------------------- *)
(* Variant function. Deliberately underspecified at the moment. In a bid to  *)
(* expunge use of sets, just pick it distinct from what's free in a term.    *)
(* ------------------------------------------------------------------------- *)

let VFREE_IN_FINITE = prove
 (`!t. FINITE {x | VFREE_IN x t}`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[VFREE_IN] THEN
  REWRITE_TAC[SET_RULE `{x | a = x} = {a}`;
              SET_RULE `{x | P x \/ Q x} = {x | P x} UNION {x | Q x}`;
              SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[FINITE_INSERT; FINITE_RULES; FINITE_UNION; FINITE_INTER]);;

let VFREE_IN_FINITE_ALT = prove
 (`!t ty. FINITE {x | VFREE_IN (Var x ty) t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(Var x ty). x) {x | VFREE_IN x t}` THEN
  SIMP_TAC[VFREE_IN_FINITE; FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:string` THEN DISCH_TAC THEN
  EXISTS_TAC `Var x ty` THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[]);;

let VARIANT_EXISTS = prove
 (`!t x:string ty. ?x'. ~(VFREE_IN (Var x' ty) t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:term`; `ty:type`] VFREE_IN_FINITE_ALT) THEN
  DISCH_THEN(MP_TAC o CONJ string_INFINITE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_DIFF_FINITE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_ELIM_THM; IN_UNIV]);;

let VARIANT = new_specification ["VARIANT"]
 (PURE_REWRITE_RULE[SKOLEM_THM] VARIANT_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* Term substitution.                                                        *)
(* ------------------------------------------------------------------------- *)

let VSUBST = define
  `(VSUBST ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) /\
   (VSUBST ilist (Equal ty) = Equal ty) /\
   (VSUBST ilist (Select ty) = Select ty) /\
   (VSUBST ilist (Comb s t) = Comb (VSUBST ilist s) (VSUBST ilist t)) /\
   (VSUBST ilist (Abs x ty t) =
        let ilist' = FILTER (\(s',s). ~(s = Var x ty)) ilist in
        let t' = VSUBST ilist' t in
        if EX (\(s',s). VFREE_IN (Var x ty) s' /\ VFREE_IN s t) ilist'
        then let z = VARIANT t' x ty in
             let ilist'' = CONS (Var z ty,Var x ty) ilist' in
             Abs z ty (VSUBST ilist'' t)
        else Abs x ty t')`;;

(* ------------------------------------------------------------------------- *)
(* Preservation of type.                                                     *)
(* ------------------------------------------------------------------------- *)

let VSUBST_HAS_TYPE = prove
 (`!tm ty ilist.
        tm has_type ty /\
        (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty)
        ==> (VSUBST ilist tm) has_type ty`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[VSUBST] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `tty:type`] THEN
    MATCH_MP_TAC list_INDUCT THEN
    SIMP_TAC[REV_ASSOCD; MEM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; PAIR_EQ] THEN
    REWRITE_TAC[ LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
    ASM_CASES_TAC `(Var x ty) has_type tty` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_type_CASES]) THEN
    REWRITE_TAC[term_DISTINCT; term_INJ; LEFT_EXISTS_AND_THM] THEN
    REWRITE_TAC[GSYM EXISTS_REFL] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY X_GEN_TAC [`s:term`; `u:term`; `ilist:(term#term)list`] THEN
    DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:string` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `aty:type` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_MESON_TAC[term_INJ];
    SIMP_TAC[];
    SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:term`; `t:term`] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_type_CASES]) THEN
    REWRITE_TAC[term_DISTINCT; term_INJ; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    DISCH_THEN(X_CHOOSE_THEN `dty:type` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(el 3 (CONJUNCTS has_type_RULES)) THEN
    EXISTS_TAC `dty:type` THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`fty:type`; `ilist:(term#term)list`] THEN STRIP_TAC THEN
  LET_TAC THEN LET_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_type_CASES]) THEN
  REWRITE_TAC[term_DISTINCT; term_INJ; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  DISCH_THEN(X_CHOOSE_THEN `rty:type` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REPEAT LET_TAC THEN
  MATCH_MP_TAC(el 4 (CONJUNCTS has_type_RULES)) THEN
  EXPAND_TAC "t'" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXPAND_TAC ["ilist''"; "ilist'"]; EXPAND_TAC "ilist'"] THEN
  REWRITE_TAC[MEM; MEM_FILTER] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[has_type_RULES]);;

let VSUBST_WELLTYPED = prove
 (`!tm ty ilist.
        welltyped tm /\
        (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty)
        ==> welltyped (VSUBST ilist tm)`,
  MESON_TAC[VSUBST_HAS_TYPE; welltyped]);;

(* ------------------------------------------------------------------------- *)
(* Right set of free variables.                                              *)
(* ------------------------------------------------------------------------- *)

let REV_ASSOCD_FILTER = prove
 (`!l:(B#A)list a b d.
        REV_ASSOCD a (FILTER (\(y,x). P x) l) b =
            if P a then REV_ASSOCD a l b else b`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[REV_ASSOCD; FILTER; COND_ID] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `x:A`; `l:(B#A)list`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REV_ASSOCD] THEN
  ASM_CASES_TAC `(P:A->bool) x` THEN ASM_REWRITE_TAC[REV_ASSOCD] THEN
  ASM_MESON_TAC[]);;

let VFREE_IN_VSUBST = prove
 (`!tm u uty ilist.
      VFREE_IN (Var u uty) (VSUBST ilist tm) <=>
        ?y ty. VFREE_IN (Var y ty) tm /\
               VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[VFREE_IN; VSUBST; term_DISTINCT] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[term_INJ];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN LET_TAC THEN LET_TAC THEN
  COND_CASES_TAC THEN REPEAT LET_TAC THEN
  ASM_REWRITE_TAC[VFREE_IN] THENL
   [MAP_EVERY EXPAND_TAC ["ilist''"; "ilist'"];
    EXPAND_TAC "t'" THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "ilist'"] THEN
  SIMP_TAC[REV_ASSOCD; REV_ASSOCD_FILTER] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VFREE_IN] THEN
  REWRITE_TAC[TAUT `(if ~b then x:bool else y) <=> (if b then y else x)`] THEN
  ONCE_REWRITE_TAC[TAUT `~a /\ b <=> ~(~a ==> ~b)`] THEN
  SIMP_TAC[TAUT `(if b then F else c) <=> ~b /\ c`] THEN
  MATCH_MP_TAC(TAUT
   `(a ==> ~c) /\ (~a ==> (b <=> c)) ==> (~(~a ==> ~b) <=> c)`) THEN
  (CONJ_TAC THENL [ALL_TAC; MESON_TAC[]]) THEN
  GEN_REWRITE_TAC LAND_CONV [term_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[NOT_IMP] THENL
   [MP_TAC(ISPECL [`VSUBST ilist' t`; `x:string`; `ty:type`] VARIANT) THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "ilist'" THEN ASM_REWRITE_TAC[REV_ASSOCD_FILTER] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EX]) THEN
  EXPAND_TAC "ilist'" THEN
  SPEC_TAC(`ilist:(term#term)list`,`l:(term#term)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL; REV_ASSOCD; VFREE_IN] THEN
  REWRITE_TAC[REV_ASSOCD; FILTER; FORALL_PAIR_THM] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[ALL] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sum type to model exception-raising.                                      *)
(* ------------------------------------------------------------------------- *)

let result_INDUCT,result_RECURSION = define_type
 "result = Clash term | Result term";;

let result_INJ = injectivity "result";;

let result_DISTINCT = distinctness "result";;

(* ------------------------------------------------------------------------- *)
(* Discriminators and extractors. (Nicer to pattern-match...)                *)
(* ------------------------------------------------------------------------- *)

let IS_RESULT = define
 `(IS_RESULT(Clash t) = F) /\
  (IS_RESULT(Result t) = T)`;;

let IS_CLASH = define
 `(IS_CLASH(Clash t) = T) /\
  (IS_CLASH(Result t) = F)`;;

let RESULT = define
 `RESULT(Result t) = t`;;

let CLASH = define
 `CLASH(Clash t) = t`;;

(* ------------------------------------------------------------------------- *)
(* We want induction/recursion on term size next.                            *)
(* ------------------------------------------------------------------------- *)

let rec sizeof = define
 `(sizeof (Var x ty) = 1) /\
  (sizeof (Equal ty) = 1) /\
  (sizeof (Select ty) = 1) /\
  (sizeof (Comb s t) = 1 + sizeof s + sizeof t) /\
  (sizeof (Abs x ty t) = 2 + sizeof t)`;;

let SIZEOF_VSUBST = prove
 (`!t ilist. (!s' s. MEM (s',s) ilist ==> ?x ty. s' = Var x ty)
             ==> (sizeof (VSUBST ilist t) = sizeof t)`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[VSUBST; sizeof] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`] THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[MEM; REV_ASSOCD; sizeof; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`s':term`; `s:term`; `l:(term#term)list`] THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[sizeof];
    ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN
  DISCH_TAC THEN X_GEN_TAC `ilist:(term#term)list` THEN DISCH_TAC THEN
  LET_TAC THEN LET_TAC THEN COND_CASES_TAC THEN
  REPEAT LET_TAC THEN REWRITE_TAC[sizeof; EQ_ADD_LCANCEL] THENL
   [ALL_TAC; ASM_MESON_TAC[MEM_FILTER]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXPAND_TAC "ilist''" THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
  ASM_MESON_TAC[MEM_FILTER]);;

(* ------------------------------------------------------------------------- *)
(* Prove existence of INST_CORE.                                             *)
(* ------------------------------------------------------------------------- *)

let INST_CORE_EXISTS = prove
 (`?INST_CORE.
  (!env tyin x ty.
        INST_CORE env tyin (Var x ty) =
          let tm = Var x ty
          and tm' = Var x (TYPE_SUBST tyin ty) in
         if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm') /\
  (!env tyin ty.
        INST_CORE env tyin (Equal ty) = Result(Equal(TYPE_SUBST tyin ty))) /\
  (!env tyin ty.
        INST_CORE env tyin (Select ty) = Result(Select(TYPE_SUBST tyin ty))) /\
  (!env tyin s t.
        INST_CORE env tyin (Comb s t) =
            let sres = INST_CORE env tyin s in
            if IS_CLASH sres then sres else
            let tres = INST_CORE env tyin t in
            if IS_CLASH tres then tres else
            let s' = RESULT sres and t' = RESULT tres in
            Result (Comb s' t')) /\
  (!env tyin x ty t.
        INST_CORE env tyin (Abs x ty t) =
            let ty' = TYPE_SUBST tyin ty in
            let env' = CONS (Var x ty,Var x ty') env in
            let tres = INST_CORE env' tyin t in
            if IS_RESULT tres then Result(Abs x ty' (RESULT tres)) else
            let w = CLASH tres in
            if ~(w = Var x ty') then tres else
            let x' = VARIANT (RESULT(INST_CORE [] tyin t)) x ty' in
            INST_CORE env tyin (Abs x' ty (VSUBST [Var x' ty,Var x ty] t)))`,
  W(fun (asl,w) -> MATCH_MP_TAC(DISCH_ALL
   (pure_prove_recursive_function_exists w))) THEN
  EXISTS_TAC `MEASURE(\(env:(term#term)list,tyin:(type#type)list,t).
                        sizeof t)` THEN
  REWRITE_TAC[WF_MEASURE; MEASURE_LE; MEASURE] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP_TAC[MEM; PAIR_EQ; term_INJ; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
           GSYM EXISTS_REFL; SIZEOF_VSUBST; LE_REFL; sizeof] THEN
  REPEAT STRIP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* So define it.                                                             *)
(* ------------------------------------------------------------------------- *)

let INST_CORE = new_specification ["INST_CORE"] INST_CORE_EXISTS;;

(* ------------------------------------------------------------------------- *)
(* And the overall function.                                                 *)
(* ------------------------------------------------------------------------- *)

let INST_DEF = new_definition
 `INST tyin tm = RESULT(INST_CORE [] tyin tm)`;;

(* ------------------------------------------------------------------------- *)
(* Various misc lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

let NOT_IS_RESULT = prove
 (`!r. ~(IS_RESULT r) <=> IS_CLASH r`,
  MATCH_MP_TAC result_INDUCT THEN REWRITE_TAC[IS_RESULT; IS_CLASH]);;

let letlemma = prove
 (`(let x = t in P x) = P t`,
  REWRITE_TAC[LET_DEF; LET_END_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Put everything together into a deductive system.                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("|-",(11,"right"));;

let prove_RULES,proves_INDUCT,proves_CASES = new_inductive_definition
 `(!t. welltyped t ==> [] |- t === t) /\
  (!asl1 asl2 l m1 m2 r.
        asl1 |- l === m1 /\ asl2 |- m2 === r /\ ACONV m1 m2
        ==> TERM_UNION asl1 asl2 |- l === r) /\
  (!asl1 l1 r1 asl2 l2 r2.
        asl1 |- l1 === r1 /\ asl2 |- l2 === r2 /\ welltyped(Comb l1 l2)
        ==> TERM_UNION asl1 asl2 |- Comb l1 l2 === Comb r1 r2) /\
  (!asl x ty l r.
        ~(EX (VFREE_IN (Var x ty)) asl) /\ asl |- l === r
        ==> asl |- (Abs x ty l) === (Abs x ty r)) /\
  (!x ty t. welltyped t ==> [] |- Comb (Abs x ty t) (Var x ty) === t) /\
  (!p. p has_type Bool ==> [p] |- p) /\
  (!asl1 asl2 p q p'.
        asl1 |- p === q /\ asl2 |- p' /\ ACONV p p'
        ==> TERM_UNION asl1 asl2 |- q) /\
  (!asl1 asl2 c1 c2.
        asl1 |- c1 /\ asl2 |- c2
        ==> TERM_UNION (FILTER((~) o ACONV c2) asl1)
                       (FILTER((~) o ACONV c1) asl2)
               |- c1 === c2) /\
  (!tyin asl p. asl |- p ==> MAP (INST tyin) asl |- INST tyin p) /\
  (!ilist asl p.
      (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty) /\
      asl |- p ==> MAP (VSUBST ilist) asl |- VSUBST ilist p)`;;
