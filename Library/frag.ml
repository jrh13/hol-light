(* ========================================================================= *)
(* A formulation of free Abelian groups on :A using a type :(A)frag.         *)
(* ========================================================================= *)

let frag_tybij =
  let th = prove
   (`?f:A->int. FINITE {x | ~(f x = &0)}`,
    EXISTS_TAC `(\x. &0):A->int` THEN
    REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]) in
  new_type_definition "frag" ("mk_frag","dest_frag") th;;

let frag_support = new_definition
 `frag_support (x:A frag) = {a | ~(dest_frag x a = &0)}`;;

let frag_0 = new_definition
 `frag_0:A frag = mk_frag (\x. &0)`;;

let frag_of = new_definition
 `frag_of (c:A) = mk_frag (\a. if a = c then &1 else &0)`;;

let frag_neg = new_definition
 `frag_neg (x:A frag) = mk_frag (\a. --(dest_frag x a))`;;

let frag_cmul = new_definition
 `frag_cmul c (x:A frag) = mk_frag (\a. c * dest_frag x a)`;;

let frag_add = new_definition
 `frag_add (x:A frag) y = mk_frag (\a. dest_frag x a + dest_frag y a)`;;

let frag_sub = new_definition
 `frag_sub (x:A frag) y = mk_frag (\a. dest_frag x a - dest_frag y a)`;;

let FRAG_EQ = prove
 (`!c1 c2:A frag. c1 = c2 <=> dest_frag c1 = dest_frag c2`,
  MESON_TAC[frag_tybij]);;

let DEST_FRAG_0 = prove
 (`dest_frag(frag_0:A frag) = \x. &0`,
  REWRITE_TAC[frag_0; GSYM(CONJUNCT2 frag_tybij)] THEN
  REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]);;

let DEST_FRAG_OF = prove
 (`!c:A. dest_frag(frag_of c) = \a. if a = c then &1 else &0`,
  REWRITE_TAC[frag_of; GSYM(CONJUNCT2 frag_tybij)] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[MESON[] `~(if p then F else T) <=> p`] THEN
  REWRITE_TAC[SING_GSPEC; FINITE_SING]);;

let DEST_FRAG_NEG = prove
 (`!x:A frag. dest_frag(frag_neg x) = \a. --(dest_frag x a)`,
  REWRITE_TAC[frag_neg; GSYM(CONJUNCT2 frag_tybij)] THEN
  REWRITE_TAC[INT_NEG_EQ_0] THEN REWRITE_TAC[frag_tybij; ETA_AX]);;

let DEST_FRAG_CMUL = prove
 (`!c x:A frag. dest_frag(frag_cmul c x) = \a. c * dest_frag x a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frag_cmul; GSYM(CONJUNCT2 frag_tybij)] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{a:A | ~(dest_frag x a = &0)}` THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM; INT_MUL_RZERO] THEN
  REWRITE_TAC[frag_tybij; ETA_AX]);;

let DEST_FRAG_ADD = prove
 (`!x y:A frag. dest_frag(frag_add x y) = \a. dest_frag x a + dest_frag y a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frag_add; GSYM(CONJUNCT2 frag_tybij)] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `{a:A | ~(dest_frag x a = &0)} UNION {a | ~(dest_frag y a = &0)}` THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
  SIMP_TAC[GSYM DE_MORGAN_THM; CONTRAPOS_THM; INT_ADD_LID] THEN
  REWRITE_TAC[FINITE_UNION; frag_tybij; ETA_AX]);;

let DEST_FRAG_SUB = prove
 (`!x y:A frag. dest_frag(frag_sub x y) = \a. dest_frag x a - dest_frag y a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frag_sub; GSYM(CONJUNCT2 frag_tybij)] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `{a:A | ~(dest_frag x a = &0)} UNION {a | ~(dest_frag y a = &0)}` THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
  SIMP_TAC[GSYM DE_MORGAN_THM; CONTRAPOS_THM; INT_SUB_RZERO] THEN
  REWRITE_TAC[FINITE_UNION; frag_tybij; ETA_AX]);;

let FRAG_OF_NONZERO = prove
 (`!a:A. ~(frag_of a = frag_0)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `a:A` o MATCH_MP (MESON[]
   `c = d ==> !a:A. dest_frag c a = dest_frag d a`)) THEN
  REWRITE_TAC[DEST_FRAG_OF; DEST_FRAG_0] THEN
  CONV_TAC INT_REDUCE_CONV);;

let FRAG_MODULE =
  let tac =
    REPEAT(CONJ_TAC ORELSE GEN_TAC) THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV
    [MESON[CONJUNCT1 frag_tybij; FUN_EQ_THM]
      `!x y:A frag. x = y <=> !a. dest_frag x a = dest_frag y a`] THEN
   GEN_REWRITE_TAC TOP_DEPTH_CONV
     [DEST_FRAG_0; DEST_FRAG_NEG; DEST_FRAG_CMUL;
      DEST_FRAG_ADD; DEST_FRAG_SUB; BETA_THM] THEN
   GEN_REWRITE_TAC DEPTH_CONV
    [AND_FORALL_THM; LEFT_OR_FORALL_THM; RIGHT_OR_FORALL_THM] THEN
   ((MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) ORELSE
    TRY(AP_TERM_TAC THEN ABS_TAC)) THEN
   CONV_TAC INT_RING in
  fun tm -> prove(tm,tac);;

let FINITE_FRAG_SUPPORT = prove
 (`!x:A frag. FINITE(frag_support (x:A frag))`,
  REWRITE_TAC[frag_support; frag_tybij; ETA_AX]);;

let FRAG_SUPPORT_0 = prove
 (`frag_support frag_0 = {}`,
  REWRITE_TAC[frag_support; DEST_FRAG_0; EMPTY_GSPEC]);;

let FRAG_SUPPORT_OF = prove
 (`!a:A. frag_support(frag_of a) = {a}`,
  REWRITE_TAC[frag_support; DEST_FRAG_OF] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[MESON[] `~(if p then F else T) <=> p`] THEN
  REWRITE_TAC[SING_GSPEC]);;

let FRAG_SUPPORT_NEG = prove
 (`!x:A frag. frag_support(frag_neg x) = frag_support x`,
  REWRITE_TAC[frag_support; DEST_FRAG_NEG; INT_NEG_EQ_0]);;

let FRAG_SUPPORT_CMUL = prove
 (`!a x:A frag. frag_support(frag_cmul a x) SUBSET frag_support x`,
  REWRITE_TAC[frag_support; DEST_FRAG_CMUL] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM; INT_MUL_RZERO] THEN
  REWRITE_TAC[frag_tybij; ETA_AX]);;

let FRAG_SUPPORT_ADD = prove
 (`!x y:A frag. frag_support(frag_add x y) SUBSET
                frag_support x UNION frag_support y`,
  REWRITE_TAC[frag_support; DEST_FRAG_ADD] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
  SIMP_TAC[GSYM DE_MORGAN_THM; CONTRAPOS_THM; INT_ADD_LID]);;

let FRAG_SUPPORT_SUB = prove
 (`!x y:A frag. frag_support(frag_sub x y) SUBSET
                frag_support x UNION frag_support y`,
  REWRITE_TAC[frag_support; DEST_FRAG_SUB] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
  SIMP_TAC[GSYM DE_MORGAN_THM; CONTRAPOS_THM; INT_SUB_RZERO]);;

let FRAG_SUPPORT_EQ_EMPTY = prove
 (`!c:A frag. frag_support c = {} <=> c = frag_0`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[MESON[frag_tybij] `c = d <=> dest_frag c = dest_frag d`] THEN
  REWRITE_TAC[DEST_FRAG_0; FUN_EQ_THM; frag_support; IN_ELIM_THM]);;

let FRAG_ADD_EQ_0 = prove
 (`!c1 c2:A frag.
        DISJOINT (frag_support c1) (frag_support c2) /\
        frag_add c1 c2 = frag_0
        ==> c1 = frag_0 /\ c2 = frag_0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frag_support; FRAG_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[DEST_FRAG_ADD; DEST_FRAG_0; FUN_EQ_THM; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC(INT_ARITH
   `~(~(x:int = &0) /\ ~(y = &0)) ==> x + y = &0 ==> x = &0 /\ y = &0`) THEN
  ASM SET_TAC[]);;

let NEUTRAL_FRAG_ADD = prove
 (`neutral frag_add :A frag = frag_0`,
  REWRITE_TAC[neutral; FRAG_MODULE
   `(frag_add x y = y <=> x = frag_0) /\
    (frag_add y x = y <=> x = frag_0)`]);;

let MONOIDAL_FRAG_ADD = prove
 (`monoidal frag_add`,
  REWRITE_TAC[monoidal; NEUTRAL_FRAG_ADD] THEN CONV_TAC FRAG_MODULE);;

let FRAG_CMUL_SUM = prove
 (`!f:B->A frag k a.
        frag_cmul a (iterate frag_add k f) =
        iterate frag_add k (\b. frag_cmul a (f b))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:int = &0` THEN
  ASM_SIMP_TAC[INT_MUL_LZERO; FRAG_MODULE `frag_cmul (&0) x = frag_0`;
   REWRITE_RULE[NEUTRAL_FRAG_ADD]
     (MATCH_MP ITERATE_EQ_NEUTRAL MONOIDAL_FRAG_ADD)] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  ASM_REWRITE_TAC[support; NEUTRAL_FRAG_ADD;
     FRAG_MODULE `frag_cmul a c = frag_0 <=> a = &0 \/ c = frag_0`] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[FRAG_MODULE `frag_cmul a frag_0 = frag_0`] THEN
  UNDISCH_TAC `FINITE {x | x IN k /\ ~((f:B->A frag) x = frag_0)}` THEN
  SPEC_TAC(`{x | x IN k /\ ~((f:B->A frag) x = frag_0)}`,`k:B->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
  REWRITE_TAC[NEUTRAL_FRAG_ADD; FRAG_MODULE `frag_cmul a frag_0 = frag_0`] THEN
  SIMP_TAC[FRAG_MODULE
   `frag_cmul a (frag_add x y) =
    frag_add (frag_cmul a x) (frag_cmul a y)`]);;

let FRAG_SUPPORT_SUM = prove
 (`!f:B->A frag k.
        frag_support(iterate frag_add k f) SUBSET
        UNIONS {frag_support(f i) | i IN k}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[NEUTRAL_FRAG_ADD] THEN COND_CASES_TAC THEN
  REWRITE_TAC[FRAG_SUPPORT_0; EMPTY_SUBSET] THEN
  TRANS_TAC SUBSET_TRANS
   `UNIONS {frag_support (f i) |i| i IN support frag_add (f:B->A frag) k}` THEN
  CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN
    SPEC_TAC(`support frag_add (f:B->A frag) k`,`k:B->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; NEUTRAL_FRAG_ADD] THEN
    REWRITE_TAC[FRAG_SUPPORT_0; EMPTY_SUBSET] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_ADD o lhand o snd) THEN
    ASM SET_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    SIMP_TAC[SUPPORT_SUBSET; IMAGE_SUBSET]]);;

let frag_extend = new_definition
 `frag_extend (f:A->B frag) x =
        iterate frag_add (frag_support x)
            (\a. frag_cmul (dest_frag x a) (f a))`;;

let FRAG_EXTEND = prove
 (`!f:A->B frag x.
        frag_extend f x =
        iterate frag_add UNIV (\a. frag_cmul (dest_frag x a) (f a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frag_extend] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_UNIV MONOIDAL_FRAG_ADD) THEN
  REWRITE_TAC[support; NEUTRAL_FRAG_ADD; frag_support; IN_UNIV] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE);;

let FRAG_EXTEND_0 = prove
 (`!f:A->B frag. frag_extend f frag_0 = frag_0`,
  REWRITE_TAC[frag_extend; FRAG_SUPPORT_0] THEN
  REWRITE_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
  REWRITE_TAC[NEUTRAL_FRAG_ADD]);;

let FRAG_EXTEND_OF = prove
 (`!f:A->B frag a. frag_extend f (frag_of a) = f a`,
  REWRITE_TAC[frag_extend; FRAG_SUPPORT_OF] THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD; FINITE_EMPTY] THEN
  REWRITE_TAC[NOT_IN_EMPTY; NEUTRAL_FRAG_ADD; DEST_FRAG_OF] THEN
  CONV_TAC FRAG_MODULE);;

let FRAG_EXTEND_CMUL = prove
 (`!f:A->B frag c x.
        frag_extend f (frag_cmul c x) = frag_cmul c (frag_extend f x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c:int = &0` THEN
  ASM_REWRITE_TAC[FRAG_MODULE `frag_cmul (&0) x = frag_0`; FRAG_EXTEND_0] THEN
  REWRITE_TAC[frag_extend; frag_support; DEST_FRAG_CMUL] THEN
  ASM_REWRITE_TAC[INT_ENTIRE; FRAG_CMUL_SUM; FRAG_MODULE
    `frag_cmul (a * b) c = frag_cmul a (frag_cmul b c)`]);;

let FRAG_EXTEND_NEG = prove
 (`!f:A->B frag x.
        frag_extend f (frag_neg x) = frag_neg(frag_extend f x)`,
  REWRITE_TAC[FRAG_MODULE `frag_neg x = frag_cmul (-- &1) x`] THEN
  REWRITE_TAC[FRAG_EXTEND_CMUL]);;

let FRAG_EXTEND_ADD = prove
 (`!f:A->B frag x y.
        frag_extend f (frag_add x y) =
        frag_add (frag_extend f x) (frag_extend f y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRAG_EXTEND] THEN
  W(MP_TAC o PART_MATCH (rand o rand)
      (MATCH_MP ITERATE_OP_GEN MONOIDAL_FRAG_ADD) o rand o snd) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[support; NEUTRAL_FRAG_ADD; IN_UNIV] THEN
    CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `frag_support (x:A frag)`;
      EXISTS_TAC `frag_support (y:A frag)`] THEN
    REWRITE_TAC[FINITE_FRAG_SUPPORT] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM; frag_support] THEN
    REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE;
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
    REWRITE_TAC[IN_UNIV] THEN CONV_TAC FRAG_MODULE]);;

let FRAG_EXTEND_SUB = prove
 (`!f:A->B frag x y.
        frag_extend f (frag_sub x y) =
        frag_sub (frag_extend f x) (frag_extend f y)`,
  REWRITE_TAC[FRAG_MODULE
   `frag_sub x y = frag_add x (frag_cmul (-- &1) y)`] THEN
  REWRITE_TAC[FRAG_EXTEND_CMUL; FRAG_EXTEND_ADD]);;

let FRAG_EXTEND_SUM = prove
 (`!f:A->B frag g k:C->bool.
        FINITE k
        ==> frag_extend f (iterate frag_add k g) =
            iterate frag_add k (frag_extend f o g)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
  SIMP_TAC[NEUTRAL_FRAG_ADD; FRAG_EXTEND_0; FRAG_EXTEND_ADD; o_THM]);;

let FRAG_EXTEND_EQ = prove
 (`!(g:A->B frag) h c.
        (!f. f IN frag_support c ==> g f = h f)
        ==> frag_extend g c = frag_extend h c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frag_extend] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
  ASM_SIMP_TAC[]);;

let FRAG_EXTEND_EQ_0 = prove
 (`!(f:A->B frag) c.
        (!a. a IN frag_support c ==> f a = frag_0)
        ==> frag_extend f c = frag_0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frag_extend] THEN
  REWRITE_TAC[GSYM NEUTRAL_FRAG_ADD] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ_NEUTRAL MONOIDAL_FRAG_ADD) THEN
  ASM_SIMP_TAC[NEUTRAL_FRAG_ADD] THEN REPEAT STRIP_TAC THEN
  CONV_TAC FRAG_MODULE);;

let FRAG_SUPPORT_FRAG_EXTEND = prove
 (`!f:A->B frag c.
        frag_support(frag_extend f c) SUBSET
        UNIONS {frag_support(f a) | a IN frag_support c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frag_extend] THEN
  W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_SUM o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC UNIONS_MONO_IMAGE THEN
  REWRITE_TAC[FRAG_SUPPORT_CMUL]);;

let FRAG_EXPANSION = prove
 (`!x:A frag. x = frag_extend frag_of x`,
  GEN_TAC THEN REWRITE_TAC[frag_extend] THEN MATCH_MP_TAC(MESON[frag_tybij]
   `dest_frag x = dest_frag y ==> x = y`) THEN
  REWRITE_TAC[o_THM; FUN_EQ_THM; I_THM] THEN X_GEN_TAC `b:A` THEN
  SUBGOAL_THEN
   `!k. FINITE k
        ==> dest_frag(iterate frag_add k
                        (\a:A. frag_cmul (dest_frag x a) (frag_of a))) b =
            if b IN k then dest_frag x b else &0`
   (fun th -> SIMP_TAC[th; FINITE_FRAG_SUPPORT])
  THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
    REWRITE_TAC[NOT_IN_EMPTY; NEUTRAL_FRAG_ADD; DEST_FRAG_0] THEN
    SIMP_TAC[DEST_FRAG_ADD; DEST_FRAG_CMUL; DEST_FRAG_OF] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
    ASM_CASES_TAC `b:A = a` THEN ASM_SIMP_TAC[IN_INSERT] THEN INT_ARITH_TAC;
    REWRITE_TAC[frag_support; IN_ELIM_THM] THEN MESON_TAC[]]);;

let FRAG_CLOSURE_SUB_CMUL = prove
 (`!P:A frag->bool.
        P frag_0 /\
        (!c1 c2. P c1 /\ P c2 ==> P(frag_sub c1 c2))
        ==> !a c. P c ==> P(frag_cmul a c)`,
  GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. (P:(A frag)->bool) (frag_cmul (&n) c)` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC; FRAG_MODULE
    `frag_cmul (a + &1) x = frag_sub (frag_cmul a x) (frag_sub frag_0 x)`] THEN
    ASM_SIMP_TAC[DEST_FRAG_0; FRAG_MODULE `frag_cmul (&0) x = frag_0`];
    ALL_TAC] THEN
  X_GEN_TAC `a:int` THEN
  DISJ_CASES_TAC(INT_ARITH `&0:int <= a \/ &0 <= --a`) THENL
   [UNDISCH_TAC `&0:int <= a` THEN SPEC_TAC(`a:int`,`a:int`);
    ONCE_REWRITE_TAC[FRAG_MODULE
     `frag_cmul a x = frag_sub frag_0 (frag_cmul (--a) x)`] THEN
    ASM_SIMP_TAC[DEST_FRAG_CMUL; DEST_FRAG_0; FRAG_MODULE
     `frag_sub x y = frag_sub x z <=> y = z`] THEN
    UNDISCH_TAC `&0:int <= --a` THEN SPEC_TAC(`--a:int`,`a:int`)] THEN
  ASM_SIMP_TAC[GSYM INT_FORALL_POS]);;

let FRAG_INDUCTION = prove
 (`!P:A frag->bool s.
        P frag_0 /\
        (!a. a IN s ==> P(frag_of a)) /\
        (!c1 c2. P c1 /\ P c2 ==> P(frag_sub c1 c2))
        ==> !c. frag_support c SUBSET s ==> P c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `P:A frag->bool` FRAG_CLOSURE_SUB_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o RAND_CONV) [FRAG_EXPANSION] THEN
  REWRITE_TAC[frag_extend; o_THM] THEN X_GEN_TAC `c:A frag` THEN
  MP_TAC(ISPEC `c:A frag` FINITE_FRAG_SUPPORT) THEN
  SPEC_TAC(`frag_support(c:A frag)`,`k:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
  ASM_REWRITE_TAC[NEUTRAL_FRAG_ADD; INSERT_SUBSET] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FRAG_MODULE
   `frag_add x y = frag_sub x (frag_sub frag_0 y)`] THEN
  REPEAT(FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

let FRAG_EXTEND_COMPOSE = prove
 (`!(f:B->C frag) (g:A->B) c.
        frag_extend f (frag_extend (frag_of o g) c) = frag_extend (f o g) c`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC(MESON[SUBSET_UNIV]
   `(!c. frag_support c SUBSET UNIV ==> P c) ==> (!c. P c)`) THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  SIMP_TAC[FRAG_EXTEND_0; FRAG_EXTEND_SUB; FRAG_EXTEND_OF; o_THM]);;

let FRAG_SPLIT = prove
 (`!c s t:A->bool.
        frag_support c SUBSET s UNION t
        ==> ?d e. frag_support d SUBSET s /\ frag_support e SUBSET t /\
                  frag_add d e = c`,
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`frag_extend (\f. if f IN s then frag_of f else frag_0) c:A frag`;
    `frag_extend (\f. if f IN s then frag_0 else frag_of f) c:A frag`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THEN
    W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_FRAG_EXTEND o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[FRAG_SUPPORT_0; EMPTY_SUBSET; FRAG_SUPPORT_OF] THEN
    ASM SET_TAC[];
    POP_ASSUM MP_TAC THEN SPEC_TAC(`c:A frag`,`c:A frag`) THEN
    MATCH_MP_TAC FRAG_INDUCTION THEN
    REWRITE_TAC[FRAG_EXTEND_0; FRAG_EXTEND_SUB; FRAG_EXTEND_OF] THEN
    CONJ_TAC THENL [CONV_TAC FRAG_MODULE; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC FRAG_MODULE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC FRAG_MODULE]);;
