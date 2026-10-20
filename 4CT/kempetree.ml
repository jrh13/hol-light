(* ========================================================================= *)
(* 4CT/kempetree.ml                                                          *)
(*                                                                           *)
(* kempetree.v: the Kempe closure tree (the KempeTreeClosure section through *)
(* Kempe_tree_closure_correct, Kempe_validP and Kempe_completeP).            *)
(* ctree_size counts the colourings stored in a ctree; kempe_tree_closure h  *)
(* d ctu ctr gtu runs d rounds of the double restriction step ktc_step       *)
(* (restrict the colouring tree by the deleted chromograms, then close up    *)
(* under rotation what that removed) on top of the simple restriction of gtu *)
(* by ctr.  kempe_valid is the loop invariant and kempe_complete the         *)
(* progress predicate; KEMPE_TREE_CLOSURE_CORRECT says that the closure      *)
(* keeps the invariant and improves completeness by 3^d, KEMPE_VALIDP that   *)
(* an even trace missing from a valid ctu is in the Kempe co-closure, and    *)
(* KEMPE_COMPLETEP that in a complete state this is an equivalence.          *)
(* ctrace_a et = APPEND et [sumt et] is Gonthier's completed trace (sum at   *)
(* the end, matching cgram and matchpg), as opposed to color.ml's cyclic     *)
(* ctrace with the sum in front.                                             *)
(* ========================================================================= *)

needs "4CT/gtreerestrict.ml";;
needs "4CT/ctreerestrict.ml";;
needs "4CT/initgtree.ml";;

(* ------------------------------------------------------------------------- *)
(* ctree_size t: the number of distinct colourings stored in t.              *)
(* ------------------------------------------------------------------------- *)

let ctree_size = define
 `(ctree_size (CtreeNode t1 t2 t3) =
  ctree_size t1 + (ctree_size t2 + ctree_size t3)) /\
  (ctree_size (CtreeLeaf lf) = 1) /\
  (ctree_size CtreeEmpty = 0)`;;

let CTREE_SIZE_NOMEM = prove
 (`!t. (!et. ~(ctree_mem t et)) ==> ctree_size t = 0`,
  MATCH_MP_TAC ctree_INDUCT THEN
  REWRITE_TAC[ctree_size; CTREE_MEM_LEAF; CTREE_MEM_EMPTY] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[ADD_EQ_0] THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `et:color list` THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `CONS Color1 et` th) THEN
      MP_TAC(SPEC `CONS Color2 et` th) THEN
      MP_TAC(SPEC `CONS Color3 et` th)) THEN
    REWRITE_TAC[CTREE_MEM_NODE_CONS] THEN MESON_TAC[];
    GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `[]:color list`) THEN REWRITE_TAC[]]);;

let CTREE_SIZE_NOCONS = prove
 (`!t. (!c et. ~(ctree_mem t (CONS c et)))
       ==> ctree_size t = (if ctree_mem t [] then 1 else 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t:ctree` (cases "ctree")) THEN
  REWRITE_TAC[ctree_size; CTREE_MEM_LEAF; CTREE_MEM_EMPTY;
              CTREE_MEM_NODE_NIL] THEN
  DISCH_TAC THEN REWRITE_TAC[ADD_EQ_0] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC CTREE_SIZE_NOMEM THEN X_GEN_TAC `et:color list` THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`Color1`; `et:color list`] th) THEN
    MP_TAC(SPECL [`Color2`; `et:color list`] th) THEN
    MP_TAC(SPECL [`Color3`; `et:color list`] th)) THEN
  REWRITE_TAC[CTREE_MEM_NODE_CONS] THEN MESON_TAC[]);;

let CTREE_SIZE_SEL = prove
 (`!t. ctree_size t =
       (if ctree_leaf t then 1
        else ctree_size (ctree_sel t Color1) +
             ctree_size (ctree_sel t Color2) +
             ctree_size (ctree_sel t Color3))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t:ctree` (cases "ctree")) THEN
  REWRITE_TAC[ctree_size; ctree_leaf; ctree_sel; palette; ADD_CLAUSES]);;

let CTREE_SIZE_PARTITION = prove
 (`!t t' t''. ctree_partition t (CtreePair t' t'')
              ==> ctree_size t = ctree_size t' + ctree_size t''`,
  REWRITE_TAC[ctree_partition; sctree_partition] THEN
  MATCH_MP_TAC ctree_INDUCT THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t1:ctree`; `t2:ctree`; `t3:ctree`] THEN
    STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`t':ctree`; `t'':ctree`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `[]:color list`) THEN
    REWRITE_TAC[CTREE_MEM_NODE_NIL; CTREE_MEM_SEQ0; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[CTREE_SIZE_SEL] THEN
    ASM_REWRITE_TAC[ctree_leaf; ctree_sel; palette] THEN
    SUBGOAL_THEN
     `ctree_size t1 =
      ctree_size (ctree_sel t' Color1) + ctree_size (ctree_sel t'' Color1) /\
      ctree_size t2 =
      ctree_size (ctree_sel t' Color2) + ctree_size (ctree_sel t'' Color2) /\
      ctree_size t3 =
      ctree_size (ctree_sel t' Color3) + ctree_size (ctree_sel t'' Color3)`
     (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `et:color list` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `CONS Color1 et`);
      FIRST_X_ASSUM(MP_TAC o SPEC `CONS Color2 et`);
      FIRST_X_ASSUM(MP_TAC o SPEC `CONS Color3 et`)] THEN
    REWRITE_TAC[CTREE_MEM_SEL; ctree_sel; palette];
    GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `ctree_size t' = (if ctree_mem t' [] then 1 else 0) /\
      ctree_size t'' = (if ctree_mem t'' [] then 1 else 0)`
     (fun th -> REWRITE_TAC[th; ctree_size]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC CTREE_SIZE_NOCONS THEN REPEAT GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `CONS (c:color) et`) THEN
      REWRITE_TAC[CTREE_MEM_LEAF; NOT_CONS_NIL] THEN CONV_TAC TAUT;
      FIRST_X_ASSUM(MP_TAC o SPEC `[]:color list`) THEN
      REWRITE_TAC[CTREE_MEM_LEAF] THEN
      MAP_EVERY ASM_CASES_TAC [`ctree_mem t' []`; `ctree_mem t'' []`] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    REPEAT GEN_TAC THEN REWRITE_TAC[CTREE_MEM_EMPTY; ctree_size] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ctree_size t' = 0 /\ ctree_size t'' = 0`
     (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
    CONJ_TAC THEN MATCH_MP_TAC CTREE_SIZE_NOMEM THEN ASM_MESON_TAC[]]);;

let CTREE_SIZE_PROPER = prove
 (`!h t. ctree_proper h t /\ ctree_size t = 0 ==> t = CtreeEmpty`,
  INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:ctree` (cases "ctree")) THEN
  REWRITE_TAC[ctree_proper; ctree_size; NOT_SUC; distinctness "ctree";
              ADD_EQ_0; ARITH; SUC_SUB1; ctree_empty_node] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_SIMP_TAC[ctree_empty]);;

let CTREE_MAX_SIZE_PROPER = prove
 (`!h t. ctree_proper h t ==> ctree_size t <= 3 EXP h`,
  INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:ctree` (cases "ctree")) THEN
  REWRITE_TAC[ctree_proper; ctree_size; NOT_SUC; EXP; ARITH; LE_REFL; LE_0;
              SUC_SUB1] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a <= e /\ b <= e /\ c <= e ==> a + b + c <= 3 * e`)
  THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Trace normalisation (Gonthier color.v): the even normal form etrace, its  *)
(* interaction with the Eperm132 flip, and composition of permutations.      *)
(* ------------------------------------------------------------------------- *)

let EVEN_TAIL_PERMT132 = prove
 (`!tl. ~(even_tail tl) ==> even_tail (permt Eperm132 tl)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[permt; even_tail] THEN
  STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
  ASM_REWRITE_TAC[permc_DEF; distinctness "color"; even_tail]);;

let EVEN_ETAIL = prove
 (`!et. even_tail (etail et)`,
  GEN_TAC THEN REWRITE_TAC[etail; etrace_perm; even_trace] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[PERMT_ID; EVEN_TAIL_PERMT132]);;

let PERMT_PERMT_CONG = prove
 (`!p1 q1 p2 q2.
      (!c. permc p1 (permc q1 c) = permc p2 (permc q2 c))
      ==> !l. permt p1 (permt q1 l) = permt p2 (permt q2 l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[permt]);;

let TTAIL_PERMT132 = prove
 (`!et. ttail (permt Eperm132 et) = permt Eperm132 (ttail et)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ttail; proper_trace; permt; NOT_CONS_NIL; HD; TL; PERMC_EQ_0;
              permc_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[permt; permc_DEF] THEN
  SPEC_TAC(`t:color list`,`l:color list`) THEN
  MATCH_MP_TAC PERMT_PERMT_CONG THEN
  STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
  MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[edge_rot_DEF; permc_DEF]);;

let TTAIL_ETRACE = prove
 (`!et. ttail (etrace et) = etail et`,
  GEN_TAC THEN REWRITE_TAC[etrace; etail; etrace_perm] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PERMT_ID; TTAIL_PERMT132]);;

let EVEN_ETRACE = prove
 (`!et. even_trace (etrace et)`,
  REWRITE_TAC[even_trace; TTAIL_ETRACE; EVEN_ETAIL]);;

let EVEN_TRACE_OR_FLIP = prove
 (`!et. even_trace et \/ even_trace (permt Eperm132 et)`,
  REWRITE_TAC[even_trace; TTAIL_PERMT132] THEN
  MESON_TAC[EVEN_TAIL_PERMT132]);;

let ETRACE_LENGTH = prove
 (`!et. LENGTH (etrace et) = LENGTH et`,
  REWRITE_TAC[etrace; LENGTH_PERMT]);;

let COMPOSE_PERMT = prove
 (`!g g'. ?h. !l. permt g (permt g' l) = permt h l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `\c. permc g (permc g' c)` COLOR_INJ_PERMC) THEN
  REWRITE_TAC[PERMC_0] THEN ANTS_TAC THENL
   [MESON_TAC[PERMC_INJ];
    DISCH_THEN(X_CHOOSE_TAC `h:edge_perm`) THEN EXISTS_TAC `h:edge_perm` THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[permt]]);;

let PERMT_EPERM132_INVOL = prove
 (`!et. permt Eperm132 (permt Eperm132 et) = et`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[permt] THEN
  STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
  REWRITE_TAC[permc_DEF]);;

let PERMT_ETRACE_PERM = prove
 (`!et. permt (etrace_perm et) (etrace et) = et`,
  GEN_TAC THEN REWRITE_TAC[etrace; etrace_perm] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PERMT_ID; PERMT_EPERM132_INVOL]);;

(* Every permutation acts on traces as some edge_rot e, up to the flip.      *)

let PERMT_EDGE_ROT_NORM = prove
 (`!g:edge_perm. ?e. (!X. permt (edge_rot e) X = permt g X) \/
                     (!X. permt (edge_rot e) X = permt Eperm132 (permt g X))`,
  MATCH_MP_TAC edge_perm_INDUCT THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `Color1`; EXISTS_TAC `Color1`; EXISTS_TAC `Color2`;
    EXISTS_TAC `Color3`; EXISTS_TAC `Color2`; EXISTS_TAC `Color3`] THEN
  REWRITE_TAC[edge_rot_DEF] THEN
  ((DISJ1_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[permt] THEN
    STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
    REWRITE_TAC[permc_DEF] THEN NO_TAC) ORELSE
   (DISJ2_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[permt] THEN
    STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
    REWRITE_TAC[permc_DEF] THEN NO_TAC)));;

(* ------------------------------------------------------------------------- *)
(* ctrace_a: the completed trace with the sum at the end (Gonthier ctrace).  *)
(* ------------------------------------------------------------------------- *)

let ctrace_a = new_definition
 `ctrace_a (et:color list) = APPEND et [sumt et]`;;

let SUMT_CTRACE_A = prove
 (`!et. sumt (ctrace_a et) = Color0`,
  REWRITE_TAC[ctrace_a; SUMT_APPEND; sumt; ADDC_0_RIGHT; ADDCC]);;

let LENGTH_CTRACE_A = prove
 (`!et. LENGTH (ctrace_a et) = LENGTH et + 1`,
  REWRITE_TAC[ctrace_a; LENGTH_APPEND; LENGTH; ARITH]);;

let CTRACE_A_PERMT = prove
 (`!g et. ctrace_a (permt g et) = permt g (ctrace_a et)`,
  REWRITE_TAC[ctrace_a; PERMT_APPEND; SUMT_PERMT; permt]);;

let MATCHG_CTRACE_A = prove
 (`!et w. gram_balanced 0 F (cgram 0 F w)
          ==> (matchg [] (ctrace_a et) (cgram 0 F w) <=>
               matchpg Bstack0 et w)`,
  REWRITE_TAC[ctrace_a; MATCHG_PG]);;

(* A chromogram matching a completed trace is balanced and closes its own    *)
(* front (Gonthier matchg_cgram); a balanced colour list is a completed      *)
(* trace.                                                                    *)

let MATCHG_CGRAM_A = prove
 (`!et w. matchg [] (ctrace_a et) w
          ==> gram_balanced 0 F w /\ w = cgram 0 F (BUTLAST w)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATCHG_BALANCED) THEN
  REWRITE_TAC[SUMT_CTRACE_A; cbit0; distinctness "color"] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MATCHG_SIZE) THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` (cases "list")) THEN
  REWRITE_TAC[LENGTH; LENGTH_CTRACE_A; ARITH_RULE `~(0 = n + 1)`] THEN
  DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BALANCED_CGRAM THEN ASM_REWRITE_TAC[]);;

let CTRACE_A_BUTLAST = prove
 (`!cet. ~(cet = []) /\ sumt cet = Color0 ==> cet = ctrace_a (BUTLAST cet)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ctrace_a] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
    [SYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  AP_TERM_TAC THEN REWRITE_TAC[CONS_11] THEN
  UNDISCH_TAC `sumt (cet:color list) = Color0` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
    [SYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[SUMT_APPEND; sumt; ADDC_0_RIGHT; ADDC_EQ_0] THEN
  MESON_TAC[]);;

let MATCHG_CGRAM_CTRACE_A = prove
 (`!w cet. gram_balanced 0 F (cgram 0 F w) /\ matchg [] cet (cgram 0 F w)
           ==> ?et. cet = ctrace_a et /\ matchpg Bstack0 et w`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `BUTLAST (cet:color list)` THEN
  SUBGOAL_THEN `ctrace_a (BUTLAST cet) = cet` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CTRACE_A_BUTLAST THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP MATCHG_SIZE) THEN
      REWRITE_TAC[LENGTH_CGRAM] THEN
      MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `~(n + 1 = 0)`];
      ASM_MESON_TAC[BALANCED_SUMT0]];
    MP_TAC(SPECL [`BUTLAST (cet:color list)`; `w:gram_symbol list`]
      MATCHG_CTRACE_A) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Chromogram counts: emptiness and invariance under the trace normal forms. *)
(* ------------------------------------------------------------------------- *)

let GTREE_SUB_NOMEM = prove
 (`!gt. (!w. ~(gtree_mem gt w)) ==> !bs et. gtree_sub gt bs et = 0`,
  REWRITE_TAC[GTREE_SUB_EQ_0] THEN MESON_TAC[]);;

let GTREE_SUB_FLIP = prove
 (`!gt et. gtree_sub gt Bstack0 (permt Eperm132 et) = 0 <=>
           gtree_sub gt Bstack0 et = 0`,
  REWRITE_TAC[GTREE_SUB_EQ_0; MATCHPG_FLIP]);;

let GTREE_SUB_ETRACE = prove
 (`!gt et. gtree_sub gt Bstack0 (etrace et) = 0 <=>
           gtree_sub gt Bstack0 et = 0`,
  REWRITE_TAC[GTREE_SUB_EQ_0; MATCHPG_ETRACE]);;

(* The restriction of gtu by a single ctree ctr: membership of both halves   *)
(* and the count split.                                                      *)

let GTREE_RESTRICT_SPLIT = prove
 (`!gtu ctr gtr1 gtu1.
     gtree_restrict gtu (GtrCons Bstack0 ctr GtrNil) = GtreePair gtr1 gtu1
     ==> (!w. gtree_mem gtr1 w <=>
              gtree_mem gtu w /\ has_match Bstack0 (ctree_mem ctr) w) /\
         (!w. gtree_mem gtu1 w <=>
              gtree_mem gtu w /\ ~(has_match Bstack0 (ctree_mem ctr) w)) /\
         (!et. gtree_sub gtu Bstack0 et =
               gtree_sub gtr1 Bstack0 et + gtree_sub gtu1 Bstack0 et)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`gtu:gtree`; `GtrCons Bstack0 ctr GtrNil`]
    GTREE_MEM0_RESTRICT) THEN
  MP_TAC(ISPECL [`gtu:gtree`; `GtrCons Bstack0 ctr GtrNil`]
    GTREE_RESTRICT_PARTITION) THEN
  ASM_REWRITE_TAC[gtree_pair_sub; gtree_pair_partition; gtr_mem] THEN
  DISCH_THEN(LABEL_TAC "Part") THEN DISCH_THEN(LABEL_TAC "Mr") THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:gram_symbol list` THEN
    USE_THEN "Part" (MP_TAC o SPEC `w:gram_symbol list` o
      REWRITE_RULE[sgtree_partition]) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC TAUT;
    GEN_TAC THEN REWRITE_TAC[gtree_sub] THEN
    MATCH_MP_TAC MATCH_COUNT_PARTITION THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Kempe co-closure argument shared by Kempe_validP and the validity     *)
(* half of the closure step: a trace of the right length matched by no       *)
(* chromogram of gtu is in the co-closure, provided every chromogram missing *)
(* from gtu is accounted for by a co-closed trace (the closedP clause of     *)
(* kempe_valid).  The co-closure is also inherited from permuted traces.     *)
(* ------------------------------------------------------------------------- *)

let KEMPE_COCLOSURE_PERMT = prove
 (`!P g et. kempe_coclosure P (permt g et) ==> kempe_coclosure P et`,
  REWRITE_TAC[kempe_coclosure] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[kempe_closed]);;

let KEMPE_COCLOSURE_UNMATCHED = prove
 (`!h P gtu et.
     (!w. ~(gtree_mem gtu w) /\ init_gtree_spec (SUC h) w
          ==> ?et. kempe_coclosure P (ctrace_a et) /\ matchpg Bstack0 et w) /\
     LENGTH et = SUC h /\ gtree_sub gtu Bstack0 et = 0
     ==> kempe_coclosure P (ctrace_a et)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "closedP") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[kempe_coclosure] THEN X_GEN_TAC `P1:color list->bool` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `ctrace_a et` o REWRITE_RULE[kempe_closed]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:gram_symbol list` STRIP_ASSUME_TAC o
             CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATCHG_CGRAM_A) THEN
  ABBREV_TAC `w1 = BUTLAST (w0:gram_symbol list)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `matchpg Bstack0 et w1` ASSUME_TAC THENL
   [ASM_MESON_TAC[MATCHG_CTRACE_A]; ALL_TAC] THEN
  SUBGOAL_THEN `init_gtree_spec (SUC h) w1 /\ ~(gtree_mem gtu w1)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[init_gtree_spec; MATCHPG_SIZE; GTREE_SUB_EQ_0]; ALL_TAC] THEN
  USE_THEN "closedP" (MP_TAC o SPEC `w1:gram_symbol list`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `et1:color list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `kempe_coclosure P (ctrace_a et1)` THEN
  REWRITE_TAC[kempe_coclosure] THEN
  DISCH_THEN(MP_TAC o SPEC `P1:color list->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[MATCHG_CTRACE_A]);;

(* ------------------------------------------------------------------------- *)
(* The closure functional (Gonthier ktc_step / Kempe_tree_closure) and the   *)
(* invariants.  h is the ring size minus 2 (Coq's section variable);         *)
(* ktc_step is flattened over the components (ctu, GtreePair gtr gtu) of its *)
(* state argument and ktc_stepp is the pair form.                            *)
(* ------------------------------------------------------------------------- *)

let ktc_step = define
 `ktc_step h ktc0 ctu gtr gtu =
    (if ctree_empty ctu then (ctu, GtreePair gtr gtu)
     else if gtree_empty gtr then (ctu, GtreePair gtr gtu)
     else if gtree_empty gtu then (CtreeEmpty, empty_gtree_pair)
     else
       ktc0 (ctree_pair_sub (ctree_restrict h ctu
                             (CtrCons Bstack0 gtr CtrNil)) F)
            (ctree_rotlr
        (ctree_pair_sub (ctree_restrict h ctu (CtrCons Bstack0 gtr CtrNil)) T))
            gtu)`;;

let ktc_stepp = new_definition
 `ktc_stepp h (ktc0:ctree->ctree->gtree->ctree#gtree_pair) kr =
    ktc_step h ktc0 (FST kr) (gtree_pair_sub (SND kr) F)
    (gtree_pair_sub (SND kr) T)`;;

let kempe_tree_closure_fn = new_recursive_definition num_RECURSION
 `(kempe_tree_closure_fn h 0 =
      (\ctu ctr gtu. (ctu, gtree_restrict gtu (GtrCons Bstack0 ctr GtrNil))))
      /\
  (kempe_tree_closure_fn h (SUC d) =
      (\ctu ctr gtu. ktc_stepp h (kempe_tree_closure_fn h d)
         (ktc_stepp h (kempe_tree_closure_fn h d)
            (kempe_tree_closure_fn h d ctu ctr gtu))))`;;

let kempe_tree_closure = new_definition
 `kempe_tree_closure h d ctu ctr gtu = kempe_tree_closure_fn h d ctu ctr gtu`;;

(* Kempe_valid: a valid intermediate state (ctu is the proper tree of the    *)
(* even traces matched by gtr or gtu with multiplicities; ctr and gtr hold   *)
(* co-closed material; the chromograms missing from gtu are accounted for).  *)

let kempe_valid = new_definition
 `kempe_valid h P ctu ctr gtr gtu <=>
    (ctree_proper (SUC h) ctu /\
     (!et. ctree_sub ctu et =
           (if ~(even_trace et) then 0
            else gtree_sub gtr Bstack0 et + gtree_sub gtu Bstack0 et))) /\
    (!et. ctree_mem ctr et
          ==> kempe_coclosure P (ctrace_a et) /\ LENGTH et = SUC h) /\
    (!w. gtree_mem gtr w ==> ~(gtree_mem gtu w) /\ init_gtree_spec (SUC h) w)
    /\
    (!w. gtree_mem gtu w ==> init_gtree_spec (SUC h) w) /\
    (!w. ~(gtree_mem gtu w) /\ init_gtree_spec (SUC h) w
         ==> ?et. kempe_coclosure P (ctrace_a et) /\ matchpg Bstack0 et w)`;;

(* Kempe_complete: a complete state up to size sz.                           *)

let kempe_complete = new_definition
 `kempe_complete P sz ctu ctr gtr gtu <=>
    ((ctree_size ctu < sz \/ (ctr = CtreeEmpty /\ (!w. ~(gtree_mem gtr w)))) /\
     (!et. (P (ctrace_a et) \/ (?e. ~(ctree_mem ctu (permt (edge_rot e)
                                                     (etrace et)))))
           ==> ctree_mem ctr (etrace et) \/ gtree_sub gtu Bstack0 et = 0))`;;

(* The invariants on a state pair kr = (ctu, GtreePair gtr gtu) (Gonthier's  *)
(* ktr_prop), and the correctness of an approximation of the closure at      *)
(* depth d (the statement of Kempe_tree_closure_correct for `ktc0`).         *)

let ktr_valid = new_definition
 `ktr_valid h P kr <=>
    kempe_valid h P (FST kr) CtreeEmpty (gtree_pair_sub (SND kr) F)
                    (gtree_pair_sub (SND kr) T)`;;

let ktr_complete = new_definition
 `ktr_complete P sz kr <=>
    kempe_complete P sz (FST kr) CtreeEmpty (gtree_pair_sub (SND kr) F)
                        (gtree_pair_sub (SND kr) T)`;;

let ktc_correct = new_definition
 `ktc_correct h P d ktc0 <=>
    !ctu ctr gtu.
       kempe_valid h P ctu ctr GtreeEmpty gtu
       ==> ktr_valid h P (ktc0 ctu ctr gtu) /\
           (!sz. kempe_complete P (3 EXP d + sz) ctu ctr GtreeEmpty gtu
                 ==> ktr_complete P (SUC sz) (ktc0 ctu ctr gtu))`;;

(* ------------------------------------------------------------------------- *)
(* Kempe_validP: an even trace of the right length missing from ctu is in    *)
(* the Kempe co-closure of P.                                                *)
(* ------------------------------------------------------------------------- *)

let KEMPE_VALIDP = prove
 (`!h P ctu ctr gtr gtu.
     kempe_valid h P ctu ctr gtr gtu
     ==> !et. LENGTH et = SUC h /\ ~(ctree_mem ctu (etrace et))
              ==> kempe_coclosure P (ctrace_a et)`,
  REWRITE_TAC[kempe_valid] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC KEMPE_COCLOSURE_PERMT THEN EXISTS_TAC `etrace_perm et` THEN
  REWRITE_TAC[GSYM CTRACE_A_PERMT; GSYM etrace] THEN
  MATCH_MP_TAC KEMPE_COCLOSURE_UNMATCHED THEN
  MAP_EVERY EXISTS_TAC [`h:num`; `gtu:gtree`] THEN
  ASM_REWRITE_TAC[ETRACE_LENGTH] THEN
  UNDISCH_TAC `~ctree_mem ctu (etrace et)` THEN
  ASM_REWRITE_TAC[ctree_mem; EVEN_ETRACE; ADD_EQ_0] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Kempe_completeP.  In a complete state with gtr empty, ctu holds exactly   *)
(* the even traces counted by gtu, and the set of completed traces whose     *)
(* normal form is in ctu is Kempe-closed (Gonthier's tr_ctu).                *)
(* ------------------------------------------------------------------------- *)

let CTU_MEM_EVEN = prove
 (`!ctu gtu.
     (!et. ctree_sub ctu et =
           (if ~(even_trace et) then 0 else gtree_sub gtu Bstack0 et))
     ==> !et. ctree_mem ctu et <=>
              even_trace et /\ ~(gtree_sub gtu Bstack0 et = 0)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ctree_mem] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let CTU_MEM_ETRACE = prove
 (`!ctu gtu.
     (!et. ctree_sub ctu et =
           (if ~(even_trace et) then 0 else gtree_sub gtu Bstack0 et))
     ==> !et. ctree_mem ctu (etrace et) <=>
              ctree_mem ctu et \/ ctree_mem ctu (permt Eperm132 et)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CTU_MEM_EVEN th]) THEN
  REWRITE_TAC[EVEN_ETRACE; GTREE_SUB_ETRACE; GTREE_SUB_FLIP] THEN
  MP_TAC(SPEC `et:color list` EVEN_TRACE_OR_FLIP) THEN CONV_TAC TAUT);;

let TR_CTU_KEMPE_CLOSED = prove
 (`!h P ctu gtu.
     (!et. ctree_sub ctu et =
           (if ~(even_trace et) then 0 else gtree_sub gtu Bstack0 et)) /\
     (!w. gtree_mem gtu w ==> init_gtree_spec (SUC h) w) /\
     (!et. P (ctrace_a et) \/
           (?e. ~(ctree_mem ctu (permt (edge_rot e) (etrace et))))
           ==> gtree_sub gtu Bstack0 et = 0)
     ==> kempe_closed
           (\cet. ?et. cet = ctrace_a et /\ ctree_mem ctu (etrace et))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let mem = MATCH_MP CTU_MEM_EVEN (CONJUNCT1 th)
    and meme = MATCH_MP CTU_MEM_ETRACE (CONJUNCT1 th) in
    MP_TAC(CONJUNCT2 th) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Dgtu") (LABEL_TAC "Cmpl")) THEN
    REWRITE_TAC[kempe_closed] THEN X_GEN_TAC `cet:color list` THEN
    DISCH_THEN(X_CHOOSE_THEN `et:color list`
      (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `g:edge_perm` THEN EXISTS_TAC `permt g et` THEN
      REWRITE_TAC[CTRACE_A_PERMT; meme] THEN
      MP_TAC(SPECL [`g:edge_perm`; `etrace_perm et`] COMPOSE_PERMT) THEN
      DISCH_THEN(X_CHOOSE_THEN `g2:edge_perm` (MP_TAC o SPEC `etrace et`)) THEN
      REWRITE_TAC[PERMT_ETRACE_PERM] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPEC `g2:edge_perm` PERMT_EDGE_ROT_NORM) THEN
      DISCH_THEN(X_CHOOSE_THEN `e:color` MP_TAC) THEN
      SUBGOAL_THEN `ctree_mem ctu (permt (edge_rot e) (etrace et))` MP_TAC
      THENL
       [UNDISCH_TAC `ctree_mem ctu (etrace et)` THEN
        GEN_REWRITE_TAC LAND_CONV [mem] THEN
        REWRITE_TAC[EVEN_ETRACE; GTREE_SUB_ETRACE] THEN
        ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
        DISCH_TAC THEN USE_THEN "Cmpl" MATCH_MP_TAC THEN DISJ2_TAC THEN
        EXISTS_TAC `e:color` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(fun th6 -> DISCH_THEN(DISJ_CASES_THEN(fun th ->
          REWRITE_TAC[GSYM th; th6])))];
      UNDISCH_TAC `ctree_mem ctu (etrace et)` THEN
      GEN_REWRITE_TAC LAND_CONV [mem] THEN
      REWRITE_TAC[EVEN_ETRACE; GTREE_SUB_EQ_0; NOT_FORALL_THM; NOT_IMP] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:gram_symbol list` STRIP_ASSUME_TAC) THEN
      USE_THEN "Dgtu" (fun th ->
        MP_TAC(MATCH_MP th (ASSUME `gtree_mem gtu w`))) THEN
      REWRITE_TAC[init_gtree_spec] THEN STRIP_TAC THEN
      EXISTS_TAC `cgram 0 F w` THEN
      MP_TAC(SPECL [`et:color list`; `w:gram_symbol list`]
        MATCHG_CTRACE_A) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MATCHPG_ETRACE]; ALL_TAC] THEN
      X_GEN_TAC `cet1:color list` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`w:gram_symbol list`; `cet1:color list`]
        MATCHG_CGRAM_CTRACE_A) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `et1:color list` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[mem; EVEN_ETRACE; GTREE_SUB_EQ_0; NOT_FORALL_THM;
                      NOT_IMP] THEN
      EXISTS_TAC `w:gram_symbol list` THEN ASM_REWRITE_TAC[MATCHPG_ETRACE]]));;

let KEMPE_COMPLETEP = prove
 (`!h P ctu ctr gtr gtu.
     kempe_valid h P ctu ctr gtr gtu /\ kempe_complete P 1 ctu ctr gtr gtu
     ==> !et. LENGTH et = SUC h
              ==> (kempe_coclosure P (ctrace_a et) <=>
                   ~(ctree_mem ctu (etrace et)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `et0:color list` THEN
  DISCH_TAC THEN EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[KEMPE_VALIDP]] THEN
  UNDISCH_TAC `kempe_complete P 1 ctu ctr gtr gtu` THEN
  UNDISCH_TAC `kempe_valid h P ctu ctr gtr gtu` THEN
  REWRITE_TAC[kempe_valid; kempe_complete; ARITH_RULE `n < 1 <=> n = 0`] THEN
  STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THENL
   [ASM_MESON_TAC[CTREE_SIZE_PROPER; CTREE_MEM_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE
    [CTREE_MEM_EMPTY; MATCH_MP GTREE_SUB_NOMEM th; ADD_CLAUSES])) THEN
  REWRITE_TAC[kempe_coclosure] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\cet. ?et. cet = ctrace_a et /\ ctree_mem ctu (etrace et)`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`h:num`; `P:color list->bool`; `ctu:ctree`; `gtu:gtree`]
        TR_CTU_KEMPE_CLOSED) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `et0:color list` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `cet:color list` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `et1:color list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
                                                       ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP CTU_MEM_EVEN th)) THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `ctree_mem ctu (etrace et1)` THEN
                         REWRITE_TAC[th; EVEN_ETRACE; GTREE_SUB_ETRACE]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Kempe_tree_closure_correct.  Base case: restricting gtu by ctr.           *)
(* ------------------------------------------------------------------------- *)

let KTC_BASE = prove
 (`!h P. ktc_correct h P 0
           (\ctu ctr gtu.
              (ctu, gtree_restrict gtu (GtrCons Bstack0 ctr GtrNil)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ktc_correct; ktr_valid; ktr_complete; EXP] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `gtree_restrict gtu (GtrCons Bstack0 ctr GtrNil)`
    (cases "gtree_pair")) THEN
  DISCH_THEN(X_CHOOSE_THEN `gtr1:gtree` (X_CHOOSE_THEN `gtu1:gtree`
   (fun th -> REWRITE_TAC[th; FST; SND; gtree_pair_sub] THEN
              MP_TAC(MATCH_MP GTREE_RESTRICT_SPLIT th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Mr")
    (CONJUNCTS_THEN2 (LABEL_TAC "Mu") (LABEL_TAC "Sub"))) THEN
  REWRITE_TAC[kempe_valid; kempe_complete; GTREE_SUB_EMPTY; GTREE_MEM_EMPTY;
              CTREE_MEM_EMPTY; ADD_CLAUSES] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[];
      X_GEN_TAC `w:gram_symbol list` THEN STRIP_TAC THEN
      ASM_CASES_TAC `gtree_mem gtu w` THENL
       [SUBGOAL_THEN `has_match Bstack0 (ctree_mem ctr) w` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[HAS_MATCHP] THEN MATCH_MP_TAC MONO_EXISTS THEN
        GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    X_GEN_TAC `sz:num` THEN REWRITE_TAC[ARITH_RULE `1 + sz = SUC sz`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Sz") (LABEL_TAC "Cmpl")) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[] THEN
      USE_THEN "Sz" (DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
                                      SUBST_ALL_TAC) THEN
      DISJ2_TAC THEN ASM_REWRITE_TAC[HAS_MATCHP; CTREE_MEM_EMPTY];
      X_GEN_TAC `et:color list` THEN DISCH_TAC THEN
      USE_THEN "Cmpl" (MP_TAC o SPEC `et:color list`) THEN ANTS_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      STRIP_TAC THENL
       [REWRITE_TAC[GTREE_SUB_EQ_0] THEN X_GEN_TAC `w:gram_symbol list` THEN
        ASM_REWRITE_TAC[HAS_MATCHP] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
        EXISTS_TAC `etrace et` THEN ASM_REWRITE_TAC[MATCHPG_ETRACE];
        USE_THEN "Sub" (MP_TAC o SPEC `et:color list`) THEN
        UNDISCH_TAC `gtree_sub gtu Bstack0 et = 0` THEN ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* The restriction step: ctu is split by the deleted chromograms gtr into    *)
(* ctu' (the traces still matched by gtu) and ctrr (the traces matched only  *)
(* by gtr), and the rotation closure of ctrr is the new ctr.                 *)
(* ------------------------------------------------------------------------- *)

let CTREE_ROTLR_EMPTY = prove
 (`ctree_rotlr CtreeEmpty = CtreeEmpty`,
  REWRITE_TAC[ctree_rotlr; ctree_union_rotlr; ctree_rotl; ctree_rotr;
              ctree_union]);;

let KTC_RESTRICT_FACTS = prove
 (`!h ctu ctu' ctrr gtr gtu.
     ctree_proper (SUC h) ctu /\
     (!et. ctree_sub ctu et =
           (if ~(even_trace et) then 0
            else gtree_sub gtr Bstack0 et + gtree_sub gtu Bstack0 et)) /\
     ctree_restrict h ctu (CtrCons Bstack0 gtr CtrNil) = CtreePair ctu' ctrr
     ==> ctree_proper (SUC h) ctu' /\ ctree_proper (SUC h) ctrr /\
         (!et. ctree_sub ctu' et =
               (if ~(even_trace et) then 0 else gtree_sub gtu Bstack0 et)) /\
         (!et. ctree_mem ctrr et <=>
               even_trace et /\ gtree_sub gtu Bstack0 et = 0 /\
               ~(gtree_sub gtr Bstack0 et = 0)) /\
         ctree_size ctu = ctree_size ctu' + ctree_size ctrr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `CtrCons Bstack0 gtr CtrNil` o
              MATCH_MP CTREE_RESTRICT_CORRECT) THEN
  ASM_REWRITE_TAC[ctree_pair_sub; ctr_sub; ADD_CLAUSES; FORALL_BOOL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Part") (LABEL_TAC "Dsub"))) THEN
  SUBGOAL_THEN
   `!et. ctree_sub ctu' et =
         (if ~(even_trace et) then 0 else gtree_sub gtu Bstack0 et)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[SUB_0; ADD_SUB2];
    ALL_TAC] THEN
  REMOVE_THEN "Dsub" (K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `et:color list` THEN
    SUBGOAL_THEN
     `(ctree_mem ctu et <=>
       even_trace et /\
       ~(gtree_sub gtr Bstack0 et + gtree_sub gtu Bstack0 et = 0)) /\
      (ctree_mem ctu' et <=>
       even_trace et /\ ~(gtree_sub gtu Bstack0 et = 0))`
     (fun th -> USE_THEN "Part" (MP_TAC o SPEC `et:color list` o
                  REWRITE_RULE[ctree_partition; sctree_partition]) THEN
                REWRITE_TAC[th; ADD_EQ_0] THEN CONV_TAC TAUT) THEN
    ASM_REWRITE_TAC[ctree_mem] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CTREE_SIZE_PARTITION THEN USE_THEN "Part" ACCEPT_TAC]);;

let KTC_RESTRICT_VALID = prove
 (`!h P ctu ctu' ctrr gtr gtu.
     kempe_valid h P ctu CtreeEmpty gtr gtu /\
     ctree_restrict h ctu (CtrCons Bstack0 gtr CtrNil) = CtreePair ctu' ctrr
     ==> kempe_valid h P ctu' (ctree_rotlr ctrr) GtreeEmpty gtu`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[kempe_valid; CTREE_MEM_EMPTY; GTREE_MEM_EMPTY; GTREE_SUB_EMPTY;
              ADD_CLAUSES] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`h:num`; `ctu:ctree`; `ctu':ctree`; `ctrr:ctree`;
                `gtr:gtree`; `gtu:gtree`] KTC_RESTRICT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `et0:color list` THEN
  MP_TAC(SPECL [`SUC h`; `ctrr:ctree`; `et0:color list`] CTREE_MEM_ROTLR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!g. gtree_sub gtu Bstack0 (permt g et0) = 0 /\
        ~(gtree_sub gtr Bstack0 (permt g et0) = 0)
        ==> kempe_coclosure P (ctrace_a et0) /\ LENGTH et0 = SUC h`
   (fun th -> MESON_TAC[th]) THEN
  X_GEN_TAC `g:edge_perm` THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (permt g et0) = SUC h` ASSUME_TAC THENL
   [UNDISCH_TAC `~(gtree_sub gtr Bstack0 (permt g et0) = 0)` THEN
    REWRITE_TAC[GTREE_SUB_EQ_0; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:gram_symbol list` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC
     `!w. gtree_mem gtr w ==> ~(gtree_mem gtu w) /\ init_gtree_spec (SUC h) w`
    THEN
    DISCH_THEN(MP_TAC o SPEC `w:gram_symbol list`) THEN
    ASM_REWRITE_TAC[init_gtree_spec] THEN
    ASM_MESON_TAC[MATCHPG_SIZE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC KEMPE_COCLOSURE_PERMT THEN EXISTS_TAC `g:edge_perm` THEN
    REWRITE_TAC[GSYM CTRACE_A_PERMT] THEN
    MATCH_MP_TAC KEMPE_COCLOSURE_UNMATCHED THEN
    MAP_EVERY EXISTS_TAC [`h:num`; `gtu:gtree`] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `LENGTH (permt g et0) = SUC h` THEN
    REWRITE_TAC[LENGTH_PERMT]]);;

let KTC_RESTRICT_FULL = prove
 (`!h P ctu ctu' ctrr gtr gtu sz.
     kempe_valid h P ctu CtreeEmpty gtr gtu /\
     ctree_restrict h ctu (CtrCons Bstack0 gtr CtrNil) = CtreePair ctu' ctrr /\
     kempe_complete P (SUC sz) ctu CtreeEmpty gtr gtu
     ==> kempe_complete P sz ctu' (ctree_rotlr ctrr) GtreeEmpty gtu`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[kempe_valid; kempe_complete; CTREE_MEM_EMPTY;
              GTREE_MEM_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Sz") (LABEL_TAC "Cmpl")))) THEN
  MP_TAC(SPECL [`h:num`; `ctu:ctree`; `ctu':ctree`; `ctrr:ctree`;
                `gtr:gtree`; `gtu:gtree`] KTC_RESTRICT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`SUC h`; `ctrr:ctree`] CTREE_MEM_ROTLR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_CASES_TAC `ctree_size ctrr = 0` THENL
     [DISJ2_TAC THEN SUBGOAL_THEN `ctrr = CtreeEmpty` SUBST1_TAC THENL
       [ASM_MESON_TAC[CTREE_SIZE_PROPER]; REWRITE_TAC[CTREE_ROTLR_EMPTY]];
      DISJ1_TAC THEN USE_THEN "Sz" (DISJ_CASES_THEN2 MP_TAC MP_TAC) THENL
       [UNDISCH_TAC `ctree_size ctu = ctree_size ctu' + ctree_size ctrr` THEN
        UNDISCH_TAC `~(ctree_size ctrr = 0)` THEN ARITH_TAC;
        DISCH_TAC THEN SUBGOAL_THEN `ctree_size ctrr = 0` MP_TAC THENL
         [MATCH_MP_TAC CTREE_SIZE_NOMEM THEN ASM_REWRITE_TAC[GTREE_SUB_EQ_0];
          ASM_REWRITE_TAC[]]]];
    X_GEN_TAC `et:color list` THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [DISJ2_TAC THEN USE_THEN "Cmpl" MATCH_MP_TAC THEN DISJ1_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `e:color`) THEN
    ASM_CASES_TAC `ctree_mem ctu' (etrace et)` THENL
     [ALL_TAC;
      DISJ2_TAC THEN UNDISCH_TAC `~ctree_mem ctu' (etrace et)` THEN
      ASM_REWRITE_TAC[ctree_mem; EVEN_ETRACE; GTREE_SUB_ETRACE]] THEN
    ASM_CASES_TAC `ctree_mem ctu (permt (edge_rot e) (etrace et))` THENL
     [ALL_TAC;
      DISJ2_TAC THEN USE_THEN "Cmpl" MATCH_MP_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `e:color` THEN FIRST_ASSUM ACCEPT_TAC] THEN
    DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(gtree_sub gtu Bstack0 (etrace et) = 0)` ASSUME_TAC THENL
     [UNDISCH_TAC `ctree_mem ctu' (etrace et)` THEN
      ASM_REWRITE_TAC[ctree_mem; EVEN_ETRACE];
      ALL_TAC] THEN
    SUBGOAL_THEN `ctree_mem ctrr (permt (edge_rot e) (etrace et))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ctree_mem ctu (permt (edge_rot e) (etrace et))` THEN
      UNDISCH_TAC `~ctree_mem ctu' (permt (edge_rot e) (etrace et))` THEN
      REWRITE_TAC[ctree_mem] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[ADD_EQ_0] THEN CONV_TAC TAUT;
      STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
      ASM_REWRITE_TAC[edge_rot_DEF; PERMT_ID] THEN CONV_TAC TAUT]]);;

(* ------------------------------------------------------------------------- *)
(* One ktc_step on a valid state, for an approximation ktc0 of the closure   *)
(* correct at depth d; its pair form; the induction on d; the main theorem.  *)
(* ------------------------------------------------------------------------- *)

let KTC_STEP_CORRECT = prove
 (`!h P d ktc0 ctu gtr gtu.
     ktc_correct h P d ktc0 /\ kempe_valid h P ctu CtreeEmpty gtr gtu
     ==> ktr_valid h P (ktc_step h ktc0 ctu gtr gtu) /\
         !sz. kempe_complete P (3 EXP d + SUC sz) ctu CtreeEmpty gtr gtu
              ==> ktr_complete P (SUC sz) (ktc_step h ktc0 ctu gtr gtu)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ktc_step] THEN
  ASM_CASES_TAC `ctree_empty ctu` THEN
  ASM_REWRITE_TAC[ktr_valid; ktr_complete; FST; SND; gtree_pair_sub] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP CTREE_EMPTY_EQ) THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    REWRITE_TAC[kempe_complete; ctree_size; ADD_CLAUSES; LT_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `gtree_empty gtr` THEN
  ASM_REWRITE_TAC[ktr_valid; ktr_complete; FST; SND; gtree_pair_sub] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[GTREE_EMPTY_IFF]) THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    REWRITE_TAC[kempe_complete; GTREE_MEM_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `gtree_empty gtu` THEN
  ASM_REWRITE_TAC[ktr_valid; ktr_complete; FST; SND; gtree_pair_sub;
                  empty_gtree_pair] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[GTREE_EMPTY_IFF]) THEN
    UNDISCH_TAC `kempe_valid h P ctu CtreeEmpty gtr GtreeEmpty` THEN
    REWRITE_TAC[kempe_valid; kempe_complete; ctree_proper; ctree_sub;
                ctree_size; CTREE_MEM_EMPTY; GTREE_MEM_EMPTY; GTREE_SUB_EMPTY;
                ADD_CLAUSES; COND_ID; LT_0] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `ctree_restrict h ctu (CtrCons Bstack0 gtr CtrNil)`
    (cases "ctree_pair")) THEN
  DISCH_THEN(X_CHOOSE_THEN `ctu':ctree` (X_CHOOSE_THEN `ctrr:ctree`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[ctree_pair_sub] THEN
  FIRST_X_ASSUM(MP_TAC o
                SPECL [`ctu':ctree`; `ctree_rotlr ctrr`; `gtu:gtree`] o
                REWRITE_RULE[ktc_correct; ktr_valid; ktr_complete]) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`h:num`; `P:color list->bool`; `ctu:ctree`; `ctu':ctree`;
                  `ctrr:ctree`; `gtr:gtree`; `gtu:gtree`]
                 KTC_RESTRICT_VALID) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) MP_TAC) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN X_GEN_TAC `sz:num` THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC KTC_RESTRICT_FULL THEN
  MAP_EVERY EXISTS_TAC [`h:num`; `ctu:ctree`; `gtr:gtree`] THEN
  ASM_REWRITE_TAC[]);;

let KTC_STEPP_CORRECT = prove
 (`!h P d ktc0 kr.
     ktc_correct h P d ktc0 /\ ktr_valid h P kr
     ==> ktr_valid h P (ktc_stepp h ktc0 kr) /\
         !sz. ktr_complete P (3 EXP d + SUC sz) kr
              ==> ktr_complete P (SUC sz) (ktc_stepp h ktc0 kr)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `kr:ctree#gtree_pair` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ctu:ctree` (X_CHOOSE_THEN `gp:gtree_pair`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `gp:gtree_pair` (cases "gtree_pair")) THEN
  DISCH_THEN(X_CHOOSE_THEN `gtr:gtree` (X_CHOOSE_THEN `gtu:gtree`
    SUBST1_TAC)) THEN
  REWRITE_TAC[ktc_stepp; FST; SND; gtree_pair_sub] THEN
  MP_TAC(SPECL [`h:num`; `P:color list->bool`; `d:num`;
                `ktc0:ctree->ctree->gtree->ctree#gtree_pair`;
                `ctu:ctree`; `gtr:gtree`; `gtu:gtree`] KTC_STEP_CORRECT) THEN
  REWRITE_TAC[ktr_valid; ktr_complete; FST; SND; gtree_pair_sub]);;

let KTC_CLOSURE_FN_CORRECT = prove
 (`!h P d. ktc_correct h P d (kempe_tree_closure_fn h d)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[kempe_tree_closure_fn; KTC_BASE] THEN
  REWRITE_TAC[ktc_correct] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`ctu:ctree`; `ctr:ctree`; `gtu:gtree`] o
              REWRITE_RULE[ktc_correct]) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `kr0 = kempe_tree_closure_fn h d ctu ctr gtu` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "V0") (LABEL_TAC "C0")) THEN
  MP_TAC(SPECL [`h:num`; `P:color list->bool`; `d:num`;
                `kempe_tree_closure_fn h d`; `kr0:ctree#gtree_pair`]
               KTC_STEPP_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `kr1 = ktc_stepp h (kempe_tree_closure_fn h d) kr0` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "V1") (LABEL_TAC "C1")) THEN
  MP_TAC(SPECL [`h:num`; `P:color list->bool`; `d:num`;
                `kempe_tree_closure_fn h d`; `kr1:ctree#gtree_pair`]
               KTC_STEPP_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) (LABEL_TAC "C2")) THEN
  X_GEN_TAC `sz:num` THEN DISCH_TAC THEN
  USE_THEN "C2" MATCH_MP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  USE_THEN "C1" MATCH_MP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  USE_THEN "C0" MATCH_MP_TAC THEN
  SUBGOAL_THEN `3 EXP d + 3 EXP d + 3 EXP d + sz = 3 EXP SUC d + sz`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXP] THEN ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]);;

let KEMPE_TREE_CLOSURE_CORRECT = prove
 (`!h P d ctu ctr gtu.
     kempe_valid h P ctu ctr GtreeEmpty gtu
     ==> kempe_valid h P (FST(kempe_tree_closure h d ctu ctr gtu)) CtreeEmpty
           (gtree_pair_sub (SND(kempe_tree_closure h d ctu ctr gtu)) F)
           (gtree_pair_sub (SND(kempe_tree_closure h d ctu ctr gtu)) T) /\
         (!sz. kempe_complete P (3 EXP d + sz) ctu ctr GtreeEmpty gtu
               ==> kempe_complete P (SUC sz)
                     (FST(kempe_tree_closure h d ctu ctr gtu)) CtreeEmpty
                     (gtree_pair_sub
                        (SND(kempe_tree_closure h d ctu ctr gtu)) F)
                     (gtree_pair_sub
                        (SND(kempe_tree_closure h d ctu ctr gtu)) T))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kempe_tree_closure] THEN
  MP_TAC(SPECL [`h:num`; `P:color list->bool`; `d:num`]
    KTC_CLOSURE_FN_CORRECT) THEN
  REWRITE_TAC[ktc_correct; ktr_valid; ktr_complete] THEN
  DISCH_THEN(MP_TAC o SPECL [`ctu:ctree`; `ctr:ctree`; `gtu:gtree`]) THEN
  REWRITE_TAC[]);;
