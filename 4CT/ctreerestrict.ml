(* ========================================================================= *)
(* 4CT/ctreerestrict.ml                                                      *)
(*                                                                           *)
(* ctreerestrict.v: restricting a colour trace tree.  A ctree_restriction is *)
(* a list of (bit stack, gtree) pairs standing for a set of chromogram       *)
(* matches; ctree_restrict h t r splits the ctree t into the pair of the     *)
(* traces whose match counts, decremented by those of r, are still positive  *)
(* and the others.  The main theorem CTREE_RESTRICT_CORRECT (Coq             *)
(* ctree_restrict_correct) says the result is a height-preserving partition  *)
(* of t whose first component carries the decremented counts.                *)
(* ========================================================================= *)

needs "4CT/ctree.ml";;
needs "4CT/gtree.ml";;

(* ------------------------------------------------------------------------- *)
(* ctree_restriction: a list of (bit_stack, gtree) match-pairs. Each pair    *)
(* (bs, gt) stands for the matches (bs, et, w) with matchpg bs et w and      *)
(* gtree_mem gt w. (Dual to gtreerestrict's (bit_stack, ctree) pairs.)       *)
(* ------------------------------------------------------------------------- *)

let ctree_restriction_INDUCT,ctree_restriction_RECURSION =
  define_type
    "ctree_restriction = CtrNil | CtrCons bit_stack gtree ctree_restriction";;

let ctr_cons = define
 `ctr_cons bs t r = (if gtree_empty t then r else CtrCons bs t r)`;;

(* ctr_sub r et : total match count of the partial color trace et in r.      *)
let ctr_sub = define
 `(ctr_sub CtrNil et = 0) /\
  (ctr_sub (CtrCons bs t r') et = gtree_sub t bs et + ctr_sub r' et)`;;

let CTR_SUB_CONS = prove
 (`!bs t r et. ctr_sub (ctr_cons bs t r) et =
 gtree_sub t bs et + ctr_sub r et`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ctr_cons] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ctr_sub] THEN
  FIRST_X_ASSUM(SUBST1_TAC o REWRITE_RULE[GTREE_EMPTY_IFF]) THEN
  REWRITE_TAC[GTREE_SUB_EMPTY; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* ctr_split (CPS): split a ctree_restriction into 3 sub-restrictions, one   *)
(* per non-zero color (Color1, Color2, Color3), then call the continuation.  *)
(* A node (bs, GtreeNode t0 t1 t2 t3) contributes t1 to r1 and, via the pop  *)
(* logic in ctr_cons_pop, t0/t2/t3 to r2/r3. Non-node entries are skipped.   *)
(* ------------------------------------------------------------------------- *)

(* case_gtree_node t f d : f t0 t1 t2 t3 on a node, else d.                  *)
let case_gtree_node = define
 `(case_gtree_node (GtreeNode t0 t1 t2 t3) (f:gtree->gtree->gtree->gtree->A) d
  = f t0 t1 t2 t3) /\
  (case_gtree_node GtreeLeaf0 f d = d) /\
  (case_gtree_node GtreeLeaf1 f d = d) /\
  (case_gtree_node GtreeLeaf2 f d = d) /\
  (case_gtree_node GtreeLeaf3 f d = d) /\
  (case_gtree_node GtreeLeaf01 f d = d) /\
  (case_gtree_node GtreeLeaf12 f d = d) /\
  (case_gtree_node GtreeLeaf13 f d = d) /\
  (case_gtree_node GtreeLeaf23 f d = d) /\
  (case_gtree_node GtreeEmpty f d = d)`;;

(* ctr_cons_pop bs t t' r' : the pop-branch cons used in ctr_split.          *)
let ctr_cons_pop = define
 `(ctr_cons_pop Bstack0 t t' r' = r') /\
  (ctr_cons_pop (Bpush0 bs') t t' r' = ctr_cons bs' t r') /\
  (ctr_cons_pop (Bpush1 bs') t t' r' = ctr_cons bs' t' r')`;;

let ctr_split_fn = new_recursive_definition ctree_restriction_RECURSION
 `(ctr_split_fn CtrNil =
      (\(continue:ctree_restriction->ctree_restriction->ctree_restriction->A)
        r1 r2 r3. continue r1 r2 r3)) /\
  (ctr_split_fn (CtrCons bs t r) =
      (\continue r1 r2 r3.
         case_gtree_node t
           (\t0 t1 t2 t3.
              ctr_split_fn r continue
                (ctr_cons bs t1 r1)
                (ctr_cons (Bpush0 bs) t0 (ctr_cons_pop bs t2 t3 r2))
                (ctr_cons (Bpush1 bs) t0 (ctr_cons_pop bs t3 t2 r3)))
           (ctr_split_fn r continue r1 r2 r3)))`;;

let ctr_split = new_definition
 `ctr_split continue r1 r2 r3 r = ctr_split_fn r continue r1 r2 r3`;;

let CTR_SPLIT = prove
 (`(ctr_split continue r1 r2 r3 CtrNil = continue r1 r2 r3) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs t r) =
      case_gtree_node t
        (\t0 t1 t2 t3.
           ctr_split continue
             (ctr_cons bs t1 r1)
             (ctr_cons (Bpush0 bs) t0 (ctr_cons_pop bs t2 t3 r2))
             (ctr_cons (Bpush1 bs) t0 (ctr_cons_pop bs t3 t2 r3)) r)
        (ctr_split continue r1 r2 r3 r))`,
  REWRITE_TAC[ctr_split; ctr_split_fn]);;

let CTR_SPLIT_SOME = prove
 (`ctr_split continue r1 r2 r3 (CtrCons bs (GtreeNode t0 t1 t2 t3) r) =
   ctr_split continue
     (ctr_cons bs t1 r1)
     (ctr_cons (Bpush0 bs) t0 (ctr_cons_pop bs t2 t3 r2))
     (ctr_cons (Bpush1 bs) t0 (ctr_cons_pop bs t3 t2 r3)) r`,
  REWRITE_TAC[CTR_SPLIT; case_gtree_node]);;

let CTR_SPLIT_SKIP = prove
 (`(ctr_split continue r1 r2 r3 (CtrCons bs GtreeLeaf0 r) =
    ctr_split continue r1 r2 r3 r) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs GtreeLeaf1 r) =
    ctr_split continue r1 r2 r3 r) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs GtreeLeaf2 r) =
    ctr_split continue r1 r2 r3 r) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs GtreeLeaf3 r) =
    ctr_split continue r1 r2 r3 r) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs GtreeLeaf01 r) =
    ctr_split continue r1 r2 r3 r) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs GtreeLeaf12 r) =
    ctr_split continue r1 r2 r3 r) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs GtreeLeaf13 r) =
    ctr_split continue r1 r2 r3 r) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs GtreeLeaf23 r) =
    ctr_split continue r1 r2 r3 r) /\
   (ctr_split continue r1 r2 r3 (CtrCons bs GtreeEmpty r) =
    ctr_split continue r1 r2 r3 r)`,
  REWRITE_TAC[CTR_SPLIT; case_gtree_node]);;

(* csplit r e : the e-component of the split (e in Color1/Color2/Color3).    *)
let csplit = define
 `csplit r e =
  ctr_split (\t1 t2 t3. palette CtrNil t1 t2 t3 e) CtrNil CtrNil CtrNil r`;;

let CTR_SPLIT_ACC = prove
 (`!r rk r1 r2 r3.
     ctr_split rk r1 r2 r3 r =
     rk (ctr_split (\t1 t2 t3. t1) r1 r2 r3 r)
        (ctr_split (\t1 t2 t3. t2) r1 r2 r3 r)
        (ctr_split (\t1 t2 t3. t3) r1 r2 r3 r)`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[CTR_SPLIT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a1:gtree` (cases "gtree")) THEN
  REWRITE_TAC[CTR_SPLIT; case_gtree_node] THEN
  FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN REWRITE_TAC[]);;

let CTR_SPLIT_EQ = prove
 (`!rk r. ctr_split rk CtrNil CtrNil CtrNil r =
          rk (csplit r Color1) (csplit r Color2) (csplit r Color3)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CTR_SPLIT_ACC] THEN
  REWRITE_TAC[csplit; palette]);;

(* ------------------------------------------------------------------------- *)
(* ctr_sub_csplit: the split component's match count equals a one-deeper     *)
(* count of r (or 0 on the empty trace). This is what lets us view/eliminate *)
(* a ctree_restriction as a ctree. Needs several match_count facts.          *)
(* ------------------------------------------------------------------------- *)

(* gtree_sub on the empty trace is 0.                                        *)
let GTREE_SUB_NIL = prove
 (`!t bs. gtree_sub t bs [] = 0`,
  REWRITE_TAC[gtree_sub; MATCH_COUNT; GTREE_MEM]);;

let CTR_SUB_NIL = prove
 (`!r. ctr_sub r [] = 0`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN
  REWRITE_TAC[ctr_sub; GTREE_SUB_NIL; ADD_CLAUSES]);;

(* gtree_mem on a node steps to the s-selected subtree (as a predicate).     *)
let GTREE_MEM_NODE_SHIFT = prove
 (`((\w. gtree_mem (GtreeNode t0 t1 t2 t3) (CONS Gpush w)) = gtree_mem t0) /\
   ((\w. gtree_mem (GtreeNode t0 t1 t2 t3) (CONS Gskip w)) = gtree_mem t1) /\
   ((\w. gtree_mem (GtreeNode t0 t1 t2 t3) (CONS Gpop0 w)) = gtree_mem t2) /\
   ((\w. gtree_mem (GtreeNode t0 t1 t2 t3) (CONS Gpop1 w)) = gtree_mem t3)`,
  REWRITE_TAC[FUN_EQ_THM; GTREE_MEM; gtree_isleaf; gtree_sel;
              distinctness "gram_symbol"]);;

(* gtree_sub on a node steps through a color, per the matchpg pop logic.     *)
let GTREE_SUB_NODE_STEP = prove
 (`(gtree_sub (GtreeNode t0 t1 t2 t3) bs (CONS Color1 et) =
    gtree_sub t1 bs et) /\
   (gtree_sub (GtreeNode t0 t1 t2 t3) bs (CONS Color2 et) =
    gtree_sub t0 (Bpush0 bs) et +
    case_bitstack bs 0 (\bs'. gtree_sub t2 bs' et)
                       (\bs'. gtree_sub t3 bs' et)) /\
   (gtree_sub (GtreeNode t0 t1 t2 t3) bs (CONS Color3 et) =
    gtree_sub t0 (Bpush1 bs) et +
    case_bitstack bs 0 (\bs'. gtree_sub t3 bs' et)
                       (\bs'. gtree_sub t2 bs' et))`,
  REWRITE_TAC[gtree_sub; MATCH_COUNT; distinctness "color"] THEN
  REWRITE_TAC[GTREE_MEM_NODE_SHIFT]);;

let GTREE_SUB_NODE_C0 = prove
 (`gtree_sub (GtreeNode t0 t1 t2 t3) bs (CONS Color0 et) = 0`,
  REWRITE_TAC[gtree_sub; MATCH_COUNT]);;

(* A leaf gtree only accepts single-symbol chromograms, so its count on a    *)
(* trace of length >= 2 is 0.                                                *)
let GTREE_MEM_LEAF_LENGTH = prove
 (`!t w. gtree_isleaf t /\ gtree_mem t w ==> LENGTH w = 1`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  SIMP_TAC[GTREE_MEM; LENGTH; ONE; SUC_INJ; LENGTH_EQ_NIL;
           TAUT `p /\ (if p then q else r) <=> p /\ q`]);;

let GTREE_SUB_LEAF_2 = prove
 (`!t bs e e' et'. gtree_isleaf t
                   ==> gtree_sub t bs (CONS e (CONS e' et')) = 0`,
  REWRITE_TAC[GTREE_SUB_EQ_0] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATCHPG_SIZE) THEN
  MP_TAC(SPECL [`t:gtree`; `w:gram_symbol list`] GTREE_MEM_LEAF_LENGTH) THEN
  ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let PALETTE_CONST = prove
 (`!e. palette (x:A) x x x e = x`,
  MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[palette]);;

(* Accumulator form: ctr_sub of a split component = deeper count of r plus   *)
(* the count already accumulated in the corresponding r_i.                   *)
let CTR_SUB_CSPLIT_ACC = prove
 (`!r r1 r2 r3 e e' et'.
     ctr_sub (ctr_split (\t1 t2 t3. palette CtrNil t1 t2 t3 e) r1 r2 r3 r)
     (CONS e' et')
       = ctr_sub (palette CtrNil r1 r2 r3 e) (CONS e' et') +
       ctr_sub r (CONS e (CONS e' et'))`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[CTR_SPLIT; ctr_sub; ADD_CLAUSES]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a1:gtree` (cases "gtree")) THEN
  ASM_SIMP_TAC[CTR_SPLIT_SKIP; ctr_sub; GTREE_SUB_LEAF_2; gtree_isleaf;
               GTREE_SUB_EMPTY; ADD_CLAUSES] THEN
  REWRITE_TAC[CTR_SPLIT_SOME] THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
  REWRITE_TAC[palette; GTREE_SUB_NODE_STEP; GTREE_SUB_NODE_C0; ctr_sub] THEN
  TRY(STRUCT_CASES_TAC(ISPEC `a0:bit_stack` (cases "bit_stack"))) THEN
  REWRITE_TAC[ctr_cons_pop; case_bitstack; CTR_SUB_CONS; GTREE_SUB_NODE_C0;
              ADD_CLAUSES] THEN
  ARITH_TAC);;

let CTR_SUB_CSPLIT = prove
 (`!r e et. ctr_sub (csplit r e) et =
            (if et = [] then 0 else ctr_sub r (CONS e et))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `et:color list` (cases "list")) THEN
  REWRITE_TAC[NOT_CONS_NIL; CTR_SUB_NIL] THEN
  REWRITE_TAC[csplit; CTR_SUB_CSPLIT_ACC; PALETTE_CONST; ctr_sub;
              ADD_CLAUSES]);;

(* ========================================================================= *)
(* Leaf-count decrement machinery (ctree_decr / ctr_decr): the base (height  *)
(* 1) case of ctree_restrict subtracts match counts from the three leaf      *)
(* subtrees.                                                                 *)
(* ========================================================================= *)

(* ctree_leaf_child (CtreeLeaf t) = t, else identity/Empty. Gives the child  *)
(* popped by ctree_decr.                                                     *)
let ctree_leaf_child = define
 `(ctree_leaf_child (CtreeLeaf t) = t) /\
  (ctree_leaf_child (CtreeNode t1 t2 t3) = CtreeNode t1 t2 t3) /\
  (ctree_leaf_child CtreeEmpty = CtreeEmpty)`;;

(* ctree_decr lf n : pop n CtreeLeaf's off lf (stops early at a non-leaf).   *)
let ctree_decr = define
 `(ctree_decr lf 0 = lf) /\
  (ctree_decr lf (SUC n) =
     (if ctree_leaf lf then ctree_decr (ctree_leaf_child lf) n else lf))`;;

let CTREE_LEAF_OF_SUC_EQ = prove
 (`ctree_leaf_of (SUC n) = CtreeLeaf (ctree_leaf_of n)`,
  REWRITE_TAC[ctree_leaf_of; ITER]);;

let CTREE_VAL_DECR = prove
 (`!m n. ctree_decr (ctree_leaf_of m) n = ctree_leaf_of (m - n)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[ctree_decr; SUB_0] THEN
  STRUCT_CASES_TAC(ISPEC `m:num` num_CASES) THEN
  REWRITE_TAC[ctree_leaf_of; ITER; ctree_leaf; ctree_leaf_child; SUB_0;
              SUB_SUC; ARITH_RULE `0 - n = 0`] THEN
  ASM_REWRITE_TAC[GSYM ctree_leaf_of]);;

(* ctr_e_decr bs t e lf : decrement lf by gtree_sub t bs [e].                *)
let ctr_e_decr = define
 `ctr_e_decr bs t e lf = ctree_decr lf (gtree_sub t bs [e])`;;

(* ctr_decr cont lf1 lf2 lf3 r : decrement each lfi by the color-i count of  *)
(* r, then apply the continuation. This is exactly Gonthier's ctr_decr_some  *)
(* spec (his nested-match definition is a lazy-evaluation optimisation of    *)
(* this).                                                                    *)
let ctr_decr = new_recursive_definition ctree_restriction_RECURSION
 `(ctr_decr cont lf1 lf2 lf3 CtrNil = cont lf1 lf2 lf3) /\
  (ctr_decr cont lf1 lf2 lf3 (CtrCons bs t r) =
     ctr_decr cont (ctr_e_decr bs t Color1 lf1)
                   (ctr_e_decr bs t Color2 lf2)
                   (ctr_e_decr bs t Color3 lf3) r)`;;

let CTR_DECR_SOME = prove
 (`ctr_decr cont lf1 lf2 lf3 (CtrCons bs t r)
     = ctr_decr cont (ctr_e_decr bs t Color1 lf1)
                     (ctr_e_decr bs t Color2 lf2)
                     (ctr_e_decr bs t Color3 lf3) r`,
  REWRITE_TAC[ctr_decr]);;

(* cdecr e lf1 lf2 lf3 r : the color-e component of ctr_decr from Empty      *)
(* cont.                                                                     *)
let cdecr = define
 `cdecr e = ctr_decr (\ct1 ct2 ct3. palette CtreeEmpty ct1 ct2 ct3 e)`;;

let CTR_DECR_EQ = prove
 (`!lfk lf1 lf2 lf3 r.
     ctr_decr lfk lf1 lf2 lf3 r =
     lfk (cdecr Color1 lf1 lf2 lf3 r) (cdecr Color2 lf1 lf2 lf3 r)
         (cdecr Color3 lf1 lf2 lf3 r)`,
  REWRITE_TAC[cdecr] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[]
    `(!lf1 lf2 lf3 r. P lf1 lf2 lf3 r) <=> (!r lf1 lf2 lf3. P lf1 lf2 lf3 r)`
    ] THEN
  MATCH_MP_TAC ctree_restriction_INDUCT THEN
  REWRITE_TAC[ctr_decr; palette] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let CTREE_PROPER_LEAF_OF_VAL = prove
 (`!lf. ctree_proper 0 lf ==> lf = ctree_leaf_of (ctree_sub lf [])`,
  MATCH_MP_TAC ctree_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ctree_proper; ARITH];
    GEN_TAC THEN REWRITE_TAC[ctree_proper; ctree_sub] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM ADD1; CTREE_LEAF_OF_SUC_EQ] THEN
    AP_TERM_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[ctree_sub; ctree_leaf_of; ITER]]);;

(* Decrementing a proper-0 leaf preserves properness and subtracts from      *)
(* count.                                                                    *)
let CTREE_DECR_PROPER = prove
 (`!lf n. ctree_proper 0 lf ==> ctree_proper 0 (ctree_decr lf n)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP CTREE_PROPER_LEAF_OF_VAL th)) THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CTREE_VAL_DECR; CTREE_LEAF_OF_PROPER]);;

let CTREE_SUB_DECR = prove
 (`!lf n. ctree_proper 0 lf
          ==> ctree_sub (ctree_decr lf n) [] = ctree_sub lf [] - n`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ONCE_REWRITE_TAC[MATCH_MP CTREE_PROPER_LEAF_OF_VAL th]) THEN
  REWRITE_TAC[CTREE_VAL_DECR; CTREE_SUB_LEAF_OF]);;

(* Each subtree of a proper-1 cons is a proper-0 leaf.                       *)
let PROPER_CONS_SEL = prove
 (`ctree_proper 1 (ctree_cons lf1 lf2 lf3)
     ==> ctree_proper 0 lf1 /\ ctree_proper 0 lf2 /\ ctree_proper 0 lf3`,
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`1`; `ctree_cons lf1 lf2 lf3`; `Color1`] CTREE_PROPER_SEL);
    MP_TAC(ISPECL [`1`; `ctree_cons lf1 lf2 lf3`; `Color2`] CTREE_PROPER_SEL);
    MP_TAC(ISPECL [`1`; `ctree_cons lf1 lf2 lf3`; `Color3`] CTREE_PROPER_SEL)]
  THEN ASM_REWRITE_TAC[CTREE_SEL_CONS; ctree_sel; palette; ARITH]);;

(* base of cdecr_leaf: the empty-restriction continuation value.             *)
let CDECR_BASE = prove
 (`!e lf1 lf2 lf3. ctree_proper 1 (ctree_cons lf1 lf2 lf3)
     ==> palette CtreeEmpty lf1 lf2 lf3 e =
         ctree_leaf_of (ctree_sub (ctree_cons lf1 lf2 lf3) [e])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROPER_CONS_SEL) THEN
  STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
  REWRITE_TAC[palette; CTREE_SUB_CONS; ctree_sub; HD; TL; NOT_CONS_NIL;
              distinctness "color"; LET_DEF; LET_END_DEF; ctree_leaf_of;
              ITER] THEN
  ASM_MESON_TAC[CTREE_PROPER_LEAF_OF_VAL; ctree_leaf_of]);;

(* cdecr_leaf: the decremented leaf value = leaf_of (count minus             *)
(* restriction).                                                             *)
let CDECR_LEAF = prove
 (`!r e lf1 lf2 lf3.
     ctree_proper 1 (ctree_cons lf1 lf2 lf3)
     ==> cdecr e lf1 lf2 lf3 r =
         ctree_leaf_of
         (ctree_sub (ctree_cons lf1 lf2 lf3) [e] - ctr_sub r [e])`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[cdecr; ctr_decr; ctr_sub; SUB_0] THEN
    ASM_MESON_TAC[CDECR_BASE; cdecr];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[cdecr; CTR_DECR_SOME] THEN REWRITE_TAC[GSYM cdecr] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROPER_CONS_SEL) THEN
  FIRST_X_ASSUM(fun ih -> MP_TAC(SPECL
    [`e:color`; `ctr_e_decr a0 a1 Color1 lf1`; `ctr_e_decr a0 a1 Color2 lf2`;
     `ctr_e_decr a0 a1 Color3 lf3`] ih)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ctr_e_decr] THEN
    MATCH_MP_TAC(REWRITE_RULE[ARITH_RULE `0 + 1 = 1`]
                   (SPEC `0` CTREE_CONS_PROPER)) THEN
    ASM_SIMP_TAC[CTREE_DECR_PROPER];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ctr_sub] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `ctree_sub (ctree_cons (ctr_e_decr a0 a1 Color1 lf1)
               (ctr_e_decr a0 a1 Color2 lf2)
                          (ctr_e_decr a0 a1 Color3 lf3)) [e]
    = ctree_sub (ctree_cons lf1 lf2 lf3) [e] - gtree_sub a1 a0 [e]`
   (fun th -> REWRITE_TAC[th]) THENL
   [STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
    REWRITE_TAC[CTREE_SUB_CONS; CTREE_SUB_SEL; ctree_sel; palette;
                ctr_e_decr] THEN
    REWRITE_TAC[ctree_sub; SUB_0] THEN ASM_SIMP_TAC[CTREE_SUB_DECR];
    ARITH_TAC]);;

(* ========================================================================= *)
(* ctree_cons_pairs, partitions, and ctree_leaf_pair (recursive-step and     *)
(* base-case pair constructors of ctree_restrict).                           *)
(* ========================================================================= *)

(* ctree_cons_pairs pt1 pt2 pt3 : node-combine the components of 3 pairs.    *)
let ctree_cons_pairs = define
 `ctree_cons_pairs (CtreePair t1 t1') (CtreePair t2 t2') (CtreePair t3 t3') =
    (if ctree_empty_node (CtreeNode t1 t2 t3) then
       (if ctree_empty_node (CtreeNode t1' t2' t3')
       then CtreePair CtreeEmpty CtreeEmpty
        else CtreePair CtreeEmpty (CtreeNode t1' t2' t3'))
     else if ctree_empty_node (CtreeNode t1' t2' t3')
     then CtreePair (CtreeNode t1 t2 t3) CtreeEmpty
     else CtreePair (CtreeNode t1 t2 t3) (CtreeNode t1' t2' t3'))`;;

let CTREE_CONS_PAIRS_SPEC = prove
 (`ctree_cons_pairs (CtreePair t1 t1') (CtreePair t2 t2') (CtreePair t3 t3') =
     CtreePair (ctree_cons t1 t2 t3) (ctree_cons t1' t2' t3')`,
  REWRITE_TAC[ctree_cons_pairs; CTREE_CONS_SPEC] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]));;

(* sctree_partition / ctree_partition: pt is a partition of t (counts need   *)
(* not add up, only membership).                                             *)
let sctree_partition = define
 `sctree_partition (st:colseq->bool) st' st'' <=>
    (!et. (if st et then (st' et <=> st'' et) else (st' et \/ st'' et)) = F)`;;

let ctree_partition = define
 `ctree_partition t (CtreePair t' t'') <=>
    sctree_partition (ctree_mem t) (ctree_mem t') (ctree_mem t'')`;;

let CTREE_CONS_PAIRS_PARTITION = prove
 (`!t1 t2 t3 pt1 pt2 pt3.
     ctree_partition t1 pt1 /\ ctree_partition t2 pt2 /\ ctree_partition t3 pt3
     ==> ctree_partition (CtreeNode t1 t2 t3) (ctree_cons_pairs pt1 pt2 pt3)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `pt1:ctree_pair` (cases "ctree_pair")) THEN
  STRUCT_CASES_TAC(ISPEC `pt2:ctree_pair` (cases "ctree_pair")) THEN
  STRUCT_CASES_TAC(ISPEC `pt3:ctree_pair` (cases "ctree_pair")) THEN
  REWRITE_TAC[ctree_partition; CTREE_CONS_PAIRS_SPEC] THEN
  REWRITE_TAC[sctree_partition; ctree_mem; CTREE_SUB_CONS] THEN
  STRIP_TAC THEN X_GEN_TAC `et:color list` THEN
  MP_TAC(ISPEC `et:color list` (cases "list")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `c:color` (X_CHOOSE_THEN `w:color list` SUBST1_TAC))) THEN
  REWRITE_TAC[ctree_sub; HD; TL; NOT_CONS_NIL; LET_DEF; LET_END_DEF] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `w:color list`)) THEN
  STRUCT_CASES_TAC(ISPEC `c:color` (cases "color")) THEN
  REWRITE_TAC[distinctness "color"] THEN CONV_TAC TAUT);;

let CTREE_SUB0_CONS_PAIRS = prove
 (`!pt1 pt2 pt3 et.
     ctree_sub (ctree_pair_sub (ctree_cons_pairs pt1 pt2 pt3) F) et =
     ctree_sub (CtreeNode (ctree_pair_sub pt1 F) (ctree_pair_sub pt2 F)
                          (ctree_pair_sub pt3 F)) et`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `pt1:ctree_pair` (cases "ctree_pair")) THEN
  STRUCT_CASES_TAC(ISPEC `pt2:ctree_pair` (cases "ctree_pair")) THEN
  STRUCT_CASES_TAC(ISPEC `pt3:ctree_pair` (cases "ctree_pair")) THEN
  REWRITE_TAC[CTREE_CONS_PAIRS_SPEC; ctree_pair_sub; CTREE_SUB_CONS]);;

(* ctree_leaf_pair: the height-1 base pair. Defined via the clean spec       *)
(* (ctree_leaf_pair_spec); Gonthier's nested match is a lazy-eval            *)
(* optimisation.                                                             *)
let ctree_if_e = define
 `ctree_if_e lf lf' = (if ctree_empty lf' then lf else CtreeEmpty)`;;

let ctree_leaf_pair = define
 `ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3' =
    CtreePair (ctree_cons lf1' lf2' lf3')
              (ctree_cons (ctree_if_e lf1 lf1') (ctree_if_e lf2 lf2')
              (ctree_if_e lf3 lf3'))`;;

let CTREE_LEAF_PAIR_SPEC = prove
 (`ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3' =
     CtreePair (ctree_cons lf1' lf2' lf3')
               (ctree_cons (if ctree_empty lf1' then lf1 else CtreeEmpty)
                           (if ctree_empty lf2' then lf2 else CtreeEmpty)
                           (if ctree_empty lf3' then lf3 else CtreeEmpty))`,
  REWRITE_TAC[ctree_leaf_pair; ctree_if_e]);;

(* ========================================================================= *)
(* ctree_restrict h t r: the ctree_pair partition of t whose false (first)   *)
(* component subtracts the ctr_sub match counts from t (for height h+1).     *)
(* Recurses on the height h; CtrNil short-circuits; a node either splits     *)
(* (recursive step) or decrements its leaves (base, height 0).               *)
(* ========================================================================= *)

let ctr_isnil = define
 `(ctr_isnil CtrNil = T) /\ (ctr_isnil (CtrCons bs t r) = F)`;;

(* case_ctree_node t f d : f t1 t2 t3 on a node, else d.                     *)
let case_ctree_node = define
 `(case_ctree_node (CtreeNode t1 t2 t3) (f:ctree->ctree->ctree->A) d =
  f t1 t2 t3) /\
  (case_ctree_node (CtreeLeaf lf) f d = d) /\
  (case_ctree_node CtreeEmpty f d = d)`;;

let ctree_restrict_fn = new_recursive_definition num_RECURSION
 `(ctree_restrict_fn 0 =
     (\t r. if ctr_isnil r then CtreePair t CtreeEmpty
            else case_ctree_node t
                   (\lf1 lf2 lf3. ctr_decr (ctree_leaf_pair lf1 lf2 lf3)
                   lf1 lf2 lf3 r)
                   ctree_empty_pair)) /\
  (ctree_restrict_fn (SUC h) =
     (\t r. if ctr_isnil r then CtreePair t CtreeEmpty
            else case_ctree_node t
                   (\t1 t2 t3. ctr_split
                      (\r1 r2 r3. ctree_cons_pairs (ctree_restrict_fn h t1 r1)
                                                   (ctree_restrict_fn h t2 r2)
                                                   (ctree_restrict_fn h t3 r3))
                      CtrNil CtrNil CtrNil r)
                   ctree_empty_pair))`;;

let ctree_restrict = new_definition
 `ctree_restrict h t r = ctree_restrict_fn h t r`;;

let CTREE_RESTRICT = prove
 (`(ctree_restrict 0 t r =
      (if ctr_isnil r then CtreePair t CtreeEmpty
       else case_ctree_node t
              (\lf1 lf2 lf3. ctr_decr (ctree_leaf_pair lf1 lf2 lf3)
              lf1 lf2 lf3 r)
              ctree_empty_pair)) /\
   (ctree_restrict (SUC h) t r =
      (if ctr_isnil r then CtreePair t CtreeEmpty
       else case_ctree_node t
              (\t1 t2 t3. ctr_split
                 (\r1 r2 r3. ctree_cons_pairs (ctree_restrict h t1 r1)
                                              (ctree_restrict h t2 r2)
                                              (ctree_restrict h t3 r3))
                 CtrNil CtrNil CtrNil r)
              ctree_empty_pair))`,
  REWRITE_TAC[ctree_restrict; ctree_restrict_fn]);;

(* ========================================================================= *)
(* Main correctness theorem (ctree_restrict_correct): the restriction is a   *)
(* height-preserving partition whose false component subtracts the counts.   *)
(* Supporting lemmas first.                                                  *)
(* ========================================================================= *)

let CTR_ISNIL_EQ = prove
 (`!r. ctr_isnil r <=> r = CtrNil`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN
  REWRITE_TAC[ctr_isnil; distinctness "ctree_restriction"]);;

let CTREE_PARTITION_LEFT = prove
 (`!t. ctree_partition t (CtreePair t CtreeEmpty)`,
  GEN_TAC THEN
  REWRITE_TAC[ctree_partition; sctree_partition; ctree_mem; ctree_sub] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let CTREE_CONS_NODE_PROPER = prove
 (`ctree_proper (SUC h) (CtreeNode t1 t2 t3) ==>
 ctree_cons t1 t2 t3 = CtreeNode t1 t2 t3`,
  REWRITE_TAC[ctree_proper; CTREE_CONS_SPEC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* leaf_of arithmetic: emptiness, membership, node-singleton subtraction.    *)
let CTREE_EMPTY_LEAF_OF = prove
 (`!n. ctree_empty (ctree_leaf_of n) <=> n = 0`,
  INDUCT_TAC THEN
  REWRITE_TAC[CTREE_LEAF_OF_SUC_EQ; ctree_leaf_of; ITER;
              ctree_empty; NOT_SUC]);;

let CTREE_SUB_NODE_SING = prove
 (`(ctree_sub (CtreeNode t1 t2 t3) [Color1] = ctree_sub t1 []) /\
   (ctree_sub (CtreeNode t1 t2 t3) [Color2] = ctree_sub t2 []) /\
   (ctree_sub (CtreeNode t1 t2 t3) [Color3] = ctree_sub t3 []) /\
   (ctree_sub (CtreeNode t1 t2 t3) [Color0] = 0)`,
  REWRITE_TAC[ctree_sub; HD; TL; NOT_CONS_NIL; distinctness "color";
              LET_DEF; LET_END_DEF]);;

(* The CtreeNode/non-nil sub-case of the height-0 base: ctr_decr over the    *)
(* leaf triple decrements each leaf's count by the restriction's count       *)
(* (Gonthier ctreerestrict.v:342-360). Everything reduces to ctree_leaf_of   *)
(* arithmetic.                                                               *)
let NODE_BASE = prove
 (`!lf1 lf2 lf3 r. ctree_proper (SUC 0) (CtreeNode lf1 lf2 lf3) ==>
     (!b. ctree_proper (SUC 0)
            (ctree_pair_sub
            (ctr_decr (ctree_leaf_pair lf1 lf2 lf3) lf1 lf2 lf3 r) b)) /\
     ctree_partition (CtreeNode lf1 lf2 lf3)
                     (ctr_decr (ctree_leaf_pair lf1 lf2 lf3) lf1 lf2 lf3 r) /\
     (!et. ctree_sub
 (ctree_pair_sub (ctr_decr (ctree_leaf_pair lf1 lf2 lf3) lf1 lf2 lf3 r) F) et =
           ctree_sub (CtreeNode lf1 lf2 lf3) et - ctr_sub r et)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CTREE_CONS_NODE_PROPER) THEN
  SUBGOAL_THEN `ctree_proper 1 (ctree_cons lf1 lf2 lf3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `SUC 0 = 1`]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROPER_CONS_SEL) THEN
  REWRITE_TAC[CTR_DECR_EQ] THEN ASM_SIMP_TAC[CDECR_LEAF] THEN
  REWRITE_TAC[CTREE_LEAF_PAIR_SPEC] THEN
  ASM_REWRITE_TAC[CTREE_SUB_NODE_SING] THEN
  ABBREV_TAC `n1 = ctree_sub lf1 []` THEN
  ABBREV_TAC `n2 = ctree_sub lf2 []` THEN
  ABBREV_TAC `n3 = ctree_sub lf3 []` THEN
  SUBGOAL_THEN
   `lf1 = ctree_leaf_of n1 /\ lf2 = ctree_leaf_of n2 /\ lf3 = ctree_leaf_of n3`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CTREE_PROPER_LEAF_OF_VAL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* height preserved *)
    GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `b:bool` BOOL_CASES_AX) THEN
    REWRITE_TAC[ctree_pair_sub] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `SUC 0 = 0 + 1`] THEN
    MATCH_MP_TAC CTREE_CONS_PROPER THEN
    REPEAT CONJ_TAC THEN TRY(COND_CASES_TAC) THEN
    ASM_REWRITE_TAC[CTREE_LEAF_OF_PROPER; ctree_proper];
(* partition                                                                 *)
    ASM_REWRITE_TAC[ctree_partition; sctree_partition; ctree_mem;
                    CTREE_SUB_CONS] THEN
    X_GEN_TAC `et:color list` THEN
    MP_TAC(ISPEC `et:color list` (cases "list")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `c:color` (X_CHOOSE_THEN `w:color list` SUBST1_TAC))) THEN
    REWRITE_TAC[ctree_sub; HD; TL; NOT_CONS_NIL; LET_DEF; LET_END_DEF] THEN
    STRUCT_CASES_TAC(ISPEC `c:color` (cases "color")) THEN
    REWRITE_TAC[distinctness "color"] THEN
    STRUCT_CASES_TAC(ISPEC `w:color list` (cases "list")) THEN
    REWRITE_TAC[CTREE_SUB_LEAF_OF; CTREE_EMPTY_LEAF_OF; NOT_CONS_NIL] THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[CTREE_SUB_LEAF_OF; ctree_sub; NOT_CONS_NIL] THEN
    ASM_ARITH_TAC;
(* count subtraction                                                         *)
    GEN_TAC THEN ASM_REWRITE_TAC[ctree_pair_sub; CTREE_SUB_CONS] THEN
    STRUCT_CASES_TAC(ISPEC `et:color list` (cases "list")) THEN
    REWRITE_TAC[ctree_sub; HD; TL; NOT_CONS_NIL; LET_DEF; LET_END_DEF] THEN
    STRUCT_CASES_TAC(ISPEC `a0:color` (cases "color")) THEN
    REWRITE_TAC[distinctness "color"; CTREE_SUB_LEAF_OF; SUB_0] THEN
    STRUCT_CASES_TAC(ISPEC `a1:color list` (cases "list")) THEN
    REWRITE_TAC[NOT_CONS_NIL; SUB_0]]);;

(* Recursive-step helpers: cons_pairs preserves height; a proper (SUC h)     *)
(* tree has zero empty-trace count.                                          *)
let CTREE_CONS_PAIRS_PROPER = prove
 (`!h pt1 pt2 pt3.
     (!b. ctree_proper (SUC h) (ctree_pair_sub pt1 b)) /\
     (!b. ctree_proper (SUC h) (ctree_pair_sub pt2 b)) /\
     (!b. ctree_proper (SUC h) (ctree_pair_sub pt3 b))
     ==> (!b. ctree_proper (SUC(SUC h))
                (ctree_pair_sub (ctree_cons_pairs pt1 pt2 pt3) b))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `pt1:ctree_pair` (cases "ctree_pair")) THEN
  STRUCT_CASES_TAC(ISPEC `pt2:ctree_pair` (cases "ctree_pair")) THEN
  STRUCT_CASES_TAC(ISPEC `pt3:ctree_pair` (cases "ctree_pair")) THEN
  REWRITE_TAC[CTREE_CONS_PAIRS_SPEC; ctree_pair_sub] THEN STRIP_TAC THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `b:bool` BOOL_CASES_AX) THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `SUC(SUC h) = (SUC h) + 1`] THEN
  MATCH_MP_TAC CTREE_CONS_PROPER THEN
  REPEAT CONJ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `T` th) THEN MP_TAC(SPEC `F` th)))
    THEN
  REWRITE_TAC[ctree_pair_sub] THEN MESON_TAC[]);;

let CTREE_SUB_NIL_PROPER = prove
 (`!t h. ctree_proper (SUC h) t ==> ctree_sub t [] = 0`,
  MATCH_MP_TAC ctree_INDUCT THEN
  REWRITE_TAC[ctree_sub; ctree_proper; NOT_SUC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* The CtreeNode/non-nil recursive step: split r by colour, restrict each    *)
(* subtree at height h (IH), and recombine with ctree_cons_pairs.            *)
let NODE_STEP_SUC = prove
 (`!h t1 t2 t3 r.
     (!t r. ctree_proper (SUC h) t ==>
        (!b. ctree_proper (SUC h) (ctree_pair_sub (ctree_restrict h t r) b)) /\
        ctree_partition t (ctree_restrict h t r) /\
        (!et. ctree_sub (ctree_pair_sub (ctree_restrict h t r) F) et =
              ctree_sub t et - ctr_sub r et))
     ==> ctree_proper (SUC(SUC h)) (CtreeNode t1 t2 t3)
     ==> (!b. ctree_proper (SUC(SUC h))
                (ctree_pair_sub (ctr_split
                   (\r1 r2 r3. ctree_cons_pairs (ctree_restrict h t1 r1)
                                                (ctree_restrict h t2 r2)
                                                (ctree_restrict h t3 r3))
                   CtrNil CtrNil CtrNil r) b)) /\
         ctree_partition (CtreeNode t1 t2 t3)
                (ctr_split (\r1 r2 r3. ctree_cons_pairs
                            (ctree_restrict h t1 r1)
                                                (ctree_restrict h t2 r2)
                                                (ctree_restrict h t3 r3))
                   CtrNil CtrNil CtrNil r) /\
         (!et. ctree_sub (ctree_pair_sub (ctr_split
                   (\r1 r2 r3. ctree_cons_pairs (ctree_restrict h t1 r1)
                                                (ctree_restrict h t2 r2)
                                                (ctree_restrict h t3 r3))
                   CtrNil CtrNil CtrNil r) F) et =
               ctree_sub (CtreeNode t1 t2 t3) et - ctr_sub r et)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[CTR_SPLIT_EQ] THEN
  FIRST_X_ASSUM(fun ih ->
    MP_TAC(SPECL [`t1:ctree`; `csplit r Color1`] ih) THEN
    MP_TAC(SPECL [`t2:ctree`; `csplit r Color2`] ih) THEN
    MP_TAC(SPECL [`t3:ctree`; `csplit r Color3`] ih)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[ctree_proper; ARITH_RULE `SUC(SUC h) - 1 = SUC h`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
    `ctree_sub t1 [] = 0 /\ ctree_sub t2 [] = 0 /\ ctree_sub t3 [] = 0`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CTREE_SUB_NIL_PROPER]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CTREE_CONS_PAIRS_PROPER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CTREE_CONS_PAIRS_PARTITION THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[CTREE_SUB0_CONS_PAIRS] THEN
    STRUCT_CASES_TAC(ISPEC `et:color list` (cases "list")) THEN
    REWRITE_TAC[ctree_sub; HD; TL; NOT_CONS_NIL; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CTR_SUB_CSPLIT] THEN
    STRUCT_CASES_TAC(ISPEC `a0:color` (cases "color")) THEN
    REWRITE_TAC[distinctness "color"] THEN
    STRUCT_CASES_TAC(ISPEC `a1:color list` (cases "list")) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; SUB_0; ctree_sub] THEN
    REWRITE_TAC[ARITH_RULE `0 - x = 0`]]);;

(* Main correctness theorem (Gonthier ctree_restrict_correct,                *)
(* ctreerestrict.v:329)                                                      *)
let CTREE_RESTRICT_CORRECT = prove
 (`!h t r. ctree_proper (SUC h) t ==>
     (!b. ctree_proper (SUC h) (ctree_pair_sub (ctree_restrict h t r) b)) /\
     ctree_partition t (ctree_restrict h t r) /\
     (!et. ctree_sub (ctree_pair_sub (ctree_restrict h t r) F) et =
           ctree_sub t et - ctr_sub r et)`,
  INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:ctree` (cases "ctree")) THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `ctr_isnil r` THEN
  ASM_REWRITE_TAC[CTREE_RESTRICT; case_ctree_node] THEN
  TRY(FIRST_X_ASSUM(fun th -> MP_TAC th THEN
        REWRITE_TAC[ctree_proper; ARITH; NOT_SUC] THEN NO_TAC)) THEN
  TRY(RULE_ASSUM_TAC(REWRITE_RULE[CTR_ISNIL_EQ]) THEN
      ASM_REWRITE_TAC[ctree_pair_sub; ctr_sub; SUB_0;
                      CTREE_PARTITION_LEFT] THEN
      REPEAT CONJ_TAC THEN
      TRY(GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ctree_proper]) THEN
      NO_TAC) THEN
  TRY(REWRITE_TAC[ctree_empty_pair; ctree_pair_sub; ctree_proper; COND_ID;
                  ctree_sub; SUB_0; ctree_partition; sctree_partition;
                  CTREE_MEM_EMPTY] THEN
      NO_TAC) THENL
   [MATCH_MP_TAC NODE_BASE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] NODE_STEP_SUC) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM ACCEPT_TAC]);;
