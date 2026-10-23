(* ========================================================================= *)
(* 4CT/ctree.ml                                                              *)
(*                                                                           *)
(* ctree.v: colour trace trees.  A ctree is a ternary tree indexed by edge   *)
(* traces, representing a set of ring colouring traces: either the           *)
(* unreachable traces with multiplicities (a stack of CtreeLeaf constructors *)
(* counting the matching chromograms) or a set of reachable traces.  All     *)
(* leaves of a proper tree (ctree_proper) sit at the same depth, the ring    *)
(* size minus one.  The file defines the constructors (ctree_cons,           *)
(* ctree_leaf_of, ctree_of_ttail), membership and multiplicity (ctree_mem,   *)
(* ctree_sub), the union, the rotations and the disjointness test, with      *)
(* their membership and properness lemmas.                                   *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "4CT/color.ml";;

(* ------------------------------------------------------------------------- *)
(* The datatype: ternary node, unary leaf (repeated => multiplicity), empty. *)
(* ------------------------------------------------------------------------- *)

let ctree_INDUCT,ctree_RECURSION =
  define_type
    "ctree = CtreeNode ctree ctree ctree | CtreeLeaf ctree | CtreeEmpty";;

let ctree_pair_INDUCT,ctree_pair_RECURSION =
  define_type "ctree_pair = CtreePair ctree ctree";;

(* ------------------------------------------------------------------------- *)
(* palette v0 v1 v2 v3 : color -> A  --  case analysis on a color            *)
(* (Gonthier's `palette` Notation).                                          *)
(* ------------------------------------------------------------------------- *)

let palette = define
 `palette (v0:A) v1 v2 v3 Color0 = v0 /\
  palette (v0:A) v1 v2 v3 Color1 = v1 /\
  palette (v0:A) v1 v2 v3 Color2 = v2 /\
  palette (v0:A) v1 v2 v3 Color3 = v3`;;

(* ------------------------------------------------------------------------- *)
(* Classifiers.                                                              *)
(* ------------------------------------------------------------------------- *)

let ctree_empty = define
 `ctree_empty CtreeEmpty = T /\
  ctree_empty (CtreeNode t1 t2 t3) = F /\
  ctree_empty (CtreeLeaf t) = F`;;

let ctree_leaf = define
 `ctree_leaf CtreeEmpty = F /\
  ctree_leaf (CtreeNode t1 t2 t3) = F /\
  ctree_leaf (CtreeLeaf t) = T`;;

(* ctree_empty_node t <=> t is a node whose three subtrees are all empty.    *)
let ctree_empty_node = define
 `ctree_empty_node CtreeEmpty = F /\
  ctree_empty_node (CtreeLeaf t) = F /\
  ctree_empty_node (CtreeNode t1 t2 t3) =
     (ctree_empty t1 /\ ctree_empty t2 /\ ctree_empty t3)`;;

(* Node subtree accessors (return CtreeEmpty off a node).                    *)
let ctree_lsub = define
 `ctree_lsub (CtreeNode t1 t2 t3) = t1 /\
  ctree_lsub (CtreeLeaf t) = CtreeEmpty /\
  ctree_lsub CtreeEmpty = CtreeEmpty`;;
let ctree_msub = define
 `ctree_msub (CtreeNode t1 t2 t3) = t2 /\
  ctree_msub (CtreeLeaf t) = CtreeEmpty /\
  ctree_msub CtreeEmpty = CtreeEmpty`;;
let ctree_rsub = define
 `ctree_rsub (CtreeNode t1 t2 t3) = t3 /\
  ctree_rsub (CtreeLeaf t) = CtreeEmpty /\
  ctree_rsub CtreeEmpty = CtreeEmpty`;;

(* ctree_sel t e : the immediate subtree of t indexed by color e (CtreeEmpty *)
(* off a node or at Color0).                                                 *)
let ctree_sel = define
 `ctree_sel (CtreeNode t1 t2 t3) = palette CtreeEmpty t1 t2 t3 /\
  ctree_sel (CtreeLeaf t) = (\c. CtreeEmpty) /\
  ctree_sel CtreeEmpty = (\c. CtreeEmpty)`;;

(* ------------------------------------------------------------------------- *)
(* ctree_proper h t : t is a proper ctree of height h (no empty nodes, no    *)
(* nodes under leaves, all leaves at depth h).                               *)
(* ------------------------------------------------------------------------- *)

let ctree_proper = define
 `(ctree_proper h CtreeEmpty <=> T) /\
  (ctree_proper h (CtreeNode t1 t2 t3) <=>
      ~(h = 0) /\
      ~(ctree_empty_node (CtreeNode t1 t2 t3)) /\
      ctree_proper (h-1) t1 /\ ctree_proper (h-1) t2 /\ ctree_proper (h-1) t3)
      /\
  (ctree_proper h (CtreeLeaf lf) <=> (h = 0) /\ ctree_proper 0 lf)`;;

(* ------------------------------------------------------------------------- *)
(* ctree_sub t et : multiplicity of trace et in t (a multiset count).        *)
(* ctree_mem t et : et occurs (positive multiplicity).                       *)
(* ------------------------------------------------------------------------- *)

let ctree_sub = define
 `(ctree_sub CtreeEmpty et = 0) /\
  (ctree_sub (CtreeNode t1 t2 t3) et =
      (if et = [] then 0
       else (let e = HD et in let et' = TL et in
             if e = Color0 then 0
             else if e = Color1 then ctree_sub t1 et'
             else if e = Color2 then ctree_sub t2 et'
             else ctree_sub t3 et'))) /\
  (ctree_sub (CtreeLeaf lf) et =
      (if et = [] then ctree_sub lf et + 1 else 0))`;;

let ctree_mem = define
 `ctree_mem t et <=> ~(ctree_sub t et = 0)`;;

(* ------------------------------------------------------------------------- *)
(* Pairs (return type of the restriction operation).                         *)
(* ------------------------------------------------------------------------- *)

let ctree_empty_pair = define
 `ctree_empty_pair = CtreePair CtreeEmpty CtreeEmpty`;;

let ctree_pair_sub = define
 `ctree_pair_sub (CtreePair t0 t1) b = (if b then t1 else t0)`;;

(* ------------------------------------------------------------------------- *)
(* Leaf constructor: ctree_leaf_of n = a stack of n leaves over CtreeEmpty.  *)
(* ------------------------------------------------------------------------- *)

let ctree_leaf_of = define
 `ctree_leaf_of n = ITER n CtreeLeaf CtreeEmpty`;;

(* ------------------------------------------------------------------------- *)
(* The interlocking node constructor and its specialisations. ctree_cons t1  *)
(* t2 t3 = CtreeEmpty if all empty, else CtreeNode t1 t2 t3.                 *)
(* ------------------------------------------------------------------------- *)

let ctree_cons = define
 `ctree_cons t1 t2 t3 =
    (if ctree_empty t1 /\ ctree_empty t2 /\ ctree_empty t3
     then CtreeEmpty else CtreeNode t1 t2 t3)`;;

let ctree_cons0 = define `ctree_cons0 (t:ctree) = CtreeEmpty`;;
let ctree_cons1 = define `ctree_cons1 t = ctree_cons t CtreeEmpty CtreeEmpty`;;
let ctree_cons2 = define `ctree_cons2 t = ctree_cons CtreeEmpty t CtreeEmpty`;;
let ctree_cons3 = define `ctree_cons3 t = ctree_cons CtreeEmpty CtreeEmpty t`;;

let ctree_simple_leaf = define `ctree_simple_leaf = CtreeLeaf CtreeEmpty`;;

let ctree_cons_e = define
 `ctree_cons_e = palette ctree_cons0 ctree_cons1 ctree_cons2 ctree_cons3`;;

(* ctree_of_ttail et : the singleton ctree containing exactly et.            *)
let ctree_of_ttail = define
 `ctree_of_ttail (et:color list) = ITLIST ctree_cons_e et ctree_simple_leaf`;;

(* ------------------------------------------------------------------------- *)
(* Union (interlocked): recursion on the right argument.                     *)
(* ------------------------------------------------------------------------- *)

let ctree_union = define
 `(ctree_union tl CtreeEmpty = tl) /\
  (ctree_union tl (CtreeLeaf lr) =
      (if ctree_empty tl then CtreeLeaf lr else ctree_simple_leaf)) /\
  (ctree_union tl (CtreeNode tr1 tr2 tr3) =
      (if ctree_empty tl then CtreeNode tr1 tr2 tr3
       else if ctree_leaf tl then ctree_simple_leaf
       else ctree_cons (ctree_union (ctree_lsub tl) tr1)
                       (ctree_union (ctree_msub tl) tr2)
                       (ctree_union (ctree_rsub tl) tr3)))`;;

(* ------------------------------------------------------------------------- *)
(* Rotations (image under Eperm231 / Eperm312) and the initial cons_rot.     *)
(* ------------------------------------------------------------------------- *)

let ctree_rotl = define
 `(ctree_rotl (CtreeNode t1 t2 t3) =
      ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2)) /\
  (ctree_rotl (CtreeLeaf lf) = CtreeLeaf lf) /\
  (ctree_rotl CtreeEmpty = CtreeEmpty)`;;

let ctree_rotr = define
 `(ctree_rotr (CtreeNode t1 t2 t3) =
      ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1)) /\
  (ctree_rotr (CtreeLeaf lf) = CtreeLeaf lf) /\
  (ctree_rotr CtreeEmpty = CtreeEmpty)`;;

let ctree_cons_rot = define
 `ctree_cons_rot t = ctree_cons t (ctree_rotl t) (ctree_rotr t)`;;

(* ------------------------------------------------------------------------- *)
(* Union of rotations (interlocked): recursion on the right argument.        *)
(* ------------------------------------------------------------------------- *)

let ctree_union_rotlr = define
 `(ctree_union_rotlr tl CtreeEmpty =
  ctree_union (ctree_rotl tl) (ctree_rotr CtreeEmpty)) /\
  (ctree_union_rotlr tl (CtreeLeaf lr) =
      (if ctree_leaf tl then ctree_simple_leaf
       else ctree_union (ctree_rotl tl) (ctree_rotr (CtreeLeaf lr)))) /\
  (ctree_union_rotlr tl (CtreeNode tr1 tr2 tr3) =
      (if ctree_empty tl \/ ctree_leaf tl
       then ctree_union (ctree_rotl tl) (ctree_rotr (CtreeNode tr1 tr2 tr3))
       else ctree_cons (ctree_union_rotlr (ctree_rsub tl) tr2)
                       (ctree_union_rotlr (ctree_lsub tl) tr3)
                       (ctree_union_rotlr (ctree_msub tl) tr1)))`;;

let ctree_rotlr = define `ctree_rotlr t = ctree_union_rotlr t t`;;

(* ------------------------------------------------------------------------- *)
(* Disjointness test (recursion on the right argument).                      *)
(* ------------------------------------------------------------------------- *)

let ctree_disjoint = define
 `(ctree_disjoint tl CtreeEmpty = T) /\
  (ctree_disjoint tl (CtreeLeaf lr) = (if ctree_leaf tl then F else T)) /\
  (ctree_disjoint tl (CtreeNode tr1 tr2 tr3) =
      (if ctree_empty tl \/ ctree_leaf tl then T
       else (ctree_disjoint (ctree_lsub tl) tr1 /\
             ctree_disjoint (ctree_msub tl) tr2 /\
             ctree_disjoint (ctree_rsub tl) tr3)))`;;

(* ========================================================================= *)
(* Classifier and accessor lemmas.                                           *)
(* ========================================================================= *)

let CTREE_EMPTY_EQ = prove
 (`!t. ctree_empty t ==> t = CtreeEmpty`,
  MATCH_MP_TAC ctree_INDUCT THEN REWRITE_TAC[ctree_empty]);;

let CTREE_EMPTY_NODE_EQ = prove
 (`!t1 t2 t3. ctree_empty_node (CtreeNode t1 t2 t3)
              ==> t1 = CtreeEmpty /\ t2 = CtreeEmpty /\ t3 = CtreeEmpty`,
  REWRITE_TAC[ctree_empty_node] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CTREE_EMPTY_EQ]);;

let CTREE_SEL_0 = prove
 (`!t. ctree_sel t Color0 = CtreeEmpty`,
  MATCH_MP_TAC ctree_INDUCT THEN REWRITE_TAC[ctree_sel; palette]);;

let CTREE_PROPER_SEL = prove
 (`!h t e. ctree_proper h t ==> ctree_proper (h-1) (ctree_sel t e)`,
  GEN_TAC THEN MATCH_MP_TAC ctree_INDUCT THEN
  REWRITE_TAC[ctree_sel; ctree_proper] THEN REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
  ASM_REWRITE_TAC[palette; ctree_proper]);;

let CTREE_SUB_SEL = prove
 (`!t e et. ctree_sub t (CONS e et) = ctree_sub (ctree_sel t e) et`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:ctree` (cases "ctree")) THEN
  REWRITE_TAC[ctree_sub; ctree_sel; NOT_CONS_NIL; HD; TL; LET_DEF;
              LET_END_DEF] THEN
  STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
  REWRITE_TAC[palette; ctree_sub; distinctness "color"]);;

let CTREE_SUB_0 = prove
 (`!t et. MEM Color0 et ==> ctree_sub t et = 0`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; CTREE_SUB_SEL] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CTREE_SEL_0; ctree_sub]);;

let CTREE_MEM_0 = prove
 (`!t et. MEM Color0 et ==> (ctree_mem t et <=> F)`,
  REWRITE_TAC[ctree_mem] THEN MESON_TAC[CTREE_SUB_0]);;

let CTREE_MEM_SEQ0 = prove
 (`!t. ctree_mem t [] <=> ctree_leaf t`,
  REWRITE_TAC[ctree_mem] THEN MATCH_MP_TAC ctree_INDUCT THEN
  REWRITE_TAC[ctree_sub; ctree_leaf] THEN ARITH_TAC);;

let CTREE_MEM_SEL = prove
 (`!t e et. ctree_mem t (CONS e et) <=> ctree_mem (ctree_sel t e) et`,
  REWRITE_TAC[ctree_mem; CTREE_SUB_SEL]);;

let CTREE_MEM_EMPTY = prove
 (`!et. ctree_mem CtreeEmpty et <=> F`,
  REWRITE_TAC[ctree_mem; ctree_sub]);;

let CTREE_MEM_NODE_NIL = prove
 (`!t1 t2 t3. ctree_mem (CtreeNode t1 t2 t3) [] <=> F`,
  REWRITE_TAC[CTREE_MEM_SEQ0; ctree_leaf]);;

let CTREE_MEM_NODE_CONS = prove
 (`(!t1 t2 t3 et. ctree_mem (CtreeNode t1 t2 t3) (CONS Color1 et) <=>
                  ctree_mem t1 et) /\
   (!t1 t2 t3 et. ctree_mem (CtreeNode t1 t2 t3) (CONS Color2 et) <=>
                  ctree_mem t2 et) /\
   (!t1 t2 t3 et. ctree_mem (CtreeNode t1 t2 t3) (CONS Color3 et) <=>
                  ctree_mem t3 et) /\
   (!t1 t2 t3 et. ~(ctree_mem (CtreeNode t1 t2 t3) (CONS Color0 et)))`,
  REWRITE_TAC[CTREE_MEM_SEL; ctree_sel; palette; CTREE_MEM_EMPTY]);;

let CTREE_MEM_LEAF = prove
 (`!lf et. ctree_mem (CtreeLeaf lf) et <=> (et = [])`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ctree_mem; ctree_sub; NOT_CONS_NIL] THEN ARITH_TAC);;

let CTREE_LEAF_OF_PROPER = prove
 (`!n. ctree_proper 0 (ctree_leaf_of n)`,
  REWRITE_TAC[ctree_leaf_of] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITER; ctree_proper]);;

let CTREE_SUB_LEAF_OF = prove
 (`!n et. ctree_sub (ctree_leaf_of n) et = (if et = [] then n else 0)`,
  REWRITE_TAC[ctree_leaf_of] THEN INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[ITER; ctree_sub] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    ASM_CASES_TAC `et:color list = []` THEN ASM_REWRITE_TAC[ADD1]]);;

let CTREE_CONS_SPEC = prove
 (`!t1 t2 t3. ctree_cons t1 t2 t3 =
      (if ctree_empty_node (CtreeNode t1 t2 t3) then CtreeEmpty
       else CtreeNode t1 t2 t3)`,
  REWRITE_TAC[ctree_cons; ctree_empty_node]);;

let CTREE_LEAF_CONS = prove
 (`!t1 t2 t3. ctree_leaf (ctree_cons t1 t2 t3) = F`,
  REWRITE_TAC[ctree_cons] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[ctree_leaf]);;

let CTREE_SEL_CONS = prove
 (`!t1 t2 t3 e. ctree_sel (ctree_cons t1 t2 t3) e =
 ctree_sel (CtreeNode t1 t2 t3) e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CTREE_CONS_SPEC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CTREE_EMPTY_NODE_EQ) THEN
  ASM_REWRITE_TAC[ctree_sel] THEN
  STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
  REWRITE_TAC[palette]);;

let CTREE_CONS_PROPER = prove
 (`!h t1 t2 t3. ctree_proper h t1 /\ ctree_proper h t2 /\ ctree_proper h t3
                ==> ctree_proper (h+1) (ctree_cons t1 t2 t3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CTREE_CONS_SPEC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ctree_proper; ADD1; ADD_SUB] THEN
  ARITH_TAC);;

let CTREE_SUB_CONS = prove
 (`!t1 t2 t3 et. ctree_sub (ctree_cons t1 t2 t3) et =
 ctree_sub (CtreeNode t1 t2 t3) et`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CTREE_CONS_SPEC] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CTREE_EMPTY_NODE_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `et:color list` (cases "list")) THEN
  REWRITE_TAC[ctree_sub; NOT_CONS_NIL; HD; TL; LET_DEF;
              LET_END_DEF; COND_ID]);;

let CTREE_MEM_CONS = prove
 (`!t1 t2 t3 et. ctree_mem (ctree_cons t1 t2 t3) et <=>
 ctree_mem (CtreeNode t1 t2 t3) et`,
  REWRITE_TAC[ctree_mem; CTREE_SUB_CONS]);;

(* ========================================================================= *)
(* ctree_of_ttail, union, and their membership / properness lemmas.          *)
(* ========================================================================= *)

let CTREE_CONS_E_SPEC = prove
 (`!e t. ctree_cons_e e t =
     ctree_cons (if Color1 = e then t else CtreeEmpty)
                (if Color2 = e then t else CtreeEmpty)
                (if Color3 = e then t else CtreeEmpty)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[ctree_cons_e] THEN
  STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
  REWRITE_TAC[palette; ctree_cons0; ctree_cons1; ctree_cons2; ctree_cons3;
              distinctness "color"; ctree_cons; ctree_empty]);;

let CTREE_CONS_E_PROPER = prove
 (`!h e t. ctree_proper h t ==> ctree_proper (h+1) (ctree_cons_e e t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CTREE_CONS_E_SPEC] THEN
  MATCH_MP_TAC CTREE_CONS_PROPER THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[ctree_proper]));;

let CTREE_OF_TTAIL_PROPER = prove
 (`!et. ctree_proper (LENGTH et) (ctree_of_ttail et)`,
  REWRITE_TAC[ctree_of_ttail] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST; LENGTH; ctree_simple_leaf; ctree_proper] THEN
  REWRITE_TAC[GSYM ctree_simple_leaf] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `SUC n = n + 1`] THEN
  MATCH_MP_TAC CTREE_CONS_E_PROPER THEN ASM_REWRITE_TAC[]);;

let CTREE_OF_TTAIL_MEM = prove
 (`!et et'. ~MEM Color0 et
            ==> (ctree_mem (ctree_of_ttail et) et' <=> (et' = et))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ctree_of_ttail; ITLIST] THEN
  REWRITE_TAC[GSYM ctree_of_ttail; ctree_simple_leaf; CTREE_MEM_LEAF; MEM;
              DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CTREE_CONS_E_SPEC; CTREE_MEM_CONS] THEN
  STRUCT_CASES_TAC(ISPEC `et':color list` (cases "list")) THEN
  REWRITE_TAC[CTREE_MEM_SEQ0; ctree_leaf; NOT_CONS_NIL; CTREE_MEM_SEL;
              ctree_sel; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `a0:color` (cases "color")) THEN
  REWRITE_TAC[palette] THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[CTREE_MEM_EMPTY]);;

let CTREE_UNION_NR = prove
 (`!t. ctree_union t CtreeEmpty = t`, REWRITE_TAC[ctree_union]);;

let CTREE_UNION_NL = prove
 (`!t. ctree_union CtreeEmpty t = t`,
  MATCH_MP_TAC ctree_INDUCT THEN REWRITE_TAC[ctree_union; ctree_empty]);;

let CTREE_UNION_PROPER = prove
 (`!h tl tr. ctree_proper h tl /\ ctree_proper h tr
             ==> ctree_proper h (ctree_union tl tr)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `tl:ctree` (cases "ctree")) THEN
  STRUCT_CASES_TAC(ISPEC `tr:ctree` (cases "ctree")) THEN
  REWRITE_TAC[ctree_proper; NOT_SUC; SUC_SUB1; CTREE_UNION_NL; CTREE_UNION_NR;
              ctree_union; ctree_empty; ctree_leaf; ctree_lsub; ctree_msub;
              ctree_rsub; ctree_simple_leaf] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ctree_proper] THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM ADD1] CTREE_CONS_PROPER) THEN
  ASM_SIMP_TAC[]);;

let CTREE_MEM_SIMPLE_LEAF = prove
 (`!et. ctree_mem ctree_simple_leaf et <=> (et = [])`,
  REWRITE_TAC[ctree_simple_leaf; CTREE_MEM_LEAF]);;

let CTREE_MEM_UNION = prove
 (`!h tl tr et. ctree_proper h tl /\ ctree_proper h tr
                ==> (ctree_mem (ctree_union tl tr) et <=>
                     ctree_mem tl et \/ ctree_mem tr et)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `tl:ctree` (cases "ctree")) THEN
  STRUCT_CASES_TAC(ISPEC `tr:ctree` (cases "ctree")) THEN
  REWRITE_TAC[ctree_proper; NOT_SUC; SUC_SUB1; CTREE_UNION_NL; CTREE_UNION_NR;
              ctree_union; ctree_empty; ctree_leaf; ctree_lsub;
              ctree_msub; ctree_rsub;
              CTREE_MEM_EMPTY; CTREE_MEM_SIMPLE_LEAF; CTREE_MEM_LEAF] THEN
  REWRITE_TAC[GSYM ctree_mem; CTREE_MEM_CONS; CTREE_MEM_EMPTY] THEN
  STRIP_TAC THEN DISJ_CASES_THEN2 SUBST1_TAC
   (X_CHOOSE_THEN `c:color` (X_CHOOSE_THEN `l:color list` SUBST1_TAC))
   (ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[CTREE_MEM_SEQ0; ctree_leaf; CTREE_MEM_SEL; ctree_sel] THEN
  STRUCT_CASES_TAC(ISPEC `c:color` (cases "color")) THEN
  ASM_SIMP_TAC[palette; CTREE_MEM_EMPTY]);;

(* ========================================================================= *)
(* Rotations: properness and membership (image under Eperm312 / Eperm231).   *)
(* ========================================================================= *)

(* The two rotations are handled alike.                                      *)

let CTREE_ROT_PROPER_TAC rot =
  INDUCT_TAC THEN MATCH_MP_TAC ctree_INDUCT THEN
  REWRITE_TAC[rot; ctree_proper; NOT_SUC; SUC_SUB1] THEN
  REPEAT STRIP_TAC THEN
  TRY(MATCH_MP_TAC(REWRITE_RULE[GSYM ADD1] CTREE_CONS_PROPER) THEN
      ASM_SIMP_TAC[]) THEN
  ASM_REWRITE_TAC[rot; ctree_proper];;

let CTREE_ROTL_PROPER = prove
 (`!h t. ctree_proper h t ==> ctree_proper h (ctree_rotl t)`,
  CTREE_ROT_PROPER_TAC ctree_rotl);;

let CTREE_ROTR_PROPER = prove
 (`!h t. ctree_proper h t ==> ctree_proper h (ctree_rotr t)`,
  CTREE_ROT_PROPER_TAC ctree_rotr);;

let CTREE_MEM_ROT_TAC rot =
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[permt] THEN
    STRUCT_CASES_TAC(ISPEC `t:ctree` (cases "ctree")) THEN
    REWRITE_TAC[rot; CTREE_MEM_SEQ0; ctree_leaf; CTREE_LEAF_CONS];
    STRUCT_CASES_TAC(ISPEC `t':ctree` (cases "ctree")) THEN
    REWRITE_TAC[rot; permt; CTREE_MEM_SEL; CTREE_MEM_CONS; CTREE_SEL_CONS;
                ctree_sel; CTREE_MEM_EMPTY] THEN
    STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
    ASM_REWRITE_TAC[permc_DEF; palette; CTREE_MEM_EMPTY]];;

let CTREE_MEM_ROTL = prove
 (`!t et. ctree_mem (ctree_rotl t) et = ctree_mem t (permt Eperm312 et)`,
  CTREE_MEM_ROT_TAC ctree_rotl);;

let CTREE_MEM_ROTR = prove
 (`!t et. ctree_mem (ctree_rotr t) et = ctree_mem t (permt Eperm231 et)`,
  CTREE_MEM_ROT_TAC ctree_rotr);;

let CTREE_MEM_C0_SEQ = prove
 (`!u. ctree_mem u [Color0] <=> F`,
  GEN_TAC THEN MATCH_MP_TAC CTREE_MEM_0 THEN REWRITE_TAC[MEM]);;

let CTREE_MEM_CONS_ROT = prove
 (`!t et. ctree_mem (ctree_cons_rot t) et = ctree_mem t (ttail et)`,
  GEN_TAC THEN REWRITE_TAC[ctree_cons_rot; ttail] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[proper_trace; CTREE_MEM_CONS; CTREE_MEM_SEQ0; CTREE_LEAF_CONS];
    ALL_TAC] THEN
  REWRITE_TAC[proper_trace; NOT_CONS_NIL; HD; TL] THEN
  STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
  REWRITE_TAC[distinctness "color"; ctree_leaf; edge_rot_DEF; PERMT_ID;
              CTREE_MEM_CONS; CTREE_MEM_SEL; ctree_sel; palette;
              CTREE_MEM_EMPTY;
              CTREE_MEM_ROTL; CTREE_MEM_ROTR; CTREE_MEM_C0_SEQ]);;

(* ========================================================================= *)
(* Union of rotations (ctree_rotlr).                                         *)
(* ========================================================================= *)

let CTREE_UNION_CONS = prove
 (`!a b c d e f.
     ctree_union (ctree_cons a b c) (ctree_cons d e f) =
     ctree_cons (ctree_union a d) (ctree_union b e) (ctree_union c f)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `ctree_empty a /\ ctree_empty b /\ ctree_empty c` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN
     (SUBST1_TAC o MATCH_MP CTREE_EMPTY_EQ)) THEN
    REWRITE_TAC[ctree_cons; ctree_empty; CTREE_UNION_NL];
    ALL_TAC] THEN
  ASM_CASES_TAC `ctree_empty d /\ ctree_empty e /\ ctree_empty f` THENL
   [FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN
     (SUBST1_TAC o MATCH_MP CTREE_EMPTY_EQ)) THEN
    REWRITE_TAC[ctree_cons; ctree_empty; CTREE_UNION_NR];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ctree_cons] THEN
  REWRITE_TAC[ctree_union; ctree_empty; ctree_lsub; ctree_msub;
              ctree_rsub] THEN
  REWRITE_TAC[ctree_leaf; GSYM ctree_cons]);;

let CTREE_UNION_ROTLR_SPEC = prove
 (`!t u. ctree_union_rotlr t u = ctree_union (ctree_rotl t) (ctree_rotr u)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC ctree_INDUCT THEN
  REPEAT STRIP_TAC THEN STRUCT_CASES_TAC(ISPEC `t:ctree` (cases "ctree")) THEN
  ASM_REWRITE_TAC[ctree_union_rotlr; ctree_rotl; ctree_rotr; ctree_empty;
                  ctree_leaf; ctree_lsub; ctree_msub; ctree_rsub; ctree_union;
                  CTREE_UNION_NL; CTREE_UNION_NR; CTREE_UNION_CONS]);;

let CTREE_ROTLR_SPEC = prove
 (`!t. ctree_rotlr t = ctree_union (ctree_rotl t) (ctree_rotr t)`,
  REWRITE_TAC[ctree_rotlr; CTREE_UNION_ROTLR_SPEC]);;

let CTREE_MEM_ROTLR = prove
 (`!h t et. ctree_proper h t
            ==> (ctree_mem (ctree_rotlr t) et <=>
                 ctree_mem t (permt Eperm312 et) \/
                 ctree_mem t (permt Eperm231 et))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CTREE_ROTLR_SPEC] THEN
  MP_TAC(ISPECL [`h:num`; `ctree_rotl t`; `ctree_rotr t`; `et:color list`
  ] CTREE_MEM_UNION) THEN
  ASM_SIMP_TAC[CTREE_ROTL_PROPER; CTREE_ROTR_PROPER] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CTREE_MEM_ROTL; CTREE_MEM_ROTR]);;

(* ========================================================================= *)
(* Disjointness test: exact interpretation (the 4ct needs one direction).    *)
(* An existential over traces is split by the head of the trace and then by  *)
(* its first colour; the two splitting rules are also used in gtree.ml.      *)
(* ========================================================================= *)

let EXISTS_LIST_CASES = prove
 (`!P. (?l:A list. P l) <=> P [] \/ (?h t. P (CONS h t))`,
  MESON_TAC[list_CASES]);;

let EXISTS_COLOR_CASES = prove
 (`!P. (?c. P c) <=> P Color0 \/ P Color1 \/ P Color2 \/ P Color3`,
  MESON_TAC[cases "color"]);;

let CTREE_MEM_DISJOINT_SPEC = prove
 (`!tl tr. ~ctree_disjoint tl tr <=>
           (?et. ctree_mem tl et /\ ctree_mem tr et)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC ctree_INDUCT THEN
  REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `tl:ctree` (cases "ctree")) THEN
  ONCE_REWRITE_TAC[EXISTS_LIST_CASES] THEN
  ASM_REWRITE_TAC[ctree_disjoint; ctree_empty; ctree_leaf; ctree_lsub;
                  ctree_msub; ctree_rsub; DE_MORGAN_THM; CTREE_MEM_SEQ0;
                  CTREE_MEM_SEL; ctree_sel; palette; EXISTS_COLOR_CASES;
                  CTREE_MEM_EMPTY; CTREE_MEM_LEAF; NOT_CONS_NIL]);;

let CTREE_MEM_DISJOINT = prove
 (`!tl tr et. ctree_disjoint tl tr /\ ctree_mem tr et ==> ctree_mem tl et = F`,
  MESON_TAC[CTREE_MEM_DISJOINT_SPEC]);;
