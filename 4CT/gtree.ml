(* ========================================================================= *)
(* 4CT/gtree.ml                                                              *)
(*                                                                           *)
(* gtree.v: chromogram trees.  A gtree is a 4-way tree storing a set of      *)
(* partial chromograms, the analogue of a ctree for edge traces, without     *)
(* multiplicities; the four subtrees of a node hold the chromograms          *)
(* continuing with Gpush, Gskip, Gpop0 and Gpop1 (in Gonthier's order).  The *)
(* file defines membership (gtree_mem), the match count gtree_sub of a tree  *)
(* against a trace, the empty-node interlock and the pair and partition      *)
(* constructors, and proves the reflection lemmas HAS_MATCHP and             *)
(* MATCH_COUNTP (Coq has_matchP, match_countP) used by the restriction       *)
(* files.                                                                    *)
(* ========================================================================= *)

needs "4CT/chromogram.ml";;
needs "4CT/ctree.ml";;

(* ------------------------------------------------------------------------- *)
(* The datatype: 4-way node, 8 leaf kinds, empty.                            *)
(* ------------------------------------------------------------------------- *)

let gtree_INDUCT,gtree_RECURSION =
  define_type
 "gtree = GtreeNode gtree gtree gtree gtree | GtreeLeaf0 | GtreeLeaf1 | \
  GtreeLeaf2 | GtreeLeaf3 | GtreeLeaf01 | GtreeLeaf12 | GtreeLeaf13 | \
  GtreeLeaf23 | GtreeEmpty";;

let gtree_pair_INDUCT,gtree_pair_RECURSION =
  define_type "gtree_pair = GtreePair gtree gtree";;

(* ------------------------------------------------------------------------- *)
(* Classifiers and the node subtree selector.                                *)
(* ------------------------------------------------------------------------- *)

let gtree_empty = define
 `(gtree_empty GtreeEmpty = T) /\
  (gtree_empty (GtreeNode t0 t1 t2 t3) = F) /\
  (gtree_empty GtreeLeaf0 = F) /\ (gtree_empty GtreeLeaf1 = F) /\
  (gtree_empty GtreeLeaf2 = F) /\ (gtree_empty GtreeLeaf3 = F) /\
  (gtree_empty GtreeLeaf01 = F) /\ (gtree_empty GtreeLeaf12 = F) /\
  (gtree_empty GtreeLeaf13 = F) /\ (gtree_empty GtreeLeaf23 = F)`;;

(* gtree_isleaf t <=> t is one of the 8 leaf constructors.                   *)
let gtree_isleaf = define
 `(gtree_isleaf (GtreeNode t0 t1 t2 t3) = F) /\
  (gtree_isleaf GtreeLeaf0 = T) /\ (gtree_isleaf GtreeLeaf1 = T) /\
  (gtree_isleaf GtreeLeaf2 = T) /\ (gtree_isleaf GtreeLeaf3 = T) /\
  (gtree_isleaf GtreeLeaf01 = T) /\ (gtree_isleaf GtreeLeaf12 = T) /\
  (gtree_isleaf GtreeLeaf13 = T) /\ (gtree_isleaf GtreeLeaf23 = T) /\
  (gtree_isleaf GtreeEmpty = F)`;;

(* gtree_sel t s : subtree of node t under symbol s (off a node -> Empty).   *)
let gtree_sel = define
 `(gtree_sel (GtreeNode t0 t1 t2 t3) s =
      (if s = Gpush then t0 else if s = Gskip then t1
       else if s = Gpop0 then t2 else t3)) /\
  (gtree_sel GtreeLeaf0 s = GtreeEmpty) /\
  (gtree_sel GtreeLeaf1 s = GtreeEmpty) /\
  (gtree_sel GtreeLeaf2 s = GtreeEmpty) /\
  (gtree_sel GtreeLeaf3 s = GtreeEmpty) /\
  (gtree_sel GtreeLeaf01 s = GtreeEmpty) /\
  (gtree_sel GtreeLeaf12 s = GtreeEmpty) /\
  (gtree_sel GtreeLeaf13 s = GtreeEmpty) /\
  (gtree_sel GtreeLeaf23 s = GtreeEmpty) /\
  (gtree_sel GtreeEmpty s = GtreeEmpty)`;;

(* gtree_leaf_mem t s : does leaf-tree t accept the single symbol s?         *)
let gtree_leaf_mem = define
 `(gtree_leaf_mem (GtreeNode t0 t1 t2 t3) s = F) /\
  (gtree_leaf_mem GtreeLeaf0 s = (s = Gpush)) /\
  (gtree_leaf_mem GtreeLeaf1 s = (s = Gskip)) /\
  (gtree_leaf_mem GtreeLeaf2 s = (s = Gpop0)) /\
  (gtree_leaf_mem GtreeLeaf3 s = (s = Gpop1)) /\
  (gtree_leaf_mem GtreeLeaf01 s = (s = Gpush \/ s = Gskip)) /\
  (gtree_leaf_mem GtreeLeaf12 s = (s = Gskip \/ s = Gpop0)) /\
  (gtree_leaf_mem GtreeLeaf13 s = (s = Gskip \/ s = Gpop1)) /\
  (gtree_leaf_mem GtreeLeaf23 s = (s = Gpop0 \/ s = Gpop1)) /\
  (gtree_leaf_mem GtreeEmpty s = F)`;;

(* ------------------------------------------------------------------------- *)
(* gtree_mem t w : t contains the partial chromogram w. Recurse on w: a node *)
(* steps into the s-subtree; a leaf accepts a single matching symbol.        *)
(* Clausal on tree x list like Gonthier; a leaf accepts exactly its          *)
(* one-symbol chromograms (gtree_leaf_mem spells out the same table).        *)
(* ------------------------------------------------------------------------- *)

let gtree_mem = define
 `(gtree_mem t [] = F) /\
  (gtree_mem (GtreeNode t0 t1 t2 t3) (CONS s w) =
     gtree_mem (gtree_sel (GtreeNode t0 t1 t2 t3) s) w) /\
  (gtree_mem GtreeLeaf0 (CONS s w) = (w = [] /\ s = Gpush)) /\
  (gtree_mem GtreeLeaf1 (CONS s w) = (w = [] /\ s = Gskip)) /\
  (gtree_mem GtreeLeaf2 (CONS s w) = (w = [] /\ s = Gpop0)) /\
  (gtree_mem GtreeLeaf3 (CONS s w) = (w = [] /\ s = Gpop1)) /\
  (gtree_mem GtreeLeaf01 (CONS s w) = (w = [] /\ (s = Gpush \/ s = Gskip))) /\
  (gtree_mem GtreeLeaf12 (CONS s w) = (w = [] /\ (s = Gskip \/ s = Gpop0))) /\
  (gtree_mem GtreeLeaf13 (CONS s w) = (w = [] /\ (s = Gskip \/ s = Gpop1))) /\
  (gtree_mem GtreeLeaf23 (CONS s w) = (w = [] /\ (s = Gpop0 \/ s = Gpop1))) /\
  (gtree_mem GtreeEmpty (CONS s w) = F)`;;

(* ------------------------------------------------------------------------- *)
(* Match counting over predicates (spec_ctree = colseq->bool, spec_gtree =   *)
(* chromogram->bool). case_bitstack is the bit_stack case-analysis helper.   *)
(* ------------------------------------------------------------------------- *)

let case_bitstack = define
 `(case_bitstack Bstack0 (v0:A) f0 f1 = v0) /\
  (case_bitstack (Bpush0 bs') v0 f0 f1 = f0 bs') /\
  (case_bitstack (Bpush1 bs') v0 f0 f1 = f1 bs')`;;

(* has_match bs ct w <=> ?et. ct et /\ matchpg bs et w. (curried via _fn.)   *)
let has_match_fn = new_recursive_definition list_RECURSION
 `(has_match_fn [] = (\bs (ct:(color)list->bool). ct [])) /\
  (has_match_fn (CONS s w) =
    (\bs ct.
      if s = Gpush then
        has_match_fn w (Bpush0 bs) (\et. ct (CONS Color2 et)) \/
        has_match_fn w (Bpush1 bs) (\et. ct (CONS Color3 et))
      else if s = Gskip then
        has_match_fn w bs (\et. ct (CONS Color1 et))
      else if s = Gpop0 then
        case_bitstack bs F
          (\bs'. has_match_fn w bs' (\et. ct (CONS Color2 et)))
          (\bs'. has_match_fn w bs' (\et. ct (CONS Color3 et)))
      else
        case_bitstack bs F
          (\bs'. has_match_fn w bs' (\et. ct (CONS Color3 et)))
          (\bs'. has_match_fn w bs' (\et. ct (CONS Color2 et)))))`;;

let has_match = new_definition
 `has_match bs (ct:(color)list->bool) w = has_match_fn w bs ct`;;

(* match_count st bs et : # chromograms w with st w /\ matchpg bs et w.      *)
let match_count_fn = new_recursive_definition list_RECURSION
 `(match_count_fn [] =
  (\(st:(gram_symbol)list->bool) bs. if st [] then 1 else 0)) /\
  (match_count_fn (CONS e et) =
    (\st bs.
      if e = Color0 then 0
      else if e = Color1 then match_count_fn et (\w. st (CONS Gskip w)) bs
      else if e = Color2 then
         match_count_fn et (\w. st (CONS Gpush w)) (Bpush0 bs) +
         case_bitstack bs 0
            (\bs'. match_count_fn et (\w. st (CONS Gpop0 w)) bs')
            (\bs'. match_count_fn et (\w. st (CONS Gpop1 w)) bs')
      else
         match_count_fn et (\w. st (CONS Gpush w)) (Bpush1 bs) +
         case_bitstack bs 0
            (\bs'. match_count_fn et (\w. st (CONS Gpop1 w)) bs')
            (\bs'. match_count_fn et (\w. st (CONS Gpop0 w)) bs')))`;;

let match_count = new_definition
 `match_count (st:(gram_symbol)list->bool) bs et = match_count_fn et st bs`;;

(* gtree_sub t bs et : # partial 'grams w in t with matchpg bs et w.         *)
let gtree_sub = define
 `gtree_sub t bs et = match_count (gtree_mem t) bs et`;;

(* ------------------------------------------------------------------------- *)
(* Empty-node interlock, pairs, partitions, and the cons-pairs constructor.  *)
(* ------------------------------------------------------------------------- *)

let gtree_empty_and = define
 `gtree_empty_and t b = (gtree_empty t /\ b)`;;

let gtree_empty4 = define
 `(gtree_empty4 (GtreeNode t0 t1 t2 t3) =
     gtree_empty_and t0
     (gtree_empty_and t1 (gtree_empty_and t2 (gtree_empty t3)))) /\
  (gtree_empty4 GtreeLeaf0 = F) /\ (gtree_empty4 GtreeLeaf1 = F) /\
  (gtree_empty4 GtreeLeaf2 = F) /\ (gtree_empty4 GtreeLeaf3 = F) /\
  (gtree_empty4 GtreeLeaf01 = F) /\ (gtree_empty4 GtreeLeaf12 = F) /\
  (gtree_empty4 GtreeLeaf13 = F) /\ (gtree_empty4 GtreeLeaf23 = F) /\
  (gtree_empty4 GtreeEmpty = F)`;;

let empty_gtree_pair = define
  `empty_gtree_pair = GtreePair GtreeEmpty GtreeEmpty`;;

let gtree_pair_sub = define
 `gtree_pair_sub (GtreePair t0 t1) b = (if b then t1 else t0)`;;

let sgtree_partition = define
 `sgtree_partition (st:(gram_symbol)list->bool) st' st'' <=>
    (!w. (if st w then (st' w <=> st'' w) else (st' w \/ st'' w)) = F)`;;

let gtree_pair_partition = define
 `gtree_pair_partition t (GtreePair t0 t1) <=>
    sgtree_partition (gtree_mem t) (gtree_mem t0) (gtree_mem t1)`;;

let gtree_cons_pairs = define
 `gtree_cons_pairs t (GtreePair t'0 t''0) (GtreePair t'1 t''1)
                     (GtreePair t'2 t''2) (GtreePair t'3 t''3) =
    (if gtree_empty4 (GtreeNode t'0 t'1 t'2 t'3) then GtreePair t'0 t
     else if gtree_empty4 (GtreeNode t''0 t''1 t''2 t''3) then GtreePair t t''0
     else GtreePair (GtreeNode t'0 t'1 t'2 t'3)
     (GtreeNode t''0 t''1 t''2 t''3))`;;

(* ========================================================================= *)
(* Membership: clean recursion characterisation + empty tree.                *)
(* ========================================================================= *)

let GTREE_MEM_EMPTY = prove
 (`!w. gtree_mem GtreeEmpty w = F`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gtree_mem]);;

let GTREE_MEM = prove
 (`(!t. gtree_mem t [] = F) /\
   (!t s w. gtree_mem t (CONS s w) =
       (if gtree_isleaf t then (w = [] /\ gtree_leaf_mem t s)
        else gtree_mem (gtree_sel t s) w))`,
  REWRITE_TAC[gtree_mem] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:gtree` (cases "gtree")) THEN
  REWRITE_TAC[gtree_isleaf; gtree_sel; gtree_leaf_mem; gtree_mem;
              GTREE_MEM_EMPTY]);;

let MATCH_COUNT = prove
 (`(match_count st bs [] = (if st [] then 1 else 0)) /\
   (match_count st bs (CONS e et) =
      (if e = Color0 then 0
       else if e = Color1 then match_count (\w. st (CONS Gskip w)) bs et
       else if e = Color2 then
          match_count (\w. st (CONS Gpush w)) (Bpush0 bs) et +
          case_bitstack bs 0
             (\bs'. match_count (\w. st (CONS Gpop0 w)) bs' et)
             (\bs'. match_count (\w. st (CONS Gpop1 w)) bs' et)
       else
          match_count (\w. st (CONS Gpush w)) (Bpush1 bs) et +
          case_bitstack bs 0
             (\bs'. match_count (\w. st (CONS Gpop1 w)) bs' et)
             (\bs'. match_count (\w. st (CONS Gpop0 w)) bs' et)))`,
  REWRITE_TAC[match_count; match_count_fn]);;

(* ========================================================================= *)
(* match_count basics: zero, extensionality, additivity over partitions.     *)
(* ========================================================================= *)

let MATCH_COUNT_0 = prove
 (`!et st bs. (!w. ~st w) ==> match_count st bs et = 0`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [ASM_REWRITE_TAC[MATCH_COUNT];
    REWRITE_TAC[MATCH_COUNT] THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
    STRUCT_CASES_TAC(ISPEC `bs:bit_stack` (cases "bit_stack")) THEN
    ASM_SIMP_TAC[case_bitstack; ADD_CLAUSES]]);;

let GTREE_SUB_EMPTY = prove
 (`!bs et. gtree_sub GtreeEmpty bs et = 0`,
  REWRITE_TAC[gtree_sub] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MATCH_COUNT_0 THEN REWRITE_TAC[GTREE_MEM_EMPTY]);;

let MATCH_COUNT_EQ = prove
 (`!et st st' bs. (!w. st w = st' w)
                  ==> match_count st bs et = match_count st' bs et`,
  SIMP_TAC[GSYM FUN_EQ_THM]);;

let SGTREE_PARTITION_SUB = prove
 (`!st st' st'' s. sgtree_partition st st' st''
      ==> sgtree_partition (\w. st (CONS s w)) (\w. st' (CONS s w))
      (\w. st'' (CONS s w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sgtree_partition] THEN DISCH_TAC THEN
  GEN_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CONS (s:gram_symbol) w`) THEN
  REWRITE_TAC[]);;

let MATCH_COUNT_PARTITION = prove
 (`!et st st' st'' bs. sgtree_partition st st' st''
      ==> match_count st bs et =
      match_count st' bs et + match_count st'' bs et`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [POP_ASSUM(MP_TAC o REWRITE_RULE[sgtree_partition]) THEN
    DISCH_THEN(MP_TAC o SPEC `[]:gram_symbol list`) THEN
    REWRITE_TAC[MATCH_COUNT] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ARITH_TAC;
    REWRITE_TAC[MATCH_COUNT] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    STRUCT_CASES_TAC(ISPEC `bs:bit_stack` (cases "bit_stack")) THEN
    REWRITE_TAC[case_bitstack; ADD_CLAUSES] THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SGTREE_PARTITION_SUB] THEN
    NO_TAC) THEN
    ONCE_REWRITE_TAC[ARITH_RULE `(a + b) + (c + d) = (a + c) + (b + d)`] THEN
    BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SGTREE_PARTITION_SUB]]);;

(* ========================================================================= *)
(* has_match / match_count correctness (Coq has_matchP, match_countP): one   *)
(* induction each, splitting the existential over the head of the list and   *)
(* then over the head colour or symbol (EXISTS_LIST_CASES and                *)
(* EXISTS_COLOR_CASES of ctree.ml), which leaves matchpg's clause table.     *)
(* ========================================================================= *)

let EXISTS_GRAM_CASES = prove
 (`!P. (?s. P s) <=> P Gpush \/ P Gskip \/ P Gpop0 \/ P Gpop1`,
  MESON_TAC[cases "gram_symbol"]);;

let HAS_MATCHP = prove
 (`!w bs ct. has_match bs ct w <=> (?et. ct et /\ matchpg bs et w)`,
  REWRITE_TAC[has_match] THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [EXISTS_LIST_CASES] THEN
  ASM_REWRITE_TAC[has_match_fn; matchpg; EXISTS_COLOR_CASES] THEN
  STRUCT_CASES_TAC(ISPEC `h:gram_symbol` (cases "gram_symbol")) THEN
  STRUCT_CASES_TAC(ISPEC `bs:bit_stack` (cases "bit_stack")) THEN
  REWRITE_TAC[case_bitstack; distinctness "gram_symbol"; distinctness "color";
              distinctness "bit_stack"; injectivity "bit_stack";
              UNWIND_THM1]);;

let MATCH_COUNTP = prove
 (`!et st bs. ~(match_count st bs et = 0) <=> (?w. st w /\ matchpg bs et w)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [EXISTS_LIST_CASES] THEN
  REWRITE_TAC[MATCH_COUNT; matchpg; EXISTS_GRAM_CASES] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
  STRUCT_CASES_TAC(ISPEC `bs:bit_stack` (cases "bit_stack")) THEN
  ASM_REWRITE_TAC[case_bitstack; ADD_EQ_0; DE_MORGAN_THM;
                  distinctness "gram_symbol"; distinctness "color";
                  distinctness "bit_stack"; injectivity "bit_stack";
                  UNWIND_THM1]);;

let GTREE_SUB_EQ_0 = prove
 (`!gt bs et. gtree_sub gt bs et = 0 <=>
              !w. gtree_mem gt w ==> ~(matchpg bs et w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gtree_sub] THEN
  ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[MATCH_COUNTP; NOT_FORALL_THM; NOT_IMP]);;

(* ========================================================================= *)
(* Empty4, partitions, and cons-pairs correctness.                           *)
(* ========================================================================= *)

let GTREE_EMPTY_IFF = prove
 (`!t. gtree_empty t <=> (t = GtreeEmpty)`,
  MATCH_MP_TAC gtree_INDUCT THEN
  REWRITE_TAC[gtree_empty; distinctness "gtree"]);;

(* gtree_empty4 (GtreeNode ...) unfolds via gtree_empty4 and gtree_empty_and *)
(* to a conjunction of gtree_empty tests, and GTREE_EMPTY_IFF turns each     *)
(* into ti = GtreeEmpty (a four-fold case split over the ten constructors    *)
(* would cost 10000 subgoals).  gtree_empty_and is its own specification     *)
(* (Coq gtree_empty_and_spec).                                               *)
let GTREE_EMPTY4P = prove
 (`!t0 t1 t2 t3. gtree_empty4 (GtreeNode t0 t1 t2 t3) <=>
      t0 = GtreeEmpty /\ t1 = GtreeEmpty /\ t2 = GtreeEmpty /\
      t3 = GtreeEmpty`,
  REWRITE_TAC[gtree_empty4; gtree_empty_and; GTREE_EMPTY_IFF]);;

let SGTREE_PARTITION_MEMEMPTY = prove
 (`!t. sgtree_partition (gtree_mem t) (gtree_mem GtreeEmpty) (gtree_mem t) /\
       sgtree_partition (gtree_mem t) (gtree_mem t) (gtree_mem GtreeEmpty)`,
  GEN_TAC THEN REWRITE_TAC[sgtree_partition; GTREE_MEM_EMPTY] THEN
  GEN_TAC THEN BOOL_CASES_TAC `gtree_mem t w` THEN REWRITE_TAC[]);;

let SGTREE_PARTITION_NODE = prove
 (`!a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3.
     sgtree_partition (gtree_mem a0) (gtree_mem b0) (gtree_mem c0) /\
     sgtree_partition (gtree_mem a1) (gtree_mem b1) (gtree_mem c1) /\
     sgtree_partition (gtree_mem a2) (gtree_mem b2) (gtree_mem c2) /\
     sgtree_partition (gtree_mem a3) (gtree_mem b3) (gtree_mem c3)
     ==> sgtree_partition (gtree_mem (GtreeNode a0 a1 a2 a3))
                          (gtree_mem (GtreeNode b0 b1 b2 b3))
                          (gtree_mem (GtreeNode c0 c1 c2 c3))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sgtree_partition] THEN STRIP_TAC THEN
  X_GEN_TAC `w:gram_symbol list` THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[GTREE_MEM; gtree_isleaf; gtree_sel] THEN
  STRUCT_CASES_TAC(ISPEC `h:gram_symbol` (cases "gram_symbol")) THEN
  REWRITE_TAC[distinctness "gram_symbol"] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `t:gram_symbol list`)) THEN
  MESON_TAC[]);;

let GTREE_CONS_PAIRS_PARTITION = prove
 (`!t0 t1 t2 t3 pt0 pt1 pt2 pt3.
     gtree_pair_partition t0 pt0 /\ gtree_pair_partition t1 pt1 /\
     gtree_pair_partition t2 pt2 /\ gtree_pair_partition t3 pt3
     ==> gtree_pair_partition (GtreeNode t0 t1 t2 t3)
           (gtree_cons_pairs (GtreeNode t0 t1 t2 t3) pt0 pt1 pt2 pt3)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC(ISPEC v (cases "gtree_pair")))
    [`pt0:gtree_pair`; `pt1:gtree_pair`; `pt2:gtree_pair`;
     `pt3:gtree_pair`] THEN
  REWRITE_TAC[gtree_pair_partition; gtree_cons_pairs] THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THENL
          [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[GTREE_EMPTY4P]);
           ALL_TAC]) THEN
  ASM_REWRITE_TAC[gtree_pair_partition; SGTREE_PARTITION_MEMEMPTY] THEN
  MATCH_MP_TAC SGTREE_PARTITION_NODE THEN ASM_REWRITE_TAC[]);;

let GTREE_MEM0_CONS_PAIRS = prove
 (`!t0 t1 t2 t3 pt0 pt1 pt2 pt3.
     gtree_pair_partition t0 pt0 /\ gtree_pair_partition t1 pt1 /\
     gtree_pair_partition t2 pt2 /\ gtree_pair_partition t3 pt3
     ==> !w. gtree_mem (gtree_pair_sub
                (gtree_cons_pairs (GtreeNode t0 t1 t2 t3) pt0 pt1 pt2 pt3) F) w
                =
             gtree_mem (GtreeNode (gtree_pair_sub pt0 F) (gtree_pair_sub pt1 F)
                                  (gtree_pair_sub pt2 F)
                                  (gtree_pair_sub pt3 F)) w`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC(ISPEC v (cases "gtree_pair")))
    [`pt0:gtree_pair`; `pt1:gtree_pair`; `pt2:gtree_pair`;
     `pt3:gtree_pair`] THEN
  REWRITE_TAC[gtree_pair_partition; gtree_cons_pairs; gtree_pair_sub] THEN
  STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THENL
          [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[GTREE_EMPTY4P]);
           ALL_TAC]) THEN
  ASM_REWRITE_TAC[gtree_pair_sub] THEN X_GEN_TAC `w:gram_symbol list` THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[GTREE_MEM; gtree_isleaf; gtree_sel] THEN
  STRUCT_CASES_TAC(ISPEC `h:gram_symbol` (cases "gram_symbol")) THEN
  REWRITE_TAC[distinctness "gram_symbol"; COND_ID; GTREE_MEM_EMPTY] THEN
  ASM_MESON_TAC[sgtree_partition; GTREE_MEM_EMPTY]);;
