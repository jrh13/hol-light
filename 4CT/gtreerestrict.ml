(* ========================================================================= *)
(* 4CT/gtreerestrict.ml                                                      *)
(*                                                                           *)
(* gtreerestrict.v: restricting a chromogram tree.  A gtree_restriction is a *)
(* list of (bit stack, ctree) pairs standing for a set of matches;           *)
(* gtree_restrict t r splits the gtree t into the pair of the chromograms    *)
(* matched by r and the others, using the 24 static leaf pairs.  The main    *)
(* theorem GTREE_MEM0_RESTRICT (Coq gtree_mem0_restrict) says the first      *)
(* component collects exactly the chromograms of t matched by r.             *)
(* ========================================================================= *)

needs "4CT/ctree.ml";;
needs "4CT/gtree.ml";;
needs "4CT/ctreerestrict.ml";;

(* ------------------------------------------------------------------------- *)
(* gtree_restriction: a list of (bit_stack, ctree) match-pairs.              *)
(* ------------------------------------------------------------------------- *)

let gtree_restriction_INDUCT,gtree_restriction_RECURSION =
  define_type
    "gtree_restriction = GtrNil | GtrCons bit_stack ctree gtree_restriction";;

let gtr_mem = define
 `(gtr_mem GtrNil w = F) /\
  (gtr_mem (GtrCons bs t r') w =
  (has_match bs (ctree_mem t) w \/ gtr_mem r' w))`;;

let gtr_cons = define
 `gtr_cons bs t r = (if ctree_empty t then r else GtrCons bs t r)`;;

let gtr_isnil = define
 `(gtr_isnil GtrNil = T) /\ (gtr_isnil (GtrCons bs t r) = F)`;;

(* cons_pop bs t t' r' : the pop-branch cons used in gtr_split.              *)
let cons_pop = define
 `(cons_pop Bstack0 t t' r' = r') /\
  (cons_pop (Bpush0 bs') t t' r' = gtr_cons bs' t r') /\
  (cons_pop (Bpush1 bs') t t' r' = gtr_cons bs' t' r')`;;

(* ------------------------------------------------------------------------- *)
(* gtr_split (CPS): split a gtree_restriction into 4 sub-restrictions, one   *)
(* per gram symbol (Gpush, Gskip, Gpop0, Gpop1), then call the continuation. *)
(* Curried via gtr_split_fn (recursion on r); node case = Gonthier's uniform *)
(* gtr_cons form (gtr_split_some), leaf/empty ctree entries skip.            *)
(* ------------------------------------------------------------------------- *)

let gtr_split_fn = new_recursive_definition gtree_restriction_RECURSION
 `(gtr_split_fn GtrNil =
      (\(continue:gtree_restriction->gtree_restriction->gtree_restriction
         ->gtree_restriction->A)
        r0 r1 r2 r3. continue r0 r1 r2 r3)) /\
  (gtr_split_fn (GtrCons bs t r) =
      (\continue r0 r1 r2 r3.
         case_ctree_node t
           (\t1 t2 t3.
              gtr_split_fn r continue
                (gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 r0))
                (gtr_cons bs t1 r1)
                (cons_pop bs t2 t3 r2)
                (cons_pop bs t3 t2 r3))
           (gtr_split_fn r continue r0 r1 r2 r3)))`;;

let gtr_split = new_definition
 `gtr_split continue r0 r1 r2 r3 r = gtr_split_fn r continue r0 r1 r2 r3`;;

(* gsplit r s : the s-component of the split (s in Gpush/Gskip/Gpop0/Gpop1). *)
let gsplit = define
 `gsplit r s = gtr_split
    (\g0 g1 g2 g3. if s = Gpush then g0 else if s = Gskip then g1
                  else if s = Gpop0 then g2 else g3)
    GtrNil GtrNil GtrNil GtrNil r`;;

(* gtr_match[0123] r : r contains the singleton [Gpush/Gskip/Gpop0/Gpop1].   *)
let gtr_match0 = new_recursive_definition gtree_restriction_RECURSION
 `(gtr_match0 GtrNil = F) /\
  (gtr_match0 (GtrCons bs t r') =
     case_ctree_node t
       (\t1 t2 t3. ctree_leaf t2 \/ ctree_leaf t3 \/ gtr_match0 r')
       (gtr_match0 r'))`;;

let gtr_match1 = new_recursive_definition gtree_restriction_RECURSION
 `(gtr_match1 GtrNil = F) /\
  (gtr_match1 (GtrCons bs t r') =
     case_ctree_node t (\t1 t2 t3. ctree_leaf t1 \/ gtr_match1 r')
     (gtr_match1 r'))`;;

let gtr_match2 = new_recursive_definition gtree_restriction_RECURSION
 `(gtr_match2 GtrNil = F) /\
  (gtr_match2 (GtrCons bs t r') =
     case_ctree_node t
       (\t1 t2 t3. (case_bitstack bs F (\bs'. ctree_leaf t2)
                    (\bs'. ctree_leaf t3)) \/ gtr_match2 r')
       (gtr_match2 r'))`;;

let gtr_match3 = new_recursive_definition gtree_restriction_RECURSION
 `(gtr_match3 GtrNil = F) /\
  (gtr_match3 (GtrCons bs t r') =
     case_ctree_node t
       (\t1 t2 t3. (case_bitstack bs F (\bs'. ctree_leaf t3)
                    (\bs'. ctree_leaf t2)) \/ gtr_match3 r')
       (gtr_match3 r'))`;;

(* ------------------------------------------------------------------------- *)
(* The 24 statically-defined gtree_pairs of leaves.                          *)
(* ------------------------------------------------------------------------- *)

let gtp_0_e = define `gtp_0_e = GtreePair GtreeLeaf0 GtreeEmpty`;;
let gtp_1_e = define `gtp_1_e = GtreePair GtreeLeaf1 GtreeEmpty`;;
let gtp_2_e = define `gtp_2_e = GtreePair GtreeLeaf2 GtreeEmpty`;;
let gtp_3_e = define `gtp_3_e = GtreePair GtreeLeaf3 GtreeEmpty`;;
let gtp_01_e = define `gtp_01_e = GtreePair GtreeLeaf01 GtreeEmpty`;;
let gtp_12_e = define `gtp_12_e = GtreePair GtreeLeaf12 GtreeEmpty`;;
let gtp_13_e = define `gtp_13_e = GtreePair GtreeLeaf13 GtreeEmpty`;;
let gtp_23_e = define `gtp_23_e = GtreePair GtreeLeaf23 GtreeEmpty`;;
let gtp_e_0 = define `gtp_e_0 = GtreePair GtreeEmpty GtreeLeaf0`;;
let gtp_e_1 = define `gtp_e_1 = GtreePair GtreeEmpty GtreeLeaf1`;;
let gtp_e_2 = define `gtp_e_2 = GtreePair GtreeEmpty GtreeLeaf2`;;
let gtp_e_3 = define `gtp_e_3 = GtreePair GtreeEmpty GtreeLeaf3`;;
let gtp_e_01 = define `gtp_e_01 = GtreePair GtreeEmpty GtreeLeaf01`;;
let gtp_e_12 = define `gtp_e_12 = GtreePair GtreeEmpty GtreeLeaf12`;;
let gtp_e_13 = define `gtp_e_13 = GtreePair GtreeEmpty GtreeLeaf13`;;
let gtp_e_23 = define `gtp_e_23 = GtreePair GtreeEmpty GtreeLeaf23`;;
let gtp_0_1 = define `gtp_0_1 = GtreePair GtreeLeaf0 GtreeLeaf1`;;
let gtp_1_0 = define `gtp_1_0 = GtreePair GtreeLeaf1 GtreeLeaf0`;;
let gtp_1_2 = define `gtp_1_2 = GtreePair GtreeLeaf1 GtreeLeaf2`;;
let gtp_2_1 = define `gtp_2_1 = GtreePair GtreeLeaf2 GtreeLeaf1`;;
let gtp_1_3 = define `gtp_1_3 = GtreePair GtreeLeaf1 GtreeLeaf3`;;
let gtp_3_1 = define `gtp_3_1 = GtreePair GtreeLeaf3 GtreeLeaf1`;;
let gtp_2_3 = define `gtp_2_3 = GtreePair GtreeLeaf2 GtreeLeaf3`;;
let gtp_3_2 = define `gtp_3_2 = GtreePair GtreeLeaf3 GtreeLeaf2`;;

(* ------------------------------------------------------------------------- *)
(* gtree_restrict t r : the gtree_pair partition of t; first (false)         *)
(* component is t with the matches in r removed. (GtrNil -> nothing removed  *)
(* so first = Empty, second = t.)                                            *)
(* ------------------------------------------------------------------------- *)

let gtree_restrict = new_recursive_definition gtree_RECURSION
 `(gtree_restrict (GtreeNode t0 t1 t2 t3) r =
     (if gtr_isnil r then GtreePair GtreeEmpty (GtreeNode t0 t1 t2 t3)
      else gtr_split
             (\r0 r1 r2 r3. gtree_cons_pairs (GtreeNode t0 t1 t2 t3)
                (gtree_restrict t0 r0) (gtree_restrict t1 r1)
                (gtree_restrict t2 r2) (gtree_restrict t3 r3))
             GtrNil GtrNil GtrNil GtrNil r)) /\
  (gtree_restrict GtreeLeaf0 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf0
      else if gtr_match0 r then gtp_0_e else gtp_e_0)) /\
  (gtree_restrict GtreeLeaf1 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf1
      else if gtr_match1 r then gtp_1_e else gtp_e_1)) /\
  (gtree_restrict GtreeLeaf2 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf2
      else if gtr_match2 r then gtp_2_e else gtp_e_2)) /\
  (gtree_restrict GtreeLeaf3 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf3
      else if gtr_match3 r then gtp_3_e else gtp_e_3)) /\
  (gtree_restrict GtreeLeaf01 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf01
      else if gtr_match0 r then (if gtr_match1 r then gtp_01_e else gtp_0_1)
      else if gtr_match1 r then gtp_1_0 else gtp_e_01)) /\
  (gtree_restrict GtreeLeaf12 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf12
      else if gtr_match1 r then (if gtr_match2 r then gtp_12_e else gtp_1_2)
      else if gtr_match2 r then gtp_2_1 else gtp_e_12)) /\
  (gtree_restrict GtreeLeaf13 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf13
      else if gtr_match1 r then (if gtr_match3 r then gtp_13_e else gtp_1_3)
      else if gtr_match3 r then gtp_3_1 else gtp_e_13)) /\
  (gtree_restrict GtreeLeaf23 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf23
      else if gtr_match2 r then (if gtr_match3 r then gtp_23_e else gtp_2_3)
      else if gtr_match3 r then gtp_3_2 else gtp_e_23)) /\
  (gtree_restrict GtreeEmpty r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeEmpty
     else empty_gtree_pair))`;;

(* ========================================================================= *)
(* Split lemmas + match-singleton characterisations.                         *)
(* ========================================================================= *)

let GTR_SPLIT = prove
 (`(gtr_split continue r0 r1 r2 r3 GtrNil = continue r0 r1 r2 r3) /\
   (gtr_split continue r0 r1 r2 r3 (GtrCons bs t r) =
      case_ctree_node t
        (\t1 t2 t3.
           gtr_split continue
             (gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 r0))
             (gtr_cons bs t1 r1) (cons_pop bs t2 t3 r2)
             (cons_pop bs t3 t2 r3) r)
        (gtr_split continue r0 r1 r2 r3 r))`,
  REWRITE_TAC[gtr_split; gtr_split_fn]);;

let GTR_MEM_CONS = prove
 (`!bs t r w. gtr_mem (gtr_cons bs t r) w =
              (has_match bs (ctree_mem t) w \/ gtr_mem r w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gtr_cons] THEN COND_CASES_TAC THEN
  REWRITE_TAC[gtr_mem] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP CTREE_EMPTY_EQ) THEN
  REWRITE_TAC[HAS_MATCHP; CTREE_MEM_EMPTY] THEN MESON_TAC[]);;

let GTREE_PARTITION_RIGHT = prove
 (`!t. gtree_pair_partition t (GtreePair GtreeEmpty t)`,
  REWRITE_TAC[gtree_pair_partition; SGTREE_PARTITION_MEMEMPTY]);;

let HAS_MATCH_SING = prove
 (`(has_match bs ct [Gpush] = (ct [Color2] \/ ct [Color3])) /\
   (has_match bs ct [Gskip] = ct [Color1]) /\
   (has_match bs ct [Gpop0] =
   case_bitstack bs F (\bs'. ct [Color2]) (\bs'. ct [Color3])) /\
   (has_match bs ct [Gpop1] =
   case_bitstack bs F (\bs'. ct [Color3]) (\bs'. ct [Color2]))`,
  REWRITE_TAC[has_match; has_match_fn] THEN BETA_TAC THEN
  REWRITE_TAC[distinctness "gram_symbol"]);;

(* The four singleton-match tests, by one induction on r.                    *)
let GTR_MATCHE_TAC def =
  MATCH_MP_TAC gtree_restriction_INDUCT THEN
  REWRITE_TAC[def; gtr_mem] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a1:ctree` (cases "ctree")) THEN
  STRUCT_CASES_TAC(ISPEC `a0:bit_stack` (cases "bit_stack")) THEN
  ASM_REWRITE_TAC[case_ctree_node; HAS_MATCH_SING; CTREE_MEM_NODE_CONS;
                  CTREE_MEM_SEQ0; CTREE_MEM_LEAF; ctree_leaf; NOT_CONS_NIL;
                  case_bitstack] THEN
  REWRITE_TAC[ctree_mem; ctree_sub] THEN CONV_TAC TAUT;;

let GTR_MATCH0E = prove
 (`!r. gtr_match0 r = gtr_mem r [Gpush]`,
  GTR_MATCHE_TAC gtr_match0);;

let GTR_MATCH1E = prove
 (`!r. gtr_match1 r = gtr_mem r [Gskip]`,
  GTR_MATCHE_TAC gtr_match1);;

let GTR_MATCH2E = prove
 (`!r. gtr_match2 r = gtr_mem r [Gpop0]`,
  GTR_MATCHE_TAC gtr_match2);;

let GTR_MATCH3E = prove
 (`!r. gtr_match3 r = gtr_mem r [Gpop1]`,
  GTR_MATCHE_TAC gtr_match3);;

(* ========================================================================= *)
(* Split accumulator factorisation and the gsplit reduction of gtr_split.    *)
(* ========================================================================= *)

(* gtr_split with any continuation = continuation applied to the 4 projected *)
(* splits (gtr_split_acc in Gonthier).                                       *)
let GTR_SPLIT_ACC = prove
 (`!r rk a0 a1 a2 a3.
     gtr_split rk a0 a1 a2 a3 r =
     rk (gtr_split (\g0 g1 g2 g3. g0) a0 a1 a2 a3 r)
        (gtr_split (\g0 g1 g2 g3. g1) a0 a1 a2 a3 r)
        (gtr_split (\g0 g1 g2 g3. g2) a0 a1 a2 a3 r)
        (gtr_split (\g0 g1 g2 g3. g3) a0 a1 a2 a3 r)`,
  MATCH_MP_TAC gtree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[GTR_SPLIT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a1:ctree` (cases "ctree")) THEN
  REWRITE_TAC[GTR_SPLIT; case_ctree_node] THEN
  FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN REWRITE_TAC[]);;

(* gtr_split from the empty accumulators = continuation on the 4 gsplits.    *)
let GTR_SPLIT_EQ = prove
 (`!rk r. gtr_split rk GtrNil GtrNil GtrNil GtrNil r =
          rk (gsplit r Gpush) (gsplit r Gskip) (gsplit r Gpop0)
          (gsplit r Gpop1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GTR_SPLIT_ACC] THEN
  REWRITE_TAC[gsplit; distinctness "gram_symbol"]);;

(* ========================================================================= *)
(* has_match: cons unfolding and vanishing on leaf/empty ctrees.             *)
(* ========================================================================= *)

let HAS_MATCH_CONS = prove
 (`has_match bs ct (CONS s w) =
     (if s = Gpush then
        has_match (Bpush0 bs) (\et. ct (CONS Color2 et)) w \/
        has_match (Bpush1 bs) (\et. ct (CONS Color3 et)) w
      else if s = Gskip then
        has_match bs (\et. ct (CONS Color1 et)) w
      else if s = Gpop0 then
        case_bitstack bs F
          (\bs'. has_match bs' (\et. ct (CONS Color2 et)) w)
          (\bs'. has_match bs' (\et. ct (CONS Color3 et)) w)
      else
        case_bitstack bs F
          (\bs'. has_match bs' (\et. ct (CONS Color3 et)) w)
          (\bs'. has_match bs' (\et. ct (CONS Color2 et)) w))`,
  REWRITE_TAC[has_match; has_match_fn]);;

let HAS_MATCH_EMPTY_CT = prove
 (`!bs w. has_match bs (ctree_mem CtreeEmpty) w = F`,
  REWRITE_TAC[HAS_MATCHP; CTREE_MEM_EMPTY]);;

let HAS_MATCH_LEAF_CONS = prove
 (`!bs a s w. has_match bs (ctree_mem (CtreeLeaf a)) (CONS s w) = F`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_MATCHP; CTREE_MEM_LEAF; UNWIND_THM2; matchpg]);;

(* ------------------------------------------------------------------------- *)
(* Key: membership of a split component = membership of the accumulator or a *)
(* one-step-deeper membership of r. (gtr_mem_split_acc.)                     *)
(* ------------------------------------------------------------------------- *)

let GTR_MEM_SPLIT_ACC = prove
 (`!r s a0 a1 a2 a3 w.
     gtr_mem (gtr_split
        (\g0 g1 g2 g3. if s = Gpush then g0 else if s = Gskip then g1
                      else if s = Gpop0 then g2 else g3) a0 a1 a2 a3 r) w
     <=> gtr_mem (if s = Gpush then a0 else if s = Gskip then a1
                 else if s = Gpop0 then a2 else a3) w \/ gtr_mem r (CONS s w)`,
  MATCH_MP_TAC gtree_restriction_INDUCT THEN
  REWRITE_TAC[GTR_SPLIT; gtr_mem] THEN REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a1:ctree` (cases "ctree")) THEN
  ASM_REWRITE_TAC[case_ctree_node] THEN
  STRUCT_CASES_TAC(ISPEC `s:gram_symbol` (cases "gram_symbol")) THEN
  STRUCT_CASES_TAC(ISPEC `a0:bit_stack` (cases "bit_stack")) THEN
  REWRITE_TAC[gtr_mem; GTR_MEM_CONS; HAS_MATCH_CONS; CTREE_MEM_NODE_CONS;
              ETA_AX; cons_pop; case_bitstack; distinctness "gram_symbol";
              HAS_MATCH_LEAF_CONS; HAS_MATCH_EMPTY_CT] THEN
  CONV_TAC TAUT);;

(* gtr_mem one step deeper = gtr_mem of the s-projected split.               *)
let GTR_MEM_GSPLIT = prove
 (`!r s w. gtr_mem r (CONS s w) = gtr_mem (gsplit r s) w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gsplit] THEN
  MP_TAC(ISPECL [`r:gtree_restriction`; `s:gram_symbol`;
                 `GtrNil`;`GtrNil`;`GtrNil`;`GtrNil`;`w:gram_symbol list`]
                GTR_MEM_SPLIT_ACC) THEN
  REWRITE_TAC[COND_ID; gtr_mem] THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* gtree_restrict is a partition, and its false (deleted) component collects *)
(* exactly the chromograms of t that r matches.                              *)
(* ========================================================================= *)

(* All 24 leaf gtree_pairs (+ the empty pair) are partitions of their leaf.  *)
let LEAF_PARTITIONS = prove
 (`gtree_pair_partition GtreeLeaf0 gtp_0_e /\
   gtree_pair_partition GtreeLeaf0 gtp_e_0 /\
   gtree_pair_partition GtreeLeaf1 gtp_1_e /\
   gtree_pair_partition GtreeLeaf1 gtp_e_1 /\
   gtree_pair_partition GtreeLeaf2 gtp_2_e /\
   gtree_pair_partition GtreeLeaf2 gtp_e_2 /\
   gtree_pair_partition GtreeLeaf3 gtp_3_e /\
   gtree_pair_partition GtreeLeaf3 gtp_e_3 /\
   gtree_pair_partition GtreeLeaf01 gtp_01_e /\
   gtree_pair_partition GtreeLeaf01 gtp_0_1 /\
   gtree_pair_partition GtreeLeaf01 gtp_1_0 /\
   gtree_pair_partition GtreeLeaf01 gtp_e_01 /\
   gtree_pair_partition GtreeLeaf12 gtp_12_e /\
   gtree_pair_partition GtreeLeaf12 gtp_1_2 /\
   gtree_pair_partition GtreeLeaf12 gtp_2_1 /\
   gtree_pair_partition GtreeLeaf12 gtp_e_12 /\
   gtree_pair_partition GtreeLeaf13 gtp_13_e /\
   gtree_pair_partition GtreeLeaf13 gtp_1_3 /\
   gtree_pair_partition GtreeLeaf13 gtp_3_1 /\
   gtree_pair_partition GtreeLeaf13 gtp_e_13 /\
   gtree_pair_partition GtreeLeaf23 gtp_23_e /\
   gtree_pair_partition GtreeLeaf23 gtp_2_3 /\
   gtree_pair_partition GtreeLeaf23 gtp_3_2 /\
   gtree_pair_partition GtreeLeaf23 gtp_e_23 /\
   gtree_pair_partition GtreeEmpty empty_gtree_pair`,
  REWRITE_TAC[gtp_0_e; gtp_1_e; gtp_2_e; gtp_3_e; gtp_01_e; gtp_12_e;
              gtp_13_e; gtp_23_e;
              gtp_e_0; gtp_e_1; gtp_e_2; gtp_e_3; gtp_e_01; gtp_e_12;
              gtp_e_13; gtp_e_23;
              gtp_0_1; gtp_1_0; gtp_1_2; gtp_2_1; gtp_1_3; gtp_3_1;
              gtp_2_3; gtp_3_2;
              empty_gtree_pair] THEN
  REWRITE_TAC[gtree_pair_partition; sgtree_partition] THEN REPEAT CONJ_TAC THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` (cases "list")) THEN
  REWRITE_TAC[GTREE_MEM; gtree_isleaf; gtree_leaf_mem; GTREE_MEM_EMPTY] THEN
  TRY(STRUCT_CASES_TAC(ISPEC `a0:gram_symbol` (cases "gram_symbol"))) THEN
  REWRITE_TAC[distinctness "gram_symbol"] THEN CONV_TAC TAUT);;

let GTREE_RESTRICT_PARTITION = prove
 (`!t r. gtree_pair_partition t (gtree_restrict t r)`,
  MATCH_MP_TAC gtree_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[gtree_restrict] THEN
  ASM_CASES_TAC `gtr_isnil r` THEN ASM_REWRITE_TAC[GTREE_PARTITION_RIGHT] THEN
  TRY(REWRITE_TAC[GTR_SPLIT_EQ] THEN
      MATCH_MP_TAC GTREE_CONS_PAIRS_PARTITION THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  REWRITE_TAC[LEAF_PARTITIONS]);;

(* gtr_isnil characterisation, used to discharge the GtrNil membership case. *)
let GTR_ISNIL_EQ = prove
 (`!r. gtr_isnil r <=> r = GtrNil`,
  MATCH_MP_TAC gtree_restriction_INDUCT THEN
  REWRITE_TAC[gtr_isnil; distinctness "gtree_restriction"]);;

let GTR_MEM_NIL = prove
 (`!w. gtr_mem GtrNil w <=> F`, REWRITE_TAC[gtr_mem]);;

(* The node step of gtree_mem0_restrict, factored out so the main induction  *)
(* can dispatch it uniformly.                                                *)
let NODE_STEP = prove
 (`(!r w. gtree_mem (gtree_pair_sub (gtree_restrict t0 r) F) w <=>
          gtree_mem t0 w /\ gtr_mem r w) /\
   (!r w. gtree_mem (gtree_pair_sub (gtree_restrict t1 r) F) w <=>
          gtree_mem t1 w /\ gtr_mem r w) /\
   (!r w. gtree_mem (gtree_pair_sub (gtree_restrict t2 r) F) w <=>
          gtree_mem t2 w /\ gtr_mem r w) /\
   (!r w. gtree_mem (gtree_pair_sub (gtree_restrict t3 r) F) w <=>
          gtree_mem t3 w /\ gtr_mem r w)
   ==> (!r w. gtree_mem (gtree_pair_sub
                            (gtree_restrict (GtreeNode t0 t1 t2 t3) r) F) w <=>
              gtree_mem (GtreeNode t0 t1 t2 t3) w /\ gtr_mem r w)`,
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[gtree_restrict] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[gtree_pair_sub; GTREE_MEM_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GTR_ISNIL_EQ]) THEN
    ASM_REWRITE_TAC[GTR_MEM_NIL];
    ALL_TAC] THEN
  REWRITE_TAC[GTR_SPLIT_EQ] THEN
  MP_TAC(ISPECL
   [`t0:gtree`; `t1:gtree`; `t2:gtree`; `t3:gtree`;
    `gtree_restrict t0 (gsplit r Gpush)`;
    `gtree_restrict t1 (gsplit r Gskip)`;
    `gtree_restrict t2 (gsplit r Gpop0)`;
    `gtree_restrict t3 (gsplit r Gpop1)`] GTREE_MEM0_CONS_PAIRS) THEN
  REWRITE_TAC[GTREE_RESTRICT_PARTITION] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` (cases "list")) THEN
  REWRITE_TAC[GTREE_MEM; gtree_isleaf] THEN
  REWRITE_TAC[GTR_MEM_GSPLIT] THEN
  STRUCT_CASES_TAC(ISPEC `a0:gram_symbol` (cases "gram_symbol")) THEN
  REWRITE_TAC[gtree_sel; distinctness "gram_symbol"] THEN ASM_REWRITE_TAC[]);;

(* Main correctness theorem: the deleted (false) component of gtree_restrict *)
(* t r collects exactly the chromograms of t matched by r.                   *)
let GTREE_MEM0_RESTRICT = prove
 (`!t r w. gtree_mem (gtree_pair_sub (gtree_restrict t r) F) w <=>
           gtree_mem t w /\ gtr_mem r w`,
  MATCH_MP_TAC gtree_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (* The node case is NODE_STEP.  Otherwise either r is GtrNil, or t is      *)
  (* GtreeEmpty, and the deleted component is empty, or t is one of the 8    *)
  (* nonempty leaves.                                                        *)
  TRY(DISCH_TAC THEN MATCH_MP_TAC NODE_STEP THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  REWRITE_TAC[gtree_restrict] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(REWRITE_TAC[gtree_pair_sub; GTREE_MEM_EMPTY] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GTR_ISNIL_EQ]) THEN
      ASM_REWRITE_TAC[GTR_MEM_NIL] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[empty_gtree_pair; gtree_pair_sub; GTREE_MEM_EMPTY] THEN
      NO_TAC) THEN
  REWRITE_TAC[GTR_MATCH0E; GTR_MATCH1E; GTR_MATCH2E; GTR_MATCH3E] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[gtp_0_e; gtp_1_e; gtp_2_e; gtp_3_e; gtp_01_e; gtp_12_e;
                  gtp_13_e; gtp_23_e;
                  gtp_e_0; gtp_e_1; gtp_e_2; gtp_e_3; gtp_e_01; gtp_e_12;
                  gtp_e_13; gtp_e_23;
                  gtp_0_1; gtp_1_0; gtp_1_2; gtp_2_1; gtp_1_3; gtp_3_1;
                  gtp_2_3; gtp_3_2;
                  gtree_pair_sub; GTREE_MEM_EMPTY] THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` (cases "list")) THEN
  REWRITE_TAC[GTREE_MEM; gtree_isleaf; gtree_leaf_mem] THEN
  STRUCT_CASES_TAC(ISPEC `a0:gram_symbol` (cases "gram_symbol")) THEN
  REWRITE_TAC[distinctness "gram_symbol"] THEN
  ASM_CASES_TAC `a1:gram_symbol list = []` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;
