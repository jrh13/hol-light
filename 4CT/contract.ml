(* ========================================================================= *)
(* 4CT/contract.ml                                                           *)
(*                                                                           *)
(* contract.v: contracts, sparse contracts, triads and the contract          *)
(* colouring theorem (Gonthier's contract_coloring): in a minimal counter-   *)
(* example a valid contract cc has a contract colouring.  Structure:         *)
(*   1. contract rings, contract_ring_max, sparse_contract_ring              *)
(*   2. fcard_adj_max (birkhoff.v), contract3_valid, triad_valid             *)
(*   3. the contracted map (two face Walkup steps), its rings and colourings *)
(*   4. contract_coloring                                                    *)
(* ========================================================================= *)

needs "4CT/embed.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition: contract_ring (contract.v).  triad is in coloring.ml.         *)
(* ------------------------------------------------------------------------- *)

let contract_ring = new_definition
 `contract_ring (H:(A)hypermap) (cc:(A)list) (r:(A)list) <=>
    scycle H (rlink H) r /\ proper_ring H r /\
    (!x. MEM x (TL r) ==> MEM x (insertE H cc))`;;

(* ------------------------------------------------------------------------- *)
(* Elementary facts: insertE, filters, minimal counter-examples.             *)
(* ------------------------------------------------------------------------- *)

let INSERTE_NIL = prove
 (`!(H:(A)hypermap). insertE H [] = []`,
  REWRITE_TAC[INSERTE_CLAUSES]);;

let MEM_INSERTE = prove
 (`!(H:(A)hypermap) cc x.
     MEM x (insertE H cc) <=> ?c. MEM c cc /\ (x = c \/ x = edge_map H c)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[INSERTE_CLAUSES; MEM] THEN MESON_TAC[]);;

let INSERTE_IN_DART = prove
 (`!(H:(A)hypermap) p x.
     (!u. MEM u p ==> u IN dart H) /\ MEM x (insertE H p) ==> x IN dart H`,
  REWRITE_TAC[MEM_INSERTE] THEN MESON_TAC[EDGE_MAP_IN_DART]);;

(* In a plain map insertE cc is closed under edge_map (Coq's ccE); off the   *)
(* darts edge_map is the identity, so no dart hypothesis is needed.          *)

let INSERTE_EDGE_CLOSED = prove
 (`!(H:(A)hypermap) cc x.
     plain_hypermap H /\ MEM x (insertE H cc)
     ==> MEM (edge_map H x) (insertE H cc)`,
  REWRITE_TAC[MEM_INSERTE] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `c:A` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(c:A) IN dart H` THEN
  ASM_SIMP_TAC[PLAIN_EQ; MAP_FIX_OFFDART]);;

let INSERTE_EDGE_SYM = prove
 (`!(H:(A)hypermap) p x.
     plain_hypermap H
     ==> (MEM (edge_map H x) (insertE H p) <=> MEM x (insertE H p))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[INSERTE_EDGE_CLOSED] THEN
  ASM_CASES_TAC `(x:A) IN dart H` THEN
  ASM_MESON_TAC[INSERTE_EDGE_CLOSED; PLAIN_EQ; MAP_FIX_OFFDART]);;

let FBAND_FILTER = prove
 (`!(H:(A)hypermap) P l x. fband H (FILTER P l) x ==> fband H l x`,
  REWRITE_TAC[FBAND_MEM_IFF; MEM_FILTER] THEN MESON_TAC[]);;

let FACE_SIMPLE_FILTER = prove
 (`!(H:(A)hypermap) P l. face_simple H l ==> face_simple H (FILTER P l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; face_simple] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[face_simple] THEN
  ASM_MESON_TAC[FBAND_FILTER]);;

let MCE_PROPS = prove
 (`!H:(A)hypermap. minimal_counter_example H
     ==> planar_hypermap H /\ bridgeless H /\ plain_hypermap H /\ precubic H /\
         cubic_hypermap H /\ connected_hypermap H`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MCE_CUBIC; MCE_CONNECTED] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[minimal_counter_example] THEN SIMP_TAC[]);;

let PROPER_RING_GE2 = prove
 (`!(H:(A)hypermap) r. proper_ring H r ==> 2 <= LENGTH r`,
  REWRITE_TAC[proper_ring] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let CONTRACT_RING_FACTS = prove
 (`!(H:(A)hypermap) cc p.
     contract_ring H cc p
     ==> scycle H (rlink H) p /\ proper_ring H p /\ 2 <= LENGTH p /\
         ALL (\z. z IN dart H) p /\ PAIRWISE (\a b. ~(a = b)) p /\
         (!x. MEM x (TL p) ==> MEM x (insertE H cc))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contract_ring] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PROPER_RING_GE2; SCYCLE_GE2_ALL_DART; SCYCLE_PAIRWISE]);;

let PAIRWISE_TL = prove
 (`!(R:A->A->bool) l. ~(l = []) /\ PAIRWISE R l ==> PAIRWISE R (TL l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP_TAC[PAIRWISE; TL; NOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* contract_ring_max: a contract ring has at most LENGTH cc + 1 darts.       *)
(* The tail of the ring injects into cc via z |-> (if MEM z cc then z else   *)
(* edge z): two tail darts with the same image would be an edge pair on the  *)
(* ring (DISKN_EDGE_EXCL).                                                   *)
(* ------------------------------------------------------------------------- *)

let CONTRACT_RING_MAX = prove
 (`!(H:(A)hypermap) cc p.
     minimal_counter_example H /\ contract_ring H cc p
     ==> LENGTH p <= LENGTH cc + 1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS)
    (STRIP_ASSUME_TAC o MATCH_MP CONTRACT_RING_FACTS)) THEN
  SUBGOAL_THEN `~(p:(A)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `2 <= n ==> ~(n = 0)`]; ALL_TAC]
     THEN
  ABBREV_TAC `f = \z:A. if MEM z cc then z else edge_map H z` THEN
  SUBGOAL_THEN `!z:A. MEM z (TL p) ==> MEM ((f:A->A) z) cc` ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (z:A) (insertE H cc)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MEM_INSERTE] THEN EXPAND_TAC "f" THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A`
      (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(c:A) IN dart H` THEN ASM_SIMP_TAC[PLAIN_EQ] THEN
    ASM_MESON_TAC[MAP_FIX_OFFDART];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. MEM a (TL p) /\ MEM b (TL p) /\ (f:A->A) a = f b
    ==> a = b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `MEM (a:A) p /\ MEM b p /\ a IN dart H /\ b IN dart H`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MEM_TL_IMP; RING_MEM_DART]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `p:(A)list`; `a:A`] DISKN_EDGE_EXCL) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `p:(A)list`; `b:A`] DISKN_EDGE_EXCL) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(f:A->A) a = f b` THEN EXPAND_TAC "f" THEN
    REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[EDGEI];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`set_of_list (cc:(A)list)`; `MAP (f:A->A) (TL p)`]
    PAIRWISE_LENGTH_LE_CARD) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_SET_OF_LIST; IN_SET_OF_LIST; MEM_MAP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PAIRWISE_INJ_MAP THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; MATCH_MP_TAC PAIRWISE_TL
         THEN ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[]];
    MP_TAC(ISPEC `cc:(A)list` CARD_SET_OF_LIST_LE) THEN
    MP_TAC(ISPEC `p:(A)list` LENGTH_TL) THEN
    ASM_SIMP_TAC[LENGTH_MAP] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Sparse lists have no two darts in the same node.                          *)
(* ------------------------------------------------------------------------- *)

let CNODE_SYM = prove
 (`!(H:(A)hypermap) a b. a IN dart H /\ cnode H a b ==> cnode H b a`,
  REWRITE_TAC[cnode; node] THEN
  MESON_TAC[ORBIT_MAP_SYM; NODE_MAP_PERMUTES; FINITE_DART]);;

let SPARSE_CNODE = prove
 (`!(H:(A)hypermap) l a b.
     sparse H l /\ MEM a l /\ MEM b l /\ a IN dart H /\ cnode H a b ==> a = b`,
  REWRITE_TAC[sparse; MEM_EXISTS_EL] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THEN
  ASM_MESON_TAC[CNODE_SYM; ARITH_RULE `i:num = j \/ i < j \/ j < i`]);;

(* ------------------------------------------------------------------------- *)
(* Arcs of a duplicate-free cyclic list (mathcomp arc / rot_to_arc): the arc *)
(* from j to u (excluded) avoids u and nextc p u when nextc p u <> j, and    *)
(* then it is shorter than p by at least two items.                          *)
(* ------------------------------------------------------------------------- *)

let NEXTL_APPEND_CONS = prove
 (`!(a:(A)list) h u s.
     ~MEM u a
       ==> nextl h (APPEND a (CONS u s)) u = (if s = [] then h else HD s)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[APPEND; nextl; MEM; DE_MORGAN_THM]);;

let NEXTC_ROT_LIST = prove
 (`!(p:(A)list) i u. uniq_list p /\ MEM u p
   ==> nextc (rot_list i p) u = nextc p u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEXTC_CYCLE THEN
  REWRITE_TAC[LIST_CYCLE_ROT; MEM_ROT_LIST] THEN
  ASM_MESON_TAC[LIST_CYCLE_NEXTC; UNIQ_ROT; uniq_list; MEM]);;

let ARC_LIST_PROPS = prove
 (`!(p:(A)list) u j.
     uniq_list p /\ MEM u p /\ MEM j p /\ ~(j = u) /\ ~(nextc p u = j)
     ==> LENGTH (arc_list p j u) + 2 <= LENGTH p /\ ~MEM u (arc_list p j u) /\
         ~MEM (nextc p u) (arc_list p j u) /\
         (!z. MEM z (arc_list p j u) ==> MEM z p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(A)list`; `j:A`; `u:A`] ROT_TO_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `p1:(A)list`
    (X_CHOOSE_THEN `p2:(A)list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `nextc (p:(A)list) u = nextc (rot_list i p) u` SUBST_ALL_TAC
    THENL
   [ASM_MESON_TAC[NEXTC_ROT_LIST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`; `p:(A)list`] UNIQ_ROT) THEN
  MP_TAC(ISPECL [`i:num`; `p:(A)list`] LENGTH_ROT_LIST) THEN
  UNDISCH_TAC `rot_list i (p:(A)list) = APPEND (CONS j p1) (CONS u p2)` THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`CONS (j:A) p1`; `CONS (u:A) p2`] UNIQ_LIST_APPEND_DISJOINT)
    THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `nextc (APPEND (CONS (j:A) p1) (CONS u p2)) u =
                if p2 = [] then j else HD p2` SUBST_ALL_TAC THENL
   [REWRITE_TAC[nextc; APPEND_EQ_NIL; NOT_CONS_NIL; HD_APPEND; HD] THEN
    MATCH_MP_TAC NEXTL_APPEND_CONS THEN ASM_MESON_TAC[MEM];
    ALL_TAC] THEN
  UNDISCH_TAC `~((if p2 = [] then j else HD p2) = (j:A))` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `LENGTH (APPEND (CONS (j:A) p1) (CONS u p2)) = LENGTH
     (p:(A)list)` THEN
    UNDISCH_TAC `~(p2:(A)list = [])` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    ASM_MESON_TAC[MEM];
    ASM_MESON_TAC[MEM; HD_MEM];
    ASM_MESON_TAC[MEM_ARC_LIST]]);;

(* ------------------------------------------------------------------------- *)
(* sparse_contract_ring (contract.v): a contract ring p of a sparse contract *)
(* is nontrivial.  Core claim (dF_cc): the inner disk of a contract ring has *)
(* a face.  Otherwise, with x = HD p, both node x and node (node x) lie on   *)
(* the ring: by DF_CC_NODE at y = x and at y = node x, else the chord        *)
(* edge (node y) cuts off a shorter contract ring with an empty inner disk,  *)
(* contradicting the induction hypothesis.  So the tail of p holds two       *)
(* darts of the same node, contradicting sparseness (DF_CC_STEP).            *)
(* ------------------------------------------------------------------------- *)

let MEM_HD_TL = prove
 (`!l (x:A). ~(l = []) ==> (MEM x l <=> x = HD l \/ MEM x (TL l))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; MEM; HD; TL]);;

let CHORD_RING_SMALLER = prove
 (`!(H:(A)hypermap) cc p c.
     minimal_counter_example H /\ contract_ring H cc p /\ (!y. ~diskF H p y) /\
     c IN diskE H p /\ fband H p c /\ fband H p (edge_map H c) /\
     ~(nextc p (fproj H p c) = fproj H p (edge_map H c)) /\
     ~MEM (HD p) (arc_list p (fproj H p (edge_map H c)) (fproj H p c))
     ==> contract_ring H cc (chord_ring H p c) /\
         LENGTH (chord_ring H p c) < LENGTH p /\
         (!y. ~diskF H (chord_ring H p c) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS)
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP CONTRACT_RING_FACTS)
      STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `diskE H p (c:A) /\ diskN H p c /\ ~MEM c p` STRIP_ASSUME_TAC
    THENL
   [UNDISCH_TAC `(c:A) IN diskE H p` THEN REWRITE_TAC[IN; diskE]
     THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p:(A)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `2 <= n ==> ~(n = 0)`]; ALL_TAC]
     THEN
  ABBREV_TAC `u = fproj (H:(A)hypermap) p c` THEN
  ABBREV_TAC `j = fproj (H:(A)hypermap) p (edge_map H c)` THEN
  SUBGOAL_THEN `MEM (u:A) p /\ cface H c u /\ MEM (j:A) p
    /\ cface H (edge_map H c) j`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FPROJ_IN_FBAND]; ALL_TAC] THEN
  SUBGOAL_THEN `~(j:A = u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FPROJ_NEQ_BRIDGELESS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:(A)list`; `u:A`; `j:A`] ARC_LIST_PROPS) THEN
  ASM_REWRITE_TAC[uniq_list] THEN STRIP_TAC THEN
  SUBGOAL_THEN `TL (chord_ring (H:(A)hypermap) p c) = arc_list p j u /\
                LENGTH (chord_ring H p c) = LENGTH (arc_list p j u) + 1`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[chord_ring; TL; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[contract_ring] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCYCLE_CHORD_RING THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PROPER_CHORD_RING THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `p:(A)list`; `c:A`] DISKN_EDGE_EXCL) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM_HD_TL]];
    ASM_ARITH_TAC;
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL
     [ASM_MESON_TAC[diskF; DISKN_SUBSET_DART; ALL_DART_CHORD_RING]; ALL_TAC]
       THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `p:(A)list`; `c:A`;
      `y:A`] DISKF_CHORD_RING) THEN
    ASM_REWRITE_TAC[]]);;

let DF_CC_NODE = prove
 (`!(H:(A)hypermap) cc p y.
     minimal_counter_example H /\ contract_ring H cc p /\ (!z. ~diskF H p z) /\
     (!q. LENGTH q < LENGTH p /\ contract_ring H cc q ==> ?z. diskF H q z) /\
     MEM y p /\ (y = HD p \/ nextc p y = HD p)
     ==> MEM (node_map H y) p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
       STRIP_ASSUME_TAC (MATCH_MP MCE_PROPS th))
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
       STRIP_ASSUME_TAC (MATCH_MP CONTRACT_RING_FACTS th))
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  SUBGOAL_THEN `(y:A) IN dart H /\ node_map H y IN dart H /\
                edge_map H y IN dart H` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MEM_DART; NODE_MAP_IN_DART; EDGE_MAP_IN_DART];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  (* Keep the disjunction out of CFACE_TAC's way (it case-splits on it).     *)
  FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
  SUBGOAL_THEN `diskN H p (node_map H (y:A)) /\ fband H p (node_map H y)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IN_DISKN; DISKN_NODE_FWD; diskF]; ALL_TAC] THEN
  ABBREV_TAC `c = edge_map H (node_map H (y:A))` THEN
  SUBGOAL_THEN `face_map H (c:A) = y /\ edge_map H c = node_map H y /\
                c IN dart H` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[nodeK; PLAIN_EQ; EDGE_MAP_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:A) IN diskE H p` ASSUME_TAC THENL
   [REWRITE_TAC[IN] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `p:(A)list`; `node_map H (y:A)`]
      DISKE_EDGE) THEN
    ASM_REWRITE_TAC[diskE];
    ALL_TAC] THEN
  SUBGOAL_THEN `fband H p (c:A) /\ fband H p (edge_map H c)`
  STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fproj H p (c:A) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[FPROJ_CFACE; SIMPLE_FPROJ; CFT_FACE; SCYCLE_SIMPLE];
    ALL_TAC] THEN
  ABBREV_TAC `y1 = nextc p (y:A)` THEN
  SUBGOAL_THEN `MEM (y1:A) p /\ cface H (edge_map H y) y1` STRIP_ASSUME_TAC
  THENL
   [ASM_MESON_TAC[NEXTC_MEM; CYCLE_NEXTC_STEP; rlink; SCYCLE_CYCLE];
    ALL_TAC] THEN
  ABBREV_TAC `j = fproj H p (node_map H (y:A))` THEN
  SUBGOAL_THEN `MEM (j:A) p /\ cface H (node_map H y) j` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[FPROJ_IN_FBAND]; ALL_TAC] THEN
  SUBGOAL_THEN `~(j:A = y) /\ ~(y1:A = j)` STRIP_ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`p:(A)list`; `y:A`; `j:A`] ARC_LIST_PROPS) THEN
  ASM_REWRITE_TAC[uniq_list] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`; `p:(A)list`; `c:A`]
    CHORD_RING_SMALLER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let CNODE_NODE = prove
 (`!(H:(A)hypermap) x. cnode H x (node_map H x)`,
  REWRITE_TAC[cnode; node] THEN MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]);;

let DF_CC_STEP = prove
 (`!(H:(A)hypermap) cc p.
     minimal_counter_example H /\ sparse H (insertE H cc) /\
     contract_ring H cc p /\ (!y. ~diskF H p y) /\
     (!q. LENGTH q < LENGTH p /\ contract_ring H cc q ==> ?y. diskF H q y)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTRACT_RING_FACTS) THEN
  ABBREV_TAC `x = HD (p:(A)list)` THEN
  SUBGOAL_THEN `~(p:(A)list = []) /\ MEM (x:A) p /\ x IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `2 <= n ==> ~(n = 0)`; HD_MEM;
                  RING_MEM_DART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`; `p:(A)list`; `x:A`]
    DF_CC_NODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`; `p:(A)list`;
                 `node_map H (x:A)`] DF_CC_NODE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN MATCH_MP_TAC RLINK_NEXTC_EQ THEN
    EXISTS_TAC `H:(A)hypermap` THEN ASM_REWRITE_TAC[RLINK_NODE];
    DISCH_TAC] THEN
  SUBGOAL_THEN `node_map H (x:A) IN dart H /\ ~(node_map H x = x) /\
                ~(node_map H (node_map H x) = x) /\
                ~(node_map H x = node_map H (node_map H x))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NODE_MAP_IN_DART; CUBIC_NEQ; CUBIC_EQ; NODEI]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (node_map H (x:A)) (insertE H cc) /\
                MEM (node_map H (node_map H x)) (insertE H cc)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MEM_HD_TL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `insertE H (cc:(A)list)`; `node_map H (x:A)`;
                 `node_map H (node_map H (x:A))`] SPARSE_CNODE) THEN
  ASM_REWRITE_TAC[CNODE_NODE]);;

let DF_CC = prove
 (`!(H:(A)hypermap) cc p.
     minimal_counter_example H /\ sparse H (insertE H cc)
       /\ contract_ring H cc p
     ==> ?y. diskF H p y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
    THEN
  SPEC_TAC(`p:(A)list`,`p:(A)list`) THEN
  SUBGOAL_THEN `!n p:(A)list. LENGTH p = n ==> contract_ring H cc p
                              ==> ?y. diskF H p y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `p:(A)list` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_TAC
    THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!q:(A)list. LENGTH q < LENGTH (p:(A)list)
    /\ contract_ring H cc q
                            ==> ?y. diskF H q y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (q:(A)list)`)
     THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q:(A)list`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`; `p:(A)list`] DF_CC_STEP) THEN
  ASM_REWRITE_TAC[]);;

let SPARSE_CONTRACT_RING = prove
 (`!(H:(A)hypermap) cc p.
     minimal_counter_example H /\ sparse H (insertE H cc)
       /\ contract_ring H cc p
     ==> nontrivial_ring H 0 p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTRACT_RING_FACTS) THEN
  ASM_SIMP_TAC[NONTRIVIAL0P] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN] THEN ASM_MESON_TAC[DF_CC]; ALL_TAC] THEN
  MP_TAC(ISPEC `p:(A)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `p':(A)list` SUBST_ALL_TAC))) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = APPEND (p':(A)list) [x]` THEN
  SUBGOAL_THEN `scycle H (rlink H) (r:(A)list) /\ proper_ring H r /\
                ALL (\z. z IN dart H) r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    ASM_SIMP_TAC[SCYCLE_ROT1_CONS; PROPER_RING_ROT1_CONS; ALL_APPEND; ALL] THEN
    UNDISCH_TAC `ALL (\z. z IN dart H) (CONS (x:A) p')` THEN
    REWRITE_TAC[ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `contract_ring H cc (rev_ring H (r:(A)list))` ASSUME_TAC THENL
   [REWRITE_TAC[contract_ring] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SCYCLE_REV_RING];
      ASM_SIMP_TAC[PROPER_REV_RING];
      EXPAND_TAC "r" THEN
      REWRITE_TAC[REV_RING_ROT1_CONS; TL; rev_ring; MEM_REVERSE; MEM_MAP] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INSERTE_EDGE_CLOSED THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[TL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`;
    `rev_ring H (r:(A)list)`] DF_CC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y:A`) THEN
  EXISTS_TAC `y:A` THEN
  SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[diskF; DISKN_SUBSET_DART; REV_RING_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `y:A`] DISKF_REV_RING) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "r" THEN
  REWRITE_TAC[DISKN_ROT1_CONS; diskFC; FBAND_APPEND; FBAND_CONS; FBAND_SING]
    THEN
  MESON_TAC[]);;

let CONTRACT3_VALID = prove
 (`!(H:(A)hypermap) cc p.
     minimal_counter_example H /\ sparse H (insertE H cc) /\ LENGTH cc <= 3
     ==> ~contract_ring H cc p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTRACT_RING_FACTS) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`; `p:(A)list`] CONTRACT_RING_MAX)
    THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (p:(A)list) <= 5 /\ ~(LENGTH p = 5)` STRIP_ASSUME_TAC
    THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`;
    `p:(A)list`] SPARSE_CONTRACT_RING) THEN
  MP_TAC(SPEC `p:(A)list`
    (MATCH_MP BIRKHOFF (ASSUME `minimal_counter_example (H:(A)hypermap)`)))
      THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* fcard_adj_max (birkhoff.v): two non-cofacial darts x, y have at most two  *)
(* common adjacent faces.  Everything happens on the spoke ring of x, which  *)
(* is a chordless simple R-cycle of length arity x > 4 whose darts are       *)
(* exactly the faces adjacent to x (SPOKE_RING_FACTS).                       *)
(* ------------------------------------------------------------------------- *)

let ADJ_DART = prove
 (`!(H:(A)hypermap) x t. x IN dart H /\ adj H x t ==> t IN dart H`,
  REWRITE_TAC[adj; rlink] THEN
  MESON_TAC[FACE_IN_DART; EDGE_MAP_IN_DART; CFT_DART]);;

let SPOKE_RING_FACTS = prove
 (`!(H:(A)hypermap) x.
     minimal_counter_example H /\ x IN dart H
     ==> scycle H (rlink H) (spoke_ring H x) /\ 4 < LENGTH (spoke_ring H x) /\
         chordless H (spoke_ring H x) /\
         ALL (\z. z IN dart H) (spoke_ring H x) /\
         PAIRWISE (\a b. ~(a = b)) (spoke_ring H x) /\
         (!z. MEM z (spoke_ring H x)
              ==> z IN dart H /\ cface H x (node_map H z) /\ adj H x z
                /\ adj H z x) /\
         (!t. t IN dart H /\ adj H x t
              ==> ?t1. MEM t1 (spoke_ring H x) /\ cface H t t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  SUBGOAL_THEN `scycle H (rlink H) (spoke_ring H (x:A)) /\
                4 < LENGTH (spoke_ring H x) /\ chordless H (spoke_ring H x)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCYCLE_SPOKE_RING; SIZE_SPOKE_RING; MIN_ARITY;
     CHORDLESS_SPOKE_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\z. z IN dart H) (spoke_ring H (x:A))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCYCLE_GE2_ALL_DART THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\a b:A. ~(a = b)) (spoke_ring H x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCYCLE_PAIRWISE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN dart H` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_MEM_DART]; ALL_TAC] THEN
    SUBGOAL_THEN `cface H x (node_map H (z:A))` ASSUME_TAC THENL
     [ASM_MESON_TAC[MEM_SPOKE_RING]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `adj H x (z:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ADJ_NODE; ADJ_CFACE_L]; ALL_TAC] THEN
    ASM_MESON_TAC[ADJ_SYM];
    X_GEN_TAC `t:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `t:A`] FBAND_SPOKE_RING) THEN
    ASM_REWRITE_TAC[FBAND_MEM_IFF]]);;

let NEXTC_NEXTC_NEQ = prove
 (`!(r:(A)list) y. PAIRWISE (\a b. ~(a = b)) r /\ MEM y r /\ 2 < LENGTH r
                  ==> ~(nextc r (nextc r y) = y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. ITER k (nextc r) (y:A) = y
    \/ ITER k (nextc r) y = nextc r y`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:A. MEM t r ==> t IN {y, nextc r y}` ASSUME_TAC THENL
   [X_GEN_TAC `t:A` THEN DISCH_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]
     THEN
    MP_TAC(ISPECL [`r:(A)list`; `y:A`] RING_CHAIN_COVERS)
      THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `t:A`) THEN ASM_REWRITE_TAC[MEM] THEN
    ASM_MESON_TAC[MEM_ITERLIST_IMP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{y:A, nextc r y}`; `r:(A)list`] PAIRWISE_LENGTH_LE_CARD) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY]
    THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let FCARD_ADJ_ADJ = prove
 (`!(H:(A)hypermap) x y.
     minimal_counter_example H /\ x IN dart H /\ y IN dart H /\ adj H x y
     ==> fcard_face H {z | adj H y z /\ adj H x z} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] SPOKE_RING_FACTS)
    THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = spoke_ring (H:(A)hypermap) x` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y1:A. MEM y1 r /\ cface H y y1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `z1 = prevc (r:(A)list) y1` THEN
  ABBREV_TAC `z2 = nextc (r:(A)list) y1` THEN
  SUBGOAL_THEN `MEM (z1:A) r /\ MEM (z2:A) r /\ rlink H z1 y1 /\ rlink H y1 z2
    /\
                ~(z1 = z2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[PREVC_MEM]; ASM_MESON_TAC[NEXTC_MEM];
      ASM_MESON_TAC[RLINK_PREVC]; ASM_MESON_TAC[CYCLE_NEXTC_STEP;
        SCYCLE_CYCLE];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`r:(A)list`; `y1:A`] NEXTC_NEXTC_NEQ) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[NEXTC_PREVC; ARITH_RULE `4 < n ==> 2 < n`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z1:A) IN dart H /\ (z2:A) IN dart H /\ (y1:A) IN dart H /\
                adj H x z1 /\ adj H x z2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `adj H y (z1:A) /\ adj H y (z2:A) /\ ~cface H z1 z2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `adj H (y1:A) z1` MP_TAC THENL
       [ASM_MESON_TAC[RLINK_ADJ; ADJ_SYM]; ASM_MESON_TAC[ADJ_CFACE_L]];
      SUBGOAL_THEN `adj H (y1:A) z2` MP_TAC THENL
       [ASM_MESON_TAC[RLINK_ADJ]; ASM_MESON_TAC[ADJ_CFACE_L]];
      ASM_MESON_TAC[SCYCLE_CFACE_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (orbit_map (face_map H)) {z:A | adj H y z /\ adj H x z} =
                {orbit_map (face_map H) z1, orbit_map (face_map H) z2}`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `s:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A`
        (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(t:A) IN dart H` ASSUME_TAC THENL
       [ASM_MESON_TAC[ADJ_DART]; ALL_TAC] THEN
      SUBGOAL_THEN `?t1:A. MEM t1 r /\ cface H t t1` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(t1:A) IN dart H` ASSUME_TAC
        THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `adj H (y1:A) t1` ASSUME_TAC THENL
       [ASM_MESON_TAC[ADJ_CFACE_L; ADJ_CFACE]; ALL_TAC] THEN
      SUBGOAL_THEN `~(t1:A = y1)` ASSUME_TAC THENL
       [ASM_MESON_TAC[ADJ_NO_CFACE; CFT_TRANS; CFACE_SYM_GEN]; ALL_TAC] THEN
      SUBGOAL_THEN `t1:A = z2 \/ t1 = z1` MP_TAC THENL
       [MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `y1:A`; `t1:A`]
          CHORDLESS_RING) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PREVC_NEXTC];
        ALL_TAC] THEN
      ASM_MESON_TAC[ORBIT_EQ_CFACE];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [EXISTS_TAC `z1:A`; EXISTS_TAC `z2:A`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(orbit_map (face_map H) (z1:A) = orbit_map (face_map H) z2)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ORBIT_EQ_CFACE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
    NOT_IN_EMPTY] THEN
  ARITH_TAC);;

let ADJ12_RING = prove
 (`!(H:(A)hypermap) x y z y1 z1 x1.
     minimal_counter_example H /\ x IN dart H /\ y IN dart H /\ z IN dart H /\
     y1 IN dart H /\ z1 IN dart H /\ x1 IN dart H /\
     cface H y y1 /\ cface H x (node_map H y1) /\
     cface H z z1 /\ cface H x (node_map H z1) /\
     cface H z x1 /\ cface H (edge_map H y) (edge_map H x1) /\
     ~cface H z y /\ ~adj H z y /\ ~cface H x (edge_map H y)
       /\ ~adj H x (edge_map H y)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  SUBGOAL_THEN
   `edge_map H (x1:A) IN dart H /\ node_map H (z1:A) IN dart H /\
    edge_map H (node_map H z1) IN dart H /\ node_map H (y1:A) IN dart H /\
    edge_map H (y:A) IN dart H /\ node_map H (node_map H y1) IN dart H /\
    node_map H (node_map H z1) IN dart H /\ edge_map H y1 IN dart H /\
    edge_map H z1 IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `face_map H (edge_map H (node_map H (z1:A))) = z1 /\
    face_map H (edge_map H (node_map H (y1:A))) = y1 /\
    edge_map H (edge_map H (x1:A)) = x1 /\
    edge_map H (edge_map H (node_map H (z1:A))) = node_map H z1 /\
    node_map H (node_map H (y1:A)) = face_map H (edge_map H y1) /\
    node_map H (node_map H (z1:A)) = face_map H (edge_map H z1)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[nodeK; PLAIN_EQ; CUBIC_EQ']; ALL_TAC] THEN
  SUBGOAL_THEN
   `cface H (edge_map H (node_map H (z1:A))) z1 /\
    cface H (edge_map H (node_map H (y1:A))) y1 /\
    cface H (node_map H (node_map H (y1:A))) (edge_map H y1) /\
    cface H (node_map H (node_map H (z1:A))) (edge_map H z1) /\
    ~cface H (node_map H (node_map H (y1:A))) (node_map H y1) /\
    ~cface H (node_map H (node_map H (z1:A))) (node_map H z1) /\
    ~cface H (y1:A) (node_map H y1) /\ ~cface H (z1:A) (node_map H z1)`
  STRIP_ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~cface H (y:A) (edge_map H y) /\ ~cface H (x1:A) (edge_map H x1) /\
    ~cface H (y1:A) (edge_map H y1) /\ ~cface H (z1:A) (edge_map H z1)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[BRIDGELESS_CFACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `adj H x (node_map H (node_map H (y1:A))) /\
    adj H x (node_map H (node_map H (z1:A))) /\
    adj H y (node_map H (node_map H (y1:A))) /\ adj H z (edge_map H (z1:A)) /\
    ~adj H y (z:A)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[ADJ_NODE; ADJ_SYM; ADJ_CFACE_L];
      ASM_MESON_TAC[ADJ_NODE; ADJ_SYM; ADJ_CFACE_L];
      ASM_MESON_TAC[ADJ_EDGE; ADJ_CFACE; ADJ_CFACE_L];
      ASM_MESON_TAC[ADJ_EDGE; ADJ_CFACE_L];
      ASM_MESON_TAC[ADJ_SYM]];
    ALL_TAC] THEN
  ABBREV_TAC `q = [y:A; edge_map H x1; edge_map H (node_map H z1);
    node_map H y1]` THEN
  SUBGOAL_THEN `scycle H (rlink H) (q:(A)list) /\ ALL (\w. w IN dart H) q /\
                LENGTH q = 4 /\ MEM (edge_map H (node_map H (z1:A))) q /\
                MEM (node_map H (y1:A)) q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[scycle; list_cycle; face_simple; FBAND_CONS; FBAND_NIL;
      list_path;
                LAST; NOT_CONS_NIL; ALL; LENGTH; MEM; rlink; ARITH] THEN
    ASM_REWRITE_TAC[] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `proper_ring H (q:(A)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIZE_PROPER_RING THEN ASM_REWRITE_TAC[]
     THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nontrivial_ring H 0 (q:(A)list)` MP_TAC THENL
   [ASM_SIMP_TAC[NONTRIVIAL0P] THEN CONJ_TAC THENL
     [EXISTS_TAC `node_map H (node_map H (y1:A))` THEN REWRITE_TAC[IN; diskF]
       THEN
      CONJ_TAC THENL [ASM_MESON_TAC[RING_IN_DISKN; DISKN_NODE_FWD]; ALL_TAC]
        THEN
      EXPAND_TAC "q" THEN CFACE_TAC[NO_ADJ_ADJ];
      EXISTS_TAC `node_map H (node_map H (z1:A))` THEN
      ASM_REWRITE_TAC[diskFC] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`H:(A)hypermap`; `q:(A)list`;
                       `edge_map H (node_map H (z1:A))`] DISKN_EDGE_RING) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DISKN_NODE_EQ];
        EXPAND_TAC "q" THEN CFACE_TAC[NO_ADJ_ADJ]]];
    MP_TAC(SPEC `q:(A)list`
      (MATCH_MP BIRKHOFF (ASSUME `minimal_counter_example (H:(A)hypermap)`)))
        THEN
    ASM_REWRITE_TAC[ARITH]]);;

let ADJ12_EDGE = prove
 (`!(H:(A)hypermap) x y z.
     minimal_counter_example H /\ x IN dart H /\ y IN dart H /\ z IN dart H /\
     adj H x y /\ adj H x z /\ adj H z (edge_map H y)
     ==> (cface H z y \/ adj H z y) \/
         cface H x (edge_map H y) \/ adj H x (edge_map H y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] SPOKE_RING_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y1:A. MEM y1 (spoke_ring H x) /\ cface H y y1`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?z1:A. MEM z1 (spoke_ring H x) /\ cface H z z1`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x1:A. cface H z x1 /\ cface H (edge_map H y) (edge_map H x1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `adj H z (edge_map H (y:A))` THEN
    REWRITE_TAC[adj; rlink; GSYM cface] THEN MESON_TAC[CFACE_SYM_GEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y1:A) IN dart H /\ (z1:A) IN dart H /\ (x1:A) IN dart H /\
                cface H x (node_map H y1) /\ cface H x (node_map H z1)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]
    THEN ASM_MESON_TAC[CFT_DART]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `y:A`; `z:A`; `y1:A`; `z1:A`; `x1:A`]
    ADJ12_RING) THEN
  ASM_REWRITE_TAC[]);;

let CROSS_ADJ = prove
 (`!(H:(A)hypermap) x y a b.
     minimal_counter_example H /\ x IN dart H /\ y IN dart H /\
     a IN dart H /\ b IN dart H /\
     ~cface H x y /\ ~adj H x y /\ ~cface H a b /\
     adj H x a /\ adj H x b /\ adj H y a /\ adj H y b
     ==> adj H a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  SUBGOAL_THEN `?u:A. cface H y u /\ cface H (edge_map H u) b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `adj H y (b:A)` THEN REWRITE_TAC[adj; rlink; GSYM cface] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:A) IN dart H /\ edge_map H u IN dart H /\
                edge_map H (edge_map H u) = u`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CFT_DART; EDGE_MAP_IN_DART; PLAIN_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `edge_map H (u:A)`; `a:A`] ADJ12_EDGE)
    THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[ADJ_CFACE; ADJ_CFACE_L; ADJ_SYM];
    ASM_MESON_TAC[ADJ_CFACE; CFT_TRANS; CFACE_SYM_GEN]]);;

let NEXTC_CLOSED_LENGTH = prove
 (`!(r:(A)list) y s.
     PAIRWISE (\a b. ~(a = b)) r /\ MEM y r /\ FINITE s /\ y IN s /\
     (!t. t IN s ==> nextc r t IN s)
     ==> LENGTH r <= CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. ITER k (nextc r) (y:A) IN s` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC[ITER]; ALL_TAC] THEN
  MATCH_MP_TAC PAIRWISE_LENGTH_LE_CARD THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:(A)list`; `y:A`] RING_CHAIN_COVERS) THEN ASM_REWRITE_TAC[]
    THEN
  DISCH_THEN(MP_TAC o SPEC `t:A`) THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[MEM_ITERLIST_IMP; ITER]);;

let RING_ADJ_NEXT = prove
 (`!(H:(A)hypermap) r u v.
     bridgeless H /\ chordless H r /\ PAIRWISE (\a b. ~(a = b)) r /\
     MEM u r /\ MEM v r /\ u IN dart H /\ adj H u v
     ==> ~(nextc r u = nextc r v) /\ (nextc r u = v \/ nextc r v = u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(u:A = v)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ADJ_NO_CFACE; CFACE_REFL]; ALL_TAC] THEN
  ASM_MESON_TAC[NEXTC_INJ; CHORDLESS_RING]);;

let XOR3_ARITH = prove
 (`!n i j k. 4 < n /\ i < n /\ j < n /\ k < n /\ ~(i = j) /\ ~(i = k)
   /\ ~(j = k)
     ==> ~((j = (i + 1) MOD n \/ i = (j + 1) MOD n) /\
           (k = (i + 1) MOD n \/ i = (k + 1) MOD n) /\
           (k = (j + 1) MOD n \/ j = (k + 1) MOD n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m. m < n ==> (m + 1) MOD n = (if m + 1 = n then 0 else m + 1)`
    (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[MOD_REFL]; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let EL_EQ_PAIRWISE = prove
 (`!(r:(A)list) i j. PAIRWISE (\a b. ~(a = b)) r /\ i < LENGTH r
   /\ j < LENGTH r
                    ==> (EL i r = EL j r <=> i = j)`,
  MESON_TAC[EL_PAIRWISE_INJ]);;

let NEXTC_XOR_3_EL = prove
 (`!(r:(A)list) i j k.
     PAIRWISE (\x y. ~(x = y)) r /\ 4 < LENGTH r /\
     i < LENGTH r /\ j < LENGTH r /\ k < LENGTH r /\
     ~(EL i r = EL j r) /\ ~(EL i r = EL k r) /\ ~(EL j r = EL k r) /\
     (EL j r = nextc r (EL i r) \/ EL i r = nextc r (EL j r)) /\
     (EL k r = nextc r (EL i r) \/ EL i r = nextc r (EL k r)) /\
     (EL k r = nextc r (EL j r) \/ EL j r = nextc r (EL k r))
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  SUBGOAL_THEN `~(LENGTH (r:(A)list) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NEXTC_EL; EL_EQ_PAIRWISE; MOD_LT_EQ] THEN
  MP_TAC(SPECL [`LENGTH (r:(A)list)`; `i:num`; `j:num`; `k:num`] XOR3_ARITH)
    THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let NEXTC_XOR_3 = prove
 (`!(r:(A)list) a b c.
     PAIRWISE (\x y. ~(x = y)) r /\ 4 < LENGTH r /\
     MEM a r /\ MEM b r /\ MEM c r /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     (b = nextc r a \/ a = nextc r b) /\ (c = nextc r a \/ a = nextc r c) /\
     (c = nextc r b \/ b = nextc r c)
     ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM_EXISTS_EL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) MP_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:(A)list`; `i:num`; `j:num`; `k:num`] NEXTC_XOR_3_EL) THEN
  ASM_REWRITE_TAC[]);;

let ADJ_CFACE2 = prove
 (`!(H:(A)hypermap) x1 x2 y1 y2.
     x1 IN dart H /\ y1 IN dart H /\ cface H x1 x2 /\ cface H y1 y2
       /\ adj H x1 y1
     ==> adj H x2 y2`,
  MESON_TAC[ADJ_CFACE; ADJ_CFACE_L]);;

let FCARD_ADJ_MAX = prove
 (`!(H:(A)hypermap) x y.
     minimal_counter_example H /\ x IN dart H /\ y IN dart H /\ ~cface H x y
     ==> fcard_face H {z | adj H y z /\ adj H x z} <= 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `adj H (x:A) y` THENL
   [ASM_SIMP_TAC[FCARD_ADJ_ADJ; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE] THEN
  MATCH_MP_TAC(ARITH_RULE `~(2 < n) ==> n <= 2`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP THREE_DISTINCT) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A->bool`; `b:A->bool`; `c:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:A` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z2:A` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z3:A` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)))
     THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  SUBGOAL_THEN `(z1:A) IN dart H /\ (z2:A) IN dart H /\ (z3:A) IN dart H`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC ADJ_DART THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~cface H (z1:A) z2 /\ ~cface H (z1:A) z3 /\ ~cface H (z2:A) z3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(a:A->bool = b)`; UNDISCH_TAC `~(a:A->bool = c)`;
      UNDISCH_TAC `~(b:A->bool = c)`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[ORBIT_EQ_CFACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `adj H (z1:A) z2 /\ adj H (z1:A) z3 /\ adj H (z2:A) z3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CROSS_ADJ THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] SPOKE_RING_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = spoke_ring (H:(A)hypermap) x` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?t1:A. MEM t1 r /\ cface H z1 t1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?t2:A. MEM t2 r /\ cface H z2 t2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?t3:A. MEM t3 r /\ cface H z3 t3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t1:A) IN dart H /\ (t2:A) IN dart H /\ (t3:A) IN dart H`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `adj H (t1:A) t2 /\ adj H (t1:A) t3 /\ adj H (t2:A) t3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC ADJ_CFACE2 THENL
     [MAP_EVERY EXISTS_TAC [`z1:A`; `z2:A`];
      MAP_EVERY EXISTS_TAC [`z1:A`; `z3:A`];
      MAP_EVERY EXISTS_TAC [`z2:A`; `z3:A`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t1:A = t2) /\ ~(t1:A = t3) /\ ~(t2:A = t3)`
  STRIP_ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `t1:A`; `t2:A`] RING_ADJ_NEXT)
    THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `t1:A`; `t3:A`] RING_ADJ_NEXT)
    THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `t2:A`; `t3:A`] RING_ADJ_NEXT)
    THEN
  MP_TAC(ISPECL [`r:(A)list`; `t1:A`; `t2:A`; `t3:A`] NEXTC_XOR_3) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The list form of triad: the face count of the definition (coloring.ml)    *)
(* is the length of the filtered orbit list (ORBIT_FILTER_CARD; off the      *)
(* darts both sides are at most 1).                                          *)
(* ------------------------------------------------------------------------- *)

let ORBIT_FILTER_CARD = prove
 (`!(H:(A)hypermap) (P:A->bool) x0.
     x0 IN dart H
     ==> LENGTH (FILTER P (orbit_list (face_map H) x0)) =
         CARD {z:A | z IN face H x0 /\ P z}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `set_of_list (FILTER P (orbit_list (face_map (H:(A)hypermap)) x0)) =
     {z:A | z IN face H x0 /\ P z}` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_FILTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN
    MP_TAC(ISPECL[`face_map (H:(A)hypermap)`; `dart H:A->bool`; `x0:A`;
                  `z:A`] MEM_ORBIT_LIST) THEN
    ASM_SIMP_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[face] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPEC `FILTER P (orbit_list (face_map (H:(A)hypermap)) x0)`
    HAS_SIZE_SET_OF_LIST) THEN
  REWRITE_TAC[HAS_SIZE] THEN
  SUBGOAL_THEN
    `PAIRWISE (\a b:A. ~(a = b)) (orbit_list (face_map (H:(A)hypermap)) x0)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORBIT_LIST THEN
    EXISTS_TAC `dart (H:(A)hypermap)` THEN
    ASM_SIMP_TAC[FINITE_DART; FACE_MAP_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN
    `PAIRWISE (\a b:A. ~(a = b))
              (FILTER P (orbit_list (face_map (H:(A)hypermap)) x0))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC PAIRWISE_FILTER_GEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let TRIAD_LIST = prove
 (`!(H:(A)hypermap) p x0.
     triad H p x0 <=>
     2 < LENGTH (FILTER (\y. fband H p (edge_map H y))
                        (orbit_list (face_map H) x0)) /\
     ~(!z. MEM z p ==> adj H x0 z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[triad] THEN
  ASM_CASES_TAC `(x0:A) IN dart H` THENL
   [ASM_SIMP_TAC[ORBIT_FILTER_CARD]; ALL_TAC] THEN
  SUBGOAL_THEN `face_map (H:(A)hypermap) x0 = x0` ASSUME_TAC THENL
   [MP_TAC(ISPEC `H:(A)hypermap` FACE_MAP_PERMUTES) THEN
    REWRITE_TAC[permutes] THEN STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `face (H:(A)hypermap) x0 = {x0}` ASSUME_TAC THENL
   [REWRITE_TAC[face] THEN MATCH_MP_TAC ORBIT_FIXED THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `orbit_list (face_map (H:(A)hypermap)) x0 = [x0:A]`
    ASSUME_TAC THENL
   [REWRITE_TAC[orbit_list] THEN
    SUBGOAL_THEN `orbit_size (face_map (H:(A)hypermap)) x0 = 1`
      SUBST1_TAC THENL
     [REWRITE_TAC[orbit_size; GSYM face] THEN ASM_REWRITE_TAC[CARD_SING];
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `1 - 1 = 0`; iterlist]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `~(2 < CARD {y:A | y IN {x0} /\ fband H p (edge_map H y)}) /\
     ~(2 < LENGTH (FILTER (\y:A. fband H p (edge_map H y)) [x0]))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `n <= 1 ==> ~(2 < n)`) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {x0:A}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN
        REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
        REWRITE_TAC[CARD_SING; LE_REFL]];
      REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN
      ARITH_TAC];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* triad_valid (contract.v): a sparse contract of size 4 with a triad has no *)
(* contract ring.  Such a ring p would be a 5-ring (contract_ring_max and    *)
(* the Birkhoff theorem) with a single face y0 on one side; all the contract *)
(* darts lie in fband p (else dropping one contract edge leaves a contract   *)
(* of size 3 for p), so the triad dart x0 has more than two common neighbour *)
(* faces with y0, contradicting fcard_adj_max.                               *)
(* ------------------------------------------------------------------------- *)

let SPARSE_CONS_IMP = prove
 (`!(H:(A)hypermap) x l. sparse H (CONS x l) ==> sparse H l`,
  REWRITE_TAC[sparse] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SUC i`; `SUC j`]) THEN
  ASM_REWRITE_TAC[LENGTH; EL; TL; LT_SUC]);;

let SPARSE_INSERTE_DART = prove
 (`!(H:(A)hypermap) cc. sparse H (insertE H cc) ==> ALL (\c. c IN dart H) cc`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; INSERTE_CLAUSES] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `1`] o REWRITE_RULE[sparse]) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `1 = SUC 0`; EL; HD; TL; LT_0; LT_SUC] THEN
    ASM_CASES_TAC `(h:A) IN dart H`
      THEN ASM_SIMP_TAC[MAP_FIX_OFFDART; CNODE_REFL];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SPARSE_CONS_IMP]]);;

let FCARD_FACE_SUBSET = prove
 (`!(H:(A)hypermap) s t. s SUBSET t /\ FINITE t
   ==> fcard_face H s <= fcard_face H t`,
  REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE] THEN
  MESON_TAC[CARD_SUBSET; IMAGE_SUBSET; FINITE_IMAGE]);;

let TRIAD_KEY = prove
 (`!(H:(A)hypermap) p y t.
     bridgeless H /\ y IN dart H /\ adj H y t /\ ~fband H p t
     ==> ?z. z IN dart H /\ cface H y z /\
             node_map H (face_map H (edge_map H z)) = z /\
             ~fband H p (face_map H (edge_map H z)) /\
             ~cface H y (face_map H (edge_map H z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[adj; rlink; GSYM cface] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  EXISTS_TAC `z:A` THEN REWRITE_TAC[edgeK] THEN CFACE_TAC[]);;

let LENGTH_FILTER_LT = prove
 (`!(x:A) l. MEM x l ==> LENGTH (FILTER (\c. ~(c = x)) l) < LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; FILTER; LENGTH] THEN
  ASM_CASES_TAC `h:A = x` THEN ASM_REWRITE_TAC[LENGTH; LT_SUC] THEN
  MP_TAC(ISPECL [`\c:A. ~(c = x)`; `t:(A)list`] LENGTH_FILTER)
    THEN ARITH_TAC);;

let P_CC = prove
 (`!(H:(A)hypermap) cc p z.
     minimal_counter_example H /\ sparse H (insertE H cc) /\ LENGTH cc = 4 /\
     contract_ring H cc p /\ LENGTH p = 5 /\ MEM z (insertE H cc)
     ==> fband H p z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTRACT_RING_FACTS) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `ALL (\c:A. c IN dart H) cc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SPARSE_INSERTE_DART]; ALL_TAC] THEN
  UNDISCH_TAC `MEM (z:A) (insertE H cc)` THEN REWRITE_TAC[MEM_INSERTE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z1:A) IN dart H /\ edge_map H (edge_map H z1) = z1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[RING_MEM_DART; PLAIN_EQ]; ALL_TAC] THEN
  ABBREV_TAC `cc1 = FILTER (\c:A. ~(c = z1)) cc` THEN
  SUBGOAL_THEN `LENGTH (cc1:(A)list) < 4` ASSUME_TAC THENL
   [EXPAND_TAC "cc1" THEN ASM_MESON_TAC[LENGTH_FILTER_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `contract_ring H cc1 (p:(A)list)` ASSUME_TAC THENL
   [REWRITE_TAC[contract_ring] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (t:A) p /\ MEM t (insertE H cc)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MEM_TL_IMP; LENGTH_EQ_NIL; ARITH_RULE `~(5 = 0)`]; ALL_TAC]
       THEN
    SUBGOAL_THEN `fband H p (t:A) /\ fband H p (edge_map H t)` STRIP_ASSUME_TAC
      THENL
     [ASM_SIMP_TAC[FBAND_MEM] THEN REWRITE_TAC[FBAND_MEM_IFF] THEN
      ASM_MESON_TAC[CYCLE_NEXTC_STEP; NEXTC_MEM; rlink; SCYCLE_CYCLE];
      ALL_TAC] THEN
    UNDISCH_TAC `MEM (t:A) (insertE H cc)` THEN REWRITE_TAC[MEM_INSERTE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))
      THEN
    ASM_CASES_TAC `u:A = z1` THENL
     [CFACE_TAC[];
      EXPAND_TAC "cc1" THEN REWRITE_TAC[MEM_INSERTE; MEM_FILTER] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc1:(A)list`;
    `p:(A)list`] CONTRACT_RING_MAX) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TRIAD_Y0 = prove
 (`!(H:(A)hypermap) p.
     minimal_counter_example H /\ ALL (\y. y IN dart H) p /\
     nontrivial_ring H 0 p /\ ~nontrivial_ring H 1 p
     ==> ?y0. y0 IN dart H /\ !t. adj H y0 t ==> fband H p t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP;
    TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
  SUBGOAL_THEN `?a:A. diskF H p a` (X_CHOOSE_TAC `a:A`) THENL
   [UNDISCH_TAC `nontrivial_ring H 0 (p:(A)list)`
     THEN ASM_SIMP_TAC[NONTRIVIAL0P] THEN
    REWRITE_TAC[IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b:A. b IN dart H /\ diskFC H p b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `nontrivial_ring H 0 (p:(A)list)`
     THEN ASM_SIMP_TAC[NONTRIVIAL0P] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[diskF; DISKN_SUBSET_DART]; ALL_TAC] THEN
  UNDISCH_TAC `~nontrivial_ring H 1 (p:(A)list)`
    THEN ASM_SIMP_TAC[NONTRIVIAL1P] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(a:A) IN dart H`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `p:(A)list`; `a:A`; `t:A`] TRIAD_KEY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)
      THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `face_map H (edge_map H (z:A))`] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[diskF]
      THEN MATCH_MP_TAC DISKN_NODE_BWD THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DISKF_CFACE; diskF];
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(b:A) IN dart H`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `p:(A)list`; `b:A`; `t:A`] TRIAD_KEY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)
      THEN
    MAP_EVERY EXISTS_TAC [`b:A`; `face_map H (edge_map H (z:A))`] THEN
    ASM_SIMP_TAC[diskFC; FACE_MAP_IN_DART; EDGE_MAP_IN_DART] THEN
    ASM_MESON_TAC[DISKN_NODE_FWD; DISKFC_CFACE; diskFC; FACE_MAP_IN_DART;
                  EDGE_MAP_IN_DART]]);;

let FBAND_ADJ_SUB = prove
 (`!(H:(A)hypermap) p y0 x.
     minimal_counter_example H /\ scycle H (rlink H) p
       /\ ALL (\y. y IN dart H) p /\
     LENGTH p = 5 /\ y0 IN dart H /\ (!t. adj H y0 t ==> fband H p t)
       /\ fband H p x
     ==> adj H y0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `y0:A`] SPOKE_RING_FACTS)
    THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = spoke_ring (H:(A)hypermap) y0` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[FBAND_IN_DART]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rlink (H:(A)hypermap)`;
    `r:(A)list`] SCYCLE_FCARD_FBAND) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rlink (H:(A)hypermap)`;
    `p:(A)list`] SCYCLE_FCARD_FBAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `fband H (r:(A)list)`; `fband H (p:(A)list)`]
    FCARD_FACE_PSUBSET) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  ASM_SIMP_TAC[FINITE_FBAND] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN dart H` ASSUME_TAC THENL
     [ASM_MESON_TAC[FBAND_IN_DART]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `y0:A`; `z:A`] FBAND_SPOKE_RING) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC FBAND_CFACE THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FBAND_IN_DART];
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `y0:A`; `x:A`] FBAND_SPOKE_RING) THEN
    ASM_REWRITE_TAC[]]);;

let ALL_FILTER_IMP = prove
 (`!P Q (l:(A)list). ALL P l ==> ALL P (FILTER Q l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; FILTER] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALL]);;

let TRIAD_VALID = prove
 (`!(H:(A)hypermap) cc x0 p.
     minimal_counter_example H /\ sparse H (insertE H cc) /\ LENGTH cc = 4 /\
     x0 IN dart H /\ triad H (insertE H cc) x0
     ==> ~contract_ring H cc p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTRACT_RING_FACTS) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`; `p:(A)list`] CONTRACT_RING_MAX)
    THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `cc:(A)list`;
    `p:(A)list`] SPARSE_CONTRACT_RING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (p:(A)list) <= 5` ASSUME_TAC
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (p:(A)list) = 5 /\ ~nontrivial_ring H 1 p`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `p:(A)list`
      (MATCH_MP BIRKHOFF (ASSUME `minimal_counter_example (H:(A)hypermap)`)))
        THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `LENGTH (p:(A)list) = 5` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `p:(A)list`] TRIAD_Y0) THEN ASM_REWRITE_TAC[]
    THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:A. fband H p x ==> adj H y0 x` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FBAND_ADJ_SUB THEN
    EXISTS_TAC `p:(A)list` THEN ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. MEM z (insertE H cc) ==> fband H p z` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P_CC THEN
    EXISTS_TAC `cc:(A)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `triad H (insertE H cc) (x0:A)` THEN REWRITE_TAC[TRIAD_LIST] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `cface H (x0:A) y0` THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x0:A`; `y0:A`; `z:A`] ADJ_CFACE_L) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x0:A`] SPOKE_RING_FACTS)
    THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `fl = FILTER (\t. fband H (insertE H cc) t) (spoke_ring H (x0:A))`
    THEN
  SUBGOAL_THEN `2 < LENGTH (fl:(A)list)` ASSUME_TAC THENL
   [EXPAND_TAC "fl" THEN
    REWRITE_TAC[spoke_ring; FILTER_MAP; LENGTH_MAP; LENGTH_FILTER_REVERSE] THEN
    UNDISCH_TAC `2 < LENGTH (FILTER (\y. fband H (insertE H cc) (edge_map H y))
                              (orbit_list (face_map H) (x0:A)))` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC FILTER_EQ_MEM
      THEN REWRITE_TAC[o_THM; spoke; FBAND_FACE_MAP_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_simple H (fl:(A)list)
    /\ ALL (\z. z IN dart H) fl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "fl" THEN
    ASM_SIMP_TAC[FACE_SIMPLE_FILTER; FACE_SIMPLE_SPOKE_RING; ALL_FILTER_IMP];
    ALL_TAC] THEN
  SUBGOAL_THEN `fband H (fl:(A)list) SUBSET {z | adj H y0 z
    /\ adj H x0 z}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC
     THEN
    SUBGOAL_THEN `(z:A) IN dart H` ASSUME_TAC THENL
     [MATCH_MP_TAC FBAND_IN_DART THEN EXISTS_TAC `fl:(A)list` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `fband H (fl:(A)list) z` THEN REWRITE_TAC[FBAND_MEM_IFF] THEN
    EXPAND_TAC "fl" THEN REWRITE_TAC[MEM_FILTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:A) IN dart H /\ adj H x0 t` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `adj H y0 (t:A)` ASSUME_TAC THENL
     [UNDISCH_TAC `fband H (insertE H cc) (t:A)`
       THEN REWRITE_TAC[FBAND_MEM_IFF] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `y0:A`; `t:A`; `u:A`] ADJ_CFACE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `y0:A`; `z:A`; `t:A`] ADJ_CFACE);
      MP_TAC(ISPECL [`H:(A)hypermap`; `x0:A`; `z:A`; `t:A`] ADJ_CFACE)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x0:A`; `y0:A`] FCARD_ADJ_MAX) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `fband H (fl:(A)list)`;
                 `{z:A | adj H y0 z /\ adj H x0 z}`] FCARD_FACE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `dart (H:(A)hypermap)` THEN
    REWRITE_TAC[FINITE_DART; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ADJ_DART THEN EXISTS_TAC `y0:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `fl:(A)list`] SIMPLE_FCARD_FBAND) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The contracted map (contract.v, contract_coloring): remove the edge of a  *)
(* contract dart x by two face Walkup steps, at x and then at edge x.        *)
(* ------------------------------------------------------------------------- *)

let FACE_WALKUP_COMPONENTS = prove
 (`!(H:(A)hypermap) z.
     z IN dart H
     ==> dart(face_walkup H z) = dart H DELETE z /\
         edge_map(face_walkup H z) = swap(z, edge_map H z) o edge_map H /\
         node_map(face_walkup H z) = swap(z, node_map H z) o node_map H /\
         face_map(face_walkup H z) =
           inverse(swap(z, node_map H z) o node_map H) o
           inverse(swap(z, edge_map H z) o edge_map H)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[face_walkup; PERMN_COMPONENTS]
    THEN
  MP_TAC(ISPECL [`permF (H:(A)hypermap)`; `z:A`] EDGE_WALKUP_COMPONENTS) THEN
  ASM_REWRITE_TAC[PERMF_COMPONENTS] THEN SIMP_TAC[]);;

let contract_walkup = new_definition
  `contract_walkup (H:(A)hypermap) (x:A) =
     face_walkup (face_walkup H x) (edge_map H x)`;;

let CW_G1 = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ x IN dart H
     ==> ~(edge_map H x = x) /\ edge_map H x IN dart H /\
         dart(face_walkup H x) = dart H DELETE x /\
         edge_map H x IN dart(face_walkup H x) /\
         edge_map(face_walkup H x) = swap(x, edge_map H x) o edge_map H /\
         node_map(face_walkup H x) = swap(x, node_map H x) o node_map H /\
         edge_map(face_walkup H x) (edge_map H x) = edge_map H x /\
         glink (face_walkup H x) (edge_map H x) (edge_map H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] FACE_WALKUP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PLAIN_NEQ; EDGE_MAP_IN_DART; IN_DELETE] THEN
  SUBGOAL_THEN `(swap(x,edge_map H x) o edge_map H) (edge_map H (x:A)) =
    edge_map H x`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[o_THM; PLAIN_EQ; swap]; ASM_REWRITE_TAC[glink]]);;

let CW_DART = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ x IN dart H
     ==> dart(contract_walkup H x) = (dart H DELETE x) DELETE (edge_map H x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[contract_walkup] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[FACE_WALKUP_COMPONENTS]);;

let CW_EDGE = prove
 (`!(H:(A)hypermap) x w.
     plain_hypermap H /\ x IN dart H /\ w IN dart H /\ ~(w = x)
       /\ ~(w = edge_map H x)
     ==> edge_map(contract_walkup H x) w = edge_map H w
       /\ edge_map H w IN dart H /\
         ~(edge_map H w = x) /\ ~(edge_map H w = edge_map H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `edge_map H w IN dart H /\ ~(edge_map H w = x) /\
                ~(edge_map H w = edge_map H (x:A))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EDGE_MAP_IN_DART; EDGEI; PLAIN_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[contract_walkup] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[FACE_WALKUP_COMPONENTS] THEN
  ASM_REWRITE_TAC[SWAP_REFL; I_O_ID; o_THM; swap]);;

let CW_PLANAR_CARD = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ x IN dart H
     ==> (planar_hypermap H ==> planar_hypermap (contract_walkup H x)) /\
         CARD(dart(contract_walkup H x)) + 2 = CARD(dart H)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[contract_walkup]
     THEN ASM_MESON_TAC[PLANAR_FACE_WALKUP]; ALL_TAC] THEN
  ASM_SIMP_TAC[CW_DART; CARD_DELETE; FINITE_DART; FINITE_DELETE; IN_DELETE]
    THEN
  SUBGOAL_THEN `2 <= CARD(dart(H:(A)hypermap))` MP_TAC THENL
   [MP_TAC(ISPECL [`{x:A, edge_map H x}`; `dart(H:(A)hypermap)`] CARD_SUBSET)
     THEN
    ASM_REWRITE_TAC[FINITE_DART; INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
      NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ARITH_TAC]);;

let CW_PLAIN = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ x IN dart H ==> plain_hypermap (contract_walkup H x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[plain_hypermap] THEN X_GEN_TAC `w:A` THEN
  ASM_SIMP_TAC[CW_DART; IN_DELETE] THEN STRIP_TAC THEN
  MATCH_MP_TAC ORBIT_SIZE_EQ_2
    THEN EXISTS_TAC `dart(contract_walkup (H:(A)hypermap) x)` THEN
  REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES] THEN
  ASM_SIMP_TAC[CW_DART; IN_DELETE] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `w:A`] CW_EDGE) THEN ASM_REWRITE_TAC[]
    THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `edge_map H (w:A)`] CW_EDGE) THEN
  ASM_SIMP_TAC[PLAIN_EQ; PLAIN_NEQ]);;

let ORBIT_SKIP_SIZE_LE = prove
 (`!(f:A->A) s z w.
     FINITE s /\ f permutes s /\ z IN s /\ w IN s /\ ~(w = z)
     ==> orbit_size (swap(z, f z) o f) w <= orbit_size f w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_size] THEN MATCH_MP_TAC CARD_SUBSET
    THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ORBIT_FINITE]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w2:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(w2:A = z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`swap(z:A, f z) o f`; `s DELETE (z:A)`; `w:A`] ORBIT_SUBSET)
     THEN
    ASM_SIMP_TAC[PERMUTES_SWAP_COMPOSE; IN_DELETE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[ORBIT_SKIP_MEMBER_EQ]);;

let CW_PRECUBIC = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ precubic H /\ x IN dart H
     ==> precubic (contract_walkup H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[precubic] THEN X_GEN_TAC `w:A` THEN
  ASM_SIMP_TAC[CW_DART; IN_DELETE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `orbit_size (node_map H) (w:A) <= 3` MP_TAC THENL
   [UNDISCH_TAC `precubic (H:(A)hypermap)` THEN REWRITE_TAC[precubic] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`node_map (face_walkup (H:(A)hypermap) x)`;
                 `dart (face_walkup (H:(A)hypermap) x)`; `edge_map H (x:A)`;
                   `w:A`]
    ORBIT_SKIP_SIZE_LE) THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`; `x:A`;
    `w:A`]
    ORBIT_SKIP_SIZE_LE) THEN
  MP_TAC(ISPECL [`face_walkup (H:(A)hypermap) x`; `edge_map H (x:A)`]
    FACE_WALKUP_COMPONENTS) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; IN_DELETE; contract_walkup]
    THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let G1_FACE_GLINK = prove
 (`!(H:(A)hypermap) z.
     z IN dart H /\ glink H z z
     ==> face_map(face_walkup H z) = swap(z, face_map H z) o face_map H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[face_walkup; PERMN_COMPONENTS] THEN
  MP_TAC(ISPECL [`permF (H:(A)hypermap)`; `z:A`] EDGE_MAP_GLINK_SKIP) THEN
  ASM_REWRITE_TAC[PERMF_COMPONENTS; GLINK_PERMF]);;

let G1_FACE_NONGLINK = prove
 (`!(H:(A)hypermap) z w.
     z IN dart H /\ ~glink H z z /\ w IN dart H /\ ~(w = z)
     ==> face_map(face_walkup H z) w =
         swap(face_map H z, face_map H (edge_map H z))
             (swap(z, face_map H z) (face_map H w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[face_walkup; PERMN_COMPONENTS] THEN
  MP_TAC(ISPECL [`permF (H:(A)hypermap)`; `z:A`;
    `w:A`] EDGE_WALKUP_AS_SWAP_SKIP) THEN
  ASM_REWRITE_TAC[PERMF_COMPONENTS; GLINK_PERMF]);;

let GLINK_FACE_FIX = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\ glink H x x
     ==> face_map H x = x`,
  REWRITE_TAC[glink] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[PLAIN_NEQ];
    CFACE_TAC[];
    ASM_MESON_TAC[]]);;

let ORBIT_MAP_CLOSED_INDUCT = prove
 (`!(f:A->A) P x. P x /\ (!y. P y ==> P (f y)) ==> !y. y IN orbit_map f x
   ==> P y`,
  REWRITE_TAC[ORBIT_MAP_ITER] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN ASM_SIMP_TAC[ITER]);;

let ORBIT_SWAP_OTHER = prove
 (`!(g:A->A) a b w.
     ~(a IN orbit_map g w) /\ ~(b IN orbit_map g w)
     ==> orbit_map (swap(a,b) o g) w = orbit_map g w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. ITER k (swap(a,b) o (g:A->A)) w = ITER k g w` ASSUME_TAC
    THENL
   [MATCH_MP_TAC ITER_AGREE THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `g (ITER k g (w:A)) IN orbit_map g w` MP_TAC THENL
     [REWRITE_TAC[ORBIT_MAP_ITER] THEN MESON_TAC[ITER]; ALL_TAC] THEN
    REWRITE_TAC[swap] THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; ORBIT_MAP_ITER] THEN ASM_MESON_TAC[]]);;

let ORBIT_SWAP_MERGE = prove
 (`!(g:A->A) s a b.
     FINITE s /\ g permutes s /\ a IN s /\ b IN s /\ ~(a = b)
       /\ ~(b IN orbit_map g a)
     ==> orbit_map (swap(a,b) o g) a = orbit_map g a UNION orbit_map g b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(b:A) IN orbit_map (swap(a,b) o g) a` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_MAP_MERGE_TRANSFER]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN REWRITE_TAC[SUBSET; IN_UNION]
    THENL
   [MATCH_MP_TAC ORBIT_MAP_CLOSED_INDUCT THEN REWRITE_TAC[IN_ORBIT_MAP_REFL]
     THEN
    X_GEN_TAC `y:A` THEN REWRITE_TAC[o_THM; swap] THEN STRIP_TAC THEN
    REPEAT COND_CASES_TAC
      THEN ASM_MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL];
    REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
      FORALL_AND_THM] THEN
    CONJ_TAC THEN
    (MATCH_MP_TAC ORBIT_MAP_CLOSED_INDUCT
      THEN ASM_REWRITE_TAC[IN_ORBIT_MAP_REFL] THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     (SUBGOAL_THEN `(g:A->A) y = swap(a,b) ((swap(a,b) o g) y)` SUBST1_TAC
       THENL
       [REWRITE_TAC[o_THM; SWAP_INVOLUTION]; ALL_TAC]) THEN
     (SUBGOAL_THEN `(swap(a,b) o (g:A->A)) y IN orbit_map (swap(a,b) o g) a`
       MP_TAC THENL
       [ASM_MESON_TAC[ORBIT_MAP_STEP]; ALL_TAC]) THEN
     REWRITE_TAC[swap] THEN REPEAT COND_CASES_TAC THEN
     ASM_MESON_TAC[IN_ORBIT_MAP_REFL])]);;

let G1_FACE_ORBIT_DEGEN = prove
 (`!(H:(A)hypermap) x w.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\ w IN dart H /\ ~(w = x)
       /\
     glink H x x
     ==> orbit_map (face_map (face_walkup H x)) w =
         (if cface H x w \/ cface H (edge_map H x) w
          then (orbit_map (face_map H) x UNION orbit_map (face_map H) (edge_map
            H x))
               DELETE x
          else orbit_map (face_map H) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `face_map H (x:A) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[GLINK_FACE_FIX]; ALL_TAC] THEN
  ASM_SIMP_TAC[G1_FACE_GLINK; SWAP_REFL; I_O_ID] THEN
  SUBGOAL_THEN `orbit_map (face_map H) (x:A) = {x}` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_FIXED]; ALL_TAC] THEN
  SUBGOAL_THEN `~((x:A) IN orbit_map (face_map H) (edge_map H x))` ASSUME_TAC
    THENL
   [REWRITE_TAC[CFACE_ORBIT] THEN
    ASM_MESON_TAC[BRIDGELESS_CFACE; CFACE_SYM_GEN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[cface; face; IN_SING] THEN COND_CASES_TAC THEN REWRITE_TAC[]
    THEN
  SUBGOAL_THEN `orbit_map (face_map H) (w:A) = orbit_map (face_map H) (edge_map
    H x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
    ASM_SIMP_TAC[FINITE_DART; FACE_MAP_PERMUTES; EDGE_MAP_IN_DART];
    UNDISCH_TAC `~((x:A) IN orbit_map (face_map H) (edge_map H x))`
      THEN SET_TAC[]]);;

let G1_FACE_ORBIT_MAIN = prove
 (`!(H:(A)hypermap) x w.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\ w IN dart H /\ ~(w = x)
       /\
     ~glink H x x
     ==> orbit_map (face_map (face_walkup H x)) w =
         (if cface H x w \/ cface H (edge_map H x) w
          then (orbit_map (face_map H) x UNION orbit_map (face_map H) (edge_map
            H x))
               DELETE x
          else orbit_map (face_map H) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(face_map H (x:A) = x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_GLINK_SELF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~((x:A) IN orbit_map (face_map H) (edge_map H x)) /\
    ~((face_map H (edge_map H x)) IN orbit_map (face_map H) x) /\
    ~(face_map H x = face_map H (edge_map H x)) /\
    ~(face_map H (edge_map H (x:A)) = x) /\
    face_map H x IN dart H /\ face_map H (edge_map H x) IN dart H`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CFACE_ORBIT] THEN CFACE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `g = swap(x:A, face_map H x) o face_map H` THEN
  SUBGOAL_THEN `(g:A->A) permutes (dart H DELETE x)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC PERMUTES_SWAP_COMPOSE THEN
    ASM_REWRITE_TAC[FACE_MAP_PERMUTES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN dart H /\ ~(y = x)
                      ==> orbit_map g y = orbit_map (face_map H) y DELETE x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN MATCH_MP_TAC ORBIT_SKIP_DELETE
     THEN
    EXISTS_TAC `dart (H:(A)hypermap)`
      THEN ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES];
    ALL_TAC] THEN
  ABBREV_TAC `a = face_map H (x:A)` THEN
  ABBREV_TAC `b = face_map H (edge_map H (x:A))` THEN
  SUBGOAL_THEN `orbit_map g (a:A) = orbit_map (face_map H) x DELETE x /\
                orbit_map g (b:A) = orbit_map (face_map H) (edge_map H x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `orbit_map g (a:A) = orbit_map (face_map H) a DELETE x`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
      EXISTS_TAC `dart(H:(A)hypermap)` THEN
      ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[CFACE_ORBIT; CFT_FACE];
      SUBGOAL_THEN `orbit_map g (b:A) = orbit_map (face_map H) b DELETE x`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `orbit_map (face_map H) (b:A) =
                    orbit_map (face_map H) (edge_map H x)` SUBST1_TAC THENL
       [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
        ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN EXPAND_TAC "b"
          THEN
        REWRITE_TAC[CFACE_ORBIT; CFT_FACE];
        UNDISCH_TAC `~((x:A) IN orbit_map (face_map H) (edge_map H x))` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((b:A) IN orbit_map g a) /\ (a:A) IN dart H DELETE x /\
                (b:A) IN dart H DELETE x` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `(swap(a,b) o (g:A->A)) permutes (dart H DELETE x)` ASSUME_TAC
    THENL
   [MATCH_MP_TAC PERMUTES_COMPOSE THEN ASM_SIMP_TAC[PERMUTES_SWAP]; ALL_TAC]
     THEN
  SUBGOAL_THEN `orbit_map (face_map (face_walkup H x)) (w:A) =
                orbit_map (swap(a,b) o g) w` SUBST1_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_EQ_AGREE THEN EXISTS_TAC `dart H DELETE (x:A)`
     THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `face_walkup (H:(A)hypermap) x` FACE_MAP_PERMUTES) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `y:A`] G1_FACE_NONGLINK) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `(w:A) IN orbit_map (swap(a,b) o g) a` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g:A->A`; `dart H DELETE (x:A)`; `a:A`; `b:A`]
        ORBIT_SWAP_MERGE) THEN
      ASM_REWRITE_TAC[FINITE_DELETE; FINITE_DART] THEN DISCH_THEN SUBST1_TAC
        THEN
      ASM_REWRITE_TAC[IN_UNION; IN_DELETE] THEN
      UNDISCH_TAC `cface H x w \/ cface H (edge_map H x) (w:A)` THEN
      REWRITE_TAC[cface; face] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `orbit_map (swap(a,b) o g) (w:A) = orbit_map (swap(a,b) o g)
      a`
    SUBST1_TAC THENL
     [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart H DELETE (x:A)` THEN
      ASM_REWRITE_TAC[FINITE_DELETE; FINITE_DART];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:A->A`; `dart H DELETE (x:A)`; `a:A`;
      `b:A`] ORBIT_SWAP_MERGE) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; FINITE_DART] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((x:A) IN orbit_map (face_map H) (edge_map H x))`
      THEN SET_TAC[];
    SUBGOAL_THEN `~((a:A) IN orbit_map (face_map H) w) /\
                  ~((b:A) IN orbit_map (face_map H) w)` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[CFACE_ORBIT] THEN
      CFACE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((a:A) IN orbit_map g w) /\ ~((b:A) IN orbit_map g w)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
    ASM_SIMP_TAC[ORBIT_SWAP_OTHER] THEN
    MATCH_MP_TAC(SET_RULE `~((x:A) IN s) ==> s DELETE x = s`) THEN
    REWRITE_TAC[CFACE_ORBIT] THEN CFACE_TAC[]]);;

let G1_FACE_ORBIT = prove
 (`!(H:(A)hypermap) x w.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\ w IN dart H /\ ~(w = x)
     ==> orbit_map (face_map (face_walkup H x)) w =
         (if cface H x w \/ cface H (edge_map H x) w
          then (orbit_map (face_map H) x UNION orbit_map (face_map H) (edge_map
            H x))
               DELETE x
          else orbit_map (face_map H) w)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `glink H (x:A) x` THEN
  ASM_SIMP_TAC[G1_FACE_ORBIT_DEGEN; G1_FACE_ORBIT_MAIN]);;

let CW_CFACE = prove
 (`!(H:(A)hypermap) x w w'.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     w IN dart H /\ ~(w = x) /\ ~(w = edge_map H x) /\
     w' IN dart H /\ ~(w' = x) /\ ~(w' = edge_map H x)
     ==> (cface (contract_walkup H x) w w' <=>
          (if cface H x w \/ cface H (edge_map H x) w
           then cface H x w' \/ cface H (edge_map H x) w' else cface H w w'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `face_walkup (H:(A)hypermap) x` FACE_MAP_PERMUTES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[contract_walkup] THEN
  GEN_REWRITE_TAC LAND_CONV [cface] THEN REWRITE_TAC[face] THEN
  SUBGOAL_THEN
   `face_map (face_walkup (face_walkup H x) (edge_map H x)) =
    swap(edge_map H x, face_map (face_walkup H x) (edge_map H (x:A))) o
    face_map (face_walkup H x)` SUBST1_TAC THENL
   [MATCH_MP_TAC G1_FACE_GLINK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`face_map (face_walkup (H:(A)hypermap) x)`;
    `dart H DELETE (x:A)`;
                 `edge_map H (x:A)`; `w:A`; `w':A`] ORBIT_SKIP_MEMBER_EQ) THEN
  ASM_REWRITE_TAC[FINITE_DART; FINITE_DELETE; IN_DELETE]
    THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `w:A`] G1_FACE_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_DELETE; IN_UNION; CFACE_ORBIT]);;

let CW_BRIDGELESS = prove
 (`!(H:(A)hypermap) x cc.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     (!p. ~contract_ring H (CONS x cc) p)
     ==> bridgeless (contract_walkup H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[bridgeless] THEN X_GEN_TAC `w:A` THEN
  ASM_SIMP_TAC[CW_DART; IN_DELETE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `w:A`] CW_EDGE) THEN ASM_REWRITE_TAC[]
    THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `w:A`; `edge_map H (w:A)`] CW_CFACE)
    THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THENL [ALL_TAC; CFACE_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `edge_map H (edge_map H (x:A)) = x /\ ~cface H w (edge_map H w)
    /\
                ~cface H x (edge_map H x)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PLAIN_EQ; BRIDGELESS_CFACE]; ALL_TAC] THEN
  SUBGOAL_THEN `?y:A. (y = x \/ y = edge_map H x) /\ cface H (edge_map H w) y
    /\
                      cface H (edge_map H y) w`
    (X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THENL
   [ASM_CASES_TAC `cface H x (edge_map H (w:A))` THENL
     [EXISTS_TAC `x:A`; EXISTS_TAC `edge_map H (x:A)`] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN dart H /\ ~(edge_map H w = y) /\ ~cface H w y`
  STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `[w:A; y]`) THEN
  REWRITE_TAC[contract_ring; scycle; list_cycle; NOT_CONS_NIL; LAST; list_path;
              face_simple; FBAND_CONS; FBAND_NIL; PROPER_TWO; TL; MEM;
              INSERTE_CLAUSES; rlink] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `y:A = x \/ y = edge_map H x` THEN MESON_TAC[]);;

let CW_CFACE_GROW = prove
 (`!(H:(A)hypermap) x w w'.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     w IN dart H /\ ~(w = x) /\ ~(w = edge_map H x) /\
     w' IN dart H /\ ~(w' = x) /\ ~(w' = edge_map H x) /\ cface H w w'
     ==> cface (contract_walkup H x) w w'`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CW_CFACE] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CFT_TRANS]);;

let CW_RLINK = prove
 (`!(H:(A)hypermap) x u v.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     u IN dart H /\ ~(u = x) /\ ~(u = edge_map H x) /\
     v IN dart H /\ ~(v = x) /\ ~(v = edge_map H x)
     ==> (rlink (contract_walkup H x) u v <=>
          (if cface H x (edge_map H u) \/ cface H (edge_map H x) (edge_map H u)
           then cface H x v \/ cface H (edge_map H x) v else rlink H u v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rlink] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `u:A`] CW_EDGE) THEN ASM_REWRITE_TAC[]
    THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `edge_map H (u:A)`; `v:A`] CW_CFACE)
    THEN
  ASM_REWRITE_TAC[]);;

let CW_FACE_SIMPLE = prove
 (`!(H:(A)hypermap) x p.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     ALL (\z. z IN dart H /\ ~(z = x) /\ ~(z = edge_map H x)) p /\
     face_simple (contract_walkup H x) p
     ==> face_simple H p`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[face_simple; ALL]
    THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `~fband (contract_walkup H x) t (h:A)`
    THEN REWRITE_TAC[FBAND_MEM_IFF] THEN
  MATCH_MP_TAC MONO_NOT THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)
    THEN
  EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CW_CFACE_GROW THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (\z. z IN dart H /\ ~(z = x)
    /\ ~(z = edge_map H x)) (t:(A)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
  ASM_REWRITE_TAC[]);;

let CW_PROPER = prove
 (`!(H:(A)hypermap) x p.
     plain_hypermap H /\ x IN dart H /\
     ALL (\z. z IN dart H /\ ~(z = x) /\ ~(z = edge_map H x)) p /\
     proper_ring (contract_walkup H x) p
     ==> proper_ring H p`,
  REWRITE_TAC[proper_ring] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (\z. z IN dart H /\ ~(z = x)
    /\ ~(z = edge_map H x)) (p:(A)list)` THEN
  ASM_REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `a:A`] CW_EDGE) THEN ASM_REWRITE_TAC[]
    THEN
  ASM_MESON_TAC[]);;

let INSERTE_CW = prove
 (`!(H:(A)hypermap) x cc2.
     plain_hypermap H /\ x IN dart H /\
     ALL (\c. c IN dart H /\ ~(c = x) /\ ~(c = edge_map H x)) cc2
     ==> insertE (contract_walkup H x) cc2 = insertE H cc2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[INSERTE_CLAUSES; ALL] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CW_EDGE]);;

let NEXTC_NEQ = prove
 (`!(r:(A)list) y.
     PAIRWISE (\a b. ~(a = b)) r /\ MEM y r /\ 2 <= LENGTH r
       ==> ~(nextc r y = y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:(A)list`; `y:A`; `{y:A}`] NEXTC_CLOSED_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_SING; IN_SING] THEN ASM_MESON_TAC[];
    REWRITE_TAC[CARD_SING] THEN ASM_ARITH_TAC]);;

let FACE_SIMPLE_SUBLIST = prove
 (`!(H:(A)hypermap) l m.
     face_simple H l /\ PAIRWISE (\a b. ~(a = b)) m /\
     (!t. MEM t m ==> MEM t l)
     ==> face_simple H m`,
  REWRITE_TAC[FACE_SIMPLE_EQ_PAIRWISE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PAIRWISE_FROM_MEM THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x y:A. ~cface H x y`; `l:(A)list`] PAIRWISE_SYM_MEM) THEN
  ASM_MESON_TAC[CFACE_SYM_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Contract rings of the contracted map lift to contract rings of x :: cc    *)
(* (contract.v, the `ring'cc2` step): either p is already an R-cycle of H,   *)
(* or exactly one R-link w0 -> w1 of p breaks and inserting x0 (the dart of  *)
(* {x, edge x} between them) and rotating to the head of p gives the ring.   *)
(* ------------------------------------------------------------------------- *)

let CONTRACT_RING_ROTATE = prove
 (`!(H:(A)hypermap) cc q y.
     scycle H (rlink H) q /\ 2 < LENGTH q /\ MEM y q /\
     (!z. MEM z q /\ ~(z = y) ==> MEM z (insertE H cc))
     ==> ?r. contract_ring H cc r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCYCLE_PAIRWISE) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:(A)list` (X_CHOOSE_THEN `b:(A)list`
    SUBST_ALL_TAC) o MATCH_MP MEM_SPLIT) THEN
  REWRITE_TAC[PAIRWISE_APPEND; PAIRWISE; GSYM ALL_MEM; MEM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM (y:A) a` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `rot_list (index_list (y:A) (APPEND a (CONS y b)))
                       (APPEND a (CONS y b))` THEN
  ASM_REWRITE_TAC[contract_ring; SCYCLE_ROT] THEN
  ASM_SIMP_TAC[ROT_TO_FRONT; TL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIZE_PROPER_RING THEN
    UNDISCH_TAC `2 < LENGTH (APPEND a (CONS (y:A) b))` THEN
    REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[MEM_APPEND; MEM]]);;

let MEM_INSERTE_CW_FILTER = prove
 (`!(H:(A)hypermap) x cc y.
     plain_hypermap H /\ x IN dart H /\ ALL (\c. c IN dart H) cc /\
     ~(y = x) /\ ~(y = edge_map H x)
     ==> (MEM y (insertE (contract_walkup H x)
                  (FILTER (\c. ~(c = x) /\ ~(c = edge_map H x)) cc)) <=>
          MEM y (insertE H (CONS x cc)))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INSERTE_CW o
    rand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_FILTER] THEN
    UNDISCH_TAC `ALL (\c:A. c IN dart H) cc` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INSERTE_CLAUSES; MEM; MEM_INSERTE; MEM_FILTER] THEN
  ASM_MESON_TAC[PLAIN_EQ]);;

let RING_TRANSFER = prove
 (`!(H:(A)hypermap) x cc p.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     ALL (\c. c IN dart H) cc /\
     contract_ring (contract_walkup H x)
                   (FILTER (\c. ~(c = x) /\ ~(c = edge_map H x)) cc) p
     ==> ?q. contract_ring H (CONS x cc) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTRACT_RING_FACTS) THEN
  SUBGOAL_THEN `~(p:(A)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `2 <= n ==> ~(n = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:A. MEM z p ==> z IN dart H /\ ~(z = x) /\ ~(z = edge_map H x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\z. z IN dart (contract_walkup H x)) (p:(A)list)` THEN
    ASM_SIMP_TAC[CW_DART; IN_DELETE; CONJ_ASSOC; GSYM ALL_MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. MEM z (TL p) ==> MEM z (insertE H (CONS x cc))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `MEM (z:A) p` ASSUME_TAC THENL
     [ASM_MESON_TAC[MEM_TL_IMP]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `cc:(A)list`; `z:A`]
      MEM_INSERTE_CW_FILTER) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_simple H (p:(A)list) /\ proper_ring H p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CW_FACE_SIMPLE; MATCH_MP_TAC CW_PROPER] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[GSYM ALL_MEM] THEN
    MATCH_MP_TAC SCYCLE_SIMPLE THEN
    EXISTS_TAC `rlink (contract_walkup (H:(A)hypermap) x)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `list_cycle (rlink H) (p:(A)list)` THENL
   [EXISTS_TAC `p:(A)list` THEN ASM_REWRITE_TAC[contract_ring; scycle];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w0:A. MEM w0 p /\ ~rlink H w0 (nextc p w0)` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[LIST_CYCLE_FROM_NEXTC]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (nextc p w0:A) p /\ ~(nextc p w0 = w0) /\
                prevc p (nextc p w0) = w0 /\
                rlink (contract_walkup H x) w0 (nextc p w0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NEXTC_MEM; PREVC_NEXTC; NEXTC_NEQ] THEN
    MATCH_MP_TAC CYCLE_NEXTC_STEP THEN REWRITE_TAC[ETA_AX] THEN
    FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP SCYCLE_CYCLE th]);
    ABBREV_TAC `w1 = nextc (p:(A)list) w0`] THEN
  SUBGOAL_THEN `(w0:A) IN dart H /\ ~(w0 = x) /\ ~(w0 = edge_map H x) /\
                (w1:A) IN dart H /\ ~(w1 = x) /\ ~(w1 = edge_map H x)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `w0:A`] CW_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(cface H x (edge_map H w0) \/ cface H (edge_map H x) (edge_map H w0)) /\
    (cface H x w1 \/ cface H (edge_map H x) (w1:A))`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `w0:A`; `w1:A`] CW_RLINK) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x0:A. (x0 = x \/ x0 = edge_map H x) /\
                       cface H (edge_map H w0) x0 /\
                       cface H w1 (edge_map H x0)`
  (X_CHOOSE_THEN `x0:A` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THENL
   [ASM_CASES_TAC `cface H x (edge_map H (w0:A))` THENL
     [EXISTS_TAC `x:A`; EXISTS_TAC `edge_map H (x:A)`] THEN
    CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:A. MEM u p /\ ~(u = w1) ==> ~(cface H x u \/ cface H (edge_map H x) u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u:A) IN dart H /\ ~(u = x) /\ ~(u = edge_map H x)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `w1:A`; `u:A`] CW_CFACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_MESON_TAC[SCYCLE_CFACE_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`contract_walkup (H:(A)hypermap) x`; `p:(A)list`; `w1:A`]
    RING_ROTATE_TO2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(A)list` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  SUBGOAL_THEN `(!t:A. MEM t (CONS w1 r1) <=> MEM t p) /\
                (!t:A. MEM t r1 ==> MEM t p /\ ~(t = w1)) /\ ~(r1 = [])`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `PAIRWISE (\a b:A. ~(a = b)) (CONS w1 r1)` THEN
    UNDISCH_TAC `LAST (CONS (w1:A) r1) = w0` THEN
    ASM_REWRITE_TAC[PAIRWISE; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[MEM; LAST];
    ALL_TAC] THEN
  SUBGOAL_THEN `list_path (rlink H) w1 (r1:(A)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC LIST_PATH_MONO THEN
    EXISTS_TAC `rlink (contract_walkup (H:(A)hypermap) x)` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `a:A`; `b:A`] CW_RLINK) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTRACT_RING_ROTATE THEN
  MAP_EVERY EXISTS_TAC [`CONS (x0:A) (CONS w1 r1)`; `HD (p:(A)list)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[scycle] THEN CONJ_TAC THENL
     [REWRITE_TAC[list_cycle; NOT_CONS_NIL] THEN
      ASM_REWRITE_TAC[LAST; NOT_CONS_NIL; list_path; rlink] THEN CFACE_TAC[];
      ONCE_REWRITE_TAC[face_simple] THEN CONJ_TAC THENL
       [REWRITE_TAC[FBAND_CONS; FBAND_MEM_IFF; DE_MORGAN_THM] THEN
        CONJ_TAC THENL
         [CFACE_TAC[];
          DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `MEM (u:A) p /\ ~(u = w1)` STRIP_ASSUME_TAC THENL
           [ASM_MESON_TAC[]; ALL_TAC] THEN
          CFACE_TAC[]];
        MATCH_MP_TAC FACE_SIMPLE_SUBLIST THEN EXISTS_TAC `p:(A)list` THEN
        ASM_MESON_TAC[]]];
    REWRITE_TAC[LENGTH] THEN UNDISCH_TAC `~(r1:(A)list = [])` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
    ASM_MESON_TAC[MEM; HD_MEM];
    REWRITE_TAC[MEM] THEN X_GEN_TAC `t:A` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[INSERTE_CLAUSES; MEM] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[MEM_HD_TL; MEM];
      ASM_MESON_TAC[MEM_HD_TL; MEM]]]);;

(* ------------------------------------------------------------------------- *)
(* Lifting a contract colouring of the contracted map back to H (the `k0`    *)
(* construction of contract.v): a dart of H takes the colour of any dart of  *)
(* the contracted map in its face, Color0 if there is none; CW_AE0 is the    *)
(* precubic argument that x and edge x then both have no such dart.          *)
(* ------------------------------------------------------------------------- *)

let CFACE_COLOR_EQ = prove
 (`!(G:(A)hypermap) (k:A->color) a b.
     (!z. z IN dart G ==> k (face_map G z) = k z) /\ a IN dart G /\ cface G a b
     ==> k b = k a`,
  REWRITE_TAC[cface; face] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`face_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`;
    `k:A->color`;
                 `a:A`; `b:A`] ORBIT_INVARIANT) THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES]);;

let MEM_INSERTE_CW = prove
 (`!(H:(A)hypermap) x cc y.
     plain_hypermap H /\ x IN dart H /\ y IN dart H /\ ~(y = x)
       /\ ~(y = edge_map H x)
     ==> (MEM y (insertE H (FILTER (\c. ~(c = x) /\ ~(c = edge_map H x)) cc))
       <=>
          MEM y (insertE H (CONS x cc)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `edge_map H (edge_map H (x:A)) = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PLAIN_EQ]; ALL_TAC] THEN
  REWRITE_TAC[INSERTE_CLAUSES; MEM; MEM_INSERTE; MEM_FILTER]
    THEN ASM_MESON_TAC[]);;

let CW_AE0 = prove
 (`!(H:(A)hypermap) x y.
     plain_hypermap H /\ bridgeless H /\ precubic H /\ x IN dart H
       /\ y IN dart H /\
     ~(?w. ((w IN dart H /\ ~(w = x)) /\ ~(w = edge_map H x)) /\ cface H y w)
     ==> ~(?w. ((w IN dart H /\ ~(w = x)) /\ ~(w = edge_map H x)) /\
               cface H (edge_map H y) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `edge_map H (edge_map H (x:A)) = x /\ edge_map H (edge_map H (y:A)) = y /\
    edge_map H y IN dart H /\ face_map H y IN dart H /\ node_map H y IN dart H
      /\
    ~(edge_map H x = x) /\ ~(edge_map H y = y) /\ ~cface H y (edge_map H y) /\
    edge_map H x IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PLAIN_EQ; PLAIN_NEQ; EDGE_MAP_IN_DART; FACE_MAP_IN_DART;
                 NODE_MAP_IN_DART; BRIDGELESS_CFACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A = x \/ y = edge_map H x) /\
                (face_map H y = x \/ face_map H y = edge_map H x)`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THENL
   [UNDISCH_TAC `~(?w. ((w IN dart H /\ ~(w = x)) /\ ~(w = edge_map H x)) /\
                       cface H (y:A) w)` THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(fun th ->
      MP_TAC(SPEC `face_map H (y:A)` th) THEN MP_TAC(SPEC `y:A` th)) THEN
    ASM_REWRITE_TAC[CFACE_REFL; CFT_FACE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map H (y:A) = y` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map H (y:A) = edge_map H y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `y:A`] faceK) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `edge_map (H:(A)hypermap)`) THEN
    ASM_SIMP_TAC[PLAIN_EQ] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `~(edge_map H y IN dart H /\ ~(edge_map H y = x) /\
                  ~(edge_map H (y:A) = edge_map H x))` ASSUME_TAC THENL
   [UNDISCH_TAC `y:A = x \/ y = edge_map H x` THEN ASM_MESON_TAC[]; ALL_TAC]
     THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`; `y:A`]
    ITER_ORBIT_SIZE) THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`; `y:A`]
    ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN DISCH_TAC THEN DISCH_TAC
    THEN
  SUBGOAL_THEN `orbit_size (node_map H) (y:A) <= 3` ASSUME_TAC THENL
   [UNDISCH_TAC `precubic (H:(A)hypermap)` THEN REWRITE_TAC[precubic] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `orbit_size (node_map H) (y:A) = 1
    \/ orbit_size (node_map H) y = 2 \/
                orbit_size (node_map H) y = 3` MP_TAC
                  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `ITER (orbit_size (node_map H) (y:A)) (node_map H) y = y` THEN
  DISCH_THEN(fun th -> DISCH_THEN(DISJ_CASES_THEN2 (fun e ->
    MP_TAC(REWRITE_RULE[e] th))
    (DISJ_CASES_THEN2 (fun e -> MP_TAC(REWRITE_RULE[e] th))
                      (fun e -> MP_TAC(REWRITE_RULE[e] th))))) THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; ITER; ITER2; ITER3] THENL
   [ASM_MESON_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `node_map H (edge_map H (y:A)) = y` ASSUME_TAC THENL
     [UNDISCH_TAC `node_map H (node_map H (y:A)) = y`
       THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `face_map H (edge_map H (y:A)) = edge_map H y` ASSUME_TAC
      THENL
     [MATCH_MP_TAC(ISPEC `H:(A)hypermap` NODEI) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `edge_map H (y:A)`] faceK) THEN
      DISCH_THEN(MP_TAC o AP_TERM `edge_map (H:(A)hypermap)`) THEN
      ASM_SIMP_TAC[PLAIN_EQ; NODE_MAP_IN_DART; FACE_MAP_IN_DART;
        EDGE_MAP_IN_DART];
      ALL_TAC] THEN
    UNDISCH_TAC `cface H (edge_map H y) (w:A)` THEN
    REWRITE_TAC[cface; face] THEN ASM_SIMP_TAC[ORBIT_FIXED; IN_SING] THEN
    UNDISCH_TAC `y:A = x \/ y = edge_map H x` THEN ASM_MESON_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `node_map H (node_map H (edge_map H (y:A))) = y` ASSUME_TAC
      THENL
     [UNDISCH_TAC `node_map H (node_map H (node_map H (y:A))) = y` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `face_map H (edge_map H (y:A)) = node_map H (edge_map H y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPEC `H:(A)hypermap` NODEI) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `edge_map H (y:A)`] faceK) THEN
      DISCH_THEN(MP_TAC o AP_TERM `edge_map (H:(A)hypermap)`) THEN
      ASM_SIMP_TAC[PLAIN_EQ; NODE_MAP_IN_DART; FACE_MAP_IN_DART;
        EDGE_MAP_IN_DART];
      ALL_TAC] THEN
    CFACE_TAC[]]);;

let CW_COLOR_LIFT = prove
 (`!(H:(A)hypermap) x cc k.
     plain_hypermap H /\ bridgeless H /\ precubic H /\ x IN dart H /\
     ALL (\c. c IN dart H) cc /\
     cc_coloring (contract_walkup H x)
                 (FILTER (\c. ~(c = x) /\ ~(c = edge_map H x)) cc) k
     ==> cc_colorable H (CONS x cc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `cc2 = FILTER (\c:A. ~(c = x) /\ ~(c = edge_map H x)) cc` THEN
  UNDISCH_TAC `cc_coloring (contract_walkup H x) cc2 (k:A->color)` THEN
  REWRITE_TAC[cc_coloring] THEN ASM_SIMP_TAC[CW_DART; IN_DELETE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!a b:A. ((a IN dart H /\ ~(a = x)) /\ ~(a = edge_map H x)) /\
            ((b IN dart H /\ ~(b = x)) /\ ~(b = edge_map H x)) /\ cface H a b
            ==> (k:A->color) b = k a`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CFACE_COLOR_EQ THEN
    EXISTS_TAC `contract_walkup (H:(A)hypermap) x` THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `!z. (z IN dart H /\ ~(z = x)) /\ ~(z = edge_map H x)
                  ==> (k:A->color) (face_map (contract_walkup H x) z) = k z`
                    THEN
      ASM_SIMP_TAC[CW_DART; IN_DELETE];
      ASM_SIMP_TAC[CW_DART; IN_DELETE];
      MATCH_MP_TAC CW_CFACE_GROW THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:A. ((y IN dart H /\ ~(y = x)) /\ ~(y = edge_map H x))
          ==> ((k:A->color) (edge_map H y) = k y
            <=> MEM y (insertE H (CONS x cc)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `y:A`] CW_EDGE)
      THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `cc:(A)list`; `y:A`] MEM_INSERTE_CW)
      THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `insertE (contract_walkup H x) (cc2:(A)list) = insertE H cc2`
    MP_TAC THENL
     [MATCH_MP_TAC INSERTE_CW THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "cc2" THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
      UNDISCH_TAC `ALL (\c:A. c IN dart H) cc` THEN REWRITE_TAC[GSYM ALL_MEM]
        THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!z. (z IN dart H /\ ~(z = x)) /\ ~(z = edge_map H x)
                     ==> ((k:A->color) (edge_map (contract_walkup H x) z) = k z
                       <=>
                          MEM z (insertE (contract_walkup H x) cc2))` THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cc_colorable; cc_coloring] THEN
  ABBREV_TAC `k0 = \y:A. if ?w. ((w IN dart H /\ ~(w = x))
    /\ ~(w = edge_map H x)) /\
                                cface H y w
                         then (k:A->color)
                                (@w. ((w IN dart H /\ ~(w = x))
                                  /\ ~(w = edge_map H x)) /\
                                     cface H y w)
                         else Color0` THEN
  EXISTS_TAC `k0:A->color` THEN
  SUBGOAL_THEN
   `!y w:A. ((w IN dart H /\ ~(w = x)) /\ ~(w = edge_map H x)) /\ cface H y w
            ==> (k0:A->color) y = k w`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "k0" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `?w:A. ((w IN dart H /\ ~(w = x)) /\ ~(w = edge_map H x)) /\
                        cface H y w`
      (fun th -> REWRITE_TAC[th] THEN MP_TAC(SELECT_RULE th)) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `w' = @w:A. ((w IN dart H /\ ~(w = x)) /\ ~(w = edge_map H x))
      /\
                           cface H y w` THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cface H y (w':A)` THEN UNDISCH_TAC `cface H y (w:A)` THEN
    MESON_TAC[CFACE_SYM_GEN; CFT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. (k0:A->color) (face_map H y) = k0 y` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "k0" THEN REWRITE_TAC[CFACE_FACE_L]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. ((y IN dart H /\ ~(y = x)) /\ ~(y = edge_map H x))
                      ==> (k0:A->color) y = k y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CFACE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k0:A->color) x = k0 (edge_map H x)` ASSUME_TAC THENL
   [ASM_CASES_TAC `?w:A. ((w IN dart H /\ ~(w = x)) /\ ~(w = edge_map H x)) /\
                         cface H x w` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?w1:A. ((w1 IN dart H /\ ~(w1 = x))
        /\ ~(w1 = edge_map H x)) /\
                           cface H (edge_map H x) w1`
        (X_CHOOSE_THEN `w1:A` STRIP_ASSUME_TAC) THENL
       [MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `edge_map H (x:A)`] CW_AE0) THEN
        ASM_SIMP_TAC[PLAIN_EQ] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(k0:A->color) x = (k:A->color) w
        /\ k0 (edge_map H x) = k w1`
        (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC
         THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CFACE_COLOR_EQ
        THEN EXISTS_TAC `contract_walkup (H:(A)hypermap) x` THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `!z. (z IN dart H /\ ~(z = x)) /\ ~(z = edge_map H x)
                  ==> (k:A->color) (face_map (contract_walkup H x) z) = k z`
                    THEN
        ASM_SIMP_TAC[CW_DART; IN_DELETE];
        ASM_SIMP_TAC[CW_DART; IN_DELETE];
        MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `w1:A`; `w:A`] CW_CFACE) THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `~(?w:A. ((w IN dart H /\ ~(w = x)) /\ ~(w = edge_map H x))
        /\
                            cface H (edge_map H x) w)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `x:A`] CW_AE0)
         THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "k0" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(y:A = x) \/ (y = edge_map H x)` THENL
   [SUBGOAL_THEN `MEM (y:A) (insertE H (CONS x cc))` (fun th ->
     REWRITE_TAC[th]) THENL
     [REWRITE_TAC[INSERTE_CLAUSES; MEM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_SIMP_TAC[PLAIN_EQ];
    SUBGOAL_THEN `(y IN dart H /\ ~(y = x))
      /\ ~(y = edge_map H (x:A))` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `y:A`] CW_EDGE)
      THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(k0:A->color) (edge_map H y) = k (edge_map H y)
      /\ k0 y = k y`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC
       THEN ASM_REWRITE_TAC[CFACE_REFL];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* contract_coloring (contract.v): induction on the size of the contract,    *)
(* over all planar bridgeless plain precubic maps with fewer darts than the  *)
(* minimal counter-example (which are 4-colourable), then the main theorem.  *)
(* ------------------------------------------------------------------------- *)

let CONTRACT_COLORING_IND = prove
 (`!n nG (G:(A)hypermap) cc.
     planar_hypermap G /\ bridgeless G /\ plain_hypermap G /\ precubic G /\
     (!G':(A)hypermap. planar_hypermap G' /\ bridgeless G' /\ plain_hypermap G'
       /\
                       precubic G' /\ CARD(dart G') < nG ==> four_colorable G')
                         /\
     ALL (\c. c IN dart G) cc /\ LENGTH cc <= n /\
     CARD(dart G) < (if cc = [] then 0 else 1) + nG /\
     (!p. ~contract_ring G cc p)
     ==> cc_colorable G cc`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `cc:(A)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `cc':(A)list` SUBST1_TAC))) THEN
  REWRITE_TAC[LENGTH; NOT_CONS_NIL; ADD_CLAUSES; ALL] THEN STRIP_TAC THENL
   [REWRITE_TAC[CC_COLORABLE_NIL] THEN FIRST_X_ASSUM MATCH_MP_TAC
     THEN ASM_REWRITE_TAC[];
    ASM_ARITH_TAC;
    REWRITE_TAC[CC_COLORABLE_NIL] THEN FIRST_X_ASSUM MATCH_MP_TAC
      THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cc2 = FILTER (\c:A. ~(c = x) /\ ~(c = edge_map G x)) cc'` THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `x:A`] CW_G1) THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `x:A`] CW_PLANAR_CARD) THEN ASM_REWRITE_TAC[]
    THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!p. ~contract_ring (contract_walkup G x) (cc2:(A)list) p`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `x:A`; `cc':(A)list`;
      `p:(A)list`] RING_TRANSFER) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL [`nG:num`; `contract_walkup (G:(A)hypermap) x`;
                                  `cc2:(A)list`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC CW_BRIDGELESS THEN EXISTS_TAC `cc':(A)list`
        THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CW_PLAIN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CW_PRECUBIC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "cc2" THEN REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
      X_GEN_TAC `c:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[CW_DART; IN_DELETE] THEN
      UNDISCH_TAC `ALL (\c:A. c IN dart G) cc'` THEN REWRITE_TAC[GSYM ALL_MEM]
        THEN
      DISCH_THEN(MP_TAC o SPEC `c:A`) THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "cc2" THEN
      MP_TAC(ISPECL [`\c:A. ~(c = x) /\ ~(c = edge_map G x)`; `cc':(A)list`]
        LENGTH_FILTER) THEN
      ASM_ARITH_TAC;
      COND_CASES_TAC THEN ASM_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_TAC `k:A->color` o REWRITE_RULE[cc_colorable]) THEN
    MATCH_MP_TAC CW_COLOR_LIFT THEN EXISTS_TAC `k:A->color`
      THEN ASM_REWRITE_TAC[]]);;

let CONTRACT_COLORING = prove
 (`!(H:(A)hypermap) r cc.
     minimal_counter_example H /\ valid_contract H r cc
     ==> cc_colorable H cc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MCE_PROPS) THEN
  SUBGOAL_THEN `sparse H (insertE H (cc:(A)list)) /\ 1 <= LENGTH cc
    /\ LENGTH cc <= 4 /\
    (LENGTH cc = 4 ==> ?x0. x0 IN kernel H r /\ triad H (insertE H cc) x0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `valid_contract (H:(A)hypermap) r cc` THEN
    REWRITE_TAC[valid_contract] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. ~contract_ring (H:(A)hypermap) cc p` ASSUME_TAC THENL
   [ASM_CASES_TAC `LENGTH (cc:(A)list) = 4` THENL
     [UNDISCH_TAC `LENGTH (cc:(A)list) = 4
                   ==> ?x0. x0 IN kernel H r /\ triad H (insertE H cc) x0` THEN
      ASM_REWRITE_TAC[IN_KERNEL] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN GEN_TAC THEN
      MATCH_MP_TAC TRIAD_VALID THEN EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC CONTRACT3_VALID THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\c:A. c IN dart H) cc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SPARSE_INSERTE_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`LENGTH (cc:(A)list)`; `CARD(dart(H:(A)hypermap))`;
    `H:(A)hypermap`;
                 `cc:(A)list`] CONTRACT_COLORING_IND) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `minimal_counter_example (H:(A)hypermap)` THEN
    REWRITE_TAC[minimal_counter_example] THEN SIMP_TAC[];
    SUBGOAL_THEN `~(cc:(A)list = [])` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `1 <= LENGTH ([]:(A)list)` THEN
      REWRITE_TAC[LENGTH; ARITH];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;
