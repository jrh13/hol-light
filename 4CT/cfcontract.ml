(* ========================================================================= *)
(* 4CT/cfcontract.ml                                                         *)
(*                                                                           *)
(* cfcontract.v: contracts of configuration maps.  cfctr mr mc cp computes   *)
(* the construction program of the map obtained by contracting the edges     *)
(* selected by the masks mr (ring) and mc (kernel transversal ctrenum cp).   *)
(* CFCTR_CORRECT (cfctr_correct) shows that every contract colouring induces *)
(* a colouring of the contracted map, SPARSE_CFCTR_ALL and VALID_CFCTR_CC    *)
(* (sparse_cfctr) that the contract is sparse and off the ring, CPMASK_ADJ   *)
(* and CTRBAND_CORRECT (cfmap.v cpmask_adj, ctrband_correct) relate face     *)
(* masks to adjacency, the cptriad check of valid_ctrm yields the triad      *)
(* clause of valid_contract (CP_TRIAD_EXTRACT), and CONTRACT_CTREEP          *)
(* (contract_ctreeP) packages everything for cfreducible.ml: a successful    *)
(* contract_ctree gives a valid contract whose ctree holds the traces of all *)
(* contract colourings.  The dart carrier is :num and the old-dart           *)
(* injections icpY/icpH are the identity (as in cfmap.ml).  The inductions   *)
(* over the program for cfctr_correct (ctr_correct) and sparse_cfctr         *)
(* (ctr_sparse) reduce each Y and H step to facts about the new darts of     *)
(* ecpY G x0 and ecpH G x0 (CC_ECPY_APEX, CC_ECPH_APEX, SPARSE_ECPY_NEW,     *)
(* SPARSE_ECPH_NEW) and to the colouring extensions of the contracted map.   *)
(* ========================================================================= *)

needs "4CT/cpcolor_correct.ml";;
needs "4CT/embed_contract.ml";;

(* ------------------------------------------------------------------------- *)
(* List utilities: masks and rotations                                       *)
(* ------------------------------------------------------------------------- *)

let mask_list = define
 `(mask_list [] s = ([]:A list)) /\
  (mask_list (CONS b m) s =
     if s = [] then [] else if b then CONS (HD s) (mask_list m (TL s)) else
       mask_list m (TL s))`;;

let MASK_LIST_CLAUSES = prove
 (`(!s:A list. mask_list [] s = []) /\
   (!b m. mask_list (CONS b m) ([]:A list) = []) /\
   (!m x s:A list. mask_list (CONS T m) (CONS x s) = CONS x (mask_list m s)) /\
   (!m x s:A list. mask_list (CONS F m) (CONS x s) = mask_list m s)`,
  REWRITE_TAC[mask_list; NOT_CONS_NIL; HD; TL]);;

let MEM_MASK_LIST = prove
 (`!m s x:A. MEM x (mask_list m s) ==> MEM x s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MASK_LIST_CLAUSES; MEM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `s:A list` list_CASES) THEN
  BOOL_CASES_TAC `h:bool` THEN
  ASM_REWRITE_TAC[MASK_LIST_CLAUSES; MEM] THEN ASM_MESON_TAC[]);;

let LENGTH_MASK_LIST_EQ = prove
 (`!m s:A list. LENGTH m = LENGTH s ==> LENGTH(mask_list m s) = LENGTH(FILTER
   (\b. b) m)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MASK_LIST_CLAUSES; LENGTH; FILTER] THEN
    GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `s:A list` list_CASES) THEN REWRITE_TAC[LENGTH;
    NOT_SUC; SUC_INJ] THEN
  BOOL_CASES_TAC `h:bool` THEN ASM_SIMP_TAC[MASK_LIST_CLAUSES; LENGTH]);;

let MASK_LIST_APPEND = prove
 (`!m1 s1 m2 s2:A list. LENGTH m1 = LENGTH s1
     ==> mask_list (APPEND m1 m2) (APPEND s1 s2) = APPEND (mask_list m1 s1)
       (mask_list m2 s2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MASK_LIST_CLAUSES; LENGTH; APPEND] THEN
    GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `s1:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; APPEND] THEN
  BOOL_CASES_TAC `h:bool` THEN ASM_SIMP_TAC[MASK_LIST_CLAUSES; APPEND]);;

let MASK_LIST_ALL_T = prove
 (`!(l:A list) m. ALL (\b. b) m /\ LENGTH m = LENGTH l ==> mask_list m l = l`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MASK_LIST_CLAUSES; LENGTH; ALL] THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  BOOL_CASES_TAC `h:bool` THEN ASM_SIMP_TAC[MASK_LIST_CLAUSES]);;

let MASK_LIST_REPLICATE_F = prove
 (`!n (l:A list). mask_list (REPLICATE n F) l = []`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; MASK_LIST_CLAUSES] THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
    ASM_REWRITE_TAC[MASK_LIST_CLAUSES]);;

let MASK_LIST_REPLICATE_T = prove
 (`!l:A list. mask_list (REPLICATE (LENGTH l) T) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; REPLICATE; MASK_LIST_CLAUSES]);;

let LENGTH_ROTR_LIST = prove
 (`!n l:A list. LENGTH(rotr_list n l) = LENGTH l`,
  REWRITE_TAC[rotr_list; LENGTH_ROT_LIST]);;

let ROT_LIST_ROTR_CANCEL_GEN = prove
 (`!i l:A list. rot_list i (rotr_list i l) = l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rotr_list] THEN
  ASM_CASES_TAC `i <= LENGTH(l:A list)` THENL
   [MP_TAC(ISPECL [`i:num`; `LENGTH(l:A list) - i`; `l:A list`]
      ROT_LIST_ADD) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC ROT_LIST_ALL THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `LENGTH(l:A list) - i = 0` SUBST1_TAC THENL [ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ROT_LIST_0] THEN MATCH_MP_TAC ROT_LIST_ALL THEN
      ASM_ARITH_TAC]);;

let MASK_LIST_ROT = prove
 (`!n m s:A list. LENGTH m = LENGTH s
     ==> mask_list (rot_list n m) (rot_list n s) =
         rot_list (LENGTH(FILTER (\b. b) (take_list n m))) (mask_list m s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(take_list n (m:bool list)) = LENGTH(take_list n (s:A
    list)) /\
                LENGTH(drop_list n (m:bool list)) = LENGTH(drop_list n (s:A
                  list))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_TAKE_LIST; LENGTH_DROP_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `mask_list m (s:A list) =
                APPEND (mask_list (take_list n m) (take_list n s))
                       (mask_list (drop_list n m) (drop_list n s))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`take_list n (m:bool list)`; `take_list n (s:A list)`;
                   `drop_list n (m:bool list)`; `drop_list n (s:A list)`]
                     MASK_LIST_APPEND) THEN
    ASM_REWRITE_TAC[TAKE_DROP_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(FILTER (\b. b) (take_list n m)) =
                LENGTH(mask_list (take_list n m) (take_list n (s:A list)))`
                  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LENGTH_MASK_LIST_EQ]; ALL_TAC] THEN
  REWRITE_TAC[ROT_LIST_APPEND; rot_list] THEN
    ASM_SIMP_TAC[MASK_LIST_APPEND]);;

let MEM_MASK_LIST_ROT = prove
 (`!i m (s:A list) z. LENGTH m = LENGTH s
     ==> (MEM z (mask_list m (rot_list i s)) <=> MEM z (mask_list (rotr_list i
       m) s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `rotr_list i (m:bool list)`; `s:A list`]
    MASK_LIST_ROT) THEN
  ASM_REWRITE_TAC[LENGTH_ROTR_LIST; ROT_LIST_ROTR_CANCEL_GEN] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM_ROT_LIST]);;

(* ------------------------------------------------------------------------- *)
(* Geometry of the construction steps ecpY, ecpH (and ecpN, ecpR)            *)
(* ------------------------------------------------------------------------- *)

let EDGE_ECPY_APEX_GEN = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> edge_map (ecpY H x0) (ecpY_pt H x0)
   = SND(new_dart2(dart(ecpU H x0)))`,
  MESON_TAC[EDGE_ECPY_APEX; FINITE_DART]);;

let EDGE_ECPY_B_GEN = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> edge_map (ecpY H x0)
   (SND(new_dart2(dart(ecpU H x0)))) = ecpY_pt H x0`,
  MESON_TAC[EDGE_ECPY_B; FINITE_DART]);;

let EDGE_ECPH_ECPYPT = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> edge_map (ecpH H x0) (ecpY_pt H x0)
   = SND(new_dart2(dart(ecpU H x0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPECL [`ecpY H x0`; `ecpY_pt H x0`; `ecpY_pt H x0`]
    EDGE_ECPN_OLD_GEN) THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; EDGE_ECPY_APEX_GEN]);;

let CFACE_ICPY = prove
 (`!(H:(num)hypermap) x0 x y. x0 IN dart H /\ FINITE(dart H) /\ edge_map H
   permutes dart H /\ node_map H permutes dart H /\ face_map H permutes dart H
     /\ x IN dart H /\ y IN dart H ==> (cface (ecpY H x0) x y <=> cface H x
       y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[CFACE_ECPY_PROJ]; ASM_MESON_TAC[CFACE_ECPY_LIFT]]);;

let CFACE_ICPH = prove
 (`!(H:(num)hypermap) x0 x y. x0 IN dart H /\ proper_cpring H x0 /\ FINITE(dart
   H) /\ edge_map H permutes dart H /\ node_map H permutes dart H /\ face_map H
     permutes dart H /\ x IN dart H /\ y IN dart H ==> (cface (ecpH H x0) x y
       <=> cface H x y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[CFACE_ECPH_PROJ]; ASM_MESON_TAC[CFACE_ECPH_LIFT]]);;

let NODE_OFF_ORBIT_STEP = prove
 (`!(G:(num)hypermap) x0 z. FINITE(dart G) /\ node_map G permutes dart G /\ x0
   IN dart G /\ z IN dart G /\
     ~(z IN orbit_map (node_map G) x0) ==> ~(node_map G z IN orbit_map
       (node_map G) x0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `orbit_map (node_map G) (node_map G (z:num)) = orbit_map
    (node_map G) x0 /\
                orbit_map (node_map G) (node_map G (z:num)) = orbit_map
                  (node_map G) z`
    (fun th -> ASM_MESON_TAC[th; IN_ORBIT_MAP_REFL]) THEN
  CONJ_TAC THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC
    `dart(G:(num)hypermap)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ORBIT_MAP_STEP THEN
    REWRITE_TAC[IN_ORBIT_MAP_REFL]);;

let CPKSIZE_CLAUSES = prove
 (`cpksize [] = 0 /\ (!n cp. cpksize (CONS (CpR n) cp) = cpksize cp) /\ (!cp.
   cpksize (CONS CpY cp) = cpksize cp) /\ (!cp. cpksize (CONS CpH cp) =
     SUC(cpksize cp))`,
  REWRITE_TAC[cpksize; FILTER; LENGTH; distinctness "cpstep"]);;

let ECPN_FACE_TAC = ASM_REWRITE_TAC[] THEN REWRITE_TAC[ecpN_face] THEN
  ASM_REWRITE_TAC[];;

let CFACE_ECPN_STEP_GEN = prove
 (`!(H:(num)hypermap) x0 z. x0 IN dart H /\ FINITE(dart H) /\ edge_map H
   permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\ z IN dart H
     ==> cface (ecpN H x0) z (face_map H z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPN_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `a = FST(new_dart2(dart(H:(num)hypermap)))` THEN
  ABBREV_TAC `b = SND(new_dart2(dart(H:(num)hypermap)))` THEN
  SUBGOAL_THEN `~(z:num = a) /\ ~(z = b) /\ ~(b:num = a)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC `(a:num) IN dart H`; UNDISCH_TAC `(b:num) IN dart H`;
      UNDISCH_TAC `~(a:num = a)`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
    `z = edge_map H (face_map H (edge_map (H:(num)hypermap) x0))` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `face_map (ecpN H x0) (edge_map H (face_map H (edge_map H
      x0))) = b` ASSUME_TAC THENL [ECPN_FACE_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `long_cpring (H:(num)hypermap) x0` THENL
     [SUBGOAL_THEN `face_map (ecpN H x0) b = face_map H (edge_map H (face_map H
       (edge_map H x0)))` ASSUME_TAC THENL [ECPN_FACE_TAC; CFACE_TAC[]];
      SUBGOAL_THEN `face_map (ecpN H x0) b = a /\ face_map (ecpN H x0) a = x0`
        STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ECPN_FACE_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[long_cpring]) THEN
      ASM_REWRITE_TAC[NODEK_NUM] THEN CFACE_TAC[]];
    ASM_CASES_TAC `z = edge_map H (node_map (H:(num)hypermap) x0)` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `face_map (ecpN H x0) (edge_map H (node_map H x0)) = a /\
        face_map (ecpN H x0) a = x0`
        STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ECPN_FACE_TAC; ALL_TAC] THEN
      REWRITE_TAC[NODEK_NUM] THEN CFACE_TAC[];
      SUBGOAL_THEN `face_map (ecpN H x0) z = face_map H z` ASSUME_TAC THENL
       [ECPN_FACE_TAC; CFACE_TAC[]]]]);;

let CFACE_ECPN_LIFT_GEN = prove
 (`!(H:(num)hypermap) x0 x y. x0 IN dart H /\ FINITE(dart H) /\ edge_map H
   permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\ x IN dart H /\
       cface H x y
     ==> cface (ecpN H x0) x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. y = ITER n (face_map H) (x:num)` MP_TAC THENL
   [ASM_MESON_TAC[cface; face; ORBIT_MAP_ITER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ITER; CFACE_REFL] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `ITER n (face_map H) (x:num)`]
    CFACE_ECPN_STEP_GEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THEN CFACE_TAC[]);;

let CFACE_ECPH_LIFT_GEN = prove
 (`!(H:(num)hypermap) x0 x y. x0 IN dart H /\ FINITE(dart H) /\ edge_map H
   permutes dart H /\ node_map H permutes dart H /\ face_map H permutes dart H
     /\ x IN dart H /\ cface H x y ==> cface (ecpH H x0) x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPEC `ecpY (H:(num)hypermap) x0` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MATCH_MP_TAC CFACE_ECPN_LIFT_GEN THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; DART_H_SUBSET_ECPY; CFACE_ECPY_LIFT]);;

let NODE_ECPY_OLD = prove
 (`!(G:(num)hypermap) (x0:num) (z:num). x0 IN dart G /\ FINITE(dart G) /\
   edge_map G permutes dart G /\ node_map G permutes dart G /\ face_map G
     permutes dart G /\ z IN dart G /\ ~(z IN orbit_map (node_map G) x0) ==>
       node_map (ecpY G x0) z = node_map G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY] THEN
  MP_TAC(ISPEC `dart(G:(num)hypermap)` NEW_DART2_FRESH) THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC THEN
  MP_TAC(ISPEC `dart(ecpU G (x0:num))` NEW_DART2_FRESH) THEN
    REWRITE_TAC[FINITE_DART] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `ecpU G (x0:num)` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  SUBGOAL_THEN `dart(ecpU G (x0:num)) = FST(new_dart2(dart G)) INSERT
    SND(new_dart2(dart G)) INSERT dart G /\
                node_map(ecpU G x0) = ecpU_node G x0 (FST(new_dart2(dart G)))
                  (SND(new_dart2(dart G)))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ECPU_COMPONENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:num) IN dart(ecpU G x0) /\ ecpU_pt G IN dart(ecpU G x0)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT; ecpU_pt]; ALL_TAC] THEN
  SUBGOAL_THEN `~(z IN orbit_map (node_map(ecpU G x0)) (ecpU_pt G))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[ORBIT_ECPU_PT; IN_INSERT; DE_MORGAN_THM; ecpU_pt] THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC `FST(new_dart2(dart (G:(num)hypermap))) IN dart G`;
      UNDISCH_TAC `SND(new_dart2(dart (G:(num)hypermap))) IN dart G`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ecpU G (x0:num)`; `ecpU_pt G`] ECPN_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
  MP_TAC(ISPECL [`ecpU G (x0:num)`; `ecpU_pt G`; `FST(new_dart2(dart(ecpU G
    (x0:num))))`;
                 `SND(new_dart2(dart(ecpU G (x0:num))))`; `z:num`]
                   ECPN_NODE_OFF_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ECPU_NODE_OFF_ORBIT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ORBIT_MAP_STEP THEN REWRITE_TAC[IN_ORBIT_MAP_REFL]);;

let NODE_ECPH_OLD = prove
 (`!(G:(num)hypermap) (x0:num) (z:num). x0 IN dart G /\ FINITE(dart G) /\
   edge_map G permutes dart G /\ node_map G permutes dart G /\ face_map G
     permutes dart G /\ z IN dart G /\ ~(z IN orbit_map (node_map G) x0) ==>
       node_map (ecpH G x0) z = node_map G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPEC `ecpY G (x0:num)` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_PT_IN_DART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_PT_NOT_IN_DART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `z:num`] DART_H_SUBSET_ECPY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `z:num`] NODE_OFF_ORBIT_STEP)
    THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `z:num`] NODE_ECPY_OLD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `node_map G (z:num)`]
    NODE_ECPY_OLD) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ecpY G (x0:num)`; `ecpY_pt G x0`] ECPN_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
  MP_TAC(ISPEC `dart(ecpY G (x0:num))` NEW_DART2_FRESH) THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpY G (x0:num)`; `ecpY_pt G x0`; `FST(new_dart2(dart(ecpY G
    (x0:num))))`;
                 `SND(new_dart2(dart(ecpY G (x0:num))))`; `z:num`]
                   ECPN_NODE_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN
  DISCH_TAC THEN
  UNDISCH_TAC `~(ecpY_pt G x0 IN dart (G:(num)hypermap))` THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[NODE_MAP_IN_DART]);;

let NODE_ECPY_3CYCLE = prove
 (`!(G:(num)hypermap) (x0:num). x0 IN dart G /\ FINITE(dart G) /\ edge_map G
   permutes dart G /\ node_map G permutes dart G /\ face_map G permutes dart G
     ==> node_map (ecpY G x0) (node_map G x0) = FST(new_dart2(dart G)) /\
       node_map (ecpY G x0) (FST(new_dart2(dart G))) = SND(new_dart2(dart(ecpU
         G x0))) /\ node_map (ecpY G x0) (SND(new_dart2(dart(ecpU G x0)))) =
           node_map G x0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ecpY] THEN
  MP_TAC(ISPEC `ecpU G (x0:num)` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPU_PT_IN_DART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ecpU G (x0:num)`; `ecpU_pt G`] ECPN_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
  MP_TAC(ISPEC `dart(ecpU G (x0:num))` NEW_DART2_FRESH) THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpU G (x0:num)`; `ecpU_pt G`; `FST(new_dart2(dart(ecpU G
    (x0:num))))`;
                 `SND(new_dart2(dart(ecpU G (x0:num))))`]
                   ECPN_NODE_3CYCLE_STEPS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[LONG_ECPU]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPU_EDGE_PT) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPU_FACE_SND) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ecpU_pt] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[]);;

let NODE_ECPH_3CYCLE = prove
 (`!(G:(num)hypermap) (x0:num). x0 IN dart G /\ FINITE(dart G) /\
   plain_hypermap G /\ edge_map G permutes dart G /\ node_map G permutes dart G
     /\ face_map G permutes dart G /\ proper_cpring G x0 ==> node_map (ecpH G
       x0) (ecpY_pt G x0) = SND(new_dart2(dart (ecpY G x0))) /\ node_map (ecpH
         G x0) (SND(new_dart2(dart (ecpY G x0)))) = face_map (ecpY G x0)
           (edge_map (ecpY G x0) (ecpY_pt G x0)) /\ node_map (ecpH G x0)
             (face_map (ecpY G x0) (edge_map (ecpY G x0) (ecpY_pt G x0))) =
               ecpY_pt G x0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPEC `ecpY G (x0:num)` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_PT_IN_DART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ecpY G (x0:num)`; `ecpY_pt G x0`] ECPN_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
  MP_TAC(ISPEC `dart(ecpY G (x0:num))` NEW_DART2_FRESH) THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpY G (x0:num)`; `ecpY_pt G x0`; `FST(new_dart2(dart(ecpY G
    (x0:num))))`;
                 `SND(new_dart2(dart(ecpY G (x0:num))))`]
                   ECPN_NODE_3CYCLE_STEPS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[LONG_ECPY]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let NODE_ECPH_ECPY_OFF = prove
 (`!(G:(num)hypermap) (x0:num) (z:num). x0 IN dart G /\ FINITE(dart G) /\
   edge_map G permutes dart G /\ node_map G permutes dart G /\ face_map G
     permutes dart G /\ z IN dart(ecpY G x0) /\ ~(z IN orbit_map (node_map(ecpY
       G x0)) (ecpY_pt G x0)) ==> node_map (ecpH G x0) z = node_map (ecpY G x0)
         z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPEC `ecpY G (x0:num)` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_PT_IN_DART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ecpY G (x0:num)`; `ecpY_pt G x0`] ECPN_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
  MP_TAC(ISPEC `dart(ecpY G (x0:num))` NEW_DART2_FRESH) THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpY G (x0:num)`; `ecpY_pt G x0`; `z:num`]
    NODE_OFF_ORBIT_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ecpY G (x0:num)`; `ecpY_pt G x0`; `node_map (ecpY G x0)
    (z:num)`] NODE_OFF_ORBIT_STEP) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN DISCH_TAC THEN
  MATCH_MP_TAC ECPN_NODE_OFF THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    DISCH_TAC THENL
   [UNDISCH_TAC `~((z:num) IN orbit_map (node_map (ecpY G x0)) (ecpY_pt G
     x0))`;
    UNDISCH_TAC `~(node_map (ecpY G x0) (node_map (ecpY G x0) (z:num)) IN
                   orbit_map (node_map (ecpY G x0)) (ecpY_pt G x0))`] THEN
  ASM_REWRITE_TAC[IN_ORBIT_MAP_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Kernel edge transversal: ctrmsize, ctrmask, ctrenum                       *)
(* ------------------------------------------------------------------------- *)

let CONFIG_PROG_NIL = prove(`config_prog [] <=> F`, REWRITE_TAC[config_prog]);;

let CONFIG_PROG_CONS_CASES = prove
 (`!s cp. config_prog (CONS s cp) <=>
          ((?n. s = CpR n) /\ config_prog cp) \/ (s = CpY /\ (cp = [] \/
            config_prog cp)) \/
          (s = CpH /\ config_prog cp)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `cp:(cpstep)list = []` THEN
  ASM_REWRITE_TAC[config_prog; ALL; LAST; NOT_CONS_NIL; CONFIG_STEP_CASES] THEN
  MESON_TAC[distinctness "cpstep"]);;

let ctrmsize = define
 `(ctrmsize [] = 0) /\
  (ctrmsize (CONS (CpR n) cp') = ctrmsize cp') /\
  (ctrmsize (CONS CpRr cp') = 0) /\
  (ctrmsize (CONS CpY cp') = (if cp' = [] then 0 else SUC(ctrmsize cp'))) /\
  (ctrmsize (CONS CpH cp') = ctrmsize cp' + 3) /\
  (ctrmsize (CONS CpU cp') = 0) /\
  (ctrmsize (CONS CpK cp') = 0) /\
  (ctrmsize (CONS CpA cp') = 0)`;;

let ctrmask_rec = define
 `(ctrmask_rec cci i 0 = []) /\
  (ctrmask_rec cci i (SUC n) = CONS (MEM i cci) (ctrmask_rec cci (i+1) n))`;;

let ctrmask = new_definition
 `ctrmask cp cci = ctrmask_rec cci 0 (ctrmsize cp)`;;

let ctrenum = define
 `(ctrenum [] = []) /\
  (ctrenum (CONS (CpR n) cp') = ctrenum cp') /\
  (ctrenum (CONS CpRr cp') = []) /\
  (ctrenum (CONS CpY cp') =
     (if cp' = [] then []
      else CONS (node_map (FST(cpmap cp')) (SND(cpmap cp'))) (ctrenum cp'))) /\
  (ctrenum (CONS CpH cp') =
     CONS (face_map (ecpH (FST(cpmap cp')) (SND(cpmap cp')))
                    (ecpH_pt (FST(cpmap cp')) (SND(cpmap cp'))))
       (CONS (node_map (FST(cpmap cp')) (SND(cpmap cp')))
         (CONS (SND(cpmap cp')) (ctrenum cp')))) /\
  (ctrenum (CONS CpU cp') = []) /\
  (ctrenum (CONS CpK cp') = []) /\
  (ctrenum (CONS CpA cp') = [])`;;

let SIZE_CTRMASK = prove
 (`!cp cci. LENGTH(ctrmask cp cci) = ctrmsize cp`,
  REWRITE_TAC[ctrmask] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!n i. LENGTH(ctrmask_rec cci i n) = n` (fun th ->
    REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ctrmask_rec; LENGTH]);;

let SIZE_CTRENUM = prove
 (`!cp. LENGTH(ctrenum cp) = ctrmsize cp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ctrenum; ctrmsize; LENGTH] THEN
  MP_TAC(ISPEC `h:cpstep` (cases "cpstep")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ctrenum; ctrmsize; LENGTH] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN TRY ARITH_TAC);;

let MEM_CTRENUM_IN_DART = prove
 (`!cp. config_prog cp ==> !w. MEM w (ctrenum cp) ==> w IN dart(FST(cpmap
   cp))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[CONFIG_PROG_NIL; CONFIG_PROG_CONS_CASES] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THENL
   [REWRITE_TAC[ctrenum; CPMAP_CONS_R; ecpR] THEN ASM_MESON_TAC[];
    REWRITE_TAC[ctrenum; MEM];
    SUBGOAL_THEN `~(t:(cpstep)list = [])` ASSUME_TAC THENL
      [ASM_MESON_TAC[CONFIG_PROG_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ctrenum; CPMAP_CONS_Y; MEM] THEN
    MP_TAC(ISPECL [`FST(cpmap (t:(cpstep)list))`; `SND(cpmap
      (t:(cpstep)list))`] DART_SUBSET_ECPY) THEN
    REWRITE_TAC[CPMAP_PT_IN_DART; SUBSET] THEN ASM_MESON_TAC[NODE_MAP_IN_DART;
      CPMAP_PT_IN_DART];
    REWRITE_TAC[ctrenum; CPMAP_CONS_H; MEM] THEN
    MP_TAC(ISPECL [`FST(cpmap (t:(cpstep)list))`; `SND(cpmap
      (t:(cpstep)list))`] DART_SUBSET_ECPH) THEN
    REWRITE_TAC[CPMAP_PT_IN_DART; SUBSET] THEN
    ASM_MESON_TAC[NODE_MAP_IN_DART; FACE_MAP_IN_DART; ECPH_PT_IN_DART;
      CPMAP_PT_IN_DART]]);;

let CPMAP_FACTS = prove
 (`!cp. (cp = [] \/ config_prog cp)
        ==> SND(cpmap cp) IN dart(FST(cpmap cp)) /\
            FINITE(dart(FST(cpmap cp))) /\
            edge_map (FST(cpmap cp)) permutes dart(FST(cpmap cp)) /\
            node_map (FST(cpmap cp)) permutes dart(FST(cpmap cp)) /\
            face_map (FST(cpmap cp)) permutes dart(FST(cpmap cp)) /\
            plain_hypermap (FST(cpmap cp)) /\
            proper_cpring (FST(cpmap cp)) (SND(cpmap cp)) /\
            2 <= cprsize cp /\
            (config_prog cp
             ==> long_cpring (FST(cpmap cp)) (SND(cpmap cp)) /\
                 2 < cprsize cp /\
                 (!z. MEM z (ctrenum cp) ==> z IN dart(FST(cpmap cp)))) /\
            face_simple (FST(cpmap cp))
              (APPEND (cpring (FST(cpmap cp)) (SND(cpmap cp))) (cpker cp)) /\
            (!z. MEM z (cpker cp) ==> z IN dart(FST(cpmap cp)))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `cubic_prog cp` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONFIG_PROG_CUBIC; cubic_prog; ALL]; ALL_TAC] THEN
  MP_TAC(ISPEC `FST(cpmap cp)` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CPMAP_PT_IN_DART; CPMAP_PLAIN; CPMAP_PROPER; CPRSIZE_GE_2] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CFMAP_LONG];
      REWRITE_TAC[cprsize] THEN
      ASM_MESON_TAC[CFMAP_LONG; SIZE_LONG_CPRING; CPMAP_PT_IN_DART];
      ASM_MESON_TAC[MEM_CTRENUM_IN_DART]];
    FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC o
                  check (is_disj o concl)) THENL
     [REWRITE_TAC[CPMAP_NIL_PAIR; cpker; MEM; SIMPLE_CPMAP0_BASE];
      ASM_SIMP_TAC[CPMAP_SIMPLE] THEN MATCH_MP_TAC CPKER_IN_DART THEN
      ASM_MESON_TAC[config_prog]]]);;

(* ------------------------------------------------------------------------- *)
(* The contract construction program cfctr                                   *)
(* ------------------------------------------------------------------------- *)

let nsp = new_definition
 `nsp b x y = if b then (x \/ y) else (x /\ y)`;;

let cfctr_ok = define
 `(cfctr_ok mr mc [] = F) /\
  (cfctr_ok mr mc (CONS (CpR i) cp') = cfctr_ok (rotr_list i mr) mc cp') /\
  (cfctr_ok mr mc (CONS CpRr cp') = F) /\
  (cfctr_ok mr mc (CONS CpY cp') =
     (if cp' = [] then
        (3 <= LENGTH mr /\
         (let b1 = EL 0 mr in let b2 = EL 1 mr in let b3 = EL 2 mr in
          ~(nsp b1 b2 b3)))
      else
        (2 <= LENGTH mr /\ 1 <= LENGTH mc /\
         (let b1 = EL 0 mr in let b2 = EL 1 mr in let mr' = TL(TL mr) in
          let b3 = HD mc in let mc' = TL mc in
          ~(nsp b1 b2 b3) /\ cfctr_ok (CONS b3 mr') mc' cp')))) /\
  (cfctr_ok mr mc (CONS CpH cp') =
     (2 <= LENGTH mr /\ 3 <= LENGTH mc /\
      (let b1 = EL 0 mr in let b2 = EL 1 mr in let mr' = TL(TL mr) in
       let b3 = EL 0 mc in let b4 = EL 1 mc in let b5 = EL 2 mc in
       let mc' = TL(TL(TL mc)) in
       ~(nsp b3 b1 b4 \/ nsp b3 b2 b5) /\
       ~(b1 /\ b2 /\ ALL (\b. b) mr') /\
       cfctr_ok (CONS b4 (CONS b5 mr')) mc' cp'))) /\
  (cfctr_ok mr mc (CONS CpU cp') = F) /\
  (cfctr_ok mr mc (CONS CpK cp') = F) /\
  (cfctr_ok mr mc (CONS CpA cp') = F)`;;

let cfctr_map = define
 `(cfctr_map mr mc [] = ([]:(cpstep)list)) /\
  (cfctr_map mr mc (CONS (CpR i) cp') =
     (let mr' = rotr_list i mr in
      CONS (CpR (LENGTH(FILTER (\b. ~b) (take_list i mr'))))
           (cfctr_map mr' mc cp'))) /\
  (cfctr_map mr mc (CONS CpRr cp') = []) /\
  (cfctr_map mr mc (CONS CpY cp') =
     (if cp' = [] then
        (let b1 = EL 0 mr in let b2 = EL 1 mr in let b3 = EL 2 mr in
         if b1 \/ (b2 \/ b3) then [] else [CpY])
      else
        (let b1 = EL 0 mr in let b2 = EL 1 mr in let mr' = TL(TL mr) in
         let b3 = HD mc in let mc' = TL mc in
         if b1 \/ b2 then cfctr_map (CONS b3 mr') mc' cp'
         else CONS (if b3 then CpU else CpY)
                   (cfctr_map (CONS b3 mr') mc' cp')))) /\
  (cfctr_map mr mc (CONS CpH cp') =
     (let b1 = EL 0 mr in let b2 = EL 1 mr in let mr' = TL(TL mr) in
      let b3 = EL 0 mc in let b4 = EL 1 mc in let b5 = EL 2 mc in
      let mc' = TL(TL(TL mc)) in
      let cpc = cfctr_map (CONS b4 (CONS b5 mr')) mc' cp' in
      if b3 then cpc
      else if b1 then (if b2 then CONS CpA cpc else if b5 then cpc
                       else CONS CpK cpc)
      else if b2 then (if b4 then cpc else CONS CpK cpc)
      else if b4 then (if b5 then CONS CpU cpc else CONS CpY cpc)
      else if b5 then CONS CpY cpc else CONS CpH cpc)) /\
  (cfctr_map mr mc (CONS CpU cp') = []) /\
  (cfctr_map mr mc (CONS CpK cp') = []) /\
  (cfctr_map mr mc (CONS CpA cp') = [])`;;

let cfctr = new_definition
 `cfctr mr mc cp =
    if cfctr_ok mr mc cp then SOME(cfctr_map mr mc cp) else NONE`;;

let CFCTR_OK_CLAUSES = prove
 (`(!mr mc. cfctr_ok mr mc [] = F) /\
   (!i mr mc cp. cfctr_ok mr mc (CONS (CpR i) cp) = cfctr_ok (rotr_list i mr)
     mc cp) /\
   (!mr mc. cfctr_ok mr mc [CpY] = (3 <= LENGTH mr /\ ~(nsp (EL 0 mr) (EL 1 mr)
     (EL 2 mr)))) /\
   (!mr mc s cp. cfctr_ok mr mc (CONS CpY (CONS s cp)) =
      (2 <= LENGTH mr /\ 1 <= LENGTH mc /\ ~(nsp (EL 0 mr) (EL 1 mr) (HD mc))
        /\
       cfctr_ok (CONS (HD mc) (TL(TL mr))) (TL mc) (CONS s cp))) /\
   (!mr mc cp. cfctr_ok mr mc (CONS CpH cp) =
      (2 <= LENGTH mr /\ 3 <= LENGTH mc /\
       ~(nsp (EL 0 mc) (EL 0 mr) (EL 1 mc) \/ nsp (EL 0 mc) (EL 1 mr) (EL 2
         mc)) /\
       ~(EL 0 mr /\ EL 1 mr /\ ALL (\b. b) (TL(TL mr))) /\
       cfctr_ok (CONS (EL 1 mc) (CONS (EL 2 mc) (TL(TL mr)))) (TL(TL(TL mc)))
         cp)) /\
   (!mr mc cp. cfctr_ok mr mc (CONS CpRr cp) = F) /\ (!mr mc cp. cfctr_ok mr mc
     (CONS CpU cp) = F) /\
   (!mr mc cp. cfctr_ok mr mc (CONS CpK cp) = F) /\ (!mr mc cp. cfctr_ok mr mc
     (CONS CpA cp) = F)`,
  REWRITE_TAC[cfctr_ok; NOT_CONS_NIL] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let CFCTR_MAP_CLAUSES = prove
 (`(!mr mc. cfctr_map mr mc [] = []) /\
   (!i mr mc cp. cfctr_map mr mc (CONS (CpR i) cp) =
      CONS (CpR (LENGTH(FILTER (\b. ~b) (take_list i (rotr_list i mr)))))
        (cfctr_map (rotr_list i mr) mc cp)) /\
   (!mr mc. cfctr_map mr mc [CpY] = (if EL 0 mr \/ (EL 1 mr \/ EL 2 mr) then []
     else [CpY])) /\
   (!mr mc s cp. cfctr_map mr mc (CONS CpY (CONS s cp)) =
      (if EL 0 mr \/ EL 1 mr then cfctr_map (CONS (HD mc) (TL(TL mr))) (TL mc)
        (CONS s cp)
       else CONS (if HD mc then CpU else CpY) (cfctr_map (CONS (HD mc) (TL(TL
         mr))) (TL mc) (CONS s cp)))) /\
   (!mr mc cp. cfctr_map mr mc (CONS CpH cp) =
      (let cpc = cfctr_map (CONS (EL 1 mc) (CONS (EL 2 mc) (TL(TL mr))))
        (TL(TL(TL mc))) cp in
       if EL 0 mc then cpc
       else if EL 0 mr then (if EL 1 mr then CONS CpA cpc else if EL 2 mc then
         cpc else CONS CpK cpc)
       else if EL 1 mr then (if EL 1 mc then cpc else CONS CpK cpc)
       else if EL 1 mc then (if EL 2 mc then CONS CpU cpc else CONS CpY cpc)
       else if EL 2 mc then CONS CpY cpc else CONS CpH cpc))`,
  REWRITE_TAC[cfctr_map; NOT_CONS_NIL] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let LENGTH_GE_ARITH = ARITH_RULE
 `(3 <= SUC(SUC(SUC n)) <=> T) /\ (2 <= SUC(SUC n) <=> T) /\ (1 <= SUC n <=>
   T)`;;

let EL_NUMERAL_CLAUSES = prove
 (`(!h t:A list. EL 0 (CONS h t) = h) /\ (!h t:A list. EL 1 (CONS h t) = EL 0
   t) /\
   (!h t:A list. EL 2 (CONS h t) = EL 1 t)`,
  REWRITE_TAC[num_CONV `1`; num_CONV `2`; EL; HD; TL]);;

let CFCTR_OK_Y0 = prove
 (`!b1 b2 b3 mr mc. cfctr_ok (CONS b1 (CONS b2 (CONS b3 mr))) mc [CpY] <=>
   ~(nsp b1 b2 b3)`,
  REWRITE_TAC[CFCTR_OK_CLAUSES; EL_NUMERAL_CLAUSES; LENGTH; LENGTH_GE_ARITH]);;

let CFCTR_OK_Y = prove
 (`!b1 b2 b3 mr mc s cp. cfctr_ok (CONS b1 (CONS b2 mr)) (CONS b3 mc) (CONS CpY
   (CONS s cp)) <=>
                         ~(nsp b1 b2 b3) /\ cfctr_ok (CONS b3 mr) mc (CONS s
                           cp)`,
  REWRITE_TAC[CFCTR_OK_CLAUSES; EL_NUMERAL_CLAUSES; HD; TL; LENGTH;
    LENGTH_GE_ARITH]);;

let CFCTR_OK_H = prove
 (`!b1 b2 b3 b4 b5 mr mc cp.
     cfctr_ok (CONS b1 (CONS b2 mr)) (CONS b3 (CONS b4 (CONS b5 mc))) (CONS CpH
       cp) <=>
     ~(nsp b3 b1 b4 \/ nsp b3 b2 b5) /\ ~(b1 /\ b2 /\ ALL (\b. b) mr) /\
     cfctr_ok (CONS b4 (CONS b5 mr)) mc cp`,
  REWRITE_TAC[CFCTR_OK_CLAUSES; EL_NUMERAL_CLAUSES; HD; TL; LENGTH;
    LENGTH_GE_ARITH]);;

let CFCTR_OK_Y_CASES = prove
 (`!mr mc s cp.
     cfctr_ok mr mc (CONS CpY (CONS s cp)) <=>
     ?b1 b2 b3 mr' mc'.
       mr = CONS b1 (CONS b2 mr') /\ mc = CONS b3 mc' /\
       ~nsp b1 b2 b3 /\ cfctr_ok (CONS b3 mr') mc' (CONS s cp)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[CFCTR_OK_Y]] THEN
  STRUCT_CASES_TAC(ISPEC `mc:bool list` list_CASES) THEN
  REWRITE_TAC[CFCTR_OK_CLAUSES; LENGTH; ARITH_RULE `~(1 <= 0)`; HD; TL] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b1:bool` (X_CHOOSE_THEN `b2:bool`
    (X_CHOOSE_THEN `mr':bool list` SUBST_ALL_TAC)) o
    MATCH_MP LIST_LENGTH_GE_2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EL_NUMERAL_CLAUSES; HD; TL]) THEN
  MAP_EVERY EXISTS_TAC [`b1:bool`; `b2:bool`; `h:bool`; `mr':bool list`;
                        `t:bool list`] THEN
  ASM_REWRITE_TAC[]);;

let CFCTR_OK_H_CASES = prove
 (`!mr mc cp.
     cfctr_ok mr mc (CONS CpH cp) <=>
     ?b1 b2 b3 b4 b5 mr' mc'.
       mr = CONS b1 (CONS b2 mr') /\ mc = CONS b3 (CONS b4 (CONS b5 mc')) /\
       ~(nsp b3 b1 b4 \/ nsp b3 b2 b5) /\ ~(b1 /\ b2 /\ ALL (\b. b) mr') /\
       cfctr_ok (CONS b4 (CONS b5 mr')) mc' cp`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[CFCTR_OK_H]] THEN
  REWRITE_TAC[CFCTR_OK_CLAUSES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b1:bool` (X_CHOOSE_THEN `b2:bool`
    (X_CHOOSE_THEN `mr':bool list` SUBST_ALL_TAC)) o
    MATCH_MP LIST_LENGTH_GE_2) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b3:bool` (X_CHOOSE_THEN `b4:bool`
    (X_CHOOSE_THEN `b5:bool` (X_CHOOSE_THEN `mc':bool list`
      SUBST_ALL_TAC))) o
    MATCH_MP LIST_LENGTH_GE_3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EL_NUMERAL_CLAUSES; HD; TL]) THEN
  MAP_EVERY EXISTS_TAC [`b1:bool`; `b2:bool`; `b3:bool`; `b4:bool`;
                        `b5:bool`; `mr':bool list`; `mc':bool list`] THEN
  ASM_REWRITE_TAC[]);;

let CFCTR_MAP_Y0 = prove
 (`!b1 b2 b3 mr mc. cfctr_map (CONS b1 (CONS b2 (CONS b3 mr))) mc [CpY] =
                    (if b1 \/ (b2 \/ b3) then [] else [CpY])`,
  REWRITE_TAC[CFCTR_MAP_CLAUSES; EL_NUMERAL_CLAUSES]);;

let CFCTR_MAP_Y = prove
 (`!b1 b2 b3 mr mc s cp. cfctr_map (CONS b1 (CONS b2 mr)) (CONS b3 mc) (CONS
   CpY (CONS s cp)) =
      (if b1 \/ b2 then cfctr_map (CONS b3 mr) mc (CONS s cp)
       else CONS (if b3 then CpU else CpY) (cfctr_map (CONS b3 mr) mc (CONS s
         cp)))`,
  REWRITE_TAC[CFCTR_MAP_CLAUSES; EL_NUMERAL_CLAUSES; HD; TL]);;

let CFCTR_MAP_H = prove
 (`!b1 b2 b3 b4 b5 mr mc cp.
     cfctr_map (CONS b1 (CONS b2 mr)) (CONS b3 (CONS b4 (CONS b5 mc))) (CONS
       CpH cp) =
      (let cpc = cfctr_map (CONS b4 (CONS b5 mr)) mc cp in
       if b3 then cpc
       else if b1 then (if b2 then CONS CpA cpc else if b5 then cpc else CONS
         CpK cpc)
       else if b2 then (if b4 then cpc else CONS CpK cpc)
       else if b4 then (if b5 then CONS CpU cpc else CONS CpY cpc)
       else if b5 then CONS CpY cpc else CONS CpH cpc)`,
  REWRITE_TAC[CFCTR_MAP_CLAUSES; EL_NUMERAL_CLAUSES; HD; TL]);;

let CFCTR_CONFIG_PROG = prove
 (`!cp mr mc. cfctr_ok mr mc cp ==> config_prog cp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CFCTR_OK_CLAUSES] THEN
  MP_TAC(ISPEC `h:cpstep` (cases "cpstep")) THEN STRIP_TAC THEN FIRST_X_ASSUM
    SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:(cpstep)list` list_CASES) THEN
  REWRITE_TAC[CFCTR_OK_CLAUSES; CONFIG_PROG_CONS_CASES; CONFIG_PROG_NIL;
    NOT_CONS_NIL;
              distinctness "cpstep"] THEN
  MESON_TAC[]);;

let CFCTR_MAP_NO_CPRR = prove
 (`!cp mr mc. ALL (\s. ~(s = CpRr)) (cfctr_map mr mc cp)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[cfctr_map; ALL] THEN
  STRUCT_CASES_TAC(SPEC `h:cpstep` (cases "cpstep")) THEN
  REWRITE_TAC[cfctr_map; ALL] THEN REPEAT GEN_TAC THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ALL; distinctness "cpstep"] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL; distinctness "cpstep"]));;

(* ------------------------------------------------------------------------- *)
(* Configurations: cfprog, cfmap, cfring, cfcontract                         *)
(* ------------------------------------------------------------------------- *)

let cfprog = new_definition `cfprog (cf:(cpstep)list#(num)list) = FST cf`;;

let cfcontract_ref = new_definition `cfcontract_ref (cf:(cpstep)list#(num)list)
  = SND cf`;;

let cfmap = new_definition `cfmap (cf:(cpstep)list#(num)list) = cpmap (cfprog
  cf)`;;

let cfring = new_definition
 `cfring (cf:(cpstep)list#(num)list) = REVERSE (cpring (FST(cfmap cf))
   (SND(cfmap cf)))`;;

let cfcontract_mask = new_definition
 `cfcontract_mask (cf:(cpstep)list#(num)list) = ctrmask (cfprog cf)
   (cfcontract_ref cf)`;;

let cfcontract = new_definition
 `cfcontract (cf:(cpstep)list#(num)list) = mask_list (cfcontract_mask cf)
   (ctrenum (cfprog cf))`;;

(* ------------------------------------------------------------------------- *)
(* cfctr_correct: contract colourings induce colourings of the contract map  *)
(* ------------------------------------------------------------------------- *)

let MEM_MASK_LIST_CONS = prove
 (`!b m (y:A) s x. MEM x (mask_list (CONS b m) (CONS y s)) <=> b /\ x = y \/
   MEM x (mask_list m s)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
    REWRITE_TAC[MASK_LIST_CLAUSES; MEM]);;

let CC_COLORING_RESTRICT = prove
 (`!(G:(num)hypermap) (M:(num)hypermap) ccG ccM (k:num->color).
     (!x. x IN dart G ==> x IN dart M) /\ (!x. x IN dart G ==> edge_map M x =
       edge_map G x) /\
     (!x. x IN dart G ==> cface M x (face_map G x)) /\
     (!x. x IN dart G ==> (MEM x (insertE M ccM) <=> MEM x (insertE G ccG))) /\
     cc_coloring M ccM k ==> cc_coloring G ccG k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN dart G ==> (k:num->color) (face_map (G:(num)hypermap)
    x) = k x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CFACE_CC_COLORING THEN
    MAP_EVERY EXISTS_TAC [`M:(num)hypermap`; `ccM:num list`] THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `cc_coloring M ccM (k:num->color)` THEN
  REWRITE_TAC[cc_coloring] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:num`)) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[] THEN MESON_TAC[]);;

let ext_col = new_definition
 `ext_col (M:(num)hypermap) (D:num->bool) (h:num->color) (c0:color) u =
    if (?x. x IN D /\ cface M u x) then h (@x. x IN D /\ cface M u x) else
      c0`;;

let EXT_COL_FACE = prove
 (`!(M:(num)hypermap) D h c0 u.
     u IN dart M
     ==> ext_col M D h c0 (face_map M u) = ext_col M D h c0 u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ext_col] THEN
  ASM_SIMP_TAC[CFACE_LEFT_FACE]);;

let EXT_COL_CFACE = prove
 (`!(M:(num)hypermap) D h c0 u x.
     (!x y. x IN D /\ y IN D /\ cface M x y ==> h x = h y) /\
     x IN D /\ cface M u x
     ==> ext_col M D h c0 u = h x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ext_col] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CFACE_TAC[];
    ASM_MESON_TAC[]]);;

let EXT_COL_NEW = prove
 (`!(M:(num)hypermap) D h c0 u.
     (!x. x IN D ==> ~cface M u x) ==> ext_col M D h c0 u = c0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ext_col] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[]);;

let ADJ_INTRO = prove
 (`!(M:(num)hypermap) x u y.
     cface M x u /\ cface M (edge_map M u) y ==> adj M x y`,
  REWRITE_TAC[adj; rlink; cface] THEN MESON_TAC[]);;

(* On the faces of M that meet dart G, ext_col is h, and an edge between     *)
(* two such faces has two different colours (shared by COLORING_EXT,         *)
(* with one new face X, and COLORING_EXT0, with none).                       *)

let EXT_COL_OLD = prove
 (`!(G:(num)hypermap) (M:(num)hypermap) h c0.
     coloring G h /\
     (!x y. x IN dart G /\ y IN dart G /\ cface M x y ==> cface G x y) /\
     (!x y. x IN dart G /\ y IN dart G /\ adj M x y ==> ~(h x = h y))
     ==> (!u x. x IN dart G /\ cface M u x
                ==> ext_col M (dart G) h c0 u = h x) /\
         (!u x y. x IN dart G /\ y IN dart G /\
                  cface M u x /\ cface M (edge_map M u) y
                  ==> ~(ext_col M (dart G) h c0 (edge_map M u) =
                        ext_col M (dart G) h c0 u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EXT_COL_CFACE THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CFACE_COLORING THEN
    EXISTS_TAC `G:(num)hypermap` THEN ASM_SIMP_TAC[];
    DISCH_TAC THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `adj (M:(num)hypermap) x y` MP_TAC THENL
     [MATCH_MP_TAC ADJ_INTRO THEN EXISTS_TAC `u:num` THEN CFACE_TAC[];
      ASM_MESON_TAC[]]]);;

let COLORING_EXT = prove
 (`!(G:(num)hypermap) (M:(num)hypermap) X L h c0.
     coloring G h /\ (!x. x IN dart G ==> x IN dart M) /\
     (!x y. x IN dart G /\ y IN dart G /\ cface M x y ==> cface G x y) /\
     (!x y. x IN dart G /\ y IN dart G /\ adj M x y ==> ~(h x = h y)) /\
     (!u. u IN dart M ==> (?x. x IN dart G /\ cface M u x) \/ cface M X u) /\
     (!x. x IN dart G ==> ~cface M X x) /\
     (!u. u IN dart M /\ adj M X u ==> ?a. MEM a L /\ cface M u a) /\
     (!u. u IN dart M /\ cface M X (edge_map M u)
          ==> edge_map M (edge_map M u) = u) /\
     (!a. MEM a L ==> a IN dart G /\ ~(h a = c0))
     ==> coloring M (ext_col M (dart G) h c0) /\
         (!x. x IN dart G ==> ext_col M (dart G) h c0 x = h x) /\
         ext_col M (dart G) h c0 X = c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL EXT_COL_OLD) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k' = ext_col M (dart G) (h:num->color) c0` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!u:num. cface (M:(num)hypermap) X u ==> (k':num->color) u = c0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "k'" THEN MATCH_MP_TAC EXT_COL_NEW THEN
    REPEAT STRIP_TAC THEN CFACE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CFACE_REFL] THEN
  SUBGOAL_THEN
   `!u:num. u IN dart M /\ cface (M:(num)hypermap) X u
            ==> ~((k':num->color) (edge_map M u) = k' u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?a:num. MEM a L /\ cface (M:(num)hypermap) (edge_map M u) a`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[EDGE_MAP_IN_DART] THEN
      MATCH_MP_TAC ADJ_INTRO THEN EXISTS_TAC `u:num` THEN
      ASM_REWRITE_TAC[CFACE_REFL];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[coloring] THEN CONJ_TAC THEN X_GEN_TAC `u:num` THEN
  DISCH_TAC THENL
   [ALL_TAC; EXPAND_TAC "k'" THEN ASM_SIMP_TAC[EXT_COL_FACE]] THEN
  SUBGOAL_THEN `edge_map (M:(num)hypermap) u IN dart M` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART]; ALL_TAC] THEN
  ASM_CASES_TAC `cface (M:(num)hypermap) X (u:num)` THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `cface (M:(num)hypermap) X (edge_map M u)` THEN
  ASM_MESON_TAC[]);;

let COLORING_EXT0 = prove
 (`!(G:(num)hypermap) (M:(num)hypermap) h c0.
     coloring G h /\
     (!x y. x IN dart G /\ y IN dart G /\ cface M x y ==> cface G x y) /\
     (!x y. x IN dart G /\ y IN dart G /\ adj M x y ==> ~(h x = h y)) /\
     (!u. u IN dart M ==> ?x. x IN dart G /\ cface M u x)
     ==> coloring M (ext_col M (dart G) h c0) /\
         (!x. x IN dart G ==> ext_col M (dart G) h c0 x = h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL EXT_COL_OLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CFACE_REFL; coloring; EXT_COL_FACE] THEN
  ASM_MESON_TAC[EDGE_MAP_IN_DART]);;

let CC_COLORING_MEM_CONG = prove
 (`!(H:(A)hypermap) cc1 cc2 k. (!z. MEM z cc1 <=> MEM z cc2)
     ==> (cc_coloring H cc1 k <=> cc_coloring H cc2 k)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cc_coloring; MEM_INSERTE]);;

let MEM_INSERTE_SPLIT = prove
 (`!(M:(num)hypermap) cc A D z.
     (!w. MEM w cc ==> MEM w A \/ w IN D) /\ (!w. MEM w A ==> MEM w cc) /\
     (!w. w IN D ==> ~(z = w) /\ ~(z = edge_map M w))
     ==> (MEM z (insertE M cc) <=> MEM z (insertE M A))`,
  REWRITE_TAC[MEM_INSERTE] THEN MESON_TAC[]);;

let MEM_INSERTE_OLD = prove
 (`!(M:(num)hypermap) (G:(num)hypermap) ccM ccG D x.
     (!y. MEM y ccM ==> MEM y ccG \/ ~(y IN D) /\ ~(edge_map M y IN D)) /\
     (!y. MEM y ccG ==> MEM y ccM /\ edge_map M y = edge_map G y) /\ x IN D
     ==> (MEM x (insertE M ccM) <=> MEM x (insertE G ccG))`,
  REWRITE_TAC[MEM_INSERTE] THEN MESON_TAC[]);;

let ctr_correct = new_definition
 `ctr_correct cp <=>
    !mr mc (k:num->color).
       LENGTH mr = cprsize cp /\ LENGTH mc = ctrmsize cp /\
       cc_coloring (FST(cpmap cp))
         (APPEND (mask_list mr (cpring (FST(cpmap cp)) (SND(cpmap cp))))
           (mask_list mc (ctrenum cp))) k /\
       cfctr_ok mr mc cp
       ==> ?k'. coloring (FST(cpmap (cfctr_map mr mc cp))) k' /\
                MAP k' (cpring (FST(cpmap (cfctr_map mr mc cp))) (SND(cpmap
                  (cfctr_map mr mc cp)))) =
                MAP k (mask_list (MAP (\b. ~b) mr) (cpring (FST(cpmap cp))
                  (SND(cpmap cp))))`;;

let CTR_CORRECT_R = prove
 (`!n cp. ctr_correct cp ==> ctr_correct (CONS (CpR n) cp)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ctr_correct] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`mr:bool list`; `mc:bool list`; `k:num->color`] THEN
  REWRITE_TAC[CPRSIZE_CONS_R; ctrmsize; ctrenum;
    CFCTR_OK_CLAUSES; CFCTR_MAP_CLAUSES;
              CPMAP_CONS_R; ecpR; cprsize] THEN
  STRIP_TAC THEN
  ABBREV_TAC `G = FST(cpmap (cp:(cpstep)list))` THEN ABBREV_TAC `x0 = SND(cpmap
    (cp:(cpstep)list))` THEN
  SUBGOAL_THEN `(x0:num) IN dart G /\ FINITE(dart G) /\ node_map G permutes
    dart G` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "x0"] THEN
    REWRITE_TAC[CPMAP_PT_IN_DART; FINITE_DART; NODE_MAP_PERMUTES];
    ALL_TAC] THEN
  SUBGOAL_THEN `cpring G (ecpR_pt G n x0) = rot_list n (cpring G (x0:num))`
    SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `n:num`]
      CPRING_ECPR_ROT_GEN) THEN
    ASM_REWRITE_TAC[ecpR]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rotr_list n (mr:bool list)`; `mc:bool list`;
    `k:num->color`]) THEN
  ASM_REWRITE_TAC[LENGTH_ROTR_LIST; cprsize] THEN ANTS_TAC THENL
   [SUBGOAL_THEN
     `cc_coloring G (APPEND (mask_list (rotr_list n mr) (cpring G x0))
       (mask_list mc (ctrenum cp))) k <=>
      cc_coloring G (APPEND (mask_list mr (rot_list n (cpring G x0)))
        (mask_list mc (ctrenum cp)))
                    (k:num->color)`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CC_COLORING_MEM_CONG THEN REWRITE_TAC[MEM_APPEND] THEN
    ASM_SIMP_TAC[MEM_MASK_LIST_ROT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':num->color` STRIP_ASSUME_TAC) THEN EXISTS_TAC
    `k':num->color` THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Gc = FST(cpmap (cfctr_map (rotr_list n mr) mc
    (cp:(cpstep)list)))` THEN
  ABBREV_TAC `yc = SND(cpmap (cfctr_map (rotr_list n mr) mc
    (cp:(cpstep)list)))` THEN
  SUBGOAL_THEN `!c. cpring Gc (ecpR_pt Gc c yc) = rot_list c (cpring Gc
    (yc:num))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`Gc:(num)hypermap`; `yc:num`; `c:num`]
     CPRING_ECPR_ROT_GEN) THEN
    REWRITE_TAC[ecpR; FINITE_DART; NODE_MAP_PERMUTES] THEN DISCH_THEN
      MATCH_MP_TAC THEN
    MAP_EVERY EXPAND_TAC ["Gc"; "yc"] THEN REWRITE_TAC[CPMAP_PT_IN_DART];
      ALL_TAC] THEN
  ASM_REWRITE_TAC[MAP_ROT_LIST] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
    [GSYM(ISPECL [`n:num`; `mr:bool list`] ROT_LIST_ROTR_CANCEL_GEN)] THEN
  REWRITE_TAC[MAP_ROT_LIST] THEN
  ASM_SIMP_TAC[MASK_LIST_ROT; LENGTH_MAP; LENGTH_ROTR_LIST] THEN
  REWRITE_TAC[MAP_ROT_LIST; GSYM MAP_TAKE_LIST; COUNT_NEGB]);;

(* ------------------------------------------------------------------------- *)
(* Ring colours: along the ring of a contracted map, the colours propagate   *)
(* through the contracted ring edges, so the colour of a ring dart is that   *)
(* of the first uncontracted dart from it on (RING_CHAIN; the ring is cut as *)
(* APPEND p q).                                                              *)
(* ------------------------------------------------------------------------- *)

let CC_RING_CONTRACTED = prove
 (`!(G:(num)hypermap) m r L (k:num->color) w.
     cc_coloring G (APPEND (mask_list m r) L) k /\ w IN dart G /\
     MEM w (mask_list m r)
     ==> k (edge_map G w) = k w`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cc_coloring]) THEN
  DISCH_THEN(MP_TAC o SPEC `w:num`) THEN
  ASM_REWRITE_TAC[MEM_INSERTE; MEM_APPEND] THEN
  DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[]);;

let MASK_CHAIN = prove
 (`!(k:A->B) l m z.
     LENGTH m = LENGTH l /\
     (!i. i < LENGTH l /\ EL i m
          ==> k (EL i l) = k (EL (SUC i) (APPEND l [z])))
     ==> k (HD (APPEND l [z])) =
         HD (APPEND (MAP k (mask_list (MAP (\b. ~b) m) l)) [k z])`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; LENGTH_EQ_NIL; APPEND; HD] THEN
  REPEAT GEN_TAC THENL
   [DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[MAP; MASK_LIST_CLAUSES; APPEND; HD];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `m:bool list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n)`; SUC_INJ; MAP] THEN
  BOOL_CASES_TAC `h':bool` THEN
  REWRITE_TAC[MASK_LIST_CLAUSES; MAP; APPEND; HD] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "step")) THEN
  USE_THEN "step" (MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[EL; HD; TL; LT_0] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  USE_THEN "step" (MP_TAC o SPEC `SUC i`) THEN
  REWRITE_TAC[EL; TL; LT_SUC] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MEM_MASK_LIST_EL = prove
 (`!m (l:A list) i.
     LENGTH m = LENGTH l /\ i < LENGTH l /\ EL i m
     ==> MEM (EL i l) (mask_list m l)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; NOT_SUC; ARITH_RULE `~(SUC n = 0)`;
              SUC_INJ] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC] THEN
  BOOL_CASES_TAC `h:bool` THEN
  ASM_SIMP_TAC[MASK_LIST_CLAUSES; MEM]);;

let RING_NODE_EL = prove
 (`!(G:(num)hypermap) x0 j.
     x0 IN dart G /\ proper_cpring G x0 /\ j < LENGTH(cpring G x0)
     ==> node_map G (EL (SUC j) (APPEND (cpring G x0) [node_map G x0])) =
         EL j (cpring G x0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] SIZE_PROPER_CPRING) THEN
  UNDISCH_TAC `j < LENGTH(cpring G (x0:num))` THEN
  ASM_SIMP_TAC[SIZE_CPRING; EL_APPEND] THEN REPEAT DISCH_TAC THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC RING_CONSEC_NODE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `SUC j - orbit_size (node_map G) (x0:num) = 0 /\
                  j = orbit_size (node_map G) x0 - 1`
     (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL; HD] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] RING_WRAP_NODE) THEN
    ASM_SIMP_TAC[EL; HEAD_CPRING] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

(* For a contract colouring k of G with ring mask APPEND mp mq, cut the      *)
(* ring as APPEND p q: k at the head of q is the colour of the first dart    *)
(* of q whose ring edge is not contracted, or k (node_map G x0).             *)

let RING_CHAIN = prove
 (`!(G:(num)hypermap) x0 p q mp mq L (k:num->color).
     x0 IN dart G /\ proper_cpring G x0 /\
     cpring G x0 = APPEND p q /\ LENGTH mp = LENGTH p /\
     LENGTH mq = LENGTH q /\
     cc_coloring G (APPEND (mask_list (APPEND mp mq) (cpring G x0)) L) k
     ==> k (HD (APPEND q [node_map G x0])) =
         HD (APPEND (MAP k (mask_list (MAP (\b. ~b) mq) q))
                    [k (node_map G x0)])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MASK_CHAIN THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `LENGTH(p:num list) + i`]
    RING_NODE_EL) THEN
  SUBGOAL_THEN
   `MEM (EL i q) (mask_list (APPEND mp mq) (cpring G x0)) /\
    EL (LENGTH(p:num list) + i) (cpring G x0) = EL i q /\
    EL (SUC(LENGTH(p:num list) + i)) (APPEND (cpring G x0) [node_map G x0]) =
    EL (SUC i) (APPEND q [node_map G x0])`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MASK_LIST_APPEND; MEM_APPEND; MEM_MASK_LIST_EL;
                 GSYM APPEND_ASSOC; EL_APPEND; LENGTH_APPEND;
                 ARITH_RULE `~(p + i < p)`; ADD_SUB2;
                 ARITH_RULE `~(SUC(p + i) < p) /\ SUC(p + i) - p = SUC i`;
                 ARITH_RULE `(SUC(p + i) < p + q <=> SUC i < q) /\
                             SUC(p + i) - (p + q) = SUC i - q`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LT_ADD_LCANCEL] THEN
  ABBREV_TAC `v = EL (SUC i) (APPEND q [node_map (G:(num)hypermap) x0])` THEN
  ABBREV_TAC `w = EL i (q:num list)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:num) IN dart G` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_MASK_LIST; MEM_CPRING_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `APPEND mp mq:bool list`;
    `cpring G (x0:num)`; `L:num list`; `k:num->color`; `w:num`]
    CC_RING_CONTRACTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check
    (fun th -> lhs(concl th) = `node_map (G:(num)hypermap) v`)) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [GSYM(ISPEC `G:(num)hypermap` nodeK)] THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [cc_coloring]) THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART]);;

(* ------------------------------------------------------------------------- *)
(* The Y step: the fresh darts and edges of ecpY G x0, the colouring         *)
(* extensions to ecpY G x0 and ecpU G x0 (COLORING_ECPY_RING,                *)
(* COLORING_ECPU_RING), the colours that a contract colouring of ecpY G x0   *)
(* gives its new darts (CC_ECPY_APEX) and its restriction to G               *)
(* (CC_ECPY_RESTRICT), and the base case [CpY] (CTR_CORRECT_Y0).             *)
(* ------------------------------------------------------------------------- *)

let EDGE_ECPY_RINGB = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> edge_map (ecpY H x0)
   (SND(new_dart2(dart H))) = ecpU_pt H`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`;
    `SND(new_dart2(dart(H:(num)hypermap)))`] EDGE_ECPY_ECPU) THEN
  ASM_SIMP_TAC[FINITE_DART; SND_NEW_IN_ECPU] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EDGE_ECPU_B_APEX THEN ASM_REWRITE_TAC[FINITE_DART]);;

let EDGE_ECPY_ECPUPT = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> edge_map (ecpY H x0) (ecpU_pt H) =
   SND(new_dart2(dart H))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `ecpU_pt (H:(num)hypermap)`]
    EDGE_ECPY_ECPU) THEN
  ASM_SIMP_TAC[FINITE_DART; ECPU_PT_IN_DART; ECPU_EDGE_PT]);;

let ECPY_FRESH = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> ~(ecpU_pt H IN dart H) /\ ~(SND(new_dart2(dart H)) IN dart H) /\
         ~(ecpY_pt H x0 IN dart H) /\ ~(SND(new_dart2(dart(ecpU H x0))) IN dart
           H) /\
         ~(ecpU_pt H = SND(new_dart2(dart H))) /\
         ~(ecpY_pt H x0 = ecpU_pt H) /\ ~(ecpY_pt H x0 = SND(new_dart2(dart
           H))) /\
         ~(SND(new_dart2(dart(ecpU H x0))) = ecpU_pt H) /\
         ~(SND(new_dart2(dart(ecpU H x0))) = SND(new_dart2(dart H))) /\
         ~(ecpY_pt H x0 = SND(new_dart2(dart(ecpU H x0))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN
    REWRITE_TAC[FINITE_DART] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `dart(ecpU (H:(num)hypermap) x0)` NEW_DART2_FRESH) THEN
    REWRITE_TAC[FINITE_DART] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN REWRITE_TAC[IN_INSERT;
    DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ecpY_pt; ecpN_pt; ecpU_pt] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    ASM_REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN
  ASM_MESON_TAC[]);;

let DART_ECPY_CASES = prove
 (`!(H:(num)hypermap) x0 z. x0 IN dart H
     ==> (z IN dart(ecpY H x0) <=>
          z = ecpY_pt H x0 \/ z = SND(new_dart2(dart(ecpU H x0))) \/ z =
            ecpU_pt H \/
          z = SND(new_dart2(dart H)) \/ z IN dart H)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY_pt; ecpN_pt; ecpU_pt] THEN
  ASM_SIMP_TAC[ECPY_DART; IN_INSERT] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    REWRITE_TAC[IN_INSERT]);;

let ADJ_ICPY_IMP = prove
 (`!(H:(num)hypermap) x0 x y. x0 IN dart H /\ FINITE(dart H) /\ edge_map H
   permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\ x IN dart H /\
       y IN dart H /\
     adj (ecpY H x0) x y ==> adj H x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adj]) THEN
  REWRITE_TAC[rlink; GSYM cface] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(z:num) IN dart H` THENL
   [REWRITE_TAC[adj; rlink; GSYM cface] THEN EXISTS_TAC `z:num` THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `z:num`] EDGE_ECPY_OLD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CFACE_TAC[ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_ECPY_PROJ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPY_APEX_TWO_CYCLE) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] EDGE_ECPY_B_GEN) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] EDGE_ECPY_RINGB) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_ECPY_APEX_OLD) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `x:num`] DART_H_SUBSET_ECPY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:num) IN dart(ecpY H x0)` MP_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[DART_ECPY_CASES] THEN STRIP_TAC THEN CFACE_TAC[]);;

let ADJ_ECPY_IMP = prove
 (`!(H:(num)hypermap) x0 u. x0 IN dart H /\ proper_cpring H x0 /\ FINITE(dart
   H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\ face_map H
       permutes dart H /\
     adj (ecpY H x0) (ecpY_pt H x0) u
     ==> cface (ecpY H x0) u (node_map H x0) \/ cface (ecpY H x0) u x0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adj]) THEN
  REWRITE_TAC[rlink; GSYM cface] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `z:num`] FACE_ECPY_APEX) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_ECPY_B_PT) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] EDGE_ECPY_APEX_GEN) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_NODE_ECPY) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] EDGE_ECPY_ECPUPT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CFACE_TAC[]);;

let EDGE_INVOL_ECPY = prove
 (`!(H:(num)hypermap) x0 u. x0 IN dart H /\ FINITE(dart H) /\ edge_map H
   permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\
     cface (ecpY H x0) (ecpY_pt H x0) (edge_map (ecpY H x0) u)
     ==> edge_map (ecpY H x0) (edge_map (ecpY H x0) u) = u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `edge_map (ecpY H x0) u`]
    FACE_ECPY_APEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `u = SND(new_dart2(dart(ecpU (H:(num)hypermap) x0)))`
     SUBST1_TAC THENL
     [MATCH_MP_TAC EDGEI THEN EXISTS_TAC `ecpY (H:(num)hypermap) x0` THEN
      ASM_SIMP_TAC[EDGE_ECPY_B_GEN]; ALL_TAC] THEN
    ASM_SIMP_TAC[EDGE_ECPY_B_GEN; EDGE_ECPY_APEX_GEN];
    SUBGOAL_THEN `u = SND(new_dart2(dart(H:(num)hypermap)))` SUBST1_TAC THENL
     [MATCH_MP_TAC EDGEI THEN EXISTS_TAC `ecpY (H:(num)hypermap) x0` THEN
      ASM_SIMP_TAC[EDGE_ECPY_RINGB]; ALL_TAC] THEN
    ASM_SIMP_TAC[EDGE_ECPY_RINGB; EDGE_ECPY_ECPUPT]]);;

let COLORING_ECPY = prove
 (`!(G:(num)hypermap) x0 h c0.
     coloring G h /\ x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart
       G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\ proper_cpring
       G x0 /\
     ~(h (node_map G x0) = c0) /\ ~(h x0 = c0)
     ==> coloring (ecpY G x0) (ext_col (ecpY G x0) (dart G) h c0) /\
         (!x. x IN dart G ==> ext_col (ecpY G x0) (dart G) h c0 x = h x) /\
         ext_col (ecpY G x0) (dart G) h c0 (ecpY_pt G x0) = c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COLORING_EXT THEN
  EXISTS_TAC `[node_map G x0; x0:num]` THEN ASM_REWRITE_TAC[] THEN REPEAT
    CONJ_TAC THENL
   [ASM_MESON_TAC[DART_H_SUBSET_ECPY];
    ASM_MESON_TAC[CFACE_ECPY_PROJ];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ADJ_COLORING THEN
      EXISTS_TAC `G:(num)hypermap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ADJ_ICPY_IMP THEN EXISTS_TAC `x0:num`
      THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
      FBAND_ICPY) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[CFACE_SYM_GEN];
    ASM_SIMP_TAC[CFACE_ECPY_APEX_OLD];
    REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
      ADJ_ECPY_IMP) THEN
    ASM_REWRITE_TAC[MEM] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EDGE_INVOL_ECPY THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_SIMP_TAC[NODE_MAP_IN_DART]]);;

let ADJ_ICPU_IMP = prove
 (`!(H:(num)hypermap) x0 x y. x0 IN dart H /\ FINITE(dart H) /\ edge_map H
   permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\ x IN dart H /\
       y IN dart H /\
     adj (ecpU H x0) x y ==> adj H x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adj]) THEN REWRITE_TAC[rlink; GSYM
    cface] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `ecpU (H:(num)hypermap) x0` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `H:(num)hypermap` ECPU_PT_NOT_IN_DART) THEN ASM_REWRITE_TAC[]
    THEN DISCH_TAC THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN ASM_REWRITE_TAC[]
    THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:num) IN dart(ecpU H x0)` MP_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_IN THEN EXISTS_TAC `face_map (ecpU (H:(num)hypermap)
     x0)` THEN
    EXISTS_TAC `x:num` THEN ASM_SIMP_TAC[DART_H_SUBSET_ECPU] THEN
    UNDISCH_TAC `cface (ecpU H x0) (x:num) z` THEN REWRITE_TAC[cface; face];
      ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN REWRITE_TAC[IN_INSERT;
    GSYM ecpU_pt] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `cface (ecpU H x0) (ecpU_pt H) (x:num)` MP_TAC THENL
     [MATCH_MP_TAC CFACE_SYM_GEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[cface] THEN ASM_SIMP_TAC[FACE_ECPU_APEX_SING] THEN DISCH_THEN
      SUBST_ALL_TAC THEN
    UNDISCH_TAC `ecpU_pt H IN dart (H:(num)hypermap)` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `cface (ecpU H x0) (edge_map (ecpU H x0) (SND(new_dart2(dart
      H)))) (y:num)` THEN
    ASM_SIMP_TAC[EDGE_ECPU_B_APEX] THEN REWRITE_TAC[cface] THEN
    ASM_SIMP_TAC[FACE_ECPU_APEX_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ecpU_pt H IN dart (H:(num)hypermap)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[adj; rlink; GSYM cface] THEN EXISTS_TAC `z:num` THEN
    SUBGOAL_THEN `edge_map (ecpU H x0) z = edge_map H (z:num)`
      SUBST_ALL_TAC THENL
     [ASM_SIMP_TAC[EDGE_ECPU_OLD]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC CFACE_ECPU_PROJ THEN EXISTS_TAC `x0:num` THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART]]);;

let COLORING_ECPU = prove
 (`!(G:(num)hypermap) x0 h c0.
     coloring G h /\ x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart
       G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\ ~(h (node_map
       G x0) = c0)
     ==> coloring (ecpU G x0) (ext_col (ecpU G x0) (dart G) h c0) /\
         (!x. x IN dart G ==> ext_col (ecpU G x0) (dart G) h c0 x = h x) /\
         ext_col (ecpU G x0) (dart G) h c0 (ecpU_pt G) = c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COLORING_EXT THEN
  EXISTS_TAC `[node_map G x0:num]` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[DART_H_SUBSET_ECPU];
    ASM_MESON_TAC[CFACE_ECPU_PROJ];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ADJ_COLORING THEN
      EXISTS_TAC `G:(num)hypermap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ADJ_ICPU_IMP THEN EXISTS_TAC `x0:num`
      THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
      FBAND_ICPU) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[CFACE_SYM_GEN];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[cface] THEN
      ASM_SIMP_TAC[FACE_ECPU_APEX_SING] THEN
    DISCH_THEN SUBST_ALL_TAC THEN MP_TAC(ISPEC `G:(num)hypermap`
      ECPU_PT_NOT_IN_DART) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[MEM] THEN
    EXISTS_TAC `node_map (G:(num)hypermap) x0` THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPU_B_NODE) THEN
    UNDISCH_TAC `adj (ecpU G x0) (ecpU_pt G) (u:num)` THEN
    ASM_SIMP_TAC[ADJ_ECPU_APEX] THEN REPEAT STRIP_TAC THEN CFACE_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `edge_map (ecpU G x0) u = ecpU_pt (G:(num)hypermap)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `cface (ecpU G x0) (ecpU_pt G) (edge_map (ecpU G x0) u)` THEN
      REWRITE_TAC[cface] THEN ASM_SIMP_TAC[FACE_ECPU_APEX_SING]; ALL_TAC] THEN
    SUBGOAL_THEN `u = SND(new_dart2(dart (G:(num)hypermap)))` SUBST1_TAC THENL
     [MATCH_MP_TAC EDGEI THEN EXISTS_TAC `ecpU (G:(num)hypermap) x0` THEN
      ASM_SIMP_TAC[EDGE_ECPU_B_APEX]; ALL_TAC] THEN
    ASM_SIMP_TAC[EDGE_ECPU_B_APEX; ECPU_EDGE_PT];
    REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_SIMP_TAC[NODE_MAP_IN_DART]]);;

let CC_ECPY_FACE_FACTS = prove
 (`!(G:(num)hypermap) x0 cc (k:num->color).
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\ node_map G
       permutes dart G /\
     face_map G permutes dart G /\ proper_cpring G x0 /\ cc_coloring (ecpY G
       x0) cc k
     ==> k (SND(new_dart2(dart G))) = k (node_map G x0) /\
         k (ecpY_pt G x0) = k (ecpU_pt G) /\
         k (SND(new_dart2(dart(ecpU G x0)))) = k x0`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CFACE_CC_COLORING THEN
  MAP_EVERY EXISTS_TAC [`ecpY (G:(num)hypermap) x0`; `cc:num list`] THEN
    ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[HEAD_IN_DART_ECPY; CFACE_NODE_ECPY];
    ASM_SIMP_TAC[ECPY_PT_IN_DART] THEN
    MP_TAC(ISPECL [`ecpY (G:(num)hypermap) x0`; `ecpY_pt (G:(num)hypermap) x0`]
      CFT_FACE) THEN
    ASM_SIMP_TAC[ECPY_APEX_TWO_CYCLE];
    ASM_SIMP_TAC[CFACE_ECPY_B_PT] THEN ASM_SIMP_TAC[DART_ECPY_CASES]]);;

let CC_ECPY_NEW_EDGES = prove
 (`!(G:(num)hypermap) x0 b1 b2 mr R mK K (k:num->color).
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\ node_map G
       permutes dart G /\
     face_map G permutes dart G /\
     (!w. MEM w R ==> w IN dart G) /\ (!w. MEM w K ==> w IN dart G) /\
     cc_coloring (ecpY G x0)
       (APPEND (mask_list (CONS b1 (CONS b2 mr)) (CONS (SND(new_dart2(dart G)))
         (CONS (ecpY_pt G x0) R)))
               (mask_list mK K)) k
     ==> (k (ecpU_pt G) = k (SND(new_dart2(dart G))) <=> b1) /\
         (k (SND(new_dart2(dart(ecpU G x0)))) = k (ecpY_pt G x0) <=> b2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. ~(z IN dart G)
        ==> (MEM z (insertE (ecpY (G:(num)hypermap) x0)
                     (APPEND (mask_list (CONS b1 (CONS b2 mr))
                                (CONS (SND(new_dart2(dart G))) (CONS (ecpY_pt G
                                  x0) R)))
                             (mask_list mK K))) <=>
             MEM z (insertE (ecpY G x0)
                     (mask_list [b1;b2] [SND(new_dart2(dart G)); ecpY_pt G
                       x0])))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:num` THEN DISCH_TAC THEN MATCH_MP_TAC MEM_INSERTE_SPLIT THEN
    EXISTS_TAC `dart(G:(num)hypermap)` THEN
    REWRITE_TAC[MEM_APPEND; MEM_MASK_LIST_CONS; MASK_LIST_CLAUSES; MEM] THEN
      REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     DISJ2_TAC THENL
       [UNDISCH_TAC `!w. MEM w R ==> w IN dart (G:(num)hypermap)`;
        UNDISCH_TAC `!w. MEM w K ==> w IN dart (G:(num)hypermap)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MEM_MASK_LIST THENL
       [EXISTS_TAC `mr:bool list`; EXISTS_TAC `mK:bool list`] THEN
         ASM_REWRITE_TAC[];
      MESON_TAC[];
      X_GEN_TAC `w:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EDGE_ECPY_OLD] THEN
      ASM_MESON_TAC[EDGE_MAP_IN_DART]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cc_coloring]) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `SND(new_dart2(dart(G:(num)hypermap)))` th) THEN
                       MP_TAC(SPEC `ecpY_pt (G:(num)hypermap) x0` th)) THEN
  ASM_SIMP_TAC[HEAD_IN_DART_ECPY; ECPY_PT_IN_DART; EDGE_ECPY_RINGB;
    EDGE_ECPY_APEX_GEN] THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN
  ASM_REWRITE_TAC[MASK_LIST_CLAUSES; INSERTE_CLAUSES; MEM] THEN
  ASM_SIMP_TAC[EDGE_ECPY_RINGB; EDGE_ECPY_APEX_GEN] THEN MESON_TAC[]);;

let CC_ECPY_APEX = prove
 (`!(G:(num)hypermap) x0 b1 b2 mr R mK K (k:num->color).
     x0 IN dart G /\ proper_cpring G x0 /\
     (!w. MEM w R ==> w IN dart G) /\ (!w. MEM w K ==> w IN dart G) /\
     cc_coloring (ecpY G x0)
       (APPEND (mask_list (CONS b1 (CONS b2 mr))
                  (CONS (SND(new_dart2(dart G))) (CONS (ecpY_pt G x0) R)))
               (mask_list mK K)) k
     ==> k (SND(new_dart2(dart G))) = k (node_map G x0) /\
         (k (ecpY_pt G x0) = k (node_map G x0) <=> b1) /\
         (k (ecpY_pt G x0) = k x0 <=> b2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL CC_ECPY_NEW_EDGES) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`;
    `APPEND (mask_list (CONS b1 (CONS b2 mr))
               (CONS (SND(new_dart2(dart (G:(num)hypermap))))
                     (CONS (ecpY_pt G x0) R)))
            (mask_list mK K)`; `k:num->color`] CC_ECPY_FACE_FACTS) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  MESON_TAC[]);;

let NODE_CPMAP0_1 = prove
 (`node_map cpmap0 1 = 0 /\ 1 IN dart cpmap0 /\ 0 IN dart cpmap0`,
  REWRITE_TAC[CPMAP0_COMPONENTS; swap; IN_INSERT; ARITH_EQ]);;

let COLORING_CPMAP0 = prove
 (`!k:num->color. coloring cpmap0 k <=> ~(k 0 = k 1)`,
  REWRITE_TAC[coloring; CPMAP0_COMPONENTS; IN_INSERT; NOT_IN_EMPTY; I_THM] THEN
  REWRITE_TAC[MESON[] `(!x:num. x = a \/ x = b ==> (P:num->bool) x) <=> P a /\
    P b`] THEN
  REWRITE_TAC[swap; ARITH_EQ] THEN MESON_TAC[]);;

let MEM_CPMAP0_LISTS = prove
 (`(!w. MEM w [1] ==> w IN dart cpmap0) /\ (!w:num. MEM w [] ==> w IN dart
   cpmap0)`,
  REWRITE_TAC[MEM] THEN MESON_TAC[NODE_CPMAP0_1]);;

let RING_Y0 = prove
 (`cpring (ecpY cpmap0 1) (ecpY_pt cpmap0 1) = [SND(new_dart2(dart cpmap0));
   ecpY_pt cpmap0 1; 1]`,
  MP_TAC(ISPECL [`cpmap0`; `1`] CPRING_ECPY) THEN
  REWRITE_TAC[NODE_CPMAP0_1; PROPER_CPMAP0; CPRING_CPMAP0; TL]);;

let CC_ECPY_RESTRICT = prove
 (`!(G:(num)hypermap) x0 b1 b2 mr R mK K (k:num->color).
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\ node_map G
       permutes dart G /\
     face_map G permutes dart G /\
     (!w. MEM w R ==> w IN dart G) /\ (!w. MEM w K ==> w IN dart G) /\
     cc_coloring (ecpY G x0)
       (APPEND (mask_list (CONS b1 (CONS b2 mr)) (CONS (SND(new_dart2(dart G)))
         (CONS (ecpY_pt G x0) R)))
               (mask_list mK K)) k
     ==> cc_coloring G (APPEND (mask_list mr R) (mask_list mK K)) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. MEM y (mask_list mr R) \/ MEM y (mask_list mK K) ==> y IN
    dart (G:(num)hypermap)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THENL
     [UNDISCH_TAC `!w. MEM w R ==> w IN dart (G:(num)hypermap)` THEN DISCH_THEN
       MATCH_MP_TAC THEN
      MATCH_MP_TAC MEM_MASK_LIST THEN EXISTS_TAC `mr:bool list` THEN
        ASM_REWRITE_TAC[];
      UNDISCH_TAC `!w. MEM w K ==> w IN dart (G:(num)hypermap)` THEN DISCH_THEN
        MATCH_MP_TAC THEN
      MATCH_MP_TAC MEM_MASK_LIST THEN EXISTS_TAC `mK:bool list` THEN
        ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CC_COLORING_RESTRICT THEN
  MAP_EVERY EXISTS_TAC
   [`ecpY (G:(num)hypermap) x0`;
    `APPEND (mask_list (CONS b1 (CONS b2 mr))
               (CONS (SND(new_dart2(dart (G:(num)hypermap)))) (CONS (ecpY_pt G
                 x0) R)))
            (mask_list mK K)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[DART_H_SUBSET_ECPY];
    ASM_SIMP_TAC[EDGE_ECPY_OLD];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CFACE_ECPY_LIFT THEN
      ASM_REWRITE_TAC[CFT_FACE];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ecpY (G:(num)hypermap) x0`; `G:(num)hypermap`;
                   `APPEND (mask_list (CONS b1 (CONS b2 mr))
                              (CONS (SND(new_dart2(dart (G:(num)hypermap))))
                                (CONS (ecpY_pt G x0) R)))
                           (mask_list mK K)`;
                   `APPEND (mask_list mr (R:num list)) (mask_list mK (K:num
                     list))`; `dart(G:(num)hypermap)`; `x:num`]
                  MEM_INSERTE_OLD) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MEM_APPEND; MEM_MASK_LIST_CONS] THEN CONJ_TAC THEN X_GEN_TAC
      `y:num` THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[EDGE_ECPY_RINGB;
       EDGE_ECPY_APEX_GEN];
      DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
        EDGE_ECPY_OLD THEN
      ASM_SIMP_TAC[]]]);;

let COLORING_ECPY_RING = prove
 (`!(G:(num)hypermap) x0 h c0.
     coloring G h /\ x0 IN dart G /\
     ~(h (node_map G x0) = c0) /\ ~(h x0 = c0)
     ==> ?k. coloring (ecpY G x0) k /\
             MAP k (cpring (ecpY G x0) (ecpY_pt G x0)) =
             CONS (h (node_map G x0)) (CONS c0 (MAP h (TL(cpring G x0))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `proper_cpring G (x0:num)` ASSUME_TAC THENL
   [ASM_MESON_TAC[proper_cpring; COLORING_NODE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `h:num->color`; `c0:color`]
    COLORING_ECPY) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  ABBREV_TAC `k = ext_col (ecpY G x0) (dart G) (h:num->color) c0` THEN
  STRIP_TAC THEN EXISTS_TAC `k:num->color` THEN
  ASM_SIMP_TAC[CPRING_ECPY; MAP; CONS_11] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`ecpY (G:(num)hypermap) x0`; `k:num->color`;
                   `SND(new_dart2(dart (G:(num)hypermap)))`;
                   `node_map (G:(num)hypermap) x0`] CFACE_COLORING) THEN
    ASM_SIMP_TAC[HEAD_IN_DART_ECPY; CFACE_NODE_ECPY; FINITE_DART;
                 EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[NODE_MAP_IN_DART];
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[MEM_CPRING_IN_DART; MEM_TL_IMP; CPRING_NONEMPTY]]);;

let COLORING_ECPU_RING = prove
 (`!(G:(num)hypermap) x0 h c0.
     coloring G h /\ x0 IN dart G /\ ~(h (node_map G x0) = c0)
     ==> ?k. coloring (ecpU G x0) k /\
             MAP k (cpring (ecpU G x0) (ecpU_pt G)) =
             CONS (h (node_map G x0)) (CONS c0 (MAP h (cpring G x0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 < orbit_size (node_map G) (x0:num)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] SIZE_PROPER_CPRING) THEN
    ASM_SIMP_TAC[SIZE_CPRING] THEN
    ASM_MESON_TAC[proper_cpring; COLORING_NODE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `h:num->color`; `c0:color`]
    COLORING_ECPU) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  ABBREV_TAC `k = ext_col (ecpU G x0) (dart G) (h:num->color) c0` THEN
  STRIP_TAC THEN EXISTS_TAC `k:num->color` THEN
  ASM_SIMP_TAC[CPRING_ECPU; MAP; CONS_11] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`ecpU (G:(num)hypermap) x0`; `k:num->color`;
                   `SND(new_dart2(dart (G:(num)hypermap)))`;
                   `node_map (G:(num)hypermap) x0`] CFACE_COLORING) THEN
    ASM_SIMP_TAC[SND_NEW_IN_ECPU; CFACE_ECPU_B_NODE; FINITE_DART;
                 EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[NODE_MAP_IN_DART];
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[MEM_CPRING_IN_DART]]);;

let CTR_Y0_CASE = prove
 (`!b1 b2 b3 (k:num->color).
     cc_coloring (ecpY cpmap0 1)
       (APPEND (mask_list [b1;b2;b3] [SND(new_dart2(dart cpmap0)); ecpY_pt
         cpmap0 1; 1])
               (mask_list [] [])) k /\
     ~(nsp b1 b2 b3)
     ==> ?k'. coloring (FST(cpmap (if b1 \/ (b2 \/ b3) then [] else [CpY]))) k'
       /\
              MAP k' (cpring (FST(cpmap (if b1 \/ (b2 \/ b3) then [] else
                [CpY])))
                             (SND(cpmap (if b1 \/ (b2 \/ b3) then [] else
                               [CpY])))) =
              MAP k (mask_list (MAP (\b. ~b) [b1;b2;b3])
                               [SND(new_dart2(dart cpmap0)); ecpY_pt cpmap0 1;
                                 1])`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`cpmap0`; `1`; `b1:bool`; `b2:bool`; `[b3:bool]`; `[1]`;
    `[]:bool list`;
                 `[]:num list`; `k:num->color`] CC_ECPY_NEW_EDGES) THEN
  MP_TAC(ISPECL [`cpmap0`; `1`; `b1:bool`; `b2:bool`; `[b3:bool]`; `[1]`;
    `[]:bool list`;
                 `[]:num list`; `k:num->color`] CC_ECPY_RESTRICT) THEN
  MP_TAC(ISPECL [`cpmap0`; `1`;
                 `APPEND (mask_list [b1;b2;b3] [SND(new_dart2(dart cpmap0));
                   ecpY_pt cpmap0 1; 1])
                         (mask_list [] [])`; `k:num->color`]
                           CC_ECPY_FACE_FACTS) THEN
  REWRITE_TAC[CPMAP0_HYP; PROPER_CPMAP0; NODE_CPMAP0_1; MEM_CPMAP0_LISTS] THEN
  REWRITE_TAC[CPMAP_NIL_PAIR; CPMAP_CONS_Y; FST; SND; RING_Y0;
              CPRING_CPMAP0] THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`; `b3:bool`] THEN
  REWRITE_TAC[nsp; MASK_LIST_CLAUSES; MAP; APPEND; CC_COLORING_NIL] THEN
  DISCH_THEN(fun f1 -> DISCH_THEN(fun f2 -> DISCH_THEN(fun f3 -> DISCH_THEN(fun
    cc ->
    MP_TAC(MATCH_MP f1 cc) THEN MP_TAC(MATCH_MP f2 cc) THEN
    MP_TAC(MATCH_MP f3 cc) THEN MP_TAC cc)))) THEN
  REWRITE_TAC[CC_COLORING_NIL] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CPMAP_NIL_PAIR; CPMAP_CONS_Y; FST; SND; CPRING_CPMAP0;
              RING_Y0] THENL
   [EXISTS_TAC `k:num->color` THEN ASM_REWRITE_TAC[MAP; CONS_11];
    EXISTS_TAC `k:num->color` THEN ASM_REWRITE_TAC[MAP; CONS_11];
    EXISTS_TAC `\z:num. if z = 0 then (k:num->color) (SND(new_dart2(dart
      cpmap0)))
                        else k (ecpY_pt cpmap0 1)` THEN
    REWRITE_TAC[COLORING_CPMAP0; MAP; ARITH_EQ; CONS_11] THEN ASM_MESON_TAC[];
    EXISTS_TAC `k:num->color` THEN ASM_REWRITE_TAC[MAP; CONS_11]]);;

let CTR_CORRECT_Y0 = prove
 (`ctr_correct [CpY]`,
  REWRITE_TAC[ctr_correct] THEN
  MAP_EVERY X_GEN_TAC [`mr:bool list`; `mc:bool list`; `k:num->color`] THEN
  REWRITE_TAC[cprsize; ctrmsize; ctrenum; CPMAP_CONS_Y;
    CPMAP_NIL_PAIR;
              FST; SND; RING_Y0; LENGTH; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REWRITE_TAC[CFCTR_OK_Y0; CFCTR_MAP_Y0] THEN MATCH_ACCEPT_TAC CTR_Y0_CASE);;

(* ------------------------------------------------------------------------- *)
(* The H step: fresh darts, edges and restriction of a contract colouring    *)
(* of ecpH G x0 to G.                                                        *)
(* ------------------------------------------------------------------------- *)

let ECPH_FRESH = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G
     ==> ~(ecpH_pt G x0 IN dart G) /\
         ~(SND(new_dart2(dart(ecpY G x0))) IN dart G) /\
         ~(ecpH_pt G x0 = SND(new_dart2(dart(ecpY G x0))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `dart(ecpY (G:(num)hypermap) x0)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART; ecpH_pt; ecpN_pt] THEN
  ASM_MESON_TAC[DART_H_SUBSET_ECPY]);;

let EDGE_ECPH_RINGB = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G
     ==> edge_map (ecpH G x0) (SND(new_dart2(dart G))) = ecpU_pt G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPECL [`ecpY (G:(num)hypermap) x0`; `ecpY_pt (G:(num)hypermap) x0`;
                 `SND(new_dart2(dart (G:(num)hypermap)))`]
    EDGE_ECPN_OLD_GEN) THEN
  ASM_SIMP_TAC[DART_ECPY_CASES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EDGE_ECPY_RINGB]);;

let CC_ECPH_RESTRICT = prove
 (`!(G:(num)hypermap) x0 b1 b2 b3 b4 b5 mr R mK K (k:num->color).
     x0 IN dart G /\ proper_cpring G x0 /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\
     (!w. MEM w R ==> w IN dart G) /\ (!w. MEM w K ==> w IN dart G) /\
     cc_coloring (ecpH G x0)
       (APPEND (mask_list (CONS b1 (CONS b2 mr))
                  (CONS (SND(new_dart2(dart G))) (CONS (ecpH_pt G x0) R)))
               (mask_list (CONS b3 (CONS b4 (CONS b5 mK)))
                  (CONS (ecpY_pt G x0) (CONS (node_map G x0) (CONS x0 K))))) k
     ==> cc_coloring G
           (APPEND (mask_list (CONS b4 (CONS b5 mr))
                      (CONS (node_map G x0) (CONS x0 R)))
                   (mask_list mK K)) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(node_map G x0:num) IN dart G` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. MEM y (mask_list mr R) \/ MEM y (mask_list mK K)
        ==> y IN dart (G:(num)hypermap)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THENL
     [UNDISCH_TAC `!w. MEM w R ==> w IN dart (G:(num)hypermap)` THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MEM_MASK_LIST THEN
      EXISTS_TAC `mr:bool list` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `!w. MEM w K ==> w IN dart (G:(num)hypermap)` THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MEM_MASK_LIST THEN
      EXISTS_TAC `mK:bool list` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CC_COLORING_RESTRICT THEN
  MAP_EVERY EXISTS_TAC
   [`ecpH (G:(num)hypermap) x0`;
    `APPEND (mask_list (CONS b1 (CONS b2 mr))
               (CONS (SND(new_dart2(dart (G:(num)hypermap))))
                     (CONS (ecpH_pt G x0) R)))
            (mask_list (CONS b3 (CONS b4 (CONS b5 mK)))
               (CONS (ecpY_pt G x0) (CONS (node_map G x0) (CONS x0 K))))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[DART_SUBSET_ECPH; SUBSET];
    ASM_SIMP_TAC[EDGE_ECPH_OLD];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CFACE_ECPH_LIFT_GEN THEN
    ASM_REWRITE_TAC[CFACE_STEP];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`ecpH (G:(num)hypermap) x0`; `G:(num)hypermap`;
      `APPEND (mask_list (CONS b1 (CONS b2 mr))
                 (CONS (SND(new_dart2(dart (G:(num)hypermap))))
                       (CONS (ecpH_pt G x0) R)))
              (mask_list (CONS b3 (CONS b4 (CONS b5 mK)))
                 (CONS (ecpY_pt G x0) (CONS (node_map G x0) (CONS x0 K))))`;
      `APPEND (mask_list (CONS b4 (CONS b5 mr))
                 (CONS (node_map (G:(num)hypermap) x0) (CONS x0 R)))
              (mask_list mK (K:num list))`;
      `dart(G:(num)hypermap)`; `x:num`] MEM_INSERTE_OLD) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MEM_APPEND; MEM_MASK_LIST_CONS] THEN CONJ_TAC THEN
    X_GEN_TAC `y:num` THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[EDGE_ECPH_RINGB; EDGE_ECPH_APEX; EDGE_ECPH_ECPYPT];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EDGE_ECPH_OLD THEN
      ASM_SIMP_TAC[]]]);;

let DART_ECPH_CASES = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ proper_cpring G x0
     ==> (z IN dart(ecpH G x0) <=>
          z = ecpH_pt G x0 \/ z = SND(new_dart2(dart(ecpY G x0))) \/
          z IN dart(ecpY G x0))`,
  SIMP_TAC[ECPH_DART; IN_INSERT; ecpH_pt; ecpN_pt]);;

let ECPH_FRESH2 = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G
     ==> ~(ecpH_pt G x0 = SND(new_dart2(dart G))) /\
         ~(ecpH_pt G x0 = ecpY_pt G x0) /\
         ~(ecpH_pt G x0 = ecpU_pt G) /\
         ~(ecpH_pt G x0 = SND(new_dart2(dart(ecpU G x0)))) /\
         ~(SND(new_dart2(dart(ecpY G x0))) = SND(new_dart2(dart G))) /\
         ~(SND(new_dart2(dart(ecpY G x0))) = ecpY_pt G x0) /\
         ~(SND(new_dart2(dart(ecpY G x0))) = ecpU_pt G) /\
         ~(SND(new_dart2(dart(ecpY G x0))) = SND(new_dart2(dart(ecpU G x0))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `dart(ecpY (G:(num)hypermap) x0)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART; ecpH_pt; ecpN_pt] THEN
  ASM_SIMP_TAC[DART_ECPY_CASES] THEN MESON_TAC[]);;

let CC_ECPH_FACE_FACTS = prove
 (`!(G:(num)hypermap) x0 cc (k:num->color).
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\ cc_coloring (ecpH G x0) cc k
     ==> k (SND(new_dart2(dart G))) = k (node_map G x0) /\
         k (ecpY_pt G x0) = k (ecpH_pt G x0) /\
         k (ecpU_pt G) = k (ecpY_pt G x0) /\
         k (SND(new_dart2(dart(ecpU G x0)))) = k x0 /\
         k (SND(new_dart2(dart(ecpY G x0)))) = k (face_map G (edge_map G x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV; ALL_TAC; ALL_TAC; CONV_TAC SYM_CONV;
    CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC CFACE_CC_COLORING THEN
  MAP_EVERY EXISTS_TAC [`ecpH (G:(num)hypermap) x0`; `cc:num list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DART_ECPH_CASES; DART_ECPY_CASES] THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_NODE_ECPH) THEN
    ASM_SIMP_TAC[NODE_ECPY_PT_VALUE];
    MP_TAC(ISPECL [`ecpH (G:(num)hypermap) x0`; `ecpH_pt (G:(num)hypermap) x0`]
      CFACE_STEP) THEN ASM_SIMP_TAC[FACE_ECPH_PT];
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FACE_3CYCLE_STEPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CFACE_TAC[];
    REWRITE_TAC[ecpH] THEN MATCH_MP_TAC CFACE_ECPN_LIFT_GEN THEN
    ASM_SIMP_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                 FACE_MAP_PERMUTES; DART_ECPY_CASES; CFACE_ECPY_B_PT];
    ASM_SIMP_TAC[CFACE_ECPH_B_PT]]);;

let CC_ECPH_NEW_EDGES = prove
 (`!(G:(num)hypermap) x0 b1 b2 b3 b4 b5 mr R mK K (k:num->color).
     x0 IN dart G /\ proper_cpring G x0 /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\
     (!w. MEM w R ==> w IN dart G) /\ (!w. MEM w K ==> w IN dart G) /\
     cc_coloring (ecpH G x0)
       (APPEND (mask_list (CONS b1 (CONS b2 mr))
                  (CONS (SND(new_dart2(dart G))) (CONS (ecpH_pt G x0) R)))
               (mask_list (CONS b3 (CONS b4 (CONS b5 mK)))
                  (CONS (ecpY_pt G x0) (CONS (node_map G x0) (CONS x0 K))))) k
     ==> (k (ecpU_pt G) = k (SND(new_dart2(dart G))) <=> b1) /\
         (k (SND(new_dart2(dart(ecpY G x0)))) = k (ecpH_pt G x0) <=> b2) /\
         (k (SND(new_dart2(dart(ecpU G x0)))) = k (ecpY_pt G x0) <=> b3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(node_map G x0:num) IN dart G` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ~(z IN dart G)
        ==> (MEM z (insertE (ecpH (G:(num)hypermap) x0)
               (APPEND (mask_list (CONS b1 (CONS b2 mr))
                          (CONS (SND(new_dart2(dart G)))
                                (CONS (ecpH_pt G x0) R)))
                       (mask_list (CONS b3 (CONS b4 (CONS b5 mK)))
                          (CONS (ecpY_pt G x0)
                                (CONS (node_map G x0) (CONS x0 K)))))) <=>
             MEM z (insertE (ecpH G x0)
                     (mask_list [b1;b2;b3]
                        [SND(new_dart2(dart G)); ecpH_pt G x0;
                         ecpY_pt G x0])))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:num` THEN DISCH_TAC THEN MATCH_MP_TAC MEM_INSERTE_SPLIT THEN
    EXISTS_TAC `dart(G:(num)hypermap)` THEN
    REWRITE_TAC[MEM_APPEND; MEM_MASK_LIST_CONS; MASK_LIST_CLAUSES; MEM] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     DISJ2_TAC THENL
       [UNDISCH_TAC `!w. MEM w R ==> w IN dart (G:(num)hypermap)`;
        UNDISCH_TAC `!w. MEM w K ==> w IN dart (G:(num)hypermap)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MEM_MASK_LIST THENL
       [EXISTS_TAC `mr:bool list`; EXISTS_TAC `mK:bool list`] THEN
      ASM_REWRITE_TAC[];
      MESON_TAC[];
      X_GEN_TAC `w:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EDGE_ECPH_OLD] THEN
      ASM_MESON_TAC[EDGE_MAP_IN_DART]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cc_coloring]) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `SND(new_dart2(dart(G:(num)hypermap)))` th) THEN
    MP_TAC(SPEC `ecpH_pt (G:(num)hypermap) x0` th) THEN
    MP_TAC(SPEC `ecpY_pt (G:(num)hypermap) x0` th)) THEN
  ASM_SIMP_TAC[DART_ECPH_CASES; DART_ECPY_CASES; EDGE_ECPH_RINGB;
               EDGE_ECPH_APEX; EDGE_ECPH_ECPYPT] THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`; `b3:bool`] THEN
  ASM_REWRITE_TAC[MASK_LIST_CLAUSES; INSERTE_CLAUSES; MEM] THEN
  ASM_SIMP_TAC[EDGE_ECPH_RINGB; EDGE_ECPH_APEX; EDGE_ECPH_ECPYPT] THEN
  MESON_TAC[]);;

let CC_ECPH_APEX = prove
 (`!(G:(num)hypermap) x0 b1 b2 b3 b4 b5 mr R mK K (k:num->color).
     x0 IN dart G /\ proper_cpring G x0 /\
     (!w. MEM w R ==> w IN dart G) /\ (!w. MEM w K ==> w IN dart G) /\
     cc_coloring (ecpH G x0)
       (APPEND (mask_list (CONS b1 (CONS b2 mr))
                  (CONS (SND(new_dart2(dart G))) (CONS (ecpH_pt G x0) R)))
               (mask_list (CONS b3 (CONS b4 (CONS b5 mK)))
                  (CONS (ecpY_pt G x0) (CONS (node_map G x0) (CONS x0 K))))) k
     ==> k (SND(new_dart2(dart G))) = k (node_map G x0) /\
         (k (ecpH_pt G x0) = k (node_map G x0) <=> b1) /\
         (k (ecpH_pt G x0) = k (face_map G (edge_map G x0)) <=> b2) /\
         (k (ecpH_pt G x0) = k x0 <=> b3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL CC_ECPH_NEW_EDGES) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`;
    `APPEND (mask_list (CONS b1 (CONS b2 mr))
               (CONS (SND(new_dart2(dart (G:(num)hypermap))))
                     (CONS (ecpH_pt G x0) R)))
            (mask_list (CONS b3 (CONS b4 (CONS b5 mK)))
               (CONS (ecpY_pt G x0) (CONS (node_map G x0) (CONS x0 K))))`;
    `k:num->color`] CC_ECPH_FACE_FACTS) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  MESON_TAC[]);;

let EDGE_ECPH_BPRIME = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G
     ==> edge_map (ecpH G x0) (SND(new_dart2(dart(ecpU G x0)))) = ecpY_pt G
       x0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPECL [`ecpY (G:(num)hypermap) x0`; `ecpY_pt (G:(num)hypermap) x0`;
                 `SND(new_dart2(dart(ecpU (G:(num)hypermap) x0)))`]
    EDGE_ECPN_OLD_GEN) THEN
  ASM_SIMP_TAC[DART_ECPY_CASES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EDGE_ECPY_B_GEN]);;

let EDGE_ECPH_ECPUPT = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G
     ==> edge_map (ecpH G x0) (ecpU_pt G) = SND(new_dart2(dart G))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPECL [`ecpY (G:(num)hypermap) x0`; `ecpY_pt (G:(num)hypermap) x0`;
                 `ecpU_pt (G:(num)hypermap)`] EDGE_ECPN_OLD_GEN) THEN
  ASM_SIMP_TAC[DART_ECPY_CASES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EDGE_ECPY_ECPUPT]);;

let CFACE_ECPH_B_NODE = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ proper_cpring G x0 /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G
     ==> cface (ecpH G x0) (SND(new_dart2(dart G))) (node_map G x0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_NODE_ECPH) THEN
  ASM_SIMP_TAC[NODE_ECPY_PT_VALUE]);;

let CFACE_ECPH_APEX_YA = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ proper_cpring G x0 /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G
     ==> cface (ecpH G x0) (ecpH_pt G x0) (ecpY_pt G x0) /\
         cface (ecpH G x0) (ecpH_pt G x0) (ecpU_pt G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FACE_3CYCLE_STEPS) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN CFACE_TAC[]);;

let ADJ_ECPH_IMP = prove
 (`!(G:(num)hypermap) x0 u.
     x0 IN dart G /\ proper_cpring G x0 /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\ adj (ecpH G x0) (ecpH_pt G x0) u
     ==> cface (ecpH G x0) u (node_map G x0) \/ cface (ecpH G x0) u x0 \/
         cface (ecpH G x0) u (face_map G (edge_map G x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adj]) THEN
  REWRITE_TAC[rlink; GSYM cface] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `z:num`]
    ECPH_APEX_FACE_CASES) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_APEX) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_PT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_ECPYPT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_BPRIME) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_ECPUPT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_NODE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CFACE_TAC[]);;

let ADJ_ICPH_IMP = prove
 (`!(G:(num)hypermap) x0 x y.
     x0 IN dart G /\ proper_cpring G x0 /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\ x IN dart G /\ y IN dart G /\
     adj (ecpH G x0) x y
     ==> adj G x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adj]) THEN
  REWRITE_TAC[rlink; GSYM cface] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(z:num) IN dart G` THENL
   [REWRITE_TAC[adj; rlink; GSYM cface] THEN EXISTS_TAC `z:num` THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `z:num`] EDGE_ECPH_OLD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CFACE_TAC[ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_PROJ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_YA) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_B) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_BPRIME) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_RINGB) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_OLD) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] DART_SUBSET_ECPH) THEN
  ASM_REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:num) IN dart(ecpH G x0)` MP_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[DART_ECPH_CASES; DART_ECPY_CASES] THEN STRIP_TAC THEN
  CFACE_TAC[]);;

let EDGE_INVOL_ECPH = prove
 (`!(G:(num)hypermap) x0 u.
     x0 IN dart G /\ proper_cpring G x0 /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\
     cface (ecpH G x0) (ecpH_pt G x0) (edge_map (ecpH G x0) u)
     ==> edge_map (ecpH G x0) (edge_map (ecpH G x0) u) = u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `edge_map (ecpH G x0) u`]
    ECPH_APEX_FACE_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_APEX) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_B) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_ECPYPT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_BPRIME) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_ECPUPT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_RINGB) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[EDGEI]);;

let FBAND_ECPH = prove
 (`!(G:(num)hypermap) x0 u.
     x0 IN dart G /\ proper_cpring G x0 /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\ u IN dart(ecpH G x0)
     ==> (?x. x IN dart G /\ cface (ecpH G x0) u x) \/
         cface (ecpH G x0) (ecpH_pt G x0) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_YA) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_NODE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_BPRIME) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_PT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(u:num) IN dart (ecpH G x0)` THEN
  ASM_SIMP_TAC[DART_ECPH_CASES; DART_ECPY_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[CFACE_REFL_ALL];
    DISJ1_TAC THEN EXISTS_TAC `face_map G (edge_map G (x0:num))` THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART];
    DISJ1_TAC THEN EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[];
    DISJ1_TAC THEN EXISTS_TAC `node_map G (x0:num)` THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART];
    DISJ1_TAC THEN EXISTS_TAC `u:num` THEN ASM_REWRITE_TAC[CFACE_REFL_ALL]]);;

let COLORING_ECPH = prove
 (`!(G:(num)hypermap) x0 h c0.
     coloring G h /\ x0 IN dart G /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\ proper_cpring G x0 /\
     ~(h (node_map G x0) = c0) /\ ~(h x0 = c0) /\
     ~(h (face_map G (edge_map G x0)) = c0)
     ==> coloring (ecpH G x0) (ext_col (ecpH G x0) (dart G) h c0) /\
         (!x. x IN dart G ==> ext_col (ecpH G x0) (dart G) h c0 x = h x) /\
         ext_col (ecpH G x0) (dart G) h c0 (ecpH_pt G x0) = c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COLORING_EXT THEN
  EXISTS_TAC `[node_map G x0; x0:num; face_map G (edge_map G x0)]` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[DART_SUBSET_ECPH; SUBSET];
    ASM_MESON_TAC[CFACE_ECPH_PROJ];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ADJ_COLORING THEN
    EXISTS_TAC `G:(num)hypermap` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ADJ_ICPH_IMP THEN EXISTS_TAC `x0:num` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`] FBAND_ECPH) THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[CFACE_ECPH_APEX_OLD];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`] ADJ_ECPH_IMP) THEN
    ASM_REWRITE_TAC[MEM] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EDGE_INVOL_ECPH THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART; FACE_MAP_IN_DART; EDGE_MAP_IN_DART]]);;

let MEM_TL_TL_CPRING_IN_DART = prove
 (`!(G:(num)hypermap) x0 w.
     x0 IN dart G /\ proper_cpring G x0 /\ MEM w (TL(TL(cpring G x0)))
     ==> w IN dart G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] MEM_CPRING_IN_DART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[MEM]);;

let COLORING_ECPH_RING = prove
 (`!(G:(num)hypermap) x0 h c0.
     coloring G h /\ x0 IN dart G /\
     ~(h (node_map G x0) = c0) /\ ~(h x0 = c0) /\
     ~(h (face_map G (edge_map G x0)) = c0)
     ==> ?k. coloring (ecpH G x0) k /\
             MAP k (cpring (ecpH G x0) (ecpH_pt G x0)) =
             CONS (h (node_map G x0))
                  (CONS c0 (MAP h (TL(TL(cpring G x0)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `proper_cpring G (x0:num)` ASSUME_TAC THENL
   [ASM_MESON_TAC[proper_cpring; COLORING_NODE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `h:num->color`; `c0:color`]
    COLORING_ECPH) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  ABBREV_TAC `k = ext_col (ecpH G x0) (dart G) (h:num->color) c0` THEN
  STRIP_TAC THEN EXISTS_TAC `k:num->color` THEN
  ASM_SIMP_TAC[CPRING_ECPH; NODE_ECPY_PT_VALUE; MAP; CONS_11] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`ecpH (G:(num)hypermap) x0`; `k:num->color`;
                   `SND(new_dart2(dart (G:(num)hypermap)))`;
                   `node_map (G:(num)hypermap) x0`] CFACE_COLORING) THEN
    ASM_SIMP_TAC[DART_ECPH_CASES; DART_ECPY_CASES; CFACE_ECPH_B_NODE;
                 FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                 FACE_MAP_PERMUTES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[NODE_MAP_IN_DART];
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[MEM_TL_TL_CPRING_IN_DART]]);;

let ADJ_ICPK_IMP = prove
 (`!(G:(num)hypermap) x0 x y.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     long_cpring G x0 /\ x IN dart G /\ y IN dart G /\ adj (ecpK G x0) x y
     ==> adj G x y \/
         cface G x (node_map G x0) /\ cface G y (face_map G (edge_map G x0)) \/
         cface G x (face_map G (edge_map G x0)) /\ cface G y (node_map G x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adj]) THEN
  REWRITE_TAC[rlink; GSYM cface] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(z:num) IN dart G` THENL
   [DISJ1_TAC THEN REWRITE_TAC[adj; rlink; GSYM cface] THEN
    EXISTS_TAC `z:num` THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `z:num`] EDGE_ECPK_OLD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CFACE_TAC[ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPK_PROJ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPK_A_NODE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPK_B_FE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPK_AB) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:num) IN dart(ecpK G x0)` MP_TAC THENL
   [MATCH_MP_TAC CFT_DART THEN EXISTS_TAC `x:num` THEN
    ASM_SIMP_TAC[DART_ECPK_CASES];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DART_ECPK_CASES] THEN STRIP_TAC THEN DISJ2_TAC THEN
  (SUBGOAL_THEN `cface (ecpK G x0) x (node_map G x0) /\
                 cface (ecpK G x0) y (face_map G (edge_map G x0)) \/
                 cface (ecpK G x0) x (face_map G (edge_map G x0)) /\
                 cface (ecpK G x0) y (node_map G x0)`
   MP_TAC THENL [CFACE_TAC[]; ALL_TAC]) THEN STRIP_TAC THEN
  CFACE_TAC[ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPK_PROJ]);;

let COLORING_ECPK = prove
 (`!(G:(num)hypermap) x0 h c0.
     coloring G h /\ x0 IN dart G /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\ long_cpring G x0 /\
     ~(h (node_map G x0) = h (face_map G (edge_map G x0)))
     ==> coloring (ecpK G x0) (ext_col (ecpK G x0) (dart G) h c0) /\
         (!x. x IN dart G ==> ext_col (ecpK G x0) (dart G) h c0 x = h x) /\
         ext_col (ecpK G x0) (dart G) h c0 (ecpN_pt G) = h (node_map G x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y. x IN dart G /\ y IN dart G /\ cface (ecpK G x0) x y
          ==> (h:num->color) x = h y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CFACE_COLORING THEN EXISTS_TAC `G:(num)hypermap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CFACE_ECPK_PROJ THEN
    EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ c ==> a /\ b /\ c`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC COLORING_EXT0 THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CFACE_ECPK_PROJ];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`; `y:num`]
        ADJ_ICPK_IMP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [MATCH_MP_TAC ADJ_COLORING THEN EXISTS_TAC `G:(num)hypermap` THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[CFACE_COLORING];
        ASM_MESON_TAC[CFACE_COLORING]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FBAND_ECPK THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EXT_COL_CFACE THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ASM_SIMP_TAC[NODE_MAP_IN_DART];
      ASM_SIMP_TAC[CFACE_ECPK_A_NODE]]]);;

let COLORING_ECPK_RING = prove
 (`!(G:(num)hypermap) x0 h.
     coloring G h /\ x0 IN dart G /\ long_cpring G x0 /\
     ~(h (node_map G x0) = h (face_map G (edge_map G x0)))
     ==> ?k. coloring (ecpK G x0) k /\
             MAP k (cpring (ecpK G x0) (ecpK_pt G x0)) =
             CONS (h (node_map G x0)) (MAP h (TL(TL(cpring G x0))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `h:num->color`;
                 `h (node_map G (x0:num)):color`] COLORING_ECPK) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  ABBREV_TAC `k = ext_col (ecpK G x0) (dart G) (h:num->color)
                    (h (node_map G x0))` THEN
  STRIP_TAC THEN EXISTS_TAC `k:num->color` THEN
  ASM_SIMP_TAC[CPRING_ECPK; MAP; CONS_11; FINITE_DART; EDGE_MAP_PERMUTES;
               NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[MEM_TL_TL_CPRING_IN_DART; LONG_IMP_PROPER]);;

let COLOR_EDGE_NODE = prove
 (`!(G:(num)hypermap) (h:num->color) z.
     coloring G h /\ z IN dart G
     ==> h (edge_map G (node_map G z)) = h z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [coloring]) THEN
  DISCH_THEN(MP_TAC o SPEC `edge_map G (node_map G (z:num))`) THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; nodeK]);;

let COLORING_ECPA = prove
 (`!(G:(num)hypermap) x0 h.
     coloring G h /\ x0 IN dart G /\ FINITE(dart G) /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\
     h (face_map G (edge_map G x0)) = h (node_map G x0)
     ==> coloring (ecpA G x0) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [coloring]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "he") (LABEL_TAC "hf")) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `h:num->color`; `x0:num`]
    COLOR_EDGE_NODE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `h:num->color`; `node_map G (x0:num)`]
    COLOR_EDGE_NODE) THEN
  USE_THEN "he" (MP_TAC o SPEC `node_map G (x0:num)`) THEN
  USE_THEN "he" (MP_TAC o SPEC `node_map G (node_map G (x0:num))`) THEN
  USE_THEN "hf" (MP_TAC o SPEC `edge_map G (x0:num)`) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; EDGE_MAP_IN_DART] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPA_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[coloring; th]) THEN
  REWRITE_TAC[ecpA_edge; ecpA_face] THEN CONJ_TAC THEN X_GEN_TAC `x:num` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "he" (MP_TAC o SPEC `x:num`) THEN
  USE_THEN "hf" (MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[]);;

let MASK_LIST_NOT_ALL_NONEMPTY = prove
 (`!m (l:A list).
     LENGTH m = LENGTH l /\ ~(ALL (\b. b) m)
     ==> ~(mask_list (MAP (\b. ~b) m) l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; MASK_LIST_CLAUSES] THEN
  BOOL_CASES_TAC `h:bool` THEN
  REWRITE_TAC[MASK_LIST_CLAUSES; NOT_CONS_NIL] THEN ASM_MESON_TAC[]);;

let HD_APPEND_MAP = prove
 (`!(h:A->B) l z. HD (APPEND (MAP h l) [h z]) = h (HD (APPEND l [z]))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; APPEND; HD]);;

let NOT_LONG_TL_TL = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ proper_cpring G x0 /\ ~long_cpring G x0
     ==> TL(TL(cpring G x0)) = []`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] SIZE_LONG_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `t2 = TL(TL(cpring G (x0:num)))` THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LENGTH; GSYM LENGTH_EQ_NIL] THEN
  ARITH_TAC);;

let FE_RING = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ proper_cpring G x0
     ==> face_map G (edge_map G x0) =
         HD (APPEND (TL(TL(cpring G x0))) [node_map G x0])`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `long_cpring G (x0:num)` THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_LONG_CPRING) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `t3 = TL(TL(TL(cpring G (x0:num))))` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[TL; APPEND; HD];
    ASM_SIMP_TAC[NOT_LONG_TL_TL; APPEND; HD] THEN
    UNDISCH_TAC `~long_cpring G (x0:num)` THEN REWRITE_TAC[long_cpring]]);;

(* ------------------------------------------------------------------------- *)
(* The Y and H steps of cfctr_correct.  The contract colouring k of the new  *)
(* map restricts to a contract colouring of G (CC_ECPY_RESTRICT,             *)
(* CC_ECPH_RESTRICT), which the induction hypothesis turns into a colouring  *)
(* h of the contracted map Gc whose ring colours are those of k on the       *)
(* uncontracted ring darts.  The colour of the new apex face compared with   *)
(* the faces at node_map G x0, x0 and face_map G (edge_map G x0) records the *)
(* contracted new edges (CC_ECPY_APEX, CC_ECPH_APEX), and RING_CHAIN reads   *)
(* the first ring colours of Gc off the ring of G.  CTR_CASES_TAC splits on  *)
(* the mask bits of the step, leaving one goal per pattern accepted by       *)
(* cfctr_ok (4 for Y, 10 for H), and CTR_EXTEND_TAC closes each one by the   *)
(* colouring extension for the step that cfctr_map adds (none, U, Y, H, K or *)
(* A: COLORING_ECPU_RING etc.).                                              *)
(* ------------------------------------------------------------------------- *)

let CTR_CASES_TAC bits =
  REMOVE_THEN "IH" (fun ih ->
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      exists (fun v -> free_in v (concl th)) bits))) THEN
    MP_TAC(SYM ih)) THEN
  ASM_REWRITE_TAC[MAP] THEN MAP_EVERY BOOL_CASES_TAC bits THEN
  REWRITE_TAC[nsp; MASK_LIST_CLAUSES; MAP; CONS_11; CPMAP_CONS_U;
              CPMAP_CONS_Y; CPMAP_CONS_H; CPMAP_CONS_K; CPMAP_CONS_A] THEN
  DISCH_THEN(fun ih -> REWRITE_TAC[ih; NOT_CONS_NIL; HD; APPEND] THEN
                       ASSUME_TAC ih) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];;

let CTR_EXTEND_TAC c0 =
  let gyh = [`Gc:(num)hypermap`; `yc:num`; `h:num->color`] in
  let EXT_TAC th args =
    MP_TAC(ISPECL args th) THEN ASM_REWRITE_TAC[MAP; TL] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN ACCEPT_TAC] in
  let LONG_TAC =
    SUBGOAL_THEN `long_cpring Gc (yc:num)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MAP]; ALL_TAC] in
  fun (asl,w) ->
    let m = rand(rator(lhand(snd(dest_exists w)))) in
    let tac =
      match (try fst(dest_const(fst(strip_comb m))) with Failure _ -> "") with
        "ecpU" -> EXT_TAC COLORING_ECPU_RING (gyh @ [c0])
      | "ecpY" -> EXT_TAC COLORING_ECPY_RING (gyh @ [c0])
      | "ecpH" -> EXT_TAC COLORING_ECPH_RING (gyh @ [c0])
      | "ecpK" -> LONG_TAC THEN EXT_TAC COLORING_ECPK_RING gyh
      | "ecpA" -> LONG_TAC THEN EXISTS_TAC `h:num->color` THEN
                  ASM_SIMP_TAC[CPRING_ECPA_LONG] THEN
                  MATCH_MP_TAC COLORING_ECPA THEN
                  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES;
                                  NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
                  ASM_MESON_TAC[]
      | _ -> EXISTS_TAC `h:num->color` THEN ASM_REWRITE_TAC[MAP] in
    tac (asl,w);;

let CTR_CORRECT_Y = prove
 (`!s cp. ctr_correct (CONS s cp) ==> ctr_correct (CONS CpY (CONS s cp))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ctr_correct; cprsize; ctrmsize; ctrenum; NOT_CONS_NIL;
              CPMAP_CONS_Y] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`mr:bool list`; `mc:bool list`; `k:num->color`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `config_prog (CONS (s:cpstep) cp)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CFCTR_CONFIG_PROG) THEN
    REWRITE_TAC[CONFIG_PROG_CONS_CASES; NOT_CONS_NIL; distinctness "cpstep"];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CFCTR_OK_Y_CASES]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:bool`; `b2:bool`; `b3:bool`; `mr':bool list`;
                       `mc':bool list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[CFCTR_MAP_Y] THEN
  MP_TAC(ISPEC `CONS (s:cpstep) cp` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `G = FST(cpmap (CONS (s:cpstep) cp))` THEN
  ABBREV_TAC `x0 = SND(cpmap (CONS (s:cpstep) cp))` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_CONS_HEAD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `t = TL(cpring G (x0:num))` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; SUC_INJ]) THEN
  UNDISCH_TAC `SUC(SUC(LENGTH(mr':bool list))) =
               LENGTH (cpring (ecpY G x0) (ecpY_pt G x0))` THEN
  UNDISCH_TAC `cc_coloring (ecpY G x0)
     (APPEND (mask_list (CONS b1 (CONS b2 mr'))
               (cpring (ecpY G x0) (ecpY_pt G x0)))
             (mask_list (CONS b3 mc')
               (CONS (node_map G x0) (ctrenum (CONS (s:cpstep) cp))))) k` THEN
  ASM_SIMP_TAC[CPRING_ECPY; LENGTH; SUC_INJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(!w. MEM w t ==> w IN dart (G:(num)hypermap)) /\
    (!w. MEM w (CONS (node_map G x0) (ctrenum (CONS (s:cpstep) cp)))
         ==> w IN dart G)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN
    MATCH_MP_TAC MEM_CPRING_IN_DART THEN EXISTS_TAC `x0:num` THEN
    ASM_REWRITE_TAC[MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t = []) /\ HD t = (x0:num)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
    ASM_REWRITE_TAC[CONS_11] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[NOT_CONS_NIL; HD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `b1:bool`; `b2:bool`;
                 `mr':bool list`; `t:num list`; `CONS b3 mc':bool list`;
                 `CONS (node_map G x0) (ctrenum (CONS (s:cpstep) cp))`;
                 `k:num->color`] CC_ECPY_APEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cc_coloring G
                  (APPEND (mask_list (CONS b3 mr') (CONS (node_map G x0) t))
                          (mask_list mc' (ctrenum (CONS (s:cpstep) cp)))) k`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `b1:bool`; `b2:bool`;
                   `mr':bool list`; `t:num list`; `CONS b3 mc':bool list`;
                   `CONS (node_map G x0) (ctrenum (CONS (s:cpstep) cp))`;
                   `k:num->color`] CC_ECPY_RESTRICT) THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                    FACE_MAP_PERMUTES] THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
    MATCH_MP_TAC CC_COLORING_MEM_CONG THEN
    REWRITE_TAC[MEM_APPEND; MEM_MASK_LIST_CONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`;
                 `[node_map (G:(num)hypermap) x0]`; `t:num list`;
                 `[b3:bool]`; `mr':bool list`;
                 `mask_list mc' (ctrenum (CONS (s:cpstep) cp))`;
                 `k:num->color`] RING_CHAIN) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `[]:num list`;
                 `cpring G (x0:num)`; `[]:bool list`; `CONS b3 mr':bool list`;
                 `mask_list mc' (ctrenum (CONS (s:cpstep) cp))`;
                 `k:num->color`] RING_CHAIN) THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; HD; HD_APPEND; NOT_CONS_NIL] THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS b3 mr':bool list`; `mc':bool list`;
                                `k:num->color`]) THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  ABBREV_TAC `cpc = cfctr_map (CONS b3 mr') mc' (CONS (s:cpstep) cp)` THEN
  ABBREV_TAC `Gc = FST(cpmap (cpc:(cpstep)list))` THEN
  ABBREV_TAC `yc = SND(cpmap (cpc:(cpstep)list))` THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->color`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH"))) THEN
  SUBGOAL_THEN `proper_cpring Gc (yc:num) /\ yc IN dart Gc`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Gc"; "yc"] THEN
    REWRITE_TAC[CPMAP_PT_IN_DART; proper_cpring] THEN
    ASM_MESON_TAC[COLORING_NODE; CPMAP_PT_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:(num)hypermap`; `yc:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tc = TL(TL(cpring Gc (yc:num)))` THEN DISCH_TAC THEN
  CTR_CASES_TAC [`b1:bool`; `b2:bool`; `b3:bool`] THEN
  CTR_EXTEND_TAC `(k:num->color) (ecpY_pt (G:(num)hypermap) x0)`);;

let CTR_CORRECT_H = prove
 (`!cp. ctr_correct cp ==> ctr_correct (CONS CpH cp)`,
  GEN_TAC THEN
  REWRITE_TAC[ctr_correct; cprsize; ctrmsize; ctrenum; CPMAP_CONS_H] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`mr:bool list`; `mc:bool list`; `k:num->color`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `config_prog (cp:(cpstep)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CFCTR_CONFIG_PROG) THEN
    REWRITE_TAC[CONFIG_PROG_CONS_CASES; distinctness "cpstep"];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CFCTR_OK_H_CASES]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:bool`; `b2:bool`; `b3:bool`; `b4:bool`; `b5:bool`;
                       `mr':bool list`; `mc':bool list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `G = FST(cpmap (cp:(cpstep)list))` THEN
  ABBREV_TAC `x0 = SND(cpmap (cp:(cpstep)list))` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `t = TL(TL(cpring G (x0:num)))` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `cpring (ecpH G x0) (ecpH_pt G x0) =
    CONS (SND(new_dart2(dart G))) (CONS (ecpH_pt G x0) t) /\
    face_map (ecpH G x0) (ecpH_pt G x0) = ecpY_pt G (x0:num)`
  (fun th -> REWRITE_TAC[th] THEN
             RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH; SUC_INJ;
               ARITH_RULE `SUC(SUC(SUC n)) = m + 3 <=> n = m`])) THENL
   [ASM_SIMP_TAC[CPRING_ECPH; NODE_ECPY_PT_VALUE; FACE_ECPH_PT]; ALL_TAC] THEN
  SUBGOAL_THEN `(!w. MEM w t ==> w IN dart (G:(num)hypermap)) /\
                node_map G x0 IN dart G`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN X_GEN_TAC `w:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC MEM_CPRING_IN_DART THEN EXISTS_TAC `x0:num` THEN
    ASM_REWRITE_TAC[MEM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `b1:bool`; `b2:bool`;
                 `b3:bool`; `b4:bool`; `b5:bool`; `mr':bool list`;
                 `t:num list`; `mc':bool list`; `ctrenum cp`;
                 `k:num->color`] CC_ECPH_APEX) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `b1:bool`; `b2:bool`;
                 `b3:bool`; `b4:bool`; `b5:bool`; `mr':bool list`;
                 `t:num list`; `mc':bool list`; `ctrenum cp`;
                 `k:num->color`] CC_ECPH_RESTRICT) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (p,q,mp,mq) ->
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; p; q; mp; mq;
                   `mask_list mc' (ctrenum cp)`; `k:num->color`] RING_CHAIN))
   [`[]:num list`, `cpring G (x0:num)`, `[]:bool list`,
    `CONS b4 (CONS b5 mr'):bool list`;
    `[node_map (G:(num)hypermap) x0]`, `CONS (x0:num) t`, `[b4:bool]`,
    `CONS b5 mr':bool list`;
    `[node_map (G:(num)hypermap) x0; x0]`, `t:num list`, `[b4:bool; b5]`,
    `mr':bool list`] THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; HD; NOT_CONS_NIL] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] FE_RING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
  REWRITE_TAC[CFCTR_MAP_H] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS b4 (CONS b5 mr'):bool list`;
                                `mc':bool list`; `k:num->color`]) THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  ABBREV_TAC `cpc = cfctr_map (CONS b4 (CONS b5 mr')) mc' cp` THEN
  ABBREV_TAC `Gc = FST(cpmap (cpc:(cpstep)list))` THEN
  ABBREV_TAC `yc = SND(cpmap (cpc:(cpstep)list))` THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->color`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH"))) THEN
  SUBGOAL_THEN `proper_cpring Gc (yc:num) /\ yc IN dart Gc`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Gc"; "yc"] THEN
    REWRITE_TAC[CPMAP_PT_IN_DART; proper_cpring] THEN
    ASM_MESON_TAC[COLORING_NODE; CPMAP_PT_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:(num)hypermap`; `yc:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tc = TL(TL(cpring Gc (yc:num)))` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `HD (APPEND (MAP h tc) [h (node_map Gc yc)]) =
    (h:num->color) (face_map Gc (edge_map Gc yc)) /\
    (~long_cpring Gc yc
     ==> tc = [] /\ h (face_map Gc (edge_map Gc yc)) = h (node_map Gc yc)) /\
    (~ALL (\b. b) mr'
     ==> ~(MAP (k:num->color) (mask_list (MAP (\b. ~b) mr') t) = []))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Gc:(num)hypermap`; `yc:num`] FE_RING) THEN
    MP_TAC(ISPECL [`Gc:(num)hypermap`; `yc:num`] NOT_LONG_TL_TL) THEN
    ASM_REWRITE_TAC[HD_APPEND_MAP; MAP_EQ_NIL] THEN REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[APPEND; HD];
      MP_TAC(ISPECL [`mr':bool list`; `t:num list`]
        MASK_LIST_NOT_ALL_NONEMPTY) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CTR_CASES_TAC [`b1:bool`; `b2:bool`; `b3:bool`; `b4:bool`; `b5:bool`] THEN
  CTR_EXTEND_TAC `(k:num->color) (ecpH_pt (G:(num)hypermap) x0)`);;

let CTR_CORRECT_NIL = prove
 (`ctr_correct []`,
  REWRITE_TAC[ctr_correct; CFCTR_OK_CLAUSES]);;

let CTR_CORRECT_VACUOUS = prove
 (`!s cp. (s = CpRr \/ s = CpU \/ s = CpK \/ s = CpA)
          ==> ctr_correct (CONS s cp)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ctr_correct; CFCTR_OK_CLAUSES]);;

let CFCTR_CORRECT = prove
 (`!cp. ctr_correct cp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CTR_CORRECT_NIL] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(SPEC `h:cpstep` (cases "cpstep")) THEN
  STRUCT_CASES_TAC(ISPEC `t:(cpstep)list` list_CASES) THEN
  MESON_TAC[CTR_CORRECT_R; CTR_CORRECT_VACUOUS; CTR_CORRECT_H;
            CTR_CORRECT_Y0; CTR_CORRECT_Y]);;

(* ------------------------------------------------------------------------- *)
(* Face masks: cpmask, cfmask1, cpadj and cpmask_adj                         *)
(* ------------------------------------------------------------------------- *)

let proper_cpmask = new_definition
  `proper_cpmask (cp:(cpstep)list) (cm:(bool)list#(bool)list) <=>
     LENGTH(FST cm) = cprsize cp /\ LENGTH(SND cm) = cpksize cp`;;

let cpmask = new_definition
  `cpmask (cm:(bool)list#(bool)list) (cp:(cpstep)list) =
     APPEND (mask_list (FST cm) (cpring (FST(cpmap cp)) (SND(cpmap cp))))
            (mask_list (SND cm) (cpker cp))`;;

let mask_pred1_from = define
  `mask_pred1_from (j:num) (i:num) 0 = [] /\
   mask_pred1_from j i (SUC n) = CONS (j = i) (mask_pred1_from (SUC j) i n)`;;

let mask_pred1 = new_definition
  `mask_pred1 (i:num) (n:num) = mask_pred1_from 0 i n`;;

let cfmask1 = new_definition
  `cfmask1 (cp:(cpstep)list) (i:num) =
     (REPLICATE (cprsize cp) F, mask_pred1 i (cpksize cp))`;;

let cpadj = define
  `(cpadj (cm:(bool)list#(bool)list) [] =
      (CONS (HD(TL(FST cm))) (CONS (HD(FST cm)) []), SND cm)) /\
   (cpadj cm (CONS (CpR n) cp') =
      (rot_list n (FST(cpadj (rotr_list n (FST cm), SND cm) cp')),
       SND(cpadj (rotr_list n (FST cm), SND cm) cp'))) /\
   (cpadj cm (CONS CpY cp') =
      (let mr = FST cm in
       let b0 = HD mr in let b1 = HD(TL mr) in let b2 = HD(TL(TL mr)) in
       let res = cpadj (CONS b0 (CONS b2 (TL(TL(TL mr)))), SND cm) cp' in
       let a0 = HD(FST res) in let a2 = HD(TL(FST res)) in let mr' = TL(TL(FST
         res)) in
       (CONS (a0 \/ b1) (CONS (b0 \/ b2) (CONS (a2 \/ b1) mr')), SND res))) /\
   (cpadj cm (CONS CpH cp') =
      (let mr = FST cm in let mk = SND cm in
       let b0 = HD mr in let b1 = HD(TL mr) in let b1' = HD mk in
       let res = cpadj (CONS b0 (CONS b1' (TL(TL mr))), TL mk) cp' in
       let a0 = HD(FST res) in let a1 = HD(TL(FST res)) in let mr' = TL(TL(FST
         res)) in
       (CONS (a0 \/ b1)
             (CONS (b0 \/ b1' \/ HD(APPEND (TL(TL mr)) [b0]))
                   (if mr' = [] then [] else CONS (HD mr' \/ b1) (TL mr'))),
        CONS (a1 \/ b1) (SND res))))`;;

(* ------------------------------------------------------------------------- *)
(* ctrband: the faces incident to the contract edges                         *)
(* ------------------------------------------------------------------------- *)

let ctrband = define
 `(ctrband (cm:(bool)list) [] = ([]:(bool)list,[]:(bool)list)) /\
  (ctrband cm (CONS (CpR n) cp') =
     (rot_list n (FST(ctrband cm cp')), SND(ctrband cm cp'))) /\
  (ctrband cm (CONS CpRr cp') = ([],[])) /\
  (ctrband cm (CONS CpY cp') =
     (if cp' = [] then (REPLICATE 3 F, [])
      else
        (let b1 = HD cm in let cm' = TL cm in
         let res = ctrband cm' cp' in let mr = FST res in let mk = SND res in
         if 2 <= LENGTH mr then
           (CONS (b1 \/ HD mr) (CONS F (CONS (b1 \/ HD(TL mr)) (TL(TL mr)))),
            mk)
         else ([],[])))) /\
  (ctrband cm (CONS CpH cp') =
     (let b1 = HD cm in let b0 = HD(TL cm) in let b2 = HD(TL(TL cm)) in
      let cm' = TL(TL(TL cm)) in
      let res = ctrband cm' cp' in let mr = FST res in let mk = SND res in
      if 3 <= LENGTH mr then
        (CONS (b0 \/ HD mr)
              (CONS b1 (CONS (b2 \/ HD(TL(TL mr))) (TL(TL(TL mr))))),
         CONS (b0 \/ b1 \/ b2 \/ HD(TL mr)) mk)
      else ([],[]))) /\
  (ctrband cm (CONS CpU cp') = ([],[])) /\
  (ctrband cm (CONS CpK cp') = ([],[])) /\
  (ctrband cm (CONS CpA cp') = ([],[]))`;;

(* ------------------------------------------------------------------------- *)
(* cptriad and valid_ctrm                                                    *)
(* ------------------------------------------------------------------------- *)

let cptriad = define
 `(cptriad (ccm:(bool)list#(bool)list) (cp:(cpstep)list) 0 = F) /\
  (cptriad (ccm:(bool)list#(bool)list) (cp:(cpstep)list) (SUC i') =
     let adjm = cpadj (cfmask1 cp i') cp in
     let mrt = FST adjm in let mkt = SND adjm in
     let mrc = FST ccm in let mkc = SND ccm in
     let mct = APPEND (mask_list mrc mrt) (mask_list mkc mkt) in
     if EX (\b. ~b) mct /\ 2 < LENGTH(FILTER (\b. b) mct) then T
     else cptriad ccm cp i')`;;

let valid_ctrm = new_definition
 `valid_ctrm (cm:(bool)list) (cp:(cpstep)list) =
    (let n = LENGTH(FILTER (\b. b) cm) in
     if n = 4 then cptriad (ctrband cm cp) cp (cpksize cp)
     else 0 < n /\ n <= 3)`;;

(* ------------------------------------------------------------------------- *)
(* contract_ctree and contract_ctreeP                                        *)
(* ------------------------------------------------------------------------- *)

let CTRACE_BEHEAD_ZEROSUM = prove
 (`!et:(color)list. ~(et = []) /\ sumt et = Color0 ==> ctrace(TL et) = et`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; sumt; TL; ctrace; CONS_11; ADDC_EQ_0] THEN
  MESON_TAC[]);;

let contract_ctree = new_definition
 `contract_ctree (cf:(cpstep)list#(num)list) =
    (let cp = cfprog cf in
     let cm = cfcontract_mask cf in
     match cfctr (REPLICATE (cprsize cp) F) cm cp with
       NONE -> NONE
     | SOME cpc -> if valid_ctrm cm cp then SOME(cpcolor cpc) else NONE)`;;

(* ------------------------------------------------------------------------- *)
(* Sparseness of the contract (Gonthier sparse_cfctr).  Invariant:           *)
(* sparse_inv G x0 S <=> the pointer x0 and the darts of S lie in pairwise   *)
(* distinct nodes (PAIRWISE over cnode) and S is inside dart G.  The ring    *)
(* mask contributes the edge partners of the contracted ring darts, the      *)
(* contract mask contributes insertE of the contracted darts.                *)
(* ------------------------------------------------------------------------- *)

let ORBIT_AGREE = prove
 (`!(f:A->A) g x.
     (!u. u IN orbit_map f x ==> g u = f u) ==> orbit_map g x = orbit_map f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. ITER n (g:A->A) x = ITER n f x` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[ORBIT_MAP_ITER] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; ORBIT_MAP_ITER] THEN ASM_REWRITE_TAC[]);;

let CNODE_3CYCLE = prove
 (`!(M:(A)hypermap) u v w z.
     node_map M u = v /\ node_map M v = w /\ node_map M w = u
     ==> (cnode M u z <=> z = u \/ z = v \/ z = w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[cnode; node; ORBIT_MAP_ITER] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `0`; EXISTS_TAC `1`; EXISTS_TAC `2`] THEN
    REWRITE_TAC[num_CONV `2`; num_CONV `1`; ITER] THEN ASM_REWRITE_TAC[]]);;

let CNODE_PRESERVED = prove
 (`!(G:(A)hypermap) (M:(A)hypermap) x0 z.
     FINITE(dart G) /\ node_map G permutes dart G /\ x0 IN dart G /\
     z IN dart G /\ ~cnode G x0 z /\
     (!u. u IN dart G /\ ~(u IN orbit_map (node_map G) x0)
          ==> node_map M u = node_map G u)
     ==> !w. cnode M z w <=> cnode G z w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cnode; node] THEN
  SUBGOAL_THEN `orbit_map (node_map M) (z:A) = orbit_map (node_map G) z`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ORBIT_AGREE THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ORBIT_MAP_IN];
    DISCH_TAC THEN UNDISCH_TAC `~cnode G (x0:A) z` THEN
    REWRITE_TAC[cnode; node] THEN
    ASM_MESON_TAC[ORBIT_MAP_EQ; IN_ORBIT_MAP_REFL]]);;

let INSERTE_OLD_EQ = prove
 (`!(M:(A)hypermap) (G:(A)hypermap) l.
     (!x. MEM x l ==> edge_map M x = edge_map G x) ==> insertE M l = insertE G
       l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[INSERTE_CLAUSES; MEM] THEN DISCH_TAC THEN
  REWRITE_TAC[CONS_11] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let PAIRWISE_EL_IMP = prove
 (`!(R:A->A->bool) l i j.
     PAIRWISE R l /\ i < j /\ j < LENGTH l ==> R (EL i l) (EL j l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; PAIRWISE] THEN REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `i':num` SUBST1_TAC)
    (ISPEC `i:num` num_CASES) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `j':num` SUBST1_TAC)
    (ISPEC `j:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC; LT; GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[MEM_EL]);;

let SPARSE_OF_PAIRWISE = prove
 (`!(H:(A)hypermap) p. PAIRWISE (\x y. ~cnode H x y) p ==> sparse H p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sparse] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x y. ~cnode (H:(A)hypermap) x y`; `p:A list`; `i:num`;
                 `j:num`] PAIRWISE_EL_IMP) THEN
  ASM_REWRITE_TAC[]);;

let sparse_inv = new_definition
 `sparse_inv (G:(num)hypermap) x0 S <=>
    PAIRWISE (\x y. ~cnode G x y) (CONS x0 S) /\ (!z. MEM z S ==> z IN dart
      G)`;;

let ctr_sparse = new_definition
 `ctr_sparse cp <=>
    !mr mc. LENGTH mr = cprsize cp /\ LENGTH mc = ctrmsize cp /\
            cfctr_ok mr mc cp
            ==> sparse_inv (FST(cpmap cp)) (SND(cpmap cp))
                  (APPEND (MAP (edge_map (FST(cpmap cp)))
                             (mask_list mr (cpring (FST(cpmap cp)) (SND(cpmap
                               cp)))))
                          (insertE (FST(cpmap cp)) (mask_list mc (ctrenum
                            cp))))`;;

let CTR_SPARSE_NIL = prove
 (`ctr_sparse []`,
  REWRITE_TAC[ctr_sparse; CFCTR_OK_CLAUSES]);;

let CTR_SPARSE_VACUOUS = prove
 (`!s cp. (s = CpRr \/ s = CpU \/ s = CpK \/ s = CpA) ==> ctr_sparse (CONS s
   cp)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ctr_sparse; CFCTR_OK_CLAUSES]);;

let CNODE_ORBIT_EQ = prove
 (`!(G:(A)hypermap) x0 x1.
     FINITE(dart G) /\ node_map G permutes dart G /\ x0 IN dart G /\
     cnode G x0 x1
     ==> !z. cnode G x1 z <=> cnode G x0 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cnode; node] THEN
  MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`; `x0:A`;
                 `x1:A`] ORBIT_MAP_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `cnode G (x0:A) x1` THEN REWRITE_TAC[cnode; node] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[]);;

let PAIRWISE_SYM_ROT_LIST = prove
 (`!(R:num->num->bool) n l.
     (!x y. MEM x l /\ MEM y l ==> (R x y <=> R y x))
     ==> (PAIRWISE R (rot_list n l) <=> PAIRWISE R l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:num->num->bool`; `drop_list n (l:num list)`;
                 `take_list n (l:num list)`] PAIRWISE_APPEND_SYM_MEM) THEN
  REWRITE_TAC[GSYM rot_list; MEM_ROT_LIST] THEN
  FIRST_ASSUM(fun th -> DISCH_THEN(fun imp -> MP_TAC(MP imp th))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; TAKE_DROP_LIST]));;

let EDGE_CPMAP0_1 = prove
 (`edge_map cpmap0 1 = 0`,
  REWRITE_TAC[CPMAP0_COMPONENTS; swap] THEN ARITH_TAC);;

let CTR_SPARSE_R = prove
 (`!n cp. ctr_sparse cp ==> ctr_sparse (CONS (CpR n) cp)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ctr_sparse] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`mr:bool list`; `mc:bool list`] THEN
  REWRITE_TAC[cprsize; ctrmsize; ctrenum; CPMAP_CONS_R; FST;
    SND;
              CFCTR_OK_CLAUSES; ecpR] THEN
  ABBREV_TAC `G = FST(cpmap (cp:(cpstep)list))` THEN
  ABBREV_TAC `x0 = SND(cpmap (cp:(cpstep)list))` THEN
  SUBGOAL_THEN `(x0:num) IN dart G /\ FINITE(dart G) /\ node_map G permutes
    dart G`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "x0"] THEN
    REWRITE_TAC[CPMAP_PT_IN_DART; FINITE_DART; NODE_MAP_PERMUTES];
      ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`;
    `n:num`] CPRING_ECPR_ROT_GEN) THEN
  ASM_REWRITE_TAC[ecpR] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LENGTH_ROT_LIST] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rotr_list n (mr:bool list)`;
    `mc:bool list`]) THEN
  ASM_REWRITE_TAC[LENGTH_ROTR_LIST; cprsize] THEN
  MP_TAC(ISPECL [`n:num`; `rotr_list n (mr:bool list)`; `cpring G (x0:num)`]
    MASK_LIST_ROT) THEN
  ASM_REWRITE_TAC[LENGTH_ROTR_LIST; ROT_LIST_ROTR_CANCEL_GEN] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MAP_ROT_LIST] THEN
  ABBREV_TAC `Y = MAP (edge_map (G:(num)hypermap))
                      (mask_list (rotr_list n mr) (cpring G x0))` THEN
  ABBREV_TAC `Ins = insertE (G:(num)hypermap) (mask_list mc (ctrenum cp))` THEN
  ABBREV_TAC `j = LENGTH (FILTER (\b. b) (take_list n (rotr_list n (mr:bool
    list))))` THEN
  REWRITE_TAC[sparse_inv; PAIRWISE; GSYM ALL_MEM; MEM_APPEND;
    MEM_ROT_LIST] THEN
  SUBGOAL_THEN `cnode G (x0:num) (ecpR_pt G n x0)` ASSUME_TAC THENL
   [REWRITE_TAC[cnode; node; ORBIT_MAP_ITER; ecpR_pt] THEN
     MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`;
    `ecpR_pt G n (x0:num)`] CNODE_ORBIT_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
    `PAIRWISE (\x y. ~cnode (G:(num)hypermap) x y) (APPEND Y Ins)` THEN
  REWRITE_TAC[PAIRWISE_APPEND; MEM_ROT_LIST] THEN
  MP_TAC(ISPECL [`\x y. ~cnode (G:(num)hypermap) x y`; `j:num`; `Y:num list`]
    PAIRWISE_SYM_ROT_LIST) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[CNODE_SYM]; DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let CTR_SPARSE_Y0 = prove
 (`ctr_sparse [CpY]`,
  REWRITE_TAC[ctr_sparse] THEN
    MAP_EVERY X_GEN_TAC [`mr:bool list`; `mc:bool list`] THEN
  REWRITE_TAC[cprsize; ctrmsize; ctrenum; CPMAP_CONS_Y;
    CPMAP_NIL_PAIR;
              FST; SND; RING_Y0; LENGTH; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REWRITE_TAC[CFCTR_OK_Y0; nsp] THEN
  MP_TAC(ISPECL [`cpmap0`; `1`] ECPY_FRESH) THEN
  REWRITE_TAC[NODE_CPMAP0_1] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpY cpmap0 1`; `ecpY_pt cpmap0 1`] MEM_CPRING) THEN
  ASM_SIMP_TAC[DART_ECPY_CASES; NODE_CPMAP0_1; RING_Y0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[sparse_inv; PAIRWISE; GSYM ALL_MEM;
    GSYM th]) THEN
  REWRITE_TAC[MEM; MASK_LIST_CLAUSES; INSERTE_CLAUSES; APPEND; MAP] THEN
  MAP_EVERY BOOL_CASES_TAC [`h:bool`; `h':bool`; `h'':bool`] THEN
  REWRITE_TAC[MASK_LIST_CLAUSES; MAP; MEM; APPEND; ALL; PAIRWISE] THEN
  ASM_SIMP_TAC[EDGE_ECPY_RINGB; EDGE_ECPY_APEX_GEN; EDGE_ECPY_OLD;
    NODE_CPMAP0_1;
               DART_ECPY_CASES; EDGE_CPMAP0_1] THEN
  REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[NODE_CPMAP0_1]);;

let CNODE_ECPY_RING = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ proper_cpring G x0
     ==> (cnode (ecpY G x0) (ecpY_pt G x0) z <=>
          z = SND(new_dart2(dart G)) \/ z = ecpY_pt G x0 \/ MEM z (TL(cpring G
            x0)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpY (G:(num)hypermap) x0`; `ecpY_pt (G:(num)hypermap) x0`;
                 `z:num`] MEM_CPRING) THEN
  ASM_SIMP_TAC[DART_ECPY_CASES; CPRING_ECPY; MEM]);;

let CNODE_ECPY_N1 = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G
     ==> (cnode (ecpY G x0) (node_map G x0) z <=>
          z = node_map G x0 \/ z = ecpU_pt G \/
          z = SND(new_dart2(dart(ecpU G x0)))) /\
         (cnode (ecpY G x0) (ecpU_pt G) z <=>
          z = ecpU_pt G \/ z = SND(new_dart2(dart(ecpU G x0))) \/
          z = node_map G x0) /\
         (cnode (ecpY G x0) (SND(new_dart2(dart(ecpU G x0)))) z <=>
          z = SND(new_dart2(dart(ecpU G x0))) \/ z = node_map G x0 \/
          z = ecpU_pt G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] NODE_ECPY_3CYCLE) THEN
  ASM_REWRITE_TAC[ecpU_pt] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC CNODE_3CYCLE THEN ASM_REWRITE_TAC[ecpU_pt]);;

let CNODE_ECPY_OLD = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     z IN dart G /\ ~cnode G x0 z
     ==> !w. cnode (ecpY G x0) z w <=> cnode G z w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CNODE_PRESERVED THEN
  EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NODE_ECPY_OLD THEN ASM_REWRITE_TAC[]);;

let CNODE_ECPH_RING = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ proper_cpring G x0
     ==> (cnode (ecpH G x0) (ecpH_pt G x0) z <=>
          z = SND(new_dart2(dart G)) \/ z = ecpH_pt G x0 \/
          MEM z (TL(TL(cpring G x0))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpH (G:(num)hypermap) x0`; `ecpH_pt (G:(num)hypermap) x0`;
                 `z:num`] MEM_CPRING) THEN
  ASM_SIMP_TAC[DART_ECPH_CASES; CPRING_ECPH; NODE_ECPY_PT_VALUE; MEM]);;

let CNODE_ECPH_N2 = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ FINITE(dart G) /\ plain_hypermap G /\
     edge_map G permutes dart G /\ node_map G permutes dart G /\
     face_map G permutes dart G /\ proper_cpring G x0
     ==> (cnode (ecpH G x0) (ecpY_pt G x0) z <=>
          z = ecpY_pt G x0 \/ z = SND(new_dart2(dart(ecpY G x0))) \/ z = x0) /\
         (cnode (ecpH G x0) (SND(new_dart2(dart(ecpY G x0)))) z <=>
          z = SND(new_dart2(dart(ecpY G x0))) \/ z = x0 \/ z = ecpY_pt G x0) /\
         (cnode (ecpH G x0) x0 z <=>
          z = x0 \/ z = ecpY_pt G x0 \/ z = SND(new_dart2(dart(ecpY G x0))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] NODE_ECPH_3CYCLE) THEN
  ASM_SIMP_TAC[EDGE_ECPY_APEX_GEN; FACE_ECPY_B] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CNODE_3CYCLE THEN ASM_REWRITE_TAC[]);;

let CNODE_ECPH_OLD = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     z IN dart G /\ ~cnode G x0 z
     ==> !w. cnode (ecpH G x0) z w <=> cnode G z w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CNODE_PRESERVED THEN
  EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NODE_ECPH_OLD THEN ASM_REWRITE_TAC[]);;

let CNODE_ECPH_N1 = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0
     ==> (cnode (ecpH G x0) (node_map G x0) z <=>
          z = node_map G x0 \/ z = ecpU_pt G \/
          z = SND(new_dart2(dart(ecpU G x0)))) /\
         (cnode (ecpH G x0) (ecpU_pt G) z <=>
          z = ecpU_pt G \/ z = SND(new_dart2(dart(ecpU G x0))) \/
          z = node_map G x0) /\
         (cnode (ecpH G x0) (SND(new_dart2(dart(ecpU G x0)))) z <=>
          z = SND(new_dart2(dart(ecpU G x0))) \/ z = node_map G x0 \/
          z = ecpU_pt G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. MEM w (TL(cpring G (x0:num))) ==> w IN dart G`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MEM_CPRING_IN_DART THEN
    EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEM_TL_IMP THEN ASM_SIMP_TAC[CPRING_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `~(MEM (node_map G (x0:num)) (TL(cpring G x0)))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] PAIRWISE_CPRING) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[PAIRWISE; TL; ALL; MEM; GSYM ALL_MEM] THEN
      MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(node_map G x0:num) IN dart G` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. (u = node_map G x0 \/ u = ecpU_pt G \/
         u = SND(new_dart2(dart(ecpU G x0))))
        ==> node_map (ecpH G x0) u = node_map (ecpY G x0) u`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC NODE_ECPH_ECPY_OFF THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM node; GSYM cnode] THEN
    ASM_SIMP_TAC[DART_ECPY_CASES; CNODE_ECPY_RING] THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] NODE_ECPY_3CYCLE) THEN
  ASM_REWRITE_TAC[ecpU_pt] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC CNODE_3CYCLE THEN ASM_SIMP_TAC[ecpU_pt]);;

let PAIRWISE_SYM_MEM_IMP = prove
 (`!(R:A->A->bool) l.
     PAIRWISE R l /\ (!x y. MEM x l /\ MEM y l /\ R x y ==> R y x)
     ==> !x y. MEM x l /\ MEM y l /\ ~(x = y) ==> R x y`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[PAIRWISE; MEM; GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let SPARSE_INV_IMP = prove
 (`!(G:(num)hypermap) x0 S.
     sparse_inv G x0 S
     ==> PAIRWISE (\x y. ~(x = y)) S /\
         (!z. MEM z S ==> z IN dart G /\ ~cnode G x0 z) /\
         (!z w. MEM z S /\ MEM w S /\ ~(z = w) ==> ~cnode G z w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sparse_inv; PAIRWISE; GSYM ALL_MEM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_IMPLIES THEN
    EXISTS_TAC `\x y. ~cnode (G:(num)hypermap) x y` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[CNODE_REFL];
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PAIRWISE_SYM_MEM_IMP THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CNODE_SYM]]);;

let SPARSE_INV_OLD = prove
 (`!(G:(num)hypermap) (M:(num)hypermap) x0 p S.
     sparse_inv G x0 S /\
     (!z. MEM z S
          ==> z IN dart M /\ ~cnode M p z /\ (!w. cnode M z w <=> cnode G z w))
     ==> sparse_inv M p S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sparse_inv; PAIRWISE; GSYM ALL_MEM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC PAIRWISE_IMPLIES THEN
    EXISTS_TAC `\x y. ~cnode (G:(num)hypermap) x y` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let SPARSE_INV_INSERT = prove
 (`!(M:(num)hypermap) p S u.
     sparse_inv M p S /\ u IN dart M /\ ~cnode M p u /\
     (!z. MEM z S ==> ~cnode M u z)
     ==> sparse_inv M p (CONS u S)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sparse_inv; PAIRWISE; GSYM ALL_MEM; MEM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SPARSE_INV_SWAP = prove
 (`!(M:(num)hypermap) p l1 l2 l3.
     sparse_inv M p (APPEND l1 (APPEND l2 l3)) <=>
     sparse_inv M p (APPEND l2 (APPEND l1 l3))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sparse_inv; PAIRWISE; GSYM ALL_MEM; MEM_APPEND;
    APPEND_ASSOC] THEN
  MATCH_MP_TAC(TAUT
   `(d1 <=> d2) /\ (d1 ==> (a1 <=> a2)) /\ (d1 ==> (b1 <=> b2))
    ==> ((a1 /\ b1) /\ d1 <=> (a2 /\ b2) /\ d2)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    DISCH_TAC THEN MESON_TAC[];
    DISCH_TAC THEN ONCE_REWRITE_TAC[PAIRWISE_APPEND] THEN
    MP_TAC(ISPECL [`\x y. ~cnode (M:(num)hypermap) x y`; `l1:num list`;
                   `l2:num list`] PAIRWISE_APPEND_SYM_MEM) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MEM_APPEND] THEN REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[CNODE_SYM];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]]]);;

let SPARSE_INV_INSERT_MID = prove
 (`!(M:(num)hypermap) p l1 l2 u.
     sparse_inv M p (APPEND l1 l2) /\ u IN dart M /\ ~cnode M p u /\
     (!z. MEM z l1 \/ MEM z l2 ==> ~cnode M u z)
     ==> sparse_inv M p (APPEND l1 (CONS u l2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `APPEND l1 (CONS u l2) = APPEND l1 (APPEND [u:num] l2)`
    SUBST1_TAC THENL
   [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[SPARSE_INV_SWAP] THEN REWRITE_TAC[APPEND] THEN
  MATCH_MP_TAC SPARSE_INV_INSERT THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MEM_APPEND]);;

let SPARSE_INV_SWAP1 = prove
 (`!(M:(num)hypermap) p l1 u l3.
     sparse_inv M p (APPEND l1 (CONS u l3)) <=>
     sparse_inv M p (CONS u (APPEND l1 l3))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`M:(num)hypermap`; `p:num`; `l1:num list`; `[u:num]`;
                 `l3:num list`] SPARSE_INV_SWAP) THEN
  REWRITE_TAC[APPEND]);;

let SPARSE_INV_SWAP2 = prove
 (`!(M:(num)hypermap) p l1 u v l3.
     sparse_inv M p (APPEND l1 (CONS u (CONS v l3))) <=>
     sparse_inv M p (CONS u (CONS v (APPEND l1 l3)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`M:(num)hypermap`; `p:num`; `l1:num list`; `[u:num; v]`;
                 `l3:num list`] SPARSE_INV_SWAP) THEN
  REWRITE_TAC[APPEND]);;

let SPARSE_INV_INSERT_MID2 = prove
 (`!(M:(num)hypermap) p l1 v l2 u.
     sparse_inv M p (APPEND l1 (CONS v l2)) /\ u IN dart M /\ ~cnode M p u /\
     (!z. MEM z l1 \/ z = v \/ MEM z l2 ==> ~cnode M u z)
     ==> sparse_inv M p (APPEND l1 (CONS v (CONS u l2)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`M:(num)hypermap`; `p:num`; `APPEND l1 [v:num]`;
    `l2:num list`;
                 `u:num`] SPARSE_INV_INSERT_MID) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; MEM_APPEND; MEM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Y and H steps of the sparseness invariant.  The darts of the old list *)
(* lie off the ring of G, so they keep their node orbits and stay off the    *)
(* new ring (SPARSE_INV_ECPY_OLD, SPARSE_INV_ECPH_OLD).  The new darts that  *)
(* the masks can add lie in the new node 3-cycles of ecpY/ecpH, off the new  *)
(* ring (SPARSE_ECPY_NEW, SPARSE_ECPH_NEW); the conditions ~nsp of cfctr_ok  *)
(* allow at most one of them in each 3-cycle, and they are inserted one at a *)
(* time (SPARSE_INV_INSERTS_TAC).                                            *)
(* ------------------------------------------------------------------------- *)

let SPARSE_INV_ECPY_OLD = prove
 (`!(G:(num)hypermap) x0 S.
     x0 IN dart G /\ proper_cpring G x0 /\ sparse_inv G x0 S
     ==> sparse_inv (ecpY G x0) (ecpY_pt G x0) S`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPARSE_INV_OLD THEN
  MAP_EVERY EXISTS_TAC [`G:(num)hypermap`; `x0:num`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:num` o CONJUNCT1 o CONJUNCT2 o
              MATCH_MP SPARSE_INV_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM (z:num) (TL(cpring G x0))` ASSUME_TAC THENL
   [UNDISCH_TAC `~cnode G x0 (z:num)` THEN
    ASM_SIMP_TAC[GSYM MEM_CPRING; CONTRAPOS_THM] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_CONS_HEAD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    SIMP_TAC[MEM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  ASM_SIMP_TAC[DART_H_SUBSET_ECPY; CNODE_ECPY_RING; CNODE_ECPY_OLD;
               FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
               FACE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[]);;

let SPARSE_INV_ECPH_OLD = prove
 (`!(G:(num)hypermap) x0 S.
     x0 IN dart G /\ proper_cpring G x0 /\ sparse_inv G x0 S
     ==> sparse_inv (ecpH G x0) (ecpH_pt G x0) S`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPARSE_INV_OLD THEN
  MAP_EVERY EXISTS_TAC [`G:(num)hypermap`; `x0:num`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:num` o CONJUNCT1 o CONJUNCT2 o
              MATCH_MP SPARSE_INV_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM (z:num) (TL(TL(cpring G x0)))` ASSUME_TAC THENL
   [UNDISCH_TAC `~cnode G x0 (z:num)` THEN
    ASM_SIMP_TAC[GSYM MEM_CPRING; CONTRAPOS_THM] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    SIMP_TAC[MEM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_FRESH) THEN
  ASM_SIMP_TAC[DART_ECPH_CASES; DART_H_SUBSET_ECPY; CNODE_ECPH_RING;
               CNODE_ECPH_OLD; FINITE_DART; EDGE_MAP_PERMUTES;
               NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[]);;

let SPARSE_ECPY_NEW = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ proper_cpring G x0
     ==> ALL (\u. u IN dart (ecpY G x0) /\
                  ~cnode (ecpY G x0) (ecpY_pt G x0) u /\
                  !z. z IN dart G /\ ~cnode G x0 z
                      ==> ~cnode (ecpY G x0) u z)
             [node_map G x0; ecpU_pt G; SND(new_dart2(dart(ecpU G x0)))]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_FRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM (node_map G x0) (TL(cpring G x0)) /\
                (!w:num. MEM w (TL(cpring G x0)) ==> w IN dart G) /\
                cnode G x0 (node_map G x0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] PAIRWISE_CPRING) THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] MEM_CPRING_IN_DART) THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] MEM_CPRING) THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[PAIRWISE; ALL; MEM; GSYM ALL_MEM; TL] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ALL; DART_ECPY_CASES; NODE_MAP_IN_DART; CNODE_ECPY_RING;
               CNODE_ECPY_N1; FINITE_DART; EDGE_MAP_PERMUTES;
               NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[NODE_MAP_IN_DART]);;

let SPARSE_ECPH_NEW = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ proper_cpring G x0 /\ plain_hypermap G
     ==> ALL (\u. u IN dart (ecpH G x0) /\
                  ~cnode (ecpH G x0) (ecpH_pt G x0) u /\
                  !z. z IN dart G /\ ~cnode G x0 z
                      ==> ~cnode (ecpH G x0) u z)
             [node_map G x0; ecpU_pt G; SND(new_dart2(dart(ecpU G x0)));
              ecpY_pt G x0; SND(new_dart2(dart(ecpY G x0))); x0] /\
         ALL (\u. ALL (\v. ~cnode (ecpH G x0) u v /\ ~cnode (ecpH G x0) v u)
                      [ecpY_pt G x0; SND(new_dart2(dart(ecpY G x0))); x0])
             [node_map G x0; ecpU_pt G; SND(new_dart2(dart(ecpU G x0)))]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] th) THEN
                       ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [ECPY_FRESH; ECPH_FRESH; ECPH_FRESH2] THEN
  SUBGOAL_THEN `~MEM (node_map G x0) (TL(TL(cpring G x0))) /\
                ~MEM x0 (TL(TL(cpring G x0))) /\ ~(node_map G x0 = x0) /\
                (!w:num. MEM w (TL(TL(cpring G x0))) ==> w IN dart G) /\
                cnode G x0 (node_map G x0) /\ cnode G x0 x0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] PAIRWISE_CPRING) THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] MEM_CPRING_IN_DART) THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] MEM_CPRING) THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[PAIRWISE; ALL; MEM; GSYM ALL_MEM; TL] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ALL; DART_ECPH_CASES; DART_ECPY_CASES; NODE_MAP_IN_DART;
               CNODE_ECPH_RING; CNODE_ECPH_N1; CNODE_ECPH_N2; FINITE_DART;
               EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[NODE_MAP_IN_DART]);;

(* SPARSE_INV_INSERTS_TAC inserts the new darts of the list (those with an   *)
(* "IN dart" assumption, from SPARSE_ECPY_NEW or SPARSE_ECPH_NEW) at its     *)
(* head or after its first block, then moves the darts that head the         *)
(* induction list back to the front (SPARSE_INV_SWAP1/2) to meet the lifted  *)
(* hypothesis.                                                               *)
let SPARSE_INS_TAC th =
  MATCH_MP_TAC th THEN REPEAT CONJ_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[] THEN NO_TAC; ASM_REWRITE_TAC[] THEN NO_TAC;
    REWRITE_TAC[MEM; MEM_APPEND] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[]];;

let SPARSE_INV_INSERTS_TAC =
  REPEAT(SPARSE_INS_TAC SPARSE_INV_INSERT ORELSE
         SPARSE_INS_TAC SPARSE_INV_INSERT_MID ORELSE
         SPARSE_INS_TAC SPARSE_INV_INSERT_MID2) THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ONCE_REWRITE_TAC[SPARSE_INV_SWAP1] THEN FIRST_ASSUM ACCEPT_TAC;
         ONCE_REWRITE_TAC[SPARSE_INV_SWAP2] THEN FIRST_ASSUM ACCEPT_TAC];;

let SPARSE_INV_ECPY_STEP = prove
 (`!(G:(num)hypermap) x0 t K b1 b2 b3 mr mc.
     x0 IN dart G /\ proper_cpring G x0 /\
     cpring G x0 = CONS (node_map G x0) t /\
     (!z. MEM z K ==> z IN dart G) /\ ~nsp b1 b2 b3 /\
     sparse_inv G x0
       (APPEND (MAP (edge_map G)
                    (mask_list (CONS b3 mr) (CONS (node_map G x0) t)))
               (insertE G (mask_list mc K)))
     ==> sparse_inv (ecpY G x0) (ecpY_pt G x0)
           (APPEND (MAP (edge_map (ecpY G x0))
                        (mask_list (CONS b1 (CONS b2 mr))
                           (CONS (SND(new_dart2(dart G)))
                                 (CONS (ecpY_pt G x0) t))))
                   (insertE (ecpY G x0)
                      (mask_list (CONS b3 mc) (CONS (node_map G x0) K))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC MP_TAC))))) THEN
  SUBGOAL_THEN `(!w. MEM w t ==> w IN dart (G:(num)hypermap)) /\
                node_map G x0 IN dart G` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_CPRING_IN_DART; MEM; NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP (edge_map (ecpY G x0)) (mask_list mr t) =
    MAP (edge_map G) (mask_list mr t) /\
    insertE (ecpY G x0) (mask_list mc K) = insertE G (mask_list mc K) /\
    edge_map (ecpY G x0) (node_map G x0) = edge_map G (node_map G x0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_ECPY_OLD] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MAP_EQ; MATCH_MP_TAC INSERTE_OLD_EQ] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    ASM_MESON_TAC[EDGE_ECPY_OLD; MEM_MASK_LIST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] SPARSE_ECPY_NEW) THEN
  ASM_REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  DISCH_THEN(fun th ->
    MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP SPARSE_INV_IMP th))) THEN
    MP_TAC(MATCH_MP SPARSE_INV_ECPY_OLD
     (CONJ (ASSUME `x0 IN dart (G:(num)hypermap)`)
       (CONJ (ASSUME `proper_cpring (G:(num)hypermap) x0`) th)))) THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`; `b3:bool`] THEN
  ASM_SIMP_TAC[nsp; MASK_LIST_CLAUSES; MAP; APPEND; INSERTE_CLAUSES;
               EDGE_ECPY_RINGB; EDGE_ECPY_APEX_GEN] THEN
  REWRITE_TAC[MEM; MEM_APPEND] THEN REPEAT DISCH_TAC THEN
  SPARSE_INV_INSERTS_TAC);;

let SPARSE_INV_ECPH_STEP = prove
 (`!(G:(num)hypermap) x0 t K b1 b2 b3 b4 b5 mr mc.
     x0 IN dart G /\ proper_cpring G x0 /\ plain_hypermap G /\
     cpring G x0 = CONS (node_map G x0) (CONS x0 t) /\
     (!z. MEM z K ==> z IN dart G) /\ ~(nsp b3 b1 b4 \/ nsp b3 b2 b5) /\
     sparse_inv G x0
       (APPEND (MAP (edge_map G)
                    (mask_list (CONS b4 (CONS b5 mr))
                               (CONS (node_map G x0) (CONS x0 t))))
               (insertE G (mask_list mc K)))
     ==> sparse_inv (ecpH G x0) (ecpH_pt G x0)
           (APPEND (MAP (edge_map (ecpH G x0))
                        (mask_list (CONS b1 (CONS b2 mr))
                           (CONS (SND(new_dart2(dart G)))
                                 (CONS (ecpH_pt G x0) t))))
                   (insertE (ecpH G x0)
                      (mask_list (CONS b3 (CONS b4 (CONS b5 mc)))
                         (CONS (ecpY_pt G x0)
                               (CONS (node_map G x0) (CONS x0 K))))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)))))) THEN
  SUBGOAL_THEN `(!w. MEM w t ==> w IN dart (G:(num)hypermap)) /\
                node_map G x0 IN dart G` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_CPRING_IN_DART; MEM; NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP (edge_map (ecpH G x0)) (mask_list mr t) =
    MAP (edge_map G) (mask_list mr t) /\
    insertE (ecpH G x0) (mask_list mc K) = insertE G (mask_list mc K) /\
    edge_map (ecpH G x0) (node_map G x0) = edge_map G (node_map G x0) /\
    edge_map (ecpH G x0) x0 = edge_map G x0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_ECPH_OLD] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MAP_EQ; MATCH_MP_TAC INSERTE_OLD_EQ] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    ASM_MESON_TAC[EDGE_ECPH_OLD; MEM_MASK_LIST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] SPARSE_ECPH_NEW) THEN
  ASM_REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  DISCH_THEN(fun th ->
    MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP SPARSE_INV_IMP th))) THEN
    MP_TAC(MATCH_MP SPARSE_INV_ECPH_OLD
     (CONJ (ASSUME `x0 IN dart (G:(num)hypermap)`)
       (CONJ (ASSUME `proper_cpring (G:(num)hypermap) x0`) th)))) THEN
  MAP_EVERY BOOL_CASES_TAC
   [`b1:bool`; `b2:bool`; `b3:bool`; `b4:bool`; `b5:bool`] THEN
  ASM_SIMP_TAC[nsp; MASK_LIST_CLAUSES; MAP; APPEND; INSERTE_CLAUSES;
               EDGE_ECPH_RINGB; EDGE_ECPH_APEX; EDGE_ECPH_ECPYPT] THEN
  REWRITE_TAC[MEM; MEM_APPEND] THEN REPEAT DISCH_TAC THEN
  SPARSE_INV_INSERTS_TAC);;

let CTR_SPARSE_Y = prove
 (`!s cp. ctr_sparse (CONS s cp) ==> ctr_sparse (CONS CpY (CONS s cp))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ctr_sparse; cprsize; ctrmsize; ctrenum; NOT_CONS_NIL;
              CPMAP_CONS_Y] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`mr:bool list`; `mc:bool list`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `config_prog (CONS (s:cpstep) cp)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CFCTR_CONFIG_PROG) THEN
    REWRITE_TAC[CONFIG_PROG_CONS_CASES; NOT_CONS_NIL; distinctness "cpstep"];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CFCTR_OK_Y_CASES]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:bool`; `b2:bool`; `b3:bool`; `mr':bool list`;
                       `mc':bool list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `CONS (s:cpstep) cp` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `G = FST(cpmap (CONS (s:cpstep) cp))` THEN
  ABBREV_TAC `x0 = SND(cpmap (CONS (s:cpstep) cp))` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_CONS_HEAD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `t = TL(cpring G (x0:num))` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; SUC_INJ]) THEN
  UNDISCH_TAC `SUC(SUC(LENGTH(mr':bool list))) =
               LENGTH (cpring (ecpY G x0) (ecpY_pt G x0))` THEN
  ASM_SIMP_TAC[CPRING_ECPY; LENGTH; SUC_INJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC SPARSE_INV_ECPY_STEP THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(ASSUME `cpring G x0 = CONS (node_map G x0) t`)] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let CTR_SPARSE_H = prove
 (`!cp. ctr_sparse cp ==> ctr_sparse (CONS CpH cp)`,
  GEN_TAC THEN
  REWRITE_TAC[ctr_sparse; cprsize; ctrmsize; ctrenum; CPMAP_CONS_H] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`mr:bool list`; `mc:bool list`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `config_prog (cp:(cpstep)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CFCTR_CONFIG_PROG) THEN
    REWRITE_TAC[CONFIG_PROG_CONS_CASES; distinctness "cpstep"];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CFCTR_OK_H_CASES]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:bool`; `b2:bool`; `b3:bool`; `b4:bool`; `b5:bool`;
                       `mr':bool list`; `mc':bool list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `G = FST(cpmap (cp:(cpstep)list))` THEN
  ABBREV_TAC `x0 = SND(cpmap (cp:(cpstep)list))` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `t = TL(TL(cpring G (x0:num)))` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; SUC_INJ;
    ARITH_RULE `SUC(SUC(SUC n)) = m + 3 <=> n = m`]) THEN
  UNDISCH_TAC `SUC(SUC(LENGTH(mr':bool list))) =
               LENGTH (cpring (ecpH G x0) (ecpH_pt G x0))` THEN
  ASM_SIMP_TAC[CPRING_ECPH; NODE_ECPY_PT_VALUE; FACE_ECPH_PT; LENGTH;
               SUC_INJ] THEN
  DISCH_TAC THEN MATCH_MP_TAC SPARSE_INV_ECPH_STEP THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(ASSUME
    `cpring G x0 = CONS (node_map G x0) (CONS (x0:num) t)`)] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let SPARSE_CFCTR_ALL = prove
 (`!cp. ctr_sparse cp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CTR_SPARSE_NIL] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(SPEC `h:cpstep` (cases "cpstep")) THEN
  STRUCT_CASES_TAC(ISPEC `t:(cpstep)list` list_CASES) THEN
  MESON_TAC[CTR_SPARSE_R; CTR_SPARSE_VACUOUS; CTR_SPARSE_H;
            CTR_SPARSE_Y0; CTR_SPARSE_Y]);;

(* ------------------------------------------------------------------------- *)
(* The contract edges of a valid contract are sparse and off the ring        *)
(* (Gonthier cfcontract.v sparse_cfctr): instance of the                     *)
(* sparseness invariant with the empty ring mask.                            *)
(* ------------------------------------------------------------------------- *)

let VALID_CFCTR_CC = prove
 (`!cp mc. config_prog cp /\ LENGTH mc = ctrmsize cp /\
           cfctr_ok (REPLICATE (cprsize cp) F) mc cp
           ==> sparse (FST(cpmap cp))
                 (insertE (FST(cpmap cp)) (mask_list mc (ctrenum cp))) /\
               (!x. MEM x (insertE (FST(cpmap cp)) (mask_list mc (ctrenum cp)))
                    ==> ~(MEM x (cpring (FST(cpmap cp)) (SND(cpmap cp)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `cp:(cpstep)list` SPARSE_CFCTR_ALL) THEN
    REWRITE_TAC[ctr_sparse] THEN
  DISCH_THEN(MP_TAC o SPECL [`REPLICATE (cprsize cp) F`; `mc:bool list`]) THEN
  ASM_REWRITE_TAC[LENGTH_REPLICATE; MASK_LIST_REPLICATE_F; MAP; APPEND] THEN
  REWRITE_TAC[sparse_inv; PAIRWISE; GSYM ALL_MEM] THEN STRIP_TAC THEN
    CONJ_TAC THENL
   [MATCH_MP_TAC SPARSE_OF_PAIRWISE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`FST(cpmap (cp:(cpstep)list))`;
      `SND(cpmap (cp:(cpstep)list))`;
                   `x:num`] MEM_CPRING) THEN
    REWRITE_TAC[CPMAP_PT_IN_DART] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Adjacency transfer through the Y step (used by the face-mask lemmas       *)
(* below).                                                                   *)
(* ------------------------------------------------------------------------- *)

let SUB_ADJ_LIFT = prove
 (`!(H:(num)hypermap) H' x y.
     (!u v. u IN dart H /\ cface H u v ==> cface H' u v) /\
     (!u. u IN dart H ==> edge_map H' u = edge_map H u) /\
     x IN dart H /\ adj H x y
     ==> adj H' x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[adj; rlink; GSYM cface] THEN STRIP_TAC THEN
  EXISTS_TAC `z:num` THEN
  SUBGOAL_THEN `z IN dart (H:(num)hypermap) /\ edge_map H z IN dart H`
  STRIP_ASSUME_TAC THENL
   [CFACE_TAC[]; ASM_SIMP_TAC[]]);;

let SUB_ADJ_ICPY = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ FINITE(dart H) /\ edge_map H permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\
     x IN dart H /\ y IN dart H /\ adj H x y
     ==> adj (ecpY H x0) x y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUB_ADJ_LIFT THEN
  EXISTS_TAC `H:(num)hypermap` THEN
  ASM_SIMP_TAC[CFACE_ECPY_LIFT; EDGE_ECPY_OLD]);;

(* ------------------------------------------------------------------------- *)
(* Face masks (Gonthier cfmap.v proper_cpmask1, cpmask1, cpadj_proper,       *)
(* cpmask_adj and cfcontract.v ctrband_correct), proved as inductions over   *)
(* the construction program with one geometric lemma per step, following the *)
(* Coq proofs: the faces of the new darts of ecpY/ecpH (ECPY_APEX_ATOMS,     *)
(* ECPY_OLD_ATOMS, ECPH_OLD_ATOMS, ECPH_APEX_ATOMS), the two cases of        *)
(* fband_icpY/fband_icpH for a dart of the new map (an old face, or the face *)
(* of the new pointer: ECPY_OLD_CASE, ECPY_APEX_CASE, ECPH_OLD_CASE and      *)
(* ECPH_APEX_CASE; ECPY_SETUP and ECPH_SETUP give the shape of the rings and *)
(* FBAND_ICPY_TRANSFER, FBAND_ICPH_TRANSFER move a dart to its               *)
(* representative), the step lemmas CPMASK_ADJ_STEP_R, CPMASK_ADJ_STEP_Y,    *)
(* CPMASK_ADJ_STEP_H and CTRBAND_STEP_R, CTRBAND_STEP_Y, CTRBAND_STEP_H, and *)
(* the program-level inductions on the predicates cpmask_adj_ok and          *)
(* ctrband_ok.  The propositional cores of the steps are closed by TAUT.     *)
(* ------------------------------------------------------------------------- *)

let FBAND_MASK_CONS = prove
 (`!(H:(A)hypermap) c m a s y.
     fband H (mask_list (CONS c m) (CONS a s)) y <=>
     (c /\ cface H y a) \/ fband H (mask_list m s) y`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
  REWRITE_TAC[MASK_LIST_CLAUSES; FBAND_CONS]);;

let EX_MASK_CONS = prove
 (`!(P:A->bool) c m a s.
     EX P (mask_list (CONS c m) (CONS a s)) <=>
     (c /\ P a) \/ EX P (mask_list m s)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
  REWRITE_TAC[MASK_LIST_CLAUSES; EX]);;

let FBAND_INSERTE_MASK_CONS = prove
 (`!(H:(A)hypermap) c m a s y.
     fband H (insertE H (mask_list (CONS c m) (CONS a s))) y <=>
     (c /\ (cface H y a \/ cface H y (edge_map H a))) \/
     fband H (insertE H (mask_list m s)) y`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
  REWRITE_TAC[MASK_LIST_CLAUSES; INSERTE_CLAUSES; FBAND_CONS; DISJ_ASSOC]);;

let EX_MEM_CONG = prove
 (`!(P:A->bool) Q p. (!z. MEM z p ==> (P z <=> Q z)) ==> (EX P p <=> EX Q p)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[EX; MEM] THEN ASM_MESON_TAC[]);;

let FBAND_CFACE_CONG2 = prove
 (`!(H1:(A)hypermap) (H2:(A)hypermap) p u x.
     (!z. MEM z p ==> (cface H1 u z <=> cface H2 x z))
     ==> (fband H1 p u <=> fband H2 p x)`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[]);;

let EX_ADJ_CFACE_CONG = prove
 (`!(H:(A)hypermap) p u x.
     u IN dart H /\ cface H u x ==> (EX (adj H u) p <=> EX (adj H x) p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EX_MEM_CONG THEN
  ASM_MESON_TAC[ADJ_CFACE_L]);;

let FBAND_OUT_DART = prove
 (`!(H:(A)hypermap) p x.
     ~(x IN dart H) /\ (!z. MEM z p ==> z IN dart H) ==> ~fband H p x`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[CFACE_LEFT_IN_DART]);;

let ADJ_LEFT_IN_DART = prove
 (`!(H:(A)hypermap) x y. adj H x y /\ y IN dart H ==> x IN dart H`,
  REWRITE_TAC[adj; rlink; GSYM cface] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `H:(A)hypermap` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  ASM_MESON_TAC[CFACE_LEFT_IN_DART; PERMUTES_IN_IMAGE]);;

let EX_ADJ_OUT_DART = prove
 (`!(H:(A)hypermap) p x.
     ~(x IN dart H) /\ (!z. MEM z p ==> z IN dart H) ==> ~EX (adj H x) p`,
  REWRITE_TAC[GSYM EX_MEM] THEN MESON_TAC[ADJ_LEFT_IN_DART]);;

let MASK_LIST_CONS_CONS = prove
 (`!b m (h:A) t. mask_list (CONS b m) (CONS h t) =
                 if b then CONS h (mask_list m t) else mask_list m t`,
  REWRITE_TAC[mask_list; NOT_CONS_NIL; HD; TL]);;

let CFACE_RIGHT_CONG = prove
 (`!(H:(A)hypermap) a b z.
     a IN dart H /\ cface H a b ==> (cface H z a <=> cface H z b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CFACE_TAC[]);;

let ADJ_ECPY_APEX_IFF = prove
 (`!(G:(num)hypermap) x0 u.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0
     ==> (adj (ecpY G x0) (ecpY_pt G x0) u <=>
          cface (ecpY G x0) u (node_map G x0) \/ cface (ecpY G x0) u x0)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC ADJ_ECPY_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_NODE_ECPY) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPY_B_PT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_APEX_TWO_CYCLE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPY_ECPUPT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPY_APEX_GEN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[adj; rlink; GSYM cface] THENL
   [EXISTS_TAC `ecpU_pt (G:(num)hypermap)`;
    EXISTS_TAC `ecpY_pt (G:(num)hypermap) x0`] THEN
  CFACE_TAC[]);;

let ECPY_APEX_ATOMS = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0
     ==> ~cface (ecpY G x0) (ecpY_pt G x0) (SND(new_dart2(dart G))) /\
         (!z. z IN dart G ==> ~cface (ecpY G x0) (ecpY_pt G x0) z) /\
         adj (ecpY G x0) (ecpY_pt G x0) (SND(new_dart2(dart G))) /\
         ~adj (ecpY G x0) (ecpY_pt G x0) (ecpY_pt G x0) /\
         adj (ecpY G x0) (ecpY_pt G x0) x0 /\
         (!z. z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0
              ==> ~adj (ecpY G x0) (ecpY_pt G x0) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] NODE_MAP_IN_DART) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPY_APEX_NOT_B) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_NODE_ECPY) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPY_APEX_OLD) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ADJ_ECPY_APEX_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  CFACE_TAC[ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPY_PROJ]);;

let ECPY_OLD_ATOMS = prove
 (`!(G:(num)hypermap) x0 x.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     plain_hypermap G /\ proper_cpring G x0 /\ x IN dart G
     ==> (cface (ecpY G x0) x (SND(new_dart2(dart G))) <=>
          cface G x (node_map G x0)) /\
         ~cface (ecpY G x0) x (ecpY_pt G x0) /\
         (cface (ecpY G x0) x x0 <=> cface G x x0) /\
         (adj (ecpY G x0) x (SND(new_dart2(dart G))) <=>
          adj G x (node_map G x0)) /\
         (adj (ecpY G x0) x (ecpY_pt G x0) <=>
          cface G x (node_map G x0) \/ cface G x x0) /\
         (adj (ecpY G x0) x x0 <=> adj G x x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `node_map G (x0:num) IN dart G` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN dart G ==> (cface (ecpY G x0) x z <=> cface G x z)`
  ASSUME_TAC THENL [ASM_MESON_TAC[CFACE_ICPY]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN dart G ==> (adj (ecpY G x0) x z <=> adj G x z)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ADJ_ICPY_IMP; SUB_ADJ_ICPY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_NODE_ECPY) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_IN_DART_ECPY) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_PT_IN_DART) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] PLAIN_ECPY) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`] DART_H_SUBSET_ECPY) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`]
                CFACE_ECPY_APEX_OLD) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`] ADJ_ECPY_APEX_IFF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CFACE_RIGHT_CONG];
    ASM_MESON_TAC[CFACE_SYM_GEN];
    ASM_MESON_TAC[ADJ_CFACE];
    ASM_MESON_TAC[ADJ_SYM]]);;

let ECPY_OLD_LISTS = prove
 (`!(G:(num)hypermap) x0 x p.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     x IN dart G /\ (!z. MEM z p ==> z IN dart G)
     ==> (fband (ecpY G x0) p x <=> fband G p x) /\
         (EX (adj (ecpY G x0) x) p <=> EX (adj G x) p)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC FBAND_CFACE_CONG2 THEN ASM_MESON_TAC[CFACE_ICPY];
    MATCH_MP_TAC EX_MEM_CONG THEN ASM_MESON_TAC[ADJ_ICPY_IMP; SUB_ADJ_ICPY]]);;

let ECPY_OLD_CASE = prove
 (`!(G:(num)hypermap) x0 x r2 k c0 c1 c2 mr' mk' d0 d1 d2 mr0 mk.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     plain_hypermap G /\ proper_cpring G x0 /\ x IN dart G /\
     (!z. MEM z r2
          ==> z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0) /\
     (!z. MEM z k
          ==> z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0)
     ==> (fband (ecpY G x0)
            (APPEND (mask_list (CONS c0 (CONS c1 (CONS c2 mr')))
                               (CONS (SND(new_dart2(dart G)))
                                     (CONS (ecpY_pt G x0) (CONS x0 r2))))
                    (mask_list mk' k)) x <=>
          (c0 /\ cface G x (node_map G x0)) \/ (c2 /\ cface G x x0) \/
          fband G (mask_list mr' r2) x \/ fband G (mask_list mk' k) x) /\
         (EX (adj (ecpY G x0) x)
            (APPEND (mask_list (CONS d0 (CONS d1 (CONS d2 mr0)))
                               (CONS (SND(new_dart2(dart G)))
                                     (CONS (ecpY_pt G x0) (CONS x0 r2))))
                    (mask_list mk k)) <=>
          (d0 /\ adj G x (node_map G x0)) \/
          (d1 /\ (cface G x (node_map G x0) \/ cface G x x0)) \/
          (d2 /\ adj G x x0) \/
          EX (adj G x) (mask_list mr0 r2) \/ EX (adj G x) (mask_list mk k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FBAND_APPEND; EX_APPEND; FBAND_MASK_CONS; EX_MASK_CONS] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`] ECPY_OLD_ATOMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!z:num. MEM z (mask_list mr' r2) ==> z IN dart G) /\
    (!z:num. MEM z (mask_list mk' k) ==> z IN dart G) /\
    (!z:num. MEM z (mask_list mr0 r2) ==> z IN dart G) /\
    (!z:num. MEM z (mask_list mk k) ==> z IN dart G)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MEM_MASK_LIST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                 `mask_list mr' (r2:(num)list)`] ECPY_OLD_LISTS) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                 `mask_list mk' (k:(num)list)`] ECPY_OLD_LISTS) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                 `mask_list mr0 (r2:(num)list)`] ECPY_OLD_LISTS) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                 `mask_list mk (k:(num)list)`] ECPY_OLD_LISTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT);;

let ECPY_APEX_CASE = prove
 (`!(G:(num)hypermap) x0 r2 k c0 c1 c2 mr' mk' d0 d1 d2 mr0 mk.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\
     (!z. MEM z r2
          ==> z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0) /\
     (!z. MEM z k
          ==> z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0)
     ==> (fband (ecpY G x0)
            (APPEND (mask_list (CONS c0 (CONS c1 (CONS c2 mr')))
                               (CONS (SND(new_dart2(dart G)))
                                     (CONS (ecpY_pt G x0) (CONS x0 r2))))
                    (mask_list mk' k)) (ecpY_pt G x0) <=> c1) /\
         (EX (adj (ecpY G x0) (ecpY_pt G x0))
            (APPEND (mask_list (CONS d0 (CONS d1 (CONS d2 mr0)))
                               (CONS (SND(new_dart2(dart G)))
                                     (CONS (ecpY_pt G x0) (CONS x0 r2))))
                    (mask_list mk k)) <=> d0 \/ d2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FBAND_APPEND; EX_APPEND; FBAND_MASK_CONS; EX_MASK_CONS] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPY_APEX_ATOMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CFACE_REFL] THEN
  SUBGOAL_THEN
   `~cface (ecpY G x0) (ecpY_pt G x0) x0 /\
    ~fband (ecpY G x0) (mask_list mr' r2) (ecpY_pt G x0) /\
    ~fband (ecpY G x0) (mask_list mk' k) (ecpY_pt G x0) /\
    ~EX (adj (ecpY G x0) (ecpY_pt G x0)) (mask_list mr0 r2) /\
    ~EX (adj (ecpY G x0) (ecpY_pt G x0)) (mask_list mk k)`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FBAND_MEM_IFF; GSYM EX_MEM] THEN ASM_MESON_TAC[MEM_MASK_LIST]);;

let ECPY_APEX_NOT_FBAND_OLD = prove
 (`!(G:(num)hypermap) x0 p.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     (!z. MEM z p ==> z IN dart G)
     ==> ~fband (ecpY G x0) p (ecpY_pt G x0)`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[CFACE_ECPY_APEX_OLD]);;

let ECPY_SETUP = prove
 (`!(G:(num)hypermap) x0 k.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\ (!z. MEM z k ==> z IN dart G) /\
     face_simple G (APPEND (cpring G x0) k)
     ==> ?r2. cpring G x0 = CONS (node_map G x0) (CONS x0 r2) /\
              cpring (ecpY G x0) (ecpY_pt G x0) =
              CONS (SND(new_dart2(dart G)))
                   (CONS (ecpY_pt G x0) (CONS x0 r2)) /\
              (!z. MEM z r2
                   ==> z IN dart G /\ ~cface G z (node_map G x0) /\
                       ~cface G z x0) /\
              (!z. MEM z k
                   ==> z IN dart G /\ ~cface G z (node_map G x0) /\
                       ~cface G z x0)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `TL(TL(cpring (G:(num)hypermap) x0))` THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_ECPY) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r2 = TL(TL(cpring (G:(num)hypermap) x0))` THEN
  SUBGOAL_THEN `!z:num. MEM z r2 ==> z IN dart G` ASSUME_TAC THENL
   [EXPAND_TAC "r2" THEN ASM_MESON_TAC[MEM_TL_TL_CPRING_IN_DART]; ALL_TAC] THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN REWRITE_TAC[th]) THEN
  REWRITE_TAC[TL] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `face_simple G (APPEND (CONS (node_map G x0) (CONS x0 r2))
                                     (k:(num)list))` THEN
  REWRITE_TAC[APPEND; face_simple] THEN STRIP_TAC THEN CFACE_TAC[]);;

let FBAND_ICPY_TRANSFER = prove
 (`!(G:(num)hypermap) x0 u.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     u IN dart(ecpY G x0)
     ==> (?x. x IN dart G /\
              (!l. fband (ecpY G x0) l u <=> fband (ecpY G x0) l x) /\
              (!w. cface (ecpY G x0) u w <=> cface (ecpY G x0) x w) /\
              (!l. EX (adj (ecpY G x0) u) l <=> EX (adj (ecpY G x0) x) l)) \/
         (!l. fband (ecpY G x0) l u <=>
              fband (ecpY G x0) l (ecpY_pt G x0)) /\
         (!w. cface (ecpY G x0) u w <=>
              cface (ecpY G x0) (ecpY_pt G x0) w) /\
         (!l. EX (adj (ecpY G x0) u) l <=>
              EX (adj (ecpY G x0) (ecpY_pt G x0)) l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`] FBAND_ICPY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)
                              ASSUME_TAC) THENL
   [DISJ1_TAC THEN EXISTS_TAC `x:num`; DISJ2_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[FBAND_CFACE_CONG_ELT; CFACE_TRANS; EX_ADJ_CFACE_CONG]);;

let ADJ_ICPH_IFF = prove
 (`!(G:(num)hypermap) x0 x y.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\ x IN dart G /\ y IN dart G
     ==> (adj (ecpH G x0) x y <=> adj G x y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[ADJ_ICPH_IMP];
    DISCH_TAC THEN MATCH_MP_TAC SUB_ADJ_LIFT THEN
    EXISTS_TAC `G:(num)hypermap` THEN
    ASM_MESON_TAC[CFACE_ECPH_LIFT; EDGE_ECPH_OLD]]);;

let ADJ_ECPH_APEX_IFF = prove
 (`!(G:(num)hypermap) x0 u.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0
     ==> (adj (ecpH G x0) (ecpH_pt G x0) u <=>
          cface (ecpH G x0) u (node_map G x0) \/ cface (ecpH G x0) u x0 \/
          cface (ecpH G x0) u (face_map G (edge_map G x0)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC ADJ_ECPH_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_YA) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_NODE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_BPRIME) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_PT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_ECPUPT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_ECPYPT) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] EDGE_ECPH_APEX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[adj; rlink; GSYM cface] THENL
   [EXISTS_TAC `ecpU_pt (G:(num)hypermap)`;
    EXISTS_TAC `ecpY_pt (G:(num)hypermap) x0`;
    EXISTS_TAC `ecpH_pt (G:(num)hypermap) x0`] THEN
  CFACE_TAC[]);;

let ECPH_OLD_ATOMS = prove
 (`!(G:(num)hypermap) x0 x.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     plain_hypermap G /\ proper_cpring G x0 /\ x IN dart G
     ==> (cface (ecpH G x0) x (SND(new_dart2(dart G))) <=>
          cface G x (node_map G x0)) /\
         ~cface (ecpH G x0) x (ecpH_pt G x0) /\
         ~cface (ecpH G x0) x (ecpY_pt G x0) /\
         (cface (ecpH G x0) x (SND(new_dart2(dart(ecpU G x0)))) <=>
          cface G x x0) /\
         (cface (ecpH G x0) x (node_map G x0) <=> cface G x (node_map G x0)) /\
         (cface (ecpH G x0) x (edge_map G (node_map G x0)) <=> cface G x x0) /\
         (cface (ecpH G x0) x x0 <=> cface G x x0) /\
         (cface (ecpH G x0) x (edge_map G x0) <=>
          cface G x (face_map G (edge_map G x0))) /\
         (cface (ecpH G x0) x (face_map G (edge_map G x0)) <=>
          cface G x (face_map G (edge_map G x0))) /\
         (adj (ecpH G x0) x (SND(new_dart2(dart G))) <=>
          adj G x (node_map G x0)) /\
         (adj (ecpH G x0) x (ecpH_pt G x0) <=>
          cface G x (node_map G x0) \/ cface G x x0 \/
          cface G x (face_map G (edge_map G x0))) /\
         (adj (ecpH G x0) x (face_map G (edge_map G x0)) <=>
          adj G x (face_map G (edge_map G x0))) /\
         (adj (ecpH G x0) x x0 <=> adj G x x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `node_map G (x0:num) IN dart G /\ edge_map G (node_map G x0) IN dart G /\
    edge_map G x0 IN dart G /\ face_map G (edge_map G x0) IN dart G`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN dart G ==> (cface (ecpH G x0) x z <=> cface G x z)`
  ASSUME_TAC THENL [ASM_MESON_TAC[CFACE_ICPH]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN dart G ==> (adj (ecpH G x0) x z <=> adj G x z)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ADJ_ICPH_IFF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `SND(new_dart2(dart G)) IN dart(ecpH (G:(num)hypermap) x0) /\
    SND(new_dart2(dart(ecpU G x0))) IN dart(ecpH G x0) /\ x IN dart(ecpH G x0)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[DART_ECPY_SUBSET_ECPH; HEAD_IN_DART_ECPY; DART_SUBSET_ECPH;
                  BPRIME_IN_DART_ECPY; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_NODE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_BPRIME) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_YA) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_PT_IN_DART) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] PLAIN_ECPH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`]
                CFACE_ECPH_APEX_OLD) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`] ADJ_ECPH_APEX_IFF) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[CFACE_RIGHT_CONG; CFACE_SYM_GEN; ADJ_CFACE; ADJ_SYM;
                CFACE_EDGE_NODE; CFT_FACE]);;

let ECPH_APEX_ATOMS = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0
     ==> ~cface (ecpH G x0) (ecpH_pt G x0) (SND(new_dart2(dart G))) /\
         (!z. z IN dart G ==> ~cface (ecpH G x0) (ecpH_pt G x0) z) /\
         cface (ecpH G x0) (ecpH_pt G x0) (ecpY_pt G x0) /\
         ~cface (ecpH G x0) (ecpH_pt G x0) (SND(new_dart2(dart(ecpU G x0)))) /\
         ~cface (ecpH G x0) (ecpH_pt G x0) (node_map G x0) /\
         ~cface (ecpH G x0) (ecpH_pt G x0) (edge_map G (node_map G x0)) /\
         ~cface (ecpH G x0) (ecpH_pt G x0) x0 /\
         ~cface (ecpH G x0) (ecpH_pt G x0) (edge_map G x0) /\
         adj (ecpH G x0) (ecpH_pt G x0) (SND(new_dart2(dart G))) /\
         ~adj (ecpH G x0) (ecpH_pt G x0) (ecpH_pt G x0) /\
         adj (ecpH G x0) (ecpH_pt G x0) (face_map G (edge_map G x0)) /\
         adj (ecpH G x0) (ecpH_pt G x0) x0 /\
         (!z. z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0 /\
              ~cface G z (face_map G (edge_map G x0))
              ==> ~adj (ecpH G x0) (ecpH_pt G x0) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `node_map G (x0:num) IN dart G /\ edge_map G (node_map G x0) IN dart G /\
    edge_map G x0 IN dart G /\ face_map G (edge_map G x0) IN dart G`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_NOT_B) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_B_NODE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_YA) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_BPRIME) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_APEX_OLD) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ADJ_ECPH_APEX_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  CFACE_TAC[ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPH_PROJ]);;

let ECPH_OLD_LISTS = prove
 (`!(G:(num)hypermap) x0 x p.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\ x IN dart G /\ (!z. MEM z p ==> z IN dart G)
     ==> (fband (ecpH G x0) p x <=> fband G p x) /\
         (EX (adj (ecpH G x0) x) p <=> EX (adj G x) p)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC FBAND_CFACE_CONG2 THEN ASM_MESON_TAC[CFACE_ICPH];
    MATCH_MP_TAC EX_MEM_CONG THEN ASM_MESON_TAC[ADJ_ICPH_IFF]]);;

let ECPH_OLD_CASE = prove
 (`!(G:(num)hypermap) x0 x r3 k c0 c1 c2 mr' ck mk' d0 d1 d2 mr0 dk mk0.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     plain_hypermap G /\ proper_cpring G x0 /\ x IN dart G /\
     (!z. MEM z r3
          ==> z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0 /\
              ~cface G z (face_map G (edge_map G x0))) /\
     (!z. MEM z k
          ==> z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0 /\
              ~cface G z (face_map G (edge_map G x0)))
     ==> (fband (ecpH G x0)
            (APPEND (mask_list (CONS c0 (CONS c1 (CONS c2 mr')))
                               (CONS (SND(new_dart2(dart G)))
                                     (CONS (ecpH_pt G x0)
                                           (CONS (face_map G (edge_map G x0))
                                                 r3))))
                    (mask_list (CONS ck mk') (CONS x0 k))) x <=>
          (c0 /\ cface G x (node_map G x0)) \/
          (c2 /\ cface G x (face_map G (edge_map G x0))) \/
          fband G (mask_list mr' r3) x \/
          (ck /\ cface G x x0) \/ fband G (mask_list mk' k) x) /\
         (EX (adj (ecpH G x0) x)
            (APPEND (mask_list (CONS d0 (CONS d1 (CONS d2 mr0)))
                               (CONS (SND(new_dart2(dart G)))
                                     (CONS (ecpH_pt G x0)
                                           (CONS (face_map G (edge_map G x0))
                                                 r3))))
                    (mask_list (CONS dk mk0) (CONS x0 k))) <=>
          (d0 /\ adj G x (node_map G x0)) \/
          (d1 /\ (cface G x (node_map G x0) \/ cface G x x0 \/
                  cface G x (face_map G (edge_map G x0)))) \/
          (d2 /\ adj G x (face_map G (edge_map G x0))) \/
          EX (adj G x) (mask_list mr0 r3) \/
          (dk /\ adj G x x0) \/ EX (adj G x) (mask_list mk0 k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FBAND_APPEND; EX_APPEND; FBAND_MASK_CONS; EX_MASK_CONS] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`] ECPH_OLD_ATOMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!z:num. MEM z (mask_list mr' r3) ==> z IN dart G) /\
    (!z:num. MEM z (mask_list mk' k) ==> z IN dart G) /\
    (!z:num. MEM z (mask_list mr0 r3) ==> z IN dart G) /\
    (!z:num. MEM z (mask_list mk0 k) ==> z IN dart G)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MEM_MASK_LIST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                 `mask_list mr' (r3:(num)list)`] ECPH_OLD_LISTS) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                 `mask_list mk' (k:(num)list)`] ECPH_OLD_LISTS) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                 `mask_list mr0 (r3:(num)list)`] ECPH_OLD_LISTS) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                 `mask_list mk0 (k:(num)list)`] ECPH_OLD_LISTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT);;

let ECPH_APEX_CASE = prove
 (`!(G:(num)hypermap) x0 r3 k c0 c1 c2 mr' ck mk' d0 d1 d2 mr0 dk mk0.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\
     (!z. MEM z r3
          ==> z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0 /\
              ~cface G z (face_map G (edge_map G x0))) /\
     (!z. MEM z k
          ==> z IN dart G /\ ~cface G z (node_map G x0) /\ ~cface G z x0 /\
              ~cface G z (face_map G (edge_map G x0)))
     ==> (fband (ecpH G x0)
            (APPEND (mask_list (CONS c0 (CONS c1 (CONS c2 mr')))
                               (CONS (SND(new_dart2(dart G)))
                                     (CONS (ecpH_pt G x0)
                                           (CONS (face_map G (edge_map G x0))
                                                 r3))))
                    (mask_list (CONS ck mk') (CONS x0 k))) (ecpH_pt G x0) <=>
          c1) /\
         (EX (adj (ecpH G x0) (ecpH_pt G x0))
            (APPEND (mask_list (CONS d0 (CONS d1 (CONS d2 mr0)))
                               (CONS (SND(new_dart2(dart G)))
                                     (CONS (ecpH_pt G x0)
                                           (CONS (face_map G (edge_map G x0))
                                                 r3))))
                    (mask_list (CONS dk mk0) (CONS x0 k))) <=>
          d0 \/ d2 \/ dk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FBAND_APPEND; EX_APPEND; FBAND_MASK_CONS; EX_MASK_CONS] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_APEX_ATOMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CFACE_REFL] THEN
  SUBGOAL_THEN
   `~cface (ecpH G x0) (ecpH_pt G x0) x0 /\
    ~cface (ecpH G x0) (ecpH_pt G x0) (face_map G (edge_map G x0)) /\
    ~fband (ecpH G x0) (mask_list mr' r3) (ecpH_pt G x0) /\
    ~fband (ecpH G x0) (mask_list mk' k) (ecpH_pt G x0) /\
    ~EX (adj (ecpH G x0) (ecpH_pt G x0)) (mask_list mr0 r3) /\
    ~EX (adj (ecpH G x0) (ecpH_pt G x0)) (mask_list mk0 k)`
   (fun th -> REWRITE_TAC[th] THEN CONV_TAC TAUT) THEN
  REWRITE_TAC[FBAND_MEM_IFF; GSYM EX_MEM] THEN
  ASM_MESON_TAC[MEM_MASK_LIST; PERMUTES_IN_IMAGE]);;

let ECPH_APEX_NOT_FBAND_OLD = prove
 (`!(G:(num)hypermap) x0 p.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\ (!z. MEM z p ==> z IN dart G)
     ==> ~fband (ecpH G x0) p (ecpH_pt G x0)`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[CFACE_ECPH_APEX_OLD]);;

let ECPH_SETUP = prove
 (`!(G:(num)hypermap) x0 k.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\ long_cpring G x0 /\
     (!z. MEM z k ==> z IN dart G) /\ face_simple G (APPEND (cpring G x0) k)
     ==> ?r3. cpring G x0 =
              CONS (node_map G x0)
                   (CONS x0 (CONS (face_map G (edge_map G x0)) r3)) /\
              cpring (ecpH G x0) (ecpH_pt G x0) =
              CONS (SND(new_dart2(dart G)))
                   (CONS (ecpH_pt G x0)
                         (CONS (face_map G (edge_map G x0)) r3)) /\
              (!z. MEM z r3
                   ==> z IN dart G /\ ~cface G z (node_map G x0) /\
                       ~cface G z x0 /\
                       ~cface G z (face_map G (edge_map G x0))) /\
              (!z. MEM z k
                   ==> z IN dart G /\ ~cface G z (node_map G x0) /\
                       ~cface G z x0 /\
                       ~cface G z (face_map G (edge_map G x0)))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `TL(TL(TL(cpring (G:(num)hypermap) x0)))` THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CPRING_ECPH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] NODE_ECPY_PT_VALUE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_LONG_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r3 = TL(TL(TL(cpring (G:(num)hypermap) x0)))` THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN `!z:num. MEM z r3 ==> z IN dart G` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MEM_CPRING_IN_DART THEN
      EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[th; MEM]; ALL_TAC] THEN
    SUBST_ALL_TAC th THEN REWRITE_TAC[th]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[TL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `face_simple G (APPEND (CONS (node_map G x0) (CONS x0
      (CONS (face_map G (edge_map G x0)) r3))) (k:(num)list))` THEN
  REWRITE_TAC[APPEND; face_simple] THEN STRIP_TAC THEN CFACE_TAC[]);;

let FBAND_ICPH_TRANSFER = prove
 (`!(G:(num)hypermap) x0 u.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     proper_cpring G x0 /\ u IN dart(ecpH G x0)
     ==> (?x. x IN dart G /\
              (!l. fband (ecpH G x0) l u <=> fband (ecpH G x0) l x) /\
              (!w. cface (ecpH G x0) u w <=> cface (ecpH G x0) x w) /\
              (!l. EX (adj (ecpH G x0) u) l <=> EX (adj (ecpH G x0) x) l)) \/
         (!l. fband (ecpH G x0) l u <=>
              fband (ecpH G x0) l (ecpH_pt G x0)) /\
         (!w. cface (ecpH G x0) u w <=>
              cface (ecpH G x0) (ecpH_pt G x0) w) /\
         (!l. EX (adj (ecpH G x0) u) l <=>
              EX (adj (ecpH G x0) (ecpH_pt G x0)) l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`] FBAND_ICPH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)
                              ASSUME_TAC) THENL
   [DISJ1_TAC THEN EXISTS_TAC `x:num`; DISJ2_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[FBAND_CFACE_CONG_ELT; CFACE_TRANS; EX_ADJ_CFACE_CONG]);;

let CPMASK_ADJ_STEP_R = prove
 (`!(G:(num)hypermap) r k n mr mk mr' mk' u.
     LENGTH mr = LENGTH r /\ LENGTH mr' = LENGTH r /\
     (fband G (APPEND (mask_list mr' r) (mask_list mk' k)) u <=>
      EX (adj G u) (APPEND (mask_list (rotr_list n mr) r) (mask_list mk k)))
     ==> (fband G (APPEND (mask_list (rot_list n mr') (rot_list n r))
                          (mask_list mk' k)) u <=>
          EX (adj G u) (APPEND (mask_list mr (rot_list n r))
                               (mask_list mk k)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`n:num`; `mr':(bool)list`; `r:(num)list`] MASK_LIST_ROT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`n:num`; `mr:(bool)list`; `r:(num)list`]
                MEM_MASK_LIST_ROT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[FBAND_MEM_IFF; GSYM EX_MEM; MEM_APPEND; MEM_ROT_LIST] THEN
  ASM_REWRITE_TAC[]);;

let CPMASK_ADJ_STEP_Y = prove
 (`!(G:(num)hypermap) x0 k b0 b1 b2 a0 a2 mr0 mr' mk mk'.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     plain_hypermap G /\ proper_cpring G x0 /\
     (!z. MEM z k ==> z IN dart G) /\
     face_simple G (APPEND (cpring G x0) k) /\
     (!x. x IN dart G
          ==> (fband G (APPEND (mask_list (CONS a0 (CONS a2 mr'))
                                          (cpring G x0))
                               (mask_list mk' k)) x <=>
               EX (adj G x) (APPEND (mask_list (CONS b0 (CONS b2 mr0))
                                               (cpring G x0))
                                    (mask_list mk k))))
     ==> !u. u IN dart(ecpY G x0)
             ==> (fband (ecpY G x0)
                    (APPEND (mask_list (CONS (a0 \/ b1)
                                         (CONS (b0 \/ b2)
                                           (CONS (a2 \/ b1) mr')))
                                       (cpring (ecpY G x0) (ecpY_pt G x0)))
                            (mask_list mk' k)) u <=>
                  EX (adj (ecpY G x0) u)
                     (APPEND (mask_list (CONS b0 (CONS b1 (CONS b2 mr0)))
                                        (cpring (ecpY G x0) (ecpY_pt G x0)))
                             (mask_list mk k)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast(CONJUNCTS th)) THEN
                       MP_TAC(last(CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `k:(num)list`] ECPY_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(num)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(fun ih -> X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
                  FBAND_ICPY_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (X_CHOOSE_THEN `x:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th])))
      (fun th -> REWRITE_TAC[th])) THENL
     [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`; `r2:(num)list`;
                     `k:(num)list`; `a0 \/ b1`; `b0 \/ b2`; `a2 \/ b1`;
                     `mr':(bool)list`; `mk':(bool)list`; `b0:bool`;
                     `b1:bool`; `b2:bool`; `mr0:(bool)list`; `mk:(bool)list`]
                    ECPY_OLD_CASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      MP_TAC(SPEC `x:num` ih) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FBAND_APPEND; EX_APPEND; FBAND_MASK_CONS; EX_MASK_CONS] THEN
      CONV_TAC TAUT;
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `r2:(num)list`;
                     `k:(num)list`; `a0 \/ b1`; `b0 \/ b2`; `a2 \/ b1`;
                     `mr':(bool)list`; `mk':(bool)list`; `b0:bool`;
                     `b1:bool`; `b2:bool`; `mr0:(bool)list`; `mk:(bool)list`]
                    ECPY_APEX_CASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[]]));;

let CPMASK_ADJ_STEP_H = prove
 (`!(G:(num)hypermap) x0 k b0 b1 b2 b1' a0 a1 a2 mr0 mr' mk0 mk'.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     plain_hypermap G /\ proper_cpring G x0 /\ long_cpring G x0 /\
     (!z. MEM z k ==> z IN dart G) /\
     face_simple G (APPEND (cpring G x0) k) /\
     (!x. x IN dart G
          ==> (fband G (APPEND (mask_list (CONS a0 (CONS a1 (CONS a2 mr')))
                                          (cpring G x0))
                               (mask_list mk' k)) x <=>
               EX (adj G x)
                  (APPEND (mask_list (CONS b0 (CONS b1' (CONS b2 mr0)))
                                     (cpring G x0))
                          (mask_list mk0 k))))
     ==> !u. u IN dart(ecpH G x0)
             ==> (fband (ecpH G x0)
                    (APPEND (mask_list (CONS (a0 \/ b1)
                                         (CONS (b0 \/ b1' \/ b2)
                                           (CONS (a2 \/ b1) mr')))
                                       (cpring (ecpH G x0) (ecpH_pt G x0)))
                            (mask_list (CONS (a1 \/ b1) mk')
                                       (CONS x0 k))) u <=>
                  EX (adj (ecpH G x0) u)
                     (APPEND (mask_list (CONS b0 (CONS b1 (CONS b2 mr0)))
                                        (cpring (ecpH G x0) (ecpH_pt G x0)))
                             (mask_list (CONS b1' mk0) (CONS x0 k))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast(CONJUNCTS th)) THEN
                       MP_TAC(last(CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `k:(num)list`] ECPH_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:(num)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(fun ih -> X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
                  FBAND_ICPH_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (X_CHOOSE_THEN `x:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th])))
      (fun th -> REWRITE_TAC[th])) THENL
     [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`; `r3:(num)list`;
                     `k:(num)list`; `a0 \/ b1`; `b0 \/ b1' \/ b2`; `a2 \/ b1`;
                     `mr':(bool)list`; `a1 \/ b1`; `mk':(bool)list`;
                     `b0:bool`; `b1:bool`; `b2:bool`; `mr0:(bool)list`;
                     `b1':bool`; `mk0:(bool)list`] ECPH_OLD_CASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      MP_TAC(SPEC `x:num` ih) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FBAND_APPEND; EX_APPEND; FBAND_MASK_CONS; EX_MASK_CONS] THEN
      CONV_TAC TAUT;
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `r3:(num)list`;
                     `k:(num)list`; `a0 \/ b1`; `b0 \/ b1' \/ b2`; `a2 \/ b1`;
                     `mr':(bool)list`; `a1 \/ b1`; `mk':(bool)list`;
                     `b0:bool`; `b1:bool`; `b2:bool`; `mr0:(bool)list`;
                     `b1':bool`; `mk0:(bool)list`] ECPH_APEX_CASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      CONV_TAC TAUT]));;

let CTRBAND_STEP_R = prove
 (`!(G:(num)hypermap) r k n mr mk E u.
     LENGTH mr = LENGTH r /\
     (fband G E u <=> fband G (APPEND (mask_list mr r) (mask_list mk k)) u)
     ==> (fband G E u <=>
          fband G (APPEND (mask_list (rot_list n mr) (rot_list n r))
                          (mask_list mk k)) u)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `mr:(bool)list`; `r:(num)list`] MASK_LIST_ROT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FBAND_APPEND; FBAND_ROT]);;

let CTRBAND_STEP_Y = prove
 (`!(G:(num)hypermap) x0 k L b1 cm' a0 a1 mr2 mk.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     plain_hypermap G /\ proper_cpring G x0 /\
     (!z. MEM z k ==> z IN dart G) /\ (!z. MEM z L ==> z IN dart G) /\
     face_simple G (APPEND (cpring G x0) k) /\
     (!x. x IN dart G
          ==> (fband G (insertE G (mask_list cm' L)) x <=>
               fband G (APPEND (mask_list (CONS a0 (CONS a1 mr2))
                                          (cpring G x0))
                               (mask_list mk k)) x))
     ==> !u. u IN dart(ecpY G x0)
             ==> (fband (ecpY G x0)
                    (insertE (ecpY G x0)
                       (mask_list (CONS b1 cm')
                                  (CONS (node_map G x0) L))) u <=>
                  fband (ecpY G x0)
                    (APPEND (mask_list (CONS (b1 \/ a0)
                                         (CONS F (CONS (b1 \/ a1) mr2)))
                                       (cpring (ecpY G x0) (ecpY_pt G x0)))
                            (mask_list mk k)) u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast(CONJUNCTS th)) THEN
                       MP_TAC(last(CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `k:(num)list`] ECPY_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(num)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!z:num. MEM z (mask_list (CONS b1 cm') (CONS (node_map G x0) L))
            ==> z IN dart G`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_MASK_LIST; MEM; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `insertE (ecpY G x0) (mask_list (CONS b1 cm') (CONS (node_map G x0) L)) =
    insertE G (mask_list (CONS b1 cm') (CONS (node_map G x0) L))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INSERTE_OLD_EQ THEN ASM_MESON_TAC[EDGE_ECPY_OLD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:num. MEM z (insertE G (mask_list (CONS b1 cm')
                                        (CONS (node_map G x0) L)))
            ==> z IN dart G`
  ASSUME_TAC THENL [ASM_MESON_TAC[INSERTE_IN_DART]; ALL_TAC] THEN
  DISCH_THEN(fun ih -> X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
                  FBAND_ICPY_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (X_CHOOSE_THEN `x:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th])))
      (fun th -> REWRITE_TAC[th])) THENL
     [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
        `insertE (G:(num)hypermap) (mask_list (CONS (b1:bool) cm')
                                      (CONS (node_map G x0) (L:(num)list)))`]
        ECPY_OLD_LISTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`; `r2:(num)list`;
                     `k:(num)list`; `b1 \/ a0`; `F`; `b1 \/ a1`;
                     `mr2:(bool)list`; `mk:(bool)list`; `F`; `F`; `F`;
                     `mr2:(bool)list`; `mk:(bool)list`] ECPY_OLD_CASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      REWRITE_TAC[FBAND_INSERTE_MASK_CONS] THEN
      SUBGOAL_THEN `cface (G:(num)hypermap) x (edge_map G (node_map G x0)) <=>
        cface G x x0`
        (fun th -> REWRITE_TAC[th]) THENL [CFACE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `x:num` ih) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FBAND_APPEND; FBAND_MASK_CONS] THEN CONV_TAC TAUT;
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `r2:(num)list`;
                     `k:(num)list`; `b1 \/ a0`; `F`; `b1 \/ a1`;
                     `mr2:(bool)list`; `mk:(bool)list`; `F`; `F`; `F`;
                     `mr2:(bool)list`; `mk:(bool)list`] ECPY_APEX_CASE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
      MATCH_MP_TAC ECPY_APEX_NOT_FBAND_OLD THEN ASM_REWRITE_TAC[]]));;

let CTRBAND_STEP_H = prove
 (`!(G:(num)hypermap) x0 k L b1 b0 b2 cm' a0 a1 a2 mr3 mk.
     x0 IN dart G /\ FINITE(dart G) /\ edge_map G permutes dart G /\
     node_map G permutes dart G /\ face_map G permutes dart G /\
     plain_hypermap G /\ proper_cpring G x0 /\ long_cpring G x0 /\
     (!z. MEM z k ==> z IN dart G) /\ (!z. MEM z L ==> z IN dart G) /\
     face_simple G (APPEND (cpring G x0) k) /\
     (!x. x IN dart G
          ==> (fband G (insertE G (mask_list cm' L)) x <=>
               fband G (APPEND (mask_list (CONS a0 (CONS a1 (CONS a2 mr3)))
                                          (cpring G x0))
                               (mask_list mk k)) x))
     ==> !u. u IN dart(ecpH G x0)
             ==> (fband (ecpH G x0)
                    (insertE (ecpH G x0)
                       (mask_list (CONS b1 (CONS b0 (CONS b2 cm')))
                          (CONS (face_map (ecpH G x0) (ecpH_pt G x0))
                                (CONS (node_map G x0) (CONS x0 L))))) u <=>
                  fband (ecpH G x0)
                    (APPEND (mask_list (CONS (b0 \/ a0)
                                         (CONS b1 (CONS (b2 \/ a2) mr3)))
                                       (cpring (ecpH G x0) (ecpH_pt G x0)))
                            (mask_list (CONS (b0 \/ b1 \/ b2 \/ a1) mk)
                                       (CONS x0 k))) u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast(CONJUNCTS th)) THEN
                       MP_TAC(last(CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `k:(num)list`] ECPH_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:(num)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] FACE_ECPH_PT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `node_map G (x0:num) IN dart G /\
    !z:num. MEM z (mask_list cm' L) ==> z IN dart G`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_MASK_LIST; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `insertE (ecpH G x0) (mask_list cm' L) = insertE G (mask_list cm' L) /\
    edge_map (ecpH G x0) (node_map G x0) = edge_map G (node_map G x0) /\
    edge_map (ecpH G x0) x0 = edge_map G x0 /\
    edge_map (ecpH G x0) (ecpY_pt G x0) = SND(new_dart2(dart(ecpU G x0))) /\
    (!z:num. MEM z (insertE G (mask_list cm' L)) ==> z IN dart G)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INSERTE_OLD_EQ THEN ASM_MESON_TAC[EDGE_ECPH_OLD];
      ASM_MESON_TAC[EDGE_ECPH_OLD]; ASM_MESON_TAC[EDGE_ECPH_OLD];
      ASM_MESON_TAC[EDGE_ECPH_ECPYPT]; ASM_MESON_TAC[INSERTE_IN_DART]];
    ALL_TAC] THEN
  DISCH_THEN(fun ih -> X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    REWRITE_TAC[FBAND_INSERTE_MASK_CONS] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `u:num`]
                  FBAND_ICPH_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (X_CHOOSE_THEN `x:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th])))
      (fun th -> REWRITE_TAC[th])) THENL
     [MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`;
                     `insertE (G:(num)hypermap)
                              (mask_list (cm':(bool)list) (L:(num)list))`]
                    ECPH_OLD_LISTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`; `r3:(num)list`;
                     `k:(num)list`; `b0 \/ a0`; `b1:bool`; `b2 \/ a2`;
                     `mr3:(bool)list`; `b0 \/ b1 \/ b2 \/ a1`; `mk:(bool)list`;
                     `F`; `F`; `F`; `mr3:(bool)list`; `F`; `mk:(bool)list`]
                    ECPH_OLD_CASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `x:num`] ECPH_OLD_ATOMS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `x:num` ih) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FBAND_APPEND; FBAND_MASK_CONS] THEN CONV_TAC TAUT;
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`; `r3:(num)list`;
                     `k:(num)list`; `b0 \/ a0`; `b1:bool`; `b2 \/ a2`;
                     `mr3:(bool)list`; `b0 \/ b1 \/ b2 \/ a1`; `mk:(bool)list`;
                     `F`; `F`; `F`; `mr3:(bool)list`; `F`; `mk:(bool)list`]
                    ECPH_APEX_CASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] ECPH_APEX_ATOMS) THEN
      MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`;
                     `insertE (G:(num)hypermap)
                              (mask_list (cm':(bool)list) (L:(num)list))`]
                    ECPH_APEX_NOT_FBAND_OLD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[]]));;

let CFACE_CPMAP0 = prove
 (`!x y. cface cpmap0 x y <=> y = x`,
  REWRITE_TAC[cface; face; CPMAP0_COMPONENTS; ORBIT_MAP_ITER; IN_ELIM_THM;
              ITER_I'] THEN
  MESON_TAC[]);;

let ADJ_CPMAP0 = prove
 (`!x y. adj cpmap0 x y <=> y = swap(0,1) x`,
  REWRITE_TAC[adj; rlink; GSYM cface; CFACE_CPMAP0; CPMAP0_COMPONENTS] THEN
  MESON_TAC[]);;

let CPADJ_CONS_Y_EQ = prove
 (`!cp b0 b1 b2 mr0 mk a0 a2 mr'.
     FST(cpadj (CONS b0 (CONS b2 mr0),mk) cp) = CONS a0 (CONS a2 mr')
     ==> cpadj (CONS b0 (CONS b1 (CONS b2 mr0)),mk) (CONS CpY cp) =
         (CONS (a0 \/ b1) (CONS (b0 \/ b2) (CONS (a2 \/ b1) mr')),
          SND(cpadj (CONS b0 (CONS b2 mr0),mk) cp))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cpadj] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[HD; TL]);;

let CPADJ_CONS_H_EQ = prove
 (`!cp b0 b1 b2 mr0 b1' mk0 a0 a1 a2 mr'.
     FST(cpadj (CONS b0 (CONS b1' (CONS b2 mr0)),mk0) cp) =
     CONS a0 (CONS a1 (CONS a2 mr'))
     ==> cpadj (CONS b0 (CONS b1 (CONS b2 mr0)),CONS b1' mk0) (CONS CpH cp) =
         (CONS (a0 \/ b1) (CONS (b0 \/ b1' \/ b2) (CONS (a2 \/ b1) mr')),
          CONS (a1 \/ b1)
               (SND(cpadj (CONS b0 (CONS b1' (CONS b2 mr0)),mk0) cp)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cpadj] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[HD; TL; APPEND; NOT_CONS_NIL]);;

let CTRBAND_CONS_Y_EQ = prove
 (`!t b1 cm' a0 a1 mr2.
     ~(t = []) /\ FST(ctrband cm' t) = CONS a0 (CONS a1 mr2)
     ==> ctrband (CONS b1 cm') (CONS CpY t) =
         (CONS (b1 \/ a0) (CONS F (CONS (b1 \/ a1) mr2)),SND(ctrband cm' t))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ctrband] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[HD; TL; LENGTH; ARITH_RULE `2 <= SUC(SUC n)`]);;

let CTRBAND_CONS_H_EQ = prove
 (`!t b1 b0 b2 cm' a0 a1 a2 mr3.
     FST(ctrband cm' t) = CONS a0 (CONS a1 (CONS a2 mr3))
     ==> ctrband (CONS b1 (CONS b0 (CONS b2 cm'))) (CONS CpH t) =
         (CONS (b0 \/ a0) (CONS b1 (CONS (b2 \/ a2) mr3)),
          CONS (b0 \/ b1 \/ b2 \/ a1) (SND(ctrband cm' t)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ctrband] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[HD; TL; LENGTH; ARITH_RULE `3 <= SUC(SUC(SUC n))`]);;

let cpmask_adj_ok = new_definition
 `cpmask_adj_ok (cp:(cpstep)list) <=>
    !cm. proper_cpmask cp cm
         ==> proper_cpmask cp (cpadj cm cp) /\
             (!u. u IN dart(FST(cpmap cp))
                  ==> (fband (FST(cpmap cp)) (cpmask (cpadj cm cp) cp) u <=>
                       EX (adj (FST(cpmap cp)) u) (cpmask cm cp)))`;;

let ctrband_ok = new_definition
 `ctrband_ok (cp:(cpstep)list) <=>
    !cm. LENGTH cm = ctrmsize cp
         ==> proper_cpmask cp (ctrband cm cp) /\
             (!x. x IN dart(FST(cpmap cp))
                  ==> (fband (FST(cpmap cp))
                         (insertE (FST(cpmap cp)) (mask_list cm (ctrenum cp)))
                         x <=>
                       fband (FST(cpmap cp)) (cpmask (ctrband cm cp) cp) x))`;;

let CPMASK_ADJ_CASE_R = prove
 (`!cp n. config_prog cp /\ cpmask_adj_ok cp
          ==> cpmask_adj_ok (CONS (CpR n) cp)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[cpmask_adj_ok; FORALL_PAIR_THM; proper_cpmask; CPRSIZE_CONS_R;
              CPKSIZE_CLAUSES] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`mr:(bool)list`; `mk:(bool)list`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rotr_list n (mr:(bool)list)`;
                                `mk:(bool)list`]) THEN
  ASM_REWRITE_TAC[LENGTH_ROTR_LIST] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  REWRITE_TAC[cpadj; LENGTH_ROT_LIST; CPMAP_CONS_R; ecpR; cpmask; cpker] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`FST(cpmap cp)`; `SND(cpmap cp)`; `n:num`]
                CPRING_ECPR_ROT_GEN) THEN
  ASM_REWRITE_TAC[ecpR] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `u:num` THEN DISCH_TAC THEN MATCH_MP_TAC CPMASK_ADJ_STEP_R THEN
  ASM_REWRITE_TAC[GSYM cprsize] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:num`) THEN ASM_REWRITE_TAC[cpmask]);;

let CPMASK_ADJ_CASE_Y = prove
 (`!cp. (cp = [] \/ config_prog cp) /\ cpmask_adj_ok cp
        ==> cpmask_adj_ok (CONS CpY cp)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[cpmask_adj_ok; FORALL_PAIR_THM; proper_cpmask; CPRSIZE_CONS_Y;
              CPKSIZE_CLAUSES] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`mr:(bool)list`; `mk:(bool)list`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `mr:(bool)list` LIST_LENGTH_GE_3) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:bool` (X_CHOOSE_THEN `b1:bool`
   (X_CHOOSE_THEN `b2:bool` (X_CHOOSE_THEN `mr0:(bool)list`
      SUBST_ALL_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (b0:bool) (CONS b2 mr0)`;
                                `mk:(bool)list`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN REWRITE_TAC[LENGTH] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `FST(cpadj (CONS (b0:bool) (CONS b2 mr0),mk:(bool)list) cp)`
               LIST_LENGTH_GE_2) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:bool` (X_CHOOSE_THEN `a2:bool`
   (X_CHOOSE_THEN `mr':(bool)list`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) THEN
  REWRITE_TAC[cpmask] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`; `b0:bool`; `b1:bool`; `b2:bool`;
                 `mr0:(bool)list`; `mk:(bool)list`; `a0:bool`; `a2:bool`;
                 `mr':(bool)list`] CPADJ_CONS_Y_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CPMAP_CONS_Y; cpmask; cpker; LENGTH] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CPMASK_ADJ_STEP_Y THEN ASM_REWRITE_TAC[]]);;

let CPMASK_ADJ_CASE_H = prove
 (`!cp. config_prog cp /\ cpmask_adj_ok cp ==> cpmask_adj_ok (CONS CpH cp)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[cpmask_adj_ok; FORALL_PAIR_THM; proper_cpmask; CPRSIZE_CONS_H;
               CPKSIZE_CLAUSES] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`mr:(bool)list`; `mk:(bool)list`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `mr:(bool)list` LIST_LENGTH_GE_3) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:bool` (X_CHOOSE_THEN `b1:bool`
   (X_CHOOSE_THEN `b2:bool` (X_CHOOSE_THEN `mr0:(bool)list`
      SUBST_ALL_TAC)))) THEN
  MP_TAC(ISPECL [`mk:(bool)list`; `cpksize cp`] LENGTH_NIL_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1':bool` (X_CHOOSE_THEN `mk0:(bool)list`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (b0:bool) (CONS b1' (CONS b2 mr0))`;
                                `mk0:(bool)list`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN REWRITE_TAC[LENGTH] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `FST(cpadj (CONS (b0:bool) (CONS b1' (CONS b2 mr0)),
                           mk0:(bool)list) cp)` LIST_LENGTH_GE_3) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:bool` (X_CHOOSE_THEN `a1:bool`
   (X_CHOOSE_THEN `a2:bool` (X_CHOOSE_THEN `mr':(bool)list`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th))))) THEN
  REWRITE_TAC[cpmask] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`; `b0:bool`; `b1:bool`; `b2:bool`;
                 `mr0:(bool)list`; `b1':bool`; `mk0:(bool)list`; `a0:bool`;
                 `a1:bool`; `a2:bool`; `mr':(bool)list`] CPADJ_CONS_H_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CPMAP_CONS_H; cpmask; cpker; LENGTH] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CPMASK_ADJ_STEP_H THEN ASM_REWRITE_TAC[]]);;

let CPMASK_ADJ_OK = prove
 (`!cp. (cp = [] \/ config_prog cp) ==> cpmask_adj_ok cp`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[cpmask_adj_ok; FORALL_PAIR_THM; proper_cpmask; CPRSIZE_NIL;
                CPKSIZE_CLAUSES; LENGTH_EQ_NIL] THEN
    MAP_EVERY X_GEN_TAC [`mr:(bool)list`; `mk:(bool)list`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP LIST_LENGTH_2)
                               SUBST1_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `b0:bool`
                (X_CHOOSE_THEN `b1:bool` SUBST1_TAC)) THEN
    REWRITE_TAC[CPMAP_NIL_PAIR; CPMAP0_COMPONENTS; IN_INSERT; NOT_IN_EMPTY;
                cpadj; cpmask; cpker; CPRING_CPMAP0; HD; TL; LENGTH] THEN
    REWRITE_TAC[FBAND_APPEND; EX_APPEND; FBAND_MASK_CONS; EX_MASK_CONS;
                MASK_LIST_CLAUSES; FBAND_NIL; EX; CFACE_CPMAP0;
                ADJ_CPMAP0] THEN
    CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[swap; ARITH_EQ] THEN
      CONV_TAC TAUT];
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[NOT_CONS_NIL; CONFIG_PROG_CONS_CASES] THEN
    MESON_TAC[CPMASK_ADJ_CASE_R; CPMASK_ADJ_CASE_Y; CPMASK_ADJ_CASE_H]]);;

let CPADJ_PROPER = prove
 (`!(cp:(cpstep)list) (cm:(bool)list#(bool)list).
     config_prog cp /\ proper_cpmask cp cm ==> proper_cpmask cp (cpadj cm cp)`,
  MESON_TAC[CPMASK_ADJ_OK; cpmask_adj_ok]);;

let MEM_CPMASK_IN_DART = prove
 (`!cp cm z.
     config_prog cp /\ MEM z (cpmask cm cp) ==> z IN dart(FST(cpmap cp))`,
  REWRITE_TAC[cpmask; MEM_APPEND] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[MEM_MASK_LIST; MEM_CPRING_IN_DART; CPMAP_PT_IN_DART];
    ASM_MESON_TAC[MEM_MASK_LIST; CPKER_IN_DART; config_prog]]);;

let CPMASK_ADJ = prove
 (`!(cp:(cpstep)list) (cm:(bool)list#(bool)list).
     config_prog cp /\ proper_cpmask cp cm
     ==> !x:num. (fband (FST(cpmap cp)) (cpmask (cpadj cm cp) cp) x <=>
                  EX (adj (FST(cpmap cp)) x) (cpmask cm cp))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x IN dart(FST(cpmap cp))` THENL
   [MP_TAC(ISPEC `cp:(cpstep)list` CPMASK_ADJ_OK) THEN
    ASM_REWRITE_TAC[cpmask_adj_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `cm:(bool)list#(bool)list`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:num` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[FBAND_OUT_DART; EX_ADJ_OUT_DART; MEM_CPMASK_IN_DART]]);;

let CTRBAND_CASE_R = prove
 (`!cp n. config_prog cp /\ ctrband_ok cp ==> ctrband_ok (CONS (CpR n) cp)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[ctrband_ok; ctrmsize; proper_cpmask; CPRSIZE_CONS_R;
              CPKSIZE_CLAUSES] THEN
  DISCH_TAC THEN X_GEN_TAC `cm:(bool)list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cm:(bool)list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ctrband; ctrenum; cpker; cpmask; CPMAP_CONS_R; ecpR;
              LENGTH_ROT_LIST] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`FST(cpmap cp)`; `SND(cpmap cp)`; `n:num`]
                CPRING_ECPR_ROT_GEN) THEN
  ASM_REWRITE_TAC[ecpR] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN MATCH_MP_TAC CTRBAND_STEP_R THEN
  ASM_REWRITE_TAC[GSYM cprsize] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[cpmask]);;

let CTRBAND_CASE_Y0 = prove
 (`ctrband_ok [CpY]`,
  REWRITE_TAC[ctrband_ok; ctrmsize; LENGTH_EQ_NIL] THEN GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ctrband; ctrenum; proper_cpmask; cpmask; cpker; LENGTH_REPLICATE;
              LENGTH; CPRSIZE_CONS_Y; CPRSIZE_NIL; CPKSIZE_CLAUSES;
              MASK_LIST_CLAUSES; MASK_LIST_REPLICATE_F; INSERTE_NIL; APPEND;
              FBAND_NIL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CTRBAND_CASE_Y = prove
 (`!cp. config_prog cp /\ ctrband_ok cp ==> ctrband_ok (CONS CpY cp)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(cp:(cpstep)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[config_prog]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ctrband_ok; ctrmsize] THEN DISCH_TAC THEN
  X_GEN_TAC `cm:(bool)list` THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:bool` (X_CHOOSE_THEN `cm':(bool)list`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) o MATCH_MP LENGTH_NIL_CASES) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cm':(bool)list`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[proper_cpmask] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `FST(ctrband cm' cp):(bool)list` LIST_LENGTH_GE_2) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:bool` (X_CHOOSE_THEN `a1:bool`
   (X_CHOOSE_THEN `mr2:(bool)list`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) THEN
  REWRITE_TAC[cpmask] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`; `b1:bool`; `cm':(bool)list`; `a0:bool`;
                 `a1:bool`; `mr2:(bool)list`] CTRBAND_CONS_Y_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[proper_cpmask; CPMAP_CONS_Y; ctrenum; cpker; cpmask;
                  CPRSIZE_CONS_Y; CPKSIZE_CLAUSES; LENGTH] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CTRBAND_STEP_Y THEN ASM_REWRITE_TAC[]]);;

let CTRBAND_CASE_H = prove
 (`!cp. config_prog cp /\ ctrband_ok cp ==> ctrband_ok (CONS CpH cp)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[ctrband_ok; ctrmsize] THEN DISCH_TAC THEN
  X_GEN_TAC `cm:(bool)list` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `cm:(bool)list` LIST_LENGTH_GE_3) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:bool` (X_CHOOSE_THEN `b0:bool`
   (X_CHOOSE_THEN `b2:bool` (X_CHOOSE_THEN `cm':(bool)list`
      SUBST_ALL_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cm':(bool)list`) THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[proper_cpmask] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `FST(ctrband cm' cp):(bool)list` LIST_LENGTH_GE_3) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:bool` (X_CHOOSE_THEN `a1:bool`
   (X_CHOOSE_THEN `a2:bool` (X_CHOOSE_THEN `mr3:(bool)list`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th))))) THEN
  REWRITE_TAC[cpmask] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`; `b1:bool`; `b0:bool`; `b2:bool`;
                 `cm':(bool)list`; `a0:bool`; `a1:bool`; `a2:bool`;
                 `mr3:(bool)list`] CTRBAND_CONS_H_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[proper_cpmask; CPMAP_CONS_H; ctrenum; cpker; cpmask;
               CPRSIZE_CONS_H; CPKSIZE_CLAUSES; LENGTH] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CTRBAND_STEP_H THEN ASM_REWRITE_TAC[]]);;

let CTRBAND_OK = prove
 (`!cp. config_prog cp ==> ctrband_ok cp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CONFIG_PROG_NIL] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONFIG_PROG_CONS_CASES] THEN
  MESON_TAC[CTRBAND_CASE_R; CTRBAND_CASE_Y0; CTRBAND_CASE_Y; CTRBAND_CASE_H]);;

let CTRBAND_CORRECT = prove
 (`!(cm:(bool)list) (cp:(cpstep)list).
     LENGTH cm = ctrmsize cp /\ config_prog cp
     ==> proper_cpmask cp (ctrband cm cp) /\
         (!x:num. fband (FST(cpmap cp)) (insertE (FST(cpmap cp)) (mask_list cm
           (ctrenum cp))) x <=>
                  fband (FST(cpmap cp)) (cpmask (ctrband cm cp) cp) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CTRBAND_OK) THEN
  ASM_REWRITE_TAC[ctrband_ok] THEN
  DISCH_THEN(MP_TAC o SPEC `cm:(bool)list`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) ASSUME_TAC) THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x IN dart(FST(cpmap cp))` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. MEM z (insertE (FST(cpmap cp)) (mask_list cm (ctrenum cp)))
        ==> z IN dart(FST(cpmap cp))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[INSERTE_IN_DART; MEM_MASK_LIST; MEM_CTRENUM_IN_DART];
    ASM_MESON_TAC[FBAND_OUT_DART; MEM_CPMASK_IN_DART]]);;

let LENGTH_MASK_PRED1_FROM = prove
 (`!n j i. LENGTH(mask_pred1_from j i n) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[mask_pred1_from; LENGTH]);;

let MASK_LIST_MASK_PRED1_FROM = prove
 (`!(l:A list) j i.
     mask_list (mask_pred1_from j i (LENGTH l)) l =
     if j <= i /\ i < j + LENGTH l then [EL (i - j) l] else []`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; mask_pred1_from; MASK_LIST_CLAUSES; ADD_CLAUSES] THENL
   [REWRITE_TAC[ARITH_RULE `~(j <= i /\ i < j)`]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `j:num = i` THENL
   [ASM_REWRITE_TAC[MASK_LIST_CONS_CONS; LE_REFL; SUB_REFL; EL; HD;
                    ARITH_RULE `i < SUC(i + n)`; ARITH_RULE `~(SUC i <= i)`];
    ASM_REWRITE_TAC[MASK_LIST_CONS_CONS] THEN
    SUBGOAL_THEN
     `(j <= i /\ i < SUC(j + LENGTH(t:A list))) <=>
      (SUC j <= i /\ i < SUC j + LENGTH t)`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `i - j = SUC(i - SUC j)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]]]);;

let MASK_LIST_MASK_PRED1 = prove
 (`!(l:A list) i n.
     LENGTH l = n /\ i < n ==> mask_list (mask_pred1 i n) l = [EL i l]`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[mask_pred1; MASK_LIST_MASK_PRED1_FROM; LE_0; ADD_CLAUSES;
                  SUB_0]);;

let PROPER_CPMASK1 = prove
 (`!(cp:(cpstep)list) i. proper_cpmask cp (cfmask1 cp i)`,
  REWRITE_TAC[proper_cpmask; cfmask1; LENGTH_REPLICATE; mask_pred1;
              LENGTH_MASK_PRED1_FROM]);;

let CPMASK1 = prove
 (`!(cp:(cpstep)list) i. i < cpksize cp /\ config_prog cp
        ==> cpmask (cfmask1 cp i) cp = [EL i (cpker cp)]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cpmask; cfmask1; MASK_LIST_REPLICATE_F; APPEND] THEN
  MATCH_MP_TAC MASK_LIST_MASK_PRED1 THEN ASM_SIMP_TAC[SIZE_CPKER]);;

(* ========================================================================= *)
(* The triad clause of valid_contract for a configuration contract (Gonthier *)
(* cfcontract.v, the cptriad check of valid_ctrm): a valid size-4 contract   *)
(* mask yields a kernel dart x whose face meets the contract band more than  *)
(* twice and which is not adjacent to every contract dart.  Steps:           *)
(*   MASK_LIST_SIMPLE_COUNT  bit counts of a doubly masked list over a face- *)
(*                           simple list are fband / adjacency counts;       *)
(*   CPTRIAD_WITNESS, CPTRIAD_COND_COUNTS  cptriad gives an index i with     *)
(*                           more than two band darts adjacent to            *)
(*                           EL i (cpker cp) and a band dart not adjacent;   *)
(*   CFCARD_BRIDGE           the adjacent band darts bound the face count of *)
(*                           the semantic triad (SIMPLE_FCARD_FBAND);        *)
(*   CP_TRIAD_EXTRACT        the cp-level witness, lifted to the             *)
(*                           configuration level inside CONTRACT_CTREEP.     *)
(* ========================================================================= *)

let FBAND_SUBLIST = prove
 (`!(H:(A)hypermap) l1 l2 d.
     (!z. MEM z l1 ==> MEM z l2) /\ fband H l1 d ==> fband H l2 d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[]);;

let MASK_LIST_SIMPLE_COUNT = prove
 (`!(H:(A)hypermap) q.
     face_simple H q /\ (!z. MEM z q ==> z IN dart H)
     ==> !mc mt. LENGTH mc = LENGTH q /\ LENGTH mt = LENGTH q
         ==> (EX (\b. ~b) (mask_list mc mt) <=>
              ?d. MEM d (mask_list mc q) /\ ~fband H (mask_list mt q) d) /\
             LENGTH (FILTER (\b. b) (mask_list mc mt)) =
             LENGTH (FILTER (fband H (mask_list mt q)) (mask_list mc q))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[mask_list; EX; MEM; FILTER; LENGTH];
    ALL_TAC] THEN
  REWRITE_TAC[face_simple; MEM; LENGTH] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`mc:(bool)list`; `mt:(bool)list`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`mc:(bool)list`; `LENGTH(t:(A)list)`] LENGTH_NIL_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:bool` (X_CHOOSE_THEN `mc':(bool)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL[`mt:(bool)list`; `LENGTH(t:(A)list)`] LENGTH_NIL_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b2:bool` (X_CHOOSE_THEN `mt':(bool)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_MESON_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL[`mc':(bool)list`; `mt':(bool)list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d:A. MEM d (mask_list mc' t) ==> ~cface H d h`
    ASSUME_TAC THENL
   [X_GEN_TAC `d:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (d:A) t` ASSUME_TAC THENL
     [ASM_MESON_TAC[MEM_MASK_LIST]; CFACE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `~fband (H:(A)hypermap) (mask_list mt' t) h` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL[`H:(A)hypermap`; `mask_list mt' (t:(A)list)`; `t:(A)list`;
                  `h:A`] FBAND_SUBLIST) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[MEM_MASK_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN
    `FILTER (fband (H:(A)hypermap) (CONS h (mask_list mt' t)))
            (mask_list mc' t) =
     FILTER (fband H (mask_list mt' t)) (mask_list mc' t)` ASSUME_TAC THENL
   [MATCH_MP_TAC FILTER_EQ_MEM THEN X_GEN_TAC `d:A` THEN DISCH_TAC THEN
    REWRITE_TAC[FBAND_CONS] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MASK_LIST_CONS_CONS] THEN
  ASM_CASES_TAC `b1:bool` THEN ASM_CASES_TAC `b2:bool` THEN
  ASM_REWRITE_TAC[EX; MEM; FILTER; LENGTH; FBAND_CONS; CFACE_REFL] THEN
  ASM_MESON_TAC[CFACE_REFL]);;

(* cptriad's per-index condition, abbreviating the mask-count test.          *)
let cptriad_cond = new_definition
 `cptriad_cond (ccm:(bool)list#(bool)list) (cp:(cpstep)list) i <=>
    EX (\b. ~b)
       (APPEND (mask_list (FST ccm) (FST(cpadj (cfmask1 cp i) cp)))
               (mask_list (SND ccm) (SND(cpadj (cfmask1 cp i) cp)))) /\
    2 < LENGTH(FILTER (\b. b)
                 (APPEND
                    (mask_list (FST ccm) (FST(cpadj (cfmask1 cp i) cp)))
                    (mask_list (SND ccm) (SND(cpadj (cfmask1 cp i) cp)))))`;;

let CPTRIAD_REC_COND = prove
 (`!ccm cp i. cptriad ccm cp (SUC i) =
              (if cptriad_cond ccm cp i then T else cptriad ccm cp i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cptriad] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[cptriad_cond]);;

(* cptriad true => some index i<n satisfies the condition.                   *)
let CPTRIAD_WITNESS = prove
 (`!ccm cp n. cptriad ccm cp n ==> ?i. i < n /\ cptriad_cond ccm cp i`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[cptriad];
    REWRITE_TAC[CPTRIAD_REC_COND] THEN COND_CASES_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `?i. i < n /\ cptriad_cond ccm cp i` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]]);;

(* The condition at index i, read on the contract band cpmask (ctrband cm    *)
(* cp) cp: more than two band darts are adjacent to x = EL i (cpker cp) and  *)
(* at least one band dart is not adjacent to x.  CPMASK_ADJ turns the mask   *)
(* cpadj (cfmask1 cp i) cp into adjacency to x, and MASK_LIST_SIMPLE_COUNT   *)
(* over the face-simple ring ++ kernel turns the bit counts of the doubly    *)
(* masked list into counts over the band.                                    *)
let CPTRIAD_COND_COUNTS = prove
 (`!cp cm i.
     config_prog cp /\ LENGTH cm = ctrmsize cp /\ i < cpksize cp /\
     cptriad_cond (ctrband cm cp) cp i
     ==> 2 < LENGTH(FILTER (\d. adj (FST(cpmap cp)) d (EL i (cpker cp)))
                           (cpmask (ctrband cm cp) cp)) /\
         (?d. MEM d (cpmask (ctrband cm cp) cp) /\
              ~adj (FST(cpmap cp)) d (EL i (cpker cp)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cubic_prog cp` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONFIG_PROG_CUBIC]; ALL_TAC] THEN
  MP_TAC(ISPECL[`cm:(bool)list`;`cp:(cpstep)list`] CTRBAND_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `proper_cpmask cp (cpadj (cfmask1 cp i) cp)` ASSUME_TAC THENL
   [MATCH_MP_TAC CPADJ_PROPER THEN ASM_REWRITE_TAC[PROPER_CPMASK1];
    ALL_TAC] THEN
  SUBGOAL_THEN `cpmask (cfmask1 cp i) cp = [EL i (cpker cp)]` ASSUME_TAC THENL
   [MATCH_MP_TAC CPMASK1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `fband (FST(cpmap cp)) (cpmask (cpadj (cfmask1 cp i) cp) cp) =
    (\d. adj (FST(cpmap cp)) d (EL i (cpker cp)))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    MP_TAC(ISPECL[`cp:(cpstep)list`; `cfmask1 cp i`] CPMASK_ADJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[PROPER_CPMASK1]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[EX; MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(FST(ctrband cm cp):(bool)list) =
    LENGTH(cpring (FST(cpmap cp)) (SND(cpmap cp))) /\
    LENGTH(SND(ctrband cm cp):(bool)list) = LENGTH(cpker cp) /\
    LENGTH(FST(cpadj (cfmask1 cp i) cp):(bool)list) =
    LENGTH(cpring (FST(cpmap cp)) (SND(cpmap cp))) /\
    LENGTH(SND(cpadj (cfmask1 cp i) cp):(bool)list) = LENGTH(cpker cp)`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[proper_cpmask]) THEN
    ASM_SIMP_TAC[SIZE_CPKER; GSYM cprsize]; ALL_TAC] THEN
  SUBGOAL_THEN
   `face_simple (FST(cpmap cp))
      (APPEND (cpring (FST(cpmap cp)) (SND(cpmap cp))) (cpker cp)) /\
    (!z. MEM z (APPEND (cpring (FST(cpmap cp)) (SND(cpmap cp))) (cpker cp))
         ==> z IN dart (FST(cpmap cp)))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[CPMAP_SIMPLE];
      REWRITE_TAC[MEM_APPEND] THEN X_GEN_TAC `z:num` THEN STRIP_TAC THENL
       [MATCH_MP_TAC MEM_CPRING_IN_DART THEN EXISTS_TAC `SND(cpmap cp)` THEN
        ASM_REWRITE_TAC[CPMAP_PT_IN_DART];
        MP_TAC(ISPEC `cp:(cpstep)list` CPKER_IN_DART) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC[config_prog; CONFIG_PROG_CONS]; ALL_TAC] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mask_list (APPEND (FST(ctrband cm cp):(bool)list) (SND(ctrband cm cp)))
              (APPEND (cpring (FST(cpmap cp)) (SND(cpmap cp))) (cpker cp)) =
    cpmask (ctrband cm cp) cp /\
    mask_list (APPEND (FST(cpadj (cfmask1 cp i) cp):(bool)list)
                      (SND(cpadj (cfmask1 cp i) cp)))
              (APPEND (cpring (FST(cpmap cp)) (SND(cpmap cp))) (cpker cp)) =
    cpmask (cpadj (cfmask1 cp i) cp) cp`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cpmask] THEN CONJ_TAC THEN
    MATCH_MP_TAC MASK_LIST_APPEND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `APPEND (mask_list (FST(ctrband cm cp):(bool)list)
                      (FST(cpadj(cfmask1 cp i) cp)))
           (mask_list (SND(ctrband cm cp))(SND(cpadj(cfmask1 cp i) cp))) =
    mask_list (APPEND (FST(ctrband cm cp):(bool)list)(SND(ctrband cm cp)))
              (APPEND (FST(cpadj(cfmask1 cp i) cp):(bool)list)
                      (SND(cpadj(cfmask1 cp i) cp)))`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MASK_LIST_APPEND THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL[`FST(cpmap cp)`;
                `APPEND (cpring (FST(cpmap cp)) (SND(cpmap cp))) (cpker cp)`]
         MASK_LIST_SIMPLE_COUNT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`APPEND (FST(ctrband cm cp):(bool)list) (SND(ctrband cm cp))`;
     `APPEND (FST(cpadj (cfmask1 cp i) cp):(bool)list)
             (SND(cpadj (cfmask1 cp i) cp))`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cptriad_cond (ctrband cm cp) cp i` THEN
  ASM_REWRITE_TAC[cptriad_cond] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LT_REFL; LTE_TRANS]; ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* From "2 < #{contract-band darts adjacent to x}" (CPTRIAD_COND_COUNTS) to  *)
(* the semantic triad's face-orbit count "2 < #{y in face x : band(edge y)}" *)
(* (the first conjunct of TRIAD_LIST).  Pure hypermap geometry.              *)
(* ------------------------------------------------------------------------- *)

let FBAND_IN_DART_MEM = prove
 (`!(H:(A)hypermap) l z.
     (!y. MEM y l ==> y IN dart H) /\ fband H l z ==> z IN dart H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FBAND_MEM_IFF] THEN STRIP_TAC THEN
  CFACE_TAC[]);;

let FBAND_FILTER_ADJ_SET = prove
 (`!(H:(A)hypermap) r cc x.
     plain_hypermap H /\ x IN dart H /\
     (!d. MEM d r ==> d IN dart H) /\
     (!d. fband H r d <=> fband H (insertE H cc) d)
     ==> (!z. z IN dart H
              ==> (fband H (FILTER (\d. adj H d x) r) z <=>
                   adj H z x /\ fband H (insertE H cc) z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `fband H (insertE H cc) (z:A) <=> fband H r z`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FBAND_MEM_IFF; MEM_FILTER] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[ADJ_CFACE_L];
      EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ADJ_CFACE_L]]);;

let CFCARD_BRIDGE = prove
 (`!(H:(A)hypermap) r cc x.
     plain_hypermap H /\ x IN dart H /\ face_simple H r /\
     (!d. MEM d r ==> d IN dart H) /\
     (!d. fband H r d <=> fband H (insertE H cc) d)
     ==> LENGTH (FILTER (\d. adj H d x) r) <=
         LENGTH (FILTER (\y. fband H (insertE H cc) (edge_map H y))
                        (orbit_list (face_map H) x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `FILTER (\d:A. adj H d x) r`]
    SIMPLE_FCARD_FBAND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_SIMPLE_FILTER]];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `\y:A. fband H (insertE H cc) (edge_map H y)`;
                `x:A`] ORBIT_FILTER_CARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE] THEN
  SUBGOAL_THEN
    `FINITE {z:A | z IN face H x /\ fband H (insertE H cc) (edge_map H z)}`
    ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `dart (H:(A)hypermap)` THEN
    REWRITE_TAC[FINITE_DART; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[FACE_IN_DART];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `CARD (IMAGE (\y:A. orbit_map (face_map H) (edge_map H y))
                 {z:A | z IN face H x /\
                        fband H (insertE H cc) (edge_map H z)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CARD_IMAGE_LE THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `oo:A->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  POP_ASSUM(ASSUME_TAC o REWRITE_RULE[IN]) THEN
  SUBGOAL_THEN `(w:A) IN dart H` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`H:(A)hypermap`; `FILTER (\d:A. adj H d x) r`; `w:A`]
      FBAND_IN_DART_MEM) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[MEM_FILTER] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
      DISCH_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `cc:(A)list`; `x:A`]
    FBAND_FILTER_ADJ_SET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `adj (H:(A)hypermap) w x` THEN REWRITE_TAC[adj; rlink] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:A) IN dart H /\ edge_map H (edge_map H z) = z`
  STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `edge_map H (z:A)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM face] THEN ASM_MESON_TAC[FACE_EQ];
    CFACE_TAC[]; CFACE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The cp-level triad extraction: a valid size-4 ctr-mask yields a kernel    *)
(* dart whose face meets the contract band more than twice and that is not   *)
(* adjacent to all contract darts.  Pieces: band simplicity / in-dart (mask  *)
(* of the simple cpring++cpker), kernel-off-ring, valid_ctrm -> cptriad,     *)
(* CPTRIAD_WITNESS, CPTRIAD_COND_COUNTS, CFCARD_BRIDGE, CTRBAND_CORRECT.     *)
(* ------------------------------------------------------------------------- *)

(* A mask (subsequence) of a face-simple list is face-simple.                *)
let FACE_SIMPLE_MASK_LIST = prove
 (`!(H:(A)hypermap) m s. face_simple H s ==> face_simple H (mask_list m s)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[mask_list; face_simple];
    GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `s:(A)list` list_CASES) THEN
    REWRITE_TAC[mask_list; face_simple; HD; TL; NOT_CONS_NIL;
                COND_CLAUSES] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[face_simple] THEN
    ASM_MESON_TAC[FBAND_SUBLIST; MEM_MASK_LIST]]);;

(* The contract band cpmask ccm cp is face-simple (it is a mask of the       *)
(* simple cpring ++ cpker; cross-face condition inherited via                *)
(* MEM_MASK_LIST).                                                           *)
let BAND_FACE_SIMPLE = prove
 (`!cp ccm. config_prog cp
            ==> face_simple (FST(cpmap cp)) (cpmask ccm cp)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cpmask] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FACE_SIMPLE_APPEND'] o
    MATCH_MP CPMAP_SIMPLE) THEN
  REWRITE_TAC[FACE_SIMPLE_APPEND'] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FACE_SIMPLE_MASK_LIST THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FACE_SIMPLE_MASK_LIST THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MEM_MASK_LIST; FBAND_SUBLIST]]);;

(* The i-th kernel dart is in the carrier and off the ring's face-band.      *)
let CPKER_EL_PROPS = prove
 (`!cp i. config_prog cp /\ i < cpksize cp
          ==> EL i (cpker cp) IN dart (FST(cpmap cp)) /\
              ~fband (FST(cpmap cp)) (cpring (FST(cpmap cp)) (SND(cpmap cp)))
                     (EL i (cpker cp))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (EL i (cpker cp)) (cpker cp)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEM_EL THEN ASM_MESON_TAC[SIZE_CPKER]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL config_step cp` ASSUME_TAC THENL
   [ASM_MESON_TAC[config_prog]; ALL_TAC] THEN
  SUBGOAL_THEN `EL i (cpker cp) IN dart (FST(cpmap cp))` ASSUME_TAC THENL
   [ASM_MESON_TAC[CPKER_IN_DART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FACE_SIMPLE_APPEND'] o
              MATCH_MP CPMAP_SIMPLE) THEN
  REWRITE_TAC[FBAND_MEM_IFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fband (FST(cpmap cp)) (cpker cp) y` MP_TAC THENL
   [REWRITE_TAC[FBAND_MEM_IFF] THEN EXISTS_TAC `EL i (cpker cp)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CFACE_SYM_GEN THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* A valid ctr-mask with exactly four selected columns forces cptriad.       *)
let VALID_CTRM_CPTRIAD = prove
 (`!cp cm. valid_ctrm cm cp /\ LENGTH (FILTER (\b. b) cm) = 4
           ==> cptriad (ctrband cm cp) cp (cpksize cp)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_ctrm] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* The cp-level triad extraction.                                            *)
let CP_TRIAD_EXTRACT = prove
 (`!cp cm. config_prog cp /\ LENGTH cm = ctrmsize cp /\
           LENGTH (FILTER (\b. b) cm) = 4 /\ valid_ctrm cm cp
           ==> ?x. ~fband (FST(cpmap cp))
                          (cpring (FST(cpmap cp)) (SND(cpmap cp))) x /\
                   x IN dart (FST(cpmap cp)) /\
                   triad (FST(cpmap cp))
                         (insertE (FST(cpmap cp)) (mask_list cm (ctrenum cp)))
                         x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `plain_hypermap (FST(cpmap cp))` ASSUME_TAC THENL
   [ASM_MESON_TAC[CPMAP_PLAIN; CONFIG_PROG_CUBIC]; ALL_TAC] THEN
  MP_TAC(ISPECL[`cm:(bool)list`;`cp:(cpstep)list`] CTRBAND_CORRECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
  MP_TAC(ISPECL[`cp:(cpstep)list`;`cm:(bool)list`] VALID_CTRM_CPTRIAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CPTRIAD_WITNESS) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL[`cp:(cpstep)list`;`cm:(bool)list`;`i:num`]
    CPTRIAD_COND_COUNTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL[`cp:(cpstep)list`;`i:num`] CPKER_EL_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  EXISTS_TAC `EL i (cpker cp)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[TRIAD_LIST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `LENGTH(FILTER (\d. adj (FST(cpmap cp)) d (EL i (cpker cp)))
                                (cpmask (ctrband cm cp) cp))` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MP_TAC(ISPECL[`FST(cpmap cp)`; `cpmask (ctrband cm cp) cp`;
                      `mask_list cm (ctrenum cp)`; `EL i (cpker cp)`]
          CFCARD_BRIDGE) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
            ASM_MESON_TAC[BAND_FACE_SIMPLE]; ASM_MESON_TAC[MEM_CPMASK_IN_DART];
            GEN_TAC THEN ASM_MESON_TAC[]];
          DISCH_THEN ACCEPT_TAC]];
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
        `fband (FST(cpmap cp))
           (insertE (FST(cpmap cp)) (mask_list cm (ctrenum cp))) d`
        MP_TAC THENL
       [ASM_MESON_TAC[FBAND_MEM]; ALL_TAC] THEN
      REWRITE_TAC[FBAND_MEM_IFF] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `d IN dart (FST(cpmap cp))` ASSUME_TAC THENL
       [ASM_MESON_TAC[MEM_CPMASK_IN_DART]; ALL_TAC] THEN
      SUBGOAL_THEN `z IN dart (FST(cpmap cp))` ASSUME_TAC THENL
       [CFACE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~adj (FST(cpmap cp)) z (EL i (cpker cp))` ASSUME_TAC THENL
       [ASM_MESON_TAC[ADJ_CFACE_L]; ALL_TAC] THEN
      ASM_MESON_TAC[ADJ_SYM]]]);;

(* ------------------------------------------------------------------------- *)
(* CONTRACT_CTREEP (Gonthier cfcontract.v contract_ctreeP): a successful     *)
(* contract_ctree gives the whole valid_contract record of the configuration *)
(* contract -- off the ring and sparse (VALID_CFCTR_CC), size 1..4 and the   *)
(* triad clause -- and its ctree contains the traces of all contract         *)
(* colourings (CFCTR_CORRECT, CTREE_MEM_CPCOLOR_GEN).  contract_ctree cf =   *)
(* SOME ct forces config_prog (cfctr_ok) and valid_ctrm (cfcontract_mask cf) *)
(* (cfprog cf); with cfmap cf = cpmap (cfprog cf) and cfcontract cf =        *)
(* mask_list (cfcontract_mask cf) (ctrenum (cfprog cf)) this lifts           *)
(* CP_TRIAD_EXTRACT to the triad clause (the kernel of cfring = REVERSE      *)
(* cpring, by FBAND_REVERSE).                                                *)
(* ------------------------------------------------------------------------- *)

let CONTRACT_CTREEP = prove
 (`!cf:(cpstep)list#(num)list.
     (!ct. contract_ctree cf = SOME ct
           ==> valid_contract (FST(cfmap cf)) (cfring cf) (cfcontract cf) /\
               (!et. cc_ring_trace (FST(cfmap cf)) (cfcontract cf)
                        (rot_list 1 (cpring (FST(cfmap cf)) (SND(cfmap cf))))
                          et
                     ==> ctree_mem ct (etrace (TL et))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[contract_ctree; cfmap; cfcontract; cfcontract_mask; cfprog;
              cfring; cfcontract_ref; cfctr] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `cp = FST(cf:(cpstep)list#(num)list)` THEN
  ABBREV_TAC `cm = ctrmask cp (SND(cf:(cpstep)list#(num)list))` THEN
  ABBREV_TAC `G = FST(cpmap (cp:(cpstep)list))` THEN
  ABBREV_TAC `p0 = SND(cpmap (cp:(cpstep)list))` THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `cpc = cfctr_map (REPLICATE (cprsize cp) F) cm cp` THEN
  SUBGOAL_THEN `config_prog (cp:(cpstep)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CFCTR_CONFIG_PROG]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (cm:bool list) = ctrmsize cp` ASSUME_TAC THENL
   [EXPAND_TAC "cm" THEN REWRITE_TAC[SIZE_CTRMASK]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`; `cm:bool list`] VALID_CFCTR_CC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[valid_contract; MEM_REVERSE] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH (mask_list cm (ctrenum cp)) =
                  LENGTH (FILTER (\b. b) (cm:bool list))` SUBST1_TAC THENL
     [MATCH_MP_TAC LENGTH_MASK_LIST_EQ THEN ASM_REWRITE_TAC[SIZE_CTRENUM];
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= LENGTH (FILTER (\b. b) (cm:bool list)) /\
                  LENGTH (FILTER (\b. b) (cm:bool list)) <= 4`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `valid_ctrm cm cp` THEN REWRITE_TAC[valid_ctrm] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THENL
       [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
        ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`cp:(cpstep)list`; `cm:bool list`] CP_TRIAD_EXTRACT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_KERNEL; FBAND_REVERSE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `et:color list` THEN REWRITE_TAC[cc_ring_trace] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num->color`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    MP_TAC(ISPEC `cp:(cpstep)list` CFCTR_CORRECT) THEN
    REWRITE_TAC[ctr_correct] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`REPLICATE (cprsize cp) F`; `cm:bool list`; `k:num->color`]) THEN
    ASM_REWRITE_TAC[LENGTH_REPLICATE; MASK_LIST_REPLICATE_F; APPEND;
                    MAP_NOT_REPLICATE_F] THEN
    SUBGOAL_THEN `mask_list (REPLICATE (cprsize cp) T) (cpring G p0) =
                  cpring G p0` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["G"; "p0"] THEN
      REWRITE_TAC[cprsize; MASK_LIST_REPLICATE_T]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k':num->color` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`cpc:(cpstep)list`;
      `etrace (TL (trace_col (MAP (k:num->color) (rot_list 1 (cpring G
        p0)))))`]
      CTREE_MEM_CPCOLOR_GEN) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "cpc" THEN REWRITE_TAC[CFCTR_MAP_NO_CPRR];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[EVEN_ETRACE; GSYM ctrace; ring_trace] THEN
    ABBREV_TAC
      `et = trace_col (MAP (k:num->color) (rot_list 1 (cpring G p0)))` THEN
    SUBGOAL_THEN `ctrace (TL (et:color list)) = et` ASSUME_TAC THENL
     [MATCH_MP_TAC CTRACE_BEHEAD_ZEROSUM THEN EXPAND_TAC "et" THEN
      REWRITE_TAC[SUMT_TRACE] THEN MATCH_MP_TAC TRACE_COL_NONEMPTY THEN
      REWRITE_TAC[MAP_EQ_NIL] THEN MATCH_MP_TAC ROT_LIST_NONEMPTY THEN
      MAP_EVERY EXPAND_TAC ["G"; "p0"] THEN MATCH_MP_TAC CPRING_NONEMPTY THEN
      REWRITE_TAC[CPMAP_PT_IN_DART]; ALL_TAC] THEN
    REWRITE_TAC[etrace; CTRACE_PERMT] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC
      `permc (etrace_perm (TL (et:color list))) o (k':num->color)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC COLORING_PERMC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MAP_o] THEN REWRITE_TAC[GSYM PERMT_MAP; TRACE_PERMT;
      MAP_ROT_LIST] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MAP_ROT_LIST] THEN
    ASM_REWRITE_TAC[]]);;
