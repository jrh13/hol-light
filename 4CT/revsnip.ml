(* ========================================================================= *)
(* 4CT/revsnip.ml                                                            *)
(*                                                                           *)
(* revsnip.v, first part: proper rings and the reversed ring.  proper_ring   *)
(* (a ring that is not a bare edge orbit [x; edge x]), rev_ring r = REVERSE  *)
(* (MAP edge r) with its cycle, simplicity and face-band lemmas              *)
(* (CYCLE_REV_RING, SCYCLE_REV_RING, FBAND_REV_RING), connectivity by clink  *)
(* paths (CLINK_CONNECTED, Coq connected_clink), the disk of the reversed    *)
(* ring (DISKN_EDGE_RING, DISKN_REV_RING, DISKF_REV_RING), the face count    *)
(* fcard_face of a set and nontrivial_ring.  The last part of revsnip.v is   *)
(* in revsnip_tail.ml.                                                       *)
(* ========================================================================= *)

needs "4CT/snip.ml";;
needs "4CT/preembedding.ml";;

(* proper_ring r: a non-empty ring that is not a bare edge orbit [x; edge    *)
(* x], following Gonthier's list match (length >= 3: true; [x; y]: edge x <> *)
(* y; otherwise false).                                                      *)
let proper_ring = new_definition
  `proper_ring (H:(A)hypermap) r <=>
     (?x y z t. r = CONS x (CONS y (CONS z t))) \/
     (?x y. r = [x; y] /\ ~(edge_map H x = y))`;;

let SIZE_PROPER_RING = prove
 (`!(H:(A)hypermap) r. 2 < LENGTH r ==> proper_ring H r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[proper_ring] THEN DISJ1_TAC THEN
  MATCH_MP_TAC LEN3 THEN ASM_REWRITE_TAC[]);;

(* Structural clauses for proper_ring.                                       *)
let PROPER_NIL = prove
 (`!H:(A)hypermap. proper_ring H [] <=> F`,
  REWRITE_TAC[proper_ring] THEN MESON_TAC[NOT_CONS_NIL]);;

let PROPER_ONE = prove
 (`!(H:(A)hypermap) x. proper_ring H [x] <=> F`,
  REWRITE_TAC[proper_ring] THEN MESON_TAC[NOT_CONS_NIL; CONS_11]);;

let PROPER_TWO = prove
 (`!(H:(A)hypermap) x y. proper_ring H [x;y] <=> ~(edge_map H x = y)`,
  REWRITE_TAC[proper_ring; CONS_11; NOT_CONS_NIL] THEN MESON_TAC[]);;

let NOT_PROPER_RING = prove
 (`!(H:(A)hypermap) r.
     ~proper_ring H r <=>
     r = [] \/ (?x. r = [x]) \/ (?x. r = [x; edge_map H x])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[proper_ring] THEN
  STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `t':(A)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* The reversed ring rev_ring r = REVERSE (MAP edge r), the ring seen from   *)
(* the other side (Coq RevSnip section).                                     *)
(* ========================================================================= *)

let rev_ring = new_definition
  `rev_ring (H:(A)hypermap) r = REVERSE (MAP (edge_map H) r)`;;

let MAP_EDGE_INVOL = prove
 (`!(H:(A)hypermap) l.
     plain_hypermap H ==> MAP (edge_map H) (MAP (edge_map H) l) = l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP] THEN
  SIMP_TAC[CFT_PLAIN_EE]);;

let REV_REV_RING = prove
 (`!(H:(A)hypermap) r. plain_hypermap H ==> rev_ring H (rev_ring H r) = r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rev_ring] THEN
  REWRITE_TAC[GSYM MAP_REVERSE; REVERSE_REVERSE] THEN
  ASM_SIMP_TAC[MAP_EDGE_INVOL]);;

let MEM_REV_RING = prove
 (`!(H:(A)hypermap) r x.
     plain_hypermap H ==> (MEM x (rev_ring H r) <=> MEM (edge_map H x) r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rev_ring; MEM_REVERSE; MEM_MAP] THEN
  ASM_MESON_TAC[CFT_PLAIN_EE]);;

(* Same case-analysis shape as proper_ring_rot; rev_ring [x;y] = [e y; e x]. *)
let PROPER_REV_RING = prove
 (`!(H:(A)hypermap) r.
     plain_hypermap H ==> (proper_ring H (rev_ring H r) <=> proper_ring H r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THENL
   [REWRITE_TAC[rev_ring; MAP; REVERSE]; ALL_TAC] THEN
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THEN REPEAT DISCH_TAC THENL
   [REWRITE_TAC[rev_ring; MAP; REVERSE; APPEND; PROPER_ONE]; ALL_TAC] THEN
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `t':(A)list` list_CASES) THEN REPEAT DISCH_TAC THENL
   [REWRITE_TAC[rev_ring; MAP; REVERSE; APPEND; PROPER_TWO] THEN
    ASM_MESON_TAC[CFT_PLAIN_EE];
    EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIZE_PROPER_RING THEN
    REWRITE_TAC[rev_ring; LENGTH_REVERSE; LENGTH_MAP; LENGTH] THEN
    ARITH_TAC]);;

(* Splitting a path after a snoc boundary, keeping the folded APPEND R [a]   *)
(* intact so that an induction hypothesis stated on that shape can still     *)
(* fire.                                                                     *)
let LIST_PATH_SNOC_CONS = prove
 (`!e (R:(A)list) a q x.
     list_path e x (APPEND (APPEND R [a]) q) <=>
     list_path e x (APPEND R [a]) /\ list_path e a q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_PATH_APPEND; LAST_CONS_SNOC] THEN
  CONV_TAC TAUT);;

(* Path reversal: a rel-chain from y to x along APPEND p [x] is the same as  *)
(* a rel'-chain from f x to f y along the reversed mapped list, whenever     *)
(* rel' (f b) (f a) <=> rel a b (converse transport along f).                *)
let REV_CHAIN = prove
 (`!(rel:A->A->bool) (rel':B->B->bool) (f:A->B).
     (!a b. rel' (f b) (f a) <=> rel a b)
     ==> !p x y. list_path rel' (f x) (APPEND (REVERSE (MAP f p)) [f y]) <=>
                 list_path rel y (APPEND p [x])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THENL
   [ASM_REWRITE_TAC[MAP; REVERSE; APPEND; list_path]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; REVERSE] THEN
  REWRITE_TAC[LIST_PATH_SNOC_CONS] THEN
  ASM_REWRITE_TAC[APPEND; list_path] THEN
  CONV_TAC TAUT);;

(* cycle in rot1 form: cycle (h::t) <=> path h (t ++ [h]).                   *)
let LIST_CYCLE_CONS_PATH = prove
 (`!rel h (t:(A)list).
     list_cycle rel (CONS h t) <=> list_path rel h (APPEND t [h])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[list_cycle; NOT_CONS_NIL; LIST_PATH_APPEND; list_path] THEN
  ASM_CASES_TAC `t:(A)list = []` THEN
  ASM_REWRITE_TAC[LAST; NOT_CONS_NIL; list_path; APPEND] THEN
  CONV_TAC TAUT);;

(* Generic cycle reversal: converse-transport along f flips REVERSE(MAP f    *)
(* l).                                                                       *)
let LIST_CYCLE_REV_MAP = prove
 (`!(rel:A->A->bool) (rel':B->B->bool) (f:A->B).
     (!a b. rel' (f b) (f a) <=> rel a b)
     ==> !l. list_cycle rel' (REVERSE (MAP f l)) <=> list_cycle rel l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THENL
   [REWRITE_TAC[MAP; REVERSE; list_cycle]; ALL_TAC] THEN
  REWRITE_TAC[MAP; REVERSE; LIST_CYCLE_CONS_PATH] THEN
  REWRITE_TAC[list_cycle; APPEND_EQ_NIL; NOT_CONS_NIL; LAST_SNOC'] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REV_CHAIN th]));;

(* rlink converse-transports along edge on plain maps.                       *)
let RLINK_EDGE_SWAP = prove
 (`!(H:(A)hypermap) a b.
     plain_hypermap H ==>
     (rlink H (edge_map H b) (edge_map H a) <=> rlink H a b)`,
  REPEAT STRIP_TAC THEN CFACE_TAC[]);;

(* Coq cycle_rev_ring, as a biconditional.                                   *)
let CYCLE_REV_RING = prove
 (`!(H:(A)hypermap) r.
     plain_hypermap H
     ==> (list_cycle (rlink H) (rev_ring H r) <=> list_cycle (rlink H) r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rev_ring] THEN
  MP_TAC(ISPECL [`rlink (H:(A)hypermap)`; `rlink (H:(A)hypermap)`;
                `edge_map (H:(A)hypermap)`] LIST_CYCLE_REV_MAP) THEN
  ANTS_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RLINK_EDGE_SWAP THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* Every member of a cycle has a successor/predecessor in the cycle.         *)
let SUCC_IN_SNOC_PATH = prove
 (`!rel (t:(A)list) x0 z w.
     list_path rel x0 (APPEND t [z]) /\ (w = x0 \/ MEM w t)
     ==> ?y. (MEM y t \/ y = z) /\ rel w y`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; list_path; MEM] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[APPEND; list_path; MEM] THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `h:A` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let PRED_IN_SNOC_PATH = prove
 (`!rel (t:(A)list) x0 z v.
     list_path rel x0 (APPEND t [z]) /\ (MEM v t \/ v = z)
     ==> ?u. (u = x0 \/ MEM u t) /\ rel u v`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; list_path; MEM] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[APPEND; list_path; MEM] THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let CYCLE_MEM_SUCC = prove
 (`!rel (l:(A)list) x. list_cycle rel l /\ MEM x l ==> ?y. MEM y l /\ rel x y`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THEN
  REWRITE_TAC[list_cycle; NOT_CONS_NIL; MEM; LIST_CYCLE_CONS_PATH] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rel:A->A->bool`; `t:(A)list`; `h:A`; `h:A`; `x:A`]
    SUCC_IN_SNOC_PATH) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CYCLE_MEM_PRED = prove
 (`!rel (l:(A)list) y. list_cycle rel l /\ MEM y l ==> ?x. MEM x l /\ rel x y`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THEN
  REWRITE_TAC[list_cycle; NOT_CONS_NIL; MEM; LIST_CYCLE_CONS_PATH] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rel:A->A->bool`; `t:(A)list`; `h:A`; `h:A`; `y:A`]
    PRED_IN_SNOC_PATH) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* fband / face_simple layer of RevSnip.                                     *)
(* ------------------------------------------------------------------------- *)

(* fband (rev_ring r) = fband r for an rlink cycle (Coq fband_rev_ring).     *)
let FBAND_REV_RING = prove
 (`!(H:(A)hypermap) r z.
     plain_hypermap H /\ list_cycle (rlink H) r
     ==> (fband H (rev_ring H r) z <=> fband H r z)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FBAND_MEM_IFF; MEM_REV_RING] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`rlink (H:(A)hypermap)`; `r:(A)list`; `edge_map H w:A`]
      CYCLE_MEM_SUCC);
    MP_TAC(ISPECL [`rlink (H:(A)hypermap)`; `r:(A)list`; `w:A`]
      CYCLE_MEM_PRED)] THEN
  ASM_SIMP_TAC[rlink; CFT_PLAIN_EE] THEN
  ASM_MESON_TAC[CFT_TRANS; CFACE_SYM_GEN; CFT_PLAIN_EE]);;

(* fband congruences: in the tested element, and elementwise in the list.    *)
let FBAND_CFACE_CONG_ELT = prove
 (`!(H:(A)hypermap) l z z'. cface H z z' ==> (fband H l z <=> fband H l z')`,
  REPEAT STRIP_TAC THEN CFACE_TAC[]);;

let FBAND_ALL2_CONG = prove
 (`!(H:(A)hypermap) l m.
     ALL2 (cface H) l m ==> !z. fband H l z <=> fband H m z`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `m:(A)list` list_CASES) THEN
    REWRITE_TAC[ALL2; FBAND_NIL];
    ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `m:(A)list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC[FBAND_CONS] THEN BINOP_TAC THENL
   [CFACE_TAC[]; ASM_MESON_TAC[]]);;

(* face_simple congruence along elementwise cface.                           *)
let FACE_SIMPLE_CFACE_CONG = prove
 (`!(H:(A)hypermap) l m.
     ALL2 (cface H) l m ==> (face_simple H l <=> face_simple H m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `m:(A)list` list_CASES) THEN
    REWRITE_TAC[ALL2];
    ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `m:(A)list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN STRIP_TAC THEN
  REWRITE_TAC[face_simple] THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN
    SUBGOAL_THEN `!z:A. fband (H:(A)hypermap) t z <=> fband H t' z`
      (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC FBAND_ALL2_CONG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC FBAND_CFACE_CONG_ELT THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* face_simple over APPEND.                                                  *)
let FACE_SIMPLE_APPEND' = prove
 (`!(H:(A)hypermap) p q.
     face_simple H (APPEND p q) <=>
     face_simple H p /\ face_simple H q /\ (!x. MEM x p ==> ~fband H q x)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; face_simple; MEM]; ALL_TAC] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[APPEND; face_simple; MEM; FBAND_APPEND] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* face_simple is invariant under the rot1 shift and under reversal.         *)
let FACE_SIMPLE_ROT1 = prove
 (`!(H:(A)hypermap) h t.
     face_simple H (APPEND t [h]) <=> face_simple H (CONS h t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FACE_SIMPLE_APPEND'; face_simple; FBAND_NIL; FBAND_CONS;
              FBAND_MEM_IFF] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CFACE_SYM_GEN]);;

let FBAND_REVERSE = prove
 (`!(H:(A)hypermap) l z. fband H (REVERSE l) z <=> fband H l z`,
  REWRITE_TAC[FBAND_MEM_IFF; MEM_REVERSE]);;

let FACE_SIMPLE_REVERSE = prove
 (`!(H:(A)hypermap) l. face_simple H (REVERSE l) <=> face_simple H l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE; face_simple] THEN
  REWRITE_TAC[FACE_SIMPLE_ROT1; face_simple] THEN
  ASM_REWRITE_TAC[FBAND_REVERSE]);;

(* Along an rlink path from x0, each edge is cofacial with the next dart.    *)
let ALL2_CFACE_FROM_PATH = prove
 (`!(H:(A)hypermap) t x0 z.
     list_path (rlink H) x0 (APPEND t [z])
     ==> ALL2 (cface H) (MAP (edge_map H) (CONS x0 t)) (APPEND t [z])`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; list_path; MAP; ALL2; rlink] THEN SIMP_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[APPEND; list_path] THEN
    ONCE_REWRITE_TAC[MAP] THEN REWRITE_TAC[ALL2] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[rlink];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Coq simple_rev_ring, as a biconditional needing only the cycle.           *)
let SIMPLE_REV_RING = prove
 (`!(H:(A)hypermap) r.
     list_cycle (rlink H) r
     ==> (face_simple H (rev_ring H r) <=> face_simple H r)`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THENL
   [REWRITE_TAC[list_cycle]; ALL_TAC] THEN
  REWRITE_TAC[LIST_CYCLE_CONS_PATH] THEN DISCH_TAC THEN
  REWRITE_TAC[rev_ring; FACE_SIMPLE_REVERSE] THEN
  SUBGOAL_THEN
    `face_simple (H:(A)hypermap) (MAP (edge_map H) (CONS h t)) <=>
     face_simple H (APPEND t [h])` SUBST1_TAC THENL
   [MATCH_MP_TAC FACE_SIMPLE_CFACE_CONG THEN
    MATCH_MP_TAC ALL2_CFACE_FROM_PATH THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FACE_SIMPLE_ROT1]]);;

(* Coq scycle_rev_ring: the reversed ring of an rlink scycle is one too.     *)
let SCYCLE_REV_RING = prove
 (`!(H:(A)hypermap) r.
     plain_hypermap H /\ scycle H (rlink H) r ==>
     scycle H (rlink H) (rev_ring H r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[scycle] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CYCLE_REV_RING]; ASM_MESON_TAC[SIMPLE_REV_RING]]);;

(* ========================================================================= *)
(* Connectivity by clink paths: in a connected hypermap any two darts are    *)
(* joined by a clink path (CLINK_CONNECTED, Coq connected_clink).            *)
(* ========================================================================= *)

(* Orbit periodicity: after orbit_size - 1 more steps, f x returns to x.     *)
let ITER_RETURN = prove
 (`!(H:(A)hypermap) f x. f permutes dart H /\ x IN dart H
     ==> ?k. ITER k f (f x) = x`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `orbit_size (f:A->A) x - 1` THEN
  REWRITE_TAC[ITER_SHIFT] THEN
  SUBGOAL_THEN `SUC (orbit_size (f:A->A) x - 1) = orbit_size f x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`f:A->A`; `dart(H:(A)hypermap)`; `x:A`] ORBIT_SIZE_POS) THEN
    ASM_REWRITE_TAC[FINITE_DART] THEN ARITH_TAC;
    MATCH_MP_TAC ITER_ORBIT_SIZE THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART]]);;

(* One glink step gives a clink path.  Face step: a clink step.  Node step:  *)
(* walk round the node orbit (CNODE_CLINK_PATH_ITER) to the return index.    *)
(* Edge step: the clink step x -> face (edge x) (by edgeK), then round the   *)
(* face orbit to edge x (CFACE_CLINK_PATH).                                  *)
let GLINK_CLINK_PATH = prove
 (`!(H:(A)hypermap) x y.
     x IN dart H /\ glink H x y
     ==> ?p. list_path (clink H) x p /\ LAST (CONS x p) = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glink] THEN STRIP_TAC THENL
   [SUBGOAL_THEN
     `cface (H:(A)hypermap) (face_map H (edge_map H x)) (edge_map H x)`
    MP_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CFACE_CLINK_PATH) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:(A)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `CONS (face_map (H:(A)hypermap) (edge_map H x)) m` THEN
    ASM_REWRITE_TAC[list_path; LAST; NOT_CONS_NIL] THEN
    REWRITE_TAC[clink] THEN DISJ1_TAC THEN REWRITE_TAC[edgeK];
    MP_TAC(ISPECL [`H:(A)hypermap`; `node_map (H:(A)hypermap)`; `x:A`]
      ITER_RETURN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NODE_MAP_PERMUTES]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `k:num`; `node_map (H:(A)hypermap) x`]
      CNODE_CLINK_PATH_ITER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:(A)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m:(A)list` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `[face_map (H:(A)hypermap) x]` THEN
    ASM_REWRITE_TAC[list_path; LAST; NOT_CONS_NIL; clink]]);;

(* The direction of Coq clink_glink used: a glink walk from a dart can be    *)
(* replaced by a clink path (induction along the walk, GCOMP_INDUCT).        *)
let GCOMP_CLINK_PATH = prove
 (`!(H:(A)hypermap) x y.
     x IN dart H /\ gcomp H x y
     ==> ?p. list_path (clink H) x p /\ LAST (CONS x p) = y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`y:A`,`y:A`) THEN
  SUBGOAL_THEN
   `!y. gcomp H x y
        ==> y IN dart H /\
            ?p. list_path (clink H) (x:A) p /\ LAST (CONS x p) = y`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC GCOMP_INDUCT THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `[]:(A)list` THEN
    REWRITE_TAC[list_path; LAST];
    MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `p:(A)list` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[GLINK_IN_DART]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `u:A`; `v:A`] GLINK_CLINK_PATH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `APPEND p q:(A)list` THEN
    ASM_REWRITE_TAC[LIST_PATH_APPEND; LAST_CONS_APPEND_GEN]]);;

(* Coq connected_clink.                                                      *)
let CLINK_CONNECTED = prove
 (`!(H:(A)hypermap) x y.
     connected_hypermap H /\ x IN dart H /\ y IN dart H
     ==> ?p. list_path (clink H) x p /\ LAST (CONS x p) = y`,
  REWRITE_TAC[connected_hypermap] THEN MESON_TAC[GCOMP_CLINK_PATH]);;

(* Rotation invariance in the form rot 1 (x :: p) = APPEND p [x] used by     *)
(* embed.v.                                                                  *)
let PROPER_RING_ROT1_CONS = prove
 (`!(H:(A)hypermap) x p.
     plain_hypermap H ==>
     (proper_ring H (APPEND p [x]) <=> proper_ring H (CONS x p))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p:(A)list` list_CASES) THENL
   [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THEN REPEAT DISCH_TAC THENL
   [REWRITE_TAC[APPEND; PROPER_TWO] THEN ASM_MESON_TAC[CFT_PLAIN_EE];
    EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIZE_PROPER_RING THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* DISKN_EDGE_RING (Coq diskN_edge_ring): for x on a proper scycle ring,     *)
(* edge x lies outside the disk.  If edge x were in the disk it would lie on *)
(* the ring (DISKN_E, DISKE_EDGE); then nextc r x = edge x and nextc r (edge *)
(* x) = x.  A ring [a; b] would have edge a = b, and on a longer ring the    *)
(* positions i and i + 2 (mod the length) of x would coincide (NEXTC_EL).    *)
(* ------------------------------------------------------------------------- *)

let MOD_SUCC_SUCC_NEQ = prove
 (`!n i. 3 <= n /\ i < n ==> ~(((i + 1) MOD n + 1) MOD n = i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `1`; `n:num`] MOD_SUC_STEP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `i + SUC 1 = i + 2`] THEN
  MATCH_MP_TAC MOD_ADD_NEQ THEN ASM_ARITH_TAC);;

let DISKN_EDGE_RING = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ plain_hypermap H /\ scycle H (rlink H) r /\
     ALL (\y. y IN dart H) r /\ proper_ring H r /\ MEM x r
     ==> ~diskN H r (edge_map H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_PAIRWISE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_CYCLE) THEN
  SUBGOAL_THEN `(x:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MEM_DART]; ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `MEM (edge_map H x:A) r` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_E; DISKE_EDGE; diskE; EDGE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `nextc r x = edge_map H x /\ nextc r (edge_map H x) = (x:A)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`rlink (H:(A)hypermap)`; `r:(A)list`; `x:A`]
        CYCLE_NEXTC_STEP);
      MP_TAC(ISPECL [`rlink (H:(A)hypermap)`; `r:(A)list`; `edge_map H x:A`]
        CYCLE_NEXTC_STEP)] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[rlink] THEN
    ASM_SIMP_TAC[CFT_PLAIN_EE] THEN ASM_MESON_TAC[SCYCLE_CFACE_EQ; NEXTC_MEM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I [proper_ring]) THENL
   [SUBGOAL_THEN `3 <= LENGTH(r:(A)list)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [MEM_EXISTS_EL] o
      check (fun th -> concl th = `MEM (x:A) r`)) THEN
    MP_TAC(ISPECL [`LENGTH(r:(A)list)`; `i:num`] MOD_SUCC_SUCC_NEQ) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EL_PAIRWISE_INJ THEN EXISTS_TAC `r:(A)list` THEN
    ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `3 <= n ==> ~(n = 0)`] THEN
    SUBGOAL_THEN `(i + 1) MOD LENGTH(r:(A)list) < LENGTH r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `3 <= n ==> ~(n = 0)`]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `x:A = EL i r`)) THEN
    MP_TAC(ISPECL [`r:(A)list`; `(i + 1) MOD LENGTH(r:(A)list)`] NEXTC_EL) THEN
    MP_TAC(ISPECL [`r:(A)list`; `i:num`] NEXTC_EL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MEM; ALL]) THEN
    ASM_MESON_TAC[PLAIN_EQ; PLAIN_NEQ]]);;

(* ------------------------------------------------------------------------- *)
(* rev_ring stays inside the dart carrier (plainness is not needed).         *)
(* ------------------------------------------------------------------------- *)
let REV_RING_DART = prove
 (`!(H:(A)hypermap) r.
     plain_hypermap H /\ ALL (\y. y IN dart H) r
     ==> ALL (\y. y IN dart H) (rev_ring H r)`,
  REWRITE_TAC[rev_ring; GSYM ALL_MEM; MEM_REVERSE; MEM_MAP] THEN
  MESON_TAC[EDGE_MAP_IN_DART]);;

(* A property holding at the end of a path and propagating backwards along   *)
(* each step holds at its start.                                             *)
let LIST_PATH_LAST_INDUCT = prove
 (`!(e:A->A->bool) P q x.
     (!a b. e a b /\ P b ==> P a) /\ list_path e x q /\ P (LAST (CONS x q))
     ==> P x`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_path; LAST_CLAUSES] THENL [MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `h:A` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* DISKN_REV_RING (Coq diskN_rev_ring): the reversed ring bounds exactly the *)
(* complementary disk.  The equivalence holds at edge y for y on the ring    *)
(* (DISKN_EDGE_RING) and propagates backwards along clink steps: node steps  *)
(* by DISKN_NODE_EQ for both rings; for a face step x -> z with edge x off   *)
(* the ring, both sides reduce through DISKE_EDGE to diskN at edge x = node  *)
(* z; with edge x on the ring, x is on the reversed ring and DISKN_EDGE_RING *)
(* applies.  Connectivity (CLINK_CONNECTED) gives a clink path to edge y.    *)
(* ------------------------------------------------------------------------- *)
let DISKN_REV_RING_STEP = prove
 (`!(H:(A)hypermap) r x z.
     planar_hypermap H /\ plain_hypermap H /\ scycle H (rlink H) r /\
     ALL (\z. z IN dart H) r /\ proper_ring H r /\
     x IN dart H /\ clink H x z /\
     (diskN H (rev_ring H r) z <=> ~diskN H r z)
     ==> (diskN H (rev_ring H r) x <=> ~diskN H r x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `scycle H (rlink H) (rev_ring H r) /\
    ALL (\z. z IN dart H) (rev_ring H r) /\ (z:A) IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SCYCLE_REV_RING; REV_RING_DART; CLINK_DART]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I [clink]) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[DISKN_NODE_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `MEM (edge_map H x:A) r` THENL
   [ASM_MESON_TAC[MEM_REV_RING; RING_IN_DISKN; DISKN_EDGE_RING; CFT_PLAIN_EE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(diskN H (rev_ring H r) (edge_map H x) <=> diskN H (rev_ring H r) z) /\
    (diskN H r (edge_map H x) <=> diskN H r (z:A))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `edge_map H x = node_map H (z:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[edgeK; CFT_PLAIN_EE]; ASM_SIMP_TAC[DISKN_NODE_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`] DISKE_EDGE) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rev_ring H r:(A)list`; `x:A`]
    DISKE_EDGE) THEN
  ASM_SIMP_TAC[DISKN_E] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[diskE; MEM_REV_RING; CFT_PLAIN_EE] THEN CONV_TAC TAUT);;

let DISKN_REV_RING = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ proper_ring H r /\
     x IN dart H
     ==> (diskN H (rev_ring H r) x <=> ~diskN H r x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?y:A. MEM y r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM; PROPER_NIL; list_CASES]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN dart H /\ edge_map H y IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MEM_DART; EDGE_MAP_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `edge_map H y:A`]
    CLINK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`clink (H:(A)hypermap)`;
    `\z:A. z IN dart H ==> (diskN H (rev_ring H r) z <=> ~diskN H r z)`;
    `q:(A)list`; `x:A`] LIST_PATH_LAST_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[DISKN_REV_RING_STEP; CLINK_DART];
    ASM_MESON_TAC[MEM_REV_RING; RING_IN_DISKN; DISKN_EDGE_RING;
                  CFT_PLAIN_EE]]);;

(* diskF of the reverse ring: the complementary face-free region.            *)
let DISKF_REV_RING = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ proper_ring H r /\
     x IN dart H
     ==> (diskF H (rev_ring H r) x <=> ~diskN H r x /\ ~fband H r x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diskF] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`] DISKN_REV_RING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`] FBAND_REV_RING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rlink (H:(A)hypermap)`; `r:(A)list`]
      SCYCLE_CYCLE) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* rev_ring of a snoc and of a rotated ring (Gonthier's rot 1 (x :: p) =     *)
(* APPEND p [x]).                                                            *)
(* ------------------------------------------------------------------------- *)
let REV_RING_ROT1_CONS = prove
 (`!(H:(A)hypermap) p x.
     rev_ring H (APPEND p [x]) = CONS (edge_map H x) (rev_ring H p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rev_ring; MAP_APPEND; MAP; REVERSE_APPEND; REVERSE; APPEND]);;

let SCYCLE_ROT1_CONS = prove
 (`!(H:(A)hypermap) e p x.
     scycle H e (APPEND p [x]) <=> scycle H e (CONS x p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[scycle; FACE_SIMPLE_ROT1] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[list_cycle; APPEND_EQ_NIL; NOT_CONS_NIL; LAST_SNOC'] THEN
  REWRITE_TAC[GSYM LIST_CYCLE_CONS_PATH] THEN
  REWRITE_TAC[list_cycle; NOT_CONS_NIL]);;

(* diskN only depends on the ring's MEMbership (dlink + the EX are           *)
(* MEM-based).                                                               *)
let DISKN_MEM_CONG = prove
 (`!(H:(A)hypermap) r r' x.
     (!z. MEM z r <=> MEM z r') ==> (diskN H r x <=> diskN H r' x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dlink (H:(A)hypermap) r = dlink H r'` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; dlink] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[diskN; dconnect; dreach; GSYM EX_MEM] THEN
  ASM_REWRITE_TAC[]);;

let DISKN_ROT1_CONS = prove
 (`!(H:(A)hypermap) p x z.
     diskN H (APPEND p [x]) z <=> diskN H (CONS x p) z`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DISKN_MEM_CONG THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* ------------------------------------------------------------------------- *)
(* The number of faces meeting a set: fcard_face H s = CARD (set_of_orbits s *)
(* (face_map H)), the number of distinct face orbits meeting s, which is     *)
(* Coq's fcard face A for a face-closed set.                                 *)
(* ------------------------------------------------------------------------- *)
(* ========================================================================= *)

let fcard_face = new_definition
 `fcard_face (H:(A)hypermap) (s:A->bool) =
  CARD(set_of_orbits s (face_map H))`;;

(* Coq fcard0P: for a (face-closed) set -- here just FINITE s suffices       *)
let FCARD0P = prove
 (`!(H:(A)hypermap) s. FINITE s ==> (0 < fcard_face H s <=> ?x. x IN s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE; LT_NZ] THEN
  ASM_SIMP_TAC[CARD_EQ_0; FINITE_IMAGE] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; MEMBER_NOT_EMPTY]);;

(* Coq fcard1P: needs s SUBSET dart H so ORBIT_EQ_CFACE applies              *)
let FCARD1P = prove
 (`!(H:(A)hypermap) s. FINITE s /\ s SUBSET dart H
     ==> (1 < fcard_face H s <=> ?x y. x IN s /\ y IN s /\ ~cface H x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y. x IN (s:A->bool) /\ y IN s
          ==>
         (orbit_map (face_map (H:(A)hypermap)) x = orbit_map (face_map H) y <=>
               cface H x y)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ORBIT_EQ_CFACE THEN
   ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE] THEN
  ASM_SIMP_TAC[CARD_GE2; FINITE_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* nontrivial_ring (Coq NonTrivialRing section).  diskFC is restricted to    *)
(* the darts, {x | x IN dart H /\ diskFC H r x}: unlike Coq's diskFC over    *)
(* the finite dart type, the HOL diskFC also holds at the non-darts, which   *)
(* are face fixpoints.                                                       *)
(* ------------------------------------------------------------------------- *)
let nontrivial_ring = new_definition
 `nontrivial_ring (H:(A)hypermap) m (r:A list) <=>
    m < fcard_face H (diskF H r) /\
    m < fcard_face H {x | x IN dart H /\ diskFC H r x}`;;

let FINITE_DISKF = prove
 (`!(H:(A)hypermap) r. ALL (\y. y IN dart H) r ==> FINITE (diskF H r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `diskN (H:(A)hypermap) r` THEN ASM_SIMP_TAC[FINITE_DISKN] THEN
  REWRITE_TAC[SUBSET; IN; diskF] THEN MESON_TAC[]);;

let FINITE_DISKFC_DART = prove
 (`!(H:(A)hypermap) r. FINITE {x | x IN dart H /\ diskFC H r x}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `dart (H:(A)hypermap)` THEN
  REWRITE_TAC[FINITE_DART; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let DISKF_SUBSET_DART = prove
 (`!(H:(A)hypermap) (r:A list).
     ALL (\y. y IN dart H) r ==> diskF H r SUBSET dart H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN; diskF] THEN
  X_GEN_TAC `x:A` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;`r:A list`;`x:A`] DISKN_SUBSET_DART) THEN
  ASM_REWRITE_TAC[IN]);;

let NONTRIVIAL0P = prove
 (`!(H:(A)hypermap) r. ALL (\y. y IN dart H) r
     ==> (nontrivial_ring H 0 r <=>
          (?x. x IN diskF H r) /\ (?x. x IN dart H /\ diskFC H r x))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[nontrivial_ring; FCARD0P; FINITE_DISKF; FINITE_DISKFC_DART;
               IN_ELIM_THM]);;

let NONTRIVIAL1P = prove
 (`!(H:(A)hypermap) r. ALL (\y. y IN dart H) r
     ==> (nontrivial_ring H 1 r <=>
          (?x y. x IN diskF H r /\ y IN diskF H r /\ ~cface H x y) /\
          (?x y. (x IN dart H /\ diskFC H r x) /\
          (y IN dart H /\ diskFC H r y) /\
                 ~cface H x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nontrivial_ring] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;`diskF (H:(A)hypermap) r`] FCARD1P) THEN
  ASM_SIMP_TAC[FINITE_DISKF; DISKF_SUBSET_DART] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;
               `{x | x IN dart H /\ diskFC (H:(A)hypermap) r x}`] FCARD1P) THEN
  REWRITE_TAC[FINITE_DISKFC_DART] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM]);;

