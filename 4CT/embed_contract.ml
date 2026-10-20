(* ========================================================================= *)
(* 4CT/embed_contract.ml                                                     *)
(*                                                                           *)
(* embed.v, last part (embed.v:1306-1466): an embedded contract is a valid   *)
(* contract of the minimal counter-example, and a C-reducible configuration  *)
(* cannot embed in it.                                                       *)
(*   1. embed_sparse (EMBED_SPARSE), via mapEh1 (MAPEH1);                    *)
(*   2. face orbits along embed: orbitF_h1 (ORBITF_H1_SET) and cface_ac_h1   *)
(*      (CFACE_AC_H1_BC);                                                    *)
(*   3. the triad transfer (EMBED_TRIAD_TRANSFER: the count clause           *)
(*      TRIAD_COUNT_H1 and the non-adjacency clause TRIAD_NONADJ_H1) and     *)
(*      embed_valid_contract (EMBED_VALID_CONTRACT);                         *)
(*   4. embed_closure and embed_contract (EMBED_CLOSURE_ROTR1,               *)
(*      EMBED_CONTRACT): a contract colouring of the minimal counter-example *)
(*      pulls back to the configuration (CC_COLORING_PULLBACK) and colours   *)
(*      the remainder map (EMBED_REM_COLORING);                              *)
(*   5. c_reducible (Coq's C_reducible, coloring.v:470) and                  *)
(*      not_embed_reducible (NOT_EMBED_REDUCIBLE).                           *)
(* The contract cc is a list of darts of Gc; the lemmas about an arbitrary   *)
(* cc assume !u. MEM u cc ==> u IN dart Gc, which VALID_CONTRACT_IN_DART     *)
(* derives from valid_contract Gc rc cc.                                     *)
(* ========================================================================= *)

needs "4CT/contract.ml";;

(* ------------------------------------------------------------------------- *)
(* embed_sparse (embed.v:1312): the embedded contract is sparse.             *)
(* ------------------------------------------------------------------------- *)

let MAPEH1 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !p. (!x. MEM x p ==> x IN dart Gc)
             ==> insertE Gm (MAP (embed Gc Gm rc h) p) =
                 MAP (embed Gc Gm rc h) (insertE Gc p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP EMBEDE) THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; INSERTE_CLAUSES; MEM; CONS_11] THEN
  ASM_MESON_TAC[]);;

let RC_NODE_CLOSED = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) a.
     embed_context Gm Gc rc h /\ ~MEM a rc ==> ~MEM (node_map Gc a) rc`,
  REWRITE_TAC[embed_context; scycle] THEN MESON_TAC[RCN]);;

let EMBED_ITER_NODE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) a.
     embed_context Gm Gc rc h /\ a IN dart Gc /\ ~MEM a rc
     ==> !k. embed Gc Gm rc h (ITER k (node_map Gc) a) =
               ITER k (node_map Gm) (embed Gc Gm rc h a) /\
             ITER k (node_map Gc) a IN dart Gc /\
             ~MEM (ITER k (node_map Gc) a) rc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EMBEDN) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER; NODE_MAP_IN_DART] THEN
  ASM_MESON_TAC[RC_NODE_CLOSED]);;

let CNODE_EMBED_REFLECT = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) a b.
     embed_context Gm Gc rc h /\
     a IN dart Gc /\ ~MEM a rc /\ b IN dart Gc /\ ~MEM b rc /\
     cnode Gm (embed Gc Gm rc h a) (embed Gc Gm rc h b)
     ==> cnode Gc a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cnode; node; ORBIT_MAP_ITER] THEN
  STRIP_TAC THEN EXISTS_TAC `n:num` THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `a:A`] EMBED_ITER_NODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP EMBED_INJ) THEN ASM_REWRITE_TAC[]);;

let EMBED_SPARSE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc.
     embed_context Gm Gc rc h /\
     (!x. MEM x cc ==> x IN dart Gc) /\
     (!x. MEM x (insertE Gc cc) ==> ~MEM x rc) /\
     sparse Gc (insertE Gc cc)
     ==> sparse Gm (insertE Gm (MAP (embed Gc Gm rc h) cc))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP MAPEH1 th]) THEN
  SUBGOAL_THEN `!k. k < LENGTH (insertE Gc (cc:(A)list))
                    ==> EL k (insertE Gc cc) IN dart Gc /\
                        ~MEM (EL k (insertE Gc cc)) rc`
  ASSUME_TAC THENL [ASM_MESON_TAC[MEM_EL; INSERTE_IN_DART]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sparse]) THEN
  ASM_SIMP_TAC[sparse; LENGTH_MAP; EL_MAP] THEN
  ASM_MESON_TAC[CNODE_EMBED_REFLECT]);;

(* ------------------------------------------------------------------------- *)
(* Face orbits along embed (embed.v:1325, 1368): orbitF_h1 in set form (the  *)
(* HOL face orbit is a set) and cface_ac_h1, with its border-avoidance       *)
(* argument on the disk map embed_disk.                                      *)
(* ------------------------------------------------------------------------- *)

let EMBED_ITER_FACE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x.
     embed_context Gm Gc rc h /\ x IN kernel Gc rc
     ==> !k. embed Gc Gm rc h (ITER k (face_map Gc) x) =
               ITER k (face_map Gm) (embed Gc Gm rc h x) /\
             ITER k (face_map Gc) x IN kernel Gc rc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EMBED_FACE_KERNEL) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER; KERNEL_FCLOSED]);;

let ORBITF_H1_SET = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN kernel Gc rc
             ==> face Gm (embed Gc Gm rc h x) =
                 IMAGE (embed Gc Gm rc h) (face Gc x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `x:A`] EMBED_ITER_FACE) THEN
  ASM_REWRITE_TAC[EXTENSION; IN_IMAGE; face; ORBIT_MAP_ITER] THEN
  MESON_TAC[]);;

(* The backward direction of Coq's patch_face_d: a disk dart whose face      *)
(* avoids the border has the same face in the disk map as in the patch.      *)

let PATCH_CFACE_HD_BWD = prove
 (`!G Gd Gr hd hr bGd bGr xd yd.
     patch G Gd Gr (hd:A->B) (hr:B->B) bGd bGr /\
     xd IN dart Gd /\ yd IN dart Gd /\
     (!b. MEM b bGd ==> ~cface Gd xd b) /\ cface G (hd xd) (hd yd)
     ==> cface Gd xd yd`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(B)hypermap`;
                 `hd:A->B`; `hr:B->B`; `bGd:A list`; `bGr:B list`; `xd:A`]
                PATCH_FACE_CHAIN_HD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ITER k (face_map Gd) (xd:A)`) THEN
    ASM_REWRITE_TAC[cface; face; ITER_IN_ORBIT];
    DISCH_TAC] THEN
  UNDISCH_TAC `cface G ((hd:A->B) xd) (hd yd)` THEN
  ASM_REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[INJ] o MATCH_MP PATCH_INJ_HD) THEN
  ASM_MESON_TAC[ITER_FACE_IN_DART]);;

let KERNEL_DISK_FACE_AVOID = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x.
     embed_context Gm Gc rc h /\ x IN kernel Gc rc
     ==> !b. MEM b (MAP (edge_map Gc) rc) ==> ~cface (embed_disk Gc rc) x b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_KERNEL] THEN STRIP_TAC THEN
  X_GEN_TAC `b:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CTX_RING) THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] ERC_IN_EMBD_D) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `b:A`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN embd_D Gc rc` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_EMBD_D] THEN
    ASM_MESON_TAC[FBAND_MEM_IFF; CFACE_REFL];
    ASM_SIMP_TAC[CFACE_EMBD]] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x:A`] EERCF) THEN
  ASM_REWRITE_TAC[FBAND_MEM_IFF] THEN ASM_MESON_TAC[]);;

let CFACE_AC_H1_BC = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x y.
     embed_context Gm Gc rc h /\ x IN kernel Gc rc /\
     y IN dart Gc /\ ~MEM y rc
     ==> (cface Gm (embed Gc Gm rc h x) (embed Gc Gm rc h y) <=>
          cface Gc x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[CFACE_H1]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CTX_RING) THEN
  SUBGOAL_THEN `(x:A) IN embd_D Gc rc /\ (y:A) IN embd_D Gc rc`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_EMBD_D] THEN ASM_MESON_TAC[IN_KERNEL; AC_BC; IN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] CFACE_EMBD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[GSYM th]) THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `embed_disk (Gc:(A)hypermap) rc`;
                 `embed_rem (Gc:(A)hypermap) Gm rc (h:A->B)`;
                 `embed Gc Gm rc (h:A->B)`; `I:B->B`;
                 `MAP (edge_map (Gc:(A)hypermap)) rc`;
                 `embr_ring Gc Gm rc (h:A->B)`; `x:A`; `y:A`]
                PATCH_CFACE_HD_BWD) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[EMBED_PATCH; EMBD_DISK_COMPONENTS] THEN
  ASM_MESON_TAC[KERNEL_DISK_FACE_AVOID]);;

(* The face darts of a kernel dart are kernel darts, hence off the ring.     *)

let FACE_KERNEL_DART = prove
 (`!(Gc:(A)hypermap) rc x a.
     x IN kernel Gc rc /\ a IN face Gc x ==> a IN dart Gc /\ ~MEM a rc`,
  REPEAT STRIP_TAC THEN CFACE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The triad transfers along embed (embed.v:1382-1400, the triad clause of   *)
(* embed_valid_contract).  The HOL face orbit is a set, so Coq's count of    *)
(* adjp in orbit face x is the cardinality of the satisfying part of the     *)
(* face (TRIAD_COUNT_H1).  For the non-adjacency clause, Coq's two witnesses *)
(* for adj x0 y are node y when cface x0 (node y), and edge (face y) when    *)
(* cface x0 (node (edge y)) (CFACE_NODE_DISJ_ADJ); ADJ_PULLBACK_DISJ gets    *)
(* the disjunction from the adjacencies in Gm by adj11_edge (ADJ11_EDGE).    *)
(* ------------------------------------------------------------------------- *)

let FBAND_H1_TRANSFER = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc z.
     embed_context Gm Gc rc h /\ (!u. MEM u cc ==> u IN dart Gc) /\
     z IN dart Gc /\ fband Gc (insertE Gc cc) (edge_map Gc z)
     ==> fband Gm (insertE Gm (MAP (embed Gc Gm rc h) cc))
                  (edge_map Gm (embed Gc Gm rc h z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[MATCH_MP MAPEH1 th; GSYM(MATCH_MP EMBEDE th)]) THEN
  UNDISCH_TAC `fband Gc (insertE Gc cc) (edge_map Gc (z:A))` THEN
  REWRITE_TAC[FBAND_MEM_IFF; MEM_MAP] THEN ASM_MESON_TAC[CFACE_H1]);;

let TRIAD_COUNT_H1 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc x.
     embed_context Gm Gc rc h /\ (!z. MEM z cc ==> z IN dart Gc) /\
     x IN kernel Gc rc /\
     2 < CARD {z | z IN face Gc x /\ fband Gc (insertE Gc cc) (edge_map Gc z)}
     ==> 2 < CARD {y | y IN face Gm (embed Gc Gm rc h x) /\
                       fband Gm (insertE Gm (MAP (embed Gc Gm rc h) cc))
                         (edge_map Gm y)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (ARITH_RULE `2 < m ==> m <= n ==> 2 < n`)) THEN
  SUBGOAL_THEN `!z:A. z IN face Gc x ==> z IN dart Gc /\ ~MEM z rc`
  ASSUME_TAC THENL [ASM_MESON_TAC[FACE_KERNEL_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (face Gc (x:A))` ASSUME_TAC THENL
   [REWRITE_TAC[face] THEN MATCH_MP_TAC ORBIT_FINITE THEN
    EXISTS_TAC `dart Gc:A->bool` THEN
    REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
    ASM_MESON_TAC[IN_KERNEL];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP ORBITF_H1_SET th]) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (embed Gc Gm rc (h:A->B))
     {z | z IN face Gc x /\ fband Gc (insertE Gc cc) (edge_map Gc z)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `m = n ==> n <= m`) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[EMBED_INJ]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `face Gc (x:A)` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[FUN_IN_IMAGE; FBAND_H1_TRANSFER];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (embed Gc Gm rc (h:A->B)) (face Gc x)` THEN
      ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_ELIM_THM]]]);;

(* For an edge y off the ring, node (edge y) and edge (face y) are cofacial: *)
(* face y = node (node (edge y)) as node^3 fixes edge y (quasicubic).        *)

let CFACE_NODE_EDGE_LINK = prove
 (`!(Gc:(A)hypermap) rc y.
     plain_hypermap Gc /\ quasicubic Gc (\z. MEM z rc) /\
     y IN dart Gc /\ ~MEM (edge_map Gc y) rc
     ==> cface Gc (node_map Gc (edge_map Gc y)) (edge_map Gc (face_map Gc y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `\z:A. MEM z rc`; `edge_map Gc (y:A)`]
    QUASICUBIC_EQ) THEN
  ASM_SIMP_TAC[IN; EDGE_MAP_IN_DART] THEN DISCH_TAC THEN CFACE_TAC[]);;

let CFACE_NODE_DISJ_ADJ = prove
 (`!(Gc:(A)hypermap) rc x0 y.
     plain_hypermap Gc /\ quasicubic Gc (\z. MEM z rc) /\
     x0 IN dart Gc /\ y IN dart Gc /\ ~MEM (edge_map Gc y) rc /\
     (cface Gc x0 (node_map Gc y) \/ cface Gc x0 (node_map Gc (edge_map Gc y)))
     ==> adj Gc x0 y`,
  REWRITE_TAC[adj] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `node_map Gc (y:A)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM cface]; REWRITE_TAC[RLINK_NODE]];
    EXISTS_TAC `edge_map Gc (face_map Gc (y:A))` THEN
    MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `y:A`]
      CFACE_NODE_EDGE_LINK) THEN
    ASM_REWRITE_TAC[] THEN CFACE_TAC[]]);;

let ADJ_PULLBACK_DISJ = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x0 y.
     embed_context Gm Gc rc h /\ x0 IN kernel Gc rc /\
     y IN dart Gc /\ ~MEM y rc /\ ~MEM (edge_map Gc y) rc /\
     adj Gm (embed Gc Gm rc h x0) (embed Gc Gm rc h y) /\
     adj Gm (embed Gc Gm rc h x0) (edge_map Gm (embed Gc Gm rc h y))
     ==> cface Gc x0 (node_map Gc y) \/
         cface Gc x0 (node_map Gc (edge_map Gc y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x0:A) IN dart Gc /\ ~MEM (node_map Gc y) rc /\
                ~MEM (node_map Gc (edge_map Gc y)) rc`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_KERNEL; RC_NODE_CLOSED]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EMBED_IN_DART) THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `embed Gc Gm rc (h:A->B) x0`;
                 `embed Gc Gm rc (h:A->B) y`] ADJ11_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[embed_context]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MEM_SPOKE_RING; EDGE_MAP_IN_DART;
    GSYM(MATCH_MP EMBEDE th); GSYM(MATCH_MP EMBEDN th)]) THEN
  ASM_SIMP_TAC[CFACE_AC_H1_BC; NODE_MAP_IN_DART; EDGE_MAP_IN_DART]);;

let TRIAD_NONADJ_H1 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc x0.
     embed_context Gm Gc rc h /\ (!u. MEM u cc ==> u IN dart Gc) /\
     (!w. MEM w (insertE Gc cc) ==> ~MEM w rc) /\ x0 IN kernel Gc rc /\
     (!z. MEM z (insertE Gm (MAP (embed Gc Gm rc h) cc))
          ==> adj Gm (embed Gc Gm rc h x0) z)
     ==> !y. MEM y (insertE Gc cc) ==> adj Gc x0 y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `plain_hypermap (Gc:(A)hypermap) /\
                quasicubic Gc (\z:A. MEM z rc) /\ x0 IN dart Gc`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[embed_context; IN_KERNEL]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN dart Gc /\ MEM (edge_map Gc y) (insertE Gc cc)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[INSERTE_IN_DART; INSERTE_EDGE_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x0:A`; `y:A`]
    CFACE_NODE_DISJ_ADJ) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `x0:A`; `y:A`] ADJ_PULLBACK_DISJ) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[GSYM(MATCH_MP EMBEDE th)]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP MAPEH1 th]) THEN
  REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]);;

let EMBED_TRIAD_TRANSFER = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc x0.
     embed_context Gm Gc rc h /\ (!u. MEM u cc ==> u IN dart Gc) /\
     (!w. MEM w (insertE Gc cc) ==> ~MEM w rc) /\ x0 IN kernel Gc rc /\
     triad Gc (insertE Gc cc) x0
     ==> triad Gm (insertE Gm (MAP (embed Gc Gm rc h) cc))
               (embed Gc Gm rc h x0)`,
  REWRITE_TAC[triad] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC TRIAD_COUNT_H1 THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(!z:A. MEM z (insertE Gc cc) ==> adj Gc x0 z)` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                         `h:A->B`; `cc:(A)list`; `x0:A`] TRIAD_NONADJ_H1) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* embed_valid_contract (embed.v:1377): the embedded contract is a valid     *)
(* contract of Gm for the empty ring (kernel Gm [] is all of dart Gm), so it *)
(* has a contract colouring (contract_coloring, CONTRACT_COLORING).  The     *)
(* contract darts are darts: a non-dart is fixed by edge_map and would occur *)
(* twice in the sparse list insertE cc (VALID_CONTRACT_IN_DART).             *)
(* ------------------------------------------------------------------------- *)

let VALID_CONTRACT_IN_DART = prove
 (`!(H:(A)hypermap) r cc.
     valid_contract H r cc ==> !u. MEM u cc ==> u IN dart H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_contract] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM ALL_MEM] SPARSE_INSERTE_DART) THEN
  ASM_REWRITE_TAC[]);;

let EMBED_VALID_CONTRACT = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc.
     embed_context Gm Gc rc h /\ valid_contract Gc rc cc
     ==> valid_contract Gm [] (MAP (embed Gc Gm rc h) cc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VALID_CONTRACT_IN_DART) THEN
  UNDISCH_TAC `valid_contract (Gc:(A)hypermap) rc cc` THEN
  REWRITE_TAC[valid_contract; LENGTH_MAP; MEM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EMBED_SPARSE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `embed Gc Gm rc (h:A->B) x0` THEN
  ASM_SIMP_TAC[EMBED_TRIAD_TRANSFER; IN_KERNEL; fband; EX] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP EMBED_IN_DART) THEN
  ASM_MESON_TAC[IN_KERNEL]);;

let EMBED_VALID_CONTRACT_TRIAD = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc.
     embed_context Gm Gc rc h /\ valid_contract Gc rc cc
     ==> cc_colorable Gm (MAP (embed Gc Gm rc h) cc)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTRACT_COLORING THEN
  EXISTS_TAC `[]:(B)list` THEN
  ASM_MESON_TAC[embed_context; EMBED_VALID_CONTRACT]);;

(* ------------------------------------------------------------------------- *)
(* embed_contract (embed.v:1413): a contract colouring k of Gm on the        *)
(* embedded contract gives the contract colouring k o embed of Gc            *)
(* (CC_COLORING_PULLBACK; CC_EDGE_BC is Coq's k1Ebc) and the colouring k of  *)
(* the remainder map (EMBED_REM_COLORING: by EMBED_PATCH, hr = I and the     *)
(* remainder darts are darts of Gm, which avoid the embedded contract), with *)
(* the same trace on REVERSE rc and on rotr1 (embr_ring), the ring of Coq's  *)
(* embed_cotrace (embed.v:1403); embed_closure (EMBED_CLOSURE_ROTR1,         *)
(* embed.v:1405).                                                            *)
(* ------------------------------------------------------------------------- *)

let CFACE_CC_COLORING = prove
 (`!(H:(A)hypermap) cc k x y.
     cc_coloring H cc k /\ x IN dart H /\ cface H x y ==> k y = k x`,
  REWRITE_TAC[cc_coloring] THEN MESON_TAC[CFACE_COLOR_EQ]);;

let EMBR_AVOID_CONTRACT = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc w.
     embed_context Gm Gc rc h /\
     (!u. MEM u cc ==> u IN dart Gc) /\
     (!v. MEM v (insertE Gc cc) ==> ~MEM v rc) /\
     w IN embr_D Gc Gm rc h
     ==> ~MEM w (insertE Gm (MAP (embed Gc Gm rc h) cc))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CTX_RING) THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP MAPEH1 th]) THEN
  REWRITE_TAC[MEM_MAP; NOT_EXISTS_THM] THEN X_GEN_TAC `v:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:A) IN embd_D Gc rc` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_EMBD_D; INSERTE_IN_DART]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:B` o MATCH_MP CODOM_EMBR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_EMBR_D]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MEM_MAP; LEFT_AND_EXISTS_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `t:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v:A = u` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[INJ] o MATCH_MP EMBDD_INJ) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] ERC_IN_EMBD_D) THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (t:A) (insertE Gc cc)` MP_TAC THENL
   [SUBGOAL_THEN `t = edge_map Gc (u:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[PLAIN_EQ; RING_MEM_DART];
      ASM_SIMP_TAC[INSERTE_EDGE_CLOSED]];
    ASM_MESON_TAC[]]);;

let EMBED_REM_COLORING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc k.
     embed_context Gm Gc rc h /\
     (!u. MEM u cc ==> u IN dart Gc) /\
     (!v. MEM v (insertE Gc cc) ==> ~MEM v rc) /\
     2 <= LENGTH rc /\ cc_coloring Gm (MAP (embed Gc Gm rc h) cc) k
     ==> coloring (embed_rem Gc Gm rc h) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EMBED_PATCH) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP EMBED_REM_COMPONENTS) THEN
  SUBGOAL_THEN `!x:B. x IN embr_D Gc Gm rc (h:A->B) ==> x IN dart Gm`
  ASSUME_TAC THENL [SIMP_TAC[IN_EMBR_D]; ASM_REWRITE_TAC[coloring]] THEN
  CONJ_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `x:B` o MATCH_MP PATCH_EDGE_R) THEN
    ASM_REWRITE_TAC[I_THM] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:B` o CONJUNCT1 o
      REWRITE_RULE[cc_coloring]) THEN
    ASM_MESON_TAC[EMBR_AVOID_CONTRACT];
    MATCH_MP_TAC CFACE_CC_COLORING THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`;
                          `MAP (embed Gc Gm rc (h:A->B)) cc`] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:B` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      PATCH_CFACE_HR_STEP)) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; I_THM]]);;

let CC_EDGE_BC = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc k x.
     embed_context Gm Gc rc h /\ (!u. MEM u cc ==> u IN dart Gc) /\
     (!w. MEM w (insertE Gc cc) ==> ~MEM w rc) /\
     cc_coloring Gm (MAP (embed Gc Gm rc h) cc) k /\ x IN dart Gc /\ ~MEM x rc
     ==> (k(embed Gc Gm rc h (edge_map Gc x)) = k(embed Gc Gm rc h x) <=>
          MEM x (insertE Gc cc))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP EMBEDE th]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `embed Gc Gm rc (h:A->B) x` o CONJUNCT1 o
    REWRITE_RULE[cc_coloring]) THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[MATCH_MP EMBED_IN_DART th; MATCH_MP MAPEH1 th]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM_MAP] THEN
  ASM_MESON_TAC[EMBED_INJ; INSERTE_IN_DART]);;

let CC_COLORING_PULLBACK = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc k.
     embed_context Gm Gc rc h /\ (!u. MEM u cc ==> u IN dart Gc) /\
     (!w. MEM w (insertE Gc cc) ==> ~MEM w rc) /\
     cc_coloring Gm (MAP (embed Gc Gm rc h) cc) k
     ==> cc_coloring Gc cc ((k:B->color) o embed Gc Gm rc h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CTX_RING) THEN
  REWRITE_TAC[cc_coloring; o_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x:A`] EDGE_PERIMETER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [MATCH_MP_TAC CC_EDGE_BC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                     `h:A->B`; `cc:(A)list`; `k:B->color`;
                     `edge_map Gc (x:A)`] CC_EDGE_BC) THEN
      ASM_SIMP_TAC[EDGE_MAP_IN_DART; PLAIN_EQ; INSERTE_EDGE_SYM] THEN
      MESON_TAC[]];
    MATCH_MP_TAC CFACE_CC_COLORING THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`;
                          `MAP (embed Gc Gm rc (h:A->B)) cc`] THEN
    ASM_MESON_TAC[EMBED_IN_DART; CFACE_H1; CFT_FACE]]);;

(* MAP of a node path telescopes to the path shifted by one step; on a node  *)
(* cycle, rot1 is MAP of the node map (Coq rot1_cons).                       *)

let MAP_LIST_PATH = prove
 (`!(g:A->A) l a.
     list_path (\x y. g x = y) a l
     ==> MAP g (CONS a l) = APPEND l [g (LAST (CONS a l))]`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[MAP; APPEND; LAST; NOT_CONS_NIL];
    X_GEN_TAC `c:A` THEN X_GEN_TAC `t:(A)list` THEN DISCH_TAC THEN
    X_GEN_TAC `a:A` THEN REWRITE_TAC[list_path] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `LAST (CONS (a:A) (CONS c t)) = LAST (CONS c t)`
    SUBST1_TAC THENL [REWRITE_TAC[LAST; NOT_CONS_NIL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MAP] THEN ASM_REWRITE_TAC[APPEND]]);;

let LIST_CYCLE_ROT1_MAP = prove
 (`!(g:A->A) r. list_cycle (\x y. g x = y) r ==> rot1 r = MAP g r`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `r:(A)list` list_CASES) THENL
   [REWRITE_TAC[list_cycle]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`g:A->A`; `h:A`; `t:(A)list`] LIST_CYCLE_HD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `list_path (\x y. (g:A->A) x = y) h t` ASSUME_TAC THENL
   [UNDISCH_TAC `list_cycle (\x y. (g:A->A) x = y) (CONS h t)` THEN
    REWRITE_TAC[list_cycle; NOT_CONS_NIL; list_path] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rot1; NOT_CONS_NIL; TL; HD] THEN
  MP_TAC(ISPECL [`g:A->A`; `t:(A)list`; `h:A`] MAP_LIST_PATH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* Coq proves embed_closure by Kempe_map on rotr 1 embr_ring; here Kempe_map *)
(* (KEMPE_MAP) is applied to embr_ring and the result rotated, as rotr1 is   *)
(* an iterate of rot1 (ROTR1_ITER_ROT1, KEMPE_CLOSED_RING_ITER_ROT1).        *)

let EMBED_CLOSURE_ROTR1 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h /\ 2 <= LENGTH rc
     ==> kempe_closed (ring_trace (embed_rem Gc Gm rc h)
                                  (rotr1 (embr_ring Gc Gm rc h)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(embr_ring Gc Gm rc (h:A->B) = [])` ASSUME_TAC THENL
   [REWRITE_TAC[embr_ring; GSYM LENGTH_EQ_NIL; LENGTH_REVERSE; LENGTH_MAP] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[ROTR1_ITER_ROT1] THEN
    MATCH_MP_TAC KEMPE_CLOSED_RING_ITER_ROT1 THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC KEMPE_MAP THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`]
    UCYCLE_EMBR_RING) THEN
  ASM_SIMP_TAC[ucycle_planar_plain_quasicubic; ucycle_plain_quasicubic;
               plain_quasicubic; PLAIN_EMBR; PLANAR_EMBR; EMBED_REM_COMPONENTS;
               GSYM ALL_MEM; EMBR_RING_MEM; LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `set_of_list (embr_ring Gc Gm rc (h:A->B)) =
                  (\z. MEM z (embr_ring Gc Gm rc h))` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_MEM_LAM];
      MATCH_MP_TAC CUBIC_EMBR THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
      `h:A->B`] EMBED_ERC_IN_EMBR_D) THEN
    ASM_SIMP_TAC[]]);;

(* The two traces agree: k (embed z) = k (embed (edge (node z))) for z in    *)
(* rc, as the two darts are cofacial (nodeK), and rot1 rc = MAP node rc.     *)

let CC_TRACE_EQ_ROTR1 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc (k:B->color).
     embed_context Gm Gc rc h /\ cc_coloring Gm (MAP (embed Gc Gm rc h) cc) k
     ==> MAP (k o embed Gc Gm rc h) (REVERSE rc) =
         MAP k (rotr1 (embr_ring Gc Gm rc h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CTX_RING) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EMBED_IN_DART) THEN
  REWRITE_TAC[embr_ring; GSYM REV_ROT1; GSYM MAP_ROT1] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LIST_CYCLE_ROT1_MAP
    (MATCH_MP SCYCLE_CYCLE th)]) THEN
  REWRITE_TAC[GSYM MAP_REVERSE; GSYM MAP_o] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CFACE_CC_COLORING THEN
  MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`;
                        `MAP (embed Gc Gm rc (h:A->B)) cc`] THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP CFACE_H1) THEN CFACE_TAC[]);;

let EMBED_CONTRACT = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc.
     embed_context Gm Gc rc h /\ 2 <= LENGTH rc /\ valid_contract Gc rc cc
     ==> ?et. cc_ring_trace Gc cc (REVERSE rc) et /\
              ring_trace (embed_rem Gc Gm rc h) (rotr1 (embr_ring Gc Gm rc h))
                         et`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VALID_CONTRACT_IN_DART) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[valid_contract]) THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `cc:(A)list`] EMBED_VALID_CONTRACT_TRIAD) THEN
  ASM_REWRITE_TAC[cc_colorable] THEN DISCH_THEN(X_CHOOSE_TAC `k:B->color`) THEN
  EXISTS_TAC `trace_col (MAP ((k:B->color) o embed Gc Gm rc (h:A->B))
                             (REVERSE rc))` THEN
  REWRITE_TAC[cc_ring_trace; ring_trace] THEN CONJ_TAC THENL
   [EXISTS_TAC `(k:B->color) o embed Gc Gm rc (h:A->B)` THEN
    ASM_SIMP_TAC[CC_COLORING_PULLBACK];
    EXISTS_TAC `k:B->color` THEN
    ASM_MESON_TAC[EMBED_REM_COLORING; CC_TRACE_EQ_ROTR1]]);;

(* ------------------------------------------------------------------------- *)
(* c_reducible (Gonthier's C_reducible record, coloring.v:470): a valid      *)
(* contract whose contract ring traces lie in the Kempe coclosure of the     *)
(* ring traces.  cfreducible.ml instantiates it for the configurations.      *)
(* ------------------------------------------------------------------------- *)

let c_reducible = new_definition
 `c_reducible (H:(A)hypermap) (r:(A)list) (cc:(A)list) <=>
    valid_contract H r cc /\
    (!et. cc_ring_trace H cc (REVERSE r) et
          ==> kempe_coclosure (ring_trace H (REVERSE r)) et)`;;

(* ------------------------------------------------------------------------- *)
(* not_embed_reducible (embed.v:1446): a C-reducible configuration cannot    *)
(* embed in a minimal counter-example.  The coclosure clause of c_reducible, *)
(* at the Kempe-closed embed_cotrace, gives a trace et1 of both Gc (on       *)
(* REVERSE rc) and the remainder map (on rotr1 (embr_ring)); a colouring k   *)
(* of Gc colours the disk map embed_disk with the trace                      *)
(* rotr1 (REVERSE (rot1 et1)) on its border (EMBD_DISK_COLORING,             *)
(* EMBED_DISK_RING_TRACE), and colorable_patch (COLORABLE_PATCH) four-       *)
(* colours Gm, a contradiction.                                              *)
(* ------------------------------------------------------------------------- *)

let TRACE_COL_REVERSE_ROTR1 = prove
 (`!L:(color)list. trace_col (REVERSE L) = rotr1 (REVERSE (trace_col L))`,
  GEN_TAC THEN ASM_CASES_TAC `L:(color)list = []` THEN
  ASM_SIMP_TAC[TRACE_COL_REVERSE; REV_ROT1] THEN
  REWRITE_TAC[REVERSE; trace_DEF; rotr1]);;

let EMBD_DISK_COLORING = prove
 (`!(Gc:(A)hypermap) rc (k:A->color).
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w) /\ coloring Gc k
     ==> coloring (embed_disk Gc rc) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[coloring; EMBD_DISK_COMPONENTS; embd_emap; embd_fmap] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[coloring]) THEN
  CONJ_TAC THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_EMBD_D] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THENL
   [SUBGOAL_THEN `(k:A->color) (edge_map Gc (node_map Gc (edge_map Gc x))) =
                  k (edge_map Gc x)` SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CFACE_COLORING THEN EXISTS_TAC `Gc:(A)hypermap` THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART] THEN CFACE_TAC[]);;

let EMBED_DISK_RING_TRACE = prove
 (`!(Gc:(A)hypermap) rc (et1:(color)list).
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w) /\
     ring_trace Gc (REVERSE rc) et1
     ==> ring_trace (embed_disk Gc rc) (MAP (edge_map Gc) rc)
                    (rotr1 (REVERSE (rot1 et1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_trace] THEN STRIP_TAC THEN
  EXISTS_TAC `k:A->color` THEN ASM_SIMP_TAC[EMBD_DISK_COLORING] THEN
  SUBGOAL_THEN `MAP (k:A->color) (MAP (edge_map Gc) rc) = rotr1 (MAP k rc)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(MESON[ROTR1_ROT1]
     `!l m:(color)list. rot1 l = m ==> l = rotr1 m`) THEN
    REWRITE_TAC[GSYM MAP_ROT1] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LIST_CYCLE_ROT1_MAP
      (MATCH_MP SCYCLE_CYCLE th)]) THEN
    REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CFACE_COLORING THEN EXISTS_TAC `Gc:(A)hypermap` THEN
    ASM_SIMP_TAC[] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(MAP (k:A->color) rc = [])` ASSUME_TAC THENL
   [REWRITE_TAC[MAP_EQ_NIL] THEN ASM_MESON_TAC[SCYCLE_CYCLE; list_cycle];
    ASM_SIMP_TAC[GSYM MAP_REVERSE; TRACE_COL_REVERSE_ROTR1; TRACE_COL_ROTR1;
                 ROT1_ROTR1; REVERSE_REVERSE]]);;

let NOT_EMBED_REDUCIBLE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) cc.
     embed_context Gm Gc rc h /\ 2 <= LENGTH rc /\ c_reducible Gc rc cc
     ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c_reducible] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `cc:(A)list`] EMBED_CONTRACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `et0:(color)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `et0:(color)list`) THEN
  ASM_REWRITE_TAC[kempe_coclosure] THEN
  DISCH_THEN(MP_TAC o SPEC `ring_trace (embed_rem Gc Gm rc (h:A->B))
                                       (rotr1 (embr_ring Gc Gm rc h))`) THEN
  ASM_SIMP_TAC[EMBED_CLOSURE_ROTR1] THEN
  DISCH_THEN(X_CHOOSE_THEN `et1:(color)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `four_colorable (Gm:(B)hypermap)` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[embed_context; minimal_counter_example]] THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `embed_disk (Gc:(A)hypermap) rc`;
                 `embed_rem (Gc:(A)hypermap) Gm rc (h:A->B)`;
                 `embed Gc Gm rc (h:A->B)`; `I:B->B`;
                 `MAP (edge_map (Gc:(A)hypermap)) rc`;
                 `embr_ring Gc Gm rc (h:A->B)`] COLORABLE_PATCH) THEN
  ASM_SIMP_TAC[EMBED_PATCH; LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC `rotr1 (REVERSE (rot1 (et1:(color)list)))` THEN
  REWRITE_TAC[ROT1_ROTR1; REVERSE_REVERSE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC EMBED_DISK_RING_TRACE THEN ASM_MESON_TAC[CTX_RING];
    MP_TAC(ISPECL [`embed_rem (Gc:(A)hypermap) Gm rc (h:A->B)`;
                   `rotr1 (embr_ring Gc Gm rc (h:A->B))`; `et1:(color)list`]
                  RING_TRACE_ROT1) THEN
    ASM_REWRITE_TAC[ROT1_ROTR1] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `~(embr_ring Gc Gm rc (h:A->B) = [])` ASSUME_TAC THENL
     [REWRITE_TAC[embr_ring; GSYM LENGTH_EQ_NIL; LENGTH_REVERSE;
                  LENGTH_MAP] THEN
      ASM_ARITH_TAC;
      ASM_REWRITE_TAC[rotr1; NOT_CONS_NIL]]]);;
