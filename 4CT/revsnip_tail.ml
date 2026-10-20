(* ========================================================================= *)
(* 4CT/revsnip_tail.ml                                                       *)
(*                                                                           *)
(* revsnip.v, last part: the properties of nontrivial rings                  *)
(* (NONTRIVIAL_RING_PROPER, NONTRIVIAL_REV_RING, NONTRIVIAL_CHORD_RING), the *)
(* ring colouring lemmas COLORABLE_FROM_RING and RING_DISK_CLOSED for the    *)
(* identity-based snip of snip.ml, and RING_DISK_CHORD: a ring disk with a   *)
(* chord contains a nontrivial chord ring.                                   *)
(* ========================================================================= *)

needs "4CT/embed_prelim.ml";;

let DISKF_NONEMPTY = prove
 (`!(H:(A)hypermap) m r.
     ALL (\y. y IN dart H) r /\ nontrivial_ring H m r ==> ?u. u IN diskF H r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;`diskF (H:(A)hypermap) r`] FCARD0P) THEN
  ASM_SIMP_TAC[FINITE_DISKF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `nontrivial_ring (H:(A)hypermap) m r` THEN
  REWRITE_TAC[nontrivial_ring] THEN ARITH_TAC);;

let DISKFC_DART_NONEMPTY = prove
 (`!(H:(A)hypermap) m r.
     nontrivial_ring H m r ==> ?v. v IN dart H /\ diskFC H r v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;
               `{x | x IN dart H /\ diskFC (H:(A)hypermap) r x}`] FCARD0P) THEN
  REWRITE_TAC[FINITE_DISKFC_DART; IN_ELIM_THM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `nontrivial_ring (H:(A)hypermap) m r` THEN
  REWRITE_TAC[nontrivial_ring] THEN ARITH_TAC);;

(* The degenerate edge ring [h; edge h] bounds everything: diskN is closed   *)
(* under glink steps (node steps by DISKN_NODE_EQ; edge steps by DISKE_EDGE  *)
(* off the ring; face steps by DISKN_FACE_OFFRING off the ring and, for a    *)
(* ring dart x, whose edge x is also on the ring by plainness, by            *)
(* FACE_EDGE_IN_DISKN), so with connectivity every dart is inside.           *)
let EDGE_RING_DISKN_ALL = prove
 (`!(H:(A)hypermap) h v.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) [h; edge_map H h] /\ h IN dart H /\ v IN dart H
     ==> diskN H [h; edge_map H h] v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. gcomp H h y ==> y IN dart H /\ diskN H [h; edge_map H h] (y:A)`
   (fun th -> ASM_MESON_TAC[th; connected_hypermap]) THEN
  MATCH_MP_TAC GCOMP_INDUCT THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_IN_DISKN; MEM]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN
   `ALL (\z. z IN dart H) [h; edge_map H h] /\
    !z:A. MEM z [h; edge_map H h] ==> MEM (edge_map H z) [h; edge_map H h]`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALL; EDGE_MAP_IN_DART; MEM] THEN ASM_MESON_TAC[CFT_PLAIN_EE];
    ALL_TAC] THEN
  REWRITE_TAC[glink] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART;
               DISKN_NODE_EQ] THEN
  ASM_CASES_TAC `MEM (x:A) [h; edge_map H h]` THEN
  ASM_MESON_TAC[RING_IN_DISKN; FACE_EDGE_IN_DISKN; EDGE_MAP_IN_DART;
                CFT_PLAIN_EE; DISKN_FACE_OFFRING; DISKE_EDGE; diskE]);;

(* A nontrivial ring is proper: the empty ring has an empty disk, a one-dart *)
(* ring would be a bridge, and the edge ring [x; edge x] would leave nothing *)
(* outside its disk (NOT_PROPER_RING).                                       *)
let NONTRIVIAL_RING_PROPER = prove
 (`!(H:(A)hypermap) m r.
     planar_hypermap H /\ bridgeless H /\ plain_hypermap H /\
     connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\ nontrivial_ring H m r
     ==> proper_ring H r`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `p ==> q <=> ~q ==> ~p`] THEN
  REWRITE_TAC[NOT_PROPER_RING] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[ALL] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `m:num`; `[]:(A)list`] DISKF_NONEMPTY) THEN
    ASM_REWRITE_TAC[ALL; IN; diskF; diskN; EX];
    UNDISCH_TAC `scycle H (rlink H) [x:A]` THEN
    REWRITE_TAC[scycle; list_cycle; LAST; NOT_CONS_NIL; list_path] THEN
    CFACE_TAC[];
    MP_TAC(ISPECL [`H:(A)hypermap`; `m:num`; `[x; edge_map H x]:(A)list`]
      DISKFC_DART_NONEMPTY) THEN
    ASM_REWRITE_TAC[diskFC] THEN ASM_MESON_TAC[EDGE_RING_DISKN_ALL]]);;

(* nontrivial_ring is preserved by rev_ring: on the darts, diskF of the      *)
(* reversed ring is diskFC of r and diskFC of the reversed ring is diskF of  *)
(* r (DISKF_REV_RING, DISKN_REV_RING, FBAND_REV_RING); off the darts both    *)
(* sides are false.  So the two fcard conjuncts swap.                        *)
let NONTRIVIAL_REV_RING = prove
 (`!(H:(A)hypermap) m r.
     planar_hypermap H /\ bridgeless H /\ plain_hypermap H /\
     connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\ nontrivial_ring H m r
     ==> nontrivial_ring H m (rev_ring H r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `proper_ring (H:(A)hypermap) r /\ list_cycle (rlink H) r /\
    ALL (\y. y IN dart H) (rev_ring H r)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NONTRIVIAL_RING_PROPER; REV_RING_DART; SCYCLE_CYCLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `diskF H (rev_ring H r) = {x | x IN dart H /\ diskFC H r x} /\
    {x | x IN dart H /\ diskFC H (rev_ring H r) x} = diskF H (r:(A)list)`
   (fun th -> UNDISCH_TAC `nontrivial_ring (H:(A)hypermap) m r` THEN
              SIMP_TAC[nontrivial_ring; th]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `z:A` THEN ASM_CASES_TAC `(z:A) IN dart H` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
  ASM_SIMP_TAC[DISKF_REV_RING; diskFC; diskF; DISKN_REV_RING;
               FBAND_REV_RING] THEN
  ASM_MESON_TAC[DISKN_SUBSET_DART]);;

(* ------------------------------------------------------------------------- *)
(* The ring colouring lemmas of revsnip.v.  The snip of snip.ml has identity *)
(* injections (SNIP_PATCH: patch H (snip_disk H r) (snip_rem H r) (\x. x)    *)
(* (\x. x) r (REVERSE r)), so these are stated for colourings of the darts   *)
(* of H rather than for Coq's snipd : Gd -> G.                               *)
(* ------------------------------------------------------------------------- *)

(* COLORABLE_FROM_RING (Coq colorable_from_ring): a ring trace of the disk   *)
(* and the matching trace of the remainder give a 4-colouring; the (<==)     *)
(* direction of COLORABLE_PATCH applied to SNIP_PATCH.                       *)
let COLORABLE_FROM_RING = prove
 (`!(H:(A)hypermap) r et.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     ~(r = []) /\ 2 <= LENGTH r /\
     ring_trace (snip_disk H r) r et /\
     ring_trace (snip_rem H r) (REVERSE r) (REVERSE (rot1 et))
     ==> four_colorable H`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `snip_disk H r:(A)hypermap`;
                 `snip_rem H r:(A)hypermap`; `\x:A. x`; `\x:A. x`;
                 `r:(A)list`; `REVERSE r:(A)list`] COLORABLE_PATCH) THEN
  ASM_SIMP_TAC[SNIP_PATCH] THEN ASM_MESON_TAC[]);;

(* RING_DISK_CLOSED (Coq ring_disk_closed): the ring traces of the remainder *)
(* are Kempe-closed.  The remainder is a ucycle_planar_plain_quasicubic map  *)
(* by PLANAR_SNIPR, PLAIN_PATCH, CUBIC_PATCH and the node-cycle clause of    *)
(* patch, so KEMPE_MAP applies directly (Coq transfers the colours to the    *)
(* disk side with rev_ring_cotrace instead); REVERSE r lies in the darts of  *)
(* snip_rem by SNIP_REM_COMPONENTS and RING_NOT_DISKE.                       *)
let RING_DISK_CLOSED = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ plain_hypermap H /\ cubic_hypermap H /\
     scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\ ~(r = []) /\
     2 <= LENGTH r
     ==> kempe_closed (ring_trace (snip_rem H r) (REVERSE r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `patch H (snip_disk H r) (snip_rem H r) (\x:A. x) (\x:A. x) r (REVERSE r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SNIP_PATCH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PATCH_CYCLE_R) THEN
  MATCH_MP_TAC KEMPE_MAP THEN
  ASM_REWRITE_TAC[ucycle_planar_plain_quasicubic; ucycle_plain_quasicubic;
                  plain_quasicubic] THEN
  SUBGOAL_THEN `set_of_list(REVERSE(r:(A)list)) = \z:A. MEM z (REVERSE r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_ELIM_THM; IN]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PLAIN_PATCH];
    MATCH_MP_TAC CUBIC_PATCH THEN ASM_MESON_TAC[LENGTH_REVERSE];
    ASM_MESON_TAC[PLANAR_SNIPR];
    ASM_SIMP_TAC[SNIP_REM_COMPONENTS; GSYM ALL_MEM; MEM_REVERSE;
                 IN_REDART] THEN
    ASM_MESON_TAC[RING_MEM_DART; RING_NOT_DISKE]]);;

(* In a bridgeless map, a dart and its edge image facing the ring project to *)
(* distinct ring darts.                                                      *)
let FPROJ_NEQ_BRIDGELESS = prove
 (`!(H:(A)hypermap) r x.
     bridgeless H /\ x IN dart H /\ fband H r x /\ fband H r (edge_map H x)
     ==> ~(fproj H r x = fproj H r (edge_map H x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;`r:(A)list`;`x:A`] FPROJ_IN_FBAND) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;`r:(A)list`;`edge_map (H:(A)hypermap) x`]
    FPROJ_IN_FBAND) THEN
  ASM_REWRITE_TAC[] THEN CFACE_TAC[]);;

(* NONTRIVIAL_CHORD_RING (Coq nontrivial_chord_ring): a chord x (x in diskE  *)
(* with x and edge x both facing the ring, their projections not adjacent on *)
(* it, and the disk of the chord ring nonempty) yields a smaller nontrivial  *)
(* ring chord_ring H r x.  The ring is decomposed into the two arcs          *)
(* (ROT_TO_ARC); the dart x3 after fproj x on the arc of the other chord     *)
(* ring is in the disk of that ring, hence outside this one                  *)
(* (DISKN_CHORD_RING), and off its face band because r is face-simple and    *)
(* the two arcs are disjoint (UNIQ_LIST_APPEND_DISJOINT).                    *)
let NONTRIVIAL_CHORD_RING = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ proper_ring H r /\
     x IN diskE H r /\ fband H r x /\ fband H r (edge_map H x) /\
     ~(fproj H r (edge_map H x) = nextc r (fproj H r x)) /\
     (?y. y IN diskF H (chord_ring H r x))
     ==> nontrivial_ring H 0 (chord_ring H r x) /\
     LENGTH (chord_ring H r x) < LENGTH r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART; IN; diskE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `MEM (fproj H r x) r /\ cface H x (fproj H r (x:A)) /\
    MEM (fproj H r (edge_map H x)) r /\
    cface H (edge_map H x) (fproj H r (edge_map H x)) /\
    uniq_list r /\ ~(fproj H r x = fproj H r (edge_map H x))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FPROJ_IN_FBAND; FACE_SIMPLE_UNIQ; scycle;
                  FPROJ_NEQ_BRIDGELESS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:(A)list`; `fproj H r (x:A)`; `fproj H r (edge_map H x:A)`]
    ROT_TO_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `p1:(A)list`
    (X_CHOOSE_THEN `p2:(A)list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY ABBREV_TAC
   [`x1 = fproj H r (x:A)`; `x2 = fproj H r (edge_map H x:A)`] THEN
  SUBGOAL_THEN
   `chord_ring H r x = CONS x (CONS x2 p2) /\
    chord_ring H r (edge_map H x) = CONS (edge_map H x) (CONS (x1:A) p1)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[chord_ring; CFT_PLAIN_EE]; ALL_TAC] THEN
  SUBGOAL_THEN `uniq_list (APPEND (CONS (x1:A) p1) (CONS x2 p2))`
  ASSUME_TAC THENL [ASM_MESON_TAC[UNIQ_ROT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p1:(A)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(x2:A = nextc r x1)` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\a b:A. nextc r a = b`; `i:num`; `r:(A)list`]
      LIST_CYCLE_ROT) THEN
    ASM_REWRITE_TAC[APPEND] THEN
    MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LIST_CYCLE_NEXTC THEN
      ASM_REWRITE_TAC[GSYM uniq_list] THEN ASM_MESON_TAC[MEM];
      SIMP_TAC[list_cycle; list_path; NOT_CONS_NIL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x3:A` (X_CHOOSE_THEN `t:(A)list`
    SUBST_ALL_TAC) o MATCH_MP
    (MESON[list_CASES] `~(l:(A)list = []) ==> ?h t. l = CONS h t`)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `LENGTH(r:(A)list) = LENGTH(rot_list i r)` SUBST1_TAC THENL
     [REWRITE_TAC[rot_list; LENGTH_APPEND; LENGTH_TAKE_LIST_COND;
                  LENGTH_DROP_LIST] THEN ARITH_TAC;
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC]] THEN
  SUBGOAL_THEN `MEM (x3:A) r` ASSUME_TAC THENL
   [MATCH_MP_TAC MEM_ARC_LIST THEN
    MAP_EVERY EXISTS_TAC [`x1:A`; `x2:A`] THEN ASM_REWRITE_TAC[MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x3:A) IN dart H /\ ~(x3 = x1) /\ ~MEM x3 (CONS x2 p2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[RING_MEM_DART];
      UNDISCH_TAC
       `uniq_list (APPEND (CONS x1 (CONS x3 t)) (CONS x2 p2):A list)` THEN
      REWRITE_TAC[uniq_list; APPEND; PAIRWISE; ALL] THEN MESON_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP UNIQ_LIST_APPEND_DISJOINT) THEN
      REWRITE_TAC[MEM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `CONS x (CONS x2 p2):A list`]
    NONTRIVIAL0P) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `chord_ring H r x = CONS x (CONS x2 p2):A list`)) THEN
    MATCH_MP_TAC ALL_DART_CHORD_RING THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `y:A` THEN ASM_MESON_TAC[]; EXISTS_TAC `x3:A`] THEN
  ASM_REWRITE_TAC[diskFC] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`; `x3:A`]
      DISKN_CHORD_RING) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `diskN H (CONS (edge_map H x) (CONS x1 (CONS x3 t))) (x3:A)`
     (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC RING_IN_DISKN THEN ASM_REWRITE_TAC[MEM]; CONV_TAC TAUT];
    ALL_TAC] THEN
  REWRITE_TAC[FBAND_MEM_IFF; MEM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `w:A` THEN STRIP_TAC THENL
   [UNDISCH_TAC `~(x3:A = x1)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SCYCLE_CFACE_EQ THEN
    MAP_EVERY EXISTS_TAC [`H:(A)hypermap`; `r:(A)list`] THEN
    ASM_MESON_TAC[CFT_TRANS];
    UNDISCH_TAC `~MEM (x3:A) (CONS x2 p2)` THEN REWRITE_TAC[MEM] THEN
    DISJ1_TAC THEN MATCH_MP_TAC SCYCLE_CFACE_EQ THEN
    MAP_EVERY EXISTS_TAC [`H:(A)hypermap`; `r:(A)list`] THEN
    ASM_MESON_TAC[];
    UNDISCH_TAC `~MEM (x3:A) (CONS x2 p2)` THEN REWRITE_TAC[MEM] THEN
    DISJ2_TAC THEN SUBGOAL_THEN `x3:A = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SCYCLE_CFACE_EQ THEN
    MAP_EVERY EXISTS_TAC [`H:(A)hypermap`; `r:(A)list`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_ARC_LIST THEN
    MAP_EVERY EXISTS_TAC [`x2:A`; `x1:A`] THEN ASM_REWRITE_TAC[MEM]]);;

(* RING_DISK_CHORD (Coq ring_disk_chord).  The projections are fproj r z = x *)
(* and fproj r (edge z) = y (FPROJ_CFACE, SIMPLE_FPROJ); some t lies in      *)
(* diskF r (DISKF_NONEMPTY); if t is in the face disk of chord_ring z that   *)
(* chord ring is the witness, otherwise DISKF_CHORD_RING puts t into the     *)
(* face disk of chord_ring (edge z); both cases by NONTRIVIAL_CHORD_RING and *)
(* SCYCLE_CHORD_RING.                                                        *)
let RING_DISK_CHORD = prove
 (`!(H:(A)hypermap) m r x y z.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\w. w IN dart H) r /\
     nontrivial_ring H m r /\
     MEM x r /\ MEM y r /\ z IN diskE H r /\ cface H x z /\ rlink H z y /\
     ~(y = nextc r x) /\ ~(x = nextc r y)
     ==> ?r'. scycle H (rlink H) r' /\ nontrivial_ring H 0 r' /\
     LENGTH r' < LENGTH r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `proper_ring (H:(A)hypermap) r` ASSUME_TAC THENL
   [ASM_MESON_TAC[NONTRIVIAL_RING_PROPER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(z:A) IN dart H /\ edge_map H z IN dart H /\ x IN dart H /\ y IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART; IN; diskE; EDGE_MAP_IN_DART;
                  RING_MEM_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cface H z x /\ cface H (edge_map H z) y /\
    fband H r z /\ fband H r (edge_map H z:A)`
  STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fproj H r z = x /\ fproj H r (edge_map H z) = (y:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FPROJ_CFACE; SIMPLE_FPROJ; scycle]; ALL_TAC] THEN
  SUBGOAL_THEN
   `edge_map H z IN diskE H r /\ edge_map H (edge_map H z) = (z:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKE_EDGE_FWD; IN; CFT_PLAIN_EE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `m:num`; `r:(A)list`] DISKF_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `t:A`) THEN
  ASM_CASES_TAC `?u:A. u IN diskF H (chord_ring H r z)` THENL
   [EXISTS_TAC `chord_ring H r (z:A)`;
    EXISTS_TAC `chord_ring H r (edge_map H z:A)`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC SCYCLE_CHORD_RING THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[CFT_PLAIN_EE];
     MATCH_MP_TAC NONTRIVIAL_CHORD_RING THEN ASM_REWRITE_TAC[]]) THEN
  EXISTS_TAC `t:A` THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `z:A`; `t:A`]
    DISKF_CHORD_RING) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[DISKF_SUBSET_DART; SUBSET]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN; NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[IN]);;
