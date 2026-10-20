(* ========================================================================= *)
(* 4CT/snip.ml                                                               *)
(*                                                                           *)
(* snip.v: cutting a planar hypermap along a ring.  Given a planar hypermap  *)
(* H and a simple R-cycle r, the darts reachable from r by contour paths     *)
(* that avoid r form the disk diskN; the disk map snip_disk and the          *)
(* remainder map snip_rem patch back to H (SNIP_PATCH) and are planar        *)
(* (PLANAR_SNIPD, PLANAR_SNIPR).  Planarity is used once, in DISKE_EDGE (the *)
(* strict disk is edge-closed): a face path crossing the ring would yield a  *)
(* Moebius path, contradicting the Jordan property.                          *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/coloring.ml";;
needs "4CT/jordan.ml";;
needs "4CT/kempe.ml";;
needs "4CT/patch.ml";;

(* ------------------------------------------------------------------------- *)
(* The disk of a ring: dlink steps are contour (clink) steps from darts off  *)
(* the ring; dreach is their reflexive-transitive closure (a list_path);     *)
(* diskN r collects the darts reachable from inverse node of a ring dart.    *)
(* ------------------------------------------------------------------------- *)

let dlink = new_definition
  `dlink (H:(A)hypermap) (r:(A)list) x y <=> ~MEM x r /\ clink H x y`;;

let dreach = new_definition
  `dreach (H:(A)hypermap) (r:(A)list) x y <=>
   ?p. list_path (dlink H r) x p /\ LAST (CONS x p) = y`;;

let dconnect = new_definition
  `dconnect (H:(A)hypermap) (r:(A)list) x y <=>
   dreach H r (inverse (node_map H) y) x`;;

let diskN = new_definition
  `diskN (H:(A)hypermap) (r:(A)list) x <=> EX (\y. dconnect H r x y) r`;;

let diskE = new_definition
  `diskE (H:(A)hypermap) (r:(A)list) x <=> diskN H r x /\ ~MEM x r`;;

let diskF = new_definition
  `diskF (H:(A)hypermap) (r:(A)list) x <=> diskN H r x /\ ~fband H r x`;;

let diskFC = new_definition
  `diskFC (H:(A)hypermap) (r:(A)list) x <=> ~diskN H r x /\ ~fband H r x`;;

let DREACH_REFL = prove
 (`!(H:(A)hypermap) r x. dreach H r x x`,
  REWRITE_TAC[dreach] THEN REPEAT GEN_TAC THEN
  EXISTS_TAC `[]:(A)list` THEN REWRITE_TAC[list_path; LAST]);;

let DREACH_STEP = prove
 (`!(H:(A)hypermap) r x y. dlink H r x y ==> dreach H r x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dreach] THEN
  EXISTS_TAC `[y:A]` THEN ASM_REWRITE_TAC[list_path; LAST; NOT_CONS_NIL]);;

let DREACH_TRANS = prove
 (`!(H:(A)hypermap) r x y z.
     dreach H r x y /\ dreach H r y z ==> dreach H r x z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dreach] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:(A)list` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `APPEND p q:(A)list` THEN
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LIST_PATH_APPEND; LAST_APPEND] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LAST (CONS (y:A) q) = z` THEN
  REWRITE_TAC[LAST]);;

let DISKN_DLINK = prove
 (`!(H:(A)hypermap) r x y. diskN H r x /\ dlink H r x y ==> diskN H r y`,
  REWRITE_TAC[diskN; GSYM EX_MEM; dconnect] THEN
  MESON_TAC[DREACH_TRANS; DREACH_STEP]);;

let DISKN_INVNODE = prove
 (`!(H:(A)hypermap) r x. diskN H r x ==> diskN H r (inverse (node_map H) x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `MEM (x:A) r` THENL
   [REWRITE_TAC[diskN; GSYM EX_MEM; dconnect] THEN ASM_MESON_TAC[DREACH_REFL];
    MATCH_MP_TAC DISKN_DLINK THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[dlink; clink] THEN DISJ1_TAC THEN
    MESON_TAC[PERMUTES_INVERSES; NODE_MAP_PERMUTES]]);;

let DISKN_FACE_OFFRING = prove
 (`!(H:(A)hypermap) r x. ~MEM x r /\ diskN H r x ==> diskN H r (face_map H x)`,
  MESON_TAC[DISKN_DLINK; dlink; clink]);;

let DISKN_DLINK_WITNESS = prove
 (`!(H:(A)hypermap) r x.
     diskN H r x
     ==> ?y0 p. MEM y0 r /\
       list_path (dlink H r) (inverse (node_map H) y0) p /\
                LAST (CONS (inverse (node_map H) y0) p) = x`,
  REWRITE_TAC[diskN; GSYM EX_MEM; dconnect; dreach] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A set closed under a permutation of a finite set is closed under its      *)
(* inverse (CLOSED_INVERSE_STEP, patch.ml); hence diskN is node-closed and   *)
(* diskF, diskFC are face-closed.                                            *)
(* ------------------------------------------------------------------------- *)

let DISKN_NODE_FWD = prove
 (`!(H:(A)hypermap) r x. x IN dart H /\ diskN H r x
   ==> diskN H r (node_map H x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`inverse(node_map(H:(A)hypermap))`;
    `dart(H:(A)hypermap)`;
    `diskN (H:(A)hypermap) r`; `node_map H (x:A)`] CLOSED_INVERSE_STEP) THEN
  ASM_SIMP_TAC[FINITE_DART; PERMUTES_INVERSE; NODE_MAP_PERMUTES;
    DISKN_INVNODE] THEN
  ASM_MESON_TAC[PERMUTES_INVERSES; NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE]);;

let DISKN_NODE_BWD = prove
 (`!(H:(A)hypermap) r x. diskN H r (node_map H x) ==> diskN H r x`,
  MESON_TAC[DISKN_INVNODE; PERMUTES_INVERSES; NODE_MAP_PERMUTES]);;

let DISKN_NODE_EQ = prove
 (`!(H:(A)hypermap) r x.
     x IN dart H ==> (diskN H r (node_map H x) <=> diskN H r x)`,
  MESON_TAC[DISKN_NODE_FWD; DISKN_NODE_BWD]);;

let RING_IN_DISKN = prove
 (`!(H:(A)hypermap) r x. x IN dart H /\ MEM x r ==> diskN H r x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `diskN H r (inverse (node_map H) (x:A))` ASSUME_TAC THENL
   [REWRITE_TAC[diskN; GSYM EX_MEM; dconnect] THEN ASM_MESON_TAC[DREACH_REFL];
    ASM_MESON_TAC[DISKN_NODE_FWD; PERMUTES_INVERSES; NODE_MAP_PERMUTES;
                  PERMUTES_IN_IMAGE; PERMUTES_INVERSE]]);;

let RING_MEM_DART = prove
 (`!(H:(A)hypermap) r x. ALL (\y. y IN dart H) r /\ MEM x r ==> x IN dart H`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

let RING_SUBSET_DISKN = prove
 (`!(H:(A)hypermap) r x. ALL (\y. y IN dart H) r /\ MEM x r ==> diskN H r x`,
  MESON_TAC[RING_IN_DISKN; RING_MEM_DART]);;

let DISKN_E = prove
 (`!(H:(A)hypermap) r x.
     x IN dart H ==> (diskN H r x <=> MEM x r \/ diskE H r x)`,
  REWRITE_TAC[diskE] THEN MESON_TAC[RING_IN_DISKN]);;

let RING_NOT_DISKE = prove
 (`!(H:(A)hypermap) r x. MEM x r ==> ~diskE H r x`,
  REWRITE_TAC[diskE] THEN MESON_TAC[]);;

let FACE_EDGE_IN_DISKN = prove
 (`!(H:(A)hypermap) r x. diskN H r x
   ==> diskN H r (face_map H (edge_map H x))`,
  MESON_TAC[DISKN_NODE_BWD; edgeK]);;

let DREACH_DART = prove
 (`!(H:(A)hypermap) r x y. dreach H r x y /\ x IN dart H ==> y IN dart H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dreach] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:(A)list` MP_TAC) MP_TAC) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`y:A`; `x:A`; `p:(A)list`] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_path; LAST_CLAUSES] THEN
  ASM_MESON_TAC[dlink; CLINK_DART]);;

let DISKN_SUBSET_DART = prove
 (`!(H:(A)hypermap) r x. ALL (\y. y IN dart H) r /\ diskN H r x
   ==> x IN dart H`,
  REWRITE_TAC[diskN; GSYM EX_MEM; dconnect; GSYM ALL_MEM] THEN
  MESON_TAC[DREACH_DART; PERMUTES_INVERSE; NODE_MAP_PERMUTES;
    PERMUTES_IN_IMAGE]);;

let FINITE_DISKN = prove
 (`!(H:(A)hypermap) r. ALL (\y. y IN dart H) r ==> FINITE (diskN H r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `dart(H:(A)hypermap)` THEN REWRITE_TAC[FINITE_DART] THEN
  REWRITE_TAC[SUBSET; IN] THEN ASM_MESON_TAC[DISKN_SUBSET_DART; IN]);;

let DISKN_FACE_BWD = prove
 (`!(H:(A)hypermap) r x.
     x IN dart H /\ ~fband H r x /\ diskN H r (face_map H x) ==> diskN H r x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`face_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`;
    `\y:A. diskN H r y /\ ~fband H r y`; `x:A`] CLOSED_INVERSE_STEP) THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES; FBAND_FACE_MAP_EQ] THEN
  DISCH_THEN MATCH_MP_TAC THEN MESON_TAC[DISKN_FACE_OFFRING; FBAND_MEM]);;

let DISKF_FACE = prove
 (`!(H:(A)hypermap) r x.
     x IN dart H ==> (diskF H r (face_map H x) <=> diskF H r x)`,
  REWRITE_TAC[diskF; FBAND_FACE_MAP_EQ] THEN
  MESON_TAC[DISKN_FACE_OFFRING; DISKN_FACE_BWD; FBAND_MEM]);;

let DISKFC_FACE = prove
 (`!(H:(A)hypermap) r x.
     x IN dart H ==> (diskFC H r (face_map H x) <=> diskFC H r x)`,
  REWRITE_TAC[diskFC; FBAND_FACE_MAP_EQ] THEN
  MESON_TAC[DISKN_FACE_OFFRING; DISKN_FACE_BWD; FBAND_MEM]);;

(* ------------------------------------------------------------------------- *)
(* Faces and simple cycles.                                                  *)
(* ------------------------------------------------------------------------- *)

let SCYCLE_PAIRWISE = prove
 (`!(H:(A)hypermap) e r. scycle H e r ==> PAIRWISE (\x y:A. ~(x = y)) r`,
  MESON_TAC[SCYCLE_SIMPLE; FACE_SIMPLE_PAIRWISE_GEN]);;

let SCYCLE_CFACE_EQ = prove
 (`!(H:(A)hypermap) r u y.
     scycle H (rlink H) r /\ MEM u r /\ MEM y r /\ cface H u y ==> u = y`,
  MESON_TAC[CFT_SCYCLE]);;

(* ------------------------------------------------------------------------- *)
(* The cyclic successor nextc r and predecessor prevc r of a list r: nextl a *)
(* s x is the element after x in s, wrapping round to a.  On a repetition-   *)
(* free list r, nextc r makes r a nextc-cycle and agrees with the step map   *)
(* of any cycle on r (NEXTC_CYCLE); prevc r is its inverse on r.             *)
(* ------------------------------------------------------------------------- *)

let nextl = define
  `(nextl (h:A) [] x = x) /\
   (nextl (h:A) (CONS y s) x =
      if x = y then (if s = [] then h else HD s) else nextl h s x)`;;

let nextc = new_definition
  `nextc (r:(A)list) x = if r = [] then x else nextl (HD r) r x`;;

let prevc = new_definition
  `prevc (r:(A)list) x = nextc (REVERSE r) x`;;

let NEXTL_MEM = prove
 (`!(s:(A)list) a x. MEM x s ==> MEM (nextl a s x) s \/ nextl a s x = a`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; nextl] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HD_MEM];
    ASM_MESON_TAC[]]);;

let NEXTC_MEM = prove
 (`!(r:(A)list) x. MEM x r ==> MEM (nextc r x) r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nextc] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NEXTL_MEM;
    HD_MEM]);;

let PREVC_MEM = prove
 (`!(r:(A)list) x. MEM x r ==> MEM (prevc r x) r`,
  REWRITE_TAC[prevc] THEN MESON_TAC[NEXTC_MEM; MEM_REVERSE]);;

let LIST_PATH_CONG_MEM = prove
 (`!(f:A->A) g s a.
     (!x. MEM x (CONS a s) ==> f x = g x)
     ==> (list_path (\x y. f x = y) a s <=> list_path (\x y. g x = y) a s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC LIST_PATH_MONO THENL
   [EXISTS_TAC `\x y. (f:A->A) x = y`; EXISTS_TAC `\x y. (g:A->A) x = y`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let LIST_CYCLE_CONG_MEM = prove
 (`!(f:A->A) g r.
     (!x. MEM x r ==> f x = g x)
     ==> (list_cycle (\x y. f x = y) r <=> list_cycle (\x y. g x = y) r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[list_cycle] THEN
  ASM_CASES_TAC `r:(A)list = []` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:A->A`; `g:A->A`; `r:(A)list`; `LAST r:A`]
    LIST_PATH_CONG_MEM) THEN
  ANTS_TAC THENL [REWRITE_TAC[MEM] THEN ASM_MESON_TAC[MEM_LAST]; SIMP_TAC[]]);;

let NEXTL_PATH = prove
 (`!(s:(A)list) b a.
     PAIRWISE (\x y. ~(x = y)) (CONS b s)
     ==> list_path (\x y. nextl a (CONS b s) x = y) b s /\
         nextl a (CONS b s) (LAST (CONS b s)) = a`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[list_path; LAST; nextl]; ALL_TAC] THEN
  REWRITE_TAC[PAIRWISE_DISTINCT_CONS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`h:A`; `a:A`]) THEN
  ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS] THEN STRIP_TAC THEN SUBGOAL_THEN
   `!x:A. MEM x (CONS h t)
     ==> nextl a (CONS b (CONS h t)) x = nextl a (CONS h t) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [nextl] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LAST_CLAUSES; list_path] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [nextl] THEN REWRITE_TAC[NOT_CONS_NIL; HD];
    MP_TAC(ISPECL [`nextl a (CONS b (CONS (h:A) t))`; `nextl a (CONS (h:A) t)`;
                   `t:(A)list`; `h:A`] LIST_PATH_CONG_MEM) THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MEM_LAST; NOT_CONS_NIL]]);;

let LIST_CYCLE_NEXTC = prove
 (`!(r:(A)list). PAIRWISE (\x y:A. ~(x = y)) r /\ ~(r = [])
     ==> list_cycle (\x y. nextc r x = y) r`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; list_cycle; nextc; HD; list_path] THEN
  DISCH_TAC THEN MP_TAC(ISPECL [`t:(A)list`; `h:A`; `h:A`] NEXTL_PATH) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let LIST_PATH_FUN_STEP = prove
 (`!(e:A->A->bool) (g:A->A) s a.
     list_path e a s /\ list_path (\x y. g x = y) a s
     ==> !z. MEM z (CONS a s) /\ ~(z = LAST (CONS a s)) ==> e z (g z)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_path; LAST_CLAUSES; MEM] THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

let LIST_CYCLE_FUN_STEP = prove
 (`!(e:A->A->bool) (g:A->A) r z.
     list_cycle e r /\ list_cycle (\x y. g x = y) r /\ MEM z r ==> e z (g z)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THEN
  REWRITE_TAC[MEM; list_cycle; NOT_CONS_NIL; list_path] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`e:A->A->bool`; `g:A->A`; `t:(A)list`; `h:A`]
    LIST_PATH_FUN_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
  ASM_CASES_TAC `z:A = LAST (CONS h t)` THEN ASM_REWRITE_TAC[MEM]);;

let CYCLE_NEXTC_STEP = prove
 (`!(e:A->A->bool) r z.
     list_cycle e r /\ PAIRWISE (\x y:A. ~(x = y)) r /\ MEM z r
     ==> e z (nextc r z)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`e:A->A->bool`; `nextc (r:(A)list)`; `r:(A)list`; `z:A`]
    LIST_CYCLE_FUN_STEP) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIST_CYCLE_NEXTC THEN
  ASM_MESON_TAC[MEM]);;

let NEXTC_CYCLE = prove
 (`!(f:A->A) r x.
     list_cycle (\x y. f x = y) r /\ PAIRWISE (\x y. ~(x = y)) r /\ MEM x r
     ==> nextc r x = f x`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`\x y:A. (f:A->A) x = y`; `r:(A)list`; `x:A`]
    CYCLE_NEXTC_STEP) THEN ASM_REWRITE_TAC[]);;

let NEXTC_EL = prove
 (`!(r:(A)list) i. PAIRWISE (\x y. ~(x = y)) r /\ i < LENGTH r
      ==> nextc r (EL i r) = EL ((i + 1) MOD LENGTH r) r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_CYCLE_EL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIST_CYCLE_NEXTC THEN
  ASM_MESON_TAC[LENGTH; LT]);;

(* A cycle read backwards is a cycle of the converse relation, so prevc r    *)
(* inverts nextc r on r.                                                     *)

let LIST_PATH_REVERSE = prove
 (`!(e:A->A->bool) s a b.
     list_path e a (APPEND s [b])
     ==> list_path (\x y. e y x) b (APPEND (REVERSE s) [a])`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[APPEND; list_path; REVERSE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPECL [`h:A`; `b:A`]) THEN
  ASM_REWRITE_TAC[LIST_PATH_APPEND; list_path] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LAST_APPEND; NOT_CONS_NIL; LAST;
              APPEND_EQ_NIL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let LIST_CYCLE_REVERSE = prove
 (`!(e:A->A->bool) r. list_cycle e r ==> list_cycle (\x y. e y x) (REVERSE r)`,
  GEN_TAC THEN GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THEN
  REWRITE_TAC[list_cycle; NOT_CONS_NIL] THEN
  ASM_CASES_TAC `t:(A)list = []` THENL
   [ASM_REWRITE_TAC[REVERSE; APPEND; LAST; list_path; NOT_CONS_NIL] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SNOC_DECOMP) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(A)list` (X_CHOOSE_THEN `b:A` SUBST1_TAC)) THEN
  REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND; APPEND_NIL; NOT_CONS_NIL;
              APPEND_EQ_NIL; REVERSE_EQ_EMPTY; LAST_APPEND; LAST_CLAUSES;
              list_path] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LAST_APPEND; NOT_CONS_NIL;
              LAST_CLAUSES] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[LIST_PATH_REVERSE]);;

let NEXTC_PREVC = prove
 (`!(r:(A)list) x. PAIRWISE (\x y. ~(x = y)) r /\ MEM x r
   ==> nextc r (prevc r x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[prevc] THEN
  SUBGOAL_THEN `~(r:(A)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x y:A. nextc r y = x`; `REVERSE(r:(A)list)`; `x:A`]
    CYCLE_NEXTC_STEP) THEN
  ASM_SIMP_TAC[PAIRWISE_DISTINCT_REVERSE; MEM_REVERSE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`\x y:A. nextc r x = y`; `r:(A)list`] LIST_CYCLE_REVERSE) THEN
  ASM_SIMP_TAC[LIST_CYCLE_NEXTC]);;

let PREVC_NEXTC = prove
 (`!(r:(A)list) x. PAIRWISE (\x y. ~(x = y)) r /\ MEM x r
   ==> prevc r (nextc r x) = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r:(A)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x y:A. prevc r y = x`; `r:(A)list`; `x:A`]
    CYCLE_NEXTC_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`\x y:A. nextc (REVERSE r) x = y`; `REVERSE(r:(A)list)`]
    LIST_CYCLE_REVERSE) THEN
  ASM_SIMP_TAC[LIST_CYCLE_NEXTC; PAIRWISE_DISTINCT_REVERSE; REVERSE_EQ_EMPTY;
               REVERSE_REVERSE; GSYM prevc]);;

let NEXTC_INJ = prove
 (`!(r:(A)list) x y. PAIRWISE (\x y:A. ~(x = y)) r /\ MEM x r /\ MEM y r /\
                     nextc r x = nextc r y ==> x = y`,
  MESON_TAC[PREVC_NEXTC]);;

let CYCLE_PREVC_STEP = prove
 (`!(e:A->A->bool) r x.
     list_cycle e r /\ PAIRWISE (\x y:A. ~(x = y)) r /\ MEM x r
       ==> e (prevc r x) x`,
  MESON_TAC[CYCLE_NEXTC_STEP; PREVC_MEM; NEXTC_PREVC]);;

let LIST_CYCLE_PREVC_REVERSE = prove
 (`!(r:(A)list). PAIRWISE (\x y:A. ~(x = y)) r /\ ~(r = [])
     ==> list_cycle (\x y. prevc r x = y) (REVERSE r)`,
  REWRITE_TAC[prevc] THEN
  SIMP_TAC[LIST_CYCLE_NEXTC; PAIRWISE_DISTINCT_REVERSE; REVERSE_EQ_EMPTY]);;

(* Rotating a cycle: the cycle through y, read from y, ends at prevc r y.    *)

let LIST_CYCLE_ROTATE = prove
 (`!(e:A->A->bool) l1 y l2.
     list_cycle e (APPEND l1 (CONS y l2))
       ==> list_cycle e (CONS y (APPEND l2 l1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[list_cycle; NOT_CONS_NIL; APPEND_EQ_NIL; LIST_PATH_APPEND;
              list_path; LAST_APPEND] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LAST_APPEND; NOT_CONS_NIL] THEN
  ASM_CASES_TAC `l1:(A)list = []` THEN ASM_REWRITE_TAC[APPEND; list_path;
    LAST] THEN
  ASM_CASES_TAC `l2:(A)list = []` THEN ASM_REWRITE_TAC[LAST; list_path] THEN
  MESON_TAC[]);;

let LIST_PATH_ITERLIST_FUN = prove
 (`!(f:A->A) n x. list_path (\a b. f a = b) x (iterlist n f x)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[iterlist; list_path]);;

let MEM_ITERLIST_IMP = prove
 (`!(f:A->A) n x y. MEM y (iterlist n f x) ==> ?k. y = ITER k f x`,
  REWRITE_TAC[MEM_ITERLIST] THEN MESON_TAC[]);;

let ITERLIST_OF_PATH = prove
 (`!(g:A->A) s a. list_path (\x y. g x = y) a s
   ==> iterlist (LENGTH s) g a = s`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[list_path; LENGTH; iterlist; CONS_11]);;

let RING_CHAIN_COVERS = prove
 (`!(r:(A)list) y. PAIRWISE (\x y:A. ~(x = y)) r /\ MEM y r
    ==> !t. MEM t r ==> MEM t (CONS y (iterlist (LENGTH r - 1) (nextc r) y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:(A)list` (X_CHOOSE_THEN `l2:(A)list`
    SUBST_ALL_TAC) o MATCH_MP MEM_SPLIT) THEN
  MP_TAC(ISPECL [`\a b:A. nextc (APPEND l1 (CONS y l2)) a = b`;
                 `l1:(A)list`; `y:A`; `l2:(A)list`] LIST_CYCLE_ROTATE) THEN
  ASM_SIMP_TAC[LIST_CYCLE_NEXTC; NOT_CONS_NIL; APPEND_EQ_NIL] THEN
  REWRITE_TAC[list_cycle; NOT_CONS_NIL; list_path] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[ETA_AX] o MATCH_MP ITERLIST_OF_PATH o
             CONJUNCT2) THEN
  SUBGOAL_THEN `LENGTH (APPEND l1 (CONS (y:A) l2)) - 1 = LENGTH (APPEND l2 l1)`
    SUBST1_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]);;

let RLINK_NEXTC_EQ = prove
 (`!(H:(A)hypermap) r z y.
     scycle H (rlink H) r /\ MEM z r /\ MEM y r /\ rlink H z y
       ==> nextc r z = y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_CYCLE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_PAIRWISE) THEN
  MP_TAC(ISPECL [`rlink (H:(A)hypermap)`; `r:(A)list`;
    `z:A`] CYCLE_NEXTC_STEP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CFACE_TAC[NEXTC_MEM]);;

let RLINK_PREVC = prove
 (`!(H:(A)hypermap) r x. scycle H (rlink H) r /\ MEM x r
   ==> rlink H (prevc r x) x`,
  MESON_TAC[CYCLE_PREVC_STEP; SCYCLE_CYCLE; SCYCLE_PAIRWISE]);;

let RING_ROTATE_TO2 = prove
 (`!(H:(A)hypermap) r y.
     scycle H (rlink H) r /\ ALL (\t. t IN dart H) r /\ MEM y r
     ==> ?r1. list_path (rlink H) y r1 /\ ALL (\t. MEM t r) (CONS y r1) /\
              ALL (\t. t IN dart H) (CONS y r1) /\
              PAIRWISE (\a b:A. ~(a = b)) (CONS y r1) /\
              LAST (CONS y r1) = prevc r y /\
              (!t. MEM t r ==> MEM t (CONS y r1))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP SCYCLE_PAIRWISE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCYCLE_CYCLE) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l1:(A)list` (X_CHOOSE_THEN `l2:(A)list`
    SUBST_ALL_TAC) o MATCH_MP MEM_SPLIT) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP LIST_CYCLE_ROTATE) THEN DISCH_TAC THEN
  EXISTS_TAC `APPEND l2 l1:(A)list` THEN
  SUBGOAL_THEN `MEM (LAST (CONS y (APPEND l2 l1))) (APPEND l1 (CONS (y:A) l2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `CONS (y:A) (APPEND l2 l1)` MEM_LAST) THEN
    REWRITE_TAC[NOT_CONS_NIL; MEM; MEM_APPEND] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[list_cycle; NOT_CONS_NIL; list_path]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; MEM; MEM_APPEND] THEN MESON_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; MEM; MEM_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; MEM; MEM_APPEND]) THEN
      ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE_DISTINCT_APPEND;
      PAIRWISE_DISTINCT_CONS;
                                MEM; MEM_APPEND]) THEN
    ASM_REWRITE_TAC[PAIRWISE_DISTINCT_APPEND; PAIRWISE_DISTINCT_CONS;
                    MEM; MEM_APPEND] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `prevc (APPEND l1 (CONS (y:A) l2))
                      (nextc (APPEND l1 (CONS y l2))
                             (LAST (CONS y (APPEND l2 l1))))` THEN
    CONJ_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PREVC_NEXTC;
      AP_TERM_TAC] THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC LIST_CYCLE_HD THEN
    MATCH_MP_TAC(ISPECL [`\a b:A. nextc (APPEND l1 (CONS y l2)) a = b`;
      `l1:(A)list`; `y:A`; `l2:(A)list`] LIST_CYCLE_ROTATE) THEN
    MATCH_MP_TAC LIST_CYCLE_NEXTC THEN ASM_REWRITE_TAC[APPEND_EQ_NIL;
      NOT_CONS_NIL];
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Face paths (list paths of face steps) and the ring contour link rclink:   *)
(* a face step, except on the ring where it jumps to the next ring face.     *)
(* ------------------------------------------------------------------------- *)

let rclink = new_definition
  `rclink (H:(A)hypermap) (r:(A)list) t =
     face_map H (if MEM t r then edge_map H t else t)`;;

let FACEPATH_CFACE = prove
 (`!(H:(A)hypermap) c t.
     list_path (\a b. face_map H a = b) t c
     ==> !u v. MEM u (CONS t c) /\ MEM v (CONS t c) ==> cface H u v`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LIST_PATH_MEM_ORBIT) THEN
  REWRITE_TAC[ETA_AX; GSYM face; GSYM cface; MEM] THEN
  MESON_TAC[CFACE_REFL; CFACE_SYM_GEN; CFT_TRANS]);;

let FACEPATH_CLINK = prove
 (`!(H:(A)hypermap) c t.
     list_path (\a b. face_map H a = b) t c ==> list_path (clink H) t c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `\a b. face_map (H:(A)hypermap) a = b` THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[clink]);;

let RCLINK_CLINK = prove
 (`!(H:(A)hypermap) r t. clink H t (rclink H r t)`,
  REWRITE_TAC[rclink; clink] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[edgeK]);;

let RCLINK_CLINK_PATH = prove
 (`!(H:(A)hypermap) r c t.
     list_path (\a b. rclink H r a = b) t c ==> list_path (clink H) t c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `\a b. rclink (H:(A)hypermap) r a = b` THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[RCLINK_CLINK]);;

let DLINK_CLINK_PATH = prove
 (`!(H:(A)hypermap) r c t.
     list_path (dlink H r) t c ==> list_path (clink H) t c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `dlink (H:(A)hypermap) r` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[dlink]);;

let CFACE_FACEPATH = prove
 (`!(H:(A)hypermap) x y. cface H x y
     ==> ?p. list_path (\a b. face_map H a = b) x p /\ LAST (CONS x p) = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  EXISTS_TAC `iterlist n (face_map H) (x:A)` THEN
  REWRITE_TAC[LIST_PATH_ITERLIST_FUN; LAST_ITERLIST]);;

let FACE_CYCLE_MEM_CFACE = prove
 (`!(H:(A)hypermap) c t.
     list_path (\a b. face_map H a = b) t c /\ face_map H (LAST (CONS t c)) = t
     ==> !u. cface H t u ==> MEM u (CONS t c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`face_map(H:(A)hypermap)`; `{v:A | MEM v (CONS t c)}`; `t:A`]
    ORBIT_IN_CLOSED) THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LIST_PATH_F_MEM) THEN ASM_MESON_TAC[MEM];
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[cface; face]]);;

let FACEPATH_RCLINK = prove
 (`!(H:(A)hypermap) r c s.
     scycle H (rlink H) r /\ list_path (\a b. face_map H a = b) s c /\
     PAIRWISE (\a b:A. ~(a = b)) (CONS s c) /\ MEM (LAST (CONS s c)) r
     ==> list_path (\a b. rclink H r a = b) s c`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[list_path] THEN
  X_GEN_TAC `s:A` THEN REWRITE_TAC[PAIRWISE_DISTINCT_CONS; LAST_CLAUSES] THEN
  STRIP_TAC THEN SUBGOAL_THEN `~MEM (s:A) r` ASSUME_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `s:A = LAST (CONS h t)` MP_TAC THENL
     [MATCH_MP_TAC SCYCLE_CFACE_EQ THEN
      MAP_EVERY EXISTS_TAC [`H:(A)hypermap`; `r:(A)list`] THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`H:(A)hypermap`; `CONS (h:A) t`;
        `s:A`] FACEPATH_CFACE) THEN
      ASM_REWRITE_TAC[list_path] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[MEM; MEM_LAST; NOT_CONS_NIL];
      ASM_MESON_TAC[MEM_LAST; NOT_CONS_NIL]];
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[rclink];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS]]]);;

(* ------------------------------------------------------------------------- *)
(* The disk extends along an off-ring face path; an off-contour clink path   *)
(* leaves an rclink-closed contour S by a node step (OFFCONTOUR_PATH); a     *)
(* contour closing up at z with an off-contour path from a dart whose node   *)
(* lies on it is a Moebius path, impossible in a planar hypermap.            *)
(* ------------------------------------------------------------------------- *)

let DISKE_OF_FACEPATH = prove
 (`!(H:(A)hypermap) r p x.
     diskN H r x /\ list_path (\a b. face_map H a = b) x p /\
     ALL (\t. ~MEM t r) (CONS x p)
     ==> diskE H r (LAST (CONS x p))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_path; LAST_CLAUSES; ALL] THENL [MESON_TAC[diskE];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL] THEN ASM_MESON_TAC[DISKN_FACE_OFFRING]);;

let OFFCONTOUR_PATH = prove
 (`!(H:(A)hypermap) r S xend p a.
     (!t. MEM t S ==> MEM (rclink H r t) S) /\
     ~MEM (face_map H (edge_map H xend)) S /\
     EX (\t. MEM t S) (CONS a p) /\
     list_path (dlink H r) a p /\ LAST (CONS a p) = xend
     ==> ?x1 p'. MEM (node_map H x1) S /\
                 list_path (clink H) x1 p' /\
                 LAST (CONS x1 p') = face_map H (edge_map H xend) /\
                 ALL (\t. ~MEM t S) (CONS x1 p')`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  X_GEN_TAC `a:A` THEN REWRITE_TAC[LAST_CLAUSES; list_path] THENL
   [STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`face_map H (edge_map H (xend:A))`; `[]:(A)list`] THEN
    UNDISCH_TAC `EX (\t:A. MEM t S) [a]` THEN
    ASM_REWRITE_TAC[EX; list_path; LAST; ALL; edgeK];
    POP_ASSUM(LABEL_TAC "ih") THEN STRIP_TAC THEN
    ASM_CASES_TAC `EX (\t:A. MEM t S) (CONS h t)` THENL
     [REMOVE_THEN "ih" (MP_TAC o SPEC `h:A`) THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
    SUBGOAL_THEN `MEM (a:A) S` ASSUME_TAC THENL
     [UNDISCH_TAC `EX (\t:A. MEM t S) (CONS a (CONS h t))` THEN
      UNDISCH_TAC `~EX (\t:A. MEM t S) (CONS h t)` THEN
      REWRITE_TAC[EX] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:A) = node_map H h` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `dlink H r (a:A) h` THEN REWRITE_TAC[dlink; clink] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `MEM (h:A) S` MP_TAC THENL
       [SUBGOAL_THEN `h = rclink H r (a:A)` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[rclink];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        UNDISCH_TAC `~EX (\t:A. MEM t S) (CONS h t)` THEN REWRITE_TAC[EX] THEN
        MESON_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `~EX (\t:A. MEM t S) (CONS h t)` THEN
    REWRITE_TAC[NOT_EX; ALL] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`h:A`; `APPEND t [face_map H (edge_map H (xend:A))]`] THEN
    ASM_REWRITE_TAC[LIST_PATH_APPEND; GSYM(CONJUNCT2 APPEND); LAST_APPEND;
                    NOT_CONS_NIL; LAST; ALL_APPEND; ALL; list_path; clink;
                    edgeK; APPEND_EQ_NIL] THEN
    ASM_MESON_TAC[DLINK_CLINK_PATH]]);;

let MOEBIUS_CONTRA = prove
 (`!(H:(A)hypermap) x1 c1 z c.
     planar_hypermap H /\
     list_path (clink H) x1 c1 /\
     clink H (LAST (CONS x1 c1)) (face_map H (edge_map H z)) /\
     list_path (clink H) (face_map H (edge_map H z)) c /\
     LAST (CONS (face_map H (edge_map H z)) c) = z /\
     MEM (node_map H x1) (CONS (face_map H (edge_map H z)) c) /\
     PAIRWISE (\a b:A. ~(a = b))
              (CONS x1 (APPEND c1 (CONS (face_map H (edge_map H z)) c)))
     ==> F`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PLANAR_JORDAN) THEN REWRITE_TAC[jordan] THEN
  DISCH_THEN(MP_TAC o SPEC
    `CONS (x1:A) (APPEND c1 (CONS (face_map H (edge_map H z)) c))`) THEN
  ASM_REWRITE_TAC[moebius_path; NOT_CONS_NIL; HD; TL; LIST_PATH_APPEND] THEN
  ASM_REWRITE_TAC[list_path; GSYM(CONJUNCT2 APPEND); LAST_APPEND;
                  NOT_CONS_NIL; NODE_MAP_INVERSE; o_THM] THEN
  MATCH_MP_TAC MEM2_SPLICE_Z THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The ring contour: following the ring from y along rlink steps y, w, ...   *)
(* and inserting the face arcs face(edge y) -> w gives an rclink path that   *)
(* covers the ring darts, is repetition free and stays in the ring band.     *)
(* ------------------------------------------------------------------------- *)

let FBAND_RING_NOT_CFACE = prove
 (`!(H:(A)hypermap) r r1 y u.
     scycle H (rlink H) r /\ MEM y r /\ ~MEM y r1 /\ ALL (\t. MEM t r) r1 /\
     fband H r1 u ==> ~cface H y u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FBAND_MEM_IFF; GSYM ALL_MEM] THEN
  DISCH_THEN(REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC)
    (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC)) THEN
  DISCH_TAC THEN SUBGOAL_THEN `y:A = v` SUBST_ALL_TAC THENL
   [CFACE_TAC[]; ASM_MESON_TAC[]]);;

let RING_CONTOUR = prove
 (`!(H:(A)hypermap) r r1 y.
     scycle H (rlink H) r /\ ALL (\t. t IN dart H) r /\ MEM y r /\
     ALL (\t. MEM t r) r1 /\ list_path (rlink H) y r1 /\
     PAIRWISE (\a b:A. ~(a = b)) r1
     ==> ?c2. list_path (\a b. rclink H r a = b) y c2 /\
              PAIRWISE (\a b:A. ~(a = b)) c2 /\
              LAST (CONS y c2) = LAST (CONS y r1) /\
              (!t. MEM t r1 ==> MEM t c2) /\
              (!t. fband H c2 t ==> fband H r1 t)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `y:A` THENL
   [STRIP_TAC THEN EXISTS_TAC `[]:(A)list` THEN
    REWRITE_TAC[list_path; PAIRWISE; MEM; FBAND_NIL];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; list_path; PAIRWISE_DISTINCT_CONS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(A)list` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `fe = face_map H (edge_map H (y:A))` THEN
  SUBGOAL_THEN `cface H (fe:A) h` MP_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:(A)list` STRIP_ASSUME_TAC o
             MATCH_MP CFACE_FACEPATH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIST_PATH_SHORTEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `MEM (h:A) (CONS fe c1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_LAST; NOT_CONS_NIL]; ALL_TAC] THEN
  SUBGOAL_THEN `!u:A. MEM u (CONS fe c1) ==> cface H u h` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `c1:(A)list`; `fe:A`] FACEPATH_CFACE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:A. MEM u c2 ==> ~cface H h u` ASSUME_TAC THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL
     [`H:(A)hypermap`; `r:(A)list`; `t:(A)list`; `h:A`; `u:A`]
     FBAND_RING_NOT_CFACE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FBAND_MEM];
    ALL_TAC] THEN
  EXISTS_TAC `CONS (fe:A) (APPEND c1 c2)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[list_path; LIST_PATH_APPEND] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "fe" THEN ASM_REWRITE_TAC[rclink];
      MATCH_MP_TAC FACEPATH_RCLINK THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM(CONJUNCT2 APPEND); PAIRWISE_DISTINCT_APPEND] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CFACE_SYM_GEN];
    UNDISCH_TAC `LAST (CONS (h:A) c2) = LAST (CONS h t)` THEN
    ASM_REWRITE_TAC[LAST_CLAUSES; GSYM(CONJUNCT2 APPEND); LAST_APPEND] THEN
    REWRITE_TAC[LAST];
    REWRITE_TAC[MEM; MEM_APPEND] THEN ASM_MESON_TAC[MEM];
    X_GEN_TAC `u:A` THEN REWRITE_TAC[FBAND_CONS; FBAND_APPEND] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_MESON_TAC[CFT_TRANS; MEM];
      DISJ1_TAC THEN UNDISCH_TAC `fband H c1 (u:A)` THEN
      REWRITE_TAC[FBAND_MEM_IFF] THEN ASM_MESON_TAC[CFT_TRANS; MEM];
      DISJ2_TAC THEN ASM_SIMP_TAC[]]]);;

let CONTOUR_FROM_Y = prove
 (`!(H:(A)hypermap) r y z zz a1.
     scycle H (rlink H) r /\ ALL (\t. t IN dart H) r /\
     MEM y r /\ MEM z r /\ rlink H z y /\ face_map H (edge_map H z) = zz /\
     list_path (\a b. face_map H a = b) zz a1 /\ LAST (CONS zz a1) = y /\
     PAIRWISE (\a b:A. ~(a = b)) (CONS zz a1)
     ==> ?c. list_path (\a b. rclink H r a = b) zz c /\
             LAST (CONS zz c) = z /\
             PAIRWISE (\a b:A. ~(a = b)) (CONS zz c) /\
             (!t. MEM t r ==> MEM t (CONS zz c)) /\
             (!t. MEM t (CONS zz c) ==> MEM t (CONS zz a1) \/ ~cface H y t)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `prevc r (y:A) = z` ASSUME_TAC THENL
   [ASM_MESON_TAC[RLINK_NEXTC_EQ; PREVC_NEXTC; SCYCLE_PAIRWISE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `y:A`] RING_ROTATE_TO2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(A)list`
    (STRIP_ASSUME_TAC o REWRITE_RULE[ALL; PAIRWISE_DISTINCT_CONS])) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `r1:(A)list`; `y:A`]
    RING_CONTOUR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!u:A. MEM u c2 ==> ~cface H y u` ASSUME_TAC THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL
     [`H:(A)hypermap`; `r:(A)list`; `r1:(A)list`; `y:A`; `u:A`]
     FBAND_RING_NOT_CFACE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FBAND_MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:A. MEM u (CONS zz a1) ==> cface H u y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `a1:(A)list`; `zz:A`] FACEPATH_CFACE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM_LAST; NOT_CONS_NIL];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (y:A) (CONS zz a1)` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `LAST (CONS (zz:A) a1) = y`)) THEN
    MATCH_MP_TAC MEM_LAST THEN REWRITE_TAC[NOT_CONS_NIL];
    ALL_TAC] THEN
  EXISTS_TAC `APPEND a1 c2:(A)list` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIST_PATH_APPEND] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACEPATH_RCLINK THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `LAST (CONS (y:A) c2) = z` THEN
    ASM_REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LAST_APPEND] THEN
    REWRITE_TAC[LAST];
    REWRITE_TAC[GSYM(CONJUNCT2 APPEND); PAIRWISE_DISTINCT_APPEND] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:A` THEN REPEAT DISCH_TAC THEN
    CFACE_TAC[];
    X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (u:A) (CONS y r1)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `MEM (y:A) (CONS zz a1)` THEN
    UNDISCH_TAC `!t:A. MEM t r1 ==> MEM t c2` THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    X_GEN_TAC `u:A` THEN UNDISCH_TAC `!u:A. MEM u c2 ==> ~cface H y u` THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* DISKE_EDGE (Gonthier diskE_edge).  For x in the strict disk, a face path  *)
(* from face(edge x) back to edge x either avoids the ring (then edge x is   *)
(* in the disk) or meets it at y; with z = prevc r y and zz = face(edge z)   *)
(* on that face, the arc from zz to edge x avoids the ring unless y lies on  *)
(* it, in which case the contour through zz, the ring and the dlink path     *)
(* into the disk form a Moebius path, contradicting planarity.               *)
(* ------------------------------------------------------------------------- *)

let DISKE_EDGE_MOEBIUS = prove
 (`!(H:(A)hypermap) r x y z xx zz q1 q2.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\t. t IN dart H) r /\
     diskN H r x /\ ~MEM x r /\ MEM y r /\ MEM z r /\ rlink H z y /\
     face_map H (edge_map H x) = xx /\ face_map H (edge_map H z) = zz /\
     list_path (\a b. face_map H a = b) xx (APPEND q1 (CONS zz q2)) /\
     PAIRWISE (\a b:A. ~(a = b)) (CONS xx (APPEND q1 (CONS zz q2))) /\
     MEM y (CONS zz q2)
     ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LIST_PATH_APPEND;
              PAIRWISE_DISTINCT_APPEND; list_path] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u:A. MEM u (CONS xx q1) \/ MEM u (CONS zz q2) ==> cface H u y`
  (LABEL_TAC "cfy") THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `APPEND q1 (CONS (zz:A) q2)`; `xx:A`]
      FACEPATH_CFACE) THEN
    ASM_REWRITE_TAC[LIST_PATH_APPEND; list_path; GSYM(CONJUNCT2 APPEND);
                    MEM_APPEND] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\a b. face_map (H:(A)hypermap) a = b`; `q2:(A)list`; `zz:A`;
                 `y:A`] LIST_PATH_SPLIT_AT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:(A)list` (X_CHOOSE_THEN `m2:(A)list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `PAIRWISE (\a b:A. ~(a = b)) (CONS zz a1)` ASSUME_TAC THENL
   [UNDISCH_TAC `PAIRWISE (\a b:A. ~(a = b)) (CONS zz q2)` THEN
    ASM_REWRITE_TAC[PAIRWISE_DISTINCT_APPEND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`H:(A)hypermap`; `r:(A)list`; `y:A`; `z:A`; `zz:A`; `a1:(A)list`]
   CONTOUR_FROM_Y) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t:A. MEM t (CONS xx q1) ==> ~MEM t (CONS zz c)`
  (LABEL_TAC "m1dis") THENL
   [X_GEN_TAC `t:A` THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `MEM t (CONS (zz:A) a1) \/ ~cface H y t` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~MEM t (CONS (zz:A) q2) /\ cface H t y` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `CONS (zz:A) q2 = APPEND (CONS zz a1) m2` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; MEM_APPEND]) THEN
    MESON_TAC[CFACE_SYM_GEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `rclink H r (z:A) = zz` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rclink]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:A. MEM t (CONS zz c) ==> MEM (rclink H r t) (CONS zz c)`
  (LABEL_TAC "closed") THENL
   [MP_TAC(ISPECL [`rclink (H:(A)hypermap) r`; `zz:A`; `c:(A)list`]
      LIST_PATH_F_MEM) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `rclink H r (z:A) = zz` THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`] DISKN_DLINK_WITNESS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A` (X_CHOOSE_THEN `p:(A)list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `MEM (inverse (node_map H) (y0:A)) (CONS zz c)` ASSUME_TAC THENL
   [SUBGOAL_THEN `inverse (node_map H) (y0:A) = rclink H r y0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[NODE_MAP_INVERSE; o_THM; rclink]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `CONS (zz:A) c`; `x:A`;
                 `p:(A)list`; `inverse (node_map H) (y0:A)`]
    OFFCONTOUR_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[EX] THEN USE_THEN "m1dis" MATCH_MP_TAC THEN
    REWRITE_TAC[MEM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:A` (X_CHOOSE_THEN `p':(A)list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `list_path (clink H) (x1:A) (APPEND p' q1) /\
    clink H (LAST (CONS x1 (APPEND p' q1))) zz /\
    (!t. MEM t (CONS x1 (APPEND p' q1)) ==> ~MEM t (CONS zz c))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LIST_PATH_APPEND; GSYM(CONJUNCT2 APPEND); LAST_APPEND;
                MEM_APPEND] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FACEPATH_CLINK THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(if q1 = [] then xx else LAST q1) = LAST (CONS (xx:A) q1)`
        SUBST1_TAC THENL [REWRITE_TAC[LAST]; ASM_REWRITE_TAC[clink]];
      UNDISCH_TAC `ALL (\t:A. ~MEM t (CONS zz c)) (CONS x1 p')` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "m1dis" MP_TAC THEN
      REWRITE_TAC[MEM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`clink (H:(A)hypermap)`; `x1:A`; `APPEND p' q1:(A)list`]
    LIST_PATH_SHORTEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(A)list` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(ISPECL
   [`H:(A)hypermap`; `x1:A`; `c1:(A)list`; `z:A`; `c:(A)list`]
   MOEBIUS_CONTRA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `c:(A)list`; `zz:A`]
      RCLINK_CLINK_PATH) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM(CONJUNCT2 APPEND); PAIRWISE_DISTINCT_APPEND] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `!y:A. MEM y (CONS x1 c1) ==> MEM y (CONS x1 (APPEND p' q1))` THEN
    UNDISCH_TAC
     `!t:A. MEM t (CONS x1 (APPEND p' q1)) ==> ~MEM t (CONS zz c)` THEN
    MESON_TAC[]]);;

let FACEPATH_EXISTS = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\t. t IN dart H) r /\
     diskN H r x /\ ~MEM x r
     ==> ?x' p. diskN H r x' /\ list_path (\a b. face_map H a = b) x' p /\
                LAST (CONS x' p) = edge_map H x /\
                ALL (\t. ~MEM t r) (CONS x' p)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `xx = face_map H (edge_map H (x:A))` THEN
  SUBGOAL_THEN `diskN H r (xx:A)` ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN ASM_SIMP_TAC[FACE_EDGE_IN_DISKN]; ALL_TAC] THEN
  SUBGOAL_THEN `cface H (xx:A) (edge_map H x)` MP_TAC THENL
   [EXPAND_TAC "xx" THEN REWRITE_TAC[CFACE_FACE_MAP_L]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:(A)list` STRIP_ASSUME_TAC o
             MATCH_MP CFACE_FACEPATH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIST_PATH_SHORTEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `ALL (\t:A. ~MEM t r) (CONS xx q)` THENL
   [MAP_EVERY EXISTS_TAC [`xx:A`; `q:(A)list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:A. MEM y (CONS xx q) /\ MEM y r` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~ALL (\t:A. ~MEM t r) (CONS xx q)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z = prevc r (y:A)` THEN
  SUBGOAL_THEN `MEM (z:A) r /\ rlink H z y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_MESON_TAC[PREVC_MEM; RLINK_PREVC]; ALL_TAC] THEN
  ABBREV_TAC `zz = face_map H (edge_map H (z:A))` THEN
  SUBGOAL_THEN `!u:A. MEM u (CONS xx q) ==> cface H u y`
  (LABEL_TAC "cfy") THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `q:(A)list`; `xx:A`] FACEPATH_CFACE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (zz:A) (CONS xx q)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `q:(A)list`; `xx:A`]
      FACE_CYCLE_MEM_CFACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "cfy" (MP_TAC o SPEC `xx:A`) THEN REWRITE_TAC[MEM] THEN
    CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(zz:A = xx)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~MEM (x:A) r` THEN
    SUBGOAL_THEN `x:A = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `face_map H (edge_map H (x:A)) = face_map H (edge_map H z)`
      MP_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[FACEI; EDGEI]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\a b. face_map (H:(A)hypermap) a = b`; `q:(A)list`; `xx:A`;
                 `zz:A`] LIST_PATH_SPLIT_AT_TAIL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:(A)list` (X_CHOOSE_THEN `q2:(A)list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?q1:(A)list. m1 = CONS xx q1`
    (X_CHOOSE_THEN `q1:(A)list` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `CONS (xx:A) q = APPEND m1 (CONS zz q2)` THEN
    STRUCT_CASES_TAC(ISPEC `m1:(A)list` list_CASES) THEN
    REWRITE_TAC[APPEND; CONS_11] THEN STRIP_TAC THENL
     [UNDISCH_TAC `~(zz:A = xx)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t:(A)list` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `CONS (xx:A) q = APPEND (CONS xx q1) (CONS zz q2)` THEN
  REWRITE_TAC[APPEND; CONS_11] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `MEM (y:A) (CONS xx (APPEND q1 (CONS zz q2)))` THEN
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); MEM_APPEND] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`zz:A`; `q2:(A)list`] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "zz" THEN MATCH_MP_TAC FACE_EDGE_IN_DISKN THEN
      MATCH_MP_TAC RING_SUBSET_DISKN THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `LAST (CONS (xx:A) (APPEND q1 (CONS zz q2))) = edge_map H x` THEN
      REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LAST_APPEND; NOT_CONS_NIL];
      REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `t:A` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `y:A = t` SUBST_ALL_TAC THENL
       [USE_THEN "cfy" (MP_TAC o SPEC `t:A`) THEN
        REWRITE_TAC[GSYM(CONJUNCT2 APPEND); MEM_APPEND] THEN
        ASM_REWRITE_TAC[] THEN CFACE_TAC[];
        UNDISCH_TAC
         `PAIRWISE (\a b:A. ~(a = b)) (CONS xx (APPEND q1 (CONS zz q2)))` THEN
        REWRITE_TAC[GSYM(CONJUNCT2 APPEND); PAIRWISE_DISTINCT_APPEND] THEN
        UNDISCH_TAC `MEM (t:A) (CONS xx q1)` THEN
        UNDISCH_TAC `MEM (t:A) (CONS zz q2)` THEN MESON_TAC[]]];
    MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`; `y:A`; `z:A`;
      `xx:A`; `zz:A`; `q1:(A)list`; `q2:(A)list`] DISKE_EDGE_MOEBIUS) THEN
    ASM_REWRITE_TAC[]]);;

let DISKE_EDGE_FWD = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     diskE H r x
     ==> diskE H r (edge_map H x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`] FACEPATH_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[diskE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':A` (X_CHOOSE_THEN `p:(A)list`
    STRIP_ASSUME_TAC)) THEN
  SUBST1_TAC(SYM(ASSUME `LAST (CONS (x':A) p) = edge_map H x`)) THEN
  MATCH_MP_TAC DISKE_OF_FACEPATH THEN ASM_REWRITE_TAC[]);;

let DISKE_EDGE = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     x IN dart H
     ==> (diskE H r (edge_map H x) <=> diskE H r x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`edge_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`;
      `diskE (H:(A)hypermap) r`; `x:A`] CLOSED_INVERSE_STEP) THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES] THEN
    ASM_MESON_TAC[DISKE_EDGE_FWD];
    ASM_MESON_TAC[DISKE_EDGE_FWD]]);;

(* ------------------------------------------------------------------------- *)
(* The disk map snip_disk: darts diskN r; the edge map follows the ring on   *)
(* ring darts, the face map enters a ring dart from the face of its ring     *)
(* predecessor.  A hypermap_pred certificate from e o n o f = I alone.       *)
(* ------------------------------------------------------------------------- *)

let HYPERMAP_PRED_CANCEL = prove
 (`!(d:A->bool) e n f.
     FINITE d /\
     (!x. ~(x IN d) ==> e x = x /\ n x = x /\ f x = x) /\
     (!x. x IN d ==> e x IN d /\ n x IN d /\ f x IN d) /\
     (!x. e (n (f x)) = x)
     ==> hypermap_pred (d,e,n,f)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[hypermap_pred; FST; SND] THEN
  SUBGOAL_THEN `(f:A->A) permutes d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PERMUTES_FINITE_INJECTIVE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:A->A) permutes d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PERMUTES_FINITE_SURJECTIVE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  ASM_SIMP_TAC[PERMUTES_FINITE_INJECTIVE] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC `inverse (f:A->A) a` th) THEN
                        MP_TAC(SPEC `inverse (f:A->A) b` th)) THEN
  MP_TAC(MATCH_MP PERMUTES_INVERSES (ASSUME `(f:A->A) permutes d`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASM_MESON_TAC[th]));;

let snipd_edge = new_definition
  `snipd_edge (H:(A)hypermap) (r:(A)list) x =
     if ~diskN H r x then x
     else if MEM x r then nextc r x else edge_map H x`;;

let snipd_node = new_definition
  `snipd_node (H:(A)hypermap) (r:(A)list) x =
     if ~diskN H r x then x else node_map H x`;;

let snipd_face = new_definition
  `snipd_face (H:(A)hypermap) (r:(A)list) x =
     if ~diskN H r x then x
     else if MEM x r then face_map H (edge_map H (prevc r x))
     else face_map H x`;;

let DISKN_SNIPD_EDGE = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     diskN H r x
     ==> diskN H r (snipd_edge H r x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snipd_edge] THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[RING_SUBSET_DISKN; NEXTC_MEM];
    ASM_MESON_TAC[DISKE_EDGE_FWD; diskE]]);;

let DISKN_SNIPD_NODE = prove
 (`!(H:(A)hypermap) r x.
     ALL (\y. y IN dart H) r /\ diskN H r x ==> diskN H r (snipd_node H r x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snipd_node] THEN
  ASM_MESON_TAC[DISKN_NODE_FWD; DISKN_SUBSET_DART]);;

let DISKN_SNIPD_FACE = prove
 (`!(H:(A)hypermap) r x.
     ALL (\y. y IN dart H) r /\ diskN H r x ==> diskN H r (snipd_face H r x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snipd_face] THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[RING_SUBSET_DISKN; PREVC_MEM; FACE_EDGE_IN_DISKN];
    ASM_MESON_TAC[DISKN_FACE_OFFRING]]);;

let NODE_FACE_NOT_RING = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     diskN H r x /\ ~MEM x r
     ==> ~MEM (node_map H (face_map H x)) r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `node_map H (face_map H (x:A))`]
    DISKE_EDGE) THEN ASM_REWRITE_TAC[faceK] THEN
  ASM_MESON_TAC[diskE; DISKN_SUBSET_DART; NODE_MAP_PERMUTES; FACE_MAP_PERMUTES;
                PERMUTES_IN_IMAGE]);;

let SNIPD_CANCEL3 = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> snipd_edge H r (snipd_node H r (snipd_face H r x)) = x`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_PAIRWISE) THEN
  ASM_CASES_TAC `diskN H r (x:A)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[snipd_face; snipd_node; snipd_edge]] THEN
  SUBGOAL_THEN `diskN H r (snipd_face H r (x:A))` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SNIPD_FACE]; ALL_TAC] THEN
  SUBGOAL_THEN `snipd_node H r (snipd_face H r (x:A)) =
                node_map H (snipd_face H r x)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[snipd_node]; ALL_TAC] THEN
  SUBGOAL_THEN `diskN H r (node_map H (snipd_face H r (x:A)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_NODE_FWD; DISKN_SUBSET_DART]; ALL_TAC] THEN
  ASM_CASES_TAC `MEM (x:A) r` THENL
   [SUBGOAL_THEN `snipd_face H r (x:A) = face_map H (edge_map H (prevc r x))`
      SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[snipd_face]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[edgeK]) THEN
    ASM_SIMP_TAC[edgeK; snipd_edge; PREVC_MEM; NEXTC_PREVC];
    SUBGOAL_THEN `snipd_face H r (x:A) = face_map H x` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[snipd_face]; ALL_TAC] THEN
    ASM_SIMP_TAC[snipd_edge; NODE_FACE_NOT_RING; faceK]]);;

let SNIPD_PRED = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> hypermap_pred (diskN H r, snipd_edge H r, snipd_node H r,
                        snipd_face H r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HYPERMAP_PRED_CANCEL THEN
  ASM_SIMP_TAC[FINITE_DISKN; IN; SNIPD_CANCEL3] THEN CONJ_TAC THENL
   [SIMP_TAC[snipd_edge; snipd_node; snipd_face];
    ASM_MESON_TAC[DISKN_SNIPD_EDGE; DISKN_SNIPD_NODE; DISKN_SNIPD_FACE]]);;

let snip_disk = new_definition
  `snip_disk (H:(A)hypermap) (r:(A)list) =
     mk_hypermap (diskN H r, snipd_edge H r, snipd_node H r, snipd_face H r)`;;

let SNIP_DISK_COMPONENTS = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> dart(snip_disk H r) = diskN H r /\
         edge_map(snip_disk H r) = snipd_edge H r /\
         node_map(snip_disk H r) = snipd_node H r /\
         face_map(snip_disk H r) = snipd_face H r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[snip_disk] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN MATCH_MP_TAC SNIPD_PRED THEN
  ASM_REWRITE_TAC[]);;

let SNIPD_EDGE_PERMUTES = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> snipd_edge H r permutes (diskN H r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `snip_disk (H:(A)hypermap) r` EDGE_MAP_PERMUTES) THEN
  ASM_SIMP_TAC[SNIP_DISK_COMPONENTS]);;

let SNIPD_FACE_PERMUTES = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> snipd_face H r permutes (diskN H r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `snip_disk (H:(A)hypermap) r` FACE_MAP_PERMUTES) THEN
  ASM_SIMP_TAC[SNIP_DISK_COMPONENTS]);;

(* ------------------------------------------------------------------------- *)
(* The remainder map snip_rem: darts redart r = the darts not strictly in    *)
(* the disk; the node map follows the ring backwards on ring darts, the face *)
(* map skips the disk between a ring dart and the next.                      *)
(* ------------------------------------------------------------------------- *)

let redart = new_definition
  `redart (H:(A)hypermap) (r:(A)list) = {x | x IN dart H /\ ~diskE H r x}`;;

let snipr_edge = new_definition
  `snipr_edge (H:(A)hypermap) (r:(A)list) x =
     if ~(x IN redart H r) then x else edge_map H x`;;

let snipr_node = new_definition
  `snipr_node (H:(A)hypermap) (r:(A)list) x =
     if ~(x IN redart H r) then x
     else if MEM x r then prevc r x else node_map H x`;;

let snipr_face = new_definition
  `snipr_face (H:(A)hypermap) (r:(A)list) x =
     if ~(x IN redart H r) then x
     else if MEM (node_map H (face_map H x)) r
          then nextc r (node_map H (face_map H x)) else face_map H x`;;

let IN_REDART = prove
 (`!(H:(A)hypermap) r x. x IN redart H r <=> x IN dart H /\ ~diskE H r x`,
  REWRITE_TAC[redart; IN_ELIM_THM]);;

let FINITE_REDART = prove
 (`!(H:(A)hypermap) r. FINITE (redart H r)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `dart(H:(A)hypermap)` THEN
  SIMP_TAC[FINITE_DART; SUBSET; IN_REDART]);;

let REDART_SNIPR_EDGE = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     x IN redart H r
     ==> snipr_edge H r x IN redart H r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REDART] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[snipr_edge; IN_REDART; DISKE_EDGE] THEN
  ASM_MESON_TAC[EDGE_MAP_PERMUTES; PERMUTES_IN_IMAGE]);;

let REDART_SNIPR_NODE = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     x IN redart H r
     ==> snipr_node H r x IN redart H r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REDART] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[snipr_node; IN_REDART] THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[PREVC_MEM; RING_MEM_DART; RING_NOT_DISKE];
    ASM_MESON_TAC[diskE; DISKN_NODE_EQ; NODE_MAP_PERMUTES;
      PERMUTES_IN_IMAGE]]);;

let REDART_SNIPR_FACE = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     x IN redart H r
     ==> snipr_face H r x IN redart H r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REDART] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[snipr_face; IN_REDART] THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[NEXTC_MEM; RING_MEM_DART; RING_NOT_DISKE]; ALL_TAC] THEN
  SUBGOAL_THEN `face_map H (x:A) IN dart H /\
    node_map H (face_map H x) IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_MAP_PERMUTES; NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `node_map H (face_map H (x:A))`]
    DISKE_EDGE) THEN
  ASM_REWRITE_TAC[faceK] THEN ASM_MESON_TAC[diskE; DISKN_NODE_FWD]);;

let SNIPR_CANCEL3 = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> snipr_edge H r (snipr_node H r (snipr_face H r x)) = x`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_PAIRWISE) THEN
  ASM_CASES_TAC `x IN redart H (r:(A)list)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[snipr_face; snipr_node; snipr_edge]] THEN
  SUBGOAL_THEN `snipr_face H r x IN redart H (r:(A)list) /\
                snipr_node H r (snipr_face H r x) IN redart H r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REDART_SNIPR_FACE; REDART_SNIPR_NODE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[snipr_edge] THEN
  MP_TAC(ASSUME `x IN redart H (r:(A)list)`) THEN REWRITE_TAC[IN_REDART] THEN
  STRIP_TAC THEN ASM_CASES_TAC `MEM (node_map H (face_map H (x:A))) r` THENL
   [SUBGOAL_THEN `snipr_face H r (x:A) = nextc r (node_map H (face_map H x))`
      SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[snipr_face]; ALL_TAC] THEN
    ASM_SIMP_TAC[snipr_node; NEXTC_MEM; PREVC_NEXTC; faceK];
    SUBGOAL_THEN `snipr_face H r (x:A) = face_map H x` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[snipr_face]; ALL_TAC] THEN
    SUBGOAL_THEN `~MEM (face_map H (x:A)) r` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `diskE H r (node_map H (face_map H (x:A)))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[diskE] THEN MATCH_MP_TAC DISKN_NODE_FWD THEN
        ASM_MESON_TAC[RING_SUBSET_DISKN; RING_MEM_DART];
        ALL_TAC] THEN
      SUBGOAL_THEN `node_map H (face_map H (x:A)) IN dart H` ASSUME_TAC THENL
       [ASM_SIMP_TAC[NODE_MAP_IN_DART; FACE_MAP_IN_DART]; ALL_TAC] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`;
                     `node_map H (face_map H (x:A))`] DISKE_EDGE) THEN
      ASM_REWRITE_TAC[faceK];
      ALL_TAC] THEN
    ASM_SIMP_TAC[snipr_node; faceK]]);;

let SNIPR_PRED = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> hypermap_pred (redart H r, snipr_edge H r, snipr_node H r,
                        snipr_face H r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HYPERMAP_PRED_CANCEL THEN
  ASM_SIMP_TAC[FINITE_REDART; SNIPR_CANCEL3] THEN CONJ_TAC THENL
   [SIMP_TAC[snipr_edge; snipr_node; snipr_face];
    ASM_MESON_TAC[REDART_SNIPR_EDGE; REDART_SNIPR_NODE; REDART_SNIPR_FACE]]);;

let snip_rem = new_definition
  `snip_rem (H:(A)hypermap) (r:(A)list) =
     mk_hypermap (redart H r, snipr_edge H r, snipr_node H r,
                  snipr_face H r)`;;

let SNIP_REM_COMPONENTS = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> dart(snip_rem H r) = redart H r /\
         edge_map(snip_rem H r) = snipr_edge H r /\
         node_map(snip_rem H r) = snipr_node H r /\
         face_map(snip_rem H r) = snipr_face H r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[snip_rem] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN MATCH_MP_TAC SNIPR_PRED THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The borders: r is the edge cycle of the disk and REVERSE r the node cycle *)
(* of the remainder; the disk faces are faces of H, so r is face-simple in   *)
(* the disk; hence H is the patch of the disk and the remainder.             *)
(* ------------------------------------------------------------------------- *)

let LIST_CYCLE_SNIPD_EDGE = prove
 (`!(H:(A)hypermap) r.
     ALL (\y. y IN dart H) r /\ PAIRWISE (\x y:A. ~(x = y)) r /\ ~(r = [])
     ==> list_cycle (\x y. snipd_edge H r x = y) r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`snipd_edge (H:(A)hypermap) r`; `nextc (r:(A)list)`;
                 `r:(A)list`] LIST_CYCLE_CONG_MEM) THEN
  ASM_SIMP_TAC[LIST_CYCLE_NEXTC] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[snipd_edge] THEN ASM_MESON_TAC[RING_SUBSET_DISKN]);;

let LIST_CYCLE_SNIPR_NODE = prove
 (`!(H:(A)hypermap) r.
     ALL (\y. y IN dart H) r /\ PAIRWISE (\x y:A. ~(x = y)) r /\ ~(r = [])
     ==> list_cycle (\x y. snipr_node H r x = y) (REVERSE r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`snipr_node (H:(A)hypermap) r`; `prevc (r:(A)list)`;
                 `REVERSE r:(A)list`] LIST_CYCLE_CONG_MEM) THEN
  ASM_SIMP_TAC[LIST_CYCLE_PREVC_REVERSE] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[snipr_node; MEM_REVERSE; IN_REDART] THEN
  ASM_MESON_TAC[RING_MEM_DART; RING_NOT_DISKE]);;

let CFACE_SNIPD_STEP = prove
 (`!(H:(A)hypermap) r x.
     scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\ diskN H r x
     ==> cface H x (snipd_face H r x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snipd_face] THEN COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`] RLINK_PREVC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CFACE_TAC[];
    CFACE_TAC[]]);;

let CFACE_SNIPD_HOMO = prove
 (`!(H:(A)hypermap) r x y.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     diskN H r x /\ cface (snip_disk H r) x y
     ==> cface H x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_DISK_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. y = ITER n (snipd_face H r) (x:A)`
    (CHOOSE_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `cface (snip_disk H r) (x:A) y` THEN
    ASM_REWRITE_TAC[cface; face; ORBIT_MAP_ITER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. diskN H r (ITER n (snipd_face H r) (x:A)) /\
        cface H x (ITER n (snipd_face H r) x)`
   (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; CFACE_REFL] THEN
  ASM_MESON_TAC[DISKN_SNIPD_FACE; CFACE_SNIPD_STEP; CFT_TRANS]);;

let FACE_SIMPLE_SNIPD_RING = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r
     ==> face_simple (snip_disk H r) r`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `!p:(A)list. ALL (\x. MEM x r) p /\ face_simple H p
                ==> face_simple (snip_disk H r) p`
   MATCH_MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[ALL_MEM_SELF; SCYCLE_SIMPLE]] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[face_simple; ALL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN SUBGOAL_THEN `diskN H r (h:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_SUBSET_DISKN]; ALL_TAC] THEN
  UNDISCH_TAC `~fband H t (h:A)` THEN REWRITE_TAC[FBAND_MEM_IFF] THEN
  MATCH_MP_TAC MONO_NOT THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  ASM_MESON_TAC[CFACE_SNIPD_HOMO]);;

let SNIP_PATCH = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     ~(r = [])
     ==> patch H (snip_disk H r) (snip_rem H r) (\x:A. x) (\x:A. x) r
               (REVERSE r)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_PAIRWISE) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_REM_COMPONENTS) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_DISK_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. x) = I` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; I_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[patch; IMAGE_I; MAP_I; I_THM; scycle; INJ] THEN
  ASM_SIMP_TAC[LIST_CYCLE_SNIPD_EDGE; FACE_SIMPLE_SNIPD_RING;
               LIST_CYCLE_SNIPR_NODE; PAIRWISE_DISTINCT_REVERSE] THEN
  REWRITE_TAC[IN_REDART; MEM_REVERSE] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART; IN];
    SIMP_TAC[];
    REWRITE_TAC[IN; diskE] THEN MESON_TAC[];
    SIMP_TAC[IN; snipd_edge];
    SIMP_TAC[IN; snipd_node];
    SIMP_TAC[snipr_edge; IN_REDART];
    SIMP_TAC[snipr_node; IN_REDART]]);;

let PLANAR_SNIPD = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     2 <= LENGTH r
     ==> planar_hypermap (snip_disk H r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_PATCH) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LENGTH_EQ_NIL;
     ARITH_RULE `~(2 <= 0)`];
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] PLANAR_PATCH)) THEN
    ASM_SIMP_TAC[]]);;

let PLANAR_SNIPR = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     2 <= LENGTH r
     ==> planar_hypermap (snip_rem H r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_PATCH) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LENGTH_EQ_NIL;
     ARITH_RULE `~(2 <= 0)`];
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] PLANAR_PATCH)) THEN
    ASM_SIMP_TAC[]]);;
