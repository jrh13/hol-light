(* ========================================================================= *)
(* 4CT/coloring.ml                                                           *)
(*                                                                           *)
(* coloring.v: colourings of hypermaps.  A coloring gives every dart a       *)
(* colour, constant on faces and different across edges; four_colorable,     *)
(* ring_trace (the trace of a colouring along a ring), the node-constant     *)
(* graph_coloring with FOUR_COLORABLE_DUAL, colourings of the mirror         *)
(* (COLORABLE_MIRROR), and the contract colourings cc_coloring, cc_colorable *)
(* and cc_ring_trace, which may agree across the edges of a contract.  Then  *)
(* the configuration vocabulary of the last section of coloring.v:           *)
(* minimal_counter_example, good_ring_arity, sparse, triad and               *)
(* valid_contract (Gonthier's record with its four clauses).  C_reducible    *)
(* needs kempe_coclosure and is defined as c_reducible in embed_contract.ml; *)
(* the Preembedding section is preembedding.ml.                              *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/color.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Orbit invariance.                                                      *)
(* If k is f-invariant on s and f permutes s, then k is constant on orbits.  *)
(* This is the key tool for proving face-invariance of colorings.            *)
(* ------------------------------------------------------------------------- *)

let ORBIT_INVARIANT = prove
 (`!f s (k:A->B) x y.
    FINITE s /\ f permutes s /\ x IN s /\
    (!z. z IN s ==> k(f z) = k z) /\
    y IN orbit_map f x
    ==> k y = k x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. (k:A->B)(ITER n f x) = k x` MP_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
    FIRST_X_ASSUM(fun ih -> REWRITE_TAC[GSYM ih]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC ITER_PERMUTES_IN THEN ASM_MESON_TAC[];
    UNDISCH_TAC `y IN orbit_map f (x:A)` THEN
    REWRITE_TAC[ORBIT_MAP_ITER] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 2. Coloring definitions.                                                  *)
(*                                                                           *)
(* A coloring k of hypermap H assigns colors to darts such that:             *)
(*   - k is face-invariant: k(face x) = k(x) for all darts x                 *)
(*   - k is edge-distinguishing: k(edge x) <> k(x) for all darts x           *)
(*                                                                           *)
(* Equivalently, same color on each face, different colors on edge links.    *)
(* This is the "map coloring" convention (faces = countries).                *)
(* ------------------------------------------------------------------------- *)

let coloring = new_definition
 `coloring (H:(A)hypermap) (k:A->color) <=>
    (!x. x IN dart H ==> ~(k(edge_map H x) = k x)) /\
    (!x. x IN dart H ==> k(face_map H x) = k x)`;;

let four_colorable = new_definition
 `four_colorable (H:(A)hypermap) <=> ?k. coloring H k`;;

(* ring_trace: there exists a coloring k such that et is the trace of k      *)
(* applied to the ring r. The trace captures the edge color differences.     *)

let ring_trace = new_definition
 `ring_trace (H:(A)hypermap) (r:(A)list) (et:color list) <=>
    ?k. coloring H k /\ et = trace_col(MAP k r)`;;

(* Graph coloring: dual notion -- edge-distinguishing + node-invariant. Used *)
(* for the traditional vertex-coloring formulation.                          *)

let graph_coloring = new_definition
 `graph_coloring (H:(A)hypermap) (k:A->color) <=>
    (!x. x IN dart H ==> ~(k(edge_map H x) = k x)) /\
    (!x. x IN dart H ==> k(node_map H x) = k x)`;;

let graph_four_colorable = new_definition
 `graph_four_colorable (H:(A)hypermap) <=> ?k. graph_coloring H k`;;

(* Contract coloring: like coloring but allows same color on edges in cc.    *)
(* For edges in insertE cc, k(edge x) may equal k(x).                        *)

let cc_coloring = new_definition
 `cc_coloring (H:(A)hypermap) (cc:(A)list) (k:A->color) <=>
    (!x. x IN dart H ==> (k(edge_map H x) = k x <=> MEM x (insertE H cc))) /\
    (!x. x IN dart H ==> k(face_map H x) = k x)`;;

let cc_colorable = new_definition
 `cc_colorable (H:(A)hypermap) (cc:(A)list) <=>
    ?k. cc_coloring H cc k`;;

let cc_ring_trace = new_definition
 `cc_ring_trace (H:(A)hypermap) (cc:(A)list) (r:(A)list) (et:color list) <=>
    ?k. cc_coloring H cc k /\ et = trace_col(MAP k r)`;;

(* ------------------------------------------------------------------------- *)
(* 3. Coloring lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Face invariance: a coloring gives the same color to all darts in a face.  *)

let CFACE_COLORING = prove
 (`!H:(A)hypermap k x y.
     coloring H k /\ x IN dart H /\ cface H x y ==> k y = k x`,
  REWRITE_TAC[coloring; cface; face] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`]
    ORBIT_INVARIANT) THEN
  ASM_REWRITE_TAC[FACE_MAP_PERMUTES; FINITE_DART]);;

(* Composing a coloring with an injective function preserves coloring.       *)

let COLORING_INJ = prove
 (`!H:(A)hypermap k h.
     coloring H k /\ (!x y:color. h x = h y ==> x = y) /\ h Color0 = Color0
     ==> coloring H (h o k)`,
  REWRITE_TAC[coloring; o_THM] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]]);;

(* Composing with a color permutation preserves coloring.                    *)

let COLORING_PERMC = prove
 (`!H:(A)hypermap k g.
     coloring H k ==> coloring H (permc g o k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COLORING_INJ THEN
  ASM_REWRITE_TAC[PERMC_0] THEN MESON_TAC[PERMC_INJ]);;

(* cc_coloring with empty contract = coloring.                               *)

let CC_COLORING_NIL = prove
 (`!H:(A)hypermap k. cc_coloring H [] k <=> coloring H k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cc_coloring; coloring; insertE] THEN
  REWRITE_TAC[ITLIST; MEM] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]);;

let CC_COLORABLE_NIL = prove
 (`!H:(A)hypermap. cc_colorable H [] <=> four_colorable H`,
  REWRITE_TAC[cc_colorable; four_colorable; CC_COLORING_NIL]);;

(* Ring trace properties.                                                    *)

let RING_TRACE_PERMT = prove
 (`!H:(A)hypermap r et g. ring_trace H r et ==> ring_trace H r (permt g et)`,
  REWRITE_TAC[ring_trace] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `(permc g) o (k:A->color)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC COLORING_PERMC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[MAP_o; GSYM PERMT_MAP; TRACE_PERMT]]);;

(* ------------------------------------------------------------------------- *)
(* 4. Dual and mirror coloring lemmas.                                       *)
(* Coloring of dual(H) <=> graph coloring of H. Coloring of mirror(H) =>     *)
(*                         coloring of H.                                    *)
(* ------------------------------------------------------------------------- *)

let COLORING_DUAL = prove
 (`!H:(A)hypermap k. coloring (dual H) k <=> graph_coloring H k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[coloring; graph_coloring; DUAL_COMPONENTS; o_THM] THEN
  MP_TAC(BETA_RULE(ISPECL [`edge_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`;
    `\x:A. ~((k:A->color)(node_map H (face_map H x)) = k x)`]
    PERMUTES_FORALL_IN)) THEN
  MP_TAC(BETA_RULE(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`;
    `\x:A. (k:A->color)(face_map H (edge_map H x)) = k x`]
    PERMUTES_FORALL_IN)) THEN
  REWRITE_TAC[EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES; edgeK; nodeK] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN MESON_TAC[]);;

let FOUR_COLORABLE_DUAL = prove
 (`!H:(A)hypermap. four_colorable (dual H) <=> graph_four_colorable H`,
  REWRITE_TAC[four_colorable; graph_four_colorable; COLORING_DUAL]);;

let COLORING_MIRROR = prove
 (`!H:(A)hypermap k. coloring (mirror H) k ==> coloring H k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coloring; MIRROR_COMPONENTS; o_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!y:A. y IN dart H ==> (k:A->color)(face_map H y) = k y`
   ASSUME_TAC THENL [ASM_MESON_TAC[faceK; FACE_MAP_IN_DART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `face_map H (edge_map H (x:A))` o
    check (is_neg o snd o dest_imp o snd o dest_forall o concl)) THEN
  ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; edgeK] THEN
  MESON_TAC[]);;

let COLORABLE_MIRROR = prove
 (`!H:(A)hypermap. four_colorable (mirror H) ==> four_colorable H`,
  REWRITE_TAC[four_colorable] THEN MESON_TAC[COLORING_MIRROR]);;

(* ------------------------------------------------------------------------- *)
(* 5. Configuration properties: minimal_counter_example (the smallest        *)
(* non-4-colourable map), the contract vocabulary good_ring_arity, sparse    *)
(* and triad, and valid_contract (Gonthier's record coloring.v:462, four     *)
(* clauses).  C_reducible needs kempe_coclosure (chromogram.ml) and is       *)
(* defined as c_reducible in embed_contract.ml.                              *)
(* ------------------------------------------------------------------------- *)

(* Minimal counter-example: planar, bridgeless, plain, precubic, not         *)
(* four-colorable, and minimal by dart count.                                *)

let minimal_counter_example = new_definition
 `minimal_counter_example (H:(A)hypermap) <=>
    planar_hypermap H /\ bridgeless H /\ plain_hypermap H /\ precubic H /\
    ~(four_colorable H) /\
    (!H':(A)hypermap.
       planar_hypermap H' /\ bridgeless H' /\ plain_hypermap H' /\
         precubic H' /\
       CARD(dart H') < CARD(dart H)
       ==> four_colorable H')`;;

(* good_ring_arity: face arity is between 3 and 6                            *)
let good_ring_arity = new_definition
 `good_ring_arity (H:(A)hypermap) (x:A) <=>
    3 <= arity H x /\ arity H x <= 6`;;

(* sparse: no two darts in the list are in the same node                     *)
let sparse = new_definition
 `sparse (H:(A)hypermap) (p:(A)list) <=>
    !i j. i < LENGTH p /\ j < LENGTH p /\ i < j
          ==> ~(cnode H (EL i p) (EL j p))`;;

(* triad (Gonthier coloring.v:458): x0 is a triad for the dart list p when   *)
(* more than two darts of its face have their edge-mate in the face band of  *)
(* p, while x0 is not adjacent to every dart of p.  Coq counts over the      *)
(* orbit sequence of face; here it is the cardinality of the face subset     *)
(* (TRIAD_LIST in contract.ml is the list form).                             *)
let triad = new_definition
 `triad (H:(A)hypermap) (p:(A)list) (x0:A) <=>
    2 < CARD {y | y IN face H x0 /\ fband H p (edge_map H y)} /\
    ~(!z. MEM z p ==> adj H x0 z)`;;

(* valid_contract (Gonthier coloring.v:462): cc is a valid contract for ring *)
(* r: off the ring, sparse, of size 1..4, and a size-4 contract has a triad  *)
(* in the kernel of the ring (the kernel is dart-restricted, IN_KERNEL).     *)
let valid_contract = new_definition
 `valid_contract (H:(A)hypermap) (r:(A)list) (cc:(A)list) <=>
    (!x. MEM x (insertE H cc) ==> ~(MEM x r)) /\
    sparse H (insertE H cc) /\
    1 <= LENGTH cc /\ LENGTH cc <= 4 /\
    (LENGTH cc = 4 ==> ?x0. x0 IN kernel H r /\ triad H (insertE H cc) x0)`;;

