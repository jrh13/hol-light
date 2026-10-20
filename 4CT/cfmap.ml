(* ========================================================================= *)
(* 4CT/cfmap.ml                                                              *)
(*                                                                           *)
(* cfmap.v: configuration maps.  A configuration map is given by a           *)
(* construction program, a list of steps (cpstep: CpR n, CpRr, CpY, CpH,     *)
(* CpU, CpK, CpA) run from right to left by cpmap, starting from the         *)
(* two-dart map cpmap0; each step rotates the perimeter ring cpring or adds  *)
(* nodes and faces.  The map produced by a cubic (cubic_prog) or             *)
(* configuration (config_prog) program is plain, cubic outside the ring,     *)
(* connected, bridgeless and planar (CPMAP_PLAIN, CPMAP_CUBIC,               *)
(* CPMAP_CONNECTED, CPMAP_BRIDGELESS, CPMAP_PLANAR), its ring is long        *)
(* (CPMAP_PROPER, CFMAP_LONG), and the ring together with the kernel         *)
(* transversal cpker covers every face exactly once (CPMAP_COVER,            *)
(* CPMAP_SIMPLE); CPRING_ECPA gives the ring of an A step.                   *)
(*                                                                           *)
(* The carrier.  Gonthier grows the dart type at each step (ecp_dart A adds  *)
(* two darts to A, the injection of the old darts being the identity).  Here *)
(* the dart type is fixed to num and the dart set grows instead: a           *)
(* dart-adding step keeps the old darts and allocates two fresh numbers for  *)
(* the new pair (new_dart2, via num_FINITE_AVOID), so the injections of the  *)
(* old darts, Gonthier's icpR, icpA, Icp and injcp, are all the identity,    *)
(* and a constructed map is carried as a pair (num)hypermap # num of the map *)
(* and its pointer dart.                                                     *)
(* ========================================================================= *)

needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/color.ml";;
needs "4CT/embed_prelim.ml";;

(* ------------------------------------------------------------------------- *)
(* cpstep: the basic construction steps (Gonthier cfmap.v:94-101).           *)
(*   CpR n : rotate the outer ring start point by n (noop on overflow).      *)
(*   CpRr  : single reverse rotation (Gonthier CpR').                        *)
(*   CpY   : new Y junction and face.                                        *)
(*   CpH   : new H junction and face (closing an inner face).                *)
(*   CpU   : new face, no junctions (U-shaped loop).                         *)
(*   CpK   : new K (inverted Y) junction.                                    *)
(*   CpA   : inverted-V junction, merging neighbours of a face.              *)
(* ------------------------------------------------------------------------- *)

let cpstep_INDUCT,cpstep_RECURSION = define_type
  "cpstep = CpR num | CpRr | CpY | CpH | CpU | CpK | CpA";;

(* cprog: a configuration construction program (interpreted right-to-left).  *)
(* In HOL this is just `(cpstep)list`; we keep the name `cprog` informally.  *)

(* ------------------------------------------------------------------------- *)
(* cubic_prog cp <=> cp consists only of R, U, Y and H steps (Gonthier       *)
(* cfmap.v:108-116), stated as ALL over a per-step predicate with one clause *)
(* per constructor.                                                          *)
(* ------------------------------------------------------------------------- *)

let cubic_step = define
  `(cubic_step (CpR n) <=> T) /\ (cubic_step CpRr <=> F) /\
   (cubic_step CpY <=> T) /\ (cubic_step CpH <=> T) /\
   (cubic_step CpU <=> T) /\ (cubic_step CpK <=> F) /\
   (cubic_step CpA <=> F)`;;

let cubic_prog = new_definition
  `cubic_prog (cp:(cpstep)list) <=> ALL cubic_step cp`;;

(* ------------------------------------------------------------------------- *)
(* config_prog cp <=> cp consists only of R, Y and H steps and ends with a Y *)
(* step (Gonthier cfmap.v:137-145; as programs run from right to left, the   *)
(* construction starts with the Y step).  Gonthier's recursion bottoms out   *)
(* at the singleton [CpY], which is exactly: nonempty, last step CpY, all    *)
(* steps R, Y or H.                                                          *)
(* ------------------------------------------------------------------------- *)

let config_step = define
  `(config_step (CpR n) <=> T) /\ (config_step CpRr <=> F) /\
   (config_step CpY <=> T) /\ (config_step CpH <=> T) /\
   (config_step CpU <=> F) /\ (config_step CpK <=> F) /\
   (config_step CpA <=> F)`;;

let config_prog = new_definition
  `config_prog (cp:(cpstep)list) <=>
     ~(cp = []) /\ LAST cp = CpY /\ ALL config_step cp`;;

(* The step predicates as disjunctions of constructor cases (the shape of    *)
(* Gonthier's recursive cubic_prog/config_prog matches).                     *)
let CUBIC_STEP_CASES = prove
 (`!s. cubic_step s <=> (?n. s = CpR n) \/ s = CpU \/ s = CpY \/ s = CpH`,
  MATCH_MP_TAC cpstep_INDUCT THEN
  REWRITE_TAC[cubic_step; distinctness "cpstep"; injectivity "cpstep"] THEN
  MESON_TAC[]);;

let CONFIG_STEP_CASES = prove
 (`!s. config_step s <=> (?n. s = CpR n) \/ s = CpY \/ s = CpH`,
  MATCH_MP_TAC cpstep_INDUCT THEN
  REWRITE_TAC[config_step; distinctness "cpstep"; injectivity "cpstep"] THEN
  MESON_TAC[]);;

(* config_prog ==> cubic_prog (Gonthier config_prog_cubic, cfmap.v:146).     *)
let CONFIG_PROG_CUBIC = prove
 (`!cp. config_prog cp ==> cubic_prog cp`,
  REWRITE_TAC[config_prog; cubic_prog] THEN GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_ALL THEN
  MATCH_MP_TAC cpstep_INDUCT THEN REWRITE_TAC[config_step; cubic_step]);;

(* ========================================================================= *)
(* Carrier infrastructure for the "grow the set" representation.             *)
(* ========================================================================= *)

(* new_dart s : a num not in the finite set s (Hilbert choice +              *)
(* num_FINITE_AVOID).                                                        *)
let new_dart = new_definition
  `new_dart (s:num->bool) = @x. ~(x IN s)`;;

let NEW_DART_FRESH = prove
 (`!s:num->bool. FINITE s ==> ~(new_dart s IN s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:num->bool` num_FINITE_AVOID) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN
  REWRITE_TAC[GSYM new_dart] THEN ASM_REWRITE_TAC[]);;

(* new_dart2 s : a pair of DISTINCT fresh darts (the two new darts           *)
(* IcpX,IcpXe).                                                              *)
let new_dart2 = new_definition
  `new_dart2 (s:num->bool) =
     (new_dart s, new_dart (new_dart s INSERT s))`;;

let NEW_DART2_FRESH = prove
 (`!s:num->bool. FINITE s
     ==> ~(FST(new_dart2 s) IN s) /\ ~(SND(new_dart2 s) IN s) /\
         ~(FST(new_dart2 s) = SND(new_dart2 s))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[new_dart2; FST; SND] THEN
  SUBGOAL_THEN `~(new_dart (s:num->bool) IN s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NEW_DART_FRESH]; ALL_TAC] THEN
  SUBGOAL_THEN
    `~(new_dart (new_dart (s:num->bool) INSERT s) IN (new_dart s INSERT s))`
    MP_TAC THENL
   [ASM_SIMP_TAC[NEW_DART_FRESH; FINITE_INSERT]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* cpmap0: the base 2-dart map (Gonthier cfmap.v:1124). carrier {0,1}, edge  *)
(* = node = swap(0,1), face = I. (Gonthier: carrier bool, edge=node= negb,   *)
(* face=id.)                                                                 *)
(* ------------------------------------------------------------------------- *)

let CPMAP0_PRED = prove
 (`hypermap_pred ({0,1}, swap(0,1), swap(0,1), I)`,
  REWRITE_TAC[hypermap_pred; FINITE_INSERT; FINITE_EMPTY; I_O_ID;
              SWAP_IDEMPOTENT] THEN
  SIMP_TAC[PERMUTES_SWAP; PERMUTES_I; IN_INSERT]);;

let cpmap0 = new_definition
  `cpmap0 = mk_hypermap ({0,1}, swap(0,1), swap(0,1), I)`;;

let CPMAP0_COMPONENTS = prove
 (`dart cpmap0 = {0,1} /\ edge_map cpmap0 = swap(0,1) /\
   node_map cpmap0 = swap(0,1) /\ face_map cpmap0 = I`,
  REWRITE_TAC[cpmap0] THEN MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  REWRITE_TAC[CPMAP0_PRED]);;

(* The node and face maps keep darts in the dart set.                        *)
let NODE_FACE_IN_DART = prove
 (`!(H:(num)hypermap) y.
     y IN dart H ==> node_map H y IN dart H /\ face_map H y IN dart H`,
  SIMP_TAC[NODE_MAP_IN_DART; FACE_MAP_IN_DART]);;

(* ------------------------------------------------------------------------- *)
(* ecpU step (Gonthier cfmap.v:526-548): the U step (new face, no junction). *)
(* a = IcpX, b = IcpXe. edge swaps a,b and is edge_map H on old darts.       *)
(* ------------------------------------------------------------------------- *)

let ecpU_edge = new_definition
  `ecpU_edge (H:(num)hypermap) a b x =
     if x = a then b else if x = b then a
     else if x IN dart H then edge_map H x else x`;;

let ecpU_node = new_definition
  `ecpU_node (H:(num)hypermap) x0 a b x =
     if x = a then b
     else if x = b then node_map H (node_map H x0)
     else if x IN dart H then (if x = node_map H x0 then a else node_map H x)
     else x`;;

let ecpU_face = new_definition
  `ecpU_face (H:(num)hypermap) x0 a b x =
     if x = a then a
     else if x = b then node_map H x0
     else if x IN dart H
     then (if face_map H x = node_map H x0 then b else face_map H x)
     else x`;;

(* The cancel3 identity edge o node o face = I (Gonthier ecpU_subproof).     *)
let ECPU_ENF = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> !x. ecpU_edge H a b (ecpU_node H x0 a b (ecpU_face H x0 a b x)) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] NODE_FACE_IN_DART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`;
                 `node_map H (x0:num)`] NODE_FACE_IN_DART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~(node_map H (x0:num) = a) /\ ~(node_map H x0 = b) /\
    ~(node_map H (node_map H x0) = a) /\ ~(node_map H (node_map H x0) = b)`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN REWRITE_TAC[ecpU_face] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[ecpU_node; ecpU_edge]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[ecpU_node] THEN ASM_REWRITE_TAC[ecpU_edge]; ALL_TAC] THEN
  ASM_CASES_TAC `x IN dart (H:(num)hypermap)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[ecpU_node] THEN ASM_REWRITE_TAC[ecpU_edge]] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`] NODE_FACE_IN_DART) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(face_map H (x:num) = a) /\ ~(face_map H x = b)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[ecpU_node] THEN ASM_REWRITE_TAC[ecpU_edge] THEN
    UNDISCH_TAC `face_map H (x:num) = node_map H x0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[faceK];
    ASM_REWRITE_TAC[ecpU_node] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`;
                   `face_map H (x:num)`] NODE_FACE_IN_DART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
   `~(node_map H (face_map H (x:num)) = a) /\ ~(node_map H (face_map H x) = b)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ecpU_edge; faceK]]);;

(* A step map is a hypermap by HYPERMAP_PRED_CANCEL: its three maps fix the  *)
(* points outside the new dart set, map the set into itself and satisfy the  *)
(* cancellation identity (Gonthier likewise builds each map from its cancel3 *)
(* identity).  ECP_PRED_TAC proves the first two conditions for a U or N     *)
(* step on a INSERT b INSERT dart H, given the identity enf and the          *)
(* definitions defs of the three maps: a and b are handled first, then the   *)
(* old darts case by case.                                                   *)
let ECP_PRED_TAC enf defs =
  let finish =
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_MESON_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART] in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HYPERMAP_PRED_CANCEL THEN
  ASM_SIMP_TAC[enf; FINITE_INSERT; FINITE_DART] THEN
  SUBGOAL_THEN `~(b:num = a)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `x:num` THENL [SIMP_TAC defs; ALL_TAC] THEN
  ASM_CASES_TAC `x:num = a` THENL
   [ASM_REWRITE_TAC defs THEN finish; ALL_TAC] THEN
  ASM_CASES_TAC `x:num = b` THENL
   [ASM_REWRITE_TAC defs THEN finish; ALL_TAC] THEN
  ASM_REWRITE_TAC defs THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN finish;;

let ECPU_PRED = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> hypermap_pred (a INSERT b INSERT dart H,
                        ecpU_edge H a b, ecpU_node H x0 a b,
                        ecpU_face H x0 a b)`,
  ECP_PRED_TAC ECPU_ENF [ecpU_edge; ecpU_node; ecpU_face]);;

let ECPU_PERMUTES = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> ecpU_edge H a b permutes (a INSERT b INSERT dart H) /\
         ecpU_node H x0 a b permutes (a INSERT b INSERT dart H) /\
         ecpU_face H x0 a b permutes (a INSERT b INSERT dart H)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ECPU_PRED) THEN
  SIMP_TAC[hypermap_pred]);;

(* ecpU H x0 : the U-step map (fresh darts = new_dart2(dart H); pointer =    *)
(* first fresh = ecpU_pt).                                                   *)
let ecpU = new_definition
  `ecpU (H:(num)hypermap) x0 =
     mk_hypermap (FST(new_dart2(dart H)) INSERT SND(new_dart2(dart H))
                  INSERT dart H,
                  ecpU_edge H (FST(new_dart2(dart H)))
                  (SND(new_dart2(dart H))),
                  ecpU_node H x0 (FST(new_dart2(dart H)))
                  (SND(new_dart2(dart H))),
                  ecpU_face H x0 (FST(new_dart2(dart H)))
                  (SND(new_dart2(dart H))))`;;

let ecpU_pt = new_definition
  `ecpU_pt (H:(num)hypermap) = FST(new_dart2(dart H))`;;

let ECPU_COMPONENTS = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> dart(ecpU H x0) =
     (FST(new_dart2(dart H)) INSERT SND(new_dart2(dart H)) INSERT dart H) /\
         edge_map(ecpU H x0) =
         ecpU_edge H (FST(new_dart2(dart H))) (SND(new_dart2(dart H))) /\
         node_map(ecpU H x0) =
         ecpU_node H x0 (FST(new_dart2(dart H))) (SND(new_dart2(dart H))) /\
         face_map(ecpU H x0) =
         ecpU_face H x0 (FST(new_dart2(dart H))) (SND(new_dart2(dart H)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ecpU] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`;
                 `FST(new_dart2(dart(H:(num)hypermap)))`;
                 `SND(new_dart2(dart(H:(num)hypermap)))`] ECPU_PRED) THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* nodeK and EDGE_MAP_IN_DART at type num.                                   *)
let NODEK_NUM = prove
 (`!(H:(num)hypermap) x. face_map H (edge_map H (node_map H x)) = x`,
  REWRITE_TAC[nodeK]);;

let EDGE_IN_DART = prove
 (`!(H:(num)hypermap) y. y IN dart H ==> edge_map H y IN dart H`,
  REWRITE_TAC[EDGE_MAP_IN_DART]);;

(* ------------------------------------------------------------------------- *)
(* ecpN step (Gonthier cfmap.v:560-591): the N step (K applied at ring       *)
(* head). edge map = ecpU_edge (same swap a,b + edge on old). long_cpring x0 *)
(* = face(edge x0) <> node x0 (Gonthier long_cpring).                        *)
(* ------------------------------------------------------------------------- *)

let long_cpring = new_definition
  `long_cpring (H:(num)hypermap) x0 <=>
   ~(face_map H (edge_map H x0) = node_map H x0)`;;

let ecpN_node = new_definition
  `ecpN_node (H:(num)hypermap) x0 a b x =
     if x = a then (if long_cpring H x0 then node_map H x0 else a)
     else if x = b then face_map H (edge_map H x0)
     else if x IN dart H
          then (if x = x0 then b
                else if node_map H (node_map H x) = x0 then a
                else node_map H x)
     else x`;;

let ecpN_face = new_definition
  `ecpN_face (H:(num)hypermap) x0 a b x =
     if x = a then x0
     else if x = b then (if long_cpring H x0
                         then face_map H
                         (edge_map H (face_map H (edge_map H x0))) else a)
     else if x IN dart H
          then (if x = edge_map H (face_map H (edge_map H x0)) then b
                else if x = edge_map H (node_map H x0) then a
                else face_map H x)
     else x`;;

(* The cancel3 identity edge o node o face = I for the N step (Gonthier      *)
(* ecpN_subproof).                                                           *)
let ECPN_ENF = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> !x. ecpU_edge H a b (ecpN_node H x0 a b (ecpN_face H x0 a b x)) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `edge_map H (x0:num) IN dart H /\ node_map H (x0:num) IN dart H /\
    face_map H (edge_map H (x0:num)) IN dart H /\
    edge_map H (node_map H (x0:num)) IN dart H /\
    edge_map H (face_map H (edge_map H (x0:num))) IN dart H /\
    face_map H (edge_map H (face_map H (edge_map H (x0:num)))) IN dart H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EDGE_MAP_IN_DART; NODE_FACE_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(x0:num = a) /\ ~(x0:num = b) /\
    ~(node_map H (x0:num) = a) /\ ~(node_map H (x0:num) = b) /\
    ~(face_map H (edge_map H (x0:num)) = a) /\
    ~(face_map H (edge_map H (x0:num)) = b) /\
    ~(edge_map H (node_map H (x0:num)) = a) /\
    ~(edge_map H (node_map H (x0:num)) = b) /\
    ~(edge_map H (face_map H (edge_map H (x0:num))) = a) /\
    ~(edge_map H (face_map H (edge_map H (x0:num))) = b) /\
    ~(face_map H (edge_map H (face_map H (edge_map H (x0:num)))) = a) /\
    ~(face_map H (edge_map H (face_map H (edge_map H (x0:num)))) = b)`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN REWRITE_TAC[ecpN_face] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ecpN_node] THENL
   [REWRITE_TAC[ecpU_edge] THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:num = b` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `long_cpring H (x0:num)` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN
       `~(face_map H (edge_map H (face_map H (edge_map H (x0:num)))) = x0) /\
        node_map H (node_map H (face_map H (edge_map H
                                    (face_map H (edge_map H (x0:num)))))) = x0`
       STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [DISCH_TAC THEN UNDISCH_TAC `long_cpring H (x0:num)` THEN
          REWRITE_TAC[long_cpring] THEN
          FIRST_X_ASSUM(MP_TAC o AP_TERM `node_map(H:(num)hypermap)`) THEN
          REWRITE_TAC[edgeK];
          REWRITE_TAC[edgeK]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[ecpU_edge];
      REWRITE_TAC[ecpU_edge]];
    ALL_TAC] THEN
  ASM_CASES_TAC `x IN dart (H:(num)hypermap)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_REWRITE_TAC[ecpU_edge]] THEN
  SUBGOAL_THEN
   `face_map H (x:num) IN dart H /\
    node_map H (face_map H (x:num)) IN dart H /\
    ~(face_map H (x:num) = a) /\ ~(face_map H (x:num) = b) /\
    ~(node_map H (face_map H (x:num)) = a) /\
    ~(node_map H (face_map H (x:num)) = b)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NODE_FACE_IN_DART]; ALL_TAC] THEN
  ASM_CASES_TAC `x:num = edge_map H (face_map H (edge_map H (x0:num)))` THEN
  ASM_REWRITE_TAC[] THENL [ASM_REWRITE_TAC[ecpU_edge]; ALL_TAC] THEN
  ASM_CASES_TAC `x:num = edge_map H (node_map H (x0:num))` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `long_cpring H (x0:num)` THEN ASM_REWRITE_TAC[ecpU_edge] THEN
    UNDISCH_TAC `~(x:num = edge_map H (face_map H (edge_map H (x0:num))))` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~long_cpring H (x0:num)` THEN
    REWRITE_TAC[long_cpring] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(face_map H (x:num) = x0) /\
    ~(node_map H (node_map H (face_map H (x:num))) = x0)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(x:num = edge_map H (node_map H (x0:num)))` THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o
        AP_TERM `\y. edge_map H (node_map H (y:num))`) THEN
      REWRITE_TAC[faceK];
      DISCH_TAC THEN UNDISCH_TAC
       `~(x:num = edge_map H (face_map H (edge_map H (x0:num))))` THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o
        AP_TERM `\y. edge_map H (face_map H (edge_map H (y:num)))`) THEN
      REWRITE_TAC[nodeK; faceK]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ecpU_edge; faceK]);;

let ECPN_PRED = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> hypermap_pred (a INSERT b INSERT dart H,
                        ecpU_edge H a b, ecpN_node H x0 a b,
                        ecpN_face H x0 a b)`,
  ECP_PRED_TAC ECPN_ENF [ecpU_edge; ecpN_node; ecpN_face]);;

let ECPN_PERMUTES = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> ecpN_node H x0 a b permutes (a INSERT b INSERT dart H) /\
         ecpN_face H x0 a b permutes (a INSERT b INSERT dart H)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ECPN_PRED) THEN
  SIMP_TAC[hypermap_pred]);;

let ecpN = new_definition
  `ecpN (H:(num)hypermap) x0 =
     mk_hypermap (FST(new_dart2(dart H)) INSERT SND(new_dart2(dart H))
                  INSERT dart H,
                  ecpU_edge H (FST(new_dart2(dart H)))
                  (SND(new_dart2(dart H))),
                  ecpN_node H x0 (FST(new_dart2(dart H)))
                  (SND(new_dart2(dart H))),
                  ecpN_face H x0 (FST(new_dart2(dart H)))
                  (SND(new_dart2(dart H))))`;;

let ecpN_pt = new_definition
  `ecpN_pt (H:(num)hypermap) = FST(new_dart2(dart H))`;;

let ECPN_COMPONENTS = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> dart(ecpN H x0) =
     (FST(new_dart2(dart H)) INSERT SND(new_dart2(dart H)) INSERT dart H) /\
         edge_map(ecpN H x0) =
         ecpU_edge H (FST(new_dart2(dart H))) (SND(new_dart2(dart H))) /\
         node_map(ecpN H x0) =
         ecpN_node H x0 (FST(new_dart2(dart H))) (SND(new_dart2(dart H))) /\
         face_map(ecpN H x0) =
         ecpN_face H x0 (FST(new_dart2(dart H))) (SND(new_dart2(dart H)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ecpN] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`;
                 `FST(new_dart2(dart(H:(num)hypermap)))`;
                 `SND(new_dart2(dart(H:(num)hypermap)))`] ECPN_PRED) THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Derived steps ecpY = ecpN o ecpU, ecpH = ecpN o ecpY (Gonthier            *)
(* cfmap.v:944, 1028). These are the Y/H junctions config_prog programs are  *)
(* built from. Being compositions of ecpN/ecpU (each a hypermap), they are   *)
(* hypermaps.                                                                *)
(* ------------------------------------------------------------------------- *)

let ecpY = new_definition
  `ecpY (H:(num)hypermap) x0 = ecpN (ecpU H x0) (ecpU_pt H)`;;
let ecpY_pt = new_definition
  `ecpY_pt (H:(num)hypermap) x0 = ecpN_pt (ecpU H x0)`;;
let ecpH = new_definition
  `ecpH (H:(num)hypermap) x0 = ecpN (ecpY H x0) (ecpY_pt H x0)`;;
let ecpH_pt = new_definition
  `ecpH_pt (H:(num)hypermap) x0 = ecpN_pt (ecpY H x0)`;;

(* The new pointer of a U step is a dart of the resulting map.               *)
let ECPU_PT_IN_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> ecpU_pt H IN dart(ecpU H x0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`;`x0:num`] ECPU_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ecpU_pt; IN_INSERT]);;

(* The new pointer of an N step is a dart of the resulting map.              *)
let ECPN_PT_IN_DART = prove
 (`!(G:(num)hypermap) y. y IN dart G ==> ecpN_pt G IN dart(ecpN G y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`;`y:num`] ECPN_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ecpN_pt; IN_INSERT]);;

let ECPY_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> dart(ecpY H x0) =
         FST(new_dart2(dart(ecpU H x0))) INSERT
         SND(new_dart2(dart(ecpU H x0))) INSERT
         dart(ecpU H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY] THEN
  MP_TAC(ISPECL [`ecpU H x0`; `ecpU_pt H`] ECPN_COMPONENTS) THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let ECPY_PT_IN_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> ecpY_pt H x0 IN dart(ecpY H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY_pt; ecpY] THEN
  MATCH_MP_TAC ECPN_PT_IN_DART THEN ASM_SIMP_TAC[ECPU_PT_IN_DART]);;

let ECPH_PT_IN_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> ecpH_pt H x0 IN dart(ecpH H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH_pt; ecpH] THEN
  MATCH_MP_TAC ECPN_PT_IN_DART THEN ASM_SIMP_TAC[ECPY_PT_IN_DART]);;

(* ------------------------------------------------------------------------- *)
(* ecpR n x0 (Gonthier cfmap.v:293): ring rotation. The MAP IS UNCHANGED;    *)
(* only the pointer moves to node^(order node x0 - n)(x0). So ecpR H n x0 =  *)
(* H and the construction is identity on darts (matching Gonthier's icpR =   *)
(* id).                                                                      *)
(* ------------------------------------------------------------------------- *)

let ecpR = new_definition
  `ecpR (H:(num)hypermap) (n:num) (x0:num) = H`;;
let ecpR_pt = new_definition
  `ecpR_pt (H:(num)hypermap) (n:num) x0 =
   ITER (orbit_size (node_map H) x0 - n) (node_map H) x0`;;

let ECPR_PT_IN_DART = prove
 (`!(H:(num)hypermap) n x0. x0 IN dart H ==> ecpR_pt H n x0 IN dart H`,
  SIMP_TAC[ecpR_pt; ITER_PERMUTES_IN; NODE_MAP_PERMUTES]);;

(* ecpRr = ecpR (osize-1) : single reverse rotation (Gonthier CpR'/ecpR').   *)
let ecpRr = new_definition
  `ecpRr (H:(num)hypermap) x0 = ecpR H (orbit_size (node_map H) x0 - 1) x0`;;
let ecpRr_pt = new_definition
  `ecpRr_pt (H:(num)hypermap) x0 =
   ecpR_pt H (orbit_size (node_map H) x0 - 1) x0`;;

let ECPRR_EQ = prove
 (`!(H:(num)hypermap) x0. ecpRr H x0 = H`,
  REWRITE_TAC[ecpRr; ecpR]);;

let ECPRR_PT_IN_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> ecpRr_pt H x0 IN dart H`,
  SIMP_TAC[ecpRr_pt; ECPR_PT_IN_DART]);;

(* ecpK = ecpR 1 (ecpN (ecpRr H x0)) : the K step (Gonthier cfmap.v:900).    *)
let ecpK = new_definition
  `ecpK (H:(num)hypermap) x0 =
     ecpR (ecpN (ecpRr H x0) (ecpRr_pt H x0)) 1 (ecpN_pt (ecpRr H x0))`;;
let ecpK_pt = new_definition
  `ecpK_pt (H:(num)hypermap) x0 =
     ecpR_pt (ecpN (ecpRr H x0) (ecpRr_pt H x0)) 1 (ecpN_pt (ecpRr H x0))`;;

let ECPK_DART = prove
 (`!(H:(num)hypermap) x0.
     dart(ecpK H x0) = dart(ecpN (ecpRr H x0) (ecpRr_pt H x0))`,
  REWRITE_TAC[ecpK; ecpR]);;

let ECPK_PT_IN_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> ecpK_pt H x0 IN dart(ecpK H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpK_pt; ecpK; ecpR] THEN
  MATCH_MP_TAC ECPR_PT_IN_DART THEN MATCH_MP_TAC ECPN_PT_IN_DART THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPRR_PT_IN_DART) THEN
  ASM_REWRITE_TAC[ECPRR_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The A step ecpA (the inverted-V merge, Gonthier cfmap.v:330-395):         *)
(* definitions and hypermap structure.                                       *)
(* ------------------------------------------------------------------------- *)

let ecpA_edge = new_definition
  `ecpA_edge (H:(num)hypermap) x0 x =
     if x IN dart H
     then (if ~(cface H (edge_map H x0) (node_map H x0)) then edge_map H x
           else if x = x0 then edge_map H (node_map H (node_map H x0))
           else if x = node_map H (node_map H x0) then edge_map H x0
           else edge_map H x)
     else x`;;

let ecpA_node = new_definition
  `ecpA_node (H:(num)hypermap) x0 x =
     if x IN dart H
     then (if x = node_map H x0 then x0
           else if node_map H x = x0 then node_map H (node_map H x0)
           else node_map H x)
     else x`;;

let ecpA_face = new_definition
  `ecpA_face (H:(num)hypermap) x0 x =
     if x IN dart H
     then (if cface H (edge_map H x0) (node_map H x0) then face_map H x
           else if x = edge_map H x0 then node_map H x0
           else if face_map H x = node_map H x0 then face_map H (edge_map H x0)
           else face_map H x)
     else x`;;

(* The cancel3 identity edge o node o face = I for the A step (Gonthier      *)
(* ecpA_subproof cfmap.v:344). Case-split on c; the c=T branch uses the swap *)
(* logic in ecpA_edge, the c=F branch has ecpA_edge = edge on darts.         *)
let ECPA_ENF = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H
     ==> !x. ecpA_edge H x0 (ecpA_node H x0 (ecpA_face H x0 x)) = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:num` THEN
  ASM_CASES_TAC `x IN dart(H:(num)hypermap)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[ecpA_face] THEN ASM_REWRITE_TAC[ecpA_node] THEN
    ASM_REWRITE_TAC[ecpA_edge]] THEN
  SUBGOAL_THEN
   `edge_map H (x0:num) IN dart H /\ node_map H (x0:num) IN dart H /\
    node_map H (node_map H (x0:num)) IN dart H /\
    edge_map H (node_map H (node_map H (x0:num))) IN dart H /\
    face_map H (x:num) IN dart H /\
    node_map H (face_map H (x:num)) IN dart H /\
    face_map H (edge_map H (x0:num)) IN dart H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EDGE_MAP_IN_DART; NODE_FACE_IN_DART]; ALL_TAC] THEN
  ASM_CASES_TAC `cface H (edge_map H (x0:num)) (node_map H x0)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[ecpA_face]] THENL
   [ASM_REWRITE_TAC[ecpA_face] THEN
    ASM_REWRITE_TAC[ecpA_node] THEN
    ASM_CASES_TAC `face_map H (x:num) = node_map H x0` THEN
    ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      ASM_CASES_TAC `node_map H (face_map H (x:num)) = x0` THEN
      ASM_REWRITE_TAC[]] THENL
     [ASM_REWRITE_TAC[ecpA_edge] THEN
      MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`] faceK) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[ecpA_edge] THEN
      MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`] faceK) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[ecpA_edge] THEN
      SUBGOAL_THEN
       `~(node_map H (face_map H (x:num)) = node_map H (node_map H x0))`
      ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(face_map H (x:num) = node_map H x0)` THEN
        REWRITE_TAC[] THEN ASM_MESON_TAC[NODEI]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`] faceK) THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `!z:num. z IN dart H ==> ecpA_edge H x0 z = edge_map H z`
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[ecpA_edge]; ALL_TAC] THEN
    SUBGOAL_THEN `node_map H (face_map H (edge_map H (x0:num))) = x0`
    ASSUME_TAC THENL
     [REWRITE_TAC[edgeK]; ALL_TAC] THEN
    SUBGOAL_THEN `~(face_map H (edge_map H (x0:num)) = node_map H x0)`
    ASSUME_TAC THENL
     [DISCH_TAC THEN
     UNDISCH_TAC `~cface H (edge_map H (x0:num)) (node_map H x0)` THEN
      REWRITE_TAC[] THEN
      REWRITE_TAC[cface; face; ORBIT_MAP_ITER; IN_ELIM_THM] THEN
      EXISTS_TAC `1` THEN REWRITE_TAC[ITER_1] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `x:num = edge_map H x0` THEN ASM_REWRITE_TAC[] THENL
     [ASM_REWRITE_TAC[ecpA_node] THEN ASM_SIMP_TAC[];
      ASM_CASES_TAC `face_map H (x:num) = node_map H x0` THEN
      ASM_REWRITE_TAC[]] THENL
     [ASM_REWRITE_TAC[ecpA_node] THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`] faceK) THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(node_map H (face_map H (x:num)) = x0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(x:num = edge_map H x0)` THEN
       REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`] faceK) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        AP_TERM_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[ecpA_node] THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`] faceK) THEN
      ASM_REWRITE_TAC[]]]);;

(* The A step is a hypermap on the same dart set.                            *)
let ECPA_PRED = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H
     ==> hypermap_pred
     (dart H, ecpA_edge H x0, ecpA_node H x0, ecpA_face H x0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HYPERMAP_PRED_CANCEL THEN
  ASM_SIMP_TAC[ECPA_ENF; FINITE_DART] THEN
  SIMP_TAC[ecpA_edge; ecpA_node; ecpA_face] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART]);;

(* ecpA H x0 : the A-step map (SAME dart set; pointer = ecpA_pt below).      *)
let ecpA = new_definition
  `ecpA (H:(num)hypermap) x0 =
     mk_hypermap (dart H, ecpA_edge H x0, ecpA_node H x0, ecpA_face H x0)`;;

let ECPA_COMPONENTS = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> dart(ecpA H x0) = dart H /\
         edge_map(ecpA H x0) = ecpA_edge H x0 /\
         node_map(ecpA H x0) = ecpA_node H x0 /\
         face_map(ecpA H x0) = ecpA_face H x0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ecpA] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPA_PRED) THEN
  ASM_REWRITE_TAC[]);;

(* ecpA_pt (Gonthier: face(edge(face(edge x0))) in the NEW map).             *)
let ecpA_pt = new_definition
  `ecpA_pt (H:(num)hypermap) x0 =
     face_map (ecpA H x0) (edge_map (ecpA H x0) (face_map H (edge_map H x0)))`
     ;;

let ECPA_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> dart(ecpA H x0) = dart H`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPA_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let ECPA_PT_IN_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> ecpA_pt H x0 IN dart(ecpA H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpA_pt] THEN
  REPEAT(MATCH_MP_TAC FACE_MAP_IN_DART ORELSE
         MATCH_MP_TAC EDGE_MAP_IN_DART) THEN
  ASM_SIMP_TAC[ECPA_DART; FACE_MAP_IN_DART; EDGE_MAP_IN_DART]);;

(* ------------------------------------------------------------------------- *)
(* cpmap: running a configuration program (Gonthier cfmap.v:1128), a         *)
(* right-to-left fold of the per-step builders over the (map, pointer) pair  *)
(* starting from (cpmap0, 1).                                                *)
(* ------------------------------------------------------------------------- *)

(* cpstep_apply s (G,x): one construction step on the (map, pointer) pair,   *)
(* one clause per constructor (the match in Gonthier's cpmap, cfmap.v:1128). *)
let cpstep_apply = define
  `(cpstep_apply (CpR n) (G,x) = (ecpR G n x, ecpR_pt G n x)) /\
   (cpstep_apply CpRr (G,x) = (ecpRr G x, ecpRr_pt G x)) /\
   (cpstep_apply CpY (G,x) = (ecpY G x, ecpY_pt G x)) /\
   (cpstep_apply CpH (G,x) = (ecpH G x, ecpH_pt G x)) /\
   (cpstep_apply CpU (G,x) = (ecpU G x, ecpU_pt G)) /\
   (cpstep_apply CpK (G,x) = (ecpK G x, ecpK_pt G x)) /\
   (cpstep_apply CpA (G,x) = (ecpA G x, ecpA_pt G x))`;;

let cpmap = new_definition
  `cpmap (cp:(cpstep)list) = ITLIST cpstep_apply cp (cpmap0, 1)`;;

(* cpmap of a cons step, with the map/pointer pair split for the clauses,    *)
(* its R/Y/H/U instances, and cpmap of the empty program.                    *)
let CPMAP_CONS_PAIR = prove
 (`!s cp. cpmap (CONS s cp) = cpstep_apply s (FST(cpmap cp), SND(cpmap cp))`,
  REWRITE_TAC[cpmap; ITLIST; PAIR]);;

let CPMAP_CONS_R = prove
 (`!n cp. cpmap (CONS (CpR n) cp) =
          (ecpR (FST(cpmap cp)) n (SND(cpmap cp)),
           ecpR_pt (FST(cpmap cp)) n (SND(cpmap cp)))`,
  REWRITE_TAC[CPMAP_CONS_PAIR; cpstep_apply]);;

let CPMAP_CONS_Y = prove
 (`!cp. cpmap (CONS CpY cp) =
        (ecpY (FST(cpmap cp)) (SND(cpmap cp)),
         ecpY_pt (FST(cpmap cp)) (SND(cpmap cp)))`,
  REWRITE_TAC[CPMAP_CONS_PAIR; cpstep_apply]);;

let CPMAP_CONS_H = prove
 (`!cp. cpmap (CONS CpH cp) =
        (ecpH (FST(cpmap cp)) (SND(cpmap cp)),
         ecpH_pt (FST(cpmap cp)) (SND(cpmap cp)))`,
  REWRITE_TAC[CPMAP_CONS_PAIR; cpstep_apply]);;

let CPMAP_NIL_PAIR = prove
 (`cpmap [] = (cpmap0,1)`,
  REWRITE_TAC[cpmap; ITLIST]);;

let CPMAP_CONS_U_PAIR = prove
 (`!cp. cpmap (CONS CpU cp) =
        (ecpU (FST(cpmap cp)) (SND(cpmap cp)), ecpU_pt (FST(cpmap cp)))`,
  REWRITE_TAC[CPMAP_CONS_PAIR; cpstep_apply]);;

(* Induction over cubic and over configuration programs.                     *)
let CUBIC_PROG_INDUCT = prove
 (`!P. P [] /\
       (!n cp. cubic_prog cp /\ P cp ==> P (CONS (CpR n) cp)) /\
       (!cp. cubic_prog cp /\ P cp ==> P (CONS CpU cp)) /\
       (!cp. cubic_prog cp /\ P cp ==> P (CONS CpY cp)) /\
       (!cp. cubic_prog cp /\ P cp ==> P (CONS CpH cp))
       ==> !cp. cubic_prog cp ==> P cp`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cubic_prog] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; CUBIC_STEP_CASES] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[cubic_prog]);;

let CONFIG_PROG_INDUCT = prove
 (`!P. P [CpY] /\
       (!n cp. config_prog cp /\ P cp ==> P (CONS (CpR n) cp)) /\
       (!cp. config_prog cp /\ P cp ==> P (CONS CpY cp)) /\
       (!cp. config_prog cp /\ P cp ==> P (CONS CpH cp))
       ==> !cp. config_prog cp ==> P cp`,
  GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[config_prog; NOT_CONS_NIL; ALL] THEN
  ASM_CASES_TAC `t:(cpstep)list = []` THENL
   [ASM_REWRITE_TAC[LAST; ALL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[LAST; CONFIG_STEP_CASES] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[config_prog]]);;

(* A single step preserves "pointer IN dart".                                *)
let CPSTEP_APPLY_PT = prove
 (`!s (H:(num)hypermap) x0. x0 IN dart H
     ==> SND(cpstep_apply s (H,x0)) IN dart(FST(cpstep_apply s (H,x0)))`,
  MATCH_MP_TAC cpstep_INDUCT THEN
  SIMP_TAC[cpstep_apply; FST; SND; ecpR; ECPRR_EQ; ECPR_PT_IN_DART;
           ECPRR_PT_IN_DART; ECPY_PT_IN_DART; ECPH_PT_IN_DART; ECPU_PT_IN_DART;
           ECPK_PT_IN_DART; ECPA_PT_IN_DART]);;

(* The pointer of the map of any program is one of its darts.                *)
let CPMAP_PT_IN_DART = prove
 (`!cp. SND(cpmap cp) IN dart(FST(cpmap cp))`,
  REWRITE_TAC[cpmap] THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST] THENL
   [REWRITE_TAC[FST; SND; CPMAP0_COMPONENTS; IN_INSERT];
    MP_TAC(ISPECL [`h:cpstep`; `FST(ITLIST cpstep_apply t (cpmap0,1))`;
                   `SND(ITLIST cpstep_apply t (cpmap0,1))`]
      CPSTEP_APPLY_PT) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[PAIR]]);;

(* ========================================================================= *)
(* The perimeter ring cpring and related (Gonthier cfmap.v:201-215).         *)
(* ========================================================================= *)

let orbit_list = new_definition
  `orbit_list (f:A->A) x = CONS x (iterlist (orbit_size f x - 1) f x)`;;

let LENGTH_ORBIT_LIST = prove
 (`!(f:A->A) x. 0 < orbit_size f x
     ==> LENGTH(orbit_list f x) = orbit_size f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_list; LENGTH; LENGTH_ITERLIST] THEN
  ASM_ARITH_TAC);;

(* The orbit size is the same at every point of an orbit.                    *)
let ORBIT_SIZE_STEP_GEN = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
     ==> orbit_size f (f x) = orbit_size f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_size] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `s:A->bool` THEN
  ASM_MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]);;

(* node-orbit size is invariant under a node step.                           *)
let ORBIT_SIZE_NODE_STEP = prove
 (`!(H:(num)hypermap) x. x IN dart H
     ==> orbit_size (node_map H) (node_map H x) = orbit_size (node_map H) x`,
  MESON_TAC[ORBIT_SIZE_STEP_GEN; FINITE_DART; NODE_MAP_PERMUTES]);;

(* cpring H x0 = rev(orbit node (node(node x0))) (Gonthier cfmap.v:201).     *)
let cpring = new_definition
  `cpring (H:(num)hypermap) x0 =
     REVERSE (orbit_list (node_map H) (node_map H (node_map H x0)))`;;

let proper_cpring = new_definition
  `proper_cpring (H:(num)hypermap) x0 <=> ~(x0 = node_map H x0)`;;

let cprsize = new_definition
  `cprsize (cp:(cpstep)list) =
   LENGTH (cpring (FST(cpmap cp)) (SND(cpmap cp)))`;;

(* The node orbit of a dart has positive size and closes up after it.        *)
let NODE_ORBIT_SIZE_POS = prove
 (`!(H:(A)hypermap) x. x IN dart H ==> 0 < orbit_size (node_map H) x`,
  MESON_TAC[ORBIT_SIZE_POS; FINITE_DART; NODE_MAP_PERMUTES]);;

let NODE_ITER_OSIZE = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> ITER (orbit_size (node_map H) x0) (node_map H) x0 = x0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ITER_ORBIT_SIZE THEN
  EXISTS_TAC `dart(H:(num)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES]);;

(* size_cpring: the ring length is the node-orbit size at the pointer        *)
(* (Gonthier size_cpring).                                                   *)
let SIZE_CPRING = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> LENGTH(cpring H x0) = orbit_size (node_map H) x0`,
  SIMP_TAC[cpring; LENGTH_REVERSE; LENGTH_ORBIT_LIST; NODE_ORBIT_SIZE_POS;
           NODE_MAP_IN_DART; ORBIT_SIZE_NODE_STEP]);;

(* Membership in orbit_list = membership in the orbit (the node-orbit of a   *)
(* dart enumerates exactly the cnode-class). Reduce any iterate mod the      *)
(* orbit size into [0, osize-1]; index 0 is the head x, the rest the tail.   *)
let MEM_ORBIT_LIST = prove
 (`!(f:A->A) s x y. FINITE s /\ f permutes s /\ x IN s
     ==> (MEM y (orbit_list f x) <=> y IN orbit_map f x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[orbit_list; MEM; MEM_ITERLIST; ORBIT_MAP_ITER] THEN
  SUBGOAL_THEN `0 < orbit_size (f:A->A) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `ITER (orbit_size (f:A->A) x) f x = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[ITER_ORBIT_SIZE]; ALL_TAC] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_MESON_TAC[ITER];
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    MP_TAC(ISPECL [`f:A->A`; `x:A`; `orbit_size (f:A->A) x`;
                   `n:num`] ITER_MOD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `n MOD orbit_size (f:A->A) x < orbit_size f x`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[MOD_LT_EQ] THEN ASM_MESON_TAC[LT_NZ]; ALL_TAC] THEN
    ASM_CASES_TAC `n MOD orbit_size (f:A->A) x = 0` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[ITER];
      DISJ2_TAC THEN EXISTS_TAC `n MOD orbit_size (f:A->A) x` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let NODE2_IN_ORBIT = prove
 (`!(H:(num)hypermap) z.
     node_map H (node_map H z) IN orbit_map (node_map H) z`,
  REWRITE_TAC[GSYM ITER2; ITER_IN_ORBIT]);;

(* MEM_CPRING (Gonthier cfmap.v:209): x is on the ring iff x is in the node  *)
(* orbit (cnode-class) of the pointer. cpring = rev(orbit node (node(node    *)
(* x0))), and the node orbit is the same set viewed from node(node x0) or    *)
(* x0.                                                                       *)
let MEM_CPRING = prove
 (`!(H:(num)hypermap) x0 x. x0 IN dart H
     ==> (MEM x (cpring H x0) <=> cnode H x0 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cpring; cnode; node; MEM_REVERSE] THEN
  MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                 `node_map H (node_map H (x0:num))`; `x:num`]
    MEM_ORBIT_LIST) THEN
  ASM_SIMP_TAC[FINITE_DART; NODE_MAP_PERMUTES; NODE_MAP_IN_DART] THEN
  DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(num)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; NODE2_IN_ORBIT]);;

(* SIZE_PROPER_CPRING (Gonthier cfmap.v:215): the ring is proper (x0 is not  *)
(* a fixpoint of node) iff it has more than one element: node x0 = x0 iff    *)
(* the node orbit has size 1 (ITER 1 node x0 = x0 iff the orbit size divides *)
(* 1).                                                                       *)
let SIZE_PROPER_CPRING = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> (proper_cpring H x0 <=> 1 < LENGTH(cpring H x0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIZE_CPRING; proper_cpring] THEN
  MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                 `x0:num`; `1`] ORBIT_SIZE_DIVIDES) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] NODE_ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; ITER_1; DIVIDES_ONE] THEN
  ARITH_TAC);;

(* SIZE_LONG_CPRING (Gonthier cfmap.v:222): the ring is "long" (face(edge    *)
(* x0) not = node x0) iff it has more than two elements: by edgeK and the    *)
(* injectivity of node, face(edge x0) = node x0 iff node(node x0) = x0, iff  *)
(* the orbit size divides 2.                                                 *)
let SIZE_LONG_CPRING = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> (long_cpring H x0 <=> 2 < LENGTH(cpring H x0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIZE_CPRING; long_cpring] THEN
  SUBGOAL_THEN `face_map H (edge_map H (x0:num)) = node_map H x0 <=>
                ITER 2 (node_map H) x0 = x0`
  SUBST1_TAC THENL
   [REWRITE_TAC[ITER2] THEN MESON_TAC[NODEI; edgeK]; ALL_TAC] THEN
  MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                 `x0:num`; `2`] ORBIT_SIZE_DIVIDES) THEN
  ASM_SIMP_TAC[FINITE_DART; NODE_MAP_PERMUTES; NOT_DIVIDES_2;
               NODE_ORBIT_SIZE_POS]);;

(* The last element of orbit_list f x is f^(osize-1) x, the far end of the   *)
(* orbit.                                                                    *)
let LAST_ORBIT_LIST = prove
 (`!(f:A->A) x. 0 < orbit_size f x
     ==> LAST(orbit_list f x) = ITER (orbit_size f x - 1) f x`,
  REWRITE_TAC[orbit_list; LAST_ITERLIST]);;

(* The ring is always nonempty (its length is the positive node-orbit size). *)
let CPRING_NONEMPTY = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> ~(cpring H x0 = [])`,
  SIMP_TAC[GSYM LENGTH_EQ_NIL; SIZE_CPRING; NODE_ORBIT_SIZE_POS;
           ARITH_RULE `0 < n ==> ~(n = 0)`]);;

(* ------------------------------------------------------------------------- *)
(* Indexed view of the ring: EL k (cpring H x0) as an explicit node iterate. *)
(* This subsumes HEAD_CPRING (k = 0) and pins the second and third elements  *)
(* (x0 and face (edge x0)), the data behind Gonthier's head_proper_cpring    *)
(* and head_long_cpring (cfmap.v:255,264).                                   *)
(* ------------------------------------------------------------------------- *)

(* j-th element of iterlist n f x is f^(j+1) x; of orbit_list f x is f^j x.  *)
let EL_ITERLIST = prove
 (`!n j (f:A->A) x. j < n ==> EL j (iterlist n f x) = ITER (j+1) f x`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REWRITE_TAC[iterlist] THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[EL; HD; ADD_CLAUSES; ITER_1];
    REWRITE_TAC[EL; TL; LT_SUC] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `f:A->A`; `(f:A->A) x`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; CONJUNCT2 ITER_ALT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

let EL_ORBIT_LIST = prove
 (`!(f:A->A) x j. j < orbit_size f x ==> EL j (orbit_list f x) = ITER j f x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[orbit_list] THEN
  STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THENL
   [REWRITE_TAC[EL; HD; ITER];
    REWRITE_TAC[EL; TL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`orbit_size (f:A->A) x - 1`; `n:num`; `f:A->A`; `x:A`]
      EL_ITERLIST) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD1]]);;

(* The master indexed-ring lemma. cpring = rev(orbit node (node(node x0))),  *)
(* so element k counts backwards from the orbit's end: EL k = node^((s+1)-k) *)
(* x0 where s = osize node x0. k=0 -> node x0, k=1 -> x0, k=2 -> node^(s-1)  *)
(* = inverse(node) = face(edge x0). NB the exponent must be written (s+1)-k: *)
(* "-" binds more tightly than "+", so s + 1 - k would mean s + (1 - k).     *)
let EL_CPRING = prove
 (`!(H:(num)hypermap) x0 k. x0 IN dart H /\ k < orbit_size (node_map H) x0
     ==> EL k (cpring H x0) =
     ITER ((orbit_size (node_map H) x0 + 1) - k) (node_map H) x0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `orbit_size (node_map H) (node_map H (node_map H (x0:num))) =
    orbit_size (node_map H) x0`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ORBIT_SIZE_NODE_STEP; NODE_MAP_IN_DART]; ALL_TAC] THEN
  ASM_SIMP_TAC[cpring; EL_REVERSE; LENGTH_ORBIT_LIST; EL_ORBIT_LIST;
               NODE_ORBIT_SIZE_POS; NODE_MAP_IN_DART; LENGTH_REVERSE;
               ARITH_RULE `k < s ==> s - 1 - k < s`] THEN
  REWRITE_TAC[GSYM ITER2; ITER_ADD] THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* The ring starts at node x0: EL_CPRING at k = 0, node^(osize+1) x0 = node  *)
(* x0.                                                                       *)
let HEAD_CPRING = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> HD(cpring H x0) = node_map H x0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `0`] EL_CPRING) THEN
  ASM_SIMP_TAC[EL; SUB_0; GSYM ADD1; ITER; NODE_ORBIT_SIZE_POS;
               NODE_ITER_OSIZE]);;

(* CPRING_CONS_HEAD (Gonthier head_cpring, cfmap.v:249): cpring = node x0 :: *)
(* behead cpring.                                                            *)
let CPRING_CONS_HEAD = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> cpring H x0 = CONS (node_map H x0) (TL(cpring H x0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CPRING_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC LAND_CONV [MATCH_MP CONS_HD_TL th]) THEN
  ASM_SIMP_TAC[HEAD_CPRING]);;

(* The second ring element is the pointer x0 itself (Gonthier                *)
(* head_proper_cpring: a proper ring is node x0 :: x0 :: drop 2).            *)
let CPRING_EL1 = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ 1 < orbit_size (node_map H) x0
     ==> EL 1 (cpring H x0) = x0`,
  SIMP_TAC[EL_CPRING; ADD_SUB; NODE_ITER_OSIZE]);;

(* the last ring element: node^(d-1) x0 = face(edge x0) (Gonthier nodeK).    *)
let NODE_ITER_PRED = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> ITER (orbit_size (node_map H) x0 - 1) (node_map H) x0 =
         face_map H (edge_map H x0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `H:(num)hypermap` NODEI) THEN
  REWRITE_TAC[edgeK] THEN ONCE_REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN
  MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                 `x0:num`] ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN DISCH_TAC THEN
  SUBGOAL_THEN `SUC(orbit_size (node_map H) (x0:num) - 1) =
                orbit_size (node_map H) x0` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[NODE_ITER_OSIZE]]);;

(* The third ring element is face(edge x0) (Gonthier head_long_cpring: a     *)
(* long ring is node x0 :: x0 :: face(edge x0) :: drop 3).                   *)
let CPRING_EL2 = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ 2 < orbit_size (node_map H) x0
     ==> EL 2 (cpring H x0) = face_map H (edge_map H x0)`,
  SIMP_TAC[EL_CPRING; NODE_ITER_PRED;
           ARITH_RULE `2 < s ==> (s + 1) - 2 = s - 1`]);;

(* A list with at least two (three) elements is its first two (three)        *)
(* elements followed by the rest.                                            *)
let CONS_EL012 = prove
 (`!l:(A)list.
     (1 < LENGTH l ==> l = CONS (EL 0 l) (CONS (EL 1 l) (TL(TL l)))) /\
     (2 < LENGTH l
      ==> l = CONS (EL 0 l) (CONS (EL 1 l) (CONS (EL 2 l) (TL(TL(TL l))))))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH] THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH] THEN
  STRUCT_CASES_TAC(ISPEC `t':(A)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH] THEN
  REWRITE_TAC[EL; HD; TL; ARITH_RULE `1 = SUC 0 /\ 2 = SUC 1`]);;

(* HEAD_PROPER_CPRING (Gonthier cfmap.v:264): a proper ring starts node x0,  *)
(* x0, ... (TL TL = Gonthier's drop 2).                                      *)
let HEAD_PROPER_CPRING = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> cpring H x0 = CONS (node_map H x0) (CONS x0 (TL(TL(cpring H x0))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 < orbit_size (node_map H) (x0:num)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIZE_PROPER_CPRING; SIZE_CPRING]; ALL_TAC] THEN
  MP_TAC(CONJUNCT1(ISPEC `cpring H (x0:num)` CONS_EL012)) THEN
  ASM_SIMP_TAC[SIZE_CPRING; EL; HEAD_CPRING; CPRING_EL1]);;

(* HEAD_LONG_CPRING (Gonthier cfmap.v:255): a long ring starts node x0, x0,  *)
(* face(edge x0), ... (TL TL TL = drop 3).                                   *)
let HEAD_LONG_CPRING = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ long_cpring H x0
     ==> cpring H x0 =
         CONS (node_map H x0) (CONS x0 (CONS (face_map H (edge_map H x0))
              (TL(TL(TL(cpring H x0))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 < orbit_size (node_map H) (x0:num)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIZE_LONG_CPRING; SIZE_CPRING]; ALL_TAC] THEN
  MP_TAC(CONJUNCT2(ISPEC `cpring H (x0:num)` CONS_EL012)) THEN
  ASM_SIMP_TAC[SIZE_CPRING; EL; HEAD_CPRING; CPRING_EL1; CPRING_EL2;
               ARITH_RULE `2 < n ==> 1 < n`]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise evaluation of the step maps on the fresh darts a,b and on the   *)
(* old darts.                                                                *)
(* ------------------------------------------------------------------------- *)

(* Each clause lemma unfolds a definition and splits on its conditions.      *)
let ECP_CLAUSES_TAC def =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[def] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[];;

let ECPU_EDGE_CLAUSES = prove
 (`!(H:(num)hypermap) a b.
     ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> ecpU_edge H a b a = b /\ ecpU_edge H a b b = a /\
         (!d. d IN dart H ==> ecpU_edge H a b d = edge_map H d)`,
  ECP_CLAUSES_TAC ecpU_edge);;

let ECPU_NODE_CLAUSES = prove
 (`!(H:(num)hypermap) x0 a b.
     ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> ecpU_node H x0 a b a = b /\
         ecpU_node H x0 a b b = node_map H (node_map H x0) /\
         (!d. d IN dart H
              ==> ecpU_node H x0 a b d =
                  (if d = node_map H x0 then a else node_map H d))`,
  ECP_CLAUSES_TAC ecpU_node);;

let ECPU_FACE_CLAUSES = prove
 (`!(H:(num)hypermap) x0 a b.
     ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> ecpU_face H x0 a b a = a /\
         ecpU_face H x0 a b b = node_map H x0 /\
         (!d. d IN dart H
              ==> ecpU_face H x0 a b d =
                  (if face_map H d = node_map H x0 then b else face_map H d))`,
  ECP_CLAUSES_TAC ecpU_face);;

let ECPN_NODE_CLAUSES = prove
 (`!(H:(num)hypermap) x0 a b.
     ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> ecpN_node H x0 a b a =
         (if long_cpring H x0 then node_map H x0 else a) /\
         ecpN_node H x0 a b b = face_map H (edge_map H x0) /\
         (!d. d IN dart H
              ==> ecpN_node H x0 a b d =
                  (if d = x0 then b
                   else if node_map H (node_map H d) = x0 then a
                   else node_map H d))`,
  ECP_CLAUSES_TAC ecpN_node);;

let ECPN_FACE_CLAUSES = prove
 (`!(H:(num)hypermap) x0 a b.
     ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> ecpN_face H x0 a b a = x0 /\
         ecpN_face H x0 a b b =
         (if long_cpring H x0
          then face_map H (edge_map H (face_map H (edge_map H x0))) else a) /\
         (!d. d IN dart H
              ==> ecpN_face H x0 a b d =
                  (if d = edge_map H (face_map H (edge_map H x0)) then b
                   else if d = edge_map H (node_map H x0) then a
                   else face_map H d))`,
  ECP_CLAUSES_TAC ecpN_face);;

(* Standard opening for a lemma about a U or N step on the map hy at the     *)
(* pointer pt: name the fresh darts an,bn, record their freshness, the       *)
(* components of the new map and the pointwise clauses of its three maps.    *)
let ECP_GEN_TAC comps clauses nm hy pt an bn =
  let inst = vsubst [hy,`H:(num)hypermap`; pt,`x0:num`; an,`a:num`; bn,`b:num`;
                     nm,`G:(num)hypermap`] in
  MP_TAC(ISPEC (inst `dart(H:(num)hypermap)`) NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN
  SUBGOAL_THEN (inst `(x0:num) IN dart(H:(num)hypermap)`) MP_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT];
    DISCH_THEN(MP_TAC o MATCH_MP (ISPECL [hy; pt] comps))] THEN
  REWRITE_TAC[ecpU_pt; ecpN_pt] THEN
  ABBREV_TAC (inst `a = FST(new_dart2(dart(H:(num)hypermap)))`) THEN
  ABBREV_TAC (inst `b = SND(new_dart2(dart(H:(num)hypermap)))`) THEN
  STRIP_TAC THEN DISCH_THEN(fun fr ->
    MAP_EVERY (fun th -> MP_TAC(MATCH_MP th fr))
      (ISPECL [hy; an; bn] ECPU_EDGE_CLAUSES ::
       map (ISPECL [hy; pt; an; bn]) clauses) THEN
    STRIP_ASSUME_TAC fr) THEN
  EVERY(replicate STRIP_TAC (length clauses + 1)) THEN
  SUBGOAL_THEN (inst `!d. d IN dart(H:(num)hypermap)
                          ==> ~(a:num = d) /\ ~(d = a) /\
                              ~(b:num = d) /\ ~(d = b)`)
  ASSUME_TAC THENL
   [UNDISCH_TAC (inst `~((a:num) IN dart(H:(num)hypermap))`) THEN
    UNDISCH_TAC (inst `~((b:num) IN dart(H:(num)hypermap))`) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (inst `(a:num) IN dart(G:(num)hypermap) /\ (b:num) IN dart G /\
                      (x0:num) IN dart G /\
                      (!d. d IN dart(H:(num)hypermap) ==> d IN dart G)`)
  (MAP_EVERY ASSUME_TAC o CONJUNCTS) THENL
   [ASM_REWRITE_TAC[IN_INSERT] THEN SIMP_TAC[]; ALL_TAC];;

let ECPU_TAC =
  ECP_GEN_TAC ECPU_COMPONENTS [ECPU_NODE_CLAUSES; ECPU_FACE_CLAUSES]
    `ecpU H x0` `H:(num)hypermap` `x0:num` `a:num` `b:num`;;
let ECPN_ON_TAC hy pt an bn =
  ECP_GEN_TAC ECPN_COMPONENTS [ECPN_NODE_CLAUSES; ECPN_FACE_CLAUSES]
    (vsubst [hy,`H:(num)hypermap`; pt,`x0:num`] `ecpN H x0`) hy pt an bn;;
let ECPN_TAC = ECPN_ON_TAC `H:(num)hypermap` `x0:num` `a:num` `b:num`;;

(* ========================================================================= *)
(* Plainness of the construction. Every config/cubic map is plain (edge is   *)
(* an involution): cpmap0 is plain (edge = swap(0,1)), and every ecp step    *)
(* preserves plainness (each step's edge map either swaps the two fresh      *)
(* darts or acts as the old edge map).                                       *)
(* ========================================================================= *)

(* A plain map is one whose edge map is a fixpoint-free involution.          *)
let PLAIN_HYPERMAP_INVOLUTION = prove
 (`!H:(A)hypermap.
     plain_hypermap H <=>
     !x. x IN dart H
         ==> edge_map H (edge_map H x) = x /\ ~(edge_map H x = x)`,
  MESON_TAC[plain_hypermap; PLAIN_EQ; PLAIN_NEQ; ORBIT_SIZE_EQ_2;
            FINITE_DART; EDGE_MAP_PERMUTES]);;

(* The U and N steps share the edge map ecpU_edge, which swaps the two fresh *)
(* darts and agrees with the old edge map on the old darts.                  *)
let PLAIN_ECPU = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ plain_hypermap H
     ==> plain_hypermap (ecpU H x0)`,
  REPEAT STRIP_TAC THEN ECPU_TAC THEN
  ASM_REWRITE_TAC[PLAIN_HYPERMAP_INVOLUTION; IN_INSERT] THEN
  X_GEN_TAC `y:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; PLAIN_EQ; PLAIN_NEQ]);;

let PLAIN_ECPN = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ plain_hypermap H
     ==> plain_hypermap (ecpN H x0)`,
  REPEAT STRIP_TAC THEN ECPN_TAC THEN
  ASM_REWRITE_TAC[PLAIN_HYPERMAP_INVOLUTION; IN_INSERT] THEN
  X_GEN_TAC `y:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; PLAIN_EQ; PLAIN_NEQ]);;

(* ecpY = ecpN o ecpU, ecpH = ecpN o ecpY : plainness composes.              *)
let PLAIN_ECPY = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ plain_hypermap H
     ==> plain_hypermap (ecpY H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY] THEN
  MATCH_MP_TAC PLAIN_ECPN THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART] THEN
  MATCH_MP_TAC PLAIN_ECPU THEN ASM_REWRITE_TAC[]);;

let PLAIN_ECPH = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ plain_hypermap H
     ==> plain_hypermap (ecpH H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MATCH_MP_TAC PLAIN_ECPN THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART] THEN
  MATCH_MP_TAC PLAIN_ECPY THEN ASM_REWRITE_TAC[]);;

(* cpmap0 (base map) is plain: edge = swap(0,1), an involution on {0,1}.     *)
let PLAIN_CPMAP0 = prove
 (`plain_hypermap cpmap0`,
  REWRITE_TAC[PLAIN_HYPERMAP_INVOLUTION; CPMAP0_COMPONENTS; FORALL_IN_INSERT;
              NOT_IN_EMPTY; swap] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Every cubic program produces a plain map (Gonthier cpmap_plain).          *)
let CPMAP_PLAIN = prove
 (`!cp. cubic_prog cp ==> plain_hypermap (FST(cpmap cp))`,
  MATCH_MP_TAC CUBIC_PROG_INDUCT THEN
  SIMP_TAC[CPMAP_NIL_PAIR; CPMAP_CONS_R; CPMAP_CONS_U_PAIR; CPMAP_CONS_Y;
           CPMAP_CONS_H; ecpR; PLAIN_CPMAP0; PLAIN_ECPU; PLAIN_ECPY;
           PLAIN_ECPH; CPMAP_PT_IN_DART]);;

(* ========================================================================= *)
(* proper_cpring / long_cpring of the construction steps (toward             *)
(* CPMAP_PROPER cfmap.v:1143 and CFMAP_LONG cfmap.v:1154). proper_cpring H   *)
(* x0 = ~(x0 = node x0); long_cpring H x0 = ~(face(edge x0) = node x0) --    *)
(* evaluable at the new pointer directly from the step's map definitions, no *)
(* ring machinery.                                                           *)
(* ========================================================================= *)

let LONG_ECPU = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> long_cpring (ecpU H x0) (ecpU_pt H)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[long_cpring] THEN ECPU_TAC THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART]);;

(* ------------------------------------------------------------------------- *)
(* Ring-SIZE deltas (= node-orbit-size deltas at the new pointer;            *)
(* SIZE_CPRING turns these into LENGTH(cpring) deltas). ecpU adds 2 to the   *)
(* node orbit, ecpN subtracts 1. These are the quantitative core behind      *)
(* CPMAP_PROPER / CFMAP_LONG (and later cubic/connected/planar).             *)
(* ------------------------------------------------------------------------- *)

(* The ecpU node map keeps {a, b} U (node-orbit of x0) invariant: a->b,      *)
(* b->node^2 x0, node x0->a, other old darts d->node d.                      *)
let ECPU_NODE_CLOSED = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ node_map H permutes dart H /\ ~(a IN dart H) /\
     ~(b IN dart H) /\ ~(a = b)
     ==> (!y. y IN (a INSERT b INSERT orbit_map (node_map H) x0)
              ==> ecpU_node H x0 a b y IN
              (a INSERT b INSERT orbit_map (node_map H) x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:num` THEN
  REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[ecpU_node];
    ASM_REWRITE_TAC[ecpU_node] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN
    REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN
    EXISTS_TAC `2` THEN REWRITE_TAC[ITER2];
    SUBGOAL_THEN `(y:num) IN dart H` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                     `x0:num`; `y:num`] ORBIT_MAP_IN) THEN
      ASM_REWRITE_TAC[FINITE_DART]; ALL_TAC] THEN
    MP_TAC(ISPECL [`y:num`; `a:num`; `dart(H:(num)hypermap)`]
      IN_NOTIN_NEQ) THEN
    MP_TAC(ISPECL [`y:num`; `b:num`; `dart(H:(num)hypermap)`]
      IN_NOTIN_NEQ) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[ecpU_node] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN
    UNDISCH_TAC `(y:num) IN orbit_map (node_map H) x0` THEN
    REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    EXISTS_TAC `SUC n` THEN REWRITE_TAC[ITER]]);;

(* Every node-orbit element of x0 is reached from a in the ecpU node orbit:  *)
(* the cycle a->b->node^2 x0->node^3 x0->...->x0->node x0->a threads it all. *)
let ECPU_ORBIT_THREAD = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ node_map H permutes dart H /\ ~(a IN dart H) /\
     ~(b IN dart H) /\ ~(a = b) /\
     b = ecpU_node H x0 a b a /\
     ecpU_node H x0 a b b = node_map H (node_map H x0)
     ==> !k. ITER k (node_map H) (node_map H (node_map H x0)) IN orbit_map
     (ecpU_node H x0 a b) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `N' = ecpU_node H x0 a b` THEN
  SUBGOAL_THEN `(b:num) IN orbit_map N' a` ASSUME_TAC THENL
   [ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ITER_1]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map H (node_map H (x0:num)) IN orbit_map N' a`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_MAP_STEP]; ALL_TAC] THEN
  INDUCT_TAC THENL [ASM_REWRITE_TAC[ITER]; ALL_TAC] THEN
  REWRITE_TAC[ITER] THEN
  ABBREV_TAC `z = ITER k (node_map H) (node_map H (node_map H (x0:num)))` THEN
  SUBGOAL_THEN `(z:num) IN dart H` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    SUBGOAL_THEN `node_map H (node_map H (x0:num)) IN dart H` MP_TAC THENL
     [ASM_SIMP_TAC[NODE_FACE_IN_DART]; ALL_TAC] THEN
    SPEC_TAC(`node_map H (node_map H (x0:num))`,`w:num`) THEN
    GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`k:num`,`m:num`) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[ITER; NODE_FACE_IN_DART]; ALL_TAC] THEN
  ASM_CASES_TAC `z:num = node_map H x0` THENL
   [ASM_REWRITE_TAC[];
    SUBGOAL_THEN `node_map H (z:num) = N' z` SUBST1_TAC THENL
     [EXPAND_TAC "N'" THEN REWRITE_TAC[ecpU_node] THEN
      MP_TAC(ISPECL [`z:num`; `a:num`; `dart(H:(num)hypermap)`]
        IN_NOTIN_NEQ) THEN
      MP_TAC(ISPECL [`z:num`; `b:num`; `dart(H:(num)hypermap)`]
        IN_NOTIN_NEQ) THEN
      ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN ASSUME_TAC) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[ORBIT_MAP_STEP]]]);;

(* The node orbit of the new pointer of a U step: a -> b -> node^2 x0 -> ... *)
(* -> x0 -> node x0 -> a.                                                    *)
let ORBIT_ECPU_PT = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> orbit_map (node_map(ecpU H x0)) (ecpU_pt H) =
         ecpU_pt H INSERT SND(new_dart2(dart H)) INSERT
         orbit_map (node_map H) x0`,
  REPEAT STRIP_TAC THEN ECPU_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC ORBIT_IN_CLOSED THEN CONJ_TAC THENL
     [MATCH_MP_TAC ECPU_NODE_CLOSED THEN ASM_REWRITE_TAC[NODE_MAP_PERMUTES];
      REWRITE_TAC[IN_INSERT]];
    REWRITE_TAC[INSERT_SUBSET; IN_ORBIT_MAP_REFL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `orbit_map (node_map H) (x0:num) =
      orbit_map (node_map H) (node_map H (node_map H x0))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
      EXISTS_TAC `dart(H:(num)hypermap)` THEN
      ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; NODE2_IN_ORBIT];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; ORBIT_MAP_ITER] THEN X_GEN_TAC `w:num` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `a:num`; `b:num`]
      ECPU_ORBIT_THREAD) THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; ORBIT_MAP_ITER] THEN MESON_TAC[]]);;

(* SIZE_CPRING_ECPU: the U step adds 2 to the ring size (node-orbit size).   *)
let SIZE_CPRING_ECPU = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> orbit_size (node_map(ecpU H x0)) (ecpU_pt H) =
     orbit_size (node_map H) x0 + 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[orbit_size; ORBIT_ECPU_PT] THEN
  ECPU_TAC THEN
  SUBGOAL_THEN `orbit_map (node_map H) (x0:num) SUBSET dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SUBSET; NODE_MAP_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(orbit_map (node_map H) (x0:num)) /\
    ~((a:num) IN orbit_map (node_map H) x0) /\
    ~(b IN orbit_map (node_map H) x0)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DART; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; IN_INSERT] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Generic orbit tools: distinct iterates below the period, orbit size from  *)
(* a minimal period, threading one permutation along another, and a ring     *)
(* determined by its indexed elements (EL_CPRING in reverse).                *)
(* ------------------------------------------------------------------------- *)

let ITER_INJ_PERIOD = prove
 (`!(f:A->A) s y i j.
     FINITE s /\ f permutes s /\ y IN s /\ i < j /\ j < orbit_size f y
     ==> ~(ITER i f y = ITER j f y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `i:num`; `j:num`; `y:A`] ITER_CANCEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PERMUTES_INJ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `y:A`; `j - i:num`]
    ORBIT_SIZE_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let ORBIT_SIZE_MINIMAL = prove
 (`!(f:A->A) s z m.
     FINITE s /\ f permutes s /\ z IN s /\ 0 < m /\ ITER m f z = z /\
     (!j. 0 < j /\ j < m ==> ~(ITER j f z = z))
     ==> orbit_size f z = m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORBIT_SIZE_PERIOD THEN
  EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`f:A->A`; `z:A`; `m:num`; `n:num`] ITER_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD] THEN
  ASM_CASES_TAC `n MOD m = 0` THEN ASM_REWRITE_TAC[ITER] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[MOD_LT_EQ; LT_NZ] THEN ASM_ARITH_TAC);;

let ITER_THREAD = prove
 (`!(f:A->A) g x z m M.
     ITER m g z = ITER m f x /\
     (!j. m <= j /\ j < M ==> g (ITER j f x) = f (ITER j f x))
     ==> !j. m <= j /\ j <= M ==> ITER j g z = ITER j f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ITER] THEN
  SUBGOAL_THEN `ITER j g (z:A) = ITER j f x` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CPRING_BY_EL = prove
 (`!(G:(num)hypermap) x0 l.
     x0 IN dart G /\ LENGTH l = orbit_size (node_map G) x0 /\
     (!k. k < orbit_size (node_map G) x0
          ==> EL k l =
              ITER ((orbit_size (node_map G) x0 + 1) - k) (node_map G) x0)
     ==> cpring G x0 = l`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  ASM_SIMP_TAC[SIZE_CPRING; EL_CPRING]);;

(* proper / long rings in terms of the node-orbit size.                      *)
let PROPER_OSIZE = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> (proper_cpring H x0 <=> 1 < orbit_size (node_map H) x0)`,
  SIMP_TAC[SIZE_PROPER_CPRING; SIZE_CPRING]);;

let LONG_OSIZE = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> (long_cpring H x0 <=> 2 < orbit_size (node_map H) x0)`,
  SIMP_TAC[SIZE_LONG_CPRING; SIZE_CPRING]);;

(* iterates of the node map at x0 below the orbit size are distinct from     *)
(* x0 and from node x0.                                                      *)
let NODE_ITER_NEQ = prove
 (`!(H:(num)hypermap) x0 j.
     x0 IN dart H /\ 0 < j /\ j < orbit_size (node_map H) x0
     ==> ~(ITER j (node_map H) x0 = x0) /\
         (1 < j ==> ~(ITER j (node_map H) x0 = node_map H x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                   `x0:num`; `0`; `j:num`] ITER_INJ_PERIOD);
    DISCH_TAC THEN
    MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                   `x0:num`; `1`; `j:num`] ITER_INJ_PERIOD)] THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; ITER; ITER_1] THEN
  ASM_MESON_TAC[]);;

let ECPU_NODE_ITER = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ 1 < orbit_size (node_map H) x0 /\
     ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> (!j. 2 <= j /\ j <= orbit_size (node_map H) x0 + 1
              ==> ITER j (ecpU_node H x0 a b) a = ITER j (node_map H) x0) /\
         ITER (orbit_size (node_map H) x0 + 2) (ecpU_node H x0 a b) a = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `a:num`; `b:num`]
    ECPU_NODE_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC ITER_THREAD THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[ITER2]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ITER_PERMUTES_IN; NODE_MAP_PERMUTES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `j = orbit_size (node_map H) (x0:num)` THENL
     [UNDISCH_TAC `ITER j (node_map H) (x0:num) = node_map H x0` THEN
      ASM_SIMP_TAC[NODE_ITER_OSIZE] THEN
      MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `1`] NODE_ITER_NEQ) THEN
      ASM_REWRITE_TAC[ITER_1; ARITH] THEN MESON_TAC[];
      MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `j:num`] NODE_ITER_NEQ) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `orbit_size (node_map H) (x0:num) + 1`) THEN
    REWRITE_TAC[ARITH_RULE `2 <= d + 1 <=> 1 <= d`; LE_REFL] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 < d ==> 1 <= d`] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `d + 2 = SUC(d + 1)`; ITER] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `d + 1 = SUC d`; ITER] THEN
    ASM_SIMP_TAC[NODE_ITER_OSIZE; NODE_MAP_IN_DART]]);;

let CPRING_ECPU = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ 1 < orbit_size (node_map H) x0
     ==> cpring (ecpU H x0) (ecpU_pt H) =
         CONS (SND(new_dart2(dart H))) (CONS (ecpU_pt H) (cpring H x0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CPRING_BY_EL THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART; SIZE_CPRING_ECPU; LENGTH; SIZE_CPRING] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ECPU_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `a:num`; `b:num`]
    ECPU_NODE_ITER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `d = orbit_size (node_map H) (x0:num)` THEN
  ASM_CASES_TAC `k = 0` THENL
   [POP_ASSUM SUBST1_TAC THEN
    ASM_REWRITE_TAC[EL; HD; SUB_0; ARITH_RULE `(d + 2) + 1 = SUC(d + 2)`;
                    ITER];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [POP_ASSUM SUBST1_TAC THEN
    ASM_REWRITE_TAC[EL_CONS; ARITH; ARITH_RULE `((d + 2) + 1) - 1 = d + 2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. k = SUC(SUC m)` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `k - 2` THEN ASM_ARITH_TAC; REWRITE_TAC[EL; TL]] THEN
  SUBGOAL_THEN `((d + 2) + 1) - SUC(SUC m) = (d + 1) - m` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `(d + 1) - m` th)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "d" THEN MATCH_MP_TAC EL_CPRING THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The node orbit of the new pointer of ecpN (long case): a -> node x0 ->    *)
(* node^2 x0 -> ... -> node^(d-2) x0 -> a, of size d - 1.                    *)
(* ------------------------------------------------------------------------- *)

let ECPN_NODE_ITER = prove
 (`!(H:(num)hypermap) x0 a b.
     x0 IN dart H /\ long_cpring H x0 /\
     ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a = b)
     ==> (!j. 1 <= j /\ j <= orbit_size (node_map H) x0 - 2
              ==> ITER j (ecpN_node H x0 a b) a = ITER j (node_map H) x0) /\
         ITER (orbit_size (node_map H) x0 - 1) (ecpN_node H x0 a b) a = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `a:num`; `b:num`]
    ECPN_NODE_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LONG_OSIZE) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = orbit_size (node_map H) (x0:num)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. 0 < j /\ j + 2 < d
        ==> ecpN_node H x0 a b (ITER j (node_map H) x0) =
            node_map H (ITER j (node_map H) x0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ITER_PERMUTES_IN; NODE_MAP_PERMUTES; ITER_NODE_TWICE] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `j + 2`] NODE_ITER_NEQ) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `j:num`] NODE_ITER_NEQ) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `j + 2 < d ==> j < d`; ARITH_RULE `0 < j + 2`];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC ITER_THREAD THEN ASM_REWRITE_TAC[ITER_1] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `d - 2`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `d - 1 = SUC(d - 2)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ITER] THEN
    ASM_SIMP_TAC[ITER_PERMUTES_IN; NODE_MAP_PERMUTES; ITER_NODE_TWICE] THEN
    SUBGOAL_THEN `d - 2 + 2 = d` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "d" THEN ASM_SIMP_TAC[NODE_ITER_OSIZE] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `d - 2`] NODE_ITER_NEQ) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

let SIZE_CPRING_ECPN = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ long_cpring H x0
     ==> orbit_size (node_map(ecpN H x0)) (ecpN_pt H) =
         orbit_size (node_map H) x0 - 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LONG_OSIZE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ECPN_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `a:num`; `b:num`]
    ECPN_NODE_ITER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC ORBIT_SIZE_MINIMAL THEN
  EXISTS_TAC `a INSERT b INSERT dart(H:(num)hypermap)` THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_DART; IN_INSERT; ECPN_PERMUTES] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_MESON_TAC[ITER_PERMUTES_IN; NODE_MAP_PERMUTES]);;

let CPRING_ECPN = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ long_cpring H x0
     ==> cpring (ecpN H x0) (ecpN_pt H) =
         CONS (node_map H x0) (CONS (ecpN_pt H) (TL(TL(TL(cpring H x0)))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LONG_OSIZE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC CPRING_BY_EL THEN
  ASM_SIMP_TAC[ECPN_PT_IN_DART; SIZE_CPRING_ECPN; LENGTH; LENGTH_TL3;
               SIZE_CPRING; ARITH_RULE `2 < d ==> 3 <= d`] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ECPN_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `a:num`; `b:num`]
    ECPN_NODE_ITER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `d = orbit_size (node_map H) (x0:num)` THEN
  ASM_CASES_TAC `k = 0` THENL
   [POP_ASSUM SUBST1_TAC THEN
    SUBGOAL_THEN `((d - 1) + 1) - 0 = SUC(d - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[EL; HD; ITER]];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [POP_ASSUM SUBST1_TAC THEN
    SUBGOAL_THEN `((d - 1) + 1) - 1 = d - 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[EL_CONS; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. k = SUC(SUC m)` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `k - 2` THEN ASM_ARITH_TAC;
    REWRITE_TAC[EL; TL] THEN REWRITE_TAC[EL_TL]] THEN
  SUBGOAL_THEN `((d - 1) + 1) - SUC(SUC m) = (d + 1) - (((m + 1) + 1) + 1)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `(d + 1) - (((m + 1) + 1) + 1)` th)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "d" THEN MATCH_MP_TAC EL_CPRING THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Ring sizes and shapes of the derived steps ecpY, ecpH, ecpR (Gonthier     *)
(* size_cpring_ecpY/H/R, cpring_ecpY/H, long_ecpY).                          *)
(* ------------------------------------------------------------------------- *)

let SIZE_CPRING_ECPY = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> orbit_size (node_map(ecpY H x0)) (ecpY_pt H x0) =
         orbit_size (node_map H) x0 + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY; ecpY_pt] THEN
  ASM_SIMP_TAC[SIZE_CPRING_ECPN; ECPU_PT_IN_DART; LONG_ECPU;
               SIZE_CPRING_ECPU] THEN
  ARITH_TAC);;

let LONG_ECPY = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> long_cpring (ecpY H x0) (ecpY_pt H x0)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LONG_OSIZE; ECPY_PT_IN_DART; SIZE_CPRING_ECPY] THEN
  FIRST_X_ASSUM(MP_TAC o CONJ (ASSUME `x0 IN dart(H:(num)hypermap)`)) THEN
  ASM_SIMP_TAC[PROPER_OSIZE] THEN ARITH_TAC);;

let SIZE_CPRING_ECPH = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ 1 < orbit_size (node_map H) x0
     ==> orbit_size (node_map(ecpH H x0)) (ecpH_pt H x0) =
         orbit_size (node_map H) x0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH; ecpH_pt] THEN
  ASM_SIMP_TAC[SIZE_CPRING_ECPN; ECPY_PT_IN_DART; LONG_ECPY; PROPER_OSIZE;
               SIZE_CPRING_ECPY] THEN
  ARITH_TAC);;

let OSIZE_ECPR = prove
 (`!(H:(num)hypermap) n x0. x0 IN dart H
     ==> orbit_size (node_map(ecpR H n x0)) (ecpR_pt H n x0) =
         orbit_size (node_map H) x0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpR; ecpR_pt; orbit_size] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
  EXISTS_TAC `dart(H:(num)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; ITER_IN_ORBIT]);;

let MEM_CPRING_ECPR = prove
 (`!(H:(num)hypermap) n x0 x. x0 IN dart H
     ==> (MEM x (cpring (ecpR H n x0) (ecpR_pt H n x0)) <=>
          MEM x (cpring H x0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpR; ecpR_pt] THEN
  ASM_SIMP_TAC[MEM_CPRING; ITER_PERMUTES_IN; NODE_MAP_PERMUTES; cnode;
               node] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
  EXISTS_TAC `dart(H:(num)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; ITER_IN_ORBIT]);;

let CPRING_ECPY = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> cpring (ecpY H x0) (ecpY_pt H x0) =
         CONS (SND(new_dart2(dart H)))
              (CONS (ecpY_pt H x0) (TL(cpring H x0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY; ecpY_pt] THEN
  ASM_SIMP_TAC[CPRING_ECPN; ECPU_PT_IN_DART; LONG_ECPU] THEN
  ASM_SIMP_TAC[CPRING_ECPU; GSYM PROPER_OSIZE; TL; CONS_11] THEN
  ECPU_TAC THEN ASM_REWRITE_TAC[]);;

let CPRING_ECPH = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> cpring (ecpH H x0) (ecpH_pt H x0) =
         CONS (node_map (ecpY H x0) (ecpY_pt H x0))
              (CONS (ecpH_pt H x0) (TL(TL(cpring H x0))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH; ecpH_pt] THEN
  ASM_SIMP_TAC[CPRING_ECPN; ECPY_PT_IN_DART; LONG_ECPY; CPRING_ECPY; TL]);;

(* ------------------------------------------------------------------------- *)
(* Ring sizes of programs (Gonthier size_ring_cpmap, cpmap_proper,           *)
(* cfmap_long), by induction on cubic and configuration programs.            *)
(* ------------------------------------------------------------------------- *)

let CPMAP0_NODE_OSIZE = prove
 (`orbit_size (node_map cpmap0) 1 = 2`,
  REWRITE_TAC[CPMAP0_COMPONENTS] THEN MATCH_MP_TAC ORBIT_SIZE_EQ_2 THEN
  EXISTS_TAC `{0,1}` THEN
  SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; PERMUTES_SWAP; swap] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CPMAP_PROPER = prove
 (`!cp. cubic_prog cp ==> proper_cpring (FST(cpmap cp)) (SND(cpmap cp))`,
  MATCH_MP_TAC CUBIC_PROG_INDUCT THEN
  SIMP_TAC[PROPER_OSIZE; CPMAP_PT_IN_DART; CPMAP_CONS_R; CPMAP_CONS_U_PAIR;
           CPMAP_CONS_Y; CPMAP_CONS_H; CPMAP_NIL_PAIR; CPMAP0_NODE_OSIZE;
           OSIZE_ECPR; SIZE_CPRING_ECPU; SIZE_CPRING_ECPY;
           SIZE_CPRING_ECPH] THEN
  ARITH_TAC);;

let CFMAP_LONG = prove
 (`!cp. config_prog cp ==> long_cpring (FST(cpmap cp)) (SND(cpmap cp))`,
  MATCH_MP_TAC CONFIG_PROG_INDUCT THEN
  SIMP_TAC[LONG_OSIZE; CPMAP_PT_IN_DART; CPMAP_CONS_R; CPMAP_CONS_Y;
           CPMAP_CONS_H; CPMAP_NIL_PAIR; CPMAP0_NODE_OSIZE; OSIZE_ECPR;
           SIZE_CPRING_ECPY; SIZE_CPRING_ECPH; CPMAP0_COMPONENTS; IN_INSERT;
           ARITH_RULE `2 < d ==> 1 < d`] THEN
  ARITH_TAC);;

let CPRSIZE_OSIZE = prove
 (`!cp. cprsize cp = orbit_size (node_map(FST(cpmap cp))) (SND(cpmap cp))`,
  SIMP_TAC[cprsize; SIZE_CPRING; CPMAP_PT_IN_DART]);;

let CPRSIZE_NIL = prove
 (`cprsize [] = 2`,
  REWRITE_TAC[CPRSIZE_OSIZE; CPMAP_NIL_PAIR; CPMAP0_NODE_OSIZE]);;

let CPRSIZE_CONS_Y = prove
 (`!t. cprsize (CONS CpY t) = cprsize t + 1`,
  SIMP_TAC[CPRSIZE_OSIZE; CPMAP_CONS_Y; SIZE_CPRING_ECPY; CPMAP_PT_IN_DART]);;

let CPRSIZE_CONS_U = prove
 (`!t. cprsize (CONS CpU t) = cprsize t + 2`,
  SIMP_TAC[CPRSIZE_OSIZE; CPMAP_CONS_U_PAIR; SIZE_CPRING_ECPU;
           CPMAP_PT_IN_DART]);;

let CPRSIZE_CONS_R = prove
 (`!n t. cprsize (CONS (CpR n) t) = cprsize t`,
  SIMP_TAC[CPRSIZE_OSIZE; CPMAP_CONS_R; OSIZE_ECPR; CPMAP_PT_IN_DART]);;

let CPRSIZE_CONS_H = prove
 (`!t. proper_cpring (FST(cpmap t)) (SND(cpmap t))
       ==> cprsize (CONS CpH t) = cprsize t`,
  SIMP_TAC[CPRSIZE_OSIZE; CPMAP_CONS_H; SIZE_CPRING_ECPH; CPMAP_PT_IN_DART;
           PROPER_OSIZE]);;

(* The derived steps ecpY = ecpN o ecpU and ecpH = ecpN o ecpY: the fresh    *)
(* darts of the inner step are a,b, of the middle step a',b', of the outer   *)
(* step a'',b''.                                                             *)
let ECPY_TAC =
  REWRITE_TAC[ecpH; ecpH_pt; ecpY; ecpY_pt] THEN ECPU_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] LONG_ECPU) THEN ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ecpU_pt;
      ASSUME `FST(new_dart2(dart(H:(num)hypermap))) = a`])] THEN
  ECPN_ON_TAC `ecpU H x0` `a:num` `a':num` `b':num`;;

let ECPH_TAC =
  ECPY_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] LONG_ECPY) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ecpY; ecpY_pt; ecpU_pt; ecpN_pt;
      ASSUME `FST(new_dart2(dart(H:(num)hypermap))) = a`;
      ASSUME `FST(new_dart2(dart(ecpU H x0))) = a'`])] THEN
  ECPN_ON_TAC `ecpN (ecpU H x0) a` `a':num` `a'':num` `b'':num`;;

let ORBIT_INDEX = prove
 (`!(f:A->A) s x z. FINITE s /\ f permutes s /\ x IN s /\ z IN orbit_map f x
     ==> ?j. j < orbit_size f x /\ z = ITER j f x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [ORBIT_MAP_ITER]) THEN
  EXISTS_TAC `n MOD orbit_size (f:A->A) x` THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOD_LT_EQ; LT_NZ];
    MATCH_MP_TAC ITER_MOD THEN ASM_MESON_TAC[ITER_ORBIT_SIZE]]);;

let NODE_ORBIT_OFF = prove
 (`!(H:(num)hypermap) x0 z k.
     x0 IN dart H /\ z IN dart H /\ ~(z IN orbit_map (node_map H) x0)
     ==> ITER k (node_map H) z IN dart H /\
         ~(ITER k (node_map H) z IN orbit_map (node_map H) x0)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ITER_PERMUTES_IN; NODE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[ORBIT_MAP_TRANS; ORBIT_MAP_SYM; ITER_IN_ORBIT; FINITE_DART;
                NODE_MAP_PERMUTES]);;

let ECPN_NODE_OFF = prove
 (`!(G:(num)hypermap) y a b d.
     d IN dart G /\ ~(a IN dart G) /\ ~(b IN dart G) /\ ~(d = y) /\
     ~(node_map G (node_map G d) = y)
     ==> ecpN_node G y a b d = node_map G d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpN_node] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[]);;

let ECPU_NODE_OFF_ORBIT = prove
 (`!(H:(num)hypermap) x0 a b z.
     ~(a IN dart H) /\ ~(b IN dart H) /\
     node_map H x0 IN orbit_map (node_map H) x0 /\
     z IN dart H /\ ~(z IN orbit_map (node_map H) x0)
     ==> ecpU_node H x0 a b z = node_map H z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpU_node] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[]);;

let ECPN_NODE_OFF_ORBIT = prove
 (`!(H:(num)hypermap) y a b z.
     ~(a IN dart H) /\ ~(b IN dart H) /\ FINITE(dart H) /\
     node_map H permutes dart H /\ y IN dart H /\ z IN dart H /\
     ~(z IN orbit_map (node_map H) y)
     ==> ecpN_node H y a b z = node_map H z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ECPN_NODE_OFF THEN
  ASM_MESON_TAC[IN_ORBIT_MAP_REFL; ORBIT_MAP_SYM; NODE2_IN_ORBIT]);;

let ECPN_NODE_3CYCLE_STEPS = prove
 (`!(H:(num)hypermap) y a b.
     y IN dart H /\ node_map H permutes dart H /\ FINITE(dart H) /\
     ~(a IN dart H) /\ ~(b IN dart H) /\ ~(a=b) /\ long_cpring H y
     ==> ecpN_node H y a b y = b /\
         ecpN_node H y a b b = face_map H (edge_map H y) /\
         ecpN_node H y a b (face_map H (edge_map H y)) = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `y:num`; `a:num`; `b:num`]
    ECPN_NODE_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `y:num`] LONG_OSIZE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(node_map H (y:num) = y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(num)hypermap`; `y:num`; `1`] NODE_ITER_NEQ) THEN
    ASM_REWRITE_TAC[ITER_1] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(face_map H (edge_map H (y:num)) = y)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `node_map(H:(num)hypermap)`) THEN
    ASM_REWRITE_TAC[edgeK] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; FACE_MAP_IN_DART; edgeK]);;

let CUBIC_ECPU = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ quasicubic H (orbit_map (node_map H) x0)
     ==> quasicubic (ecpU H x0) (orbit_map (node_map(ecpU H x0)) (ecpU_pt H))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ORBIT_ECPU_PT] THEN
  REWRITE_TAC[quasicubic; IN_INSERT; DE_MORGAN_THM] THEN
  ECPU_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `z:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[orbit_size] THEN
  SUBGOAL_THEN
   `orbit_map (ecpU_node (H:(num)hypermap) x0 a b) z =
    orbit_map (node_map H) z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_AGREE THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC ECPU_NODE_OFF_ORBIT THEN
    ASM_SIMP_TAC[NODE_ORBIT_OFF; ITER_PERMUTES_IN; NODE_MAP_PERMUTES] THEN
    MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [quasicubic]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:num`) THEN ASM_REWRITE_TAC[orbit_size]]);;

let CUBIC_ECPN = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ long_cpring H x0 /\
     quasicubic H (orbit_map (node_map H) x0)
     ==> quasicubic (ecpN H x0) (orbit_map (node_map(ecpN H x0)) (ecpN_pt H))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[quasicubic] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LONG_OSIZE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ECPN_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `a:num`; `b:num`]
    ECPN_NODE_ITER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `a:num`; `b:num`]
    ECPN_NODE_3CYCLE_STEPS) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `face_map H (edge_map H (x0:num)) IN dart (H:(num)hypermap) /\
    ~(face_map H (edge_map H x0) = x0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART; FACE_MAP_IN_DART] THEN
    DISCH_THEN(MP_TAC o AP_TERM `node_map(H:(num)hypermap)`) THEN
    REWRITE_TAC[edgeK] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `1`] NODE_ITER_NEQ) THEN
    ASM_REWRITE_TAC[ITER_1] THEN ANTS_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `g = ecpN_node (H:(num)hypermap) x0 a b` THEN
  ABBREV_TAC `w = face_map (H:(num)hypermap) (edge_map H x0)` THEN
  SUBGOAL_THEN `orbit_size g (x0:num) = 3` ASSUME_TAC THENL
   [MATCH_MP_TAC ORBIT_SIZE_EQ_3 THEN
    EXISTS_TAC `a INSERT b INSERT dart(H:(num)hypermap)` THEN
    EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_DART; IN_INSERT; ECPN_PERMUTES] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `orbit_size g (b:num) = 3 /\ orbit_size g (w:num) = 3`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:num->num`; `a INSERT b INSERT dart(H:(num)hypermap)`]
      ORBIT_SIZE_STEP_GEN) THEN
    EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_DART; IN_INSERT; ECPN_PERMUTES] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x0:num` th) THEN
                         MP_TAC(SPEC `b:num` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[IN_ORBIT_MAP_REFL]; ALL_TAC] THEN
  ASM_CASES_TAC `(z:num) IN orbit_map (node_map (H:(num)hypermap)) x0` THENL
   [MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                   `x0:num`; `z:num`] ORBIT_INDEX) THEN
    ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST_ALL_TAC)) THEN
    ASM_CASES_TAC `j = 0` THENL [ASM_REWRITE_TAC[ITER]; ALL_TAC] THEN
    ASM_CASES_TAC `j = orbit_size (node_map (H:(num)hypermap)) x0 - 1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[NODE_ITER_PRED];
      ALL_TAC] THEN
    UNDISCH_TAC
     `~(ITER j (node_map (H:(num)hypermap)) x0 IN orbit_map g a)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[ITER_IN_ORBIT];
    REWRITE_TAC[orbit_size] THEN
    SUBGOAL_THEN `orbit_map g z = orbit_map (node_map (H:(num)hypermap)) z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC ORBIT_MAP_AGREE THEN X_GEN_TAC `k:num` THEN
      EXPAND_TAC "g" THEN MATCH_MP_TAC ECPN_NODE_OFF_ORBIT THEN
      ASM_SIMP_TAC[NODE_ORBIT_OFF; FINITE_DART; NODE_MAP_PERMUTES;
                   ITER_PERMUTES_IN];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [quasicubic]) THEN
      DISCH_THEN(MP_TAC o SPEC `z:num`) THEN ASM_REWRITE_TAC[orbit_size]]]);;

let CUBIC_ECPR = prove
 (`!(H:(num)hypermap) n x0.
     x0 IN dart H /\ quasicubic H (orbit_map (node_map H) x0)
     ==> quasicubic (ecpR H n x0)
                    (orbit_map (node_map(ecpR H n x0)) (ecpR_pt H n x0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpR; ecpR_pt] THEN
  SUBGOAL_THEN
   `orbit_map (node_map H) (ITER (orbit_size (node_map H) x0 - n)
                                 (node_map H) x0) =
    orbit_map (node_map (H:(num)hypermap)) x0`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(num)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; ITER_IN_ORBIT]);;

let CUBIC_ECPY = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ quasicubic H (orbit_map (node_map H) x0)
     ==> quasicubic (ecpY H x0)
                    (orbit_map (node_map(ecpY H x0)) (ecpY_pt H x0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY; ecpY_pt] THEN
  MATCH_MP_TAC CUBIC_ECPN THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART; LONG_ECPU; CUBIC_ECPU]);;

let CUBIC_ECPH = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ proper_cpring H x0 /\
     quasicubic H (orbit_map (node_map H) x0)
     ==> quasicubic (ecpH H x0)
                    (orbit_map (node_map(ecpH H x0)) (ecpH_pt H x0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH; ecpH_pt] THEN
  MATCH_MP_TAC CUBIC_ECPN THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; CUBIC_ECPY]);;

let CUBIC_CPMAP0 = prove
 (`quasicubic cpmap0 (orbit_map (node_map cpmap0) 1)`,
  REWRITE_TAC[quasicubic; CPMAP0_COMPONENTS; IN_INSERT; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `swap(0,1) 1 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[swap; ARITH_EQ]; ALL_TAC] THEN
  ASM_MESON_TAC[IN_ORBIT_MAP_REFL; ORBIT_MAP_STEP]);;

let QUASICUBIC_CPRING = prove
 (`!(G:(num)hypermap) x0. x0 IN dart G
     ==> (quasicubic G (set_of_list(REVERSE(cpring G x0))) <=>
          quasicubic G (orbit_map (node_map G) x0))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[quasicubic; IN_SET_OF_LIST; MEM_REVERSE] THEN
  ASM_SIMP_TAC[MEM_CPRING; cnode; node]);;

let CPMAP_CUBIC = prove
 (`!cp. cubic_prog cp
        ==> quasicubic (FST(cpmap cp))
                       (set_of_list(REVERSE(cpring (FST(cpmap cp))
                                                   (SND(cpmap cp)))))`,
  MATCH_MP_TAC CUBIC_PROG_INDUCT THEN
  SIMP_TAC[QUASICUBIC_CPRING; CPMAP_PT_IN_DART; CPMAP_NIL_PAIR; CPMAP_CONS_R;
           CPMAP_CONS_U_PAIR; CPMAP_CONS_Y; CPMAP_CONS_H; CUBIC_CPMAP0;
           CUBIC_ECPR; CUBIC_ECPU; CUBIC_ECPY; CUBIC_ECPH; CPMAP_PROPER]);;

(* ------------------------------------------------------------------------- *)
(* Connectivity (Gonthier connected_ecpU/N, cpmap_connected): old glink      *)
(* steps lift to gcomp steps of the new map, the new darts hang on old ones. *)
(* ------------------------------------------------------------------------- *)

let GCOMP_LIFT = prove
 (`!(G:(num)hypermap) (H:(num)hypermap) x y.
     (!d. d IN dart H
          ==> gcomp G d (edge_map H d) /\ gcomp G d (node_map H d) /\
              gcomp G d (face_map H d)) /\
     x IN dart H /\ gcomp H x y
     ==> gcomp G x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `\y:num. y IN dart H /\ gcomp G x y`;
                 `x:num`] GCOMP_INDUCT) THEN
  ASM_REWRITE_TAC[GCOMP_REFL] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[glink] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART] THEN
    ASM_MESON_TAC[GCOMP_TRANS];
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_SIMP_TAC[]]);;

let CONNECTED_VIA_POINT = prove
 (`!(G:(num)hypermap) z.
     (!x. x IN dart G ==> gcomp G x z) ==> connected_hypermap G`,
  REWRITE_TAC[connected_hypermap] THEN MESON_TAC[GCOMP_TRANS; GCOMP_SYM]);;

(* one glink step of the new map, read off the pointwise clauses; a two-step *)
(* detour through an intermediate dart.                                      *)
let GLINK_TAC =
  MATCH_MP_TAC GCOMP_GLINK THEN
  ASM_SIMP_TAC[glink; EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART];;
let VIA_TAC t = MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC t THEN CONJ_TAC;;

let CONNECTED_ECPU = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ connected_hypermap H ==> connected_hypermap (ecpU H x0)`,
  REPEAT STRIP_TAC THEN ECPU_TAC THEN
  SUBGOAL_THEN `!d. d IN dart H ==> gcomp (ecpU H x0) d x0` ASSUME_TAC THENL
   [X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC GCOMP_LIFT THEN EXISTS_TAC `H:(num)hypermap` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[connected_hypermap]] THEN
    X_GEN_TAC `e:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [GLINK_TAC;
      ASM_CASES_TAC `e:num = node_map H x0` THENL
       [VIA_TAC `a:num` THENL [GLINK_TAC; VIA_TAC `b:num` THEN GLINK_TAC];
        GLINK_TAC];
      ASM_CASES_TAC `face_map (H:(num)hypermap) e = node_map H x0` THENL
       [VIA_TAC `b:num` THEN GLINK_TAC; GLINK_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `gcomp (ecpU H x0) b x0` ASSUME_TAC THENL
   [VIA_TAC `node_map H (node_map H (x0:num))` THENL
     [GLINK_TAC; ASM_SIMP_TAC[NODE_MAP_IN_DART]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_VIA_POINT THEN EXISTS_TAC `x0:num` THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN VIA_TAC `b:num` THENL [GLINK_TAC; ASM_REWRITE_TAC[]]);;

let CONNECTED_ECPN = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ long_cpring H x0 /\ connected_hypermap H
     ==> connected_hypermap (ecpN H x0)`,
  REPEAT STRIP_TAC THEN ECPN_TAC THEN
  SUBGOAL_THEN `gcomp (ecpN H x0) a x0 /\ gcomp (ecpN H x0) b a`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN GLINK_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!d. d IN dart H ==> gcomp (ecpN H x0) d x0` ASSUME_TAC THENL
   [X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC GCOMP_LIFT THEN EXISTS_TAC `H:(num)hypermap` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[connected_hypermap]] THEN
    X_GEN_TAC `e:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [GLINK_TAC;
      ASM_CASES_TAC `e:num = x0` THENL
       [POP_ASSUM SUBST_ALL_TAC THEN VIA_TAC `a:num` THENL
         [ASM_MESON_TAC[GCOMP_SYM]; GLINK_TAC];
        ALL_TAC] THEN
      ASM_CASES_TAC `node_map (H:(num)hypermap) (node_map H e) = x0` THENL
       [SUBGOAL_THEN
         `node_map (H:(num)hypermap) e = face_map H (edge_map H x0)`
        SUBST1_TAC
        THENL
         [MATCH_MP_TAC(ISPEC `H:(num)hypermap` NODEI) THEN
          ASM_REWRITE_TAC[edgeK];
          VIA_TAC `a:num` THENL
           [GLINK_TAC; VIA_TAC `b:num` THENL [ASM_MESON_TAC[GCOMP_SYM];
                                             GLINK_TAC]]];
        GLINK_TAC];
      ASM_CASES_TAC `e:num = edge_map H (face_map H (edge_map H x0))` THENL
       [POP_ASSUM SUBST_ALL_TAC THEN VIA_TAC `b:num` THEN GLINK_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `e:num = edge_map H (node_map H x0)` THENL
       [POP_ASSUM SUBST_ALL_TAC THEN VIA_TAC `a:num` THENL
         [GLINK_TAC; ASM_REWRITE_TAC[nodeK]];
        GLINK_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_VIA_POINT THEN EXISTS_TAC `x0:num` THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[GCOMP_TRANS]);;

let CONNECTED_ECPY = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ connected_hypermap H ==> connected_hypermap (ecpY H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY] THEN MATCH_MP_TAC CONNECTED_ECPN THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART; LONG_ECPU; CONNECTED_ECPU]);;

let CONNECTED_ECPH = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ proper_cpring H x0 /\ connected_hypermap H
     ==> connected_hypermap (ecpH H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN MATCH_MP_TAC CONNECTED_ECPN THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; CONNECTED_ECPY]);;

let CPMAP0_CONNECTED = prove
 (`connected_hypermap cpmap0`,
  SUBGOAL_THEN `gcomp cpmap0 0 1` ASSUME_TAC THENL
   [MATCH_MP_TAC GCOMP_GLINK THEN
    REWRITE_TAC[glink; CPMAP0_COMPONENTS; swap; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[connected_hypermap; CPMAP0_COMPONENTS; IN_INSERT;
              NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[GCOMP_REFL; GCOMP_SYM]);;

let CPMAP_CONNECTED = prove
 (`!cp. cubic_prog cp ==> connected_hypermap (FST(cpmap cp))`,
  MATCH_MP_TAC CUBIC_PROG_INDUCT THEN
  SIMP_TAC[CPMAP_NIL_PAIR; CPMAP_CONS_R; CPMAP_CONS_U_PAIR; CPMAP_CONS_Y;
           CPMAP_CONS_H; ecpR; CPMAP0_CONNECTED; CONNECTED_ECPU;
           CONNECTED_ECPY; CONNECTED_ECPH; CPMAP_PT_IN_DART; CPMAP_PROPER]);;

(* ------------------------------------------------------------------------- *)
(* Face connectivity across a U or N step (Gonthier cface_icpU/cface_icpN,   *)
(* cface_ecpU): orbit closure arguments for both inclusions.                 *)
(* ------------------------------------------------------------------------- *)

let ORBIT_SUBSET_TWO_STEP = prove
 (`!(f:A->A) g x.
     (!y. y IN orbit_map g x ==> f y = y \/ f y = g y \/ f y = g(g y))
     ==> orbit_map f x SUBSET orbit_map g x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORBIT_IN_CLOSED THEN
  REWRITE_TAC[IN_ORBIT_MAP_REFL] THEN ASM_MESON_TAC[ORBIT_MAP_STEP]);;

let CFACE_FACE_SUCC = prove
 (`!(G:(num)hypermap) x. cface G x (face_map G x)`,
  REWRITE_TAC[cface; face] THEN MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]);;

let CFACE_ECPU_LIFT = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ FINITE(dart H) /\ edge_map H permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\
     x IN dart H /\ cface H x y
     ==> cface (ecpU H x0) x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ECPU_TAC THEN
  UNDISCH_TAC `cface (H:(num)hypermap) x y` THEN REWRITE_TAC[cface; face] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(s:num->bool) SUBSET t ==> y IN s ==> y IN t`) THEN
  MATCH_MP_TAC ORBIT_SUBSET_TWO_STEP THEN X_GEN_TAC `z:num` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `z IN a INSERT b INSERT dart(H:(num)hypermap)` MP_TAC THENL
   [MP_TAC(ISPECL [`ecpU_face H x0 a b`;
                   `a INSERT b INSERT dart(H:(num)hypermap)`; `x:num`; `z:num`]
      ORBIT_MAP_IN) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_DART; IN_INSERT; ECPU_PERMUTES];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MAPS_OUTSIDE_DART] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let CFACE_ECPU_PROJ = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ x IN dart H /\ y IN dart H /\ cface (ecpU H x0) x y
     ==> cface H x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ECPU_TAC THEN
  UNDISCH_TAC `cface (ecpU H x0) x y` THEN REWRITE_TAC[cface; face] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`ecpU_face H x0 a b`;
    `{d | d IN orbit_map (face_map (H:(num)hypermap)) x \/
          d = b /\ node_map H x0 IN orbit_map (face_map H) x}`;
    `x:num`] ORBIT_IN_CLOSED) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_ORBIT_MAP_REFL] THEN ANTS_TAC THENL
   [X_GEN_TAC `d:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d IN dart(H:(num)hypermap)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ORBIT_MAP_IN; FINITE_DART; FACE_MAP_PERMUTES];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[ORBIT_MAP_STEP];
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_MESON_TAC[]]);;

let CFACE_ECPN_LIFT = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ long_cpring H x0 /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H /\ x IN dart H /\ cface H x y
     ==> cface (ecpN H x0) x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ECPN_TAC THEN
  UNDISCH_TAC `cface (H:(num)hypermap) x y` THEN REWRITE_TAC[cface; face] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(s:num->bool) SUBSET t ==> y IN s ==> y IN t`) THEN
  MATCH_MP_TAC ORBIT_SUBSET_TWO_STEP THEN X_GEN_TAC `z:num` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `z IN a INSERT b INSERT dart(H:(num)hypermap)` MP_TAC THENL
   [MP_TAC(ISPECL [`ecpN_face H x0 a b`;
                   `a INSERT b INSERT dart(H:(num)hypermap)`; `x:num`; `z:num`]
      ORBIT_MAP_IN) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_DART; IN_INSERT; ECPN_PERMUTES];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MAPS_OUTSIDE_DART] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[nodeK]));;

let CFACE_ECPN_PROJ = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ long_cpring H x0 /\ x IN dart H /\ y IN dart H /\
     cface (ecpN H x0) x y
     ==> cface H x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ECPN_TAC THEN
  UNDISCH_TAC `cface (ecpN H x0) x y` THEN REWRITE_TAC[cface; face] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`ecpN_face H x0 a b`;
    `{d | d IN orbit_map (face_map (H:(num)hypermap)) x \/
          d = a /\ x0 IN orbit_map (face_map H) x \/
          d = b /\ face_map H (edge_map H (face_map H (edge_map H x0))) IN
                   orbit_map (face_map H) x}`;
    `x:num`] ORBIT_IN_CLOSED) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_ORBIT_MAP_REFL] THEN ANTS_TAC THENL
   [X_GEN_TAC `d:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d IN dart(H:(num)hypermap)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ORBIT_MAP_IN; FINITE_DART; FACE_MAP_PERMUTES];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_MESON_TAC[ORBIT_MAP_STEP; nodeK];
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_MESON_TAC[]]);;

let ECPN_A_IN_FACE_ORBIT = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ long_cpring H x0
     ==> FST(new_dart2(dart H)) IN orbit_map (face_map(ecpN H x0)) x0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `x0:num`;
                 `edge_map H (node_map H (x0:num))`] CFACE_ECPN_LIFT) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  ANTS_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cface; face] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ORBIT_MAP_STEP) THEN
  ECPN_TAC THEN ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o MATCH_MP (ISPEC `H:(num)hypermap` EDGEI)) THEN
  ASM_MESON_TAC[long_cpring]);;

let ECPN_B_IN_FACE_ORBIT = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ long_cpring H x0 /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H
     ==> SND(new_dart2(dart H)) IN
         orbit_map (face_map(ecpN H x0))
                   (face_map H (edge_map H (face_map H (edge_map H x0))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `edge_map H (face_map H (edge_map H (x0:num))) IN dart (H:(num)hypermap) /\
    face_map H (edge_map H (face_map H (edge_map H x0))) IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EDGE_MAP_IN_DART; FACE_MAP_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`;
                 `face_map H (edge_map H (face_map H (edge_map H (x0:num))))`;
                 `edge_map H (face_map H (edge_map H (x0:num)))`]
    CFACE_ECPN_LIFT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cface; face] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ORBIT_MAP_STEP) THEN
  ECPN_TAC THEN ASM_SIMP_TAC[]);;

(* the apex of a U step is an isolated face; the other new dart b sits in    *)
(* the face of node x0.                                                      *)
let CFACE_ECPU_APEX = prove
 (`!(H:(num)hypermap) x0 z.
     x0 IN dart H /\ cface (ecpU H x0) (ecpU_pt H) z ==> z = ecpU_pt H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `cface (ecpU H x0) (ecpU_pt H) z` THEN
  REWRITE_TAC[cface; face] THEN ECPU_TAC THEN
  ASM_SIMP_TAC[ORBIT_FIXED; IN_SING]);;

let ECPU_FACE_SND = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> face_map (ecpU H x0) (SND(new_dart2(dart H))) = node_map H x0`,
  REPEAT STRIP_TAC THEN ECPU_TAC THEN ASM_REWRITE_TAC[]);;

let ECPU_EDGE_PT = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> edge_map (ecpU H x0) (ecpU_pt H) = SND(new_dart2(dart H))`,
  REPEAT STRIP_TAC THEN ECPU_TAC THEN ASM_REWRITE_TAC[]);;

let ECPU_PT_NOT_IN_DART = prove
 (`!(H:(num)hypermap). FINITE(dart H) ==> ~(ecpU_pt H IN dart H)`,
  SIMP_TAC[ecpU_pt; NEW_DART2_FRESH]);;

(* ------------------------------------------------------------------------- *)
(* The derived steps ecpY = ecpN o ecpU and ecpH = ecpN o ecpY: the fresh    *)
(* darts of the inner step are a,b, of the middle step a',b', of the outer   *)
(* step a'',b''.  Face cycles of the new pointers and bridgelessness         *)
(* (Gonthier cface_ecpY, cface_ecpH, bridgeless_ecpU/Y/H, cpmap_bridgeless). *)
(* ------------------------------------------------------------------------- *)

let DART_SUBSET_ECPU = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> dart H SUBSET dart(ecpU H x0)`,
  REPEAT STRIP_TAC THEN ECPU_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let SND_NEW_IN_ECPU = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> SND(new_dart2(dart H)) IN dart(ecpU H x0)`,
  REPEAT STRIP_TAC THEN ECPU_TAC THEN ASM_REWRITE_TAC[IN_INSERT]);;

let ECPY_PT_NOT_IN_DART = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ FINITE(dart H) ==> ~(ecpY_pt H x0 IN dart H)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `dart(ecpU H x0)` NEW_DART2_FRESH) THEN
  ASM_SIMP_TAC[FINITE_DART; GSYM ecpN_pt; GSYM ecpY_pt] THEN
  ASM_MESON_TAC[DART_SUBSET_ECPU; SUBSET]);;

let ORBIT_2CYCLE = prove
 (`!(f:A->A) x. f(f x) = x ==> orbit_map f x = {x, f x}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC ORBIT_IN_CLOSED THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ORBIT_MAP_REFL] THEN
    SIMP_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]]);;

let ORBIT_3CYCLE_GEN = prove
 (`!(f:A->A) x. f(f(f x)) = x ==> orbit_map f x = {x, f x, f(f x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC ORBIT_IN_CLOSED THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ORBIT_MAP_REFL] THEN
    SIMP_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]]);;

let ECPY_APEX_TWO_CYCLE = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> face_map (ecpY H x0) (ecpY_pt H x0) = ecpU_pt H /\
         face_map (ecpY H x0) (ecpU_pt H) = ecpY_pt H x0`,
  REPEAT STRIP_TAC THEN ECPY_TAC THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; EDGE_MAP_IN_DART]);;

let FACE_ECPY_APEX = prove
 (`!(H:(num)hypermap) x0 z.
     x0 IN dart H /\ FINITE(dart H) /\ edge_map H permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\
     cface (ecpY H x0) (ecpY_pt H x0) z
     ==> z = ecpY_pt H x0 \/ z = ecpU_pt H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cface]) THEN
  REWRITE_TAC[face] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPY_APEX_TWO_CYCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`face_map(ecpY H x0)`; `ecpY_pt H x0`] ORBIT_2CYCLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

let CFACE_ECPY_APEX_OLD = prove
 (`!(H:(num)hypermap) x0 z.
     x0 IN dart H /\ FINITE(dart H) /\ edge_map H permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\ z IN dart H
     ==> ~cface (ecpY H x0) (ecpY_pt H x0) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `z:num`] FACE_ECPY_APEX) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[ECPY_PT_NOT_IN_DART; ECPU_PT_NOT_IN_DART]);;

let EDGE_ECPY_OLD = prove
 (`!(H:(num)hypermap) x0 z.
     x0 IN dart H /\ z IN dart H ==> edge_map (ecpY H x0) z = edge_map H z`,
  REPEAT STRIP_TAC THEN ECPY_TAC THEN ASM_SIMP_TAC[IN_INSERT]);;

let ECPY_FACE_EDGE_PT = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> face_map (ecpY H x0) (edge_map (ecpY H x0) (ecpY_pt H x0)) = x0`,
  REPEAT STRIP_TAC THEN ECPY_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[proper_cpring]) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; EDGE_MAP_IN_DART; nodeK]);;

let BRIDGELESS_ECPU = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ bridgeless H ==> bridgeless (ecpU H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bridgeless] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_ECPU_APEX) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_ECPU_PROJ) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bridgeless]) THEN ECPU_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `u:num` THEN REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THENL
   [ASM_MESON_TAC[]; CFACE_TAC[]; ASM_MESON_TAC[EDGE_MAP_IN_DART]]);;

(* an N step is bridgeless when the new edge {a,b} is not a bridge.          *)
let BRIDGELESS_ECPN_GEN = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ long_cpring H x0 /\ bridgeless H /\
     ~cface (ecpN H x0) (ecpN_pt H) (SND(new_dart2(dart H)))
     ==> bridgeless (ecpN H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bridgeless] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_ECPN_PROJ) THEN
  UNDISCH_TAC `~cface (ecpN H x0) (ecpN_pt H) (SND(new_dart2(dart H)))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bridgeless]) THEN ECPN_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `u:num` THEN REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THENL
   [CFACE_TAC[]; ASM_MESON_TAC[EDGE_MAP_IN_DART]]);;

let BRIDGELESS_ECPY = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ bridgeless H ==> bridgeless (ecpY H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY] THEN
  MATCH_MP_TAC BRIDGELESS_ECPN_GEN THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART; LONG_ECPU; BRIDGELESS_ECPU] THEN
  REWRITE_TAC[GSYM ecpY; GSYM ecpY_pt] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`;
                 `SND(new_dart2(dart(ecpU H x0)))`] FACE_ECPY_APEX) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  ECPY_TAC THEN UNDISCH_TAC `~(b' IN dart (ecpU H x0))` THEN
  UNDISCH_TAC `a IN dart (ecpU H x0)` THEN UNDISCH_TAC `~(a':num = b')` THEN
  MESON_TAC[]);;

(* the face of the ecpH apex is the 3-cycle apex, Y-apex, U-apex.            *)
let ECPH_FACE_3CYCLE_STEPS = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> face_map (ecpH H x0) (ecpH_pt H x0) = ecpY_pt H x0 /\
         face_map (ecpH H x0) (ecpY_pt H x0) = ecpU_pt H /\
         face_map (ecpH H x0) (ecpU_pt H) = ecpH_pt H x0`,
  REPEAT STRIP_TAC THEN ECPH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[proper_cpring]) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; EDGE_MAP_IN_DART; nodeK]);;

let ECPH_APEX_FACE_CASES = prove
 (`!(H:(num)hypermap) x0 z.
     x0 IN dart H /\ proper_cpring H x0 /\ cface (ecpH H x0) (ecpH_pt H x0) z
     ==> z = ecpH_pt H x0 \/ z = ecpY_pt H x0 \/ z = ecpU_pt H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cface]) THEN
  REWRITE_TAC[face] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPH_FACE_3CYCLE_STEPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`face_map(ecpH H x0)`; `ecpH_pt H x0`] ORBIT_3CYCLE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

let ECPH_PT_FRESH = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ FINITE(dart H) ==> ~(ecpH_pt H x0 IN dart H)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `dart(ecpY H x0)` NEW_DART2_FRESH) THEN
  ASM_SIMP_TAC[FINITE_DART; GSYM ecpN_pt; GSYM ecpH_pt; ECPY_DART;
               IN_INSERT] THEN
  ASM_MESON_TAC[DART_SUBSET_ECPU; SUBSET]);;

let CFACE_ECPH_APEX_OLD = prove
 (`!(H:(num)hypermap) x0 z.
     x0 IN dart H /\ proper_cpring H x0 /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H /\ z IN dart H
     ==> ~cface (ecpH H x0) (ecpH_pt H x0) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `z:num`]
    ECPH_APEX_FACE_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[ECPY_PT_NOT_IN_DART; ECPU_PT_NOT_IN_DART;
                ECPH_PT_FRESH]);;

let BRIDGELESS_ECPH = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ proper_cpring H x0 /\ bridgeless H
     ==> bridgeless (ecpH H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MATCH_MP_TAC BRIDGELESS_ECPN_GEN THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; BRIDGELESS_ECPY] THEN
  REWRITE_TAC[GSYM ecpH; GSYM ecpH_pt] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`;
                 `SND(new_dart2(dart(ecpY H x0)))`] ECPH_APEX_FACE_CASES) THEN
  ASM_REWRITE_TAC[] THEN ECPH_TAC THEN
  UNDISCH_TAC `~(b'' IN dart (ecpN (ecpU H x0) a))` THEN
  UNDISCH_TAC `a' IN dart (ecpN (ecpU H x0) a)` THEN
  UNDISCH_TAC `a IN dart (ecpN (ecpU H x0) a)` THEN
  UNDISCH_TAC `~(a'':num = b'')` THEN MESON_TAC[]);;

let CPMAP0_BRIDGELESS = prove
 (`bridgeless cpmap0`,
  REWRITE_TAC[bridgeless; cface; face; CPMAP0_COMPONENTS] THEN
  SIMP_TAC[ORBIT_FIXED; I_THM; FORALL_IN_INSERT; NOT_IN_EMPTY; IN_SING;
           swap] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CPMAP_BRIDGELESS = prove
 (`!cp. cubic_prog cp ==> bridgeless (FST(cpmap cp))`,
  MATCH_MP_TAC CUBIC_PROG_INDUCT THEN
  SIMP_TAC[CPMAP_NIL_PAIR; CPMAP_CONS_R; CPMAP_CONS_U_PAIR; CPMAP_CONS_Y;
           CPMAP_CONS_H; ecpR; CPMAP0_BRIDGELESS; BRIDGELESS_ECPU;
           BRIDGELESS_ECPY; BRIDGELESS_ECPH; CPMAP_PT_IN_DART; CPMAP_PROPER]);;

(* ------------------------------------------------------------------------- *)
(* Counting faces across a step, and the Euler formula of plain quasicubic   *)
(* connected maps (Gonthier quasicubic_Euler, planar_ecpU/N, cpmap_planar).  *)
(* ------------------------------------------------------------------------- *)

let CARD_ORBITS_SPLIT_CL = prove
 (`!f (s:A->bool) t.
     FINITE s /\ t SUBSET s /\ (!y. y IN t ==> f y IN t) /\
     (!y. y IN (s DIFF t) ==> f y IN (s DIFF t))
     ==> CARD(set_of_orbits s f) =
         CARD(set_of_orbits t f) + CARD(set_of_orbits (s DIFF t) f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_OF_ORBITS_IMAGE] THEN
  SUBGOAL_THEN
   `IMAGE (orbit_map (f:A->A)) s =
    IMAGE (orbit_map f) t UNION IMAGE (orbit_map f) (s DIFF t)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_UNION THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DIFF] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->A`; `t:A->bool`] ORBIT_IN_CLOSED) THEN
  MP_TAC(ISPECL [`f:A->A`; `s DIFF t:A->bool`] ORBIT_IN_CLOSED) THEN
  MP_TAC(ISPEC `f:A->A` IN_ORBIT_MAP_REFL) THEN ASM SET_TAC[]);;

let SET_OF_ORBITS_SING = prove
 (`!(f:A->A) a. set_of_orbits {a} f = {orbit_map f a}`,
  REWRITE_TAC[set_of_orbits; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[]);;

let UNIFORM_ORBIT_CARD_CLOSED = prove
 (`!f (s:A->bool) t k.
     FINITE s /\ f permutes s /\ t SUBSET s /\ (!y. y IN t ==> f y IN t) /\
     (!x. x IN t ==> orbit_size f x = k)
     ==> k * CARD(set_of_orbits t f) = CARD t`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = \x:A. if x IN t then f x else x` THEN
  SUBGOAL_THEN `(g:A->A) permutes t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:A. x IN t`; `f:A->A`; `s:A->bool`]
      PERMUTES_RESTRICT_SET) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:A | x IN s /\ x IN t} = t` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `t:A->bool`] PERM_COMPL_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[PERMUTES_INJ]; ALL_TAC] THEN
    DISCH_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN t ==> orbit_map g x = orbit_map f x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ORBIT_MAP_AGREE THEN
    X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `ITER n (f:A->A) x IN t` MP_TAC THENL
     [MP_TAC(ISPECL [`f:A->A`; `t:A->bool`; `x:A`] ORBIT_IN_CLOSED) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[ITER_IN_ORBIT];
      ALL_TAC] THEN
    EXPAND_TAC "g" THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `set_of_orbits t (f:A->A) = set_of_orbits t g` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SET_OF_ORBITS_AGREE THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC UNIFORM_ORBIT_CARD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `orbit_size (g:A->A) x = orbit_size f x` SUBST1_TAC THENL
   [REWRITE_TAC[orbit_size] THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]]);;

let NUMBER_FACES_ECPU = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> number_of_faces (ecpU H x0) = number_of_faces H + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_faces; face_set] THEN
  ECPU_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ecpU_face H x0 a b`;
                 `a INSERT b INSERT dart(H:(num)hypermap)`; `{a:num}`]
    CARD_ORBITS_SPLIT) THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_DART; ECPU_PERMUTES; SING_SUBSET;
               IN_INSERT; IN_SING; SET_OF_ORBITS_SING; CARD_SING] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(a INSERT b INSERT dart H) DIFF {a} = b INSERT dart(H:(num)hypermap)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(set_of_orbits (b INSERT dart H) (ecpU_face H x0 a b)) =
    CARD(set_of_orbits (dart (H:(num)hypermap)) (face_map H))`
   (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
  MP_TAC(ISPECL [`ecpU_face H x0 a b`; `b:num`; `b:num`] ORBIT_MAP_STEP) THEN
  ASM_REWRITE_TAC[IN_ORBIT_MAP_REFL] THEN DISCH_TAC THEN
  MATCH_MP_TAC CARD_ORBITS_REL THEN EXISTS_TAC `\x:num. x` THEN
  REWRITE_TAC[FINITE_DART; IN_INSERT] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    X_GEN_TAC `z:num` THEN STRIP_TAC THENL
     [EXISTS_TAC `node_map H (x0:num)` THEN ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
      EXISTS_TAC `a INSERT b INSERT dart(H:(num)hypermap)` THEN
      ASM_SIMP_TAC[FINITE_INSERT; FINITE_DART; IN_INSERT; ECPU_PERMUTES];
      EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`; `y:num`] ORBIT_EQ_CFACE) THEN
    MP_TAC(ISPECL [`ecpU H x0`; `x:num`; `y:num`] ORBIT_EQ_CFACE) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `x:num`; `y:num`]
      CFACE_ECPU_PROJ) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `x:num`; `y:num`]
      CFACE_ECPU_LIFT) THEN
    ASM_REWRITE_TAC[IN_INSERT; FINITE_DART; EDGE_MAP_PERMUTES;
                    NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
    MESON_TAC[]]);;

let NUMBER_FACES_ECPN = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ long_cpring H x0
     ==> number_of_faces (ecpN H x0) = number_of_faces H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_faces; face_set] THEN
  SUBGOAL_THEN
   `face_map H (edge_map H (face_map H (edge_map H (x0:num)))) IN
    dart (H:(num)hypermap)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[EDGE_MAP_IN_DART; FACE_MAP_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPN_A_IN_FACE_ORBIT) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPN_B_IN_FACE_ORBIT) THEN
  ECPN_TAC THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC CARD_ORBITS_REL THEN EXISTS_TAC `\x:num. x` THEN
  REWRITE_TAC[FINITE_DART; IN_INSERT] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    X_GEN_TAC `z:num` THEN STRIP_TAC THENL
     [EXISTS_TAC `x0:num`;
      EXISTS_TAC `face_map H (edge_map H (face_map H (edge_map H (x0:num))))`;
      EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
    EXISTS_TAC `a INSERT b INSERT dart(H:(num)hypermap)` THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_DART; IN_INSERT; ECPN_PERMUTES];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x:num`; `y:num`] ORBIT_EQ_CFACE) THEN
    MP_TAC(ISPECL [`ecpN H x0`; `x:num`; `y:num`] ORBIT_EQ_CFACE) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `x:num`; `y:num`]
      CFACE_ECPN_PROJ) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `x:num`; `y:num`]
      CFACE_ECPN_LIFT) THEN
    ASM_REWRITE_TAC[IN_INSERT; FINITE_DART; EDGE_MAP_PERMUTES;
                    NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
    MESON_TAC[]]);;

let CARD_DART_ECPU = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> CARD(dart (ecpU H x0)) = CARD(dart H) + 2`,
  REPEAT STRIP_TAC THEN ECPU_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_DART; IN_INSERT] THEN
  ARITH_TAC);;

let CARD_DART_ECPN = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> CARD(dart (ecpN H x0)) = CARD(dart H) + 2`,
  REPEAT STRIP_TAC THEN ECPN_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_DART; IN_INSERT] THEN
  ARITH_TAC);;

let CARD_DART_CPMAP0 = prove
 (`CARD(dart cpmap0) = 2`,
  SIMP_TAC[CPMAP0_COMPONENTS; CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let NUMBER_FACES_CPMAP0 = prove
 (`number_of_faces cpmap0 = 2`,
  REWRITE_TAC[number_of_faces; face_set; CPMAP0_COMPONENTS;
              SET_OF_ORBITS_IMAGE; IMAGE_CLAUSES] THEN
  SIMP_TAC[ORBIT_FIXED; I_THM; CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY; SET_RULE `{a:A} = {b} <=> a = b`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* a plain quasicubic map with ring r has 3 (nodes - 1) = darts - size r.    *)
let QUASICUBIC_NODES = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ quasicubic H (orbit_map (node_map H) x0)
     ==> 3 * number_of_nodes H + orbit_size (node_map H) x0 =
         CARD(dart H) + 3`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_nodes; node_set] THEN
  SUBGOAL_THEN `orbit_map (node_map H) (x0:num) SUBSET dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SUBSET; NODE_MAP_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN dart H DIFF orbit_map (node_map H) x0
        ==> node_map H y IN dart (H:(num)hypermap) DIFF
                             orbit_map (node_map H) x0`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `y:num`; `1`]
      NODE_ORBIT_OFF) THEN
    ASM_REWRITE_TAC[ITER_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                 `orbit_map (node_map H) (x0:num)`] CARD_ORBITS_SPLIT_CL) THEN
  ASM_SIMP_TAC[FINITE_DART; ORBIT_MAP_STEP] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `CARD(set_of_orbits (orbit_map (node_map H) x0)
                       (node_map (H:(num)hypermap))) = 1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_SET_OF_ORBITS_1 THEN CONJ_TAC THENL
     [MESON_TAC[IN_ORBIT_MAP_REFL; MEMBER_NOT_EMPTY];
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
      EXISTS_TAC `dart(H:(num)hypermap)` THEN
      ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                 `dart H DIFF orbit_map (node_map H) (x0:num)`; `3`]
    UNIFORM_ORBIT_CARD_CLOSED) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; SUBSET_DIFF] THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [quasicubic]) THEN
    SIMP_TAC[IN_DIFF];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DIFF; FINITE_DART] THEN
  MP_TAC(ISPECL [`orbit_map (node_map H) (x0:num)`; `dart(H:(num)hypermap)`]
    CARD_SUBSET) THEN
  ASM_REWRITE_TAC[FINITE_DART; GSYM orbit_size] THEN ARITH_TAC);;

let QUASICUBIC_PLANAR_FACES = prove
 (`!(H:(num)hypermap) x0.
     plain_hypermap H /\ connected_hypermap H /\ x0 IN dart H /\
     quasicubic H (orbit_map (node_map H) x0)
     ==> (planar_hypermap H <=>
          6 * number_of_faces H =
          CARD(dart H) + 2 * orbit_size (node_map H) x0 + 6)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `H:(num)hypermap` EVEN_GENUS) THEN
  REWRITE_TAC[even_genus; planar_hypermap; euler_lhs; euler_rhs] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] QUASICUBIC_NODES) THEN
  MP_TAC(ISPEC `H:(num)hypermap` PLAIN_DART_CARD) THEN
  MP_TAC(ISPEC `H:(num)hypermap` CONNECTED_NCOMP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ARITH_TAC]);;

let PLANAR_ECPU = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ plain_hypermap H /\ connected_hypermap H /\
     quasicubic H (orbit_map (node_map H) x0) /\ planar_hypermap H
     ==> planar_hypermap (ecpU H x0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpU H x0`; `ecpU_pt H`] QUASICUBIC_PLANAR_FACES) THEN
  ASM_SIMP_TAC[PLAIN_ECPU; CONNECTED_ECPU; ECPU_PT_IN_DART; CUBIC_ECPU;
               NUMBER_FACES_ECPU; CARD_DART_ECPU; SIZE_CPRING_ECPU] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] QUASICUBIC_PLANAR_FACES) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let PLANAR_ECPN = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ long_cpring H x0 /\ plain_hypermap H /\
     connected_hypermap H /\ quasicubic H (orbit_map (node_map H) x0) /\
     planar_hypermap H
     ==> planar_hypermap (ecpN H x0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpN H x0`; `ecpN_pt H`] QUASICUBIC_PLANAR_FACES) THEN
  ASM_SIMP_TAC[PLAIN_ECPN; CONNECTED_ECPN; ECPN_PT_IN_DART; CUBIC_ECPN;
               NUMBER_FACES_ECPN; CARD_DART_ECPN; SIZE_CPRING_ECPN] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] QUASICUBIC_PLANAR_FACES) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] LONG_OSIZE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let PLANAR_ECPY = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ plain_hypermap H /\ connected_hypermap H /\
     quasicubic H (orbit_map (node_map H) x0) /\ planar_hypermap H
     ==> planar_hypermap (ecpY H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY] THEN MATCH_MP_TAC PLANAR_ECPN THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART; LONG_ECPU; PLAIN_ECPU; CONNECTED_ECPU;
               CUBIC_ECPU; PLANAR_ECPU]);;

let PLANAR_ECPH = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ proper_cpring H x0 /\ plain_hypermap H /\
     connected_hypermap H /\ quasicubic H (orbit_map (node_map H) x0) /\
     planar_hypermap H
     ==> planar_hypermap (ecpH H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN MATCH_MP_TAC PLANAR_ECPN THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; PLAIN_ECPY; CONNECTED_ECPY;
               CUBIC_ECPY; PLANAR_ECPY]);;

let PLANAR_CPMAP0 = prove
 (`planar_hypermap cpmap0`,
  MP_TAC(ISPECL [`cpmap0`; `1`] QUASICUBIC_PLANAR_FACES) THEN
  REWRITE_TAC[PLAIN_CPMAP0; CPMAP0_CONNECTED; CUBIC_CPMAP0; CPMAP0_COMPONENTS;
              IN_INSERT; NUMBER_FACES_CPMAP0; CARD_DART_CPMAP0] THEN
  REWRITE_TAC[GSYM CPMAP0_COMPONENTS; CPMAP0_NODE_OSIZE] THEN
  DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;

let CPMAP_PLANAR = prove
 (`!cp. cubic_prog cp ==> planar_hypermap (FST(cpmap cp))`,
  MATCH_MP_TAC CUBIC_PROG_INDUCT THEN
  REWRITE_TAC[CPMAP_NIL_PAIR; CPMAP_CONS_R; CPMAP_CONS_U_PAIR; CPMAP_CONS_Y;
              CPMAP_CONS_H; ecpR; PLANAR_CPMAP0] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (MATCH_MP_TAC PLANAR_ECPU ORELSE MATCH_MP_TAC PLANAR_ECPY ORELSE
   MATCH_MP_TAC PLANAR_ECPH) THEN
  ASM_SIMP_TAC[CPMAP_PT_IN_DART; CPMAP_PLAIN; CPMAP_CONNECTED; CPMAP_PROPER;
               GSYM QUASICUBIC_CPRING; CPMAP_CUBIC]);;

(* ------------------------------------------------------------------------- *)
(* cpker (Gonthier cfmap.v:1217): the kernel transversal -- one              *)
(* representative dart per interior face introduced by each CpH step         *)
(* (CpR/CpY add none). In our identity-injection setting Gonthier's map      *)
(* icpY/icpH are the identity, so cpker is just the list of CpH-apex darts   *)
(* SND(cpmap cp') taken in order.                                            *)
(* ------------------------------------------------------------------------- *)

let cpker = define
  `(cpker [] = []) /\
   (cpker (CONS (CpR n) cp) = cpker cp) /\
   (cpker (CONS CpRr cp) = []) /\
   (cpker (CONS CpY cp) = cpker cp) /\
   (cpker (CONS CpH cp) = CONS (SND(cpmap cp)) (cpker cp)) /\
   (cpker (CONS CpU cp) = []) /\
   (cpker (CONS CpK cp) = []) /\
   (cpker (CONS CpA cp) = [])`;;

let cpksize = define
  `cpksize (cp:(cpstep)list) = LENGTH(FILTER (\s. s = CpH) cp)`;;

(* size_cpker (Gonthier cfmap.v:1395): the kernel has one dart per CpH step. *)
let SIZE_CPKER_ALL = prove
 (`!cp. ALL config_step cp ==> LENGTH(cpker cp) = cpksize cp`,
  REWRITE_TAC[cpksize] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[cpker; FILTER; LENGTH; ALL] THEN
  STRUCT_CASES_TAC(SPEC `h:cpstep` (cases "cpstep")) THEN
  ASM_SIMP_TAC[config_step; cpker; FILTER; LENGTH; distinctness "cpstep"]);;

let SIZE_CPKER = prove
 (`!cp. config_prog cp ==> LENGTH(cpker cp) = cpksize cp`,
  REWRITE_TAC[config_prog] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SIZE_CPKER_ALL THEN ASM_REWRITE_TAC[]);;

(* base ring of the construction: cpmap0 has perimeter ring [0;1].           *)
let CPRING_CPMAP0 = prove
 (`cpring cpmap0 1 = [0; 1]`,
  SUBGOAL_THEN `node_map cpmap0 (node_map cpmap0 1) = 1` ASSUME_TAC THENL
   [REWRITE_TAC[CPMAP0_COMPONENTS; swap] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[cpring; orbit_list; CPMAP0_NODE_OSIZE]] THEN
  REWRITE_TAC[ARITH_RULE `2 - 1 = SUC 0`; iterlist; REVERSE; APPEND;
              CPMAP0_COMPONENTS; swap] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* fband depends only on the MEM-set of the list (the cover predicate is     *)
(* invariant under reordering the ring, e.g. the ecpR rotation).             *)
let FBAND_MEM_CONG = prove
 (`!(H:(A)hypermap) p q x. (!z. MEM z p <=> MEM z q)
     ==> (fband H p x <=> fband H q x)`,
  SIMP_TAC[FBAND_MEM_IFF]);;

(* ------------------------------------------------------------------------- *)
(* fband_icpN, fband_icpU, fband_icpY, fband_icpH (Gonthier                  *)
(* cfmap.v:790,859,1012,1105): every dart of an extended map is              *)
(* face-connected to an old dart, or (for U/Y/H) to the new apex pointer.    *)
(* These drive the CPMAP_COVER and CPMAP_SIMPLE inductions.                  *)
(* ------------------------------------------------------------------------- *)

(* ecpN: a sits in x0's face orbit, b in face(edge(face(edge x0)))'s; old    *)
(* darts are cface to themselves -- so every ecpN dart reaches an old dart.  *)
let FBAND_ICPN = prove
 (`!(H:(num)hypermap) x0 u.
     x0 IN dart H /\ long_cpring H x0 /\ u IN dart(ecpN H x0)
     ==> ?z. z IN dart H /\ cface (ecpN H x0) u z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ecpN_pt H IN dart(ecpN H x0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ECPN_PT_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPN_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `u IN dart(ecpN H x0)` THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPN_A_IN_FACE_ORBIT) THEN
    ASM_REWRITE_TAC[GSYM face] THEN CFACE_TAC[];
    EXISTS_TAC
     `face_map H (edge_map H (face_map H (edge_map H (x0:num))))` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC FACE_MAP_IN_DART ORELSE
             MATCH_MP_TAC EDGE_MAP_IN_DART) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPN_B_IN_FACE_ORBIT) THEN
    ASM_REWRITE_TAC[GSYM face; FINITE_DART; EDGE_MAP_PERMUTES;
                    NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
    CFACE_TAC[];
    EXISTS_TAC `u:num` THEN ASM_REWRITE_TAC[cface; SELF_IN_FACE]]);;

(* ecpU: apex a is an isolated face; b reaches node x0; old darts reach      *)
(* themselves.                                                               *)
let FBAND_ICPU = prove
 (`!(H:(num)hypermap) x0 u.
     x0 IN dart H /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H /\
     u IN dart(ecpU H x0)
     ==> (?z. z IN dart H /\ cface (ecpU H x0) u z) \/
     cface (ecpU H x0) u (ecpU_pt H)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `u IN dart(ecpU H x0)` THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN REWRITE_TAC[ecpU_pt; cface; SELF_IN_FACE];
    DISJ1_TAC THEN EXISTS_TAC `node_map H (x0:num)` THEN
    ASM_SIMP_TAC[NODE_FACE_IN_DART] THEN
    REWRITE_TAC[cface; face; ORBIT_MAP_ITER; IN_ELIM_THM] THEN
    EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[ONE; ITER] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_FACE_SND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    DISJ1_TAC THEN EXISTS_TAC `u:num` THEN
    ASM_REWRITE_TAC[cface; SELF_IN_FACE]]);;

(* ecpY = ecpN o ecpU: u reaches a dart of ecpU (FBAND_ICPN), which reaches  *)
(* an old dart or the inner apex ecpU_pt (FBAND_ICPU); the apex face-steps   *)
(* to ecpY_pt via the ecpY apex 2-cycle.                                     *)
let FBAND_ICPY = prove
 (`!(H:(num)hypermap) x0 u.
     x0 IN dart H /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H /\
     u IN dart(ecpY H x0)
     ==> (?z. z IN dart H /\ cface (ecpY H x0) u z) \/
     cface (ecpY H x0) u (ecpY_pt H x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ecpU_pt H IN dart(ecpU H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[ECPU_PT_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPEC `ecpU H x0` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpU H x0`; `ecpU_pt H`; `u:num`] FBAND_ICPN) THEN
  ASM_SIMP_TAC[LONG_ECPU; GSYM ecpY] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `z:num`] FBAND_ICPU) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC)
    ASSUME_TAC) THENL
   [DISJ1_TAC THEN EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ecpU H x0`; `ecpU_pt H`; `z:num`; `w:num`]
      CFACE_ECPN_LIFT) THEN
    ASM_SIMP_TAC[LONG_ECPU; GSYM ecpY] THEN CFACE_TAC[];
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`ecpU H x0`; `ecpU_pt H`; `z:num`; `ecpU_pt H`]
      CFACE_ECPN_LIFT) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPY_APEX_TWO_CYCLE) THEN
    ASM_SIMP_TAC[LONG_ECPU; GSYM ecpY] THEN CFACE_TAC[]]);;

(* ecpH = ecpN o ecpY: same composition, inner apex ecpY_pt face-steps to    *)
(* ecpH_pt (= ecpN_pt(ecpY H x0)) via the ecpN a-branch                      *)
(* (ECPN_A_IN_FACE_ORBIT).                                                   *)
let FBAND_ICPH = prove
 (`!(H:(num)hypermap) x0 u.
     x0 IN dart H /\ proper_cpring H x0 /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H /\
     u IN dart(ecpH H x0)
     ==> (?z. z IN dart H /\ cface (ecpH H x0) u z) \/
     cface (ecpH H x0) u (ecpH_pt H x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ecpY_pt H x0 IN dart(ecpY H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[ECPY_PT_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `long_cpring (ecpY H x0) (ecpY_pt H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[LONG_ECPY]; ALL_TAC] THEN
  MP_TAC(ISPEC `ecpY H x0` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ecpY H x0`; `ecpY_pt H x0`; `u:num`] FBAND_ICPN) THEN
  ASM_REWRITE_TAC[GSYM ecpH] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `z:num`] FBAND_ICPY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC)
    ASSUME_TAC) THENL
   [DISJ1_TAC THEN EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ecpY H x0`; `ecpY_pt H x0`; `z:num`; `w:num`]
      CFACE_ECPN_LIFT) THEN
    ASM_REWRITE_TAC[GSYM ecpH] THEN CFACE_TAC[];
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`ecpY H x0`; `ecpY_pt H x0`; `z:num`; `ecpY_pt H x0`]
      CFACE_ECPN_LIFT) THEN
    MP_TAC(ISPECL [`ecpY H x0`; `ecpY_pt H x0`] ECPN_A_IN_FACE_ORBIT) THEN
    ASM_REWRITE_TAC[GSYM ecpH; GSYM face; ecpH_pt; ecpN_pt] THEN
    CFACE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Toward CPMAP_COVER / CPMAP_SIMPLE (Gonthier cfmap.v:1249,1228).           *)
(* Structural cons lemmas + ring-coverage of each construction step.         *)
(* ------------------------------------------------------------------------- *)

(* config_prog of a cons: head is R/Y/H, and the tail is a config_prog       *)
(* unless it is empty (in which case the head was the terminal CpY).         *)
let CONFIG_PROG_CONS = prove
 (`!s cp. config_prog (CONS s cp)
          ==> ((?n. s = CpR n) \/ s = CpY \/ s = CpH) /\
              (cp = [] ==> s = CpY) /\
              (~(cp = []) ==> config_prog cp)`,
  REWRITE_TAC[config_prog; ALL; LAST; CONFIG_STEP_CASES] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  MESON_TAC[]);;

(* long ring ==> proper ring (2<len ==> 1<len).                              *)
let LONG_IMP_PROPER = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ long_cpring H x0
     ==> proper_cpring H x0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SIZE_PROPER_CPRING] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] SIZE_LONG_CPRING) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* node_map(ecpY)(ecpY_pt) = the SND fresh dart b (the ecpY ring head).      *)
let NODE_ECPY_PT_VALUE = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H ==>
     node_map (ecpY H x0) (ecpY_pt H x0) = SND(new_dart2(dart H))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY; ecpY_pt] THEN
  SUBGOAL_THEN `ecpU_pt H IN dart(ecpU H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[ECPU_PT_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ecpU H x0`; `ecpU_pt H`] ECPN_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ecpN_pt; ecpN_node] THEN
  SUBGOAL_THEN `long_cpring (ecpU H x0) (ecpU_pt H)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[LONG_ECPU]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
 MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
 ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ecpU_pt; ecpU_node]);;

(* cface_node_ecpY (Gonthier cfmap.v:994): the new ecpY ring head b is cface *)
(* to the dropped old head node_H x0 (via one ecpU face step b->node x0,     *)
(* lifted).                                                                  *)
let CFACE_NODE_ECPY = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H
     ==> cface (ecpY H x0) (SND(new_dart2(dart H))) (node_map H x0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SND(new_dart2(dart H)) IN dart(ecpU H x0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
   ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  REWRITE_TAC[ecpY] THEN MATCH_MP_TAC CFACE_ECPN_LIFT THEN
  ASM_SIMP_TAC[LONG_ECPU; ECPU_PT_IN_DART] THEN
  MP_TAC(ISPEC `ecpU H x0` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[cface; face; ORBIT_MAP_ITER; IN_ELIM_THM] THEN
  EXISTS_TAC `1` THEN
  REWRITE_TAC[ONE; ITER] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_FACE_SND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* cface_node_ecpH (Gonthier cfmap.v:1087): the new ecpH ring head           *)
(* node_map(ecpY)(ecpY_pt) (= b) is cface to the dropped old head node_H x0. *)
let CFACE_NODE_ECPH = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ proper_cpring H x0 /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H
     ==> cface (ecpH H x0) (node_map(ecpY H x0)(ecpY_pt H x0)) (node_map H x0)`
     ,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] NODE_ECPY_PT_VALUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `ecpY_pt H x0 IN dart(ecpY H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[ECPY_PT_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `long_cpring (ecpY H x0) (ecpY_pt H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[LONG_ECPY]; ALL_TAC] THEN
  MP_TAC(ISPEC `ecpY H x0` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  REWRITE_TAC[ecpH] THEN MATCH_MP_TAC CFACE_ECPN_LIFT THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPY_DART) THEN
   ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  MATCH_MP_TAC CFACE_NODE_ECPY THEN ASM_REWRITE_TAC[]);;

(* RING_COVERED_ECPY: every old-ring element is in the fband of the new ecpY *)
(* ring (dropped head node_H x0 -> new head b via CFACE_NODE_ECPY; rest in   *)
(* TL).                                                                      *)
let RING_COVERED_ECPY = prove
 (`!(H:(num)hypermap) x0 e.
     x0 IN dart H /\ proper_cpring H x0 /\ MEM e (cpring H x0)
     ==> fband (ecpY H x0) (cpring (ecpY H x0) (ecpY_pt H x0)) e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CPRING_ECPY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CPRING_CONS_HEAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(AP_TERM `MEM (e:num)` th)) THEN
  ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN
  REWRITE_TAC[fband; EX] THEN FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_NODE_ECPY) THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                    FACE_MAP_PERMUTES] THEN
    CFACE_TAC[];
    REPEAT DISJ2_TAC THEN REWRITE_TAC[GSYM fband] THEN
    MATCH_MP_TAC FBAND_MEM THEN ASM_REWRITE_TAC[]]);;

(* RING_COVERED_ECPH: every old-ring element is in the fband of (new ecpH    *)
(* ring ++ [x0]). The two dropped old darts: node_H x0 -> new head           *)
(* (CFACE_NODE_ECPH); the x0 -> the singleton kernel dart [x0] (= SND(cpmap  *)
(* cp), the new CpH kernel elt).                                             *)
let RING_COVERED_ECPH = prove
 (`!(H:(num)hypermap) x0 e.
     x0 IN dart H /\ proper_cpring H x0 /\ MEM e (cpring H x0)
     ==> fband (ecpH H x0)
               (APPEND (cpring (ecpH H x0) (ecpH_pt H x0)) [x0]) e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CPRING_ECPH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(AP_TERM `MEM (e:num)` th)) THEN
  ASM_REWRITE_TAC[MEM] THEN STRIP_TAC THENL
   [REWRITE_TAC[APPEND; fband; EX] THEN DISJ1_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] CFACE_NODE_ECPH) THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                    FACE_MAP_PERMUTES] THEN
    CFACE_TAC[];
    FIRST_X_ASSUM SUBST1_TAC THEN MATCH_MP_TAC FBAND_MEM THEN
    REWRITE_TAC[MEM_APPEND; MEM];
    MATCH_MP_TAC FBAND_MEM THEN REWRITE_TAC[MEM_APPEND; MEM] THEN
    ASM_REWRITE_TAC[]]);;

(* ring elements are darts of the map.                                       *)
let MEM_CPRING_IN_DART = prove
 (`!(H:(num)hypermap) x0 e. x0 IN dart H /\ MEM e (cpring H x0)
     ==> e IN dart H`,
  SIMP_TAC[MEM_CPRING; cnode; node; IMP_CONJ] THEN
  MESON_TAC[ORBIT_MAP_IN; FINITE_DART; NODE_MAP_PERMUTES]);;

(* old cface lifts through ecpY/ecpH (compose the ecpU/ecpN lifts).          *)
let CFACE_ECPY_LIFT = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ FINITE(dart H) /\ edge_map H permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\
     x IN dart H /\ cface H x y
     ==> cface (ecpY H x0) x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY] THEN
  SUBGOAL_THEN `ecpU_pt H IN dart(ecpU H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[ECPU_PT_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPEC `ecpU H x0` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MATCH_MP_TAC CFACE_ECPN_LIFT THEN ASM_SIMP_TAC[LONG_ECPU] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
   ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  MATCH_MP_TAC CFACE_ECPU_LIFT THEN ASM_REWRITE_TAC[]);;

let CFACE_ECPH_LIFT = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ proper_cpring H x0 /\ FINITE(dart H) /\
     edge_map H permutes dart H /\
     node_map H permutes dart H /\ face_map H permutes dart H /\
     x IN dart H /\ cface H x y
     ==> cface (ecpH H x0) x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  SUBGOAL_THEN `ecpY_pt H x0 IN dart(ecpY H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[ECPY_PT_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `long_cpring (ecpY H x0) (ecpY_pt H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[LONG_ECPY]; ALL_TAC] THEN
  MP_TAC(ISPEC `ecpY H x0` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  MATCH_MP_TAC CFACE_ECPN_LIFT THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPY_DART) THEN
   ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  MATCH_MP_TAC CFACE_ECPY_LIFT THEN ASM_REWRITE_TAC[]);;

(* dart monotonicity: dart of cpmap t embeds into dart of cpmap(s::t).       *)
let DART_SUBSET_ECPY = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> dart H SUBSET dart(ecpY H x0)`,
  REPEAT STRIP_TAC THEN
 MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPY_DART) THEN
 ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPU_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let DART_SUBSET_ECPH = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H ==> dart H SUBSET dart(ecpH H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  SUBGOAL_THEN `ecpY_pt H x0 IN dart(ecpY H x0)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[ECPY_PT_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ecpY H x0`; `ecpY_pt H x0`] ECPN_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] DART_SUBSET_ECPY) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let DART_SUBSET_CONS = prove
 (`!s t. config_step s
     ==> dart(FST(cpmap t)) SUBSET dart(FST(cpmap (CONS s t)))`,
  MATCH_MP_TAC cpstep_INDUCT THEN
  REWRITE_TAC[config_step; CPMAP_CONS_R; CPMAP_CONS_Y; CPMAP_CONS_H; ecpR;
              SUBSET_REFL] THEN
  SIMP_TAC[DART_SUBSET_ECPY; DART_SUBSET_ECPH; CPMAP_PT_IN_DART]);;

(* kernel membership of a cons reduces to the tail kernel or the new CpH     *)
(* apex.                                                                     *)
let CPKER_CONS_MEM = prove
 (`!s t e. config_step s /\ MEM e (cpker (CONS s t))
     ==> MEM e (cpker t) \/ e = SND(cpmap t)`,
  MATCH_MP_TAC cpstep_INDUCT THEN REWRITE_TAC[config_step; cpker; MEM] THEN
  MESON_TAC[]);;

(* Every kernel dart is a dart of the map.                                   *)
let CPKER_IN_DART = prove
 (`!cp. ALL config_step cp ==> !e. MEM e (cpker cp)
     ==> e IN dart(FST(cpmap cp))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[cpker; MEM; ALL; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:cpstep`; `t:(cpstep)list`; `e:num`] CPKER_CONS_MEM) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:cpstep`; `t:(cpstep)list`] DART_SUBSET_CONS) THEN
  ASM_REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `ALL config_step t`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CPMAP_PT_IN_DART]]);;

(* Per-step cover preservation: R rotates the ring (the MEM set is           *)
(* invariant); Y and H are instances of COVER_STEP below, with FBAND_ICPY /  *)
(* FBAND_ICPH and RING_COVERED_ECPY / RING_COVERED_ECPH (the dropped ring    *)
(* head goes to the new head or apex).                                       *)
let COVER_STEP_R = prove
 (`!(G:(num)hypermap) (s:num) (n:num) (ker:(num)list).
     s IN dart G /\
     (!u. u IN dart G ==> fband G (APPEND (cpring G s) ker) u)
     ==> !u. u IN dart(ecpR G n s)
             ==> fband (ecpR G n s)
             (APPEND (cpring (ecpR G n s) (ecpR_pt G n s)) ker) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num` THEN
  REWRITE_TAC[ecpR] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `u:num` th)) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FBAND_MEM_CONG THEN
  X_GEN_TAC `e:num` THEN
  REWRITE_TAC[MEM_APPEND] THEN
  MATCH_MP_TAC(TAUT `(b <=> a) ==> (a \/ c <=> b \/ c)`) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `n:num`; `s:num`;
                 `e:num`] MEM_CPRING_ECPR) THEN
  REWRITE_TAC[ecpR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The cover passes along a step from G to G' when every dart of G' is       *)
(* cofacial with an old dart or with the new apex pt, the old faces survive, *)
(* and the new list l covers the old ring r and kernel ker and contains pt.  *)
let COVER_STEP = prove
 (`!(G:(num)hypermap) (G':(num)hypermap) r ker l pt.
     (!e. MEM e r \/ MEM e ker ==> e IN dart G) /\
     (!u. u IN dart G ==> fband G (APPEND r ker) u) /\
     (!u. u IN dart G'
          ==> (?z. z IN dart G /\ cface G' u z) \/ cface G' u pt) /\
     (!x y. x IN dart G /\ cface G x y ==> cface G' x y) /\
     (!e. MEM e r \/ MEM e ker ==> fband G' l e) /\ MEM pt l
     ==> !u. u IN dart G' ==> fband G' l u`,
  REWRITE_TAC[FBAND_MEM_IFF; MEM_APPEND] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(u:num) IN dart G'`)) THEN
  ASM_MESON_TAC[CFT_TRANS]);;

let COVER_STEP_Y = prove
 (`!(G:(num)hypermap) (s:num) (ker:(num)list).
     s IN dart G /\ proper_cpring G s /\ (!e. MEM e ker ==> e IN dart G) /\
     (!u. u IN dart G ==> fband G (APPEND (cpring G s) ker) u)
     ==> !u. u IN dart(ecpY G s)
             ==> fband (ecpY G s)
                       (APPEND (cpring (ecpY G s) (ecpY_pt G s)) ker) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COVER_STEP THEN
  MAP_EVERY EXISTS_TAC
   [`G:(num)hypermap`; `cpring G s`; `ker:(num)list`; `ecpY_pt G s`] THEN
  ASM_SIMP_TAC[FBAND_ICPY; CFACE_ECPY_LIFT; FINITE_DART; EDGE_MAP_PERMUTES;
               NODE_MAP_PERMUTES; FACE_MAP_PERMUTES; FBAND_APPEND;
               MEM_APPEND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MEM_CPRING_IN_DART];
    ASM_MESON_TAC[RING_COVERED_ECPY; FBAND_MEM];
    ASM_SIMP_TAC[CPRING_ECPY; MEM]]);;

let COVER_STEP_H = prove
 (`!(G:(num)hypermap) (s:num) (ker:(num)list).
     s IN dart G /\ proper_cpring G s /\ (!e. MEM e ker ==> e IN dart G) /\
     (!u. u IN dart G ==> fband G (APPEND (cpring G s) ker) u)
     ==> !u. u IN dart(ecpH G s)
             ==> fband (ecpH G s)
                       (APPEND (cpring (ecpH G s) (ecpH_pt G s)) (CONS s ker))
                       u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COVER_STEP THEN
  MAP_EVERY EXISTS_TAC
   [`G:(num)hypermap`; `cpring G s`; `ker:(num)list`; `ecpH_pt G s`] THEN
  ASM_SIMP_TAC[FBAND_ICPH; CFACE_ECPH_LIFT; FINITE_DART; EDGE_MAP_PERMUTES;
               NODE_MAP_PERMUTES; FACE_MAP_PERMUTES; FBAND_APPEND;
               MEM_APPEND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MEM_CPRING_IN_DART];
    MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] RING_COVERED_ECPH) THEN
    ASM_REWRITE_TAC[FBAND_APPEND; FBAND_CONS; FBAND_NIL] THEN
    MESON_TAC[FBAND_MEM; MEM];
    ASM_SIMP_TAC[CPRING_ECPH; MEM]]);;

(* base cover for cpmap0 ([0;1] is the whole ring, kernel empty).            *)
let CPMAP_COVER_BASE = prove
 (`!u. u IN dart cpmap0 ==> fband cpmap0 (APPEND (cpring cpmap0 1) []) u`,
  REWRITE_TAC[APPEND_NIL; CPRING_CPMAP0; CPMAP0_COMPONENTS; IN_INSERT;
              NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FBAND_MEM THEN ASM_REWRITE_TAC[MEM]);;

let PROPER_CPMAP0 = prove
 (`proper_cpring cpmap0 1`,
  SUBGOAL_THEN `(1:num) IN dart cpmap0` ASSUME_TAC THENL
   [REWRITE_TAC[CPMAP0_COMPONENTS; IN_INSERT]; ALL_TAC] THEN
  ASM_SIMP_TAC[SIZE_PROPER_CPRING] THEN REWRITE_TAC[CPRING_CPMAP0; LENGTH] THEN
  ARITH_TAC);;

(* CPMAP_COVER (Gonthier cpmap_cover, cfmap.v:1249), by induction on         *)
(* configuration programs as CPMAP_SIMPLE.                                   *)
let CPMAP_COVER = prove
 (`!cp. config_prog cp
        ==> !u. u IN dart(FST(cpmap cp))
                ==> fband (FST(cpmap cp))
                          (APPEND (cpring (FST(cpmap cp)) (SND(cpmap cp)))
                          (cpker cp)) u`,
  MATCH_MP_TAC CONFIG_PROG_INDUCT THEN
  REWRITE_TAC[CPMAP_CONS_R; CPMAP_CONS_Y; CPMAP_CONS_H; CPMAP_NIL_PAIR;
              cpker] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COVER_STEP_Y THEN
    REWRITE_TAC[PROPER_CPMAP0; MEM; CPMAP_COVER_BASE; CPMAP0_COMPONENTS;
                IN_INSERT];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COVER_STEP_R THEN
    ASM_REWRITE_TAC[CPMAP_PT_IN_DART];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COVER_STEP_Y THEN
    ASM_SIMP_TAC[CPMAP_PT_IN_DART; CPMAP_PROPER; CONFIG_PROG_CUBIC] THEN
    ASM_MESON_TAC[CPKER_IN_DART; config_prog];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COVER_STEP_H THEN
    ASM_SIMP_TAC[CPMAP_PT_IN_DART; CPMAP_PROPER; CONFIG_PROG_CUBIC] THEN
    ASM_MESON_TAC[CPKER_IN_DART; config_prog]]);;

(* ========================================================================= *)
(* Toward CPMAP_SIMPLE (Gonthier cpmap_simple): the ring together with the   *)
(* kernel transversal is face-simple.  Face-simplicity is PAIRWISE           *)
(* non-cofaciality; it transfers to a distinct sublist with the same face    *)
(* relation, and the two new ring heads of a Y or H step are handled apart   *)
(* (the apex face is new, the other head shares the face of the old head).   *)
(* ========================================================================= *)

let FACE_SIMPLE_EQ_PAIRWISE = prove
 (`!(H:(A)hypermap) p. face_simple H p <=> PAIRWISE (\x y. ~cface H x y) p`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[face_simple; PAIRWISE; fband; NOT_EX]);;

let PAIRWISE_ORBIT_LIST = prove
 (`!(f:A->A) s z. FINITE s /\ f permutes s /\ z IN s
     ==> PAIRWISE (\x y. ~(x = y)) (orbit_list f z)`,
  REWRITE_TAC[orbit_list; ORBIT_LIST_PAIRWISE]);;

let PAIRWISE_CPRING = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> PAIRWISE (\x y. ~(x = y)) (cpring H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cpring] THEN
  MATCH_MP_TAC PAIRWISE_NEQ_REVERSE THEN MATCH_MP_TAC PAIRWISE_ORBIT_LIST THEN
  EXISTS_TAC `dart(H:(num)hypermap)` THEN
  ASM_SIMP_TAC[FINITE_DART; NODE_MAP_PERMUTES; NODE_MAP_IN_DART]);;

let PAIRWISE_SYM_MEM = prove
 (`!(R:A->A->bool) l.
     (!x y. R x y ==> R y x) /\ PAIRWISE R l
     ==> !x y. MEM x l /\ MEM y l /\ ~(x = y) ==> R x y`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[PAIRWISE; MEM; GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let PAIRWISE_NEQ_SAME_SET = prove
 (`!l1 l2:(A)list.
     PAIRWISE (\x y. ~(x = y)) l1 /\ (!x. MEM x l1 <=> MEM x l2) /\
     LENGTH l1 = LENGTH l2
     ==> PAIRWISE (\x y. ~(x = y)) l2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `set_of_list (l1:(A)list) = set_of_list l2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_SET_OF_LIST]; ALL_TAC] THEN
  ASM_MESON_TAC[HAS_SIZE_SET_OF_LIST]);;

let FACE_SIMPLE_TRANSFER = prove
 (`!(G:(A)hypermap) (H:(A)hypermap) l1 l2.
     face_simple H l1 /\ PAIRWISE (\x y. ~(x = y)) l2 /\
     (!x. MEM x l2 ==> MEM x l1) /\
     (!x y. MEM x l2 /\ MEM y l2 ==> (cface G x y <=> cface H x y))
     ==> face_simple G l2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACE_SIMPLE_EQ_PAIRWISE] THEN
  MATCH_MP_TAC PAIRWISE_FROM_MEM THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`\x y. ~cface (H:(A)hypermap) x y`; `l1:(A)list`]
    PAIRWISE_SYM_MEM) THEN
  ASM_REWRITE_TAC[GSYM FACE_SIMPLE_EQ_PAIRWISE] THEN
  ANTS_TAC THENL [MESON_TAC[CFACE_SYM_GEN]; ASM_SIMP_TAC[]]);;

let CFACE_ECPY_PROJ = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ x IN dart H /\ y IN dart H /\ cface (ecpY H x0) x y
     ==> cface H x y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CFACE_ECPU_PROJ THEN
  EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CFACE_ECPN_PROJ THEN EXISTS_TAC `ecpU_pt H` THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART; LONG_ECPU; GSYM ecpY] THEN
  ASM_MESON_TAC[DART_SUBSET_ECPU; SUBSET]);;

let CFACE_ECPH_PROJ = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ proper_cpring H x0 /\ x IN dart H /\ y IN dart H /\
     cface (ecpH H x0) x y
     ==> cface H x y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CFACE_ECPY_PROJ THEN
  EXISTS_TAC `x0:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CFACE_ECPN_PROJ THEN EXISTS_TAC `ecpY_pt H x0` THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; GSYM ecpH] THEN
  ASM_MESON_TAC[DART_SUBSET_ECPY; SUBSET]);;

let SIMPLE_CPMAP0_BASE = prove
 (`face_simple cpmap0 (APPEND (cpring cpmap0 1) [])`,
  REWRITE_TAC[APPEND_NIL; CPRING_CPMAP0; face_simple; FBAND_CONS; FBAND_NIL;
              cface; face; CPMAP0_COMPONENTS] THEN
  SIMP_TAC[ORBIT_FIXED; I_THM; IN_SING; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The three steps of a configuration program preserve the simplicity of     *)
(* ring ++ kernel.                                                           *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_STEP_R = prove
 (`!(G:(num)hypermap) s n ker.
     s IN dart G /\ face_simple G (APPEND (cpring G s) ker)
     ==> face_simple (ecpR G n s)
                     (APPEND (cpring (ecpR G n s) (ecpR_pt G n s)) ker)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FACE_SIMPLE_APPEND']) THEN
  STRIP_TAC THEN MATCH_MP_TAC FACE_SIMPLE_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`G:(num)hypermap`; `APPEND (cpring G s) ker`] THEN
  ASM_REWRITE_TAC[ecpR; MEM_APPEND] THEN
  ASM_SIMP_TAC[REWRITE_RULE[ecpR] MEM_CPRING_ECPR; PAIRWISE_APPEND;
               PAIRWISE_CPRING; ECPR_PT_IN_DART] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FACE_SIMPLE_PAIRWISE_GEN THEN
    EXISTS_TAC `G:(num)hypermap` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[FBAND_MEM]]);;

let CFACE_ECPY_APEX_NOT_B = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> ~cface (ecpY H x0) (ecpY_pt H x0) (SND(new_dart2(dart H)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `SND(new_dart2(dart H))`]
    FACE_ECPY_APEX) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  MP_TAC(ISPECL [`SND(new_dart2(dart H))`; `ecpY_pt H x0`; `dart(ecpU H x0)`]
    IN_NOTIN_NEQ) THEN
  MP_TAC(ISPEC `dart(ecpU H x0)` NEW_DART2_FRESH) THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] SND_NEW_IN_ECPU) THEN
  ASM_REWRITE_TAC[FINITE_DART; ecpY_pt; ecpN_pt; ecpU_pt] THEN MESON_TAC[]);;

let CFACE_ECPH_APEX_NOT_B = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> ~cface (ecpH H x0) (ecpH_pt H x0) (SND(new_dart2(dart H)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `SND(new_dart2(dart H))`]
    ECPH_APEX_FACE_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`SND(new_dart2(dart H))`; `ecpH_pt H x0`; `dart(ecpY H x0)`]
    IN_NOTIN_NEQ) THEN
  MP_TAC(ISPECL [`SND(new_dart2(dart H))`; `ecpY_pt H x0`; `dart(ecpU H x0)`]
    IN_NOTIN_NEQ) THEN
  MP_TAC(ISPEC `dart(ecpY H x0)` NEW_DART2_FRESH) THEN
  MP_TAC(ISPEC `dart(ecpU H x0)` NEW_DART2_FRESH) THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] SND_NEW_IN_ECPU) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPY_DART) THEN
  ASM_REWRITE_TAC[FINITE_DART; ecpH_pt; ecpY_pt; ecpN_pt; ecpU_pt] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

(* The common core of the Y and H steps: the new ring CONS b (CONS pt p) is  *)
(* face-simple when b is cofacial with the dropped old head node_map G s,    *)
(* the apex pt is cofacial with no old dart, and p lists the same old darts  *)
(* as q, whose face relation is unchanged.                                   *)
let SIMPLE_TWO_HEADS = prove
 (`!(G:(num)hypermap) (G':(num)hypermap) s b pt p q.
     s IN dart G /\ (!z:num. MEM z q ==> z IN dart G) /\
     (!z:num. MEM z p <=> MEM z q) /\ PAIRWISE (\x y. ~(x = y)) p /\
     face_simple G q /\ ~fband G q (node_map G s) /\
     b IN dart G' /\ ~cface G' pt b /\ cface G' b (node_map G s) /\
     (!z. z IN dart G ==> ~cface G' pt z) /\
     (!x y. x IN dart G /\ y IN dart G ==> (cface G' x y <=> cface G x y))
     ==> face_simple G' (CONS b (CONS pt p))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[face_simple; FBAND_CONS; DE_MORGAN_THM] THEN
  REPEAT CONJ_TAC THENL
   [CFACE_TAC[];
    REWRITE_TAC[fband; GSYM EX_MEM] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `MEM (z:num) q /\ z IN dart (G:(num)hypermap)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~fband (G:(num)hypermap) q (node_map G s)` THEN
    REWRITE_TAC[fband; GSYM EX_MEM] THEN EXISTS_TAC `z:num` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cface (G':(num)hypermap) (node_map (G:(num)hypermap) s) z`
    MP_TAC THENL [CFACE_TAC[]; ASM_SIMP_TAC[NODE_MAP_IN_DART]];
    REWRITE_TAC[fband; GSYM EX_MEM] THEN
    UNDISCH_TAC `!z. z IN dart G ==> ~cface (G':(num)hypermap) pt z` THEN
    UNDISCH_TAC `!z:num. MEM z q ==> z IN dart (G:(num)hypermap)` THEN
    UNDISCH_TAC `!z:num. MEM z p <=> MEM z q` THEN MESON_TAC[];
    MATCH_MP_TAC FACE_SIMPLE_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`G:(num)hypermap`; `q:(num)list`] THEN
    ASM_SIMP_TAC[]]);;

let SIMPLE_STEP_Y = prove
 (`!(G:(num)hypermap) s ker.
     s IN dart G /\ proper_cpring G s /\ (!e. MEM e ker ==> e IN dart G) /\
     face_simple G (APPEND (cpring G s) ker)
     ==> face_simple (ecpY G s)
                     (APPEND (cpring (ecpY G s) (ecpY_pt G s)) ker)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `face_simple (G:(num)hypermap)
     (CONS (node_map G s) (APPEND (TL(cpring G s)) ker))` MP_TAC THENL
   [REWRITE_TAC[GSYM APPEND] THEN ASM_MESON_TAC[CPRING_CONS_HEAD];
    ALL_TAC] THEN
  REWRITE_TAC[face_simple] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND(new_dart2(dart G)) IN dart(ecpY (G:(num)hypermap) s)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ECPY_DART; IN_INSERT; SND_NEW_IN_ECPU]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] CFACE_ECPY_APEX_OLD) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] CFACE_NODE_ECPY) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] CFACE_ECPY_APEX_NOT_B) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  REPEAT DISCH_TAC THEN ASM_SIMP_TAC[CPRING_ECPY; APPEND] THEN
  MATCH_MP_TAC SIMPLE_TWO_HEADS THEN
  MAP_EVERY EXISTS_TAC [`G:(num)hypermap`; `s:num`;
                        `APPEND (TL(cpring (G:(num)hypermap) s)) ker`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:num` THEN REWRITE_TAC[MEM_APPEND] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MEM_CPRING_IN_DART THEN
    EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_TL_IMP THEN
    ASM_SIMP_TAC[CPRING_NONEMPTY];
    MATCH_MP_TAC FACE_SIMPLE_PAIRWISE_GEN THEN
    EXISTS_TAC `G:(num)hypermap` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`; `x:num`; `y:num`]
      CFACE_ECPY_PROJ) THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`; `x:num`; `y:num`]
      CFACE_ECPY_LIFT) THEN
    ASM_SIMP_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                 FACE_MAP_PERMUTES] THEN
    MESON_TAC[]]);;

let SIMPLE_STEP_H = prove
 (`!(G:(num)hypermap) s ker.
     s IN dart G /\ proper_cpring G s /\ (!e. MEM e ker ==> e IN dart G) /\
     face_simple G (APPEND (cpring G s) ker)
     ==> face_simple (ecpH G s)
                     (APPEND (cpring (ecpH G s) (ecpH_pt G s)) (CONS s ker))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = CONS (s:num) (APPEND (TL(TL(cpring (G:(num)hypermap) s)))
                                       ker)` THEN
  SUBGOAL_THEN `!z:num. MEM z (APPEND (TL(TL(cpring (G:(num)hypermap) s)))
                                      (CONS s ker)) <=> MEM z q`
  ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:num. MEM z q ==> z IN dart (G:(num)hypermap)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:num` THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[MEM_APPEND; MEM] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC MEM_CPRING_IN_DART THEN
    EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEM_TL_TL_IMP THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] HEAD_PROPER_CPRING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[NOT_CONS_NIL; TL];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_simple (G:(num)hypermap) (CONS (node_map G s) q)`
  MP_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[GSYM APPEND] THEN
    ASM_MESON_TAC[HEAD_PROPER_CPRING];
    ALL_TAC] THEN
  REWRITE_TAC[face_simple] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND(new_dart2(dart G)) IN dart(ecpH (G:(num)hypermap) s)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ecpH] THEN
    MP_TAC(ISPECL [`ecpY (G:(num)hypermap) s`; `ecpY_pt G s`]
      ECPN_COMPONENTS) THEN
    ASM_SIMP_TAC[ECPY_PT_IN_DART] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ECPY_DART; IN_INSERT; SND_NEW_IN_ECPU];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] CFACE_ECPH_APEX_OLD) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] CFACE_NODE_ECPH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] CFACE_ECPH_APEX_NOT_B) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`] NODE_ECPY_PT_VALUE) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                  FACE_MAP_PERMUTES] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[CPRING_ECPH; APPEND] THEN
  MATCH_MP_TAC SIMPLE_TWO_HEADS THEN
  MAP_EVERY EXISTS_TAC [`G:(num)hypermap`; `s:num`; `q:(num)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_NEQ_SAME_SET THEN EXISTS_TAC `q:(num)list` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_SIMPLE_PAIRWISE_GEN THEN
      EXISTS_TAC `G:(num)hypermap` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "q" THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`; `x:num`; `y:num`]
      CFACE_ECPH_PROJ) THEN
    MP_TAC(ISPECL [`G:(num)hypermap`; `s:num`; `x:num`; `y:num`]
      CFACE_ECPH_LIFT) THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                    FACE_MAP_PERMUTES] THEN
    MESON_TAC[]]);;

let CPMAP_SIMPLE = prove
 (`!cp. config_prog cp
        ==> face_simple (FST(cpmap cp))
                        (APPEND (cpring (FST(cpmap cp)) (SND(cpmap cp)))
                                (cpker cp))`,
  MATCH_MP_TAC CONFIG_PROG_INDUCT THEN
  REWRITE_TAC[CPMAP_CONS_R; CPMAP_CONS_Y; CPMAP_CONS_H; CPMAP_NIL_PAIR;
              cpker] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_STEP_Y THEN
    REWRITE_TAC[PROPER_CPMAP0; MEM; SIMPLE_CPMAP0_BASE; CPMAP0_COMPONENTS;
                IN_INSERT];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_STEP_R THEN
    ASM_REWRITE_TAC[CPMAP_PT_IN_DART];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_STEP_Y THEN
    ASM_SIMP_TAC[CPMAP_PT_IN_DART; CPMAP_PROPER; CONFIG_PROG_CUBIC] THEN
    ASM_MESON_TAC[CPKER_IN_DART; config_prog];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_STEP_H THEN
    ASM_SIMP_TAC[CPMAP_PT_IN_DART; CPMAP_PROPER; CONFIG_PROG_CUBIC] THEN
    ASM_MESON_TAC[CPKER_IN_DART; config_prog]]);;

(* ------------------------------------------------------------------------- *)
(* The ring of an A step (Gonthier cpring_ecpA): the node map of ecpA agrees *)
(* with the old one along node^2 x0, ..., node^(d-1) x0 (d = ring size), so  *)
(* a long ring loses its first two elements; a short ring is unchanged.      *)
(* ------------------------------------------------------------------------- *)

let ECPA_NODE_CLAUSES = prove
 (`!(H:(num)hypermap) x0 d. x0 IN dart H /\ d IN dart H
     ==> node_map (ecpA H x0) d =
         (if d = node_map H x0 then x0
          else if node_map H d = x0 then node_map H (node_map H x0)
          else node_map H d)`,
  SIMP_TAC[ECPA_COMPONENTS; ecpA_node]);;

let NODE_ECPA_PT = prove
 (`!(H:(num)hypermap) x0.
     node_map (ecpA H x0) (ecpA_pt H x0) = face_map H (edge_map H x0)`,
  REWRITE_TAC[ecpA_pt; edgeK]);;

let ECPA_NODE_ITER = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ long_cpring H x0
     ==> !j. 2 <= j /\ j <= orbit_size (node_map H) x0 - 1
             ==> ITER j (node_map (ecpA H x0)) (ecpA_pt H x0) =
                 ITER j (node_map H) x0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LONG_OSIZE) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = orbit_size (node_map H) (x0:num)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `node_map (ecpA H x0) (face_map H (edge_map H x0)) =
    node_map H (node_map H x0)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ECPA_NODE_CLAUSES; EDGE_MAP_IN_DART; FACE_MAP_IN_DART;
                 edgeK] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[long_cpring]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC ITER_THREAD THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ITER2; NODE_ECPA_PT]; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ECPA_NODE_CLAUSES; ITER_PERMUTES_IN; NODE_MAP_PERMUTES] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `j:num`] NODE_ITER_NEQ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `SUC j`] NODE_ITER_NEQ) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ITER] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `1 < j` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;

let SIZE_CPRING_ECPA = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ long_cpring H x0
     ==> orbit_size (node_map(ecpA H x0)) (ecpA_pt H x0) =
         orbit_size (node_map H) x0 - 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LONG_OSIZE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPA_NODE_ITER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "thread") THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] NODE_ITER_PRED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `d = orbit_size (node_map H) (x0:num)` THEN
  ABBREV_TAC `g = node_map (ecpA (H:(num)hypermap) x0)` THEN
  ABBREV_TAC `p = ecpA_pt (H:(num)hypermap) x0` THEN
  SUBGOAL_THEN `!u v. (g:num->num) u = g v ==> u = v` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MESON_TAC[NODEI]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:num->num) permutes dart (H:(num)hypermap) /\ p IN dart H`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g"; "p"] THEN
    ASM_MESON_TAC[ECPA_DART; NODE_MAP_PERMUTES; ECPA_PT_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN `ITER (d - 1) (g:num->num) p = g p` ASSUME_TAC THENL
   [USE_THEN "thread" (MP_TAC o SPEC `d - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXPAND_TAC ["g"; "p"] THEN ASM_REWRITE_TAC[NODE_ECPA_PT];
    ALL_TAC] THEN
  MATCH_MP_TAC ORBIT_SIZE_MINIMAL THEN EXISTS_TAC `dart(H:(num)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ASSUME `!u v. (g:num->num) u = g v ==> u = v`) THEN
    SUBGOAL_THEN `d - 1 = SUC(d - 2)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `g:num->num`) THEN
  REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN
  USE_THEN "thread" (MP_TAC o SPEC `SUC j`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `ITER (d - 1) (g:num->num) p = g p` THEN
  USE_THEN "thread" (MP_TAC o SPEC `d - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`node_map(H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                 `x0:num`; `SUC j`; `d - 1`] ITER_INJ_PERIOD) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let CPRING_ECPA_LONG = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ long_cpring H x0
     ==> cpring (ecpA H x0) (ecpA_pt H x0) = TL(TL(cpring H x0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LONG_OSIZE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPA_NODE_ITER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "thread") THEN
  MATCH_MP_TAC CPRING_BY_EL THEN
  ASM_SIMP_TAC[SIZE_CPRING_ECPA; ECPA_PT_IN_DART; ECPA_DART] THEN
  SUBGOAL_THEN `LENGTH(TL(TL(cpring H (x0:num)))) =
                orbit_size (node_map H) x0 - 2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] SIZE_CPRING) THEN
    ASM_SIMP_TAC[PROPER_OSIZE; ARITH_RULE `2 < d ==> 1 < d`] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(num)list->num`) THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_TL] THEN
  ASM_SIMP_TAC[EL_CPRING; ARITH_RULE `k < d - 2 ==> (k + 1) + 1 < d`] THEN
  SUBGOAL_THEN `((orbit_size (node_map H) x0 - 2) + 1) - k =
                (orbit_size (node_map H) (x0:num) + 1) - ((k + 1) + 1)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN USE_THEN "thread" MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let CPRING_ECPA_SHORT = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ ~long_cpring H x0
     ==> cpring (ecpA H x0) (ecpA_pt H x0) = cpring H x0`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[long_cpring]) THEN
  SUBGOAL_THEN `node_map H (node_map H x0) = (x0:num)` ASSUME_TAC THENL
   [ASM_MESON_TAC[edgeK]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map (ecpA H x0) = node_map H` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:num` THEN
    ASM_CASES_TAC `z IN dart (H:(num)hypermap)` THENL
     [ASM_SIMP_TAC[ECPA_NODE_CLAUSES] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[MAPS_OUTSIDE_DART; ECPA_DART]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ecpA_pt H x0 = x0` SUBST1_TAC THENL
   [MATCH_MP_TAC(ISPEC `H:(num)hypermap` NODEI) THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] NODE_ECPA_PT) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[cpring] THEN ASM_REWRITE_TAC[]]);;

let CPRING_ECPA = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> cpring (ecpA H x0) (ecpA_pt H x0) =
         (if long_cpring H x0 then TL(TL(cpring H x0)) else cpring H x0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CPRING_ECPA_LONG; CPRING_ECPA_SHORT]);;
