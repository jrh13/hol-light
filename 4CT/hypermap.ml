(* ========================================================================= *)
(* 4CT/hypermap.ml                                                           *)
(*                                                                           *)
(* hypermap.v: hypermaps.  The orbits orbit_map f x of a function; the type  *)
(* (A)hypermap packages a finite dart set with three permutations edge_map,  *)
(* node_map and face_map of it satisfying edge_map o node_map o face_map = I *)
(* (HYPERMAP_LEMMA, the cancellation laws edgeK, nodeK, faceK, injectivity   *)
(* and the closure of the dart set under the maps); the orbits edge, node,   *)
(* face of a dart and the relations cnode, cface; the numbers of edges,      *)
(* nodes, faces and (glink-)components, the genus and planar_hypermap; the   *)
(* contour relation clink; mk_hypermap, and the derived hypermaps permN,     *)
(* permF, dual and mirror with their components.                             *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/permutations.ml";;

(* ------------------------------------------------------------------------- *)
(* Orbits of a function                                                      *)
(* ------------------------------------------------------------------------- *)

let orbit_map = new_definition
  `orbit_map (f:A->A) (x:A) = {y:A | ?n:num. y = ITER n f x}`;;

let ORBIT_MAP_ITER = prove
 (`!(f:A->A) x y. y IN orbit_map f x <=> ?n. y = ITER n f x`,
  REWRITE_TAC[orbit_map; IN_ELIM_THM]);;

let IN_ORBIT_MAP_REFL = prove
 (`!f:A->A x:A. x IN orbit_map f x`,
  REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN MESON_TAC[ITER]);;

let ITER_IN_ORBIT = prove
 (`!f:A->A n x. ITER n f x IN orbit_map f x`,
  REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN MESON_TAC[]);;

let ORBIT_MAP_STEP = prove
 (`!f:A->A x y. y IN orbit_map f x ==> f y IN orbit_map f x`,
  REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `SUC n` THEN
  ASM_REWRITE_TAC[ITER]);;

let ORBIT_MAP_SUCC = prove
 (`!f (x:A) y. y IN orbit_map f (f x) ==> y IN orbit_map f x`,
  REWRITE_TAC[ORBIT_MAP_ITER] THEN MESON_TAC[ITER_ALT]);;

let ORBIT_MAP_TRANS_GEN = prove
 (`!(g:A->A) x y z.
     y IN orbit_map g x /\ z IN orbit_map g y ==> z IN orbit_map g x`,
  REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN MESON_TAC[ITER_ADD]);;

let ORBIT_FIXED = prove
 (`!(f:A->A) z. f z = z ==> orbit_map f z = {z}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[orbit_map; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  ASM_MESON_TAC[ITER_FIXPOINT; ITER]);;

let ORBIT_SUBSET = prove
 (`!(f:A->A) s x. f permutes s /\ x IN s ==> orbit_map f x SUBSET s`,
  REWRITE_TAC[orbit_map; SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ITER; PERMUTES_IN_IMAGE]);;

let ORBIT_FINITE = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
                  ==> FINITE(orbit_map f x)`,
  MESON_TAC[ORBIT_SUBSET; FINITE_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* The hypermap type: a hypermap packages (D, e, n, f) where D is finite,    *)
(* e, n and f permute D, and e o n o f = I.                                  *)
(* ------------------------------------------------------------------------- *)

let hypermap_pred = new_definition
 `hypermap_pred (H:(A->bool)#(A->A)#(A->A)#(A->A)) <=>
  FINITE(FST H) /\
  FST(SND H) permutes FST H /\
  FST(SND(SND H)) permutes FST H /\
  SND(SND(SND H)) permutes FST H /\
  FST(SND H) o FST(SND(SND H)) o SND(SND(SND H)) = I`;;

let HYPERMAP_EXISTS = prove
 (`?H:(A->bool)#(A->A)#(A->A)#(A->A). hypermap_pred H`,
  EXISTS_TAC `({},I,I,I):(A->bool)#(A->A)#(A->A)#(A->A)` THEN
  REWRITE_TAC[hypermap_pred; FST; SND; FINITE_EMPTY; PERMUTES_I; I_O_ID]);;

let hypermap_tybij = new_type_definition
  "hypermap" ("hypermap","tuple_hypermap") HYPERMAP_EXISTS;;

(* Accessor functions                                                        *)

let dart = new_definition
  `dart (H:(A)hypermap) = FST(tuple_hypermap H)`;;

let edge_map = new_definition
  `edge_map (H:(A)hypermap) = FST(SND(tuple_hypermap H))`;;

let node_map = new_definition
  `node_map (H:(A)hypermap) = FST(SND(SND(tuple_hypermap H)))`;;

let face_map = new_definition
  `face_map (H:(A)hypermap) = SND(SND(SND(tuple_hypermap H)))`;;

(* The predicate holds for any hypermap                                      *)

let HYPERMAP_PRED = prove
 (`!H:(A)hypermap. hypermap_pred(tuple_hypermap H)`,
  GEN_TAC THEN
  REWRITE_TAC[CONJUNCT2 hypermap_tybij] THEN
  REWRITE_TAC[CONJUNCT1 hypermap_tybij]);;

(* Master hypermap lemma                                                     *)

let HYPERMAP_LEMMA = prove
 (`!H:(A)hypermap.
     FINITE(dart H) /\
     edge_map H permutes dart H /\
     node_map H permutes dart H /\
     face_map H permutes dart H /\
     edge_map H o node_map H o face_map H = I`,
  GEN_TAC THEN
  MP_TAC(SPEC `H:(A)hypermap` HYPERMAP_PRED) THEN
  REWRITE_TAC[hypermap_pred; dart; edge_map; node_map; face_map]);;

(* Individual components of HYPERMAP_LEMMA                                   *)

let FINITE_DART = prove
 (`!H:(A)hypermap. FINITE(dart H)`,
  MESON_TAC[HYPERMAP_LEMMA]);;

let EDGE_MAP_PERMUTES = prove
 (`!H:(A)hypermap. edge_map H permutes dart H`,
  MESON_TAC[HYPERMAP_LEMMA]);;

let NODE_MAP_PERMUTES = prove
 (`!H:(A)hypermap. node_map H permutes dart H`,
  MESON_TAC[HYPERMAP_LEMMA]);;

let FACE_MAP_PERMUTES = prove
 (`!H:(A)hypermap. face_map H permutes dart H`,
  MESON_TAC[HYPERMAP_LEMMA]);;

let ENF_I = prove
 (`!H:(A)hypermap. edge_map H o node_map H o face_map H = I`,
  MESON_TAC[HYPERMAP_LEMMA]);;

(* Injectivity lemmas                                                        *)

let EDGEI = prove
 (`!H:(A)hypermap x y. edge_map H x = edge_map H y ==> x = y`,
  MESON_TAC[PERMUTES_INJECTIVE; EDGE_MAP_PERMUTES]);;

let NODEI = prove
 (`!H:(A)hypermap x y. node_map H x = node_map H y ==> x = y`,
  MESON_TAC[PERMUTES_INJECTIVE; NODE_MAP_PERMUTES]);;

let FACEI = prove
 (`!H:(A)hypermap x y. face_map H x = face_map H y ==> x = y`,
  MESON_TAC[PERMUTES_INJECTIVE; FACE_MAP_PERMUTES]);;

let HYPERMAP_INJ_EQ = prove
 (`!(G:(A)hypermap) a b.
     (edge_map G a = edge_map G b <=> a = b) /\
     (node_map G a = node_map G b <=> a = b) /\
     (face_map G a = face_map G b <=> a = b)`,
  MESON_TAC[EDGEI; NODEI; FACEI]);;

(* Cyclic composition identities                                             *)

let NFE_I = prove
 (`!H:(A)hypermap. node_map H o face_map H o edge_map H = I`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC EDGEI THEN EXISTS_TAC `H:(A)hypermap` THEN
  MP_TAC(SPEC `H:(A)hypermap` ENF_I) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN SIMP_TAC[]);;

let FEN_I = prove
 (`!H:(A)hypermap. face_map H o edge_map H o node_map H = I`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC NODEI THEN EXISTS_TAC `H:(A)hypermap` THEN
  MP_TAC(SPEC `H:(A)hypermap` NFE_I) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN SIMP_TAC[]);;

(* Cancellation lemmas (named following Gonthier)                            *)

let edgeK = REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] NFE_I;;
(* |- !H x. node_map H (face_map H (edge_map H x)) = x                       *)

let nodeK = REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] FEN_I;;
(* |- !H x. face_map H (edge_map H (node_map H x)) = x                       *)

let faceK = REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] ENF_I;;
(* |- !H x. edge_map H (node_map H (face_map H x)) = x                       *)

(* Inverse relationships                                                     *)

let EDGE_MAP_INVERSE = prove
 (`!H:(A)hypermap. inverse(edge_map H) = node_map H o face_map H`,
  GEN_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REWRITE_TAC[ENF_I; GSYM o_ASSOC; NFE_I]);;

let NODE_MAP_INVERSE = prove
 (`!H:(A)hypermap. inverse(node_map H) = face_map H o edge_map H`,
  GEN_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REWRITE_TAC[NFE_I; GSYM o_ASSOC; FEN_I]);;

let FACE_MAP_INVERSE = prove
 (`!H:(A)hypermap. inverse(face_map H) = edge_map H o node_map H`,
  GEN_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REWRITE_TAC[FEN_I; GSYM o_ASSOC; ENF_I]);;

(* The three maps preserve the dart set and fix every other point.           *)

let EDGE_MAP_IN_DART = prove
 (`!H:(A)hypermap x. x IN dart H ==> edge_map H x IN dart H`,
  MESON_TAC[EDGE_MAP_PERMUTES; PERMUTES_IN_IMAGE]);;

let NODE_MAP_IN_DART = prove
 (`!H:(A)hypermap x. x IN dart H ==> node_map H x IN dart H`,
  MESON_TAC[NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE]);;

let FACE_MAP_IN_DART = prove
 (`!H:(A)hypermap x. x IN dart H ==> face_map H x IN dart H`,
  MESON_TAC[FACE_MAP_PERMUTES; PERMUTES_IN_IMAGE]);;

let MAPS_IN_DART = prove
 (`!(H:(A)hypermap) x. x IN dart H
    ==> edge_map H x IN dart H /\ node_map H x IN dart H /\
        face_map H x IN dart H`,
  SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART]);;

let MAPS_OUTSIDE_DART = prove
 (`!(H:(A)hypermap) x. ~(x IN dart H)
    ==> edge_map H x = x /\ node_map H x = x /\ face_map H x = x`,
  MESON_TAC[permutes; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
            FACE_MAP_PERMUTES]);;

(* ------------------------------------------------------------------------- *)
(* Edge, node, face orbits and equivalence relations                         *)
(* ------------------------------------------------------------------------- *)

let edge = new_definition
  `edge (H:(A)hypermap) x = orbit_map (edge_map H) x`;;

let node = new_definition
  `node (H:(A)hypermap) x = orbit_map (node_map H) x`;;

let face = new_definition
  `face (H:(A)hypermap) x = orbit_map (face_map H) x`;;

let cnode = new_definition
  `cnode (H:(A)hypermap) x y <=> y IN node H x`;;

let cface = new_definition
  `cface (H:(A)hypermap) x y <=> y IN face H x`;;

(* ------------------------------------------------------------------------- *)
(* Sets of orbits and counting                                               *)
(* ------------------------------------------------------------------------- *)

let set_of_orbits = new_definition
  `set_of_orbits (s:A->bool) (f:A->A) = {orbit_map f x | x IN s}`;;

let edge_set = new_definition
  `edge_set (H:(A)hypermap) = set_of_orbits (dart H) (edge_map H)`;;

let node_set = new_definition
  `node_set (H:(A)hypermap) = set_of_orbits (dart H) (node_map H)`;;

let face_set = new_definition
  `face_set (H:(A)hypermap) = set_of_orbits (dart H) (face_map H)`;;

let number_of_edges = new_definition
  `number_of_edges (H:(A)hypermap) = CARD(edge_set H)`;;

let number_of_nodes = new_definition
  `number_of_nodes (H:(A)hypermap) = CARD(node_set H)`;;

let number_of_faces = new_definition
  `number_of_faces (H:(A)hypermap) = CARD(face_set H)`;;

(* ------------------------------------------------------------------------- *)
(* Connectivity                                                              *)
(* ------------------------------------------------------------------------- *)

let glink = new_definition
  `glink (H:(A)hypermap) x y <=>
     y = edge_map H x \/ y = node_map H x \/ y = face_map H x`;;

let gcomp = new_definition
  `gcomp (H:(A)hypermap) x y <=>
   ?n p. p 0 = x /\ p n = y /\
         (!i. i < n ==> glink H (p i) (p (i+1)))`;;

let connected_hypermap = new_definition
  `connected_hypermap (H:(A)hypermap) <=>
   !x y. x IN dart H /\ y IN dart H ==> gcomp H x y`;;

let component = new_definition
  `component (H:(A)hypermap) x = {y:A | y IN dart H /\ gcomp H x y}`;;

let set_of_components = new_definition
  `set_of_components (H:(A)hypermap) =
   {component H (x:A) | x | x IN dart H}`;;

let number_of_components = new_definition
  `number_of_components (H:(A)hypermap) =
   CARD(set_of_components H:(A->bool)->bool)`;;

(* ------------------------------------------------------------------------- *)
(* Genus and planarity                                                       *)
(* ------------------------------------------------------------------------- *)

let euler_lhs = new_definition
  `euler_lhs (H:(A)hypermap) =
   2 * number_of_components H + CARD(dart H)`;;

let euler_rhs = new_definition
  `euler_rhs (H:(A)hypermap) =
   number_of_edges H + number_of_nodes H + number_of_faces H`;;

let genus = new_definition
  `genus (H:(A)hypermap) = (euler_lhs H - euler_rhs H) DIV 2`;;

let planar_hypermap = new_definition
  `planar_hypermap (H:(A)hypermap) <=> genus H = 0`;;

(* ------------------------------------------------------------------------- *)
(* clink: combined link relation for contours                                *)
(* ------------------------------------------------------------------------- *)

let clink = new_definition
  `clink (H:(A)hypermap) x y <=>
   x = node_map H y \/ face_map H x = y`;;

(* ------------------------------------------------------------------------- *)
(* Constructing hypermaps from valid tuples                                  *)
(* ------------------------------------------------------------------------- *)

let mk_hypermap = new_definition
  `mk_hypermap (d:A->bool,e:A->A,n:A->A,f:A->A) =
   hypermap (d, e, n, f)`;;

let MK_HYPERMAP_COMPONENTS = prove
 (`!d:A->bool e n f.
     hypermap_pred (d,e,n,f)
     ==> dart(mk_hypermap(d,e,n,f)) = d /\
         edge_map(mk_hypermap(d,e,n,f)) = e /\
         node_map(mk_hypermap(d,e,n,f)) = n /\
         face_map(mk_hypermap(d,e,n,f)) = f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mk_hypermap; dart; edge_map; node_map; face_map] THEN
  REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN `tuple_hypermap(hypermap(d:A->bool,e,n,f)) = (d,e,n,f)`
    (fun th -> REWRITE_TAC[th; FST; SND]) THEN
  REWRITE_TAC[GSYM(CONJUNCT2 hypermap_tybij)] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Derived maps: permN, permF                                                *)
(* ------------------------------------------------------------------------- *)

let HYPERMAP_PERMN_PRED = prove
 (`!H:(A)hypermap. hypermap_pred (dart H, node_map H, face_map H, edge_map H)`,
  REWRITE_TAC[hypermap_pred; HYPERMAP_LEMMA; NFE_I]);;

let HYPERMAP_PERMF_PRED = prove
 (`!H:(A)hypermap. hypermap_pred (dart H, face_map H, edge_map H, node_map H)`,
  REWRITE_TAC[hypermap_pred; HYPERMAP_LEMMA; FEN_I]);;

let permN = new_definition
  `permN (H:(A)hypermap) =
   mk_hypermap(dart H, node_map H, face_map H, edge_map H)`;;

let permF = new_definition
  `permF (H:(A)hypermap) =
   mk_hypermap(dart H, face_map H, edge_map H, node_map H)`;;

let PERMN_COMPONENTS = prove
 (`!H:(A)hypermap.
     dart(permN H) = dart H /\
     edge_map(permN H) = node_map H /\
     node_map(permN H) = face_map H /\
     face_map(permN H) = edge_map H`,
  GEN_TAC THEN REWRITE_TAC[permN] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  REWRITE_TAC[HYPERMAP_PERMN_PRED]);;

let PERMF_COMPONENTS = prove
 (`!H:(A)hypermap.
     dart(permF H) = dart H /\
     edge_map(permF H) = face_map H /\
     node_map(permF H) = edge_map H /\
     face_map(permF H) = node_map H`,
  GEN_TAC THEN REWRITE_TAC[permF] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  REWRITE_TAC[HYPERMAP_PERMF_PRED]);;

(* ------------------------------------------------------------------------- *)
(* Dual hypermap: e' = n o f, n' = e o n, f' = f o e (inverses of e, f, n    *)
(* respectively)                                                             *)
(* ------------------------------------------------------------------------- *)

let DUAL_COMPOSE_I = prove
 (`!H:(A)hypermap.
     (node_map H o face_map H) o (edge_map H o node_map H) o
     (face_map H o edge_map H) = I`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  X_GEN_TAC `x:A` THEN
  SUBGOAL_THEN `face_map H (edge_map H (node_map H (face_map H
    (edge_map H (x:A))))) = face_map H (edge_map H (x:A))`
    (fun th -> REWRITE_TAC[th; edgeK]) THEN
  REWRITE_TAC[nodeK]);;

let HYPERMAP_DUAL_PRED = prove
 (`!H:(A)hypermap. hypermap_pred
    (dart H, node_map H o face_map H,
     edge_map H o node_map H, face_map H o edge_map H)`,
  REWRITE_TAC[hypermap_pred; DUAL_COMPOSE_I] THEN
  SIMP_TAC[PERMUTES_COMPOSE; HYPERMAP_LEMMA]);;

let dual = new_definition
 `dual (H:(A)hypermap) =
  mk_hypermap(dart H, node_map H o face_map H,
    edge_map H o node_map H, face_map H o edge_map H)`;;

let DUAL_COMPONENTS = prove
 (`!H:(A)hypermap.
     dart(dual H) = dart H /\
     edge_map(dual H) = node_map H o face_map H /\
     node_map(dual H) = edge_map H o node_map H /\
     face_map(dual H) = face_map H o edge_map H`,
  GEN_TAC THEN REWRITE_TAC[dual] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  REWRITE_TAC[HYPERMAP_DUAL_PRED]);;

(* ------------------------------------------------------------------------- *)
(* Mirror hypermap: e' = f o n, n' = f o e, f' = e o n                       *)
(* ------------------------------------------------------------------------- *)

let MIRROR_COMPOSE_I = prove
 (`!H:(A)hypermap.
     (face_map H o node_map H) o (face_map H o edge_map H) o
     (edge_map H o node_map H) = I`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  X_GEN_TAC `x:A` THEN
  SUBGOAL_THEN `face_map H (node_map H (face_map H (edge_map H
    (edge_map H (node_map H (x:A))))) ) =
    face_map H (edge_map H (node_map H x))`
    (fun th -> REWRITE_TAC[th; nodeK]) THEN
  AP_TERM_TAC THEN REWRITE_TAC[edgeK]);;

let HYPERMAP_MIRROR_PRED = prove
 (`!H:(A)hypermap. hypermap_pred
    (dart H, face_map H o node_map H,
     face_map H o edge_map H, edge_map H o node_map H)`,
  REWRITE_TAC[hypermap_pred; MIRROR_COMPOSE_I] THEN
  SIMP_TAC[PERMUTES_COMPOSE; HYPERMAP_LEMMA]);;

let mirror = new_definition
 `mirror (H:(A)hypermap) =
  mk_hypermap(dart H, face_map H o node_map H,
    face_map H o edge_map H, edge_map H o node_map H)`;;

let MIRROR_COMPONENTS = prove
 (`!H:(A)hypermap.
     dart(mirror H) = dart H /\
     edge_map(mirror H) = face_map H o node_map H /\
     node_map(mirror H) = face_map H o edge_map H /\
     face_map(mirror H) = edge_map H o node_map H`,
  GEN_TAC THEN REWRITE_TAC[mirror] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  REWRITE_TAC[HYPERMAP_MIRROR_PRED]);;
