(* ========================================================================= *)
(* 4CT/geometry.ml                                                           *)
(*                                                                           *)
(* geometry.v: the geometry of hypermaps.  Orbit sizes and periods, orbits   *)
(* of inverses and conjugates; arity, plain_hypermap, cubic_hypermap,        *)
(* precubic, pentagonal, bridgeless, quasicubic; the face relation cface as  *)
(* an equivalence on all darts and the face-adjacency relations rlink and    *)
(* adj; the list-based notions fband, kernel, insertE, list_path,            *)
(* list_cycle, face_simple, scycle, fproj, srpath, srcycle, rlink_connected, *)
(* chordless; preservation of these by mirror; orbit counting                *)
(* (UNIONS_SET_OF_ORBITS, PLAIN_DART_CARD), components (gcomp,               *)
(* CONNECTED_NCOMP) and the bundled hypotheses (planar_bridgeless,           *)
(* plain_cubic, ..., ucycle_planar_plain_quasicubic).  The file ends with    *)
(* CFACE_TAC, a certified decision procedure for face-connectivity goals     *)
(* used throughout the later files.                                          *)
(* ========================================================================= *)

needs "4CT/hypermap.ml";;
needs "4CT/general.ml";;

(* ========================================================================= *)
(* Orbit size (order of an element under a permutation)                      *)
(* ========================================================================= *)

let orbit_size = new_definition
  `orbit_size (f:A->A) (x:A) = CARD(orbit_map f x)`;;

(* ------------------------------------------------------------------------- *)
(* Orbit size is positive                                                    *)
(* ------------------------------------------------------------------------- *)

let ORBIT_SIZE_POS = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
                   ==> 0 < orbit_size f x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[orbit_size; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  ASM_MESON_TAC[CARD_EQ_0; ORBIT_FINITE; IN_ORBIT_MAP_REFL; NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Orbit as a finite image of {0,...,d-1} when d is the period               *)
(* ------------------------------------------------------------------------- *)

let ORBIT_MAP_PERIOD = prove
 (`!(f:A->A) z d.
     0 < d /\ (!n. ITER n f z = z <=> d divides n)
     ==> orbit_map f z = IMAGE (\i. ITER i f z) {i | i < d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ITER d (f:A->A) z = z` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN SIMP_TAC[NUMBER_RULE `n divides n`]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; ORBIT_MAP_ITER; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THENL
  [DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
   EXISTS_TAC `n MOD d` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ITER_MOD THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[NUMBER_RULE `n divides n`];
    ASM_MESON_TAC[MOD_LT_EQ; ARITH_RULE `0 < d ==> ~(d = 0)`]];
   MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Orbit size equals the period                                              *)
(* ------------------------------------------------------------------------- *)

let ORBIT_SIZE_PERIOD = prove
 (`!(f:A->A) s z d.
     FINITE s /\ f permutes s /\ z IN s /\
     0 < d /\ (!n. ITER n f z = z <=> d divides n)
     ==> orbit_size f z = d`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[orbit_size] THEN
  SUBGOAL_THEN `orbit_map (f:A->A) z = IMAGE (\i. ITER i f z) {i | i < d}`
    SUBST1_TAC THENL
  [MATCH_MP_TAC ORBIT_MAP_PERIOD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `CARD(IMAGE (\i. ITER i (f:A->A) z) {i | i < d}) = CARD {i:num | i < d}`
    SUBST1_TAC THENL
  [MATCH_MP_TAC CARD_IMAGE_INJ THEN
   REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC ORBIT_ITER_DISTINCT THEN
   MAP_EVERY EXISTS_TAC [`f:A->A`; `z:A`; `d:num`] THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`f:A->A`; `s:A->bool`] PERMUTES_INJECTIVE) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[];
   REWRITE_TAC[CARD_NUMSEG_LT]]);;

(* ------------------------------------------------------------------------- *)
(* ITER at orbit_size returns to start                                       *)
(* ------------------------------------------------------------------------- *)

let ITER_ORBIT_SIZE = prove
 (`!(f:A->A) s z.
     FINITE s /\ f permutes s /\ z IN s
     ==> ITER (orbit_size f z) f z = z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:A->A`; `s:A->bool`; `z:A`] ORBIT_PERIOD_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `orbit_size (f:A->A) z = d` SUBST1_TAC THENL
  [MATCH_MP_TAC ORBIT_SIZE_PERIOD THEN
   EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[] THEN SIMP_TAC[NUMBER_RULE `n divides n`]]);;

(* ------------------------------------------------------------------------- *)
(* orbit_size divides any period                                             *)
(* ------------------------------------------------------------------------- *)

let ORBIT_SIZE_DIVIDES = prove
 (`!(f:A->A) s z n.
     FINITE s /\ f permutes s /\ z IN s
     ==> (ITER n f z = z <=> orbit_size f z divides n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:A->A`; `s:A->bool`; `z:A`] ORBIT_PERIOD_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `orbit_size (f:A->A) z = d` SUBST1_TAC THENL
  [MATCH_MP_TAC ORBIT_SIZE_PERIOD THEN
   EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

(* Orbits of size 2 are those of the points moved by f with f (f x) = x.     *)
let ORBIT_SIZE_2 = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
    ==> (orbit_size f x = 2 <=> f (f x) = x /\ ~(f x = x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_SIZE_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  REWRITE_TAC[ITER_1; ITER2] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[DIVIDES_ONE] THEN
  SPEC_TAC(`orbit_size (f:A->A) x`,`d:num`) THEN
  MESON_TAC[DIVIDES_2_NOT_1; TWO_DIV_TWO; ARITH_RULE `~(2 = 1)`]);;

(* ========================================================================= *)
(* Orbit equivalence and orbit equality                                      *)
(* ========================================================================= *)

let ORBIT_MAP_EQ = prove
 (`!(f:A->A) s x y.
     FINITE s /\ f permutes s /\ x IN s /\ y IN orbit_map f x
     ==> orbit_map f y = orbit_map f x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [ORBIT_MAP_ITER]) THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ITER_ORBIT_SIZE) THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`orbit_size (f:A->A) x`,`d:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_REFL] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; ORBIT_MAP_ITER] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THENL
   [EXISTS_TAC `n + m:num` THEN REWRITE_TAC[ITER_ADD];
    EXISTS_TAC `n + m * d` THEN REWRITE_TAC[ITER_ADD] THEN
    SUBGOAL_THEN `(n + m * d) + m = m * SUC d + n` SUBST1_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ASM_SIMP_TAC[ITER_PERIOD]]]);;

let ORBIT_MAP_IN = prove
 (`!(f:A->A) s x y.
     FINITE s /\ f permutes s /\ x IN s /\ y IN orbit_map f x ==> y IN s`,
  MESON_TAC[ORBIT_SUBSET; SUBSET]);;

let ORBIT_MAP_SYM = prove
 (`!(f:A->A) s x y.
     FINITE s /\ f permutes s /\ x IN s /\ y IN orbit_map f x
     ==> x IN orbit_map f y`,
  MESON_TAC[ORBIT_MAP_EQ; IN_ORBIT_MAP_REFL]);;

let ORBIT_MAP_TRANS = prove
 (`!(f:A->A) s x y z.
     FINITE s /\ f permutes s /\ x IN s /\
     y IN orbit_map f x /\ z IN orbit_map f y
     ==> z IN orbit_map f x`,
  MESON_TAC[ORBIT_MAP_TRANS_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Orbits of the inverse and of a conjugate permutation (the inverse         *)
(* of x lies on the orbit of x, so orbits and orbit sizes agree).            *)
(* ------------------------------------------------------------------------- *)

let INVERSE_IN_ORBIT = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
    ==> inverse f x IN orbit_map f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inverse(f:A->A) x = ITER (orbit_size f x - 1) f x`
   (fun th -> REWRITE_TAC[th; ITER_IN_ORBIT]) THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ITER_ORBIT_SIZE) THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`orbit_size (f:A->A) x`,`d:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_REFL; SUC_SUB1; ITER] THEN
  DISCH_TAC THEN DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  ASM_MESON_TAC[PERMUTES_INVERSES]);;

let ORBIT_MAP_INVERSE_STEP = prove
 (`!(f:A->A) s x y. FINITE s /\ f permutes s /\ x IN s /\
    y IN orbit_map f x
    ==> inverse f y IN orbit_map f x`,
  MESON_TAC[ORBIT_MAP_EQ; INVERSE_IN_ORBIT; ORBIT_MAP_IN]);;

let ORBIT_MAP_INVERSE_SUBSET = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
    ==> orbit_map (inverse f) x SUBSET orbit_map f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; ORBIT_MAP_ITER] THEN
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
   [MESON_TAC[ITER]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ORBIT_MAP_ITER] THEN
  MATCH_MP_TAC ORBIT_MAP_INVERSE_STEP THEN ASM_MESON_TAC[ORBIT_MAP_ITER]);;

let ORBIT_MAP_INVERSE = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
    ==> orbit_map (inverse f) x = orbit_map f x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_INVERSE_SUBSET THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`inverse(f:A->A)`; `s:A->bool`; `x:A`]
      ORBIT_MAP_INVERSE_SUBSET) THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP PERMUTES_INVERSE_INVERSE th]) THEN
    ASM_SIMP_TAC[PERMUTES_INVERSE]]);;

let ORBIT_SIZE_INVERSE = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
    ==> orbit_size (inverse f) x = orbit_size f x`,
  REWRITE_TAC[orbit_size] THEN MESON_TAC[ORBIT_MAP_INVERSE]);;

let ORBIT_SIZE_CONJUGATE = prove
 (`!(f:A->A) (h:A->A) s x.
    FINITE s /\ f permutes s /\ h permutes s /\ x IN s
    ==> orbit_size (h o f o inverse h) (h x) = orbit_size f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!n. ITER n ((h:A->A) o (f:A->A) o inverse h) (h x) = h(ITER n f x)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->A`; `s:A->bool`] PERMUTES_INVERSES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[orbit_size] THEN
  SUBGOAL_THEN `orbit_map ((h:A->A) o (f:A->A) o inverse h) (h x) =
                IMAGE h (orbit_map f x)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; ORBIT_MAP_ITER; IN_IMAGE] THEN MESON_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_MESON_TAC[ORBIT_FINITE; PERMUTES_INJECTIVE]]);;

(* ========================================================================= *)
(* Geometry: arity, plain, cubic, bridgeless, etc. Following Gonthier's      *)
(* geometry.v                                                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Arity = face order (size of face orbit)                                   *)
(* ------------------------------------------------------------------------- *)

let arity = new_definition
  `arity (H:(A)hypermap) x = orbit_size (face_map H) x`;;

(* ------------------------------------------------------------------------- *)
(* Bridgeless: no face contains both ends of an edge.                        *)
(* ------------------------------------------------------------------------- *)

let bridgeless = new_definition
  `bridgeless (H:(A)hypermap) <=>
   !x. x IN dart H ==> ~(cface H x (edge_map H x))`;;

(* ------------------------------------------------------------------------- *)
(* Plain: every edge orbit has size 2 (edge_map is an involution)            *)
(* ------------------------------------------------------------------------- *)

let plain_hypermap = new_definition
  `plain_hypermap (H:(A)hypermap) <=>
   !x. x IN dart H ==> orbit_size (edge_map H) x = 2`;;

(* ------------------------------------------------------------------------- *)
(* Cubic: every node orbit has size 3                                        *)
(* ------------------------------------------------------------------------- *)

let cubic_hypermap = new_definition
  `cubic_hypermap (H:(A)hypermap) <=>
   !x. x IN dart H ==> orbit_size (node_map H) x = 3`;;

(* ------------------------------------------------------------------------- *)
(* Precubic: every node orbit has size <= 3                                  *)
(* ------------------------------------------------------------------------- *)

let precubic = new_definition
  `precubic (H:(A)hypermap) <=>
   !x. x IN dart H ==> orbit_size (node_map H) x <= 3`;;

(* ------------------------------------------------------------------------- *)
(* Pentagonal: every face has arity > 4 (size >= 5)                          *)
(* ------------------------------------------------------------------------- *)

let pentagonal = new_definition
  `pentagonal (H:(A)hypermap) <=>
   !x. x IN dart H ==> 4 < arity H x`;;

(* ------------------------------------------------------------------------- *)
(* Plain and cubic maps: edge o edge = I and node^3 = I on darts, the        *)
(* maps have no fixed points, and n(f(x)) = e(x), n(n(x)) = f(e(x))          *)
(* (Gonthier's plain_eq, cubic_eq, plain_neq, cubic_neq, plain_eq',          *)
(* cubic_eq').                                                               *)
(* ------------------------------------------------------------------------- *)

let PLAIN_EQ = prove
 (`!H:(A)hypermap x.
     plain_hypermap H /\ x IN dart H
     ==> edge_map H (edge_map H x) = x`,
  REWRITE_TAC[plain_hypermap] THEN
  MESON_TAC[ORBIT_SIZE_2; FINITE_DART; EDGE_MAP_PERMUTES]);;

let CUBIC_EQ = prove
 (`!H:(A)hypermap x.
     cubic_hypermap H /\ x IN dart H
     ==> node_map H (node_map H (node_map H x)) = x`,
  REWRITE_TAC[cubic_hypermap] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
    ITER_ORBIT_SIZE) THEN
  ASM_SIMP_TAC[FINITE_DART; NODE_MAP_PERMUTES; ITER3]);;

let PLAIN_NEQ = prove
 (`!H:(A)hypermap x.
     plain_hypermap H /\ x IN dart H ==> ~(edge_map H x = x)`,
  REWRITE_TAC[plain_hypermap] THEN
  MESON_TAC[ORBIT_SIZE_2; FINITE_DART; EDGE_MAP_PERMUTES]);;

let CUBIC_NEQ = prove
 (`!H:(A)hypermap x.
     cubic_hypermap H /\ x IN dart H ==> ~(node_map H x = x)`,
  REWRITE_TAC[cubic_hypermap] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`;
                 `1`] ORBIT_SIZE_DIVIDES) THEN
  ASM_SIMP_TAC[FINITE_DART; NODE_MAP_PERMUTES; ITER_1; DIVIDES_ONE] THEN
  ARITH_TAC);;

let PLAIN_EQ' = prove
 (`!H:(A)hypermap x.
     plain_hypermap H /\ x IN dart H
     ==> node_map H (face_map H x) = edge_map H x`,
  MESON_TAC[PLAIN_EQ; edgeK]);;

let CUBIC_EQ' = prove
 (`!H:(A)hypermap x.
     cubic_hypermap H /\ x IN dart H
     ==> node_map H (node_map H x) = face_map H (edge_map H x)`,
  MESON_TAC[CUBIC_EQ; edgeK; NODEI]);;

(* ------------------------------------------------------------------------- *)
(* Quasicubic: nodes outside ring r have order 3                             *)
(* ------------------------------------------------------------------------- *)

let quasicubic = new_definition
  `quasicubic (H:(A)hypermap) (r:A->bool) <=>
   !x. x IN dart H /\ ~(x IN r) ==> orbit_size (node_map H) x = 3`;;

(* ------------------------------------------------------------------------- *)
(* rlink: ring link relation (face adjacency through an edge)                *)
(* ------------------------------------------------------------------------- *)

let rlink = new_definition
  `rlink (H:(A)hypermap) x y <=> cface H (edge_map H x) y`;;

(* ------------------------------------------------------------------------- *)
(* adj: face adjacency (two faces share a node-link)                         *)
(* ------------------------------------------------------------------------- *)

let adj = new_definition
  `adj (H:(A)hypermap) x y <=> ?z. z IN face H x /\ rlink H z y`;;

(* ========================================================================= *)
(* Face orbits and the face relation cface                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Face orbits consist of darts and are the classes of cface.                *)
(* ------------------------------------------------------------------------- *)

let FACE_IN_DART = prove
 (`!H:(A)hypermap x y. x IN dart H /\ y IN face H x ==> y IN dart H`,
  REWRITE_TAC[face] THEN
  MESON_TAC[ORBIT_MAP_IN; FINITE_DART; FACE_MAP_PERMUTES]);;

let FACE_EQ = prove
 (`!H:(A)hypermap x y. x IN dart H /\ y IN face H x
     ==> face H y = face H x`,
  REWRITE_TAC[face] THEN
  MESON_TAC[ORBIT_MAP_EQ; FINITE_DART; FACE_MAP_PERMUTES]);;

let SELF_IN_FACE = prove
 (`!H:(A)hypermap x. x IN face H x`,
  REWRITE_TAC[face; IN_ORBIT_MAP_REFL]);;

let FACE_MAP_IN_FACE = prove
 (`!H:(A)hypermap x. face_map H x IN face H x`,
  REWRITE_TAC[face; ORBIT_MAP_ITER] THEN
  MESON_TAC[num_CONV `1`; ITER]);;

(* ------------------------------------------------------------------------- *)
(* cface is an equivalence relation on all darts (face_map H permutes        *)
(* dart H and fixes everything else), containing face_map, inverse           *)
(* face_map, its iterates and edge o node.  These are the lemmas that        *)
(* CFACE_TAC (at the end of the file) composes.                              *)
(* ------------------------------------------------------------------------- *)

let CFACE_REFL = prove
 (`!(H:(A)hypermap) a. cface H a a`,
  REWRITE_TAC[cface; face; IN_ORBIT_MAP_REFL]);;

let CFT_TRANS = prove
 (`!(H:(A)hypermap) a b c. cface H a b /\ cface H b c ==> cface H a c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) (X_CHOOSE_TAC `m:num`))
  THEN EXISTS_TAC `m + n:num` THEN ASM_REWRITE_TAC[ITER_ADD]);;

let CFACE_SYM_GEN = prove
 (`!H x (y:A). cface H x y ==> cface H y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cface; face] THEN
  ASM_CASES_TAC `(x:A) IN dart H` THENL
   [ASM_MESON_TAC[ORBIT_MAP_SYM; FINITE_DART; FACE_MAP_PERMUTES];
    ASM_MESON_TAC[ORBIT_FIXED; FACE_MAP_PERMUTES; PERMUTES_FIX_OUTSIDE;
                  IN_SING; IN_ORBIT_MAP_REFL]]);;

let CFACE_SYM = prove
 (`!H x (y:A). x IN dart H /\ cface H x y ==> cface H y x`,
  MESON_TAC[CFACE_SYM_GEN]);;

let CFACE_TRANS = prove
 (`!H x y (z:A). x IN dart H /\ cface H x y
     ==> (cface H y z <=> cface H x z)`,
  MESON_TAC[CFT_TRANS; CFACE_SYM_GEN]);;

let CFT_EQ = prove
 (`!(H:(A)hypermap) a b. a = b ==> cface H a b`,
  MESON_TAC[CFACE_REFL]);;

let CFT_FACE = prove
 (`!(H:(A)hypermap) a. cface H a (face_map H a)`,
  REWRITE_TAC[cface; FACE_MAP_IN_FACE]);;

let CFT_EDGE_NODE = prove
 (`!(H:(A)hypermap) a. cface H (edge_map H (node_map H a)) a`,
  MESON_TAC[CFT_FACE; nodeK]);;

let CFT_ITER = prove
 (`!(H:(A)hypermap) n a. cface H a (ITER n (face_map H) a)`,
  REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN MESON_TAC[]);;

let CFT_INV = prove
 (`!(H:(A)hypermap) a. cface H (inverse (face_map H) a) a`,
  MESON_TAC[CFT_FACE; PERMUTES_INVERSES; FACE_MAP_PERMUTES]);;

let CFT_DART = prove
 (`!(H:(A)hypermap) a b. a IN dart H /\ cface H a b ==> b IN dart H`,
  REWRITE_TAC[cface] THEN MESON_TAC[FACE_IN_DART]);;

let CFACE_FACE_STEP = prove
 (`!H:(A)hypermap x y.
     x IN dart H /\ y IN dart H
     ==> (cface H x (face_map H y) <=> cface H x y)`,
  MESON_TAC[CFT_FACE; CFT_TRANS; CFACE_SYM_GEN]);;

(* ========================================================================= *)
(* Arity and face iteration                                                  *)
(* ========================================================================= *)

let ARITY_CFACE = prove
 (`!H:(A)hypermap x y. x IN dart H /\ cface H x y ==> arity H y = arity H x`,
  REWRITE_TAC[arity; cface; face; orbit_size] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ORBIT_MAP_EQ THEN
  EXISTS_TAC `dart(H:(A)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[ORBIT_MAP_IN; FINITE_DART; FACE_MAP_PERMUTES]);;

let ITER_FACE_ARITY = prove
 (`!H:(A)hypermap x.
     x IN dart H ==> ITER (arity H x) (face_map H) x = x`,
  REWRITE_TAC[arity] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ITER_ORBIT_SIZE THEN
  EXISTS_TAC `dart(H:(A)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES]);;

(* ========================================================================= *)
(* Adjacency lemmas                                                          *)
(* ========================================================================= *)

let RLINK_ADJ = prove
 (`!H:(A)hypermap x y. x IN dart H /\ rlink H x y ==> adj H x y`,
  REWRITE_TAC[adj] THEN MESON_TAC[SELF_IN_FACE]);;

let ADJ_EDGE = prove
 (`!H:(A)hypermap x. x IN dart H ==> adj H x (edge_map H x)`,
  REWRITE_TAC[adj; rlink] THEN MESON_TAC[SELF_IN_FACE; CFACE_REFL]);;

let ADJ_NODE = prove
 (`!H:(A)hypermap x. x IN dart H ==> adj H (node_map H x) x`,
  REWRITE_TAC[adj; rlink] THEN
  MESON_TAC[CFACE_REFL; cface; CFT_EDGE_NODE]);;

(* ------------------------------------------------------------------------- *)
(* ADJ_SYM: adjacency is symmetric in plain maps (Gonthier's adjC)           *)
(* ------------------------------------------------------------------------- *)

let ADJ_SYM = prove
 (`!H:(A)hypermap x y.
     plain_hypermap H /\ x IN dart H /\ y IN dart H /\ adj H x y
     ==> adj H y x`,
  REWRITE_TAC[adj; rlink; GSYM cface] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `edge_map H (z:A)` THEN
  SUBGOAL_THEN `edge_map H (edge_map H z) = (z:A)` SUBST1_TAC THENL
   [ASM_MESON_TAC[PLAIN_EQ; CFT_DART]; ASM_MESON_TAC[CFACE_SYM_GEN]]);;

(* ------------------------------------------------------------------------- *)
(* Bridgeless: simpler restatement                                           *)
(* ------------------------------------------------------------------------- *)

let BRIDGELESS_CFACE = prove
 (`!H:(A)hypermap x.
     bridgeless H /\ x IN dart H ==> ~(cface H x (edge_map H x))`,
  REWRITE_TAC[bridgeless] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* ADJ_NO_CFACE: adjacent faces are distinct in bridgeless maps              *)
(* ------------------------------------------------------------------------- *)

let ADJ_NO_CFACE = prove
 (`!H:(A)hypermap x y.
     bridgeless H /\ x IN dart H /\ adj H x y ==> ~(cface H x y)`,
  REWRITE_TAC[adj; rlink; bridgeless; GSYM cface] THEN
  MESON_TAC[CFT_DART; CFT_TRANS; CFACE_SYM_GEN]);;

(* ========================================================================= *)
(* Arity, cubic and quasicubic facts; face-invariance of rlink and adj       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Arity is always positive                                                  *)
(* ------------------------------------------------------------------------- *)

let ARITY_POS = prove
 (`!H:(A)hypermap x. x IN dart H ==> 0 < arity H x`,
  REWRITE_TAC[arity] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ORBIT_SIZE_POS THEN
  EXISTS_TAC `dart(H:(A)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES]);;

(* ------------------------------------------------------------------------- *)
(* Arity is face-invariant                                                   *)
(* ------------------------------------------------------------------------- *)

let ARITY_FACE = prove
 (`!H:(A)hypermap x.
     x IN dart H ==> arity H (face_map H x) = arity H x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARITY_CFACE THEN
  ASM_REWRITE_TAC[cface; face; FACE_MAP_IN_FACE]);;

let ARITY_ITER_FACE = prove
 (`!H:(A)hypermap x n.
     x IN dart H ==> arity H (ITER n (face_map H) x) = arity H x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARITY_CFACE THEN
  ASM_REWRITE_TAC[cface; face; ITER_IN_ORBIT]);;

(* ------------------------------------------------------------------------- *)
(* Cubic implies precubic                                                    *)
(* ------------------------------------------------------------------------- *)

let CUBIC_PRECUBIC = prove
 (`!H:(A)hypermap. cubic_hypermap H ==> precubic H`,
  REWRITE_TAC[cubic_hypermap; precubic] THEN
  MESON_TAC[ARITH_RULE `x = 3 ==> x <= 3`]);;

(* ------------------------------------------------------------------------- *)
(* Quasicubic: node^3 = id outside the ring                                  *)
(* ------------------------------------------------------------------------- *)

let QUASICUBIC_EQ = prove
 (`!H:(A)hypermap r x.
     quasicubic H r /\ x IN dart H /\ ~(x IN r)
     ==> node_map H (node_map H (node_map H x)) = x`,
  REWRITE_TAC[quasicubic] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
    ITER_ORBIT_SIZE) THEN
  ASM_SIMP_TAC[FINITE_DART; NODE_MAP_PERMUTES; ITER3]);;

(* ------------------------------------------------------------------------- *)
(* rlink is face-invariant on the right                                      *)
(* ------------------------------------------------------------------------- *)

let RLINK_CFACE = prove
 (`!H:(A)hypermap x y1 y2.
     x IN dart H /\ y1 IN dart H /\ cface H y1 y2
     ==> (rlink H x y1 <=> rlink H x y2)`,
  REWRITE_TAC[rlink] THEN MESON_TAC[CFT_TRANS; CFACE_SYM_GEN]);;

(* ------------------------------------------------------------------------- *)
(* adj is face-invariant on left and right                                   *)
(* ------------------------------------------------------------------------- *)

let ADJ_CFACE_L = prove
 (`!H:(A)hypermap x1 x2 y.
     x1 IN dart H /\ cface H x1 x2
     ==> (adj H x1 y <=> adj H x2 y)`,
  REWRITE_TAC[adj; GSYM cface] THEN MESON_TAC[CFT_TRANS; CFACE_SYM_GEN]);;

let ADJ_CFACE = prove
 (`!H:(A)hypermap x y1 y2.
     x IN dart H /\ y1 IN dart H /\ cface H y1 y2
     ==> (adj H x y1 <=> adj H x y2)`,
  REWRITE_TAC[adj; rlink] THEN MESON_TAC[CFT_TRANS; CFACE_SYM_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Contrapositive: non-adjacent + adjacent implies different faces           *)
(* ------------------------------------------------------------------------- *)

let NO_ADJ_ADJ = prove
 (`!H:(A)hypermap x y1 y2.
     x IN dart H /\ y1 IN dart H /\ ~(adj H x y1) /\ adj H x y2
     ==> ~(cface H y1 y2)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~adj(H:(A)hypermap) x y1` THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`H:(A)hypermap`; `x:A`; `y1:A`; `y2:A`] ADJ_CFACE) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* List-based geometry: fband, kernel, paths, simple, insertE.  These        *)
(* parallel Gonthier's seq-based definitions using HOL Light lists.          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* fband: face band of a list (the set of darts face-connected to p)         *)
(* ------------------------------------------------------------------------- *)

let fband = new_definition
  `fband (H:(A)hypermap) (p:(A)list) (x:A) <=>
   EX (\y. cface H x y) p`;;

(* ------------------------------------------------------------------------- *)
(* kernel: the darts not in the band of p (Gonthier: kernel p = [predC fband *)
(* p] over the finite dart type).                                            *)
(* ------------------------------------------------------------------------- *)

let kernel = new_definition
  `kernel (H:(A)hypermap) (p:(A)list) (x:A) <=>
   x IN dart H /\ ~fband H p x`;;

(* ------------------------------------------------------------------------- *)
(* insertE: edge closure of a list (interleave each x with edge_map x)       *)
(* ------------------------------------------------------------------------- *)

let insertE = new_definition
  `insertE (H:(A)hypermap) (p:(A)list) =
   ITLIST (\x acc. CONS x (CONS (edge_map H x) acc)) p []`;;

let INSERTE_CLAUSES = prove
 (`(insertE (H:(A)hypermap) [] = []) /\
   (!x p. insertE H (CONS x p) =
          CONS x (CONS (edge_map H x) (insertE H p)))`,
  REWRITE_TAC[insertE; ITLIST]);;

(* ------------------------------------------------------------------------- *)
(* list_path: relational path along a list                                   *)
(* ------------------------------------------------------------------------- *)

let list_path = define
  `(list_path (e:A->A->bool) (x:A) [] <=> T) /\
   (list_path e x (CONS y p) <=> e x y /\ list_path e y p)`;;

(* ------------------------------------------------------------------------- *)
(* list_cycle: cyclic path (last element links back to first)                *)
(* ------------------------------------------------------------------------- *)

let list_cycle = new_definition
  `list_cycle (e:A->A->bool) (p:(A)list) <=>
   ~(p = []) /\ list_path e (LAST p) p`;;

(* ------------------------------------------------------------------------- *)
(* face_simple: face-simplicity (no two elements in same face)               *)
(* ------------------------------------------------------------------------- *)

let face_simple = define
  `(face_simple (H:(A)hypermap) [] <=> T) /\
   (face_simple H (CONS (x:A) p) <=>
    ~(fband H p x) /\ face_simple H p)`;;

(* ------------------------------------------------------------------------- *)
(* scycle: simple cycle under a relation                                     *)
(* ------------------------------------------------------------------------- *)

let scycle = new_definition
  `scycle (H:(A)hypermap) (e:A->A->bool) (p:(A)list) <=>
   list_cycle e p /\ face_simple H p`;;

(* ------------------------------------------------------------------------- *)
(* Key lemmas about fband                                                    *)
(* ------------------------------------------------------------------------- *)

(* The biconditional form, used by the surgery and embedding files           *)

let FBAND_MEM_IFF = prove
 (`!(H:(A)hypermap) l z. fband H l z <=> (?y. MEM y l /\ cface H z y)`,
  REWRITE_TAC[fband; GSYM EX_MEM] THEN MESON_TAC[]);;

let FBAND_MEM = prove
 (`!H:(A)hypermap p x. MEM x p ==> fband H p x`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[CFACE_REFL]);;

let FBAND_CFACE = prove
 (`!H:(A)hypermap p x y.
     x IN dart H /\ fband H p x /\ cface H x y ==> fband H p y`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[CFT_TRANS; CFACE_SYM_GEN]);;

let FBAND_NIL = prove
 (`!H (y:A). fband H [] y <=> F`,
  REWRITE_TAC[fband; EX]);;

let FBAND_CONS = prove
 (`!H (x:A) p y. fband H (CONS x p) y <=> cface H y x \/ fband H p y`,
  REWRITE_TAC[fband; EX; DISJ_SYM]);;

let FBAND_APPEND = prove
 (`!H (p1:(A)list) p2 x.
     fband H (APPEND p1 p2) x <=> fband H p1 x \/ fband H p2 x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; FBAND_CONS; FBAND_NIL; DISJ_ASSOC]);;

let FBAND_FACE_MAP_EQ = prove
 (`!H (p:(A)list) x. fband H p (face_map H x) <=> fband H p x`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN
  MESON_TAC[CFT_FACE; CFT_TRANS; CFACE_SYM_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Mirror preservation lemmas: the faces of mirror H are those of H (its     *)
(* face map is the inverse of face_map H); mirror preserves arity,           *)
(* plain, precubic and bridgeless.                                           *)
(* ------------------------------------------------------------------------- *)

let FACE_MIRROR = prove
 (`!H:(A)hypermap x. x IN dart H ==> face(mirror H) x = face H x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[face; MIRROR_COMPONENTS; GSYM FACE_MAP_INVERSE] THEN
  MATCH_MP_TAC ORBIT_MAP_INVERSE THEN
  ASM_MESON_TAC[FINITE_DART; FACE_MAP_PERMUTES]);;

let CFACE_MIRROR = prove
 (`!H:(A)hypermap x y. x IN dart H ==> (cface(mirror H) x y <=> cface H x y)`,
  SIMP_TAC[cface; FACE_MIRROR]);;

let ARITY_MIRROR = prove
 (`!H (x:A). x IN dart H ==> arity (mirror H) x = arity H x`,
  SIMP_TAC[arity; orbit_size; GSYM face; FACE_MIRROR]);;

let PRECUBIC_MIRROR = prove
 (`!H:(A)hypermap. precubic(mirror H) <=> precubic H`,
  GEN_TAC THEN
  REWRITE_TAC[precubic; MIRROR_COMPONENTS; GSYM NODE_MAP_INVERSE] THEN
  MESON_TAC[ORBIT_SIZE_INVERSE; FINITE_DART; NODE_MAP_PERMUTES]);;

let PLAIN_MIRROR = prove
 (`!H:(A)hypermap. plain_hypermap(mirror H) <=> plain_hypermap H`,
  GEN_TAC THEN REWRITE_TAC[plain_hypermap; MIRROR_COMPONENTS] THEN
  SUBGOAL_THEN
   `!x:A. x IN dart H
          ==> orbit_size (face_map H o node_map H) x =
              orbit_size (edge_map H) (node_map H x)`
   (fun th -> SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`node_map H o face_map(H:(A)hypermap)`;
                   `inverse(node_map(H:(A)hypermap))`; `dart(H:(A)hypermap)`;
                   `node_map H (x:A)`] ORBIT_SIZE_CONJUGATE) THEN
    MP_TAC(ISPEC `H:(A)hypermap` NODE_MAP_PERMUTES) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSE_INVERSE th] THEN
      STRIP_ASSUME_TAC(MATCH_MP PERMUTES_INVERSES th)) THEN
    ASM_SIMP_TAC[FINITE_DART; PERMUTES_COMPOSE; FACE_MAP_PERMUTES;
                 NODE_MAP_PERMUTES; PERMUTES_INVERSE; NODE_MAP_IN_DART] THEN
    SUBGOAL_THEN
     `inverse(node_map H) o (node_map H o face_map H) o node_map H =
      face_map H o node_map(H:(A)hypermap)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM EDGE_MAP_INVERSE] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC ORBIT_SIZE_INVERSE THEN
    ASM_MESON_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_IN_DART];
    MP_TAC(BETA_RULE(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`;
      `\y:A. orbit_size (edge_map H) y = 2`] PERMUTES_FORALL_IN)) THEN
    REWRITE_TAC[NODE_MAP_PERMUTES]]);;

let BRIDGELESS_MIRROR = prove
 (`!H:(A)hypermap. bridgeless(mirror H) <=> bridgeless H`,
  GEN_TAC THEN REWRITE_TAC[bridgeless; MIRROR_COMPONENTS; o_THM] THEN
  SIMP_TAC[CFACE_MIRROR] THEN
  SUBGOAL_THEN
   `!x:A. cface H x (face_map H (node_map H x)) <=>
          cface H (node_map H x) (edge_map H (node_map H x))`
   (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[CFT_FACE; CFT_EDGE_NODE; CFT_TRANS; CFACE_SYM_GEN];
    MP_TAC(BETA_RULE(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`;
      `\y:A. ~cface H y (edge_map H y)`] PERMUTES_FORALL_IN)) THEN
    REWRITE_TAC[NODE_MAP_PERMUTES]]);;

(* ------------------------------------------------------------------------- *)
(* fproj: projection onto face band. Finds first element of p in same face   *)
(* as x; returns x if none.                                                  *)
(* ------------------------------------------------------------------------- *)

let fproj = define
  `(fproj (H:(A)hypermap) [] (x:A) = x) /\
   (fproj H (CONS y p) x = if cface H x y then y else fproj H p x)`;;

let FPROJ_IN_FBAND = prove
 (`!H (p:(A)list) x. fband H p x
     ==> MEM (fproj H p x) p /\ cface H x (fproj H p x)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[fband; EX; fproj] THEN
  X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `cface(H:(A)hypermap) x h` THEN ASM_REWRITE_TAC[MEM] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[fband; EX] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let FPROJ_CFACE = prove
 (`!H (p:(A)list) x y.
     x IN dart H /\ fband H p x /\ cface H x y
     ==> fproj H p x = fproj H p y`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[fproj; FBAND_NIL; FBAND_CONS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `cface H y (h:A) <=> cface H x h` SUBST1_TAC THENL
    [ASM_MESON_TAC[CFT_TRANS; CFACE_SYM_GEN]; ALL_TAC]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let SIMPLE_FPROJ = prove
 (`!H (p:(A)list) x. face_simple H p /\ MEM x p ==> fproj H p x = x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; face_simple; fproj] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[cface; face; IN_ORBIT_MAP_REFL];
    SUBGOAL_THEN `~cface(H:(A)hypermap) x h` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `~fband H (t:(A)list) (h:A)` THEN
      REWRITE_TAC[CONTRAPOS_THM; fband; GSYM EX_MEM] THEN
      DISCH_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CFACE_SYM_GEN THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* scycle decomposition lemmas.                                              *)
(* ------------------------------------------------------------------------- *)

let SCYCLE_CYCLE = prove
 (`!H (e:A->A->bool) p. scycle H e p ==> list_cycle e p`,
  REWRITE_TAC[scycle] THEN MESON_TAC[]);;

let SCYCLE_SIMPLE = prove
 (`!H (e:A->A->bool) p. scycle H e p ==> face_simple H p`,
  REWRITE_TAC[scycle] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Kernel lemmas.                                                            *)
(* ------------------------------------------------------------------------- *)

let KERNEL_FACE = prove
 (`!H (p:(A)list) x. kernel H p x ==> kernel H p (face_map H x)`,
  REWRITE_TAC[kernel; FBAND_FACE_MAP_EQ] THEN
  MESON_TAC[FACE_MAP_PERMUTES; PERMUTES_IN_IMAGE]);;

(* set-membership form (REWRITE_TAC[IN; kernel] would also strip the IN of   *)
(* the dart conjunct).                                                       *)

let IN_KERNEL = prove
 (`!H (p:(A)list) x. x IN kernel H p <=> x IN dart H /\ ~fband H p x`,
  REWRITE_TAC[IN; kernel]);;

(* ------------------------------------------------------------------------- *)
(* srpath/srcycle: simple R-paths and simple R-cycles. From Gonthier's       *)
(* geometry.v lines 672-686. srpath x0 x p: simple rlink-path from x through *)
(* p closing back to x0. srcycle r: r is a simple rlink-cycle. SRCYCLEI:     *)
(* under bridgeless, scycle rlink = srcycle (key equivalence).               *)
(* ------------------------------------------------------------------------- *)

let srpath = define
  `(srpath (H:(A)hypermap) x0 x [] <=> cface H (edge_map H x) x0) /\
   (srpath H x0 x (CONS y p) <=>
     cface H (edge_map H x) y /\
     ALL (\z. ~cface H x z) p /\
     srpath H x0 y p)`;;

let srcycle = new_definition
  `srcycle (H:(A)hypermap) r <=>
    if r = [] then T
    else srpath H (HD r) (HD r) (TL r)`;;

let RLINK_NOT_CFACE = prove
 (`!H x y:A. bridgeless H /\ x IN dart H /\ rlink H x y ==> ~cface H x y`,
  MESON_TAC[ADJ_NO_CFACE; RLINK_ADJ]);;

let ALL_NOT_CFACE_FBAND = prove
 (`!H (p:(A)list) x. ALL (\z. ~cface H x z) p <=> ~fband H p x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; fband; EX] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[fband; DE_MORGAN_THM]);;

let SRPATH_EQ = prove
 (`!H:(A)hypermap. bridgeless H ==>
    !p x. ALL (\z. z IN dart H) (CONS x p) ==>
      !x0. (list_path (rlink H) x p /\ rlink H (LAST (CONS x p)) x0 /\
             face_simple H (CONS x p))
            <=>
            srpath H x0 x p`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[list_path; face_simple; LAST; srpath; fband; EX; ALL; rlink];
    X_GEN_TAC `x:A` THEN
    REWRITE_TAC[ALL; list_path; face_simple; srpath; LAST; NOT_CONS_NIL] THEN
    STRIP_TAC THEN X_GEN_TAC `x0:A` THEN
    SUBGOAL_THEN `rlink H x (h:A) <=> cface H (edge_map H x) h`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[rlink]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN
    REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x0:A`) THEN
    REWRITE_TAC[face_simple; LAST] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[ALL_NOT_CFACE_FBAND; fband; EX; DE_MORGAN_THM] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RLINK_NOT_CFACE; rlink]]);;

let SRCYCLEI = prove
 (`!H:(A)hypermap r.
    bridgeless H /\ ~(r = []) /\ ALL (\z. z IN dart H) r
    ==> (scycle H (rlink H) r <=> srcycle H r)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`r:(A)list`, `r:(A)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
  REWRITE_TAC[scycle; list_cycle; NOT_CONS_NIL; srcycle; HD; TL] THEN
  MP_TAC(ISPEC `H:(A)hypermap` SRPATH_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:(A)list`; `h:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `h:A`) THEN
  REWRITE_TAC[list_path] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* rlink_connected and chordless. From Gonthier's geometry.v lines 688-773.  *)
(* ------------------------------------------------------------------------- *)

let rlink_connected = new_definition
  `rlink_connected (H:(A)hypermap) (a:A->bool) <=>
    !x y. x IN a /\ y IN a ==>
      ?p. list_path (rlink H) (node_map H (face_map H x)) p /\
          ~(p = []) /\ LAST p = y /\
          ALL (\z. z IN a) p`;;

let chordless = new_definition
  `chordless (H:(A)hypermap) (r:(A)list) <=>
    !i j. i < LENGTH r /\ j < LENGTH r /\
          adj H (EL i r) (EL j r) /\
          ~(j = (i + 1) MOD LENGTH r) /\
          ~(i = (j + 1) MOD LENGTH r)
          ==> i = j`;;

(* ========================================================================= *)
(* Orbit partition and cardinality.                                          *)
(* ========================================================================= *)

let UNIONS_SET_OF_ORBITS = prove
 (`!f s:A->bool. FINITE s /\ f permutes s
    ==> UNIONS(set_of_orbits s f) = s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[set_of_orbits; UNIONS_GSPEC; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_MESON_TAC[ORBIT_SUBSET; SUBSET];
    DISCH_TAC THEN EXISTS_TAC `y:A` THEN
    ASM_SIMP_TAC[IN_ORBIT_MAP_REFL; PERMUTES_IN_IMAGE]]);;

let ORBITS_DISJOINT = prove
 (`!f s:A->bool. FINITE s /\ f permutes s
    ==> !x y. x IN s /\ y IN s /\ ~(orbit_map f x = orbit_map f y)
              ==> orbit_map f x INTER orbit_map f y = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[ORBIT_MAP_EQ]);;

let FINITE_SET_OF_ORBITS = prove
 (`!f s:A->bool. FINITE s ==> FINITE(set_of_orbits s f)`,
  SIMP_TAC[set_of_orbits; SIMPLE_IMAGE; FINITE_IMAGE]);;

let ORBITS_DISJOINT' = prove
 (`!f s:A->bool. FINITE s /\ f permutes s
    ==> !t u. t IN set_of_orbits s f /\ u IN set_of_orbits s f /\ ~(t = u)
              ==> t INTER u = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[set_of_orbits; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`f:A->A`; `s:A->bool`] ORBITS_DISJOINT) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let FINITE_IN_SET_OF_ORBITS = prove
 (`!f s:A->bool t. FINITE s /\ f permutes s /\ t IN set_of_orbits s f
    ==> FINITE t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[set_of_orbits; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
  ASM_SIMP_TAC[ORBIT_SUBSET]);;

let CARD_ORBITS_PARTITION = prove
 (`!f s:A->bool. FINITE s /\ f permutes s
    ==> CARD s = nsum (set_of_orbits s f) CARD`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `set_of_orbits (s:A->bool) (f:A->A)` CARD_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_SET_OF_ORBITS] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_IN_SET_OF_ORBITS THEN
      EXISTS_TAC `f:A->A` THEN EXISTS_TAC `s:A->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:A->bool`; `u:A->bool`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`f:A->A`; `s:A->bool`] ORBITS_DISJOINT') THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[UNIONS_SET_OF_ORBITS]]);;

let UNIFORM_ORBIT_CARD = prove
 (`!f s:A->bool k. FINITE s /\ f permutes s /\
    (!x. x IN s ==> orbit_size f x = k)
    ==> k * CARD(set_of_orbits s f) = CARD s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:A->A`; `s:A->bool`] CARD_ORBITS_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `FINITE(set_of_orbits (s:A->bool) (f:A->A))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_SET_OF_ORBITS]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum (set_of_orbits (s:A->bool) (f:A->A)) (\t:A->bool. k)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC;
    MATCH_MP_TAC NSUM_EQ THEN
    REWRITE_TAC[set_of_orbits; IN_ELIM_THM] THEN
    X_GEN_TAC `t:A->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[orbit_size] THEN MESON_TAC[]]);;

(* ========================================================================= *)
(* Edge/node count lemmas for plain and cubic maps.                          *)
(* ========================================================================= *)

let PLAIN_DART_CARD = prove
 (`!(H:(A)hypermap). plain_hypermap H
    ==> 2 * number_of_edges H = CARD(dart H)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_edges; edge_set] THEN
  MATCH_MP_TAC UNIFORM_ORBIT_CARD THEN
  REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [plain_hypermap]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]);;

let CUBIC_DART_CARD = prove
 (`!(H:(A)hypermap). cubic_hypermap H
    ==> 3 * number_of_nodes H = CARD(dart H)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_nodes; node_set] THEN
  MATCH_MP_TAC UNIFORM_ORBIT_CARD THEN
  REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cubic_hypermap]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Gcomp (connected component) symmetry and transitivity.                    *)
(* ========================================================================= *)

let GCOMP_REFL = prove
 (`!(H:(A)hypermap) x. gcomp H x x`,
  REWRITE_TAC[gcomp] THEN REPEAT GEN_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `\i:num. x:A`] THEN REWRITE_TAC[LT]);;

let GCOMP_GLINK = prove
 (`!(H:(A)hypermap) x y. glink H x y ==> gcomp H x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcomp] THEN
  MAP_EVERY EXISTS_TAC [`1`; `\i:num. if i = 0 then x:A else y`] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH] THEN
  ASM_REWRITE_TAC[]);;

let GCOMP_TRANS = prove
 (`!(H:(A)hypermap) x y z. gcomp H x y /\ gcomp H y z ==> gcomp H x z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcomp] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `p:num->A` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:num->A` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`m + k:num`; `\j:num. if j <= m then (p:num->A) j else q(j - m)`] THEN
  ASM_REWRITE_TAC[LE_0; ARITH_RULE `m + k <= m <=> k = 0`; ADD_SUB2] THEN
  CONJ_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j + 1 <= m` THENL
   [ASM_SIMP_TAC[ARITH_RULE `j + 1 <= m ==> j <= m`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th ->
      free_in `p:num->A` (concl th) && is_forall(concl th))) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `j:num = m` THENL
   [ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `(m + 1) - m = 1`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check(fun th ->
      free_in `q:num->A` (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(j + 1 <= m) /\ ~(j = m) ==> ~(j <= m)`;
                 ARITH_RULE `~(j + 1 <= m) /\ ~(j = m)
                             ==> (j + 1) - m = (j - m) + 1`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th ->
      free_in `q:num->A` (concl th) && is_forall(concl th))) THEN
    ASM_ARITH_TAC]);;

let GCOMP_SYM_GLINK = prove
 (`!(H:(A)hypermap) x y. glink H x y ==> gcomp H y x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[glink] THEN STRIP_TAC THENL
   [MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `face_map H (y:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GCOMP_GLINK THEN REWRITE_TAC[glink];
      MATCH_MP_TAC GCOMP_GLINK THEN REWRITE_TAC[glink] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN CONV_TAC SYM_CONV THEN
      ASM_REWRITE_TAC[edgeK]];
    MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `edge_map H (y:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GCOMP_GLINK THEN REWRITE_TAC[glink];
      MATCH_MP_TAC GCOMP_GLINK THEN REWRITE_TAC[glink] THEN
      DISJ2_TAC THEN DISJ2_TAC THEN CONV_TAC SYM_CONV THEN
      ASM_REWRITE_TAC[nodeK]];
    MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `node_map H (y:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GCOMP_GLINK THEN REWRITE_TAC[glink];
      MATCH_MP_TAC GCOMP_GLINK THEN REWRITE_TAC[glink] THEN
      DISJ1_TAC THEN CONV_TAC SYM_CONV THEN
      ASM_REWRITE_TAC[faceK]]]);;

let GCOMP_SYM = prove
 (`!(H:(A)hypermap) x y. gcomp H x y ==> gcomp H y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcomp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i:num. i <= n ==> gcomp H ((p:num->A) i) x` MP_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GCOMP_REFL];
      DISCH_TAC THEN
      SUBGOAL_THEN `gcomp H ((p:num->A) i) x` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `glink H ((p:num->A) i) (p (SUC i))` ASSUME_TAC THENL
       [SUBGOAL_THEN `SUC i = i + 1` SUBST1_TAC THENL
         [ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `(p:num->A) i` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GCOMP_SYM_GLINK THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[gcomp]]);;

(* ========================================================================= *)
(* Connected hypermap has exactly one component.                             *)
(* ========================================================================= *)

let CONNECTED_NCOMP = prove
 (`!(H:(A)hypermap). connected_hypermap H /\ ~(dart H = {})
    ==> number_of_components H = 1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[connected_hypermap; number_of_components; set_of_components] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!y:A. y IN dart H ==> component (H:(A)hypermap) y = dart H`
    ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    REWRITE_TAC[component; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `w:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `{component (H:(A)hypermap) x | x | x IN dart H} =
     IMAGE (component H) (dart H)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `IMAGE (component (H:(A)hypermap)) (dart H) =
     IMAGE (\x:A. dart H) (dart H)` SUBST1_TAC THENL
   [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CONST] THEN ASM_REWRITE_TAC[CARD_SING]);;

(* ========================================================================= *)
(* Record / bundle definitions. From Gonthier's geometry.v lines 469-580.    *)
(* ========================================================================= *)

let planar_bridgeless = new_definition
  `planar_bridgeless (H:(A)hypermap) <=>
    planar_hypermap H /\ bridgeless H`;;

let plain_cubic = new_definition
  `plain_cubic (H:(A)hypermap) <=>
    plain_hypermap H /\ cubic_hypermap H`;;

let plain_cubic_connected = new_definition
  `plain_cubic_connected (H:(A)hypermap) <=>
    plain_cubic H /\ connected_hypermap H`;;

let plain_cubic_pentagonal = new_definition
  `plain_cubic_pentagonal (H:(A)hypermap) <=>
    plain_cubic H /\ pentagonal H`;;

let planar_bridgeless_plain = new_definition
  `planar_bridgeless_plain (H:(A)hypermap) <=>
    planar_bridgeless H /\ plain_hypermap H`;;

let planar_bridgeless_plain_precubic = new_definition
  `planar_bridgeless_plain_precubic (H:(A)hypermap) <=>
    planar_bridgeless_plain H /\ precubic H`;;

let plain_quasicubic = new_definition
  `plain_quasicubic (H:(A)hypermap) (r:(A)list) <=>
    plain_hypermap H /\ quasicubic H (set_of_list r)`;;

let ucycle_plain_quasicubic = new_definition
  `ucycle_plain_quasicubic (H:(A)hypermap) (r:(A)list) <=>
    plain_quasicubic H r /\
    list_cycle (\x y:A. node_map H x = y) r /\
    PAIRWISE (\x y:A. ~(x = y)) r`;;

let ucycle_planar_plain_quasicubic = new_definition
  `ucycle_planar_plain_quasicubic (H:(A)hypermap) (r:(A)list) <=>
    ucycle_plain_quasicubic H r /\ planar_hypermap H`;;

let ucycle_plain_quasicubic_connected = new_definition
  `ucycle_plain_quasicubic_connected (H:(A)hypermap) (r:(A)list) <=>
    ucycle_plain_quasicubic H r /\ connected_hypermap H`;;

(* ========================================================================= *)
(* CFACE_TAC: a decision tactic for face-connectivity chains.                *)
(*                                                                           *)
(* The face relation `cface H x y` (y lies on the face orbit of x) is an     *)
(* equivalence relation on ALL darts (face_map H is a permutation of dart H  *)
(* and fixes everything else), so a goal `cface H a b` follows from the      *)
(* context exactly when a and b fall into the same class of the equivalence  *)
(* closure of the cface facts available.  CFACE_TAC computes that closure:   *)
(*                                                                           *)
(*   terms   all non-propositional, non-function subterms of the goal, the   *)
(*           assumptions and the instantiated hint conclusions; the dart-    *)
(*           typed ones are the cofaciality universe;                        *)
(*   EQ      a union-find for term equality (all types), seeded by the       *)
(*           equations of the context and closed under congruence            *)
(*           (g a = g b from a = b), the hypermap laws nodeK/edgeK/faceK     *)
(*           and, when `plain_hypermap H` is an assumption, e(e a) = a and   *)
(*           n(f a) = e a;                                                   *)
(*   CF      a union-find for cofaciality, seeded by the cface, rlink and    *)
(*           singleton-fband facts of the context, by EQ (equal darts are    *)
(*           cofacial), and by the structural facts cface a (face_map a),    *)
(*           cface (edge_map (node_map a)) a, cface a (ITER n face_map a),   *)
(*           cface (inverse face_map a) a and, under `cubic_hypermap H`,     *)
(*           cface (node_map (node_map a)) (edge_map a), all modulo EQ;      *)
(*   DART    dart membership, closed under the maps and under CF;            *)
(*   facts   ~cface, ~(a = b), fband/~fband over symbolic lists, MEM, ALL,   *)
(*           `IN kernel` (unfolded to dart + ~fband) and any other literal   *)
(*           are stored; ~fband facts travel along list equations;           *)
(*   hints   theorems `!vs. A1 /\ ... /\ Ak ==> C` (default: face-simple     *)
(*           lists, scycles, bridgeless, node_map a not cofacial with a;     *)
(*           plus the user's list and every universally quantified           *)
(*           assumption) are instantiated by matching the Ai against the     *)
(*           context facts; cface, IN dart and = antecedents are queries to  *)
(*           the closure and instances fire as soon as they hold, chaining   *)
(*           over derived facts.                                             *)
(*                                                                           *)
(* Goals: cface H a b, ~cface H a b, fband H p a, ~fband H p a, rlink H a b, *)
(* a IN face H b, a IN kernel H p, a = b, ~(a = b), a IN dart H, F, and      *)
(* conjunctions, disjunctions, negations, implications, iffs and universal   *)
(* quantifications of these.  A positive goal in a contradictory context is  *)
(* closed by refutation.  If the closure does not decide the goal, a         *)
(* disjunctive context fact over such literals (or MEM over an explicit      *)
(* list) is case-split and the goal retried in each branch (at most          *)
(* cft_max_splits = 3 nested splits), so the tactic fails fast.              *)
(*                                                                           *)
(* Every step is certified in the kernel: the union-finds store proof        *)
(* forests and the answer is composed from the cface lemmas of the section   *)
(* on the face relation above (CFT_TRANS, CFACE_SYM_GEN, CFT_EQ, CFT_FACE,   *)
(* ...), MAPS_IN_DART, the lemmas below and the hint theorems (MP), so the   *)
(* tactic is just a search strategy over existing theorems (no new axioms or *)
(* assumptions).  Set cft_debug := true to see why an atom was not decided.  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Further lemmas composed by the tactic (all unconditional in the darts).   *)
(* ------------------------------------------------------------------------- *)

let CFT_PLAIN_EE = prove
 (`!(H:(A)hypermap) a. plain_hypermap H ==> edge_map H (edge_map H a) = a`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:A) IN dart (H:(A)hypermap)` THEN
  ASM_SIMP_TAC[PLAIN_EQ; MAPS_OUTSIDE_DART]);;

let CFT_PLAIN_NF = prove
 (`!(H:(A)hypermap) a.
     plain_hypermap H ==> node_map H (face_map H a) = edge_map H a`,
  MESON_TAC[CFT_PLAIN_EE; faceK]);;

let CFT_CUBIC_NNE = prove
 (`!(H:(A)hypermap) a.
     cubic_hypermap H
     ==> cface H (node_map H (node_map H a)) (edge_map H a)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:A) IN dart (H:(A)hypermap)` THENL
   [ASM_SIMP_TAC[CUBIC_EQ'] THEN MESON_TAC[CFT_FACE; CFACE_SYM_GEN];
    ASM_SIMP_TAC[MAPS_OUTSIDE_DART; CFACE_REFL]]);;

let CFT_FBAND_CFACE = prove
 (`!(H:(A)hypermap) p a b. fband H p a /\ cface H b a ==> fband H p b`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[CFT_TRANS]);;

let CFT_FBAND_MEM = prove
 (`!(H:(A)hypermap) p a b. MEM b p /\ cface H a b ==> fband H p a`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[]);;

let CFT_NOT_FBAND = prove
 (`!(H:(A)hypermap) p a b. ~fband H p a /\ MEM b p ==> ~cface H a b`,
  MESON_TAC[CFT_FBAND_MEM]);;

(* The default hints.                                                        *)

let CFT_FACE_SIMPLE = prove
 (`!(H:(A)hypermap) r x y.
     face_simple H r /\ MEM x r /\ MEM y r /\ cface H x y ==> x = y`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; face_simple] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM DISJ_CASES_TAC) THEN
  ASM_MESON_TAC[CFT_FBAND_MEM; CFACE_SYM_GEN]);;

let CFT_SCYCLE = prove
 (`!(H:(A)hypermap) e r x y.
     scycle H e r /\ MEM x r /\ MEM y r /\ cface H x y ==> x = y`,
  REWRITE_TAC[scycle] THEN MESON_TAC[CFT_FACE_SIMPLE]);;

let CFT_NODE_NOT_SELF = prove
 (`!(H:(A)hypermap) a.
     bridgeless H /\ a IN dart H ==> ~cface H (node_map H a) a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `node_map (H:(A)hypermap) a`]
    BRIDGELESS_CFACE) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN
  ASM_MESON_TAC[CFT_EDGE_NODE; CFT_TRANS; CFACE_SYM_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Syntax helpers.                                                           *)
(* ------------------------------------------------------------------------- *)

let cft_dest name n tm =
  let f,args = strip_comb tm in
  if is_const f && fst(dest_const f) = name && length args = n then args
  else failwith "cft_dest";;

let cft_dest_cface tm =
  match cft_dest "cface" 3 tm with
    [h;a;b] -> (h,a,b)
  | _ -> failwith "cft_dest_cface";;

let cft_dest_fband tm =
  match cft_dest "fband" 3 tm with
    [h;p;a] -> (h,p,a)
  | _ -> failwith "cft_dest_fband";;

let cft_dest_mem tm =
  match cft_dest "MEM" 2 tm with
    [y;p] -> (y,p)
  | _ -> failwith "cft_dest_mem";;

let cft_dest_all tm =
  match cft_dest "ALL" 2 tm with
    [pr;p] -> (pr,p)
  | _ -> failwith "cft_dest_all";;

let cft_dest_in_dart tm =
  match cft_dest "IN" 2 tm with
    [t;d] -> (match cft_dest "dart" 1 d with
                [h] -> (t,h)
              | _ -> failwith "cft_dest_in_dart")
  | _ -> failwith "cft_dest_in_dart";;

let cft_dest_in_kernel tm =
  match cft_dest "IN" 2 tm with
    [t;k] -> (match cft_dest "kernel" 2 k with
                [h;p] -> (t,h,p)
              | _ -> failwith "cft_dest_in_kernel")
  | _ -> failwith "cft_dest_in_kernel";;

let cft_dest_map h name tm =
  match cft_dest name 2 tm with
    [h';t] -> if aconv h' h then t else failwith "cft_dest_map"
  | _ -> failwith "cft_dest_map";;

let cft_dest_fun h name tm =
  match cft_dest name 1 tm with
    [h'] -> if aconv h' h then () else failwith "cft_dest_fun"
  | _ -> failwith "cft_dest_fun";;

let cft_dest_iter h tm =
  match cft_dest "ITER" 3 tm with
    [n;f;t] -> (cft_dest_fun h "face_map" f; (n,t))
  | _ -> failwith "cft_dest_iter";;

let cft_dest_finv h tm =
  match cft_dest "inverse" 2 tm with
    [f;t] -> (cft_dest_fun h "face_map" f; t)
  | _ -> failwith "cft_dest_finv";;

let cft_dart_type h = hd(snd(dest_type(type_of h)));;

let cft_is_hypermap_ty ty =
  can dest_type ty && fst(dest_type ty) = "hypermap";;

let cft_mk_map name h t = list_mk_icomb name [h; t];;

let cft_mk_mem y p = list_mk_icomb "MEM" [y; p];;

let cft_mem_conv tm = EQT_ELIM(REWRITE_CONV[MEM] tm);;

(* The subterms of a list of terms that are neither propositions nor         *)
(* functions and contain no bound variables (the equality universe); the     *)
(* dart-typed ones among them form the cofaciality universe.                 *)

let cft_subterms tms =
  let fvs = freesl tms in
  let ok t =
    let ty = type_of t in
    not (ty = bool_ty) && not (is_type ty && fst(dest_type ty) = "fun") &&
    forall (fun v -> mem v fvs) (frees t) in
  itlist (fun tm acc -> union' aconv (find_terms ok tm) acc) tms [];;

(* Normal form of a context fact: rlink and IN face as cface, fband over     *)
(* explicit lists expanded, negations pushed inwards.                        *)

let cft_norm_thms =
  [FBAND_CONS; FBAND_NIL; FBAND_APPEND; rlink; GSYM cface; DE_MORGAN_THM;
   ALL_NOT_CFACE_FBAND];;

let cft_norm th = REWRITE_RULE cft_norm_thms th;;

(* ------------------------------------------------------------------------- *)
(* The closure state.                                                        *)
(* ------------------------------------------------------------------------- *)

type cft_state =
  { cft_h : term; cft_dty : hol_type; cft_tms : term array;
    cft_isdart : bool array; cft_randi : int array;
    cft_eqp : int array; cft_eqt : thm array;
    cft_cfp : int array; cft_cft : thm array;
    cft_dart : thm option array;
    mutable cft_neg : (int * int * thm) list;
    mutable cft_neq : (int * int * thm) list;
    mutable cft_pband : (term * int * thm) list;
    mutable cft_nband : (term * int * thm) list;
    mutable cft_mems : (int * term * thm) list;
    mutable cft_alls : (term * term * thm) list;
    mutable cft_insts : (thm * thm option list) list;
    mutable cft_misc : (term * thm) list;
    mutable cft_nmisc : (term * thm) list;
    mutable cft_derived : thm list;
    mutable cft_newfacts : thm list;
    mutable cft_fired : term list;
    mutable cft_nband_done : (int * int) list;
    cft_hints : thm list; cft_lconsts : term list; cft_u0d : term list;
    cft_asms : thm list;
    cft_plain : thm option;
    cft_cubic : thm option;
    mutable cft_changed : bool };;

let rec assoc_aconv tm l =
  match l with
    [] -> failwith "assoc_aconv"
  | (t,v)::rest -> if aconv t tm then v else assoc_aconv tm rest;;

let cft_index st tm =
  let n = Array.length st.cft_tms in
  let rec look i =
    if i >= n then failwith "cft_index"
    else if aconv st.cft_tms.(i) tm then i else look (i+1) in
  look 0;;

let cft_has st tm = can (cft_index st) tm;;

(* A fact can feed the closure only if its terms are in the universe (the    *)
(* term array is fixed when the state is built); facts outside it are kept   *)
(* as literals but not offered to the hints again, so that a self-feeding    *)
(* hypothesis like `!w. w IN a ==> face_map H w IN a` cannot create a new    *)
(* term every round.                                                         *)

let cft_in_universe st c = forall (cft_has st) (cft_subterms [c]);;

(* Union-find with a proof forest: prf.(i) relates t_i to t_(par.(i)).       *)

let rec cft_root par i = if par.(i) = i then i else cft_root par par.(i);;

let rec cft_find par prf refl trans tms i =
  if par.(i) = i then (i, refl tms.(i)) else
  let (r,p) = cft_find par prf refl trans tms par.(i) in
  (r, trans prf.(i) p);;

let cft_union par prf refl trans sym tms i j th =
  let (ri,pi) = cft_find par prf refl trans tms i
  and (rj,pj) = cft_find par prf refl trans tms j in
  if ri = rj then false else
  (par.(ri) <- rj; prf.(ri) <- trans (sym pi) (trans th pj); true);;

let cft_cf_refl st tm = ISPECL [st.cft_h; tm] CFACE_REFL;;
let cft_cf_trans th1 th2 = MATCH_MP CFT_TRANS (CONJ th1 th2);;
let cft_cf_sym th = MATCH_MP CFACE_SYM_GEN th;;

let cft_eq_same st i j = cft_root st.cft_eqp i = cft_root st.cft_eqp j;;
let cft_cf_same st i j = cft_root st.cft_cfp i = cft_root st.cft_cfp j;;

let cft_eq_prove st i j =
  let (ri,pi) = cft_find st.cft_eqp st.cft_eqt REFL TRANS st.cft_tms i
  and (rj,pj) = cft_find st.cft_eqp st.cft_eqt REFL TRANS st.cft_tms j in
  if ri = rj then TRANS pi (SYM pj) else failwith "cft_eq_prove";;

let cft_cf_prove st i j =
  let fd = cft_find st.cft_cfp st.cft_cft (cft_cf_refl st) cft_cf_trans
             st.cft_tms in
  let (ri,pi) = fd i and (rj,pj) = fd j in
  if ri = rj then cft_cf_trans pi (cft_cf_sym pj)
  else failwith "cft_cf_prove";;

let cft_cf_union st i j th =
  if cft_union st.cft_cfp st.cft_cft (cft_cf_refl st) cft_cf_trans cft_cf_sym
       st.cft_tms i j th
  then st.cft_changed <- true;;

let cft_eq_union st i j th =
  if cft_union st.cft_eqp st.cft_eqt REFL TRANS SYM st.cft_tms i j th then
   (st.cft_changed <- true;
    if st.cft_isdart.(i) then
      cft_cf_union st i j (MATCH_MP (ISPEC st.cft_h CFT_EQ) th));;

let cft_set_dart st i th =
  if st.cft_dart.(i) = None then
   (st.cft_dart.(i) <- Some th; st.cft_changed <- true);;

(* Indices of the terms `name H s` equal (EQ) to t_i.                        *)

let cft_eq_maps st name i =
  let n = Array.length st.cft_tms in
  let rec look j acc =
    if j >= n then acc else
    look (j+1) (if cft_eq_same st i j &&
                   can (cft_dest_map st.cft_h name) st.cft_tms.(j)
                then j::acc else acc) in
  look 0 [];;

let cft_map_of st tm =
  if can (cft_dest_map st.cft_h "edge_map") tm
  then ("e", cft_dest_map st.cft_h "edge_map" tm)
  else if can (cft_dest_map st.cft_h "node_map") tm
  then ("n", cft_dest_map st.cft_h "node_map" tm)
  else if can (cft_dest_map st.cft_h "face_map") tm
  then ("f", cft_dest_map st.cft_h "face_map" tm)
  else failwith "cft_map_of";;

(* ------------------------------------------------------------------------- *)
(* Adding a fact (a theorem whose conclusion is a literal or conjunction).   *)
(* ------------------------------------------------------------------------- *)

let cft_add st th =
  let h = st.cft_h and dty = st.cft_dty in
  let rec add th =
    let c = concl th in
    if is_conj c then (add (CONJUNCT1 th); add (CONJUNCT2 th)) else
    let _ = if not (exists (fun t -> aconv (concl t) c) st.cft_asms) &&
               not (exists (fun t -> aconv (concl t) c) st.cft_derived) &&
               cft_in_universe st c
            then (st.cft_derived <- th :: st.cft_derived;
                  st.cft_newfacts <- th :: st.cft_newfacts) in
    if can cft_dest_cface c then
     (let (h',a,b) = cft_dest_cface c in
      if aconv h' h && cft_has st a && cft_has st b then
        cft_cf_union st (cft_index st a) (cft_index st b) th)
    else if is_neg c && can cft_dest_cface (dest_neg c) then
     (let (h',a,b) = cft_dest_cface (dest_neg c) in
      if aconv h' h && cft_has st a && cft_has st b then
        st.cft_neg <- (cft_index st a, cft_index st b, th) :: st.cft_neg)
    else if is_eq c && not (type_of (lhs c) = bool_ty) then
     (let a,b = dest_eq c in
      if cft_has st a && cft_has st b then
        cft_eq_union st (cft_index st a) (cft_index st b) th)
    else if is_neg c && is_eq (dest_neg c) &&
            not (type_of (lhs (dest_neg c)) = bool_ty) then
     (let a,b = dest_eq (dest_neg c) in
      if cft_has st a && cft_has st b then
        st.cft_neq <- (cft_index st a, cft_index st b, th) :: st.cft_neq)
    else if can cft_dest_in_dart c then
     (let (t,h') = cft_dest_in_dart c in
      if aconv h' h && cft_has st t then cft_set_dart st (cft_index st t) th)
    else if can cft_dest_fband c then
     (let (h',p,a) = cft_dest_fband c in
      if aconv h' h && cft_has st a then
        if is_list p || is_binary "APPEND" p then
          (let th' = cft_norm th in
           if not (aconv (concl th') c) then add th')
        else st.cft_pband <- (p, cft_index st a, th) :: st.cft_pband)
    else if is_neg c && can cft_dest_fband (dest_neg c) then
     (let (h',p,a) = cft_dest_fband (dest_neg c) in
      if aconv h' h && cft_has st a then
        if is_list p || is_binary "APPEND" p then
          (let th' = cft_norm th in
           if not (aconv (concl th') c) then add th')
        else st.cft_nband <- (p, cft_index st a, th) :: st.cft_nband)
    else if can cft_dest_mem c then
     (let (y,p) = cft_dest_mem c in
      if cft_has st y then
        st.cft_mems <- (cft_index st y, p, th) :: st.cft_mems)
    else if is_neg c && can cft_dest_mem (dest_neg c) &&
            is_cons (snd (cft_dest_mem (dest_neg c))) then
      add (REWRITE_RULE[MEM; DE_MORGAN_THM] th)
    else if can cft_dest_all c then
     (let (pr,p) = cft_dest_all c in st.cft_alls <- (pr,p,th) :: st.cft_alls)
    else if can cft_dest_in_kernel c then
     (st.cft_misc <- (c,th) :: st.cft_misc;
      add (REWRITE_RULE[IN_KERNEL] th))
    else if is_neg c then st.cft_nmisc <- (dest_neg c,th) :: st.cft_nmisc
    else st.cft_misc <- (c,th) :: st.cft_misc in
  add th;;

(* Facts derived from ALL P p and ~fband H p a together with MEM y p.        *)

let cft_seed_mems st =
  do_list (fun (pr,p,th) ->
    do_list (fun (i,p',thm) ->
      if aconv p p' then
        cft_add st (BETA_RULE (MP (SPEC st.cft_tms.(i)
          (EQ_MP (SYM (ISPECL [pr; p] ALL_MEM)) th)) thm)))
      st.cft_mems) st.cft_alls;
  do_list (fun (p,i,th) ->
    do_list (fun (j,p',thm) ->
      if aconv p p' then
        st.cft_neg <-
          (i, j, MATCH_MP CFT_NOT_FBAND (CONJ th thm)) :: st.cft_neg)
      st.cft_mems) st.cft_nband;;

(* ------------------------------------------------------------------------- *)
(* Queries against the closure (used for hint antecedents).                  *)
(* ------------------------------------------------------------------------- *)

let cft_asm st a =
  if a = `T` then TRUTH else
  try find (fun th -> aconv (concl th) a) st.cft_asms
  with Failure _ ->
  try find (fun th -> aconv (concl th) a) st.cft_derived
  with Failure _ -> failwith "cft_asm";;

let cft_query st a =
  let h = st.cft_h in
  if can cft_dest_cface a then
   (let (h',x,y) = cft_dest_cface a in
    if aconv h' h && cft_has st x && cft_has st y
    then cft_cf_prove st (cft_index st x) (cft_index st y)
    else cft_asm st a)
  else if can cft_dest_in_dart a then
   (let (t,h') = cft_dest_in_dart a in
    if aconv h' h && cft_has st t then
      (match st.cft_dart.(cft_index st t) with
         Some th -> th
       | None -> failwith "cft_query")
    else cft_asm st a)
  else if is_eq a && not (type_of (lhs a) = bool_ty) then
   (let x,y = dest_eq a in
    if cft_has st x && cft_has st y
    then cft_eq_prove st (cft_index st x) (cft_index st y)
    else cft_asm st a)
  else if can cft_dest_mem a then
   (try cft_asm st a with Failure _ ->
    let (y,p) = cft_dest_mem a in
    if is_list p then cft_mem_conv a else failwith "cft_query")
  else cft_asm st a;;

let cft_is_query st a =
  can cft_dest_cface a || can cft_dest_in_dart a ||
  (is_eq a && type_of (lhs a) = st.cft_dty);;

let cft_relevant_atom dty t =
  can cft_dest_cface t || can cft_dest_fband t || can cft_dest_mem t ||
  can cft_dest_in_dart t || can cft_dest_in_kernel t ||
  (is_eq t && type_of (lhs t) = dty) || t = `F` || t = `T`;;

(* ------------------------------------------------------------------------- *)
(* Hint instantiation: antecedents with unbound variables are matched        *)
(* against the assumptions, or enumerated over the terms when they are       *)
(* closure queries; the result is a list of (instance, antecedent proofs),   *)
(* None marking the queries still to be evaluated.                           *)
(* ------------------------------------------------------------------------- *)

let cft_fresh_hint th =
  let tvs = if hyp th = [] then type_vars_in_term (concl th) else [] in
  let tyin = map (fun tv -> (mk_vartype("?CFT"^dest_vartype tv), tv)) tvs in
  let th1 = INST_TYPE tyin th in
  let vs,_ = strip_forall (concl th1) in
  let gvs = map (fun v -> genvar (type_of v)) vs in
  (SPECL gvs th1, gvs);;

let cft_bind th v u =
  let tyin = type_match (type_of v) (type_of u) [] in
  INST [(u, inst tyin v)] (INST_TYPE tyin th);;

let cft_pre_instances st base lconsts u0 hint =
  let th0,gvs = cft_fresh_hint hint in
  let gnames = map (fst o dest_var) gvs in
  let is_gv t = is_var t && mem (fst(dest_var t)) gnames in
  let gfrees t = filter is_gv (frees t) in
  let h = st.cft_h and dty = st.cft_dty in
  let bind_hyps th =
    let hv = filter (fun v -> cft_is_hypermap_ty (type_of v) &&
                              can (type_match (type_of v) (type_of h)) [])
                    (gfrees (concl th)) in
    match hv with [v] -> cft_bind th v h | _ -> th in
  let th1 = bind_hyps th0 in
  let nante = if is_imp (concl th1)
              then length(conjuncts(lhand(concl th1))) else 0 in
  let ante_of th k = el k (conjuncts(lhand(concl th))) in
  let nu = length u0 in
  let maxvars = if nu > 45 then 1 else 2 in
  let rec enum th vs =
    match vs with
      [] -> [th]
    | v::rest -> flat (map (fun u -> enum (cft_bind th v u) rest) u0) in
  let enum_ok gv = length gv <= maxvars &&
                   forall (fun v -> type_of v = dty) gv in
  let step states k =
    flat (map (fun (th,prfs) ->
      let a = ante_of th k in
      let gv = gfrees a in
      if gv = [] then [(th, prfs @ [None])]
      else if cft_is_query st a then
        (if enum_ok gv then map (fun th' -> (th', prfs @ [None])) (enum th gv)
         else [])
      else if can cft_dest_mem a && is_list (snd (cft_dest_mem a)) &&
              gv = [fst (cft_dest_mem a)] then
        (let y,p = cft_dest_mem a in
         map (fun b -> (cft_bind th y b, prfs @ [None])) (dest_list p))
      else mapfilter (fun asm ->
             let i = term_match lconsts a (concl asm) in
             (INSTANTIATE i th, prfs @ [Some asm])) base) states) in
  let rec go k states =
    if k >= nante then states else go (k+1) (step states k) in
  let finals = go 0 [(th1,[])] in
  flat (map (fun (th,prfs) ->
     let th' = bind_hyps th in
     let gv = gfrees (concl th') in
     if gv = [] then [(th',prfs)]
     else if enum_ok gv then map (fun th'' -> (th'',prfs)) (enum th' gv)
     else []) finals);;

let cft_try_fire st (th,prfs) =
  try
    if prfs = [] then (cft_add st th; true) else
    let antes = conjuncts (lhand (concl th)) in
    let proofs = map2 (fun a p -> match p with
                                    Some th' -> th'
                                  | None -> cft_query st a) antes prfs in
    st.cft_fired <- concl th :: st.cft_fired;
    cft_add st (MP th (end_itlist CONJ proofs)); true
  with Failure _ -> false;;

(* Re-instantiate the hints against the facts derived since the last pass    *)
(* (chaining, e.g. MEM u r1 ==> MEM u p and MEM u p ==> ~cface x u).         *)

let cft_reinstantiate st =
  if st.cft_newfacts = [] then () else
  let base = st.cft_asms @ st.cft_derived in
  st.cft_newfacts <- [];
  let known c = exists (fun (th,_) -> aconv (concl th) c) st.cft_insts ||
                exists (aconv c) st.cft_fired in
  let news = filter (fun (th,_) -> not (known (concl th)))
               (flat (map (cft_pre_instances st base st.cft_lconsts
                             st.cft_u0d) st.cft_hints)) in
  if news <> [] then
   (st.cft_insts <- st.cft_insts @ news; st.cft_changed <- true);;

(* ------------------------------------------------------------------------- *)
(* One round of closure rules.                                               *)
(* ------------------------------------------------------------------------- *)

let cft_round st =
  let n = Array.length st.cft_tms and h = st.cft_h and tms = st.cft_tms in
  let dart i = st.cft_isdart.(i) in
  (* congruence: g a = g b from a = b (all types) *)
  for i = 0 to n - 1 do
    if st.cft_randi.(i) >= 0 then
      for j = i + 1 to n - 1 do
        if st.cft_randi.(j) >= 0 &&
           cft_eq_same st st.cft_randi.(i) st.cft_randi.(j) &&
           not (cft_eq_same st i j) &&
           aconv (rator tms.(i)) (rator tms.(j)) then
          cft_eq_union st i j
            (AP_TERM (rator tms.(i))
                     (cft_eq_prove st st.cft_randi.(i) st.cft_randi.(j)))
      done
  done;
  (* the hypermap laws nodeK/edgeK/faceK and the plain laws, modulo EQ *)
  for i = 0 to n - 1 do
    if dart i && can (cft_map_of st) tms.(i) then
     (let (g,a) = cft_map_of st tms.(i) in
      let ia = cft_index st a in
      let (g1,g2,klem) =
        if g = "f" then ("edge_map","node_map",nodeK)
        else if g = "n" then ("face_map","edge_map",edgeK)
        else ("node_map","face_map",faceK) in
      do_list (fun j ->
        let b = cft_dest_map h g1 tms.(j) in
        let ib = cft_index st b in
        do_list (fun k ->
          let c = cft_dest_map h g2 tms.(k) in
          let ic = cft_index st c in
          if not (cft_eq_same st i ic) then
           (let th1 = AP_TERM (rator tms.(i))
                        (TRANS (cft_eq_prove st ia j)
                               (AP_TERM (rator tms.(j))
                                        (cft_eq_prove st ib k))) in
            cft_eq_union st i ic (TRANS th1 (ISPECL [h; c] klem))))
          (cft_eq_maps st g2 ib))
        (cft_eq_maps st g1 ia);
      match st.cft_plain with
        None -> ()
      | Some pl ->
          if g = "e" then
            do_list (fun j ->
              let b = cft_dest_map h "edge_map" tms.(j) in
              let ib = cft_index st b in
              if not (cft_eq_same st i ib) then
               (let th1 = AP_TERM (rator tms.(i)) (cft_eq_prove st ia j) in
                cft_eq_union st i ib
                  (TRANS th1 (MP (ISPECL [h; b] CFT_PLAIN_EE) pl))))
              (cft_eq_maps st "edge_map" ia)
          else if g = "n" then
            do_list (fun j ->
              let b = cft_dest_map h "face_map" tms.(j) in
              let eb = cft_mk_map "edge_map" h b in
              if cft_has st eb then
               (let ieb = cft_index st eb in
                if not (cft_eq_same st i ieb) then
                 (let th1 = AP_TERM (rator tms.(i)) (cft_eq_prove st ia j) in
                  cft_eq_union st i ieb
                    (TRANS th1 (MP (ISPECL [h; b] CFT_PLAIN_NF) pl)))))
              (cft_eq_maps st "face_map" ia)
          else ())
  done;
  (* cofaciality steps: face_map, edge_map o node_map, cubic, ITER, inverse *)
  for i = 0 to n - 1 do
    if dart i && can (cft_map_of st) tms.(i) then
     (let (g,a) = cft_map_of st tms.(i) in
      let ia = cft_index st a in
      if g = "f" then
       (if not (cft_cf_same st ia i) then
          cft_cf_union st ia i (ISPECL [h; a] CFT_FACE))
      else if g = "e" then
        do_list (fun j ->
          let b = cft_dest_map h "node_map" tms.(j) in
          let ib = cft_index st b in
          if not (cft_cf_same st i ib) then
           (let th1 = MATCH_MP (ISPEC h CFT_EQ)
                        (AP_TERM (rator tms.(i)) (cft_eq_prove st ia j)) in
            cft_cf_union st i ib
              (cft_cf_trans th1 (ISPECL [h; b] CFT_EDGE_NODE))))
          (cft_eq_maps st "node_map" ia)
      else
        match st.cft_cubic with
          None -> ()
        | Some cu ->
            do_list (fun j ->
              let b = cft_dest_map h "node_map" tms.(j) in
              let eb = cft_mk_map "edge_map" h b in
              if cft_has st eb then
               (let ieb = cft_index st eb in
                if not (cft_cf_same st i ieb) then
                 (let th1 = MATCH_MP (ISPEC h CFT_EQ)
                    (AP_TERM (rator tms.(i)) (cft_eq_prove st ia j)) in
                  cft_cf_union st i ieb
                    (cft_cf_trans th1
                       (MP (ISPECL [h; b] CFT_CUBIC_NNE) cu)))))
              (cft_eq_maps st "node_map" ia))
    else if dart i && can (cft_dest_iter h) tms.(i) then
     (let (nn,a) = cft_dest_iter h tms.(i) in
      let ia = cft_index st a in
      if not (cft_cf_same st ia i) then
        cft_cf_union st ia i (ISPECL [h; nn; a] CFT_ITER))
    else if dart i && can (cft_dest_finv h) tms.(i) then
     (let a = cft_dest_finv h tms.(i) in
      let ia = cft_index st a in
      if not (cft_cf_same st i ia) then
        cft_cf_union st i ia (ISPECL [h; a] CFT_INV))
  done;
  (* dart membership: through the maps and through cofaciality *)
  for i = 0 to n - 1 do
    if dart i && st.cft_dart.(i) = None && can (cft_map_of st) tms.(i) then
     (let (g,a) = cft_map_of st tms.(i) in
      match st.cft_dart.(cft_index st a) with
        Some da ->
          let th3 = MP (ISPECL [h; a] MAPS_IN_DART) da in
          cft_set_dart st i
            (if g = "e" then CONJUNCT1 th3
             else if g = "n" then CONJUNCT1(CONJUNCT2 th3)
             else CONJUNCT2(CONJUNCT2 th3))
      | None -> ());
    if dart i && st.cft_dart.(i) = None then
     (let rec look j =
        if j >= n then () else
        match st.cft_dart.(j) with
          Some dj ->
            if dart j && cft_cf_same st i j then
              cft_set_dart st i
                (MATCH_MP CFT_DART (CONJ dj (cft_cf_prove st j i)))
            else look (j+1)
        | None -> look (j+1) in
      look 0)
  done;
  (* ~fband H p a transported along list equations p = CONS .. / APPEND .. *)
  do_list (fun (p,i,th) ->
    if cft_has st p then
     (let ip = cft_index st p in
      for j = 0 to n - 1 do
        if j <> ip && (is_cons tms.(j) || is_binary "APPEND" tms.(j)) &&
           cft_eq_same st ip j && not (mem (i,j) st.cft_nband_done) then
         (st.cft_nband_done <- (i,j) :: st.cft_nband_done;
          cft_add st (SUBS [cft_eq_prove st ip j] th))
      done)) st.cft_nband;
  (* hints *)
  st.cft_insts <- filter (fun inst -> not (cft_try_fire st inst))
                         st.cft_insts;
  cft_reinstantiate st;;

(* ------------------------------------------------------------------------- *)
(* Building the closure for a hypermap h from the goal and assumptions.      *)
(* ------------------------------------------------------------------------- *)

(* Relevant formulas: propositional combinations of cface, fband, MEM,       *)
(* IN dart and dart-equality atoms.                                          *)

let cft_relevant dty t =
  let rec rel t =
    if is_neg t then rel (dest_neg t)
    else if is_conj t || is_disj t || is_imp t then
      rel (lhand t) && rel (rand t)
    else cft_relevant_atom dty t in
  rel t;;

let cft_default_hints = ref
  [CFT_FACE_SIMPLE; CFT_SCYCLE; BRIDGELESS_CFACE; CFT_NODE_NOT_SELF];;

let cft_max_rounds = ref 200;;

let cft_build hints h asl w =
  let asms = map (cft_norm o snd) asl in
  let concls = map concl asms in
  let dty = cft_dart_type h in
  let lconsts = freesl (w :: concls) in
  let u0 = cft_subterms (w :: concls) in
  let u0d = filter (fun t -> type_of t = dty) u0 in
  let has_hyp name =
    (try Some(find (fun th -> can (cft_dest_fun h name) (concl th)) asms)
     with Failure _ -> None) in
  let plain = has_hyp "plain_hypermap" and cubic = has_hyp "cubic_hypermap" in
  let nf_terms u =
    mapfilter (fun t -> cft_mk_map "edge_map" h
                          (cft_dest_map h "face_map"
                             (cft_dest_map h "node_map" t))) u in
  let cu_terms u =
    mapfilter (fun t -> cft_mk_map "edge_map" h
                          (cft_dest_map h "node_map"
                             (cft_dest_map h "node_map" t))) u in
  let extra u = (if plain = None then [] else nf_terms u) @
                (if cubic = None then [] else cu_terms u) in
  let u0 = union' aconv u0 (extra u0) in
  let dummy =
    { cft_h = h; cft_dty = dty; cft_tms = [||]; cft_isdart = [||];
      cft_randi = [||];
      cft_eqp = [||]; cft_eqt = [||]; cft_cfp = [||]; cft_cft = [||];
      cft_dart = [||]; cft_neg = []; cft_neq = []; cft_pband = [];
      cft_nband = []; cft_mems = []; cft_alls = []; cft_insts = [];
      cft_misc = []; cft_nmisc = []; cft_derived = []; cft_newfacts = [];
      cft_fired = []; cft_nband_done = []; cft_hints = [];
      cft_lconsts = lconsts; cft_u0d = u0d;
      cft_asms = asms; cft_plain = plain;
      cft_cubic = cubic; cft_changed = false } in
  let useful th =
    let body = snd (strip_forall (concl th)) in
    let conc = if is_imp body then rand body else body in
    not (is_iff conc) && not (is_forall conc) && not (is_exists conc) in
  let auto = filter (fun th -> is_forall (concl th) && useful th) asms in
  let allhints = hints @ !cft_default_hints @ auto in
  let insts = flat (map (cft_pre_instances dummy asms lconsts u0d)
                        allhints) in
  let u1 = union' aconv u0 (cft_subterms (map (concl o fst) insts)) in
  let u1 = union' aconv u1 (extra u1) in
  let n = length u1 in
  let tms = Array.of_list u1 in
  let idx t = let rec look i = if i >= n then -1
                               else if aconv tms.(i) t then i
                               else look (i+1) in look 0 in
  let st =
    { dummy with cft_tms = tms;
      cft_isdart = Array.map (fun t -> type_of t = dty) tms;
      cft_randi = Array.map (fun t -> if is_comb t then idx (rand t) else -1)
                            tms;
      cft_eqp = Array.init n (fun i -> i); cft_eqt = Array.make n TRUTH;
      cft_cfp = Array.init n (fun i -> i); cft_cft = Array.make n TRUTH;
      cft_dart = Array.make n None; cft_insts = insts;
      cft_hints = allhints } in
  do_list (cft_add st) asms;
  cft_seed_mems st;
  st.cft_newfacts <- [];
  let rec loop k =
    st.cft_changed <- false;
    cft_round st;
    if st.cft_changed && k < !cft_max_rounds then loop (k+1) in
  loop 0;
  st;;

(* ------------------------------------------------------------------------- *)
(* Deciding an atomic goal from the closure.                                 *)
(* ------------------------------------------------------------------------- *)

let cft_refute st =
  let viol (i,j,th) =
    if cft_cf_same st i j then MP (NOT_ELIM th) (cft_cf_prove st i j)
    else failwith "cft_refute" in
  try tryfind viol st.cft_neg with Failure _ ->
  try tryfind (fun (i,j,th) ->
        if cft_eq_same st i j then MP (NOT_ELIM th) (cft_eq_prove st i j)
        else failwith "cft_refute") st.cft_neq
  with Failure _ ->
  try tryfind (fun (p,i,th) ->
        tryfind (fun (p',j,th') ->
          if aconv p p' && cft_cf_same st i j then
            MP (NOT_ELIM th)
               (MATCH_MP CFT_FBAND_CFACE (CONJ th' (cft_cf_prove st i j)))
          else failwith "cft_refute") st.cft_pband) st.cft_nband
  with Failure _ ->
  try tryfind (fun (t,th) -> MP (NOT_ELIM th) (assoc_aconv t st.cft_misc))
              st.cft_nmisc
  with Failure _ -> failwith "CFACE_TAC: no contradiction found";;

let cft_decide_atom st w =
  let h = st.cft_h in
  if w = `F` then cft_refute st
  else if can cft_dest_cface w then
   (let (h',a,b) = cft_dest_cface w in
    if not (aconv h' h) then failwith "cft_decide" else
    cft_cf_prove st (cft_index st a) (cft_index st b))
  else if is_eq w && not (type_of (lhs w) = bool_ty) then
   (let a,b = dest_eq w in cft_eq_prove st (cft_index st a) (cft_index st b))
  else if can cft_dest_in_dart w then
   (let (t,h') = cft_dest_in_dart w in
    if not (aconv h' h) then failwith "cft_decide" else
    match st.cft_dart.(cft_index st t) with
      Some th -> th
    | None -> failwith "CFACE_TAC: dart membership not derivable")
  else if can cft_dest_fband w then
   (let (h',p,a) = cft_dest_fband w in
    if not (aconv h' h) then failwith "cft_decide" else
    let ia = cft_index st a in
    if is_list p then
      tryfind (fun b ->
        MATCH_MP CFT_FBAND_MEM
          (CONJ (cft_mem_conv (cft_mk_mem b p))
                (cft_cf_prove st ia (cft_index st b)))) (dest_list p)
    else
      try tryfind (fun (p',j,th) ->
            if aconv p p' then
              MATCH_MP CFT_FBAND_CFACE (CONJ th (cft_cf_prove st ia j))
            else failwith "") st.cft_pband
      with Failure _ ->
        tryfind (fun (k,p',th) ->
          if aconv p p' then
            MATCH_MP CFT_FBAND_MEM (CONJ th (cft_cf_prove st ia k))
          else failwith "") st.cft_mems)
  else try assoc_aconv w st.cft_misc
       with Failure _ -> failwith "CFACE_TAC: goal not derivable";;

let cft_decide st w =
  try cft_decide_atom st w
  with Failure s ->
    if w = `F` then failwith s else
    try CONTR w (cft_refute st) with Failure _ -> failwith s;;

(* The hypermaps relevant to a goal: the one of its atom, else all those of  *)
(* the cface/fband facts of the context.                                     *)

let cft_fst3 (a,_,_) = a;;

let cft_hypermaps w asms =
  let of_atom t =
    if can cft_dest_cface t then [cft_fst3 (cft_dest_cface t)]
    else if can cft_dest_fband t then [cft_fst3 (cft_dest_fband t)]
    else if can cft_dest_in_dart t then [snd (cft_dest_in_dart t)]
    else [] in
  let hw = of_atom w in
  if hw <> [] then hw else
  let hs = flat (map (fun th ->
             flat (map of_atom (conjuncts (concl th)))) asms) in
  let hs = flat (map (fun th ->
             let c = concl th in
             if is_neg c then of_atom (dest_neg c) else []) asms) @ hs in
  let hs = union' aconv hs [] in
  if is_eq w then filter (fun h -> cft_dart_type h = type_of (lhs w)) hs
  else hs;;

(* ------------------------------------------------------------------------- *)
(* The tactic.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Disjunctive context facts over relevant literals (candidates for case     *)
(* splits when the closure alone does not decide the goal).                  *)

let cft_split_cands dty asms =
  mapfilter (fun th ->
    let c = concl th in
    let th' = if can cft_dest_mem c && is_cons (snd (cft_dest_mem c))
              then REWRITE_RULE[MEM] th else th in
    let c' = concl th' in
    if is_disj c' && cft_relevant dty c' then th'
    else failwith "cft_split_cands") asms;;

let cft_max_splits = ref 3;;

let cft_debug = ref false;;

let cft_try_h hints asl w h =
  try cft_decide (cft_build hints h asl w) w
  with Failure s ->
    (if !cft_debug then
       Printf.printf "CFACE_TAC on %s: %s\n%!" (string_of_term h) s;
     failwith s);;

let cft_atom hints (asl,w) =
  let asms = map (cft_norm o snd) asl in
  let hs = cft_hypermaps w asms in
  if hs = [] then failwith "CFACE_TAC: no hypermap in goal or context" else
  ACCEPT_TAC (tryfind (cft_try_h hints asl w) hs) (asl,w);;

let rec cft_core hints split depth (asl,w) =
  let direct =
    if is_conj w then CONJ_TAC THEN cft_core hints split depth
    else if is_disj w then
      (DISJ1_TAC THEN cft_core hints split depth) ORELSE
      (DISJ2_TAC THEN cft_core hints split depth)
    else if is_imp w then
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      cft_core hints split depth
    else if is_neg w then DISCH_TAC THEN cft_core hints split depth
    else if is_iff w then EQ_TAC THEN cft_core hints split depth
    else if is_forall w then GEN_TAC THEN cft_core hints split depth
    else cft_atom hints in
  try direct (asl,w)
  with Failure s ->
    if depth >= !cft_max_splits then failwith s else
    let asms = map (cft_norm o snd) asl in
    let hs = cft_hypermaps w asms in
    if hs = [] then failwith s else
    let dty = cft_dart_type (hd hs) in
    let cands = filter (fun th -> not (exists (aconv (concl th)) split))
                       (cft_split_cands dty asms) in
    match cands with
      [] -> failwith s
    | th::_ ->
        (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC th THEN
         cft_core hints (concl th :: split) (depth + 1)) (asl,w);;

let CFACE_TAC_CORE hints = cft_core hints [] 0;;

let cft_goal_thms = MEM :: IN_KERNEL :: cft_norm_thms;;

let CFACE_TAC hints =
  REWRITE_TAC cft_goal_thms THEN CFACE_TAC_CORE hints;;
