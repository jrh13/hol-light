(* ========================================================================= *)
(* 4CT/walkup.ml                                                             *)
(*                                                                           *)
(* walkup.v: the Walkup construction (Stahl).  A dart z of a hypermap is     *)
(* removed by skipping it in two of the three permutations, the third being  *)
(* adjusted so that e o n o f = I still holds.  The file defines the three   *)
(* Walkup transforms edge_walkup, node_walkup and face_walkup, counts the    *)
(* orbits (edges, nodes, faces) and the connected components of the result,  *)
(* and shows that the genus does not increase (LE_GENUS_EDGE_WALKUP), so     *)
(* that all three transforms preserve planarity (PLANAR_EDGE_WALKUP,         *)
(* PLANAR_NODE_WALKUP, PLANAR_FACE_WALKUP).  The exact counting lemmas are   *)
(* used by jordan.ml.                                                        *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;

(* ------------------------------------------------------------------------- *)
(* The edge Walkup: z is skipped in the node and face maps, the edge map is  *)
(* the inverse of their composite.  Its maps, dart set and cardinality.      *)
(* ------------------------------------------------------------------------- *)

let edge_walkup = new_definition
  `edge_walkup (H:(A)hypermap) (z:A) =
   mk_hypermap(dart H DELETE z,
     inverse(swap(z, face_map H z) o face_map H) o
       inverse(swap(z, node_map H z) o node_map H),
     swap(z, node_map H z) o node_map H,
     swap(z, face_map H z) o face_map H)`;;
let node_walkup = new_definition
  `node_walkup (H:(A)hypermap) (z:A) = permF(edge_walkup (permN H) z)`;;
let face_walkup = new_definition
  `face_walkup (H:(A)hypermap) (z:A) = permN(edge_walkup (permF H) z)`;;
let cross_edge = new_definition
  `cross_edge (H:(A)hypermap) (z:A) <=>
   node_map H z IN orbit_map (edge_map H) z`;;
let dart_degenerate = new_definition
  `dart_degenerate (H:(A)hypermap) (z:A) <=>
   edge_map H z = z /\ node_map H z = z /\ face_map H z = z`;;

let EDGE_MAP_AS_INVERSE = prove
 (`!H:(A)hypermap. inverse(face_map H) o inverse(node_map H) = edge_map H`,
  REWRITE_TAC[FACE_MAP_INVERSE; NODE_MAP_INVERSE; GSYM o_ASSOC; NFE_I;
              I_O_ID]);;

let EDGE_WALKUP_COMPONENTS = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> dart(edge_walkup H z) = dart H DELETE z /\
        edge_map(edge_walkup H z) =
          inverse(swap(z, face_map H z) o face_map H) o
          inverse(swap(z, node_map H z) o node_map H) /\
        node_map(edge_walkup H z) = swap(z, node_map H z) o node_map H /\
        face_map(edge_walkup H z) = swap(z, face_map H z) o face_map H`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[edge_walkup] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `z:A`]
    PERMUTES_SWAP_COMPOSE) THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `z:A`]
    PERMUTES_SWAP_COMPOSE) THEN
  ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
  REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[hypermap_pred; FST; SND; FINITE_DELETE; FINITE_DART;
               PERMUTES_COMPOSE; PERMUTES_INVERSE] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN SIMP_TAC[]);;

let DART_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> dart(edge_walkup H z) = dart H DELETE z`,
  SIMP_TAC[EDGE_WALKUP_COMPONENTS]);;

let CARD_DART_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> CARD(dart(edge_walkup H z)) = CARD(dart H) - 1`,
  SIMP_TAC[DART_EDGE_WALKUP; CARD_DELETE; FINITE_DART]);;

let GLINK_PERMN = prove
 (`!(H:(A)hypermap) x y. glink (permN H) x y <=> glink H x y`,
  REWRITE_TAC[glink; PERMN_COMPONENTS] THEN MESON_TAC[]);;

let GLINK_PERMF = prove
 (`!(H:(A)hypermap) x y. glink (permF H) x y <=> glink H x y`,
  REWRITE_TAC[glink; PERMF_COMPONENTS] THEN MESON_TAC[]);;

let EULER_PERMN = prove
 (`!(H:(A)hypermap). euler_lhs (permN H) = euler_lhs H /\
                     euler_rhs (permN H) = euler_rhs H`,
  REWRITE_TAC[euler_lhs; euler_rhs; number_of_components; set_of_components;
    component; gcomp; GLINK_PERMN; number_of_edges; number_of_nodes;
    number_of_faces; edge_set; node_set; face_set; PERMN_COMPONENTS] THEN
  ARITH_TAC);;

let EULER_PERMF = prove
 (`!(H:(A)hypermap). euler_lhs (permF H) = euler_lhs H /\
                     euler_rhs (permF H) = euler_rhs H`,
  REWRITE_TAC[euler_lhs; euler_rhs; number_of_components; set_of_components;
    component; gcomp; GLINK_PERMF; number_of_edges; number_of_nodes;
    number_of_faces; edge_set; node_set; face_set; PERMF_COMPONENTS] THEN
  ARITH_TAC);;

let GENUS_PERMN = prove
 (`!(H:(A)hypermap). genus (permN H) = genus H`,
  REWRITE_TAC[genus; EULER_PERMN]);;

let GENUS_PERMF = prove
 (`!(H:(A)hypermap). genus (permF H) = genus H`,
  REWRITE_TAC[genus; EULER_PERMF]);;

let PLANAR_PERMN = prove
 (`!(H:(A)hypermap). planar_hypermap (permN H) <=> planar_hypermap H`,
  REWRITE_TAC[planar_hypermap; GENUS_PERMN]);;

let PLANAR_PERMF = prove
 (`!(H:(A)hypermap). planar_hypermap (permF H) <=> planar_hypermap H`,
  REWRITE_TAC[planar_hypermap; GENUS_PERMF]);;

let SKIP_EQ = prove
 (`!(m:A->A) s z x. m permutes s /\ ~(x = z)
    ==> swap(z, m z) (m x) = (if m x = z then m z else m x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[PERMUTES_INJECTIVE]);;

let NODE_MAP_WALKUP = prove
 (`!(H:(A)hypermap) z x. z IN dart H /\ ~(x = z)
    ==> node_map (edge_walkup H z) x =
        (if node_map H x = z then node_map H z else node_map H x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EDGE_WALKUP_COMPONENTS; o_THM] THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `z:A`;
                 `x:A`] SKIP_EQ) THEN
  ASM_REWRITE_TAC[NODE_MAP_PERMUTES]);;

let FACE_MAP_WALKUP = prove
 (`!(H:(A)hypermap) z x. z IN dart H /\ ~(x = z)
    ==> face_map (edge_walkup H z) x =
        (if face_map H x = z then face_map H z else face_map H x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EDGE_WALKUP_COMPONENTS; o_THM] THEN
  MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `z:A`;
                 `x:A`] SKIP_EQ) THEN
  ASM_REWRITE_TAC[FACE_MAP_PERMUTES]);;

let WALKUP_MAPS_FIX = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> edge_map (edge_walkup H z) z = z /\
        node_map (edge_walkup H z) z = z /\
        face_map (edge_walkup H z) z = z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `edge_walkup (H:(A)hypermap) z` HYPERMAP_LEMMA) THEN
  ASM_SIMP_TAC[DART_EDGE_WALKUP] THEN
  ASM_MESON_TAC[PERMUTES_FIX_OUTSIDE; IN_DELETE]);;

let EDGE_MAP_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> edge_map (edge_walkup H z) =
        edge_map H o swap(node_map H z, node_map H (face_map H z)) o
        swap(z, node_map H z)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EDGE_WALKUP_COMPONENTS] THEN
  MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `z:A`;
                 `face_map (H:(A)hypermap) z`] INVERSE_SWAP_COMPOSE) THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `z:A`;
                 `node_map (H:(A)hypermap) z`] INVERSE_SWAP_COMPOSE) THEN
  REWRITE_TAC[NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:A` THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `z:A`;
                 `face_map (H:(A)hypermap) z`] SWAP_INVERSE_COMMUTE) THEN
  REWRITE_TAC[NODE_MAP_PERMUTES; FUN_EQ_THM; o_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `H:(A)hypermap` EDGE_MAP_AS_INVERSE) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[]);;

let NOT_GLINK_SELF = prove
 (`!(H:(A)hypermap) z. ~glink H z z
    ==> ~(edge_map H z = z) /\ ~(node_map H z = z) /\ ~(face_map H z = z)`,
  REWRITE_TAC[glink] THEN MESON_TAC[]);;

let DEGENERATE_FROM_TWO_FIXED = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> (node_map H z = z /\ face_map H z = z ==> edge_map H z = z) /\
        (edge_map H z = z /\ face_map H z = z ==> node_map H z = z) /\
        (edge_map H z = z /\ node_map H z = z ==> face_map H z = z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] edgeK) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] nodeK) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] faceK) THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let EDGE_MAP_GLINK_SKIP = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ glink H z z
    ==> edge_map(edge_walkup H z) = swap(z, edge_map H z) o edge_map H`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EDGE_MAP_WALKUP] THEN
  MP_TAC(ISPEC `edge_map (H:(A)hypermap)` SWAP_CONJUGATE_INJ) THEN
  REWRITE_TAC[EDGEI] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] edgeK) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] faceK) THEN
  UNDISCH_TAC `glink (H:(A)hypermap) z z` THEN REWRITE_TAC[glink] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THENL
   [DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SWAP_REFL; I_O_ID; SWAP_SYM; SWAP_IDEMPOTENT];
    DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN
      ASM_REWRITE_TAC[SWAP_REFL; I_O_ID; th; SWAP_SYM]);
    DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN
      ASM_REWRITE_TAC[SWAP_REFL; I_O_ID; th; SWAP_SYM])]);;

let NON_GLINK_FACTS = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z
    ==> ~(edge_map H z = z) /\ ~(node_map H z = z) /\ ~(face_map H z = z) /\
        ~(edge_map H (node_map H z) = z) /\
        ~(node_map H (face_map H z) = z) /\
        ~(face_map H (edge_map H z) = z) /\
        ~(edge_map H (node_map H z) = edge_map H z) /\
        ~(node_map H (face_map H z) = node_map H z) /\
        ~(face_map H (edge_map H z) = face_map H z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glink] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] edgeK) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] nodeK) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] faceK) THEN
  ASM_MESON_TAC[EDGEI; NODEI; FACEI]);;

let EDGE_MAP_WALKUP_NON_GLINK = prove
 (`!(H:(A)hypermap) z x. z IN dart H /\ ~glink H z z /\ ~(x = z)
    ==> edge_map (edge_walkup H z) x =
        (if x = node_map H z then edge_map H z
         else if x = node_map H (face_map H z) then edge_map H (node_map H z)
         else edge_map H x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EDGE_MAP_WALKUP; o_THM] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NON_GLINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[swap] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[]);;

let EDGE_WALKUP_AS_SWAP_SKIP = prove
 (`!(H:(A)hypermap) z x.
    z IN dart H /\ ~glink H z z /\ x IN dart H /\ ~(x = z)
    ==> edge_map (edge_walkup H z) x =
        swap(edge_map H z, edge_map H (node_map H z))
          (swap(z, edge_map H z) (edge_map H x))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EDGE_MAP_WALKUP_NON_GLINK] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NON_GLINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] faceK) THEN DISCH_TAC THEN
  REWRITE_TAC[swap] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[EDGEI]);;

let WALKUP_LINKS_NON_GLINK = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z
    ==> edge_map (edge_walkup H z) (node_map H z) = edge_map H z /\
        face_map (edge_walkup H z) (edge_map H (node_map H z)) =
        face_map H z /\
        edge_map (edge_walkup H z) (node_map H (face_map H z)) =
        edge_map H (node_map H z) /\
        node_map (edge_walkup H z) (face_map H (edge_map H z)) =
        node_map H z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NON_GLINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EDGE_MAP_WALKUP_NON_GLINK; FACE_MAP_WALKUP; NODE_MAP_WALKUP;
               nodeK; edgeK]);;

let ORBIT_SKIP_DELETE = prove
 (`!(f:A->A) s z x. FINITE s /\ f permutes s /\ z IN s /\ ~(f z = z) /\
    x IN s /\ ~(x = z)
    ==> orbit_map (swap(z, f z) o f) x = orbit_map f x DELETE z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:A. ~(y = z) ==> (swap(z,f z) o f) y =
                                  (if f y = z then f z else f y)`
    ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[SKIP_EQ]; ALL_TAC] THEN
  ABBREV_TAC `g = swap(z:A, f z) o f` THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; IN_DELETE; ORBIT_MAP_ITER] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `!n. (?m. ITER n g x = ITER m (f:A->A) x) /\
                      ~(ITER n g x = z)`
      (fun th -> MESON_TAC[th]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THENL [MESON_TAC[ITER]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN
      X_CHOOSE_THEN `m:num` SUBST_ALL_TAC (CONJUNCT1 th)) THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `SUC(SUC m)`; EXISTS_TAC `SUC m`] THEN
    ASM_REWRITE_TAC[ITER];
    SUBGOAL_THEN `!n. (ITER n f x = z ==> ?k. (f:A->A) z = ITER k g x) /\
                      (~(ITER n f x = z) ==> ?k. ITER n f x = ITER k g x)`
      (fun th -> MESON_TAC[th]) THEN
    INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
     [ASM_REWRITE_TAC[] THEN MESON_TAC[ITER]; ALL_TAC] THEN
    ASM_CASES_TAC `ITER n (f:A->A) x = z` THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `(g:A->A) (ITER k g x) = ITER (SUC k) g x` MP_TAC THENL
     [REWRITE_TAC[ITER]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[]]);;

let ORBIT_SKIP_EQ = prove
 (`!(f:A->A) s z. FINITE s /\ f permutes s /\ z IN s /\ ~(f z = z)
    ==> orbit_map (swap(z, f z) o f) (f z) = orbit_map f z DELETE z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `z:A`; `(f:A->A) z`]
    ORBIT_SKIP_DELETE) THEN
  ASM_SIMP_TAC[PERMUTES_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
  EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]);;

let ORBIT_SKIP_DISJOINT = prove
 (`!(f:A->A) s z x.
    FINITE s /\ f permutes s /\ z IN s /\ x IN s /\
    ~(z IN orbit_map f x)
    ==> orbit_map (swap(z, f z) o f) x = orbit_map f x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(f:A->A) z = z` THENL
   [ASM_SIMP_TAC[SKIP_FIXED_POINT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `z:A`; `x:A`] ORBIT_SKIP_DELETE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_ORBIT_MAP_REFL]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[GSYM DELETE_NON_ELEMENT]);;

let SET_OF_ORBITS_IMAGE = prove
 (`!(f:A->A) s. set_of_orbits s f = IMAGE (orbit_map f) s`,
  REWRITE_TAC[set_of_orbits; IMAGE; EXTENSION; IN_ELIM_THM]);;

let FCARD_SKIP = prove
 (`!(f:A->A) s z.
    FINITE s /\ f permutes s /\ z IN s
    ==> CARD(set_of_orbits s f) =
        CARD(set_of_orbits (s DELETE z) (swap(z, f z) o f)) +
        (if f z = z then 1 else 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_OF_ORBITS_IMAGE] THEN
  SUBGOAL_THEN `FINITE(IMAGE (orbit_map (f:A->A)) (s DELETE z))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[SKIP_FIXED_POINT] THEN
    SUBGOAL_THEN `IMAGE (orbit_map (f:A->A)) s =
                  {z} INSERT IMAGE (orbit_map f) (s DELETE z)`
      SUBST1_TAC THENL
     [MP_TAC(ISPECL [`f:A->A`; `z:A`] ORBIT_FIXED) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE
       `(z:A) IN s
        ==> IMAGE (f:A->B) s = f z INSERT IMAGE f (s DELETE z)`) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES] THEN COND_CASES_TAC THEN
      REWRITE_TAC[ADD1] THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC[IN_IMAGE; IN_DELETE] THEN
      MESON_TAC[IN_ORBIT_MAP_REFL; IN_SING]];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_0] THEN
  SUBGOAL_THEN `IMAGE (orbit_map (swap(z:A,f z) o f)) (s DELETE z) =
                IMAGE (\t. t DELETE z) (IMAGE (orbit_map f) (s DELETE z))`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    REWRITE_TAC[o_THM; IN_DELETE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ORBIT_SKIP_DELETE THEN EXISTS_TAC `s:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (orbit_map (f:A->A)) s = IMAGE (orbit_map f) (s DELETE z)`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `orbit_map (f:A->A) (f z) = orbit_map f z /\ f z IN s`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `s:A->bool` THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL];
        ASM_MESON_TAC[PERMUTES_IN_IMAGE]];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN
      X_GEN_TAC `t:A->bool` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `x:A = z` THENL
         [EXISTS_TAC `(f:A->A) z`; EXISTS_TAC `x:A`] THEN
        ASM_REWRITE_TAC[];
        MESON_TAC[]]];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_DELETE] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2(CONJUNCT2 th)) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2 th)) THEN MP_TAC(CONJUNCT1 th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (CONJUNCTS_THEN2 SUBST1_TAC
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` (CONJUNCTS_THEN2 SUBST1_TAC
    STRIP_ASSUME_TAC)) THEN
  DISCH_TAC THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `s:A->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[IN_ORBIT_MAP_REFL]);;

let ORBIT_SIZE_GT_1 = prove
 (`!(f:A->A) s z. FINITE s /\ f permutes s /\ z IN s /\ ~(f z = z)
    ==> 1 < orbit_size f z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_size] THEN
  MP_TAC(ISPECL [`{z:A, f z}`; `orbit_map (f:A->A) z`] CARD_SUBSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[IN_ORBIT_MAP_REFL; ORBIT_MAP_STEP; ORBIT_FINITE];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[ARITH_RULE `SUC(SUC 0) <= n ==> 1 < n`]);;

let ORBIT_MAP_AGREE = prove
 (`!(f:A->A) g x. (!k. g(ITER k f x) = f(ITER k f x))
     ==> orbit_map g x = orbit_map f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_map; EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[ITER_AGREE]);;

let ORBIT_MAP_EQ_AGREE = prove
 (`!(f:A->A) g s x. f permutes s /\ (!x. x IN s ==> f x = g x) /\ x IN s
    ==> orbit_map f x = orbit_map g x`,
  MESON_TAC[ORBIT_MAP_AGREE; ITER_PERMUTES_IN]);;

let SET_OF_ORBITS_AGREE = prove
 (`!(f:A->A) g s.
    f permutes s /\ (!x. x IN s ==> f x = g x)
    ==> set_of_orbits s f = set_of_orbits s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_OF_ORBITS_IMAGE] THEN
  MATCH_MP_TAC IMAGE_EQ THEN ASM_MESON_TAC[ORBIT_MAP_EQ_AGREE]);;

let ORBIT_MAP_MERGE_TRANSFER = prove
 (`!(f:A->A) s a b. FINITE s /\ f permutes s /\ a IN s /\ b IN s /\
    ~(a = b) /\ ~(b IN orbit_map f a)
    ==> b IN orbit_map (swap(a,b) o f) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ORBIT_MAP_ITER] THEN
  MP_TAC(SPECL [`f:A->A`; `s:A->bool`; `a:A`] ORBIT_PERIOD_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:num` THEN
  SUBGOAL_THEN `ITER (d - 1) (swap(a:A,b) o f) a = ITER (d - 1) f a`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ITER_SWAP_AGREE THEN GEN_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[ORBIT_MAP_ITER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d = SUC(d - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ITER] THEN ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(f:A->A)(ITER (d - 1) f a) = ITER d f a` SUBST1_TAC THENL
   [SUBGOAL_THEN `d = SUC(d - 1)`
      (fun th -> CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[th]))) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ITER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ITER d (f:A->A) a = a` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[divides] THEN
    EXISTS_TAC `1` THEN ARITH_TAC;
    REWRITE_TAC[SWAP_LEFT]]);;

let FCARD_SWAP_SPLIT = prove
 (`!(f:A->A) s a b.
    FINITE s /\ f permutes s /\ a IN s /\ b IN s /\ ~(a = b) /\
    b IN orbit_map f a
    ==> CARD(set_of_orbits s (swap(a,b) o f)) = CARD(set_of_orbits s f) + 1`,
  SUBGOAL_THEN
   `!n (f:A->A) s a b.
      CARD s = n /\ FINITE s /\ f permutes s /\ a IN s /\ b IN s /\
      ~(a = b) /\ b IN orbit_map f a
      ==> CARD(set_of_orbits s (swap(a,b) o f)) =
          CARD(set_of_orbits s f) + 1`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((f:A->A) a = a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_FIXED; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `(swap(a:A,b) o f) permutes s` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_COMPOSE; PERMUTES_SWAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`swap(a:A,b) o (f:A->A)`; `s:A->bool`; `a:A`] FCARD_SKIP) THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `a:A`] FCARD_SKIP) THEN
  ASM_REWRITE_TAC[o_THM; ADD_0] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `(f:A->A) a = b` THENL
   [ASM_REWRITE_TAC[SWAP_RIGHT; SWAP_REFL; I_O_ID]; ALL_TAC] THEN
  ASM_SIMP_TAC[SWAP_OTHER; ADD_0] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `swap(a:A,f a) o swap(a,b) o f = swap(f a,b) o swap(a,f a) o f`
    SUBST1_TAC THENL
   [REWRITE_TAC[o_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SWAP_COMPOSE_IDENTITY THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(s DELETE (a:A))`) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE] THEN
    ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY;
                  ARITH_RULE `~(n = 0) ==> n - 1 < n`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`swap(a:A,f a) o f`; `s DELETE (a:A)`; `(f:A->A) a`; `b:A`]) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; PERMUTES_SWAP_COMPOSE;
               PERMUTES_IN_IMAGE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `a:A`] ORBIT_SKIP_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[IN_DELETE]);;

let FCARD_SWAP_MERGE = prove
 (`!(f:A->A) s a b.
    FINITE s /\ f permutes s /\ a IN s /\ b IN s /\ ~(a = b) /\
    ~(b IN orbit_map f a)
    ==> CARD(set_of_orbits s f) = CARD(set_of_orbits s (swap(a,b) o f)) + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `a:A`; `b:A`]
    ORBIT_MAP_MERGE_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`swap(a:A,b) o (f:A->A)`; `s:A->bool`; `a:A`; `b:A`]
    FCARD_SWAP_SPLIT) THEN
  ASM_SIMP_TAC[PERMUTES_COMPOSE; PERMUTES_SWAP] THEN
  REWRITE_TAC[o_ASSOC; SWAP_IDEMPOTENT; I_O_ID]);;

let FCARD_SWAP_BOUND = prove
 (`!(f:A->A) s a b.
       FINITE s /\ f permutes s /\ a IN s /\ b IN s
       ==> CARD(set_of_orbits s f) <=
       CARD(set_of_orbits s (swap(a,b) o f)) + 1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a:A = b` THENL
   [ASM_REWRITE_TAC[SWAP_REFL; I_O_ID; LE_ADD]; ALL_TAC] THEN
  ASM_CASES_TAC `(b:A) IN orbit_map f a` THENL
   [MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `a:A`; `b:A`] FCARD_SWAP_SPLIT);
    MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `a:A`; `b:A`] FCARD_SWAP_MERGE)] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let FCARD_NODE_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> number_of_nodes(edge_walkup H z) +
        (if node_map H z = z then 1 else 0) = number_of_nodes H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_nodes; node_set] THEN
  ASM_SIMP_TAC[EDGE_WALKUP_COMPONENTS] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FCARD_SKIP THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES]);;

let FCARD_FACE_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> number_of_faces(edge_walkup H z) +
        (if face_map H z = z then 1 else 0) = number_of_faces H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_faces; face_set] THEN
  ASM_SIMP_TAC[EDGE_WALKUP_COMPONENTS] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FCARD_SKIP THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES]);;

let FCARD_EDGE_GLINK = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ glink H z z
    ==> number_of_edges(edge_walkup H z) +
        (if edge_map H z = z then 1 else 0) = number_of_edges H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_edges; edge_set] THEN
  ASM_SIMP_TAC[DART_EDGE_WALKUP; EDGE_MAP_GLINK_SKIP] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FCARD_SKIP THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES]);;

let EDGE_ORBITS_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z
    ==> number_of_edges H =
        CARD(set_of_orbits (dart H DELETE z)
               (swap(z, edge_map H z) o edge_map H)) /\
        number_of_edges (edge_walkup H z) =
        CARD(set_of_orbits (dart H DELETE z)
               (swap(edge_map H z, edge_map H (node_map H z)) o
                (swap(z, edge_map H z) o edge_map H))) /\
        (swap(z, edge_map H z) o edge_map H) permutes (dart H DELETE z) /\
        edge_map H z IN dart H DELETE z /\
        edge_map H (node_map H z) IN dart H DELETE z /\
        ~(edge_map H z = edge_map H (node_map H z)) /\
        (cross_edge H z <=>
         edge_map H (node_map H z) IN
         orbit_map (swap(z, edge_map H z) o edge_map H) (edge_map H z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NON_GLINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(swap(z, edge_map H z) o edge_map H) permutes
                (dart H DELETE (z:A))` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP_COMPOSE THEN
    ASM_REWRITE_TAC[EDGE_MAP_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map H z IN dart H DELETE (z:A) /\
                edge_map H (node_map H z) IN dart H DELETE z`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[number_of_edges; edge_set] THEN
    MP_TAC(ISPECL [`edge_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`; `z:A`]
      FCARD_SKIP) THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; ADD_0];
    REWRITE_TAC[number_of_edges; edge_set] THEN
    ASM_SIMP_TAC[DART_EDGE_WALKUP] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SET_OF_ORBITS_AGREE THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `edge_walkup (H:(A)hypermap) z` EDGE_MAP_PERMUTES) THEN
      ASM_SIMP_TAC[DART_EDGE_WALKUP];
      REWRITE_TAC[IN_DELETE; o_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC EDGE_WALKUP_AS_SWAP_SKIP THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[cross_edge] THEN
    MP_TAC(ISPECL [`edge_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`; `z:A`]
      ORBIT_SKIP_EQ) THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    EQ_TAC THENL [MESON_TAC[ORBIT_MAP_STEP]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `orbit_map (edge_map H) (edge_map H (node_map H z)) =
      orbit_map (edge_map H) (z:A) /\
      orbit_map (edge_map H) (edge_map H (node_map H z)) =
      orbit_map (edge_map H) (node_map H z)`
      (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
        ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES];
        MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
        ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[PERMUTES_IN_IMAGE; NODE_MAP_PERMUTES];
          MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]]];
      REWRITE_TAC[IN_ORBIT_MAP_REFL]]]);;

let FCARD_EDGE_NON_GLINK_BOUND = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z
    ==> number_of_edges H
        <= number_of_edges(edge_walkup H z) + 1`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP EDGE_ORBITS_WALKUP) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FCARD_SWAP_BOUND THEN
  ASM_REWRITE_TAC[FINITE_DELETE; FINITE_DART]);;

let FCARD_EDGE_CROSS = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z /\ cross_edge H z
    ==> number_of_edges H + 1
        <= number_of_edges(edge_walkup H z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] EDGE_ORBITS_WALKUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`swap(z:A, edge_map H z) o edge_map H`;
    `dart H DELETE (z:A)`; `edge_map (H:(A)hypermap) z`;
    `edge_map H (node_map H (z:A))`] FCARD_SWAP_SPLIT) THEN
  ASM_REWRITE_TAC[FINITE_DELETE; FINITE_DART] THEN ARITH_TAC);;

let FCARD_EDGE_NON_CROSS = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z /\ ~cross_edge H z
    ==> number_of_edges(edge_walkup H z) + 1
        <= number_of_edges H`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] EDGE_ORBITS_WALKUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`swap(z:A, edge_map H z) o edge_map H`;
    `dart H DELETE (z:A)`; `edge_map (H:(A)hypermap) z`;
    `edge_map H (node_map H (z:A))`] FCARD_SWAP_MERGE) THEN
  ASM_REWRITE_TAC[FINITE_DELETE; FINITE_DART] THEN ARITH_TAC);;

let GLINK_IN_DART = prove
 (`!(H:(A)hypermap) x y. x IN dart H /\ glink H x y ==> y IN dart H`,
  REWRITE_TAC[glink] THEN
  MESON_TAC[PERMUTES_IN_IMAGE; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
            FACE_MAP_PERMUTES]);;

let GCOMP_GLINK_INDUCT = prove
 (`!(H:(A)hypermap) P x y.
    P x /\ (!a b. P a /\ glink H a b ==> P b) /\ gcomp H x y ==> P y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcomp] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `p:num->A` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!i. i <= n ==> (P:A->bool) (p i)` (MP_TAC o SPEC `n:num`) THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(p:num->A) i` THEN
    ASM_REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[LE_REFL]]);;

let GCOMP_WALKUP_STEP = prove
 (`!(H:(A)hypermap) z x. z IN dart H /\ x IN dart H /\ ~(x = z)
    ==> gcomp H x (node_map (edge_walkup H z) x) /\
        gcomp H x (face_map (edge_walkup H z) x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NODE_MAP_WALKUP; FACE_MAP_WALKUP] THEN
  (COND_CASES_TAC THENL
    [MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `z:A` THEN CONJ_TAC;
     ALL_TAC]) THEN
  MATCH_MP_TAC GCOMP_GLINK THEN ASM_REWRITE_TAC[glink]);;

let GLINK_WALKUP_GCOMP = prove
 (`!(H:(A)hypermap) z x y.
    z IN dart H /\ x IN dart H /\ ~(x = z) /\ glink (edge_walkup H z) x y
    ==> gcomp H x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN SUBST1_TAC) o
    REWRITE_RULE[glink]) THENL
   [ALL_TAC;
    ASM_SIMP_TAC[GCOMP_WALKUP_STEP];
    ASM_SIMP_TAC[GCOMP_WALKUP_STEP]] THEN
  SUBGOAL_THEN
   `edge_map (edge_walkup H z) x IN dart H DELETE (z:A) /\
    face_map (edge_walkup H z) (edge_map (edge_walkup H z) x) IN
    dart H DELETE z`
    MP_TAC THENL
   [MP_TAC(ISPEC `edge_walkup (H:(A)hypermap) z` HYPERMAP_LEMMA) THEN
    ASM_SIMP_TAC[DART_EDGE_WALKUP] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_DELETE];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN MATCH_MP_TAC GCOMP_SYM THEN
  SUBGOAL_THEN
   `x = node_map (edge_walkup H z) (face_map (edge_walkup H z)
          (edge_map (edge_walkup (H:(A)hypermap) z) x))`
    (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
   [REWRITE_TAC[edgeK]; ALL_TAC] THEN
  MATCH_MP_TAC GCOMP_TRANS THEN
  EXISTS_TAC `face_map (edge_walkup H z)
                (edge_map (edge_walkup (H:(A)hypermap) z) x)` THEN
  ASM_SIMP_TAC[GCOMP_WALKUP_STEP]);;

let GCOMP_WALKUP_IMP = prove
 (`!(H:(A)hypermap) z x y.
    z IN dart H /\ x IN dart H /\ ~(x = z) /\ gcomp (edge_walkup H z) x y
    ==> gcomp H x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`edge_walkup (H:(A)hypermap) z`;
    `\w:A. w IN dart H /\ ~(w = z) /\ gcomp H x w`; `x:A`; `y:A`]
    GCOMP_GLINK_INDUCT) THEN
  ASM_REWRITE_TAC[GCOMP_REFL] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b IN dart H /\ ~(b:A = z)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`edge_walkup (H:(A)hypermap) z`; `a:A`; `b:A`]
      GLINK_IN_DART) THEN
    ASM_SIMP_TAC[DART_EDGE_WALKUP; IN_DELETE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `a:A` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GLINK_WALKUP_GCOMP THEN
  EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[]);;

let GCOMP_LIFT_OUTSIDE = prove
 (`!(H:(A)hypermap) z x y.
    z IN dart H /\
    (!a b. a IN dart H /\ ~(a = z) /\ ~gcomp H a z /\ glink H a b
           ==> gcomp (edge_walkup H z) a b) /\
    x IN dart H /\ ~(x = z) /\ ~gcomp H x z /\ gcomp H x y
    ==> gcomp (edge_walkup H z) x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;
    `\w:A. w IN dart H /\ ~(w = z) /\ gcomp (edge_walkup H z) x w`;
    `x:A`; `y:A`] GCOMP_GLINK_INDUCT) THEN
  ASM_REWRITE_TAC[GCOMP_REFL] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~gcomp H (a:A) z` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~gcomp (H:(A)hypermap) x z` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `a:A` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_WALKUP_IMP THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `b IN dart H /\ ~(b:A = z)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[GLINK_IN_DART];
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[GCOMP_GLINK]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `a:A` THEN
  ASM_SIMP_TAC[]);;

let GCOMP_Z_WALKUP = prove
 (`!(H:(A)hypermap) z w.
    z IN dart H /\
    (!a b. a IN dart H /\ ~(a = z) /\ ~(b = z) /\ glink H a b
           ==> gcomp (edge_walkup H z) a b \/
               ?v. glink H z v /\ ~(v = z) /\ gcomp (edge_walkup H z) b v) /\
    gcomp H z w /\ ~(w = z)
    ==> ?v. glink H z v /\ ~(v = z) /\ gcomp (edge_walkup H z) w v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;
    `\u:A. u IN dart H /\
           (~(u = z) ==> ?v. glink H z v /\ ~(v = z) /\
                             gcomp (edge_walkup H z) u v)`;
    `z:A`; `w:A`] GCOMP_GLINK_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b IN dart (H:(A)hypermap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GLINK_IN_DART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `a:A = z` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `b:A` THEN
    ASM_REWRITE_TAC[GCOMP_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `v:A` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `a:A` THEN
    ASM_SIMP_TAC[GCOMP_SYM];
    ASM_MESON_TAC[]]);;

let GCOMP_WALKUP_TRANSFER = prove
 (`!(H:(A)hypermap) z.
    z IN dart H /\
    (!a b. a IN dart H /\ ~(a = z) /\ ~(b = z) /\ glink H a b
           ==> gcomp (edge_walkup H z) a b) /\
    (!v1 v2. glink H z v1 /\ ~(v1 = z) /\ glink H z v2 /\ ~(v2 = z)
             ==> gcomp (edge_walkup H z) v1 v2)
    ==> !x y. x IN dart H /\ ~(x = z) /\ ~(y = z) /\ gcomp H x y
              ==> gcomp (edge_walkup H z) x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `gcomp (H:(A)hypermap) x z` THENL
   [SUBGOAL_THEN `gcomp (H:(A)hypermap) z x /\ gcomp H z y`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[GCOMP_SYM; GCOMP_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`; `y:A`] GCOMP_Z_WALKUP) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`; `x:A`] GCOMP_Z_WALKUP) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:A` STRIP_ASSUME_TAC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v2:A` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `v1:A` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_TRANS THEN
    EXISTS_TAC `v2:A` THEN ASM_SIMP_TAC[GCOMP_SYM];
    MATCH_MP_TAC GCOMP_LIFT_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[GCOMP_GLINK]]);;

let NCOMP_IMAGE = prove
 (`!(H:(A)hypermap).
    number_of_components H = CARD(IMAGE (component H) (dart H))`,
  REWRITE_TAC[number_of_components; set_of_components] THEN GEN_TAC THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let GCOMP_EQ_COMPONENT = prove
 (`!(H:(A)hypermap) x y. gcomp H x y ==> component H x = component H y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[component; EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[GCOMP_TRANS; GCOMP_SYM]);;

let COMPONENT_EQ_GCOMP = prove
 (`!(H:(A)hypermap) x y.
    x IN dart H /\ y IN dart H /\ component H x = component H y
    ==> gcomp H x y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y IN component (H:(A)hypermap) x` MP_TAC THENL
   [ASM_REWRITE_TAC[component; IN_ELIM_THM; GCOMP_REFL];
    SIMP_TAC[component; IN_ELIM_THM]]);;

let NCOMP_LE_WALKUP = prove
 (`!(H:(A)hypermap) z.
    z IN dart H /\
    (!x y. x IN dart H /\ ~(x = z) /\ ~(y = z) /\ gcomp H x y
           ==> gcomp (edge_walkup H z) x y)
    ==> number_of_components (edge_walkup H z) <= number_of_components H`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NCOMP_IMAGE; DART_EDGE_WALKUP] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (component (H:(A)hypermap)) (dart H DELETE z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_LE2 THEN
    REWRITE_TAC[FINITE_DELETE; FINITE_DART; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC GCOMP_EQ_COMPONENT THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPONENT_EQ_GCOMP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN SIMP_TAC[FINITE_IMAGE; FINITE_DART] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Components when glink z z: links between darts other than z are kept and  *)
(* the non-z glink-successors of z are linked in the Walkup, so the          *)
(* component count does not increase.                                        *)
(* ------------------------------------------------------------------------- *)

let GLINK_WALKUP_GLINK = prove
 (`!(H:(A)hypermap) z a b.
    z IN dart H /\ glink H z z /\ a IN dart H /\ ~(a = z) /\ ~(b = z) /\
    glink H a b
    ==> glink (edge_walkup H z) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] EDGE_MAP_GLINK_SKIP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `glink (H:(A)hypermap) a b` THEN REWRITE_TAC[glink] THEN
  ASM_SIMP_TAC[NODE_MAP_WALKUP; FACE_MAP_WALKUP; o_THM] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [DISJ1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SWAP_OTHER THEN
    ASM_MESON_TAC[EDGEI];
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[]]);;

let SUCC_LINK_GLINK = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> (edge_map H z = z
         ==> glink (edge_walkup H z) (face_map H z) (node_map H z)) /\
        (node_map H z = z
         ==> glink (edge_walkup H z) (edge_map H z) (face_map H z)) /\
        (face_map H z = z
         ==> glink (edge_walkup H z) (node_map H z) (edge_map H z))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] DEGENERATE_FROM_TWO_FIXED) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] WALKUP_MAPS_FIX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[glink] THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN ASM_CASES_TAC `face_map H (z:A) = z` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `node_map H (face_map H (z:A)) = z` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] edgeK) THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[NODE_MAP_WALKUP]];
    DISJ2_TAC THEN DISJ2_TAC THEN ASM_CASES_TAC `edge_map H (z:A) = z` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `face_map H (edge_map H (z:A)) = z` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] nodeK) THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FACE_MAP_WALKUP]];
    DISJ1_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] EDGE_MAP_GLINK_SKIP) THEN
    ASM_REWRITE_TAC[glink] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] faceK) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SWAP_LEFT]]);;

let SUCC_CONNECTED_GLINK = prove
 (`!(H:(A)hypermap) z v1 v2.
    z IN dart H /\ glink H z z /\
    glink H z v1 /\ ~(v1 = z) /\ glink H z v2 /\ ~(v2 = z)
    ==> gcomp (edge_walkup H z) v1 v2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `glink (H:(A)hypermap) z v2` THEN
  UNDISCH_TAC `glink (H:(A)hypermap) z v1` THEN
  UNDISCH_TAC `glink (H:(A)hypermap) z z` THEN REWRITE_TAC[glink] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] SUCC_LINK_GLINK) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[GCOMP_GLINK; GCOMP_SYM; GCOMP_REFL]);;

let NCOMP_WALKUP_LE = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ glink H z z
    ==> number_of_components(edge_walkup H z)
        <= number_of_components H`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NCOMP_LE_WALKUP THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_WALKUP_TRANSFER THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[GCOMP_GLINK; GLINK_WALKUP_GLINK];
    ASM_MESON_TAC[SUCC_CONNECTED_GLINK]]);;

(* ------------------------------------------------------------------------- *)
(* Components when ~glink z z: all links between darts other than z are kept *)
(* except the edge link n z -> e (n z), which becomes n z -> e z; the darts  *)
(* e (n z) -> f z are linked, and e z, e (n z) are in the same edge orbit of *)
(* the Walkup iff ~cross_edge.                                               *)
(* ------------------------------------------------------------------------- *)

let GLINK_WALKUP_NON_GLINK = prove
 (`!(H:(A)hypermap) z a b.
    z IN dart H /\ ~glink H z z /\ a IN dart H /\ ~(a = z) /\ ~(b = z) /\
    glink H a b
    ==> glink (edge_walkup H z) a b \/
        a = node_map H z /\ b = edge_map H (node_map H z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NON_GLINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `glink (H:(A)hypermap) a b` THEN REWRITE_TAC[glink] THEN
  ASM_SIMP_TAC[EDGE_MAP_WALKUP_NON_GLINK; NODE_MAP_WALKUP;
               FACE_MAP_WALKUP] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [ASM_CASES_TAC `a = node_map H (z:A)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(a = node_map H (face_map H (z:A)))` ASSUME_TAC THENL
     [ASM_MESON_TAC[faceK]; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let GCOMP_EDGE_ORBIT = prove
 (`!(H:(A)hypermap) a b. b IN orbit_map (edge_map H) a ==> gcomp H a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ORBIT_MAP_ITER] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ITER; GCOMP_REFL] THEN
  ASM_MESON_TAC[GCOMP_TRANS; GCOMP_GLINK; glink]);;

let GCOMP_EZ_ENZ = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z /\ ~cross_edge H z
    ==> gcomp (edge_walkup H z) (edge_map H z) (edge_map H (node_map H z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] EDGE_ORBITS_WALKUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC GCOMP_EDGE_ORBIT THEN
  SUBGOAL_THEN
   `orbit_map (edge_map (edge_walkup H z)) (edge_map H z) =
    orbit_map (swap(edge_map H z, edge_map H (node_map H z)) o
               (swap(z, edge_map H z) o edge_map H)) (edge_map H (z:A))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_EQ_AGREE THEN EXISTS_TAC `dart H DELETE (z:A)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `edge_walkup (H:(A)hypermap) z` EDGE_MAP_PERMUTES) THEN
      ASM_SIMP_TAC[DART_EDGE_WALKUP];
      REWRITE_TAC[IN_DELETE; o_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC EDGE_WALKUP_AS_SWAP_SKIP THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ORBIT_MAP_MERGE_TRANSFER THEN
    EXISTS_TAC `dart H DELETE (z:A)` THEN
    ASM_REWRITE_TAC[FINITE_DELETE; FINITE_DART]]);;

let WALKUP_GCOMP_NON_GLINK = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z
    ==> gcomp (edge_walkup H z) (node_map H z) (edge_map H z) /\
        gcomp (edge_walkup H z) (edge_map H (node_map H z)) (face_map H z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP WALKUP_LINKS_NON_GLINK) THEN
  CONJ_TAC THEN MATCH_MP_TAC GCOMP_GLINK THEN ASM_REWRITE_TAC[glink]);;

let SUCC_CONNECTED_NON_CROSS = prove
 (`!(H:(A)hypermap) z v1 v2.
    z IN dart H /\ ~glink H z z /\ ~cross_edge H z /\
    glink H z v1 /\ ~(v1 = z) /\ glink H z v2 /\ ~(v2 = z)
    ==> gcomp (edge_walkup H z) v1 v2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] GCOMP_EZ_ENZ) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] WALKUP_GCOMP_NON_GLINK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `gcomp (edge_walkup H z) (edge_map H z) (node_map H z) /\
    gcomp (edge_walkup H z) (edge_map H z) (face_map H (z:A))`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GCOMP_SYM; GCOMP_TRANS]; ALL_TAC] THEN
  UNDISCH_TAC `glink (H:(A)hypermap) z v2` THEN
  UNDISCH_TAC `glink (H:(A)hypermap) z v1` THEN
  REWRITE_TAC[glink] THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GCOMP_SYM; GCOMP_TRANS; GCOMP_REFL]);;

let NCOMP_NON_GLINK_NON_CROSS = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z /\ ~cross_edge H z
    ==> number_of_components(edge_walkup H z)
        <= number_of_components H`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NCOMP_LE_WALKUP THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_WALKUP_TRANSFER THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`; `a:A`; `b:A`]
      GLINK_WALKUP_NON_GLINK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[GCOMP_GLINK];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_TRANS THEN
      EXISTS_TAC `edge_map H (z:A)` THEN
      ASM_MESON_TAC[GCOMP_EZ_ENZ; WALKUP_GCOMP_NON_GLINK]];
    ASM_MESON_TAC[SUCC_CONNECTED_NON_CROSS]]);;

(* ------------------------------------------------------------------------- *)
(* When ~glink z z the component of z splits into at most two components     *)
(* (those of e z and f z); the other components are unchanged.               *)
(* ------------------------------------------------------------------------- *)

let NCOMP_NON_GLINK_BOUND = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z
    ==> number_of_components(edge_walkup H z)
        <= number_of_components H + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] WALKUP_GCOMP_NON_GLINK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w:A. w IN dart H /\ ~(w = z) /\ gcomp H w z
          ==> gcomp (edge_walkup H z) w (edge_map H z) \/
              gcomp (edge_walkup H z) w (face_map H z)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`; `w:A`] GCOMP_Z_WALKUP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REPEAT GEN_TAC THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`; `a:A`; `b:A`]
          GLINK_WALKUP_NON_GLINK) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [ASM_SIMP_TAC[GCOMP_GLINK];
          DISJ2_TAC THEN EXISTS_TAC `face_map H (z:A)` THEN
          ASM_REWRITE_TAC[glink] THEN ASM_MESON_TAC[NOT_GLINK_SELF]];
        ASM_MESON_TAC[GCOMP_SYM]];
      REWRITE_TAC[glink] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_MESON_TAC[GCOMP_TRANS]];
    ALL_TAC] THEN
  ABBREV_TAC `T' = {x:A | x IN dart H /\ ~(x = z) /\ ~gcomp H x z}` THEN
  SUBGOAL_THEN `FINITE (T':A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "T'" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `dart(H:(A)hypermap)` THEN
    REWRITE_TAC[FINITE_DART; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NCOMP_IMAGE; DART_EDGE_WALKUP] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `CARD(IMAGE (component (edge_walkup H z)) T' UNION
         {component (edge_walkup H z) (edge_map H z),
          component (edge_walkup H z) (face_map H (z:A))})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY;
                IN_DELETE] THEN
    X_GEN_TAC `c:A->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A`
      (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `gcomp (H:(A)hypermap) a z` THENL
     [DISJ2_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:A` o
        check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
      MATCH_MP_TAC GCOMP_EQ_COMPONENT THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN EXISTS_TAC `a:A` THEN EXPAND_TAC "T'" THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `CARD(IMAGE (component (edge_walkup H z)) T') +
    CARD{component (edge_walkup H z) (edge_map H z),
         component (edge_walkup H z) (face_map H (z:A))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION_LE THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD{component (edge_walkup H z) (edge_map H z),
         component (edge_walkup H z) (face_map H (z:A))} <= 2`
    MP_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(IMAGE (component (edge_walkup H z)) T') <=
    CARD(IMAGE (component (H:(A)hypermap)) T')`
    MP_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_LE2 THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN EXPAND_TAC "T'" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC GCOMP_EQ_COMPONENT THEN MATCH_MP_TAC GCOMP_LIFT_OUTSIDE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(b:A = z) /\ ~(a = node_map H z)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
         [ASM_MESON_TAC[GCOMP_GLINK];
          UNDISCH_TAC `~gcomp H (node_map H z) (z:A)` THEN REWRITE_TAC[] THEN
          MATCH_MP_TAC GCOMP_SYM THEN MATCH_MP_TAC GCOMP_GLINK THEN
          REWRITE_TAC[glink]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`; `a:A`; `b:A`]
        GLINK_WALKUP_NON_GLINK) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[GCOMP_GLINK];
      MATCH_MP_TAC COMPONENT_EQ_GCOMP THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(IMAGE (component (H:(A)hypermap)) T') + 1 <=
    CARD(IMAGE (component H) (dart H))`
    MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(component (H:(A)hypermap) z INSERT
                     IMAGE (component H) T')` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE] THEN COND_CASES_TAC THEN
      REWRITE_TAC[ADD1; LE_REFL] THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC[IN_IMAGE] THEN EXPAND_TAC "T'" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[COMPONENT_EQ_GCOMP; GCOMP_SYM];
      MATCH_MP_TAC CARD_SUBSET THEN SIMP_TAC[FINITE_IMAGE; FINITE_DART] THEN
      REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[FUN_IN_IMAGE];
        MATCH_MP_TAC IMAGE_SUBSET THEN EXPAND_TAC "T'" THEN SET_TAC[]]];
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A degenerate dart (fixed by all three maps) is an isolated component; the *)
(* Walkup just removes it.  Otherwise the component count cannot decrease.   *)
(* ------------------------------------------------------------------------- *)

let WALKUP_DEGENERATE_MAPS = prove
 (`!(H:(A)hypermap) z.
    z IN dart H /\ edge_map H z = z /\ node_map H z = z /\ face_map H z = z
    ==> edge_map (edge_walkup H z) = edge_map H /\
        node_map (edge_walkup H z) = node_map H /\
        face_map (edge_walkup H z) = face_map H`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EDGE_WALKUP_COMPONENTS; EDGE_MAP_WALKUP; SWAP_REFL; I_O_ID]);;

let COMPONENT_DEGENERATE = prove
 (`!(H:(A)hypermap) z.
    z IN dart H /\ edge_map H z = z /\ node_map H z = z /\ face_map H z = z
    ==> component H z = {z} /\
        !x. x IN dart H /\ ~(x = z)
            ==> component (edge_walkup H z) x = component H x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] WALKUP_DEGENERATE_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:A. gcomp H z y ==> y = z` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `\y:A. y = z`; `z:A`; `y:A`]
      GCOMP_GLINK_INDUCT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN
                         SUBST1_TAC(CONJUNCT1 th)) THEN
    REWRITE_TAC[glink] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. gcomp (edge_walkup H z) x y <=> gcomp (H:(A)hypermap) x y`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[gcomp; glink]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[component; EXTENSION; IN_ELIM_THM; IN_SING] THEN
    ASM_MESON_TAC[GCOMP_REFL];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[component; EXTENSION; IN_ELIM_THM; DART_EDGE_WALKUP;
                 IN_DELETE] THEN
    ASM_MESON_TAC[GCOMP_SYM]]);;

let NCOMP_DEGENERATE = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ glink H z z /\
    edge_map H z = z /\ node_map H z = z /\ face_map H z = z
    ==> number_of_components(edge_walkup H z) + 1
        <= number_of_components H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] COMPONENT_DEGENERATE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NCOMP_IMAGE; DART_EDGE_WALKUP] THEN
  SUBGOAL_THEN
   `IMAGE (component (edge_walkup H z)) (dart H DELETE z) =
    IMAGE (component (H:(A)hypermap)) (dart H DELETE z)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (component H) (dart H) =
    component H z INSERT IMAGE (component (H:(A)hypermap)) (dart H DELETE z)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(z:A) IN s ==> IMAGE (f:A->B) s = f z INSERT IMAGE f (s DELETE z)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE; FINITE_DELETE; FINITE_DART] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ADD1; LE_REFL] THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[IN_IMAGE; IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x IN component (H:(A)hypermap) x` MP_TAC THENL
   [ASM_REWRITE_TAC[component; IN_ELIM_THM; GCOMP_REFL];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_SING]]);;

let NCOMP_NON_DEGENERATE_GE = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~dart_degenerate H z
    ==> number_of_components H <= number_of_components(edge_walkup H z)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NCOMP_IMAGE; DART_EDGE_WALKUP] THEN
  SUBGOAL_THEN
   `IMAGE (component H) (dart H) =
    IMAGE (component (H:(A)hypermap)) (dart H DELETE z)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]] THEN
    SUBGOAL_THEN `?w:A. w IN dart H /\ ~(w = z) /\ glink H z w`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~dart_degenerate (H:(A)hypermap) z` THEN
      REWRITE_TAC[dart_degenerate; glink] THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                    FACE_MAP_PERMUTES];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_DELETE] THEN X_GEN_TAC `c:A->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A`
      (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_CASES_TAC `a:A = z` THENL
     [EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GCOMP_EQ_COMPONENT THEN ASM_SIMP_TAC[GCOMP_GLINK];
      EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CARD_IMAGE_LE2 THEN
    REWRITE_TAC[FINITE_DELETE; FINITE_DART; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC GCOMP_EQ_COMPONENT THEN
    MATCH_MP_TAC GCOMP_WALKUP_IMP THEN EXISTS_TAC `z:A` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPONENT_EQ_GCOMP THEN
    ASM_SIMP_TAC[DART_EDGE_WALKUP; IN_DELETE]]);;

(* ------------------------------------------------------------------------- *)
(* The genus does not increase under the edge Walkup (combining the counts   *)
(* above), so planarity is preserved by all three Walkup transforms.         *)
(* ------------------------------------------------------------------------- *)

let GLINK_SELF_EQ = prove
 (`!(H:(A)hypermap) z.
    glink H z z <=> edge_map H z = z \/ node_map H z = z \/ face_map H z = z`,
  REWRITE_TAC[glink] THEN MESON_TAC[]);;

let LE_GENUS_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> genus(edge_walkup H z) <= genus H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[genus] THEN
  MATCH_MP_TAC GENUS_ARITH_LEMMA THEN REWRITE_TAC[euler_lhs; euler_rhs] THEN
  ASM_SIMP_TAC[CARD_DART_EDGE_WALKUP] THEN
  SUBGOAL_THEN `~(CARD(dart(H:(A)hypermap)) = 0)` MP_TAC THENL
   [ASM_MESON_TAC[CARD_EQ_0; FINITE_DART; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_NODE_EDGE_WALKUP) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_FACE_EDGE_WALKUP) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_GLINK) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_DEGENERATE) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_WALKUP_LE) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] DEGENERATE_FROM_TWO_FIXED) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_NON_GLINK_BOUND) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_NON_GLINK_BOUND) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_NON_GLINK_NON_CROSS) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_CROSS) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_NON_CROSS) THEN
  ASM_REWRITE_TAC[GLINK_SELF_EQ] THEN
  ASM_CASES_TAC `cross_edge (H:(A)hypermap) z` THEN
  ASM_CASES_TAC `edge_map H (z:A) = z` THEN
  ASM_CASES_TAC `node_map H (z:A) = z` THEN
  ASM_CASES_TAC `face_map H (z:A) = z` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let PLANAR_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z.
    z IN dart H /\ planar_hypermap H ==> planar_hypermap(edge_walkup H z)`,
  REWRITE_TAC[planar_hypermap] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] LE_GENUS_EDGE_WALKUP) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let PLANAR_NODE_WALKUP = prove
 (`!(H:(A)hypermap) z.
    z IN dart H /\ planar_hypermap H ==> planar_hypermap(node_walkup H z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[node_walkup; PLANAR_PERMF] THEN
  MATCH_MP_TAC PLANAR_EDGE_WALKUP THEN
  ASM_REWRITE_TAC[PERMN_COMPONENTS; PLANAR_PERMN]);;

let PLANAR_FACE_WALKUP = prove
 (`!(H:(A)hypermap) z.
    z IN dart H /\ planar_hypermap H ==> planar_hypermap(face_walkup H z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[face_walkup; PLANAR_PERMN] THEN
  MATCH_MP_TAC PLANAR_EDGE_WALKUP THEN
  ASM_REWRITE_TAC[PERMF_COMPONENTS; PLANAR_PERMF]);;
