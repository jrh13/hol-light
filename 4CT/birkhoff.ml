(* ========================================================================= *)
(* 4CT/birkhoff.ml                                                           *)
(*                                                                           *)
(* birkhoff.v: the Birkhoff theorem.  In a minimal counter-example one side  *)
(* of a ring of length at most 4 has no face, and one side of a ring of      *)
(* length 5 has at most one face (BIRKHOFF).  Consequences: there are no     *)
(* double darts (DOUBLE_DART); the spoke ring around a face is a simple ring *)
(* whose disk is that face (SCYCLE_SPOKE_RING, DISKF_SPOKE_RING) and is      *)
(* chordless (CHORDLESS_SPOKE_RING); every face has at least 5 sides         *)
(* (MIN_ARITY); ADJ11_EDGE.                                                  *)
(*                                                                           *)
(* The Birkhoff checks Birkhoff_check h m for (h,m) = (1,0), (2,0), (3,0)    *)
(* and (4,1) are proved by evaluation with compute.ml (birkhoff2 ..          *)
(* birkhoff5, Gonthier's Birkhoff2 .. Birkhoff5).  BIRKHOFF_VALID turns a    *)
(* check into the absence of the corresponding nontrivial rings of length    *)
(* h+1, by the Kempe-tree double recursion over the two sides of the ring.   *)
(*                                                                           *)
(* Also here, because the proof needs them: a minimal counter-example is     *)
(* cubic (MCE_CUBIC, Coq coloring.v) and connected (MCE_CONNECTED, Coq       *)
(* patch.v); orbit sizes and the cubic, plain and bridgeless properties      *)
(* across a patch (Coq patch.v); face counts of face bands (Coq geometry.v); *)
(* the equality of the disk traces of a ring with the remainder traces of    *)
(* its reverse (Coq revsnip.v rev_ring_cotrace); and the transfer of         *)
(* minimality to maps over other dart types (MINIMALITY_POLY), needed        *)
(* because the configuration sewn into a ring has darts of type A+num.       *)
(* ========================================================================= *)

needs "4CT/compute_fast.ml";;
needs "4CT/sew.ml";;
needs "4CT/revsnip_tail.ml";;
needs "4CT/cpcolor_correct.ml";;

(* ------------------------------------------------------------------------- *)
(* Small general facts (several are used by the later files).                *)
(* ------------------------------------------------------------------------- *)

let CFACE_ORBIT = prove
 (`!(H:(A)hypermap) z x. x IN orbit_map (face_map H) z <=> cface H z x`,
  REWRITE_TAC[cface; face]);;

let MAP_FIX_OFFDART = prove
 (`!(H:(A)hypermap) x.
     ~(x IN dart H)
     ==> node_map H x = x /\ face_map H x = x /\ edge_map H x = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC PERMUTES_FIX_OUTSIDE THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
  ASM_REWRITE_TAC[ETA_AX; NODE_MAP_PERMUTES; FACE_MAP_PERMUTES;
                  EDGE_MAP_PERMUTES]);;

let ORBIT_SKIP_MEMBER_EQ = prove
 (`!(f:A->A) s z w1 w2.
     FINITE s /\ f permutes s /\ z IN s /\ w1 IN s /\ ~(w1 = z) /\ ~(w2 = z)
     ==> (w2 IN orbit_map (swap(z, f z) o f) w1 <=> w2 IN orbit_map f w1)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(f:A->A) z = z` THENL
   [ASM_SIMP_TAC[SKIP_FIXED_POINT]; ALL_TAC] THEN
  ASM_CASES_TAC `z IN orbit_map (f:A->A) w1` THENL
   [ALL_TAC; ASM_MESON_TAC[ORBIT_SKIP_DISJOINT]] THEN
  SUBGOAL_THEN `orbit_map (f:A->A) z = orbit_map f w1` ASSUME_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `s:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `z:A`] ORBIT_SKIP_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `orbit_map (swap(z:A, f z) o f) w1 = orbit_map (swap(z, f z) o f) (f z)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `s DELETE (z:A)` THEN
    ASM_SIMP_TAC[FINITE_DELETE; PERMUTES_SWAP_COMPOSE; IN_DELETE;
                 IN_ORBIT_MAP_REFL] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    ASM_REWRITE_TAC[IN_DELETE]]);;

let SET_OF_COMPONENTS_IMAGE = prove
 (`!(H:(A)hypermap). set_of_components H = IMAGE (component H) (dart H)`,
  GEN_TAC THEN
  REWRITE_TAC[set_of_components; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let ORBIT_IMAGE = prove
 (`!(h:A->B) f g s x.
     f permutes s /\ x IN s /\ (!z. z IN s ==> h(f z) = g(h z))
     ==> orbit_map g (h x) = IMAGE h (orbit_map f x)`,
  MESON_TAC[IMAGE_ORBIT_INTERTWINE; PERMUTES_IN_IMAGE]);;

let ORBIT_COUNT_IMAGE = prove
 (`!(h:A->B) f g s.
     FINITE s /\ f permutes s /\ (!z. z IN s ==> h(f z) = g(h z)) /\
     (!x y. x IN s /\ y IN s ==> (h x = h y <=> x = y))
     ==> CARD(set_of_orbits (IMAGE h s) g) = CARD(set_of_orbits s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_ORBITS_INTERTWINE THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let ROT_LIST_1 = prove
 (`!l:A list. rot_list 1 l = rot1 l`,
  GEN_TAC THEN
  REWRITE_TAC[rot_list; rot1; num_CONV `1`; take_list; drop_list] THEN
  COND_CASES_TAC THEN REWRITE_TAC[APPEND]);;

let CHORDLESS_RING_EQ = prove
 (`!(H:(A)hypermap) r.
     PAIRWISE (\a b. ~(a = b)) r
     ==> (chordless H r <=>
          !z w. MEM z r /\ MEM w r /\ adj H z w /\
                ~(w = nextc r z) /\ ~(z = nextc r w) ==> z = w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chordless; MEM_EXISTS_EL] THEN
  SUBGOAL_THEN
   `!i j. i < LENGTH r /\ j < LENGTH r
          ==> (EL i r = EL j (r:(A)list) <=> i = j) /\
              (EL j r = nextc r (EL i r) <=> j = (i + 1) MOD LENGTH r)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[NEXTC_EL] THEN
    SUBGOAL_THEN `(i + 1) MOD LENGTH(r:(A)list) < LENGTH r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[EL_PAIRWISE_INJ];
    ALL_TAC] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `i':num`]) THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `EL i r = EL j (r:(A)list)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[]]]);;

let CHORDLESS_RING = prove
 (`!(H:(A)hypermap) r z w.
     chordless H r /\ PAIRWISE (\a b. ~(a = b)) r /\
     MEM z r /\ MEM w r /\ adj H z w /\ ~(w = nextc r z) /\ ~(z = nextc r w)
     ==> z = w`,
  MESON_TAC[CHORDLESS_RING_EQ]);;

let LIST_CYCLE_PATH_HD = prove
 (`!(e:A->A->bool) h t. list_cycle e (CONS h t) ==> list_path e h t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_cycle; NOT_CONS_NIL] THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL; list_path] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SCYCLE_GE2_ALL_DART = prove
 (`!(H:(A)hypermap) r. scycle H (rlink H) r /\ 2 <= LENGTH r
      ==> ALL (\y:A. y IN dart H) r`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THENL
   [REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= 0)`]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THENL
   [REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= SUC 0)`]; ALL_TAC] THEN
  REWRITE_TAC[scycle] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_CYCLE_PATH_HD) THEN
  SUBGOAL_THEN `(h:A) IN dart H` ASSUME_TAC THENL
   [ASM_CASES_TAC `(h:A) IN dart H` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `face_simple (H:(A)hypermap) (CONS h (CONS h' t'))` THEN
    UNDISCH_TAC `list_path (rlink (H:(A)hypermap)) h (CONS h' t')` THEN
    ASM_SIMP_TAC[list_path; face_simple; rlink; MAP_FIX_OFFDART] THEN
    CFACE_TAC[];
    SUBGOAL_THEN `ALL (\y:A. y IN dart H) (CONS h' t')` MP_TAC THENL
     [MATCH_MP_TAC RLINK_PATH_DART THEN EXISTS_TAC `h:A` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[ALL]]]);;

(* ------------------------------------------------------------------------- *)
(* A minimal counter-example is cubic (Coq coloring.v:233-362).  A node of   *)
(* size 2 {x, node x} is suppressed by the double Walkup of kempe.ml that    *)
(* removes the edge {x, edge x}: the result is a smaller planar bridgeless   *)
(* plain precubic map, hence colourable, and the colouring lifts.            *)
(* ------------------------------------------------------------------------- *)

let BRIDGELESS_NODE_NEQ = prove
 (`!(H:(A)hypermap) y. bridgeless H /\ y IN dart H ==> ~(node_map H y = y)`,
  REPEAT STRIP_TAC THEN CFACE_TAC[]);;

(* The basic facts about a node {x, node x} of size 2 in a plain bridgeless  *)
(* map.                                                                      *)

let MCE2_FACTS = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     ~(node_map H x = x) /\ node_map H (node_map H x) = x
     ==> (!y. y IN dart H ==> ~(node_map H y = y)) /\
         edge_map H x IN dart H /\ node_map H x IN dart H /\
         ~(edge_map H x = x) /\ edge_map H (edge_map H x) = x /\
         ~(node_map H (edge_map H x) = node_map H x) /\
         face_map H (edge_map H x) = node_map H x /\
         node_map H (face_map H x) = edge_map H x /\
         (face_map H x = x <=> edge_map H x = node_map H x) /\
         dart(edge_walkup (node_walkup H x) (edge_map H x)) =
         dart H DELETE x DELETE (edge_map H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:A. y IN dart H ==> ~(node_map H y = y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BRIDGELESS_NODE_NEQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[DART_DOUBLE_WALKUP; EDGE_MAP_IN_DART; NODE_MAP_IN_DART;
               PLAIN_NEQ; PLAIN_EQ; PLAIN_EQ'] THEN
  SUBGOAL_THEN `face_map H (edge_map H x) = node_map H (x:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC NODEI THEN EXISTS_TAC `H:(A)hypermap` THEN
    ASM_REWRITE_TAC[edgeK]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP NODEI) THEN ASM_SIMP_TAC[PLAIN_NEQ];
    EQ_TAC THENL
     [DISCH_THEN(fun th -> MP_TAC(AP_TERM `node_map (H:(A)hypermap)` th)) THEN
      ASM_SIMP_TAC[PLAIN_EQ'];
      DISCH_TAC THEN MATCH_MP_TAC NODEI THEN EXISTS_TAC `H:(A)hypermap` THEN
      ASM_SIMP_TAC[PLAIN_EQ']]]);;

(* The node map of the reduced map is node_map H conjugated by the swap of   *)
(* edge x and node x (the dart node x takes the place of edge x).            *)

let MCE2_NODE_MAP = prove
 (`!(H:(A)hypermap) x y.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     ~(node_map H x = x) /\ node_map H (node_map H x) = x /\
     y IN dart H /\ ~(y = x) /\ ~(y = edge_map H x)
     ==> node_map (edge_walkup (node_walkup H x) (edge_map H x)) y =
         swap(edge_map H x,node_map H x)
           (node_map H (swap(edge_map H x,node_map H x) y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] MCE2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NODE_MAP_DOUBLE_WALKUP] THEN
  SUBGOAL_THEN `~(node_map H (edge_map H x) = edge_map H (x:A))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `y = node_map H (x:A)` THENL
   [ASM_REWRITE_TAC[swap] THEN
    SUBGOAL_THEN `~(node_map H x = edge_map H (x:A))` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(node_map H y = (x:A)) /\ ~(node_map H y = node_map H x)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NODEI]; ALL_TAC] THEN
    ASM_REWRITE_TAC[swap] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let MCE2_PRECUBIC = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ bridgeless H /\ precubic H /\ x IN dart H /\
     ~(node_map H x = x) /\ node_map H (node_map H x) = x
     ==> precubic (edge_walkup (node_walkup H x) (edge_map H x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] MCE2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `GG = edge_walkup (node_walkup H x) (edge_map H (x:A))` THEN
  ABBREV_TAC `sw = swap(edge_map H x,node_map H (x:A))` THEN
  SUBGOAL_THEN `!z:A. sw (sw z) = z` ASSUME_TAC THENL
   [EXPAND_TAC "sw" THEN REWRITE_TAC[SWAP_INVOLUTION]; ALL_TAC] THEN
  REWRITE_TAC[precubic] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN dart H /\ ~(y = x) /\ ~(y = edge_map H x)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN dart GG` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sw:A->A) y IN dart H` ASSUME_TAC THENL
   [EXPAND_TAC "sw" THEN REWRITE_TAC[swap] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `orbit_size (node_map GG) (y:A) =
                orbit_size (node_map (H:(A)hypermap)) ((sw:A->A) y)`
    SUBST1_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `precubic (H:(A)hypermap)` THEN REWRITE_TAC[precubic] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[orbit_size] THEN
  SUBGOAL_THEN
   `orbit_map (node_map GG) (y:A) =
    orbit_map ((sw:A->A) o node_map (H:(A)hypermap) o inverse sw) y`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ORBIT_MAP_AGREE THEN
    X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `ITER k (node_map GG) (y:A) IN dart GG` MP_TAC THENL
     [MATCH_MP_TAC ITER_PERMUTES_IN THEN ASM_REWRITE_TAC[NODE_MAP_PERMUTES];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    EXPAND_TAC "GG" THEN EXPAND_TAC "sw" THEN
    REWRITE_TAC[INVERSE_SWAP; o_THM] THEN
    MATCH_MP_TAC MCE2_NODE_MAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM orbit_size] THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `sw:A->A`; `dart(H:(A)hypermap)`;
                 `(sw:A->A) y`] ORBIT_SIZE_CONJUGATE) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "sw" THEN
  MATCH_MP_TAC PERMUTES_SWAP THEN ASM_REWRITE_TAC[]);;

(* Faces of the reduced map are contained in faces of H.                     *)

let MCE2_CFACE = prove
 (`!(H:(A)hypermap) x y z.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     ~(node_map H x = x) /\ node_map H (node_map H x) = x /\
     y IN dart (edge_walkup (node_walkup H x) (edge_map H x)) /\
     cface (edge_walkup (node_walkup H x) (edge_map H x)) y z
     ==> cface H y z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] MCE2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `GG = edge_walkup (node_walkup H x) (edge_map H (x:A))` THEN
  SUBGOAL_THEN `!w:A. w IN dart GG ==> cface H w (face_map GG w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:A) IN dart H /\ ~(w = x) /\ ~(w = edge_map H x)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:A) IN dart GG` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
      MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `face_map GG w = face_map H w \/
                  face_map GG (w:A) = face_map H (face_map H w)`
      MP_TAC THENL
     [EXPAND_TAC "GG" THEN ASM_SIMP_TAC[FACE_MAP_DOUBLE_WALKUP] THEN
      ASM_CASES_TAC `face_map H w = (x:A)` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `face_map H w = edge_map H (x:A)` THEN ASM_REWRITE_TAC[];
      CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN dart GG` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `cface GG (y:A) z` THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC o
             REWRITE_RULE[cface; face; orbit_map; IN_ELIM_THM]) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[ITER; CFACE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[ITER] THEN
  SUBGOAL_THEN `ITER n (face_map GG) (y:A) IN dart GG` ASSUME_TAC THENL
   [MATCH_MP_TAC ITER_PERMUTES_IN THEN ASM_REWRITE_TAC[FACE_MAP_PERMUTES];
    CFACE_TAC[]]);;

let MCE2_BRIDGELESS = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     ~(node_map H x = x) /\ node_map H (node_map H x) = x
     ==> bridgeless (edge_walkup (node_walkup H x) (edge_map H x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] MCE2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[bridgeless] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN dart H /\ ~(y = x) /\ ~(y = edge_map H x)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `(y:A) IN dart (edge_walkup (node_walkup H x) (edge_map H x))` THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EDGE_MAP_DOUBLE_WALKUP] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `y:A`] BRIDGELESS_CFACE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MCE2_CFACE THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

(* A colouring of the reduced map lifts to H.                                *)

let MCE2_COLORABLE = prove
 (`!(H:(A)hypermap) x k.
     plain_hypermap H /\ bridgeless H /\ x IN dart H /\
     ~(node_map H x = x) /\ node_map H (node_map H x) = x /\
     coloring (edge_walkup (node_walkup H x) (edge_map H x)) k
     ==> four_colorable H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] MCE2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `GG = edge_walkup (node_walkup H x) (edge_map H (x:A))` THEN
  REWRITE_TAC[four_colorable] THEN
  ASM_CASES_TAC `edge_map H x = node_map H (x:A)` THENL
   [EXISTS_TAC `\y:A. if y = x then Color0
                     else if y = edge_map H x then Color1
                     else (k:A->color) y` THEN
    EXPAND_TAC "GG" THEN MATCH_MP_TAC COLORING_DOUBLE_WALKUP_LIFT THEN
    ASM_REWRITE_TAC[distinctness "color"];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(GSYM th)) THEN
  SUBGOAL_THEN `~(face_map H x = edge_map H (x:A))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o SYM o AP_TERM `node_map (H:(A)hypermap)`) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map H (x:A) IN dart GG /\ face_map H x IN dart GG`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_DELETE; FACE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `~(face_map H x = (x:A))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map GG (face_map H x) = node_map H (x:A)` ASSUME_TAC THENL
   [EXPAND_TAC "GG" THEN
    ASM_SIMP_TAC[NODE_MAP_DOUBLE_WALKUP; FACE_MAP_IN_DART] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((k:A->color) (face_map H x) = k (node_map H x))`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `edge_map GG (node_map H x) IN dart (GG:(A)hypermap)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[EDGE_MAP_IN_DART]; ALL_TAC] THEN
    SUBGOAL_THEN `face_map H x = face_map GG (edge_map GG (node_map H (x:A)))`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[nodeK]; ALL_TAC] THEN
    UNDISCH_TAC `coloring GG (k:A->color)` THEN REWRITE_TAC[coloring] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `node_map H (x:A)`)
     (MP_TAC o SPEC `edge_map GG (node_map H (x:A))`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\y:A. if y = x then (k:A->color) (face_map H x)
                   else if y = edge_map H x then k(face_map H (edge_map H x))
                   else k y` THEN
  EXPAND_TAC "GG" THEN MATCH_MP_TAC COLORING_DOUBLE_WALKUP_LIFT THEN
  ASM_REWRITE_TAC[]);;

let NODE_ORBIT2 = prove
 (`!(H:(A)hypermap) x.
     bridgeless H /\ precubic H /\ x IN dart H /\
     ~(orbit_size (node_map H) x = 3)
     ==> ~(node_map H x = x) /\ node_map H (node_map H x) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] BRIDGELESS_NODE_NEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
                ITER_ORBIT_SIZE) THEN
  MP_TAC(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
                ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN
  SUBGOAL_THEN `orbit_size (node_map H) (x:A) <= 3` MP_TAC THENL
   [UNDISCH_TAC `precubic (H:(A)hypermap)` THEN REWRITE_TAC[precubic] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~(orbit_size (node_map H) (x:A) = 3)` THEN
  SPEC_TAC(`orbit_size (node_map H) (x:A)`,`d:num`) THEN X_GEN_TAC `d:num` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `d = 1 \/ d = 2` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TWO; ONE; ITER]) THEN ASM_REWRITE_TAC[]);;

let MCE_CUBIC = prove
 (`!H:(A)hypermap. minimal_counter_example H ==> cubic_hypermap H`,
  GEN_TAC THEN REWRITE_TAC[minimal_counter_example] THEN STRIP_TAC THEN
  REWRITE_TAC[cubic_hypermap] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `orbit_size (node_map H) (x:A) = 3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] NODE_ORBIT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `four_colorable (edge_walkup (node_walkup H x) (edge_map H (x:A)))`
   MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PLANAR_DOUBLE_WALKUP; PLAIN_DOUBLE_WALKUP;
                 CARD_DOUBLE_WALKUP; MCE2_BRIDGELESS; MCE2_PRECUBIC];
    REWRITE_TAC[four_colorable] THEN DISCH_THEN(X_CHOOSE_TAC `k:A->color`) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `k:A->color`] MCE2_COLORABLE) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A minimal counter-example is connected (Coq patch.v                       *)
(* minimal_counter_example_is_connected).  The restriction of H to a set of  *)
(* darts closed under its three maps is a hypermap; it is planar because it  *)
(* is reached from H by edge Walkups at the other darts.                     *)
(* ------------------------------------------------------------------------- *)

let sub_hypermap = new_definition
 `sub_hypermap (H:(A)hypermap) s =
    mk_hypermap (s, (\x. if x IN s then edge_map H x else x),
                    (\x. if x IN s then node_map H x else x),
                    (\x. if x IN s then face_map H x else x))`;;

let map_closed = new_definition
 `map_closed (H:(A)hypermap) s <=>
    s SUBSET dart H /\
    (!x. x IN s ==> edge_map H x IN s) /\
    (!x. x IN s ==> node_map H x IN s) /\
    (!x. x IN s ==> face_map H x IN s)`;;

let HYPERMAP_EQ = prove
 (`!G G':(A)hypermap.
     dart G = dart G' /\
     (!x. x IN dart G ==> edge_map G x = edge_map G' x) /\
     (!x. x IN dart G ==> node_map G x = node_map G' x) /\
     (!x. x IN dart G ==> face_map G x = face_map G' x)
     ==> G = G'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `tuple_hypermap G = tuple_hypermap (G':(A)hypermap)`
  MP_TAC THENL
   [ALL_TAC; MESON_TAC[hypermap_tybij]] THEN
  SUBGOAL_THEN
   `!G:(A)hypermap.
      tuple_hypermap G = (dart G, edge_map G, node_map G, face_map G)`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[dart; edge_map; node_map; face_map; PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(x:A) IN dart G` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[PERMUTES_FIX_OUTSIDE; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
                FACE_MAP_PERMUTES]);;

let RESTRICT_PERMUTES = prove
 (`!(f:A->A) s t.
     FINITE s /\ f permutes s /\ t SUBSET s /\ (!x. x IN t ==> f x IN t)
     ==> (\x. if x IN t then f x else x) permutes t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(t:A->bool)` MP_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_FINITE_INJECTIVE th]) THEN
  SIMP_TAC[] THEN ASM_MESON_TAC[PERMUTES_INJECTIVE]);;

let SUB_HYPERMAP_COMPONENTS = prove
 (`!(H:(A)hypermap) s.
     map_closed H s
     ==> dart (sub_hypermap H s) = s /\
         (!x. x IN s ==> edge_map (sub_hypermap H s) x = edge_map H x) /\
         (!x. x IN s ==> node_map (sub_hypermap H s) x = node_map H x) /\
         (!x. x IN s ==> face_map (sub_hypermap H s) x = face_map H x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[map_closed] THEN STRIP_TAC THEN
  REWRITE_TAC[sub_hypermap] THEN
  MP_TAC(ISPECL [`s:A->bool`; `\x:A. if x IN s then edge_map H x else x`;
                 `\x:A. if x IN s then node_map H x else x`;
                 `\x:A. if x IN s then face_map H x else x`]
                MK_HYPERMAP_COMPONENTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[hypermap_pred] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DART];
      MATCH_MP_TAC RESTRICT_PERMUTES THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES];
      MATCH_MP_TAC RESTRICT_PERMUTES THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES];
      MATCH_MP_TAC RESTRICT_PERMUTES THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES];
      REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN X_GEN_TAC `x:A` THEN
      ASM_CASES_TAC `(x:A) IN s` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `face_map H x IN s /\ node_map H (face_map H (x:A)) IN s`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[faceK]]];
    SIMP_TAC[]]);;

let SUB_HYPERMAP_ORBIT = prove
 (`!(f:A->A) g s x.
     (!y. y IN s ==> f y IN s) /\ (!y. y IN s ==> g y = f y) /\ x IN s
     ==> orbit_map g x = orbit_map f x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORBIT_MAP_AGREE THEN
  X_GEN_TAC `k:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_IN_CLOSED) THEN
  ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ITER_IN_ORBIT]);;

let SUB_HYPERMAP_PROPS = prove
 (`!(H:(A)hypermap) s.
     map_closed H s
     ==> (plain_hypermap H ==> plain_hypermap (sub_hypermap H s)) /\
         (precubic H ==> precubic (sub_hypermap H s)) /\
         (bridgeless H ==> bridgeless (sub_hypermap H s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC(MATCH_MP SUB_HYPERMAP_COMPONENTS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[map_closed; SUBSET] th)) THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> orbit_map (edge_map (sub_hypermap H s)) x =
            orbit_map (edge_map H) x /\
            orbit_map (node_map (sub_hypermap H s)) x =
            orbit_map (node_map H) x /\
            orbit_map (face_map (sub_hypermap H s)) x =
            orbit_map (face_map (H:(A)hypermap)) x`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUB_HYPERMAP_ORBIT THEN
    EXISTS_TAC `s:A->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[plain_hypermap; precubic; bridgeless; orbit_size; cface;
               face]);;

let EDGE_WALKUP_OFF_MAPS = prove
 (`!(G:(A)hypermap) s z.
     z IN dart G /\ ~(z IN s) /\
     (!x. x IN s
          ==> edge_map G x IN s /\ node_map G x IN s /\ face_map G x IN s)
     ==> !x. x IN s
             ==> edge_map (edge_walkup G z) x = edge_map G x /\
                 node_map (edge_walkup G z) x = node_map G x /\
                 face_map (edge_walkup G z) x = face_map G x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:A. y IN s ==> node_map (edge_walkup G z) y = node_map G y /\
                     face_map (edge_walkup G z) y = face_map G y`
   ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[NODE_MAP_EDGE_WALKUP; FACE_MAP_EDGE_WALKUP] THEN
    CONJ_TAC THEN MATCH_MP_TAC SWAP_OTHER THEN
    ASM_MESON_TAC[NODEI; FACEI];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `x = node_map (edge_walkup G z)
          (face_map (edge_walkup G z) (edge_map G (x:A)))`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_SIMP_TAC[edgeK]; REWRITE_TAC[faceK]]);;

let SUB_HYPERMAP_PLANAR = prove
 (`!(H:(A)hypermap) s.
     planar_hypermap H /\ map_closed H s
     ==> planar_hypermap (sub_hypermap H s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP SUB_HYPERMAP_COMPONENTS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[map_closed] th))) THEN
  SUBGOAL_THEN
   `!n G:(A)hypermap.
       CARD(dart G DIFF s) = n /\ planar_hypermap G /\ s SUBSET dart G /\
       (!x. x IN s ==> edge_map G x = edge_map H x /\
                       node_map G x = node_map H x /\
                       face_map G x = face_map H x)
       ==> planar_hypermap (sub_hypermap H s)`
   (fun th -> MATCH_MP_TAC th THEN
              MAP_EVERY EXISTS_TAC [`CARD(dart H DIFF (s:A->bool))`;
                                    `H:(A)hypermap`] THEN
              ASM_REWRITE_TAC[]) THEN
  INDUCT_TAC THEN X_GEN_TAC `G:(A)hypermap` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `dart G = (s:A->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `dart G DIFF (s:A->bool)` CARD_EQ_0) THEN
      ASM_SIMP_TAC[FINITE_DIFF; FINITE_DART] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `G = sub_hypermap H (s:A->bool)`
     (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC HYPERMAP_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:A. z IN dart G /\ ~(z IN s)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `dart G DIFF (s:A->bool)` CARD_EQ_0) THEN
    ASM_SIMP_TAC[FINITE_DIFF; FINITE_DART; NOT_SUC] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `edge_walkup G (z:A)`) THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `s:A->bool`; `z:A`]
    EDGE_WALKUP_OFF_MAPS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ASM_SIMP_TAC[DART_EDGE_WALKUP; PLANAR_EDGE_WALKUP] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(dart G DELETE z) DIFF s = (dart G DIFF s) DELETE (z:A)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DIFF; FINITE_DART; IN_DIFF] THEN
    ARITH_TAC;
    ASM SET_TAC[]]);;

let SUB_HYPERMAP_COLORING_MERGE = prove
 (`!(H:(A)hypermap) s k1 k2.
     map_closed H s /\ map_closed H (dart H DIFF s) /\
     coloring (sub_hypermap H s) k1 /\
     coloring (sub_hypermap H (dart H DIFF s)) k2
     ==> coloring H (\x. if x IN s then k1 x else k2 x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP SUB_HYPERMAP_COMPONENTS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[map_closed] th)) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP SUB_HYPERMAP_COMPONENTS th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[map_closed; IN_DIFF] th)) MP_TAC) THEN
  ASM_SIMP_TAC[coloring; IN_DIFF] THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_CASES_TAC `(x:A) IN s` THEN
  ASM_SIMP_TAC[]);;

let COMPONENT_MAP_CLOSED = prove
 (`!(H:(A)hypermap) x0.
     x0 IN dart H
     ==> map_closed H (component H x0) /\
         map_closed H (dart H DIFF component H x0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[map_closed; component; SUBSET; IN_DIFF; IN_ELIM_THM] THEN
  SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  MESON_TAC[GCOMP_TRANS; GCOMP_GLINK; GCOMP_SYM_GLINK; glink]);;

let MCE_CONNECTED = prove
 (`!H:(A)hypermap. minimal_counter_example H ==> connected_hypermap H`,
  GEN_TAC THEN REWRITE_TAC[minimal_counter_example; connected_hypermap] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x0:A`; `y0:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `gcomp (H:(A)hypermap) x0 y0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!t:A->bool. map_closed H t /\ ~(t = dart H)
                ==> four_colorable (sub_hypermap H t)`
   ASSUME_TAC THENL
   [X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `t:A->bool`] SUB_HYPERMAP_PROPS) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `t:A->bool`] SUB_HYPERMAP_PLANAR) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `t:A->bool`] SUB_HYPERMAP_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[FINITE_DART; PSUBSET] THEN
    UNDISCH_TAC `map_closed H (t:A->bool)` THEN SIMP_TAC[map_closed];
    ALL_TAC] THEN
  UNDISCH_TAC `~four_colorable (H:(A)hypermap)` THEN
  REWRITE_TAC[four_colorable] THEN
  ABBREV_TAC `s = component (H:(A)hypermap) x0` THEN
  SUBGOAL_THEN `(x0:A) IN s /\ ~(y0 IN s)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[component; IN_ELIM_THM; GCOMP_REFL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `map_closed H (s:A->bool) /\ map_closed H (dart H DIFF s)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC COMPONENT_MAP_CLOSED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `dart H DIFF (s:A->bool)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN
  ASM_REWRITE_TAC[four_colorable] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(X_CHOOSE_TAC `k1:A->color`)] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(X_CHOOSE_TAC `k2:A->color`)] THEN
  EXISTS_TAC `\x:A. if x IN s then (k1:A->color) x else k2 x` THEN
  MATCH_MP_TAC SUB_HYPERMAP_COLORING_MERGE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Birkhoff checks: definitions, size facts and their evaluation.        *)
(* ------------------------------------------------------------------------- *)

let cpcard = define
 `(cpcard [] = 2) /\
  (cpcard (CONS (CpR n) cp') = cpcard cp') /\
  (cpcard (CONS CpRr cp') = cpcard cp') /\
  (cpcard (CONS CpY cp') = cpcard cp' + 4) /\
  (cpcard (CONS CpH cp') = cpcard cp' + 6) /\
  (cpcard (CONS CpU cp') = cpcard cp' + 2) /\
  (cpcard (CONS CpK cp') = cpcard cp' + 2) /\
  (cpcard (CONS CpA cp') = cpcard cp')`;;

let ctree_pick_rev_rec = new_recursive_definition ctree_RECURSION
 `(ctree_pick_rev_rec (CtreeLeaf lf) et e target =
     (if ctree_mem target (etrace(BUTLAST(CONS e et))) then CONS e et else
       [])) /\
  (ctree_pick_rev_rec (CtreeNode t1 t2 t3) et e target =
     (let r1 = ctree_pick_rev_rec t1 (CONS Color1 et) (addc e Color1) target in
      if ~(r1 = []) then r1 else
      let r2 = ctree_pick_rev_rec t2 (CONS Color2 et) (addc e Color2) target in
      if ~(r2 = []) then r2 else
      ctree_pick_rev_rec t3 (CONS Color3 et) (addc e Color3) target)) /\
  (ctree_pick_rev_rec CtreeEmpty et e target = [])`;;

let ctree_pick_rev = new_definition
 `ctree_pick_rev a b = ctree_pick_rev_rec b [] Color0 a`;;

let do_Birkhoff_check2 = new_definition
 `do_Birkhoff_check2 h check_basis et ctu gtu chk =
    (if MEM Color0 et then F else
     let pr = kempe_tree_closure (h - 1) h ctu (ctree_of_ttail (etrace et))
       gtu in
     gtree_empty (gtree_pair_sub (SND pr) F) /\
     (check_basis (FST pr) \/ chk (FST pr) (gtree_pair_sub (SND pr) T)))`;;

let birkhoff_check1 = new_definition
 `Birkhoff_check1 h m cp <=>
    cubic_prog cp /\ (cpcard cp) + 1 < 6 * m + 4 * h /\ cprsize cp = h + 1`;;

let birkhoff_check2 = new_recursive_definition num_RECURSION
 `(Birkhoff_check2 h check_basis ctu1 gtu1 0 ctu2 gtu2 = F) /\
  (Birkhoff_check2 h check_basis ctu1 gtu1 (SUC n') ctu2 gtu2 =
     (let cs = ctree_pick_rev ctu1 ctu2 in
      if cs = [] then F else
      do_Birkhoff_check2 h check_basis (BUTLAST cs) ctu1 gtu1
         (Birkhoff_check2 h check_basis ctu2 gtu2 n') /\
      do_Birkhoff_check2 h check_basis (REVERSE(TL cs)) ctu2 gtu2
         (Birkhoff_check2 h check_basis ctu1 gtu1 n')))`;;

let birkhoff_check = new_definition
 `Birkhoff_check h m <=>
    (?niter cps.
        ALL (Birkhoff_check1 h m) cps /\
        Birkhoff_check2 h (\t. EX (ctree_disjoint t) (MAP cpcolor cps))
           (ctree_init_tree h) (gtree_init_tree h) niter
           (ctree_init_tree h) (gtree_init_tree h))`;;

(* Per-step dart-count deltas. ecpU/ecpN(+2) + cpmap0(=2) are in cfmap.ml.   *)
let CARD_DART_ECPR = prove
 (`!(H:(num)hypermap) n x0. CARD(dart(ecpR H n x0)) = CARD(dart H)`,
   REWRITE_TAC[ecpR]);;

let CARD_DART_ECPRR = prove
 (`!(H:(num)hypermap) x0. CARD(dart(ecpRr H x0)) = CARD(dart H)`,
   REWRITE_TAC[ecpRr; ecpR]);;

let CARD_DART_ECPA = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H ==> CARD(dart(ecpA H x0)) = CARD(dart H)`,
  SIMP_TAC[ECPA_DART]);;

(* ecpY = 2 fresh darts over ecpU (ECPY_DART); freshness via                 *)
(* NEW_DART2_FRESH.                                                          *)
let CARD_DART_ECPY = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H ==> CARD(dart(ecpY H x0)) = CARD(dart H) + 4`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(num)hypermap`;`x0:num`] ECPY_DART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `dart(ecpU (H:(num)hypermap) x0)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_DART; IN_INSERT;
               DE_MORGAN_THM] THEN
  ASM_SIMP_TAC[CARD_DART_ECPU] THEN ARITH_TAC);;

(* ecpK = ecpN over ecpRr(=H) (ECPK_DART); ecpN adds 2, ecpRr keeps dart H.  *)
let CARD_DART_ECPK = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H ==> CARD(dart(ecpK H x0)) = CARD(dart H) + 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ecpRr_pt (H:(num)hypermap) x0 IN dart H` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`H:(num)hypermap`;`x0:num`] ECPRR_PT_IN_DART) THEN
    ASM_REWRITE_TAC[ecpRr; ecpR] THEN DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ECPK_DART; ecpRr; ecpR] THEN ASM_SIMP_TAC[CARD_DART_ECPN]);;

(* ecpH = ecpN o ecpY (ecpH def): ecpN adds 2 over ecpY's +4 -> +6.          *)
let CARD_DART_ECPH = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H ==> CARD(dart(ecpH H x0)) = CARD(dart H) + 6`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MP_TAC(ISPECL[`ecpY (H:(num)hypermap) x0`;`ecpY_pt (H:(num)hypermap) x0`]
    CARD_DART_ECPN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ECPY_PT_IN_DART]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[CARD_DART_ECPY] THEN ARITH_TAC);;

(* CARD_CPMAP: a seven-way cpstep case split; the cpstep_apply and cpcard    *)
(* clauses reduce each case to the CARD_DART_ECPR, CARD_DART_ECPY,           *)
(* CARD_DART_ECPK or CARD_DART_ECPH lemma of that step (ecpU and ecpN are in *)
(* cfmap.ml).                                                                *)
let CARD_CPMAP = prove
 (`!cp. CARD(dart(FST(cpmap cp))) = cpcard cp`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[cpmap; ITLIST; FST; CARD_DART_CPMAP0; cpcard];
    MP_TAC(ISPEC `t:(cpstep)list` CPMAP_PT_IN_DART) THEN DISCH_TAC THEN
    STRUCT_CASES_TAC(ISPEC `h:cpstep` (cases "cpstep")) THEN
    ASM_SIMP_TAC[CPMAP_CONS_PAIR; cpstep_apply; cpcard; FST; CARD_DART_ECPR;
                 CARD_DART_ECPRR; CARD_DART_ECPA; CARD_DART_ECPU;
                 CARD_DART_ECPK; CARD_DART_ECPY; CARD_DART_ECPH]]);;

(* SUMT_CTREE_PICK_REV (Coq:96): the invariant addc e (sumt et) = Color0 is  *)
(* preserved in each branch since addc (addc e c) c = e.                     *)
let SUMT_CTREE_PICK_REV = prove
 (`!a b. sumt(ctree_pick_rev a b) = Color0`,
  REWRITE_TAC[ctree_pick_rev] THEN
  SUBGOAL_THEN
   `!b et e tt. addc e (sumt et) = Color0
                ==> sumt(ctree_pick_rev_rec b et e tt) = Color0`
   (fun th -> REPEAT GEN_TAC THEN MATCH_MP_TAC th THEN
              REWRITE_TAC[sumt; ADDC_0_RIGHT]) THEN
  MATCH_MP_TAC ctree_INDUCT THEN REWRITE_TAC[ctree_pick_rev_rec; sumt] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[sumt; ADDC_ASSOC; ADDC_CANCEL];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[sumt]]);;

(* SIZE_CTREE_PICK_REV (Coq:110): with the invariant LENGTH et + n = h for   *)
(* a subtree of height n reached along et, the result is either [] (no trace *)
(* found) or a full trace of length h + 1.                                   *)
let SIZE_CTREE_PICK_REV = prove
 (`!h a b. ctree_proper h b
           ==> LENGTH(ctree_pick_rev a b) = 0 \/
               LENGTH(ctree_pick_rev a b) = h + 1`,
  GEN_TAC THEN REWRITE_TAC[ctree_pick_rev] THEN
  SUBGOAL_THEN
   `!b n et e tt. ctree_proper n b /\ LENGTH et + n = h
        ==> LENGTH(ctree_pick_rev_rec b et e tt) = 0 \/
            LENGTH(ctree_pick_rev_rec b et e tt) = h + 1`
   (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN
              EXISTS_TAC `h:num` THEN
              ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES]) THEN
  MATCH_MP_TAC ctree_INDUCT THEN
  REWRITE_TAC[ctree_pick_rev_rec; ctree_proper; LENGTH] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `n - 1`) THEN
    ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC]);;

(* Generic CBV helpers, also used by part2_eval.ml and redpart_eval.ml.      *)
let suc_rec_conv clauses argpos tm =
  let f,args = strip_comb tm in
  let k = length args in
  let n = el argpos args in
  if not (is_numeral n) then failwith "suc_rec_conv: not a numeral"
  else if dest_numeral n = num_0 then GEN_REWRITE_CONV I [clauses] tm
  else (funpow (k-1-argpos) RATOR_CONV (RAND_CONV num_CONV) THENC
    GEN_REWRITE_CONV I [clauses]) tm;;

(* f .. 0 .. = a /\ f .. (SUC m) .. = b   ==>   f .. m .. = if m = 0 then a  *)
(*                                         else b[m := m - 1]                *)
let NUM_FORM th =
  let c0,c1 = CONJ_PAIR th in
  let c0 = SPEC_ALL c0 and c1 = SPEC_ALL c1 in
  let l1,b = dest_eq(concl c1) in
  let f,args1 = strip_comb l1 in
  let pos = index true (map (fun a -> is_comb a && rator a = `SUC`) args1) in
  let m = rand (el pos args1) in
  let l0,a = dest_eq(concl c0) in
  let args0 = snd(strip_comb l0) in
  let pairs = filter (fun (x,y) -> x <> y && not (is_numeral y)) (zip args1
    args0) in
  let a' = vsubst pairs a in
  let newargs = map (fun i -> if i = pos then m else el i args1) (0 -- (length
    args1 - 1)) in
  let lhs_new = list_mk_comb(f, newargs) in
  let b' = vsubst [mk_binop `(-):num->num->num` m `1`, m] b in
  let rhs_new = mk_cond(mk_eq(m, `0`), a', b') in
  let stmt = list_mk_forall(frees lhs_new, mk_eq(lhs_new, rhs_new)) in
  prove(stmt, REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC m num_CASES) THEN
    REWRITE_TAC[th; NOT_SUC; SUC_SUB1]);;

let has_suc_arg l = exists (fun a -> is_comb a && rator a = `SUC`)
  (snd(strip_comb l));;

let has_suc_pattern th =
  exists (fun c -> try has_suc_arg (lhs(snd(strip_forall(concl c)))) with
    Failure _ -> false) (CONJUNCTS th);;

let suc_arg_info th =
  let c = find (fun c -> has_suc_arg (lhs(snd(strip_forall(concl c)))))
    (CONJUNCTS th) in
  let f,args = strip_comb (lhs(snd(strip_forall(concl c)))) in
  (f, length args, index true (map (fun a -> is_comb a && rator a = `SUC`)
    args));;

(* add a definition: plain rewrite, or NUM_FORM / suc_rec_conv for           *)
(* SUC-pattern recursions                                                    *)
let add_def cs (name, th) =
  try
    if not (has_suc_pattern th) then Compute.add_thms [th] cs
    else (try Compute.add_thms [NUM_FORM th] cs
          with _ -> let (f,ar,pos) = suc_arg_info th in
                    Compute.add_conv (f, ar, suc_rec_conv th pos) cs;
                      Printf.printf "suc_rec_conv %s\n%!" name)
  with Failure s -> Printf.printf "SKIP %s: %s\n%!" name s;;

let both_dirs th = CONJUNCTS th @ CONJUNCTS (CONV_RULE (ONCE_DEPTH_CONV
  SYM_CONV) th);;

let add_type_eqs cs tys = List.iter (fun ty ->
   (try Compute.add_thms (both_dirs (distinctness ty)) cs with _ -> ());
   (try Compute.add_thms [injectivity ty] cs with _ -> ())) tys;;

(* The constructor clauses of cpcard, cpcolor1 and cpcolor0 (the definitions *)
(* themselves), in constructor order CpR n, CpRr, CpY, CpH, CpU, CpK, CpA.   *)
let CPCARD_CASES = tl (CONJUNCTS cpcard);;

let CPCOLOR1_CASES = CONJUNCTS cpcolor1;;

let CPCOLOR0_CASES = tl (CONJUNCTS cpcolor0);;

let GTREE_MEM_CLAUSES = gtree_mem;;

let CUBIC_PROG_CLAUSES = prove
 (`cubic_prog [] /\ (!s cp. cubic_prog (CONS s cp) <=> cubic_step s /\
    cubic_prog cp)`,
  REWRITE_TAC[cubic_prog; ALL]);;

let CUBIC_STEP_CLAUSES = prove
 (`(!n. cubic_step (CpR n)) /\ cubic_step CpU /\ cubic_step CpY /\ cubic_step
    CpH /\
   ~cubic_step CpK /\ ~cubic_step CpA /\ ~cubic_step CpRr`,
  REWRITE_TAC[cubic_step]);;

(* cprsize of a concrete program: cfmap.ml's CPRSIZE_NIL, CPRSIZE_CONS_Y,    *)
(* CPRSIZE_CONS_U, CPRSIZE_CONS_R, and CPRSIZE_CONS_H under proper_cpring,   *)
(* which CPMAP_PROPER gives from cubic_prog.                                 *)
let cprsize_conv tm =
  (SIMP_CONV[CPRSIZE_NIL; CPRSIZE_CONS_Y; CPRSIZE_CONS_U; CPRSIZE_CONS_R;
   CPRSIZE_CONS_H; CPMAP_PROPER;
             CUBIC_PROG_CLAUSES;
              CUBIC_STEP_CLAUSES] THENC NUM_REDUCE_CONV) tm;;

let birkhoff_compset () =
  let cs = Compute.bool_compset() in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  List.iter (fun c -> Compute.add_conv c cs)
    [(`SUC`, 1, NUM_SUC_CONV); (`(+):num->num->num`, 2, NUM_ADD_CONV);
     (`(-):num->num->num`, 2, NUM_SUB_CONV);
     (`(*):num->num->num`, 2, NUM_MULT_CONV);
      (`(<):num->num->bool`, 2, NUM_LT_CONV);
     (`(<=):num->num->bool`, 2, NUM_LE_CONV);
      (`(=):num->num->bool`, 2, NUM_EQ_CONV);
     (`cprsize`, 1, cprsize_conv)];
  add_type_eqs cs ["cpstep"; "color"; "ctree"; "gtree"; "bit_stack";
    "ctree_restriction"; "gtree_restriction";
                   "gram_symbol"; "edge_perm"; "gtree_pair"; "ctree_pair"];
  Compute.add_thms [REFL_CLAUSE; FST; SND; LET_END_DEF; LENGTH; HD; TL;
   APPEND; ALL; EX; MAP; FILTER; MEM; REVERSE;
                    BUTLAST; LAST; ITLIST; NOT_CONS_NIL; REPLICATE_NUM;
                     EL_NUM; NUM_FORM ITER] cs;
  List.iter (add_def cs)
   [("addc_DEF",addc_DEF);("permc_DEF",permc_DEF);
   ("edge_rot_DEF",edge_rot_DEF);("cbit0",cbit0);("cbit1",cbit1);
   ("ccons",ccons);
    ("inv_eperm",inv_eperm);("ptrace",ptrace);("sumt",sumt);("ctrace",ctrace);
    ("permt",permt);("head_color",head_color);
    ("proper_trace",proper_trace);("trace_DEF",trace_DEF);("untrace",untrace);
    ("even_tail",even_tail);("ttail",ttail);
    ("even_trace",even_trace);("etrace_perm",etrace_perm);("etrace",etrace);
    ("etail",etail);("eptrace",eptrace);
    ("palette",palette);("ctree_empty",ctree_empty);("ctree_leaf",ctree_leaf);
    ("ctree_empty_node",ctree_empty_node);
    ("ctree_lsub",ctree_lsub);("ctree_msub",ctree_msub);
    ("ctree_rsub",ctree_rsub);("ctree_sel",ctree_sel);("ctree_sub",ctree_sub);
    ("ctree_mem",ctree_mem);("ctree_empty_pair",ctree_empty_pair);
    ("ctree_pair_sub",ctree_pair_sub);("ctree_leaf_of",ctree_leaf_of);
    ("ctree_cons",ctree_cons);("ctree_cons0",ctree_cons0);
    ("ctree_cons1",ctree_cons1);("ctree_cons2",ctree_cons2);
    ("ctree_cons3",ctree_cons3);
    ("ctree_simple_leaf",ctree_simple_leaf);("ctree_cons_e",ctree_cons_e);
    ("ctree_of_ttail",ctree_of_ttail);("ctree_union",ctree_union);
    ("ctree_rotl",ctree_rotl);("ctree_rotr",ctree_rotr);
    ("ctree_cons_rot",ctree_cons_rot);("ctree_union_rotlr",ctree_union_rotlr);
    ("ctree_rotlr",ctree_rotlr);("ctree_disjoint",ctree_disjoint);
    ("gtree_empty",gtree_empty);("gtree_isleaf",gtree_isleaf);
    ("gtree_sel",gtree_sel);("gtree_leaf_mem",gtree_leaf_mem);
    ("GTREE_MEM_CLAUSES",GTREE_MEM_CLAUSES);
    ("case_bitstack",case_bitstack);("has_match_fn",has_match_fn);
    ("has_match",has_match);("match_count_fn",match_count_fn);
    ("match_count",match_count);
    ("gtree_sub",gtree_sub);("gtree_empty_and",gtree_empty_and);
    ("gtree_empty4",gtree_empty4);("empty_gtree_pair",empty_gtree_pair);
    ("gtree_pair_sub",gtree_pair_sub);
    ("gtree_pair_partition",gtree_pair_partition);
    ("gtree_cons_pairs",gtree_cons_pairs);
    ("gen_dyck_fn",gen_dyck_fn);("gen_dyck",gen_dyck);("dyck",dyck);
    ("count_cbit1",count_cbit1);("ctree_table_sub",ctree_table_sub);
    ("iteri_ctree",iteri_ctree);("ctree_add_dyck_fn",ctree_add_dyck_fn);
    ("ctree_add_dyck",ctree_add_dyck);("leaf_from1_fn",leaf_from1_fn);
    ("ctree_leaf_table_from",ctree_leaf_table_from);
    ("ctree_leaf_table",ctree_leaf_table);
    ("ctree_merge_pair",ctree_merge_pair);("ctree_pairmap",ctree_pairmap);
    ("ctree_merge_table",ctree_merge_table);("ctree_prune_1",ctree_prune_1);
    ("ctree_prune_2",ctree_prune_2);("ctree_prune_3",ctree_prune_3);
    ("ctree_init_tree",ctree_init_tree);
    ("init_gtree_h1",init_gtree_h1);("gtree_merge_pairs",gtree_merge_pairs);
    ("gtree_table_sub",gtree_table_sub);
    ("gtree_merge_line_fn",gtree_merge_line_fn);
    ("gtree_merge_line",gtree_merge_line);
    ("gtree_init_table_fn",gtree_init_table_fn);
    ("gtree_init_table",gtree_init_table);("gtree_init_tree",gtree_init_tree);
    ("gtr_mem",gtr_mem);("gtr_cons",gtr_cons);("gtr_isnil",gtr_isnil);
    ("case_ctree_node",case_ctree_node);("cons_pop",cons_pop);
    ("gtr_split_fn",gtr_split_fn);("gtr_split",gtr_split);("gsplit",gsplit);
    ("gtr_match0",gtr_match0);("gtr_match1",gtr_match1);
    ("gtr_match2",gtr_match2);("gtr_match3",gtr_match3);
    ("gtp_0_e",gtp_0_e);("gtp_1_e",gtp_1_e);("gtp_2_e",gtp_2_e);
    ("gtp_3_e",gtp_3_e);("gtp_01_e",gtp_01_e);("gtp_12_e",gtp_12_e);
    ("gtp_13_e",gtp_13_e);("gtp_23_e",gtp_23_e);("gtp_e_0",gtp_e_0);
    ("gtp_e_1",gtp_e_1);("gtp_e_2",gtp_e_2);("gtp_e_3",gtp_e_3);
    ("gtp_e_01",gtp_e_01);("gtp_e_12",gtp_e_12);("gtp_e_13",gtp_e_13);
    ("gtp_e_23",gtp_e_23);("gtp_0_1",gtp_0_1);("gtp_1_0",gtp_1_0);
    ("gtp_1_2",gtp_1_2);("gtp_2_1",gtp_2_1);("gtp_1_3",gtp_1_3);
    ("gtp_3_1",gtp_3_1);("gtp_2_3",gtp_2_3);("gtp_3_2",gtp_3_2);
    ("gtree_restrict",gtree_restrict);
    ("ctr_cons",ctr_cons);("ctr_sub",ctr_sub);
    ("case_gtree_node",case_gtree_node);("ctr_cons_pop",ctr_cons_pop);
    ("ctr_split_fn",ctr_split_fn);
    ("ctr_split",ctr_split);("csplit",csplit);
    ("ctree_leaf_child",ctree_leaf_child);("ctree_decr",ctree_decr);
    ("ctr_e_decr",ctr_e_decr);
    ("ctr_decr",ctr_decr);("cdecr",cdecr);
    ("ctree_cons_pairs",ctree_cons_pairs);("ctree_partition",ctree_partition);
    ("ctree_if_e",ctree_if_e);
    ("ctree_leaf_pair",ctree_leaf_pair);("ctr_isnil",ctr_isnil);
    ("ctree_restrict_fn",ctree_restrict_fn);("ctree_restrict",ctree_restrict);
    ("ctree_size",ctree_size);("ctrace_a",ctrace_a);("ktc_step",ktc_step);
    ("ktc_stepp",ktc_stepp);
    ("kempe_tree_closure_fn",kempe_tree_closure_fn);
    ("kempe_tree_closure",kempe_tree_closure);
    ("take_list",take_list);("drop_list",drop_list);("rot_list",rot_list);
    ("rotr_list",rotr_list);
    ("ctree_cons_perm",ctree_cons_perm);("cfcbr2",cfcbr2);("cfcbr1",cfcbr1);
    ("cpbranch",cpbranch);("cpcolor",cpcolor);
    ("ctree_pick_rev_rec",ctree_pick_rev_rec);
    ("ctree_pick_rev",ctree_pick_rev);
    ("do_Birkhoff_check2",do_Birkhoff_check2);
    ("birkhoff_check1",birkhoff_check1);("birkhoff_check2",birkhoff_check2)];
  Compute.add_thms (CPCARD_CASES @ CPCOLOR1_CASES @ CPCOLOR0_CASES @
                    [CONJUNCT1 cpcolor0; CONJUNCT1 cpcard; CUBIC_PROG_CLAUSES;
                     CUBIC_STEP_CLAUSES]) cs;
  cs;;

let the_birkhoff_compset = birkhoff_compset();;

(* Birkhoff_check h m (Coq birkhoff.v Birkhoff2..5): supply the iteration    *)
(* count niter and the basis programs cps, then evaluate.                    *)
let BIRKHOFF_CHECK_TAC cs niter cps =
  REWRITE_TAC[birkhoff_check] THEN EXISTS_TAC (mk_small_numeral niter) THEN
  EXISTS_TAC (mk_list(cps, `:cpstep list`)) THEN
    CONV_TAC(Compute.CBV_CONV cs);;

let timed_birkhoff name tac =
  let t0 = Sys.time() in
  let th = prove(name, tac) in
  Printf.printf "BIRKHOFF_EVAL: %s proved in %.1f s\n%!" (string_of_term
    (concl th)) (Sys.time() -. t0); th;;

let BIRKHOFF_CHECK_1_0 = timed_birkhoff `Birkhoff_check 1 0`
  (BIRKHOFF_CHECK_TAC the_birkhoff_compset 1 [`[]:cpstep list`]);;

let BIRKHOFF_CHECK_2_0 = timed_birkhoff `Birkhoff_check 2 0`
  (BIRKHOFF_CHECK_TAC the_birkhoff_compset 1 [`[CpY]`]);;

let BIRKHOFF_CHECK_3_0 = timed_birkhoff `Birkhoff_check 3 0`
  (BIRKHOFF_CHECK_TAC the_birkhoff_compset 4 [`[CpU]`; `[CpR 1; CpU]`]);;

let BIRKHOFF_CHECK_4_1 = timed_birkhoff `Birkhoff_check 4 1`
  (BIRKHOFF_CHECK_TAC the_birkhoff_compset 10
     [`[CpU; CpY]`; `[CpR 1; CpU; CpY]`; `[CpR 2; CpU; CpY]`; `[CpR 3; CpU;
      CpY]`; `[CpR 4; CpU; CpY]`;
      `[CpH; CpR 4; CpY; CpY; CpY]`]);;

(* Gonthier's names Birkhoff2 .. Birkhoff5.                                  *)

let birkhoff2 = BIRKHOFF_CHECK_1_0;;

let birkhoff3 = BIRKHOFF_CHECK_2_0;;

let birkhoff4 = BIRKHOFF_CHECK_3_0;;

let birkhoff5 = BIRKHOFF_CHECK_4_1;;

(* ------------------------------------------------------------------------- *)
(* Face bands and face counts (Coq geometry.v simple_fcard_fband,            *)
(* scycle_fcard_fband; the annulus arF of birkhoff.v).                       *)
(* ------------------------------------------------------------------------- *)

let IN_FBAND = prove
 (`!(H:(A)hypermap) p x. x IN fband H p <=> fband H p x`,
  REWRITE_TAC[IN]);;

let FBAND_IN_DART = prove
 (`!(H:(A)hypermap) p z.
     ALL (\y. y IN dart H) p /\ fband H p z ==> z IN dart H`,
  REWRITE_TAC[FBAND_MEM_IFF; GSYM ALL_MEM] THEN
  MESON_TAC[CFACE_SYM_GEN; CFT_DART]);;

let FINITE_FBAND = prove
 (`!(H:(A)hypermap) p. ALL (\y. y IN dart H) p ==> FINITE (fband H p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `dart (H:(A)hypermap)` THEN
  REWRITE_TAC[FINITE_DART; SUBSET; IN_FBAND] THEN
  ASM_MESON_TAC[FBAND_IN_DART]);;

let DISKFC_CFACE = prove
 (`!(H:(A)hypermap) r z x.
     z IN dart H /\ cface H z x ==> (diskFC H r z <=> diskFC H r x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  ASM_SIMP_TAC[DISKFC_FACE; ITER_PERMUTES_IN; FACE_MAP_PERMUTES]);;

let SIMPLE_FCARD_FBAND = prove
 (`!(H:(A)hypermap) r.
     ALL (\y. y IN dart H) r /\ face_simple H r
     ==> fcard_face H (fband H r) = LENGTH r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE] THEN
  SUBGOAL_THEN
   `IMAGE (orbit_map (face_map H)) (fband H r) =
    IMAGE (orbit_map (face_map H)) (set_of_list (r:(A)list))`
   SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_SET_OF_LIST; IN_FBAND; FBAND_MEM_IFF] THEN
    X_GEN_TAC `s:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:A) IN dart H /\ (z:A) IN dart H` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[ALL_MEM; CFACE_SYM_GEN; CFT_DART];
        ASM_SIMP_TAC[ORBIT_EQ_CFACE]];
      DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[CFACE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\x y:A. ~(x = y)) r` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_SIMPLE_PAIRWISE_GEN]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(set_of_list (r:(A)list)) = LENGTH r`
  (SUBST1_TAC o SYM) THENL
   [ASM_MESON_TAC[HAS_SIZE_SET_OF_LIST; HAS_SIZE]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  REWRITE_TAC[FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  ASM_MESON_TAC[ALL_MEM; ORBIT_EQ_CFACE; CFT_FACE_SIMPLE]);;

let SCYCLE_FCARD_FBAND = prove
 (`!(H:(A)hypermap) e r.
     ALL (\y. y IN dart H) r /\ scycle H e r
     ==> fcard_face H (fband H r) = LENGTH r`,
  MESON_TAC[SIMPLE_FCARD_FBAND; SCYCLE_SIMPLE]);;

let FCARD_FACE_UNION_DISJOINT = prove
 (`!(H:(A)hypermap) a b:A->bool.
     FINITE a /\ FINITE b /\
     (!x. x IN a ==> face_map H x IN a) /\
     (!x. x IN b ==> face_map H x IN b) /\
     a INTER b = {}
     ==> fcard_face H (a UNION b) = fcard_face H a + fcard_face H b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE; IMAGE_UNION] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `s:A->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(p:A) IN b` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `b:A->bool`; `q:A`]
      ORBIT_IN_CLOSED) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[IN_ORBIT_MAP_REFL];
    ASM SET_TAC[]]);;

let FCARD_FACE_ARF = prove
 (`!(H:(A)hypermap) e r.
     ALL (\y. y IN dart H) r /\ scycle H e r
     ==> fcard_face H (fband H r UNION {x | x IN dart H /\ diskFC H r x})
         = LENGTH r + fcard_face H {x | x IN dart H /\ diskFC H r x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`;`fband (H:(A)hypermap) r`;
                `{x:A | x IN dart H /\ diskFC H r x}`]
                  FCARD_FACE_UNION_DISJOINT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_FBAND; FINITE_DISKFC_DART] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_FBAND] THEN DISCH_TAC THEN
      ASM_MESON_TAC[FBAND_IN_DART; FBAND_FACE_MAP_EQ];
      X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_SIMP_TAC[FACE_MAP_IN_DART; DISKFC_FACE];
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM; IN_FBAND;
                  diskFC] THEN MESON_TAC[]];
    DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[SCYCLE_FCARD_FBAND]]);;

(* ------------------------------------------------------------------------- *)
(* The Euler count of the remainder of a nontrivial ring (Coq birkhoff.v,    *)
(* the size bound inside Birkhoff_valid): it has more darts than any         *)
(* Birkhoff_check1 configuration.                                            *)
(* ------------------------------------------------------------------------- *)

let NCOMP_SNIP_REM = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ connected_hypermap H /\ scycle H (rlink H) r /\
     ALL (\y:A. y IN dart H) r /\ 2 <= LENGTH r
     ==> number_of_components (snip_rem H r) = 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r:(A)list = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_PATCH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] COMPONENTS_PATCH)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MEM (HD r) (r:(A)list)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HD_MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `HD r IN dart H /\ HD r IN diskN H r /\
                HD r IN redart (H:(A)hypermap) r`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[RING_MEM_DART];
      REWRITE_TAC[IN] THEN MATCH_MP_TAC RING_SUBSET_DISKN THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_REDART] THEN
      ASM_MESON_TAC[RING_MEM_DART; RING_NOT_DISKE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(dart (H:(A)hypermap) = {}) /\
                ~(dart (snip_disk H r) = {}) /\ ~(dart (snip_rem H r) = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_REM_COMPONENTS) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_DISK_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `snip_disk (H:(A)hypermap) r` NCOMP_POS) THEN
  MP_TAC(ISPEC `snip_rem (H:(A)hypermap) r` NCOMP_POS) THEN
  MP_TAC(ISPEC `H:(A)hypermap` CONNECTED_NCOMP) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let NODES_QUASICUBIC = prove
 (`!(G:(A)hypermap) r.
     list_cycle (\x y. node_map G x = y) r /\ PAIRWISE (\x y. ~(x = y)) r /\
     ALL (\y. y IN dart G) r /\ ~(r = []) /\ quasicubic G (\z. MEM z r)
     ==> 3 * number_of_nodes G + LENGTH r = CARD(dart G) + 3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_CYCLE_F_CLOSED) THEN
  SUBGOAL_THEN `!z:A. MEM z r ==> z IN dart G` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\y:A. y IN dart G) r` THEN REWRITE_TAC[ALL_MEM] THEN
    SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `set_of_list r SUBSET dart (G:(A)hypermap)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET; IN_SET_OF_LIST]; ALL_TAC] THEN
  REWRITE_TAC[number_of_nodes; node_set] THEN
  MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`;
                 `set_of_list (r:(A)list)`] CARD_ORBITS_SPLIT) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; IN_SET_OF_LIST] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `set_of_orbits (set_of_list r) (node_map (G:(A)hypermap)) =
    {set_of_list r}`
  SUBST1_TAC THENL
   [REWRITE_TAC[SET_OF_ORBITS_IMAGE] THEN
    SUBGOAL_THEN
     `IMAGE (orbit_map (node_map (G:(A)hypermap))) (set_of_list r) =
      IMAGE (\x. set_of_list r) (set_of_list r)`
    SUBST1_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[IMAGE_CONST] THEN ASM_REWRITE_TAC[SET_OF_LIST_EQ_EMPTY]] THEN
    MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_SET_OF_LIST] THEN DISCH_TAC THEN
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST] THEN X_GEN_TAC `y:A` THEN
    MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `r:(A)list`; `x:A`]
                  ORBIT_CYCLE_MEM) THEN
    MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`;
                   `r:(A)list`; `x:A`] LIST_CYCLE_MEM_ORBIT) THEN
    ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`;
                 `dart G DIFF set_of_list (r:(A)list)`; `3`]
                UNIFORM_ORBIT_CARD_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; SUBSET_DIFF] THEN
    MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`;
                   `set_of_list (r:(A)list)`] PERM_COMPL_CLOSED) THEN
    ASM_REWRITE_TAC[FINITE_DART; IN_SET_OF_LIST] THEN
    ANTS_TAC THENL [MESON_TAC[NODEI]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; IN_SET_OF_LIST] THEN DISCH_TAC THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[quasicubic]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(dart G DIFF set_of_list r) + LENGTH (r:(A)list) =
    CARD(dart (G:(A)hypermap))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`dart (G:(A)hypermap)`; `set_of_list (r:(A)list)`]
                  CARD_DIFF) THEN
    MP_TAC(ISPECL [`set_of_list (r:(A)list)`; `dart (G:(A)hypermap)`]
                  CARD_SUBSET) THEN
    ASM_SIMP_TAC[FINITE_DART; CARD_SET_OF_LIST_PAIRWISE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY] THEN ARITH_TAC);;

let FACES_SNIP_REM_GE = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ scycle H (rlink H) r /\
     ALL (\y:A. y IN dart H) r /\ 2 <= LENGTH r
     ==> LENGTH r + fcard_face H {x | x IN dart H /\ diskFC H r x}
         <= number_of_faces (snip_rem H r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r:(A)list = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_PATCH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] PATCH_FACES_OUTER)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rlink (H:(A)hypermap)`; `r:(A)list`]
                FCARD_FACE_ARF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET;
    MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `dart(H:(A)hypermap)` THEN
    SIMP_TAC[FINITE_DART; SUBSET; IN_ELIM_THM]] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_REM_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (\x:A. x) (redart H r) = redart H r` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; CFACE_ORBIT; IN_FBAND;
              FBAND_MEM_IFF; IN_REDART] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THENL
   [CONJ_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `y:A` THEN ASM_SIMP_TAC[RING_NOT_DISKE] THEN CFACE_TAC[];
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[CFACE_REFL] THEN
    UNDISCH_TAC `diskFC (H:(A)hypermap) r x` THEN
    REWRITE_TAC[diskFC; diskE] THEN MESON_TAC[]]);;

let CPCARD_LT_REDART = prove
 (`!(H:(A)hypermap) r n m cp.
      planar_hypermap H /\ plain_hypermap H /\ cubic_hypermap H /\
      connected_hypermap H /\
      scycle H (rlink H) r /\ ALL (\y:A. y IN dart H) r /\
      LENGTH r = n + 1 /\ 2 <= LENGTH r /\
      nontrivial_ring H m r /\ Birkhoff_check1 n m cp
      ==> cpcard cp < CARD(redart H r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r:(A)list = []) /\ 2 <= n + 1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_PATCH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `G = snip_rem (H:(A)hypermap) r` THEN
  SUBGOAL_THEN `dart (G:(A)hypermap) = redart H r /\
                node_map G = snipr_node H r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_REM_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] PLANAR_SNIPR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `snip_disk (H:(A)hypermap) r`;
                 `G:(A)hypermap`; `\x:A. x`; `\x:A. x`; `r:(A)list`;
                 `REVERSE (r:(A)list)`] CUBIC_PATCH) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `snip_disk (H:(A)hypermap) r`;
                 `G:(A)hypermap`; `\x:A. x`; `\x:A. x`; `r:(A)list`;
                 `REVERSE (r:(A)list)`] PLAIN_PATCH) THEN
  ASM_REWRITE_TAC[LENGTH_REVERSE] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `REVERSE (r:(A)list)`] NODES_QUASICUBIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REVERSE_EQ_EMPTY; ALL_REVERSE] THEN
    SUBGOAL_THEN `PAIRWISE (\x y:A. ~(x = y)) (REVERSE r)` ASSUME_TAC THENL
     [MATCH_MP_TAC PAIRWISE_DISTINCT_REVERSE THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `rlink (H:(A)hypermap)`; `r:(A)list`]
                    SCYCLE_PAIRWISE) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALL (\y:A. y IN redart H r) r` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM ALL_MEM; IN_REDART] THEN X_GEN_TAC `z:A` THEN
      DISCH_TAC THEN ASM_SIMP_TAC[RING_NOT_DISKE] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `z:A`] RING_MEM_DART) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [patch]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] NCOMP_SNIP_REM) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] FACES_SNIP_REM_GE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `G:(A)hypermap` PLAIN_DART_CARD) THEN
  MP_TAC(ISPEC `G:(A)hypermap` EVEN_GENUS) THEN
  ASM_REWRITE_TAC[even_genus; euler_lhs; euler_rhs] THEN
  UNDISCH_TAC `planar_hypermap (G:(A)hypermap)` THEN
  REWRITE_TAC[planar_hypermap] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `nontrivial_ring (H:(A)hypermap) m r` THEN
  UNDISCH_TAC `Birkhoff_check1 n m cp` THEN
  REWRITE_TAC[nontrivial_ring; birkhoff_check1; LENGTH_REVERSE] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Orbit sizes across a patch, and patches of cubic, plain and bridgeless    *)
(* maps (Coq patch.v cubic_patch, plain_patch, bridgeless_patch).            *)
(* ------------------------------------------------------------------------- *)

let EDGE_OFF_BORDER_D = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> !x. x IN dart Gd /\ ~MEM x bGd ==> ~MEM (edge_map Gd x) bGd`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
  MATCH_MP_TAC PERM_COMPL_CLOSED THEN REWRITE_TAC[FINITE_DART; ETA_AX] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_BGD_IN_DART; ALL_MEM];
    MESON_TAC[EDGEI];
    REWRITE_TAC[IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_CYCLE_D; scycle; LIST_CYCLE_F_CLOSED]]);;

let NODE_OFF_BORDER_R = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGr
     ==> !y. y IN dart Gr /\ ~MEM y bGr ==> ~MEM (node_map Gr y) bGr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
  MATCH_MP_TAC PERM_COMPL_CLOSED THEN REWRITE_TAC[FINITE_DART; ETA_AX] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_BGR_IN_DART; ALL_MEM];
    MESON_TAC[NODEI];
    REWRITE_TAC[IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_CYCLE_R; LIST_CYCLE_F_CLOSED]]);;

let ORBIT_SIZE_TRANSPORT = prove
 (`!(f:A->A) (g:B->B) s h.
     FINITE s /\
     (!y. y IN s ==> f y IN s) /\
     (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y) /\
     (!x. x IN s ==> h (f x) = g (h x))
     ==> !x. x IN s ==> orbit_size g (h x) = orbit_size f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[orbit_size] THEN
  MP_TAC(ISPECL [`f:A->A`; `g:B->B`; `s:A->bool`; `h:A->B`]
    IMAGE_ORBIT_INTERTWINE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_IN_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; FINITE_SUBSET]);;

let PATCH_BORDER_EDGE_GR_BRIDGE = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) (hd:A->B) (hr:E->B)
    (bGd:(A)list) (bGr:(E)list) (yd:A).
      patch G Gd Gr hd hr bGd bGr /\ 2 <= LENGTH bGd /\
      MEM yd bGd /\ cface G (hd yd) (hd (edge_map Gd yd))
      ==> ?w:E. w IN dart Gr /\ cface Gr w (edge_map Gr w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL (\z:A. z IN dart Gd) bGd` ASSUME_TAC THENL
   [ASM_MESON_TAC[PATCH_BGD_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (edge_map Gd (yd:A)) bGd` ASSUME_TAC THENL
   [ASM_MESON_TAC[PATCH_CYCLE_D; scycle; LIST_CYCLE_F_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `?xr:E. MEM xr bGr /\ (hr:E->B) xr = hd (edge_map Gd (yd:A))`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `MEM ((hd:A->B) (edge_map Gd (yd:A))) (MAP hr (bGr:(E)list))`
     MP_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PATCH_MAP_RING_R th]) THEN
      REWRITE_TAC[MEM_REVERSE; MEM_MAP] THEN ASM_MESON_TAC[];
      REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                 `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`; `xr:E`]
    PATCH_BGRP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xd:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(xd:A) = yd` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[INJ] o MATCH_MP PATCH_INJ_HD) THEN
    ASM_MESON_TAC[ALL_MEM; EDGE_MAP_IN_DART; EDGEI];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xr:E) IN dart Gr /\ node_map Gr xr IN dart Gr`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATCH_BGR_IN_DART; ALL_MEM; NODE_MAP_IN_DART;
                  PATCH_MAP_RING_R; LENGTH_MAP; LENGTH_REVERSE];
    ALL_TAC] THEN
  EXISTS_TAC `node_map Gr (xr:E)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cface Gr (node_map Gr (xr:E)) xr` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_CFACE_HR o C CONJ
      (ASSUME `2 <= LENGTH (bGd:(A)list)`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`node_map Gr (xr:E)`; `xr:E`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CFACE_TAC[];
    CFACE_TAC[]]);;

let PATCH_ORBIT_SIZES = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> (!x. x IN dart Gd
              ==> orbit_size (node_map G) (hd x) =
                  orbit_size (node_map Gd) x) /\
         (!x. x IN dart Gd /\ ~MEM x bGd
              ==> orbit_size (edge_map G) (hd x) =
                  orbit_size (edge_map Gd) x) /\
         (!y. y IN dart Gr
              ==> orbit_size (edge_map G) (hr y) =
                  orbit_size (edge_map Gr) y) /\
         (!y. y IN dart Gr /\ ~MEM y bGr
              ==> orbit_size (node_map G) (hr y) =
                  orbit_size (node_map Gr) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[INJ] o
              MATCH_MP PATCH_INJ_HD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[INJ] o
              MATCH_MP PATCH_INJ_HR) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_NODE_D) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_EDGE_D) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_NODE_R) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_EDGE_R) THEN
  SUBGOAL_THEN `LENGTH (bGr:(E)list) = LENGTH (bGd:(A)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_MAP_RING_R) THEN
    DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(B)list->num`) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_REVERSE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(B)hypermap`;`Gd:(A)hypermap`;`Gr:(E)hypermap`;`hd:A->B`;
                 `hr:E->B`;`bGd:(A)list`;`bGr:(E)list`] EDGE_OFF_BORDER_D) THEN
  MP_TAC(ISPECL [`G:(B)hypermap`;`Gd:(A)hypermap`;`Gr:(E)hypermap`;`hd:A->B`;
                 `hr:E->B`;`bGd:(A)list`;`bGr:(E)list`] NODE_OFF_BORDER_R) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`node_map (Gd:(A)hypermap)`; `node_map (G:(B)hypermap)`;
                   `dart (Gd:(A)hypermap)`; `hd:A->B`] ORBIT_SIZE_TRANSPORT);
    MP_TAC(ISPECL [`edge_map (Gd:(A)hypermap)`; `edge_map (G:(B)hypermap)`;
                   `{x:A | x IN dart Gd /\ ~MEM x bGd}`; `hd:A->B`]
      ORBIT_SIZE_TRANSPORT);
    MP_TAC(ISPECL [`edge_map (Gr:(E)hypermap)`; `edge_map (G:(B)hypermap)`;
                   `dart (Gr:(E)hypermap)`; `hr:E->B`] ORBIT_SIZE_TRANSPORT);
    MP_TAC(ISPECL [`node_map (Gr:(E)hypermap)`; `node_map (G:(B)hypermap)`;
                   `{y:E | y IN dart Gr /\ ~MEM y bGr}`; `hr:E->B`]
      ORBIT_SIZE_TRANSPORT)] THEN
  (ANTS_TAC THENL
    [ASM_SIMP_TAC[FINITE_DART; NODE_MAP_IN_DART; EDGE_MAP_IN_DART; IN_ELIM_THM;
                  FINITE_RESTRICT] THEN
     REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
     ASM_MESON_TAC[];
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]]));;

let CUBIC_PATCH_D = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     cubic_hypermap G
     ==> cubic_hypermap Gd`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_ORBIT_SIZES o C CONJ
    (ASSUME `2 <= LENGTH (bGd:(A)list)`)) THEN
  REWRITE_TAC[cubic_hypermap] THEN STRIP_TAC THEN
  ASM_MESON_TAC[cubic_hypermap; PATCH_HD_IN_DART]);;

let PLAIN_PATCH_D = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     plain_hypermap G
     ==> !x. x IN dart Gd /\ ~MEM x bGd ==> orbit_size (edge_map Gd) x = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_ORBIT_SIZES o C CONJ
    (ASSUME `2 <= LENGTH (bGd:(A)list)`)) THEN
  STRIP_TAC THEN ASM_MESON_TAC[plain_hypermap; PATCH_HD_IN_DART]);;

let PLAIN_PATCH_COMPOSE = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     (!x. x IN dart Gd /\ ~MEM x bGd ==> orbit_size (edge_map Gd) x = 2) /\
     plain_hypermap Gr
     ==> plain_hypermap G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(B)hypermap`;`Gd:(A)hypermap`;`Gr:(E)hypermap`;`hd:A->B`;
                 `hr:E->B`;`bGd:(A)list`;`bGr:(E)list`] PATCH_ORBIT_SIZES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[plain_hypermap] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  ASM_CASES_TAC `z IN IMAGE (hr:E->B) (dart Gr)` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:E`
     (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `plain_hypermap (Gr:(E)hypermap)` THEN
    REWRITE_TAC[plain_hypermap] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_CODOM_R) THEN
    DISCH_THEN(MP_TAC o SPEC `z:B`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DE_MORGAN_THM; IN_IMAGE; MEM_MAP; NOT_EXISTS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)
      (MP_TAC o SPEC `x:A`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[]]);;

let CUBIC_PATCH_COMPOSE = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     cubic_hypermap Gd /\ quasicubic Gr (set_of_list bGr)
     ==> cubic_hypermap G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(B)hypermap`;`Gd:(A)hypermap`;`Gr:(E)hypermap`;`hd:A->B`;
                 `hr:E->B`;`bGd:(A)list`;`bGr:(E)list`] PATCH_ORBIT_SIZES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[cubic_hypermap] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  ASM_CASES_TAC `z IN IMAGE (hd:A->B) (dart Gd)` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A`
     (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `cubic_hypermap (Gd:(A)hypermap)` THEN
    REWRITE_TAC[cubic_hypermap] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `?y:E. y IN dart (Gr:(E)hypermap) /\ (z:B) = hr y`
    MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_COVER) THEN
      DISCH_THEN(MP_TAC o AP_TERM `(IN) (z:B)`) THEN
      ASM_REWRITE_TAC[IN_UNION; IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:E`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `~MEM (y:E) bGr` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                     `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`; `y:E`]
        PATCH_HR_IN_IMAGE_HD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `quasicubic (Gr:(E)hypermap) (set_of_list bGr)` THEN
    REWRITE_TAC[quasicubic; IN_SET_OF_LIST] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let BRIDGELESS_PATCH_COMPOSE = prove
 (`!(G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap) (hd:A->B) (hr:E->B)
    (bGd:(A)list) (bGr:(E)list).
      patch G Gd Gr hd hr bGd bGr /\ 2 <= LENGTH bGd /\
      bridgeless Gd /\ bridgeless Gr /\ chordless Gd bGd
      ==> bridgeless G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[INJ] o
              MATCH_MP PATCH_INJ_HD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_EDGE_D) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_EDGE_R) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_CFACE_HD) THEN
  REWRITE_TAC[bridgeless] THEN X_GEN_TAC `x:B` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x:B) IN IMAGE (hr:E->B) (dart Gr)` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    DISCH_THEN(X_CHOOSE_THEN `xr:E` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      ASSUME_TAC)) THEN
    SUBGOAL_THEN `cface Gr (xr:E) (edge_map Gr xr)` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_CFACE_HR o C CONJ
        (ASSUME `2 <= LENGTH (bGd:(A)list)`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`xr:E`; `edge_map Gr (xr:E)`]) THEN
      ASM_SIMP_TAC[EDGE_MAP_IN_DART];
      CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?xd:A. xd IN dart Gd /\ ~MEM xd bGd /\ (x:B) = hd xd`
   STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_COVER) THEN
    DISCH_THEN(MP_TAC o AP_TERM `(IN) (x:B)`) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `xd:A` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      ASSUME_TAC)) THEN
    EXISTS_TAC `xd:A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                   `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`; `xd:A`]
      PATCH_HD_IN_IMAGE_HR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `cface G ((hd:A->B) xd) (hd (edge_map Gd (xd:A)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(hd:A->B) (edge_map Gd (xd:A)) = edge_map G (hd xd)`
     SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `edge_map Gd (xd:A) IN dart Gd` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART]; ALL_TAC] THEN
  ASM_CASES_TAC `?b:A. MEM b bGd /\ cface Gd xd b` THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `?n. (hd:A->B) (edge_map Gd (xd:A)) = ITER n (face_map G) (hd xd)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `cface G ((hd:A->B) xd) (hd (edge_map Gd (xd:A)))` THEN
      REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                   `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`; `xd:A`]
      PATCH_FACE_CHAIN_HD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(?b:A. MEM b bGd /\ cface Gd xd b)` THEN
      REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN MESON_TAC[];
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC] THEN
    SUBGOAL_THEN `edge_map Gd (xd:A) = ITER n (face_map Gd) xd`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[ITER_PERMUTES_IN; FACE_MAP_PERMUTES];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Gd:(A)hypermap`; `xd:A`] BRIDGELESS_CFACE) THEN
    ASM_REWRITE_TAC[cface; face; ORBIT_MAP_ITER; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `yd:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(hd:A->B) (edge_map Gd xd) IN
    {x | x IN dart G /\
         ?z. z IN IMAGE (hr:E->B) (dart (Gr:(E)hypermap)) /\
             x IN orbit_map (face_map G) z}`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`face_map(G:(B)hypermap)`;
       `{x | x IN dart G /\ ?z. z IN IMAGE (hr:E->B) (dart(Gr:(E)hypermap)) /\
                                x IN orbit_map (face_map G) z}`;
       `(hd:A->B) xd`] ORBIT_IN_CLOSED) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OUTER_CLOSED THEN
        REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_INJ_HR) THEN
        REWRITE_TAC[INJ] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
        MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                       `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`;
                       `xd:A`; `yd:A`] PATCH_FBAND_IN_OUTER) THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `cface G ((hd:A->B) xd) (hd (edge_map Gd (xd:A)))` THEN
      REWRITE_TAC[cface; face]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?zd:A. MEM zd bGd /\ cface Gd (edge_map Gd xd) zd`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                   `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`;
                   `edge_map Gd (xd:A)`] PATCH_NONFBAND_NOT_OUTER) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(yd:A) IN dart Gd /\ (zd:A) IN dart Gd` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                   `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`]
      PATCH_BGD_IN_DART) THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `adj Gd (yd:A) (zd:A)` ASSUME_TAC THENL
   [REWRITE_TAC[adj] THEN EXISTS_TAC `xd:A` THEN CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cface G ((hd:A->B) xd) (hd (yd:A)) /\
                cface G (hd (edge_map Gd xd)) (hd zd)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cface G ((hd:A->B) yd) (hd (zd:A))` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\x y:A. ~(x = y)) bGd /\
                list_cycle (\x y:A. edge_map Gd x = y) bGd`
   STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_CYCLE_D) THEN
    DISCH_THEN(fun th ->
      REWRITE_TAC[MATCH_MP SCYCLE_PAIRWISE th] THEN MP_TAC th) THEN
    SIMP_TAC[scycle];
    ALL_TAC] THEN
  SUBGOAL_THEN `(zd:A) = yd \/ zd = edge_map Gd yd \/ yd = edge_map Gd zd`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Gd:(A)hypermap`; `bGd:(A)list`; `yd:A`; `zd:A`]
      CHORDLESS_RING) THEN
    MP_TAC(ISPECL [`edge_map (Gd:(A)hypermap)`; `bGd:(A)list`; `yd:A`]
      NEXTC_CYCLE) THEN
    MP_TAC(ISPECL [`edge_map (Gd:(A)hypermap)`; `bGd:(A)list`; `zd:A`]
      NEXTC_CYCLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    CFACE_TAC[];
    MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                   `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`; `yd:A`]
      PATCH_BORDER_EDGE_GR_BRIDGE);
    MP_TAC(ISPECL [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`;
                   `hd:A->B`; `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`; `zd:A`]
      PATCH_BORDER_EDGE_GR_BRIDGE)] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CFACE_TAC[];
     UNDISCH_TAC `bridgeless (Gr:(E)hypermap)` THEN
     REWRITE_TAC[bridgeless] THEN MESON_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* Isomorphic copies.  The map sewn in Birkhoff_valid has darts of type      *)
(* A+num, so the minimality of a counter-example over A is carried over to   *)
(* maps over other dart types (MINIMALITY_POLY); Coq's minimal_counter_      *)
(* example quantifies over all finite dart types and needs no such step.     *)
(* ------------------------------------------------------------------------- *)

let hm_iso = new_definition
 `hm_iso (h:A->B) (g:B->A) (G:(A)hypermap) (G':(B)hypermap) <=>
    (!x. x IN dart G ==> g(h x) = x) /\
    (!y. y IN dart G' ==> h(g y) = y) /\
    dart G' = IMAGE h (dart G) /\
    (!x. x IN dart G ==> edge_map G' (h x) = h(edge_map G x)) /\
    (!x. x IN dart G ==> node_map G' (h x) = h(node_map G x)) /\
    (!x. x IN dart G ==> face_map G' (h x) = h(face_map G x))`;;

let ISO_INV = prove
 (`!(h:A->B) g G G'. hm_iso h g G G' ==> hm_iso g h G' G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hm_iso] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART]]);;

let ISO_IN_DART = prove
 (`!(h:A->B) g G G'. hm_iso h g G G'
     ==> (!x. x IN dart G ==> h x IN dart G') /\
         (!y. y IN dart G' ==> g y IN dart G) /\
         (!x y. x IN dart G /\ y IN dart G ==> (h x = h y <=> x = y))`,
  REWRITE_TAC[hm_iso] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let GCOMP_ISO_FWD = prove
 (`!(h:A->B) g G G' x y.
      hm_iso h g G G' /\ x IN dart G /\ gcomp G x y ==> gcomp G' (h x) (h y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ISO_IN_DART o CONJUNCT1) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[hm_iso])
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[gcomp] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `p:num->A`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!i. i <= n ==> (p:num->A) i IN dart G` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[LE_0] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `glink (G:(A)hypermap) (p i) (p (i + 1))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[glink; ADD1] THEN
    ASM_MESON_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART;
                  ARITH_RULE `SUC i <= n ==> i <= n`];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `\i:num. (h:A->B)((p:num->A) i)`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `glink (G:(A)hypermap) (p i) (p (i + 1)) /\ (p:num->A) i IN dart G`
  MP_TAC THENL [ASM_MESON_TAC[LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[glink] THEN ASM_MESON_TAC[]);;

let GCOMP_ISO = prove
 (`!(h:A->B) g G G' x y.
      hm_iso h g G G' /\ x IN dart G /\ y IN dart G
      ==> (gcomp G' (h x) (h y) <=> gcomp G x y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`g:B->A`; `h:A->B`; `G':(B)hypermap`; `G:(A)hypermap`;
                   `(h:A->B) x`; `(h:A->B) y`] GCOMP_ISO_FWD) THEN
    ASM_MESON_TAC[ISO_INV; ISO_IN_DART; hm_iso];
    ASM_MESON_TAC[GCOMP_ISO_FWD]]);;

let COMPONENT_ISO = prove
 (`!(h:A->B) g G G' x. hm_iso h g G G' /\ x IN dart G
      ==> component G' (h x) = IMAGE h (component G x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ISO_IN_DART) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    REWRITE_RULE[hm_iso]) THEN
  REWRITE_TAC[component; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[GCOMP_ISO]);;

let ISO_COUNTS = prove
 (`!(h:A->B) g G G'. hm_iso h g G G'
     ==> CARD(dart G') = CARD(dart G) /\
         number_of_edges G' = number_of_edges G /\
         number_of_nodes G' = number_of_nodes G /\
         number_of_faces G' = number_of_faces G`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC(MATCH_MP ISO_IN_DART th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[hm_iso] th)) THEN
  ASM_REWRITE_TAC[number_of_edges; number_of_nodes; number_of_faces;
                  edge_set; node_set; face_set] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[FINITE_DART]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC ORBIT_COUNT_IMAGE THEN
  ASM_SIMP_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES;
               FACE_MAP_PERMUTES]);;

let ISO_NUMBER_COMPONENTS = prove
 (`!(h:A->B) g G G'. hm_iso h g G G'
      ==> number_of_components G' = number_of_components G`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC(MATCH_MP ISO_IN_DART th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[hm_iso] th) THEN ASSUME_TAC th) THEN
  REWRITE_TAC[NCOMP_IMAGE] THEN ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
  SUBGOAL_THEN
   `IMAGE (component G' o (h:A->B)) (dart G) =
    IMAGE (IMAGE h o component (G:(A)hypermap)) (dart G)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN
    ASM_MESON_TAC[COMPONENT_ISO];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_DART; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  MATCH_MP_TAC(ISPECL [`h:A->B`;
   `dart(G:(A)hypermap)`] INJ_ON_IMAGE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[component; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN
  ASM_MESON_TAC[]);;

let ISO_PLANAR = prove
 (`!(h:A->B) g G G'.
     hm_iso h g G G' /\ planar_hypermap G ==> planar_hypermap G'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ISO_COUNTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ISO_NUMBER_COMPONENTS) THEN
  UNDISCH_TAC `planar_hypermap (G:(A)hypermap)` THEN
  ASM_REWRITE_TAC[planar_hypermap; genus; euler_lhs; euler_rhs]);;

let ISO_ORBIT_SIZE = prove
 (`!(h:A->B) g G G' x. hm_iso h g G G' /\ x IN dart G
     ==> orbit_size (edge_map G') (h x) = orbit_size (edge_map G) x /\
         orbit_size (node_map G') (h x) = orbit_size (node_map G) x /\
         (cface G' (h x) (h(edge_map G x)) <=> cface G x (edge_map G x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP ISO_IN_DART th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[hm_iso] th)) ASSUME_TAC) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`edge_map (G:(A)hypermap)`; `edge_map (G':(B)hypermap)`;
                   `dart (G:(A)hypermap)`; `h:A->B`] ORBIT_SIZE_TRANSPORT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_DART; EDGE_MAP_IN_DART] THEN ASM_MESON_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `node_map (G':(B)hypermap)`;
                   `dart (G:(A)hypermap)`; `h:A->B`] ORBIT_SIZE_TRANSPORT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_DART; NODE_MAP_IN_DART] THEN ASM_MESON_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[cface; face] THEN
    MP_TAC(ISPECL [`h:A->B`; `face_map (G:(A)hypermap)`;
                   `face_map (G':(B)hypermap)`; `dart (G:(A)hypermap)`; `x:A`]
      ORBIT_IMAGE) THEN
    ASM_SIMP_TAC[FACE_MAP_PERMUTES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN
    MP_TAC(ISPECL [`face_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`; `x:A`]
      ORBIT_SUBSET) THEN
    ASM_REWRITE_TAC[FACE_MAP_PERMUTES; SUBSET] THEN
    ASM_MESON_TAC[EDGE_MAP_IN_DART]]);;

let ISO_PROPS = prove
 (`!(h:A->B) g G G'. hm_iso h g G G'
     ==> (plain_hypermap G ==> plain_hypermap G') /\
         (precubic G ==> precubic G') /\
         (bridgeless G ==> bridgeless G')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hm_iso]) THEN
  REWRITE_TAC[plain_hypermap; precubic; bridgeless] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->A`; `G:(A)hypermap`; `G':(B)hypermap`; `x:A`]
    ISO_ORBIT_SIZE) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let ISO_COLORABLE = prove
 (`!(h:A->B) g G G'.
     hm_iso h g G G' /\ four_colorable G' ==> four_colorable G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[four_colorable; coloring] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `k:B->color`)) THEN
  REWRITE_TAC[hm_iso] THEN STRIP_TAC THEN
  EXISTS_TAC `\x:A. (k:B->color)(h x)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:A. x IN dart G ==> (h:A->B) x IN dart G'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let RELABEL_ISO_EXISTS = prove
 (`!(h:B->A) (G:(B)hypermap).
     (!x y. x IN dart G /\ y IN dart G /\ h x = h y ==> x = y)
     ==> ?G':(A)hypermap g. hm_iso h g G G'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:A->B`) THEN
  MAP_EVERY ABBREV_TAC
   [`ee = \b:A. if b IN IMAGE (h:B->A) (dart(G:(B)hypermap)) then h(edge_map G
      (g b)) else b`;
    `nn = \b:A. if b IN IMAGE (h:B->A) (dart(G:(B)hypermap)) then h(node_map G
      (g b)) else b`;
    `ff = \b:A. if b IN IMAGE (h:B->A) (dart(G:(B)hypermap)) then h(face_map G
      (g b)) else b`] THEN
  SUBGOAL_THEN
   `(!x:B. x IN dart G ==> ee ((h:B->A) x) = h(edge_map G x)) /\
    (!x:B. x IN dart G ==> nn ((h:B->A) x) = h(node_map G x)) /\
    (!x:B. x IN dart G ==> ff ((h:B->A) x) = h(face_map G x)) /\
    (!y:A. ~(y IN IMAGE h (dart G)) ==> ee y = y /\ nn y = y /\ ff y = y)`
   STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ee"; "nn"; "ff"] THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hypermap_pred (IMAGE (h:B->A) (dart(G:(B)hypermap)), ee, nn, ff)`
  MP_TAC THENL
   [REWRITE_TAC[hypermap_pred] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DART];
      MATCH_MP_TAC PERMUTES_TRANSFER THEN
        EXISTS_TAC `edge_map(G:(B)hypermap)` THEN
      ASM_SIMP_TAC[EDGE_MAP_PERMUTES] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC PERMUTES_TRANSFER THEN
        EXISTS_TAC `node_map(G:(B)hypermap)` THEN
      ASM_SIMP_TAC[NODE_MAP_PERMUTES] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC PERMUTES_TRANSFER THEN
        EXISTS_TAC `face_map(G:(B)hypermap)` THEN
      ASM_SIMP_TAC[FACE_MAP_PERMUTES] THEN ASM_MESON_TAC[];
      REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN X_GEN_TAC `b:A` THEN
      ASM_CASES_TAC `b IN IMAGE (h:B->A)(dart(G:(B)hypermap))` THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC o
          GEN_REWRITE_RULE I [IN_IMAGE]) THEN
        ASM_SIMP_TAC[FACE_MAP_IN_DART; NODE_MAP_IN_DART; faceK];
        ASM_SIMP_TAC[]]];
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MK_HYPERMAP_COMPONENTS)] THEN
  MAP_EVERY EXISTS_TAC
   [`mk_hypermap (IMAGE (h:B->A)(dart(G:(B)hypermap)), ee, nn, ff)`;
    `g:A->B`] THEN
  ASM_REWRITE_TAC[hm_iso] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[]);;

let MINIMALITY_POLY = prove
 (`!(H:(A)hypermap) (G:(B)hypermap).
     (!H':(A)hypermap.
         planar_hypermap H' /\ bridgeless H' /\ plain_hypermap H' /\
         precubic H' /\ CARD(dart H') < CARD(dart H)
         ==> four_colorable H') /\
     planar_hypermap G /\ bridgeless G /\ plain_hypermap G /\ precubic G /\
     CARD(dart G) < CARD(dart H)
     ==> four_colorable G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`dart(G:(B)hypermap)`;`dart(H:(A)hypermap)`] CARD_LE_INJ) THEN
  ASM_SIMP_TAC[FINITE_DART; LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:B->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL[`h:B->A`;`G:(B)hypermap`] RELABEL_ISO_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G':(A)hypermap` (X_CHOOSE_TAC `g:A->B`)) THEN
  MP_TAC(ISPECL [`h:B->A`; `g:A->B`; `G:(B)hypermap`; `G':(A)hypermap`]
    ISO_COLORABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[ISO_PLANAR; ISO_PROPS; ISO_COUNTS]);;

(* ------------------------------------------------------------------------- *)
(* Ring traces of rotated and reversed rings, the traces of a configuration  *)
(* ring (CHKBP_RING_RECONCILE), the initial Kempe-tree invariant (Coq        *)
(* kempetree.v Kempe_valid_init, Kempe_valid_restrict) and Kempe closure     *)
(* under rotation.                                                           *)
(* ------------------------------------------------------------------------- *)

let SCYCLE_RLINK_GE2 = prove
 (`!(H:(A)hypermap) r.
     bridgeless H /\ scycle H (rlink H) r /\ ALL (\y:A. y IN dart H) r
     ==> 2 <= LENGTH r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`] THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH_EQ_NIL] THEN DISCH_TAC THEN
    UNDISCH_TAC `scycle (H:(A)hypermap) (rlink H) r` THEN
    ASM_REWRITE_TAC[scycle; list_cycle];
    DISCH_TAC THEN
    SUBGOAL_THEN `?x:A. r = [x]` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `LENGTH (r:(A)list) = 1` THEN
      ONCE_REWRITE_TAC[num_CONV `1`] THEN
      REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
      STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `scycle (H:(A)hypermap) (rlink H) r` THEN
    UNDISCH_TAC `ALL (\y:A. y IN dart H) r` THEN
    ASM_REWRITE_TAC[scycle; list_cycle; list_path; LAST; NOT_CONS_NIL;
                    ALL] THEN
    CFACE_TAC[]]);;

let REV_ROT1 = prove
 (`!l:A list. REVERSE(rot1 l) = rotr1(REVERSE l)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[rot1; REVERSE; rotr1];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ROT1_CONS; REVERSE_APPEND; REVERSE; APPEND;
                rotr1; APPEND_EQ_NIL; NOT_CONS_NIL; LAST_APPEND;
                 BUTLAST_APPEND;
                LAST; BUTLAST; APPEND_NIL]]);;

let RING_TRACE_REVERSE = prove
 (`!(H:(A)hypermap) r et. ~(r = []) /\ ring_trace H r et
    ==> ring_trace H (REVERSE r) (REVERSE(rot1 et))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ring_trace (H:(A)hypermap) r et` THEN
  REWRITE_TAC[ring_trace] THEN STRIP_TAC THEN
  EXISTS_TAC `k:A->color` THEN
  SUBGOAL_THEN `~(MAP (k:A->color) r = [])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MAP_EQ_NIL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM MAP_REVERSE] THEN
  ASM_SIMP_TAC[TRACE_COL_REVERSE]);;

let ORBIT_LIST_NODE_STEP = prove
 (`!(H:(num)hypermap) x. x IN dart H
     ==> orbit_list (node_map H) (node_map H x) =
         rot1 (orbit_list (node_map H) x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < orbit_size (node_map(H:(num)hypermap)) x` ASSUME_TAC THENL
   [MATCH_MP_TAC ORBIT_SIZE_POS THEN EXISTS_TAC `dart(H:(num)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN `orbit_size (node_map(H:(num)hypermap)) (node_map H x) =
                orbit_size (node_map H) x` ASSUME_TAC THENL
   [MATCH_MP_TAC ORBIT_SIZE_NODE_STEP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ITER (orbit_size (node_map(H:(num)hypermap)) x) (node_map H) x = x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ITER_ORBIT_SIZE THEN EXISTS_TAC `dart(H:(num)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN `?p. orbit_size (node_map(H:(num)hypermap)) x = SUC p`
    STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `orbit_size (node_map(H:(num)hypermap)) x - 1` THEN
     ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ITER (SUC p) (node_map(H:(num)hypermap)) x = x`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `ITER (orbit_size (node_map(H:(num)hypermap)) x) (node_map H) x = x` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[orbit_list] THEN ASM_REWRITE_TAC[SUC_SUB1; ROT1_CONS] THEN
  SUBGOAL_THEN
   `CONS (node_map(H:(num)hypermap) x)
         (iterlist p (node_map H) (node_map H x)) =
    iterlist (SUC p) (node_map H) x`
   SUBST1_TAC THENL
   [REWRITE_TAC[iterlist]; ALL_TAC] THEN
  REWRITE_TAC[ADD1; ITERLIST_ADD] THEN AP_TERM_TAC THEN
  REWRITE_TAC[num_CONV `1`; iterlist] THEN
  SUBGOAL_THEN `node_map(H:(num)hypermap) (ITER p (node_map H) x) = x`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let CHKBP_RING_RECONCILE = prove
 (`!cp rest:(color)list.
      cubic_prog cp /\
      ring_trace (FST(cpmap cp))
        (orbit_list (node_map (FST(cpmap cp)))
                    (node_map (FST(cpmap cp)) (SND(cpmap cp))))
        (REVERSE(rot1 (ctrace rest)))
      ==> ring_trace (FST(cpmap cp))
            (rot_list 1 (cpring (FST(cpmap cp)) (SND(cpmap cp))))
            (ctrace (etrace rest))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND(cpmap cp) IN dart(FST(cpmap cp))` ASSUME_TAC THENL
   [REWRITE_TAC[CPMAP_PT_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `node_map(FST(cpmap cp))(SND(cpmap cp)) IN dart(FST(cpmap cp))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rot_list 1 (cpring (FST(cpmap cp)) (SND(cpmap cp))) =
    REVERSE(orbit_list (node_map(FST(cpmap cp)))
                       (node_map(FST(cpmap cp))(SND(cpmap cp))))`
   SUBST1_TAC THENL
   [REWRITE_TAC[ROT_LIST_1; cpring] THEN
    MP_TAC(ISPECL [`FST(cpmap cp)`;
                   `node_map(FST(cpmap cp))(SND(cpmap cp))`]
                     ORBIT_LIST_NODE_STEP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REV_ROT1; ROT1_ROTR1]; ALL_TAC] THEN
  REWRITE_TAC[etrace; CTRACE_PERMT] THEN
  MATCH_MP_TAC RING_TRACE_PERMT THEN
  MP_TAC(ISPECL
   [`FST(cpmap cp)`;
    `orbit_list (node_map(FST(cpmap cp))) (node_map(FST(cpmap cp))
       (SND(cpmap cp)))`;
    `REVERSE(rot1(ctrace(rest:(color)list)))`] RING_TRACE_REVERSE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[orbit_list; NOT_CONS_NIL]; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[REV_ROT1; REVERSE_REVERSE; ROTR1_ROT1]);;

let KEMPE_VALID_RESTRICT = prove
 (`!h P ctu ctr gtr gtu.
     (!et. ctree_mem ctr et
           ==> kempe_coclosure P (ctrace_a et) /\ LENGTH et = SUC h)
     ==> kempe_valid h P ctu CtreeEmpty gtr gtu
     ==> kempe_valid h P ctu ctr gtr gtu`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[kempe_valid] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC);;

let KEMPE_VALID_INIT = prove
 (`!h P. kempe_valid h P (ctree_init_tree (SUC h)) CtreeEmpty GtreeEmpty
                         (gtree_init_tree (SUC h))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kempe_valid] THEN REPEAT CONJ_TAC THENL
   [(* 1. proper *)
    REWRITE_TAC[CTREE_INIT_TREE_PROPER];
(* 2. ctree_sub = even? gtree_subs                                           *)
    GEN_TAC THEN
    REWRITE_TAC[CTREE_SUB_INIT_TREE; GTREE_SUB_EMPTY; ADD_CLAUSES] THEN
    SUBGOAL_THEN
      `gtree_sub (gtree_init_tree (SUC h)) Bstack0 et =
       match_count (init_gtree_spec (SUC h)) Bstack0 et`
      SUBST1_TAC THENL
     [REWRITE_TAC[gtree_sub] THEN MATCH_MP_TAC MATCH_COUNT_EQ THEN
      REWRITE_TAC[GTREE_MEM_INIT_TREE]; ALL_TAC] THEN
    REWRITE_TAC[MATCH_COUNT_BALANCED] THEN
    BOOL_CASES_TAC `even_trace et` THEN REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[];
(* 3. ctr = CtreeEmpty : vacuous                                             *)
    REWRITE_TAC[CTREE_MEM_EMPTY];
(* 4. gtr = GtreeEmpty : vacuous                                             *)
    REWRITE_TAC[GTREE_MEM_EMPTY];
(* 5. gtu members are init_gtree_spec                                        *)
    REWRITE_TAC[GTREE_MEM_INIT_TREE];
(* 6. ~gtree_mem gtu w /\ init_gtree_spec w : contradictory                  *)
    REWRITE_TAC[GTREE_MEM_INIT_TREE] THEN MESON_TAC[]]);;

let NTR_MONO = prove
 (`!(H:(A)hypermap) m r. ~nontrivial_ring H 0 r ==> ~nontrivial_ring H m r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nontrivial_ring] THEN ARITH_TAC);;

let KEMPE_COCLOSURE_SELF = prove
 (`!P et. P et ==> kempe_coclosure P et`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[kempe_coclosure] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `et:(color)list` THEN ASM_REWRITE_TAC[]);;

let KEMPE_CLOSED_ROTR1 = prove
 (`!P. kempe_closed P ==> kempe_closed (\x. P (rotr1 x))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[kempe_closed] THEN
  X_GEN_TAC `et1:(color)list` THEN BETA_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `kempe_closed (P:(color)list->bool)` THEN
  REWRITE_TAC[kempe_closed] THEN
  DISCH_THEN(MP_TAC o SPEC `rotr1 (et1:(color)list)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `g:edge_perm` THEN BETA_TAC THEN
    SUBGOAL_THEN `rotr1 (permt g (et1:(color)list)) = permt g (rotr1 et1)`
      SUBST1_TAC THENL
     [REWRITE_TAC[PERMT_MAP; MAP_ROTR1]; ALL_TAC] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    EXISTS_TAC `gram_rot w` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`rotr1 (et1:(color)list)`; `w:(gram_symbol)list`]
        MATCH_GRAM_ROT) THEN
      REWRITE_TAC[ROT1_ROTR1] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `et2:(color)list` THEN BETA_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`rotr1 (et2:(color)list)`; `w:(gram_symbol)list`]
        MATCH_GRAM_ROT) THEN
      REWRITE_TAC[ROT1_ROTR1] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]]]);;

let CTRACE_A_ROT1 = prove
 (`!et. ctrace_a et = rot1 (ctrace et)`,
  GEN_TAC THEN REWRITE_TAC[ctrace_a; ctrace; ROT1_CONS]);;

let ROTR1_PERMT = prove
 (`!g et. rotr1 (permt g et) = permt g (rotr1 et)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PERMT_MAP; MAP_ROTR1]);;

let SUMT_REVERSE = prove
 (`!l. sumt (REVERSE l) = sumt l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; sumt; SUMT_APPEND; ADDC_0_RIGHT] THEN
  REWRITE_TAC[ADDC_COMM]);;

let RING_TRACE_LENGTH = prove
 (`!(G:(A)hypermap) r et. ring_trace G r et ==> LENGTH et = LENGTH r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_trace] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_TRACE; LENGTH_MAP]);;

let CTRACE_A_BUTLAST_EQ = prove
 (`!cs:(color)list. ~(cs = []) /\ sumt cs = Color0
      ==> ctrace_a (BUTLAST cs) = cs`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ctrace_a] THEN
  SUBGOAL_THEN `sumt (BUTLAST (cs:(color)list)) = LAST cs` SUBST1_TAC THENL
   [SUBGOAL_THEN `sumt (APPEND (BUTLAST (cs:(color)list)) [LAST cs]) = Color0`
      MP_TAC THENL
     [ASM_SIMP_TAC[APPEND_BUTLAST_LAST];
      REWRITE_TAC[SUMT_APPEND; sumt; ADDC_0_RIGHT; ADDC_EQ_0]];
    ASM_SIMP_TAC[APPEND_BUTLAST_LAST]]);;

let RING_TRACE_ROTR1 = prove
 (`!(G:(A)hypermap) s y. ~(s = []) /\ ring_trace G (rot1 s) y
      ==> ring_trace G s (rotr1 y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_trace] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `k:A->color` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `k:A->color` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[MAP_ROT1] THEN
  SUBGOAL_THEN
   `trace_col(rot1 (MAP (k:A->color) s)) = rot1(trace_col(MAP k s))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TRACE_COL_ROT1 THEN ASM_REWRITE_TAC[MAP_EQ_NIL]; ALL_TAC] THEN
  REWRITE_TAC[ROTR1_ROT1]);;

let RING_TRACE_ROT1_RING_EQ = prove
 (`!(H:(A)hypermap) r et. ~(r = [])
     ==> (ring_trace H r (rot1 et) <=> ring_trace H (rotr1 r) et)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(rotr1 (r:(A)list) = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[ROT1_ROTR1; ROT1_NIL]; ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL[`H:(A)hypermap`; `rotr1 (r:(A)list)`;
    `rot1 (et:(color)list)`]
                RING_TRACE_ROTR1) THEN
    ASM_REWRITE_TAC[ROT1_ROTR1; ROTR1_ROT1];
    MP_TAC(ISPECL[`H:(A)hypermap`; `rotr1 (r:(A)list)`; `et:(color)list`]
                RING_TRACE_ROT1) THEN
    ASM_REWRITE_TAC[ROT1_ROTR1]]);;

let KEMPE_CLOSED_RING_CHROMO = prove
 (`!(H:(A)hypermap) r.
     kempe_closed (ring_trace H r) <=>
     (!et. ring_trace H r et
           ==> ?w. matchg [] et w /\
                   (!et'. matchg [] et' w ==> ring_trace H r et'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kempe_closed] THEN EQ_TAC THEN
    DISCH_TAC THENL
   [X_GEN_TAC `et:(color)list` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `et:(color)list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ACCEPT_TAC);
    X_GEN_TAC `et:(color)list` THEN DISCH_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC RING_TRACE_PERMT THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `et:(color)list`) THEN ASM_REWRITE_TAC[]]]);;

let KEMPE_CLOSED_RING_ITER_ROT1 = prove
 (`!(H:(A)hypermap) r n.
     ~(r = []) /\ kempe_closed (ring_trace H r)
     ==> kempe_closed (ring_trace H (ITER n rot1 r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[KEMPE_CLOSED_RING_CHROMO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`;
   `n:num`] CHROMOGRAM_ROT_ITER) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The disk of a ring and the remainder of the reversed ring have the same   *)
(* ring traces (Coq rev_ring_cotrace): colourings transfer directly, the     *)
(* ring darts of the remainder taking the colour of the next disk border     *)
(* dart.  Hence the disk traces are Kempe-closed (Coq ring_disk_closed).     *)
(* ------------------------------------------------------------------------- *)

let REM_COLORING_CLAUSES = prove
 (`!(H:(A)hypermap) rho kr.
     planar_hypermap H /\ scycle H (rlink H) rho /\
     ALL (\w. w IN dart H) rho /\ coloring (snip_rem H rho) kr
     ==> (!u. u IN redart H rho ==> ~(kr (edge_map H u) = kr u)) /\
         (!u. u IN redart H rho ==> kr (snipr_face H rho u) = kr u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `coloring (snip_rem (H:(A)hypermap) rho) kr` THEN
  REWRITE_TAC[coloring] THEN
  ASM_SIMP_TAC[SNIP_REM_COMPONENTS] THEN REWRITE_TAC[snipr_edge] THEN
  MESON_TAC[]);;

let DISK_COLORING_CLAUSES = prove
 (`!(H:(A)hypermap) r kd.
     planar_hypermap H /\ scycle H (rlink H) r /\ ALL (\w. w IN dart H) r /\
     coloring (snip_disk H r) kd
     ==> (!u. diskN H r u ==> ~(kd (snipd_edge H r u) = kd u)) /\
         (!u. diskN H r u ==> kd (snipd_face H r u) = kd u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `coloring (snip_disk (H:(A)hypermap) r) kd` THEN
  REWRITE_TAC[coloring] THEN ASM_SIMP_TAC[SNIP_DISK_COMPONENTS; IN]);;

let MAP_NEXTC_ROT1 = prove
 (`!r:(A)list. PAIRWISE (\x y. ~(x = y)) r ==> MAP (\y. nextc r y) r = rot1 r`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THENL
   [REWRITE_TAC[MAP; ROT1_NIL]; DISCH_TAC] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_ROT1] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; NEXTC_EL; ROT1_CONS; EL_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN REWRITE_TAC[LENGTH] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < n ==> i + 1 < SUC n`] THEN
    REWRITE_TAC[GSYM ADD1; EL; TL];
    SUBGOAL_THEN `i = LENGTH(t:(A)list)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[GSYM ADD1; MOD_REFL; SUB_REFL; EL; HD]]]);;

let MAP_NEXTC_COL = prove
 (`!(kd:A->color) L. PAIRWISE (\x y. ~(x = y)) L
      ==> MAP (\z. kd (nextc L z)) L = rot1 (MAP kd L)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MAP_ROT1] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP MAP_NEXTC_ROT1) THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF]);;

let NEXTC_REV_RING = prove
 (`!(H:(A)hypermap) rho w.
     PAIRWISE (\x y. ~(x = y)) rho /\ MEM w rho
     ==> nextc (rev_ring H rho) (edge_map H w) = edge_map H (prevc rho w) /\
         prevc (rev_ring H rho) (edge_map H w) = edge_map H (nextc rho w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rev_ring; prevc; REVERSE_REVERSE] THENL
   [REWRITE_TAC[MAP_REVERSE] THEN MATCH_MP_TAC NEXTC_MAP THEN
    ASM_SIMP_TAC[MEM_REVERSE; PAIRWISE_DISTINCT_REVERSE] THEN MESON_TAC[EDGEI];
    MATCH_MP_TAC NEXTC_MAP THEN ASM_REWRITE_TAC[] THEN MESON_TAC[EDGEI]]);;

let REDART_SPLIT = prove
 (`!(H:(A)hypermap) rho x.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) rho /\ ALL (\z. z IN dart H) rho /\ proper_ring H rho
     ==> (x IN redart H rho <=>
          x IN dart H /\ (diskN H (rev_ring H rho) x \/ MEM x rho))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_REDART; diskE] THEN
  ASM_CASES_TAC `(x:A) IN dart H` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `x:A`] DISKN_REV_RING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC TAUT);;

(* The standing facts about a proper ring rho and its reverse rr.            *)

let COTRACE_FACTS = prove
 (`!(H:(A)hypermap) rho.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) rho /\ ALL (\z. z IN dart H) rho /\
     proper_ring H rho /\ 2 <= LENGTH rho
     ==> scycle H (rlink H) (rev_ring H rho) /\
         ALL (\z. z IN dart H) (rev_ring H rho) /\
         LENGTH (rev_ring H rho) = LENGTH rho /\
         ~(rev_ring H rho = []) /\ ~(rho = []) /\
         PAIRWISE (\x y. ~(x = y)) rho /\
         PAIRWISE (\x y. ~(x = y)) (rev_ring H rho) /\
         (!w. MEM w rho ==> w IN dart H /\ edge_map H w IN dart H /\
                           edge_map H (edge_map H w) = w /\
                           MEM (edge_map H w) (rev_ring H rho) /\
                           ~MEM w (rev_ring H rho) /\
                           ~MEM (edge_map H w) rho /\
                           diskN H (rev_ring H rho) (edge_map H w) /\
                           ~diskN H (rev_ring H rho) w /\
                           w IN redart H rho /\
                           edge_map H w IN redart H rho) /\
         (!x. diskN H (rev_ring H rho) x
              ==> x IN dart H /\ x IN redart H rho /\ ~MEM x rho) /\
         (!u. u IN dart H ==> node_map H (face_map H u) = edge_map H u) /\
         dart(snip_rem H rho) = redart H rho /\
         edge_map(snip_rem H rho) = snipr_edge H rho /\
         face_map(snip_rem H rho) = snipr_face H rho /\
         dart(snip_disk H (rev_ring H rho)) = diskN H (rev_ring H rho) /\
         edge_map(snip_disk H (rev_ring H rho)) =
         snipd_edge H (rev_ring H rho) /\
         face_map(snip_disk H (rev_ring H rho)) =
         snipd_face H (rev_ring H rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `scycle H (rlink H) (rev_ring H rho) /\
                ALL (\z:A. z IN dart H) (rev_ring H rho)`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCYCLE_REV_RING; REV_RING_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (rev_ring H rho) = LENGTH (rho:(A)list)`
  ASSUME_TAC THENL
   [REWRITE_TAC[rev_ring; LENGTH_REVERSE; LENGTH_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `~(rev_ring H rho = []) /\ ~(rho:(A)list = [])`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\x y:A. ~(x = y)) rho /\
                PAIRWISE (\x y:A. ~(x = y)) (rev_ring H rho)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SCYCLE_PAIRWISE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:A. MEM w rho ==> w IN dart H /\ edge_map H w IN dart H /\
                        edge_map H (edge_map H w) = w /\
                        MEM (edge_map H w) (rev_ring H rho) /\
                        ~MEM w (rev_ring H rho) /\
                        ~MEM (edge_map H w) rho /\
                        diskN H (rev_ring H rho) (edge_map H w) /\
                        ~diskN H (rev_ring H rho) w /\
                        w IN redart H rho /\
                        edge_map H w IN redart H rho`
    ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:A) IN dart H` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_MEM_DART]; ALL_TAC] THEN
    SUBGOAL_THEN `edge_map H (w:A) IN dart H /\ edge_map H (edge_map H w) = w`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[EDGE_MAP_IN_DART; PLAIN_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `~MEM (edge_map H w) (rho:(A)list)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `w:A`]
        DISKN_EDGE_RING) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_IN_DISKN THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MEM_REV_RING] THEN
    SUBGOAL_THEN `diskN H rho (w:A)` ASSUME_TAC THENL
     [MATCH_MP_TAC RING_IN_DISKN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `diskN H (rev_ring H rho) (edge_map H (w:A))` ASSUME_TAC THENL
     [MATCH_MP_TAC RING_IN_DISKN THEN ASM_SIMP_TAC[MEM_REV_RING]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `w:A`] DISKN_REV_RING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `w:A`] REDART_SPLIT) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `edge_map H (w:A)`]
                  REDART_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. diskN H (rev_ring H rho) x
          ==> x IN dart H /\ x IN redart H rho /\ ~MEM x rho`
    ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN dart H` ASSUME_TAC THENL
     [ASM_MESON_TAC[DISKN_SUBSET_DART]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `x:A`] REDART_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `x:A`] DISKN_REV_RING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_MESON_TAC[RING_IN_DISKN];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SNIP_REM_COMPONENTS; SNIP_DISK_COMPONENTS; PLAIN_EQ']);;

(* A colouring of the disk of rr gives a colouring of the remainder of rho:  *)
(* the ring darts take the colour of the next disk border dart.              *)

let COLORING_REM_OF_DISK = prove
 (`!(H:(A)hypermap) rho kd.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) rho /\ ALL (\z. z IN dart H) rho /\
     proper_ring H rho /\ 2 <= LENGTH rho /\
     coloring (snip_disk H (rev_ring H rho)) kd
     ==> coloring (snip_rem H rho)
          (\x. if MEM x rho then kd (nextc (rev_ring H rho) (edge_map H x))
               else kd x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`] COTRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rev_ring H (rho:(A)list)`; `kd:A->color`]
                DISK_COLORING_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun cl ->
  let kE = CONJUNCT1 cl and kF = CONJUNCT2 cl in
  ABBREV_TAC `rr = rev_ring H (rho:(A)list)` THEN
  ASM_REWRITE_TAC[coloring] THEN CONJ_TAC THEN X_GEN_TAC `u:A` THEN
  DISCH_TAC THEN
  (SUBGOAL_THEN `(u:A) IN dart H` ASSUME_TAC THENL
    [ASM_MESON_TAC[IN_REDART]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[snipr_edge; snipr_face] THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `MEM (u:A) rho` THENL
   [(* edge clause, u on the ring *)
    SUBGOAL_THEN `~MEM (edge_map H u) (rho:(A)list)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `edge_map H (u:A)` kE) THEN
    ASM_SIMP_TAC[snipd_edge] THEN MESON_TAC[];
    (* edge clause, u off the ring                                           *)
    SUBGOAL_THEN `diskN H rr (u:A)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `u:A`] REDART_SPLIT) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `MEM (edge_map H u) (rho:(A)list)` THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `MEM (u:A) rr` ASSUME_TAC THENL
       [EXPAND_TAC "rr" THEN ASM_SIMP_TAC[MEM_REV_RING]; ALL_TAC] THEN
      SUBGOAL_THEN `edge_map H (edge_map H u) = (u:A)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[PLAIN_EQ]; ALL_TAC] THEN
      MP_TAC(SPEC `u:A` kE) THEN ASM_SIMP_TAC[snipd_edge];
      SUBGOAL_THEN `~MEM (u:A) rr` ASSUME_TAC THENL
       [EXPAND_TAC "rr" THEN ASM_SIMP_TAC[MEM_REV_RING]; ALL_TAC] THEN
      MP_TAC(SPEC `u:A` kE) THEN ASM_SIMP_TAC[snipd_edge]];
    (* face clause, u on the ring                                            *)
    SUBGOAL_THEN `~MEM (edge_map H u) (rho:(A)list)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `face_map H u = (u:A)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~MEM (face_map H u) (rho:(A)list)` ASSUME_TAC THENL
     [CFACE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MEM (edge_map H u) (rr:(A)list) /\ diskN H rr (edge_map H u)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `MEM (nextc rr (edge_map H (u:A))) rr /\
                  diskN H rr (nextc rr (edge_map H u))`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[NEXTC_MEM] THEN MATCH_MP_TAC RING_IN_DISKN THEN
      ASM_SIMP_TAC[NEXTC_MEM] THEN ASM_MESON_TAC[RING_MEM_DART; NEXTC_MEM];
      ALL_TAC] THEN
    MP_TAC(SPEC `nextc rr (edge_map H (u:A))` kF) THEN
    ASM_SIMP_TAC[snipd_face; PREVC_NEXTC; PLAIN_EQ] THEN MESON_TAC[];
    (* face clause, u off the ring                                           *)
    SUBGOAL_THEN `diskN H rr (u:A)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `u:A`] REDART_SPLIT) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `MEM (edge_map H u) (rho:(A)list)` THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `MEM (nextc rho (edge_map H u)) (rho:(A)list)`
     ASSUME_TAC THENL
       [ASM_SIMP_TAC[NEXTC_MEM]; ALL_TAC] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`;
                     `nextc rho (edge_map H (u:A))`] NEXTC_REV_RING) THEN
      ASM_SIMP_TAC[PREVC_NEXTC; PLAIN_EQ];
      SUBGOAL_THEN `~MEM (face_map H u) (rho:(A)list)` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `diskE H rho (edge_map H (u:A))` MP_TAC THENL
         [REWRITE_TAC[diskE] THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `edge_map H u = node_map H (face_map H (u:A))`
            SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC DISKN_NODE_FWD THEN
          ASM_SIMP_TAC[FACE_MAP_IN_DART; RING_IN_DISKN];
          ALL_TAC] THEN
        ASM_SIMP_TAC[DISKE_EDGE; diskE] THEN
        MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `u:A`]
          DISKN_REV_RING) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~MEM (u:A) rr` ASSUME_TAC THENL
       [EXPAND_TAC "rr" THEN ASM_SIMP_TAC[MEM_REV_RING]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `u:A` kF) THEN
      ASM_SIMP_TAC[snipd_face]]]));;

(* A colouring of the remainder of rho colours the disk of rr unchanged.     *)

let COLORING_DISK_OF_REM = prove
 (`!(H:(A)hypermap) rho kr.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) rho /\ ALL (\z. z IN dart H) rho /\
     proper_ring H rho /\ 2 <= LENGTH rho /\
     coloring (snip_rem H rho) kr
     ==> coloring (snip_disk H (rev_ring H rho)) kr /\
         (!w. MEM w rho ==> kr (edge_map H w) = kr (nextc rho w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`] COTRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `kr:A->color`]
                REM_COLORING_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun cl ->
  let kE = CONJUNCT1 cl and kF = CONJUNCT2 cl in
  ABBREV_TAC `rr = rev_ring H (rho:(A)list)` THEN
  SUBGOAL_THEN
   `!w:A. MEM w rho ==> (kr:A->color) (edge_map H w) = kr (nextc rho w)`
    ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    MP_TAC(SPEC `edge_map H (w:A)` kF) THEN
    ASM_SIMP_TAC[snipr_face; PLAIN_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[coloring] THEN CONJ_TAC THEN X_GEN_TAC `u:A` THEN
  REWRITE_TAC[IN] THEN DISCH_TAC THEN
  (SUBGOAL_THEN `(u:A) IN dart H /\ u IN redart H rho /\ ~MEM u rho`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[snipd_edge; snipd_face] THEN
  ASM_CASES_TAC `MEM (u:A) rr` THEN ASM_REWRITE_TAC[] THENL
   [(* edge clause, u on rr *)
    SUBGOAL_THEN `MEM (edge_map H u) (rho:(A)list)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `u:A`] MEM_REV_RING) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `w = edge_map H (u:A)` THEN
    SUBGOAL_THEN `u = edge_map H (w:A)` SUBST1_TAC THENL
     [EXPAND_TAC "w" THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[PLAIN_EQ];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `w:A`] NEXTC_REV_RING) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    SUBGOAL_THEN `MEM (prevc rho w) (rho:(A)list)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[PREVC_MEM]; ALL_TAC] THEN
    SUBGOAL_THEN `(kr:A->color) (edge_map H (prevc rho w)) = kr w`
    SUBST1_TAC THENL
     [MP_TAC(SPEC `edge_map H (prevc rho (w:A))` kF) THEN
      ASM_SIMP_TAC[snipr_face; PLAIN_EQ; NEXTC_PREVC] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `w:A` kE) THEN ASM_SIMP_TAC[] THEN MESON_TAC[];
    (* edge clause, u off rr                                                 *)
    MP_TAC(SPEC `u:A` kE) THEN ASM_SIMP_TAC[];
    (* face clause, u on rr                                                  *)
    SUBGOAL_THEN `MEM (edge_map H u) (rho:(A)list)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `u:A`] MEM_REV_RING) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `w = edge_map H (u:A)` THEN
    SUBGOAL_THEN `u = edge_map H (w:A)` SUBST1_TAC THENL
     [EXPAND_TAC "w" THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[PLAIN_EQ];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `w:A`] NEXTC_REV_RING) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    SUBGOAL_THEN `MEM (nextc rho w) (rho:(A)list)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[NEXTC_MEM]; ALL_TAC] THEN
    SUBGOAL_THEN `edge_map H (edge_map H (nextc rho w)) = nextc rho (w:A)`
      SUBST1_TAC THENL [ASM_SIMP_TAC[PLAIN_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `(kr:A->color) (face_map H (nextc rho w)) = kr (nextc rho w)`
      SUBST1_TAC THENL
     [MP_TAC(SPEC `nextc rho (w:A)` kF) THEN ASM_SIMP_TAC[snipr_face];
      ALL_TAC] THEN
    MP_TAC(SPEC `edge_map H (w:A)` kF) THEN
    ASM_SIMP_TAC[snipr_face; PLAIN_EQ] THEN MESON_TAC[];
    (* face clause, u off rr                                                 *)
    MP_TAC(SPEC `u:A` kF) THEN ASM_SIMP_TAC[snipr_face] THEN
    SUBGOAL_THEN `~MEM (edge_map H u) (rho:(A)list)`
    (fun th -> SIMP_TAC[th]) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `u:A`] MEM_REV_RING) THEN
    ASM_REWRITE_TAC[]]));;

let DISK_REM_COTRACE = prove
 (`!(H:(A)hypermap) rho et.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) rho /\ ALL (\z. z IN dart H) rho /\
     proper_ring H rho /\ 2 <= LENGTH rho
     ==> (ring_trace (snip_rem H rho) (REVERSE rho) (rot1 et) <=>
          ring_trace (snip_disk H (rev_ring H rho)) (rev_ring H rho) et)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`] COTRACE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `rr = rev_ring H (rho:(A)list)` THEN
  REWRITE_TAC[ring_trace] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->color` STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `rho:(A)list`; `k:A->color`]
                  COLORING_DISK_OF_REM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `k:A->color` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MAP (k:A->color) rr = REVERSE (rot1 (MAP k rho))`
    SUBST1_TAC THENL
     [EXPAND_TAC "rr" THEN REWRITE_TAC[rev_ring; MAP_REVERSE; GSYM MAP_o] THEN
      REWRITE_TAC[GSYM MAP_REVERSE] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `MAP ((k:A->color) o edge_map H) rho =
                    MAP (\z. k (nextc rho z)) rho` SUBST1_TAC THENL
       [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[MAP_NEXTC_COL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(MAP (k:A->color) rho = [])` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[MAP_EQ_NIL]; ALL_TAC] THEN
    SUBGOAL_THEN `~(rot1 (MAP (k:A->color) rho) = [])` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_ROT1; LENGTH_MAP] THEN
      ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    UNDISCH_TAC `rot1 et = trace_col (MAP (k:A->color) (REVERSE rho))` THEN
    DISCH_THEN(MP_TAC o AP_TERM `rotr1:color list->color list`) THEN
    REWRITE_TAC[ROTR1_ROT1; GSYM MAP_REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[TRACE_COL_REVERSE; TRACE_COL_ROT1; REV_ROT1];
    EXISTS_TAC `\x:A. if MEM x rho then (k:A->color) (nextc rr (edge_map H x))
                     else k x` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "rr" THEN MATCH_MP_TAC COLORING_REM_OF_DISK THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `MAP (\x:A. if MEM x rho then (k:A->color) (nextc rr (edge_map H x))
                 else k x) (REVERSE rho) = rot1 (MAP k rr)`
      SUBST1_TAC THENL
     [SUBGOAL_THEN
       `MAP (\x:A. if MEM x rho then (k:A->color) (nextc rr (edge_map H x))
                   else k x) (REVERSE rho) =
        MAP (\x. k (nextc rr (edge_map H x))) (REVERSE rho)`
        SUBST1_TAC THENL
       [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; MEM_REVERSE] THEN
        SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `MAP (\x. (k:A->color) (nextc rr (edge_map H x))) (REVERSE rho) =
        MAP (\z. k (nextc rr z)) (MAP (edge_map H) (REVERSE rho))`
        SUBST1_TAC THENL [REWRITE_TAC[GSYM MAP_o; o_DEF]; ALL_TAC] THEN
      SUBGOAL_THEN `MAP (edge_map H) (REVERSE rho) = rr:(A)list`
      SUBST1_TAC THENL
       [EXPAND_TAC "rr" THEN REWRITE_TAC[rev_ring; MAP_REVERSE]; ALL_TAC] THEN
      ASM_SIMP_TAC[MAP_NEXTC_COL];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(MAP (k:A->color) rr = [])` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[MAP_EQ_NIL]; ALL_TAC] THEN
    ASM_SIMP_TAC[TRACE_COL_ROT1]]);;

(* The disk traces are Kempe-closed (Coq ring_disk_closed).                  *)

let DISK_RING_CLOSED = prove
 (`!(H:(A)hypermap) m r.
     planar_hypermap H /\ bridgeless H /\ plain_hypermap H /\
     cubic_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\y. y IN dart H) r /\
     nontrivial_ring H m r /\ 2 <= LENGTH r
     ==> kempe_closed (ring_trace (snip_disk H r) r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `proper_ring H (rev_ring H (r:(A)list))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PROPER_REV_RING] THEN MATCH_MP_TAC NONTRIVIAL_RING_PROPER THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `scycle H (rlink H) (rev_ring H r) /\
                ALL (\y:A. y IN dart H) (rev_ring H r) /\
                LENGTH (rev_ring H (r:(A)list)) = LENGTH r`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCYCLE_REV_RING; REV_RING_DART] THEN
    REWRITE_TAC[rev_ring; LENGTH_REVERSE; LENGTH_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `~(REVERSE (rev_ring H (r:(A)list)) = [])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_REVERSE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_trace (snip_disk H r) (r:(A)list) =
    ring_trace (snip_rem H (rev_ring H r)) (rotr1 (REVERSE (rev_ring H r)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `et:color list` THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rev_ring H (r:(A)list)`; `et:color list`]
                  DISK_REM_COTRACE) THEN
    ASM_SIMP_TAC[REV_REV_RING] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
    MATCH_MP_TAC RING_TRACE_ROT1_RING_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ROTR1_ITER_ROT1] THEN
  MATCH_MP_TAC KEMPE_CLOSED_RING_ITER_ROT1 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_DISK_CLOSED THEN
  ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sewing a Birkhoff_check1 configuration into the disk of a ring (Coq       *)
(* chkbP in Birkhoff_valid): the sewn map is smaller, hence colourable, so a *)
(* basis tree disjoint from ctu misses some disk trace (BIRKHOFF_VALID_      *)
(* CHKBP); here the disk of the ring is chordless (CHORDLESS_SNIP_DISK)      *)
(* because a chord would give a smaller nontrivial ring.                     *)
(* ------------------------------------------------------------------------- *)

let LIST_CYCLE_ORBIT_LIST = prove
 (`!(f:A->A) s x. f permutes s /\ FINITE s /\ x IN s
      ==> list_cycle (\a b. f a = b) (orbit_list f x)`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC[orbit_list; list_cycle; NOT_CONS_NIL; list_path] THEN
      CONJ_TAC THENL
   [REWRITE_TAC[LAST_ITERLIST] THEN
    MP_TAC(ISPECL[`f:A->A`;`s:A->bool`;`x:A`] ORBIT_SIZE_POS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`f:A->A`;`s:A->bool`;`x:A`] ITER_ORBIT_SIZE) THEN
      ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `m = orbit_size (f:A->A) x - 1` THEN
    SUBGOAL_THEN `orbit_size (f:A->A) x = SUC m` SUBST1_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ITER] THEN MESON_TAC[]; REWRITE_TAC[LIST_PATH_ITERLIST_FUN]]);;

let SEW_CONTEXT_SNIP_CPMAP = prove
 (`!(H:(A)hypermap) r cp.
     planar_hypermap H /\ scycle H (rlink H) r /\
     ALL (\y:A. y IN dart H) r /\ 2 <= LENGTH r /\
     LENGTH r = cprsize cp
     ==> sew_context (snip_disk H r) (FST(cpmap cp)) r
           (orbit_list (node_map (FST(cpmap cp)))
                       (node_map (FST(cpmap cp)) (SND(cpmap cp))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Gr = FST(cpmap cp):(num)hypermap` THEN
  ABBREV_TAC `z = node_map (Gr:(num)hypermap) (SND(cpmap cp))` THEN
  SUBGOAL_THEN `(z:num) IN dart Gr /\ SND(cpmap cp) IN dart Gr`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z"; "Gr"] THEN
    SIMP_TAC[CPMAP_PT_IN_DART; NODE_MAP_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r:(A)list = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_PATCH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_DISK_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[sew_context] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [patch]) THEN
    REWRITE_TAC[scycle] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`H:(A)hypermap`; `rlink (H:(A)hypermap)`; `r:(A)list`]
                  SCYCLE_PAIRWISE) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[GSYM ALL_MEM; IN] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_SUBSET_DISKN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FACE_SIMPLE_SNIPD_RING THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LIST_CYCLE_ORBIT_LIST THEN
    EXISTS_TAC `dart(Gr:(num)hypermap)` THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART];
    MATCH_MP_TAC PAIRWISE_ORBIT_LIST THEN
    EXISTS_TAC `dart(Gr:(num)hypermap)` THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART];
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `w:num` THEN
    MP_TAC(ISPECL [`node_map(Gr:(num)hypermap)`; `dart(Gr:(num)hypermap)`;
                   `z:num`; `w:num`] MEM_ORBIT_LIST) THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ORBIT_MAP_IN THEN
    MAP_EVERY EXISTS_TAC [`node_map(Gr:(num)hypermap)`; `z:num`] THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART];
    ASM_REWRITE_TAC[cprsize; cpring; LENGTH_REVERSE] THEN
    MP_TAC(ISPECL [`Gr:(num)hypermap`; `z:num`] ORBIT_SIZE_NODE_STEP) THEN
    MP_TAC(ISPECL [`node_map (Gr:(num)hypermap)`; `dart(Gr:(num)hypermap)`;
                   `z:num`] ORBIT_SIZE_POS) THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART] THEN DISCH_TAC THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[LENGTH_ORBIT_LIST; th])]);;

let COLG2 = prove
 (`!(H:(A)hypermap) n m cp r.
    minimal_counter_example H /\
    scycle H (rlink H) r /\
    ALL (\y:A. y IN dart H) r /\
    LENGTH r = n + 1 /\
    2 <= LENGTH r /\
    nontrivial_ring H m r /\
    Birkhoff_check1 n m cp /\
    chordless (snip_disk H r) r
    ==> four_colorable
          (sew_map (snip_disk H r) (FST(cpmap cp)) r
            (orbit_list (node_map (FST(cpmap cp)))
              (node_map (FST(cpmap cp)) (SND(cpmap cp)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cubic_hypermap (H:(A)hypermap) /\ connected_hypermap H`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MCE_CUBIC; MCE_CONNECTED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `cp:(cpstep)list`]
    SEW_CONTEXT_SNIP_CPMAP) THEN
  UNDISCH_THEN `minimal_counter_example (H:(A)hypermap)`
    (STRIP_ASSUME_TAC o REWRITE_RULE[minimal_counter_example]) THEN
  UNDISCH_THEN `Birkhoff_check1 n m cp`
    (STRIP_ASSUME_TAC o REWRITE_RULE[birkhoff_check1]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP SEW_MAP_PATCH) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_PATCH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `Gr = FST(cpmap cp):(num)hypermap` THEN
  ABBREV_TAC `x0 = SND(cpmap cp):num` THEN
  ABBREV_TAC
   `bGr = orbit_list (node_map (Gr:(num)hypermap)) (node_map Gr x0)` THEN
  ABBREV_TAC `Gd = snip_disk (H:(A)hypermap) r` THEN
  SUBGOAL_THEN
   `cubic_hypermap (Gd:(A)hypermap) /\ bridgeless Gd /\ planar_hypermap Gd /\
    (!x:A. x IN dart Gd /\ ~MEM x r ==> orbit_size (edge_map Gd) x = 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CUBIC_PATCH_D];
      ASM_MESON_TAC[PATCH_BRIDGELESS];
      EXPAND_TAC "Gd" THEN MATCH_MP_TAC PLANAR_SNIPD THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[PLAIN_PATCH_D]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:num) IN dart Gr` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x0"; "Gr"] THEN REWRITE_TAC[CPMAP_PT_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `planar_hypermap (Gr:(num)hypermap) /\ plain_hypermap Gr /\
    bridgeless Gr /\ quasicubic Gr (set_of_list (bGr:(num)list))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Gr" THEN
    ASM_SIMP_TAC[CPMAP_PLANAR; CPMAP_PLAIN; CPMAP_BRIDGELESS] THEN
    MP_TAC(SPEC `cp:(cpstep)list` CPMAP_CUBIC) THEN
    UNDISCH_THEN
     `orbit_list (node_map (Gr:(num)hypermap)) (node_map Gr x0) = bGr`
     (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[cpring; REVERSE_REVERSE; ORBIT_LIST_NODE_STEP;
                 NODE_MAP_IN_DART; SET_OF_LIST_ROT1];
    ALL_TAC] THEN
  MATCH_MP_TAC MINIMALITY_POLY THEN EXISTS_TAC `H:(A)hypermap` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PLANAR_PATCH];
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
      (ONCE_REWRITE_RULE[IMP_CONJ] BRIDGELESS_PATCH_COMPOSE)) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
      (ONCE_REWRITE_RULE[IMP_CONJ] PLAIN_PATCH_COMPOSE)) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CUBIC_PRECUBIC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
      (ONCE_REWRITE_RULE[IMP_CONJ] CUBIC_PATCH_COMPOSE)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cpcard cp < CARD(redart (H:(A)hypermap) r)` MP_TAC THENL
   [MATCH_MP_TAC CPCARD_LT_REDART THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `m:num`] THEN
    ASM_REWRITE_TAC[birkhoff_check1];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] CARD_PATCH))) THEN
  MP_TAC(SPEC `cp:(cpstep)list` CARD_CPMAP) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_REM_COMPONENTS) THEN
  ASM_SIMP_TAC[] THEN ARITH_TAC);;

let NO_INTERNAL_CHORD = prove
 (`!(H:(A)hypermap) n m r x y z.
     minimal_counter_example H /\
     (!r'. scycle H (rlink H) r' /\ LENGTH r' <= n
           ==> ~nontrivial_ring H 0 r') /\
     scycle H (rlink H) r /\ ALL (\w. w IN dart H) r /\
     LENGTH r = n + 1 /\ nontrivial_ring H m r /\
     MEM x r /\ MEM y r /\ z IN diskE H r /\ cface H x z /\ rlink H z y /\
     ~(y = nextc r x) /\ ~(x = nextc r y)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected_hypermap (H:(A)hypermap)` ASSUME_TAC THENL
   [MATCH_MP_TAC MCE_CONNECTED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  UNDISCH_TAC `minimal_counter_example (H:(A)hypermap)` THEN
  REWRITE_TAC[minimal_counter_example] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`;`m:num`;`r:(A)list`;`x:A`;`y:A`;`z:A`]
    RING_DISK_CHORD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH (r':(A)list) <= n` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (r':(A)list) < n + 1` THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `!r'. scycle (H:(A)hypermap) (rlink H) r' /\ LENGTH r' <= n ==>
                ~nontrivial_ring H 0 r'` THEN
  DISCH_THEN(MP_TAC o SPEC `r':(A)list`) THEN ASM_REWRITE_TAC[]);;

let CHORDLESS_SNIP_DISK = prove
 (`!(H:(A)hypermap) n m r.
     minimal_counter_example H /\
     (!r'. scycle H (rlink H) r' /\ LENGTH r' <= n
           ==> ~nontrivial_ring H 0 r') /\
     scycle H (rlink H) r /\ ALL (\w. w IN dart H) r /\
     LENGTH r = n + 1 /\ nontrivial_ring H m r
     ==> chordless (snip_disk H r) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `planar_hypermap (H:(A)hypermap) /\ plain_hypermap H /\ bridgeless H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example]; ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\x y:A. ~(x = y)) r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCYCLE_PAIRWISE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`] SNIP_DISK_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CHORDLESS_RING_EQ] THEN
  MAP_EVERY X_GEN_TAC [`y1:A`; `y2:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `y1:A = y2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `diskN H r (y1:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_SUBSET_DISKN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `adj (snip_disk H r) (y1:A) y2` THEN
  REWRITE_TAC[adj; rlink; GSYM cface] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `diskN H r (z:A)` ASSUME_TAC THENL
   [SUBGOAL_THEN `orbit_map (snipd_face H r) (y1:A) SUBSET diskN H r`
     MP_TAC THENL
     [MATCH_MP_TAC ORBIT_SUBSET THEN
      ASM_SIMP_TAC[SNIPD_FACE_PERMUTES] THEN ASM_REWRITE_TAC[IN];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
    REWRITE_TAC[IN] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `cface (snip_disk H r) (y1:A) z` THEN
    REWRITE_TAC[cface; face] THEN ASM_REWRITE_TAC[IN];
    ALL_TAC] THEN
  SUBGOAL_THEN `cface H (y1:A) z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `y1:A`; `z:A`]
      CFACE_SNIPD_HOMO) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `MEM (z:A) r` THENL
   [SUBGOAL_THEN `y1:A = z` SUBST_ALL_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `MEM (nextc r (z:A)) r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[NEXTC_MEM]; ALL_TAC] THEN
    SUBGOAL_THEN `cface H (nextc r (z:A)) y2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `nextc r (z:A)`; `y2:A`]
        CFACE_SNIPD_HOMO) THEN
      ASM_SIMP_TAC[RING_SUBSET_DISKN] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC
       `cface (snip_disk H r) (edge_map (snip_disk H r) (z:A)) y2` THEN
      ASM_REWRITE_TAC[snipd_edge];
      ALL_TAC] THEN
    CFACE_TAC[];
    SUBGOAL_THEN `(z:A) IN diskE H r` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN; diskE]; ALL_TAC] THEN
    SUBGOAL_THEN `diskN H r (edge_map H (z:A))` ASSUME_TAC THENL
     [SUBGOAL_THEN `edge_map H (z:A) = snipd_edge H r z` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[snipd_edge]; ALL_TAC] THEN
      MP_TAC(ISPECL [`snipd_edge (H:(A)hypermap) (r:(A)list)`;
                     `diskN (H:(A)hypermap) (r:(A)list)`; `z:A`]
        PERMUTES_IN_IMAGE) THEN
      ASM_SIMP_TAC[SNIPD_EDGE_PERMUTES] THEN ASM_REWRITE_TAC[IN];
      ALL_TAC] THEN
    SUBGOAL_THEN `cface H (edge_map H (z:A)) y2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `edge_map H (z:A)`; `y2:A`]
        CFACE_SNIPD_HOMO) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC
       `cface (snip_disk H r) (edge_map (snip_disk H r) (z:A)) y2` THEN
      ASM_REWRITE_TAC[snipd_edge];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `n:num`; `m:num`; `r:(A)list`;
                   `y1:A`; `y2:A`; `z:A`] NO_INTERNAL_CHORD) THEN
    ASM_REWRITE_TAC[rlink]]);;

let BIRKHOFF_VALID_CHKBP = prove
 (`!(H:(A)hypermap) n m cps r.
       minimal_counter_example H /\
       (!r'. scycle H (rlink H) r' /\ LENGTH r' <= n
             ==> ~nontrivial_ring H 0 r') /\
       ALL (Birkhoff_check1 n m) cps /\
       scycle H (rlink H) r /\ ALL (\y:A. y IN dart H) r /\
       LENGTH r = n + 1 /\ nontrivial_ring H m r
       ==> !ctu. EX (ctree_disjoint ctu) (MAP cpcolor cps)
                 ==> ?et. ring_trace (snip_disk H r) r (ctrace et) /\
                          ~ctree_mem ctu (etrace et)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 <= LENGTH (r:(A)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCYCLE_RLINK_GE2; minimal_counter_example]; ALL_TAC] THEN
  SUBGOAL_THEN `chordless (snip_disk (H:(A)hypermap) r) r` ASSUME_TAC THENL
   [MATCH_MP_TAC CHORDLESS_SNIP_DISK THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `m:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `ALL (Birkhoff_check1 n m) cps` THEN
  SPEC_TAC(`cps:((cpstep)list)list`,`cps:((cpstep)list)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; EX] THEN
  STRIP_TAC THEN X_GEN_TAC `ctu:ctree` THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `cubic_prog h /\ cprsize h = n + 1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[birkhoff_check1]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `n:num`; `m:num`; `h:(cpstep)list`;
                 `r:(A)list`] COLG2) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `h:(cpstep)list`]
    SEW_CONTEXT_SNIP_CPMAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[minimal_counter_example];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEW_MAP_PATCH) THEN
  DISCH_THEN(MP_TAC o C CONJ (ASSUME `2 <= LENGTH (r:(A)list)`)) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP COLORABLE_PATCH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `et':(color)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?rest. et' = ctrace rest`
    (X_CHOOSE_THEN `rest:(color)list` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `ring_trace (snip_disk (H:(A)hypermap) r) r et'` THEN
    REWRITE_TAC[ring_trace] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:A->color` (SUBST1_TAC o CONJUNCT2)) THEN
    MP_TAC(ISPEC `MAP (k:A->color) r` SUMT_TRACE) THEN
    MP_TAC(ISPEC `MAP (k:A->color) r` LENGTH_TRACE) THEN
    SPEC_TAC(`trace_col (MAP (k:A->color) r)`, `l:(color)list`) THEN
    LIST_INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH; LENGTH_MAP] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_ARITH_TAC;
      REWRITE_TAC[ctrace; sumt; CONS_11; ADDC_EQ_0] THEN MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `rest:(color)list` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ctu:ctree`; `cpcolor (h:(cpstep)list)`;
                 `etrace (rest:(color)list)`] CTREE_MEM_DISJOINT) THEN
  ASM_SIMP_TAC[CTREE_MEM_CPCOLOR; EVEN_ETRACE; GSYM ctrace;
               CHKBP_RING_RECONCILE]);;

(* Rings of length 0 and 1 are trivial.                                      *)

let FCARD_FACE_EMPTY = prove
 (`!(H:(A)hypermap). fcard_face H {} = 0`,
  GEN_TAC THEN REWRITE_TAC[fcard_face; set_of_orbits] THEN
  SUBGOAL_THEN `{orbit_map (face_map (H:(A)hypermap)) x | x IN {}} = {}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[CARD_CLAUSES]);;

let NTR_EMPTY = prove
 (`!(H:(A)hypermap). ~nontrivial_ring H 0 []`,
  GEN_TAC THEN REWRITE_TAC[nontrivial_ring] THEN
  SUBGOAL_THEN `diskF (H:(A)hypermap) [] = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN; diskF; diskN; EX];
    REWRITE_TAC[FCARD_FACE_EMPTY; LT_REFL]]);;

let DREACH_FROM_MEM = prove
 (`!(H:(A)hypermap) r x y. MEM x r /\ dreach H r x y ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dreach] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `p:(A)list` THEN
  STRUCT_CASES_TAC(ISPEC `p:(A)list` list_CASES) THEN
  REWRITE_TAC[list_path; dlink; LAST] THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[]);;

let DISKF_OFFDART_SING = prove
 (`!(H:(A)hypermap) x. ~(x IN dart H) ==> diskF H [x] = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[IN; diskF; diskN; EX; dconnect] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `inverse (node_map H) (x:A) = x` ASSUME_TAC THENL
   [MP_TAC(ISPEC `H:(A)hypermap` NODE_MAP_PERMUTES) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT2 o
               MATCH_MP PERMUTES_INVERSES) THEN
    ASM_SIMP_TAC[MAP_FIX_OFFDART];
    ALL_TAC] THEN
  SUBGOAL_THEN `x:A = y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `[x:A]`; `x:A`;
    `y:A`] DREACH_FROM_MEM) THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `dreach (H:(A)hypermap) [x] (inverse (node_map H) x) y` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `~fband H [x:A] y` THEN
      ASM_REWRITE_TAC[fband; EX; CFACE_REFL]]);;

let NTR_SING = prove
 (`!(H:(A)hypermap) x.
     minimal_counter_example H /\ scycle H (rlink H) [x]
     ==> ~nontrivial_ring H 0 [x]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x IN dart (H:(A)hypermap)` THENL
   [SUBGOAL_THEN `bridgeless (H:(A)hypermap)` ASSUME_TAC THENL
     [ASM_MESON_TAC[minimal_counter_example]; ALL_TAC] THEN
    UNDISCH_TAC `scycle H (rlink H) [x:A]` THEN
    REWRITE_TAC[scycle; list_cycle; NOT_CONS_NIL; list_path; LAST] THEN
    CFACE_TAC[];
    REWRITE_TAC[nontrivial_ring] THEN
    ASM_SIMP_TAC[DISKF_OFFDART_SING; FCARD_FACE_EMPTY] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Birkhoff_valid (Coq birkhoff.v:191-341): the Kempe-tree double recursion. *)
(* One check step (BIRKHOFF_STEP) serves both sides; the induction on the    *)
(* iteration count alternates the two sides.                                 *)
(* ------------------------------------------------------------------------- *)

let BUTLAST_REVERSE_TL = prove
 (`!cs:(A)list. ~(cs = []) ==> BUTLAST (REVERSE cs) = REVERSE (TL cs)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; REVERSE; TL; BUTLAST_APPEND; BUTLAST;
    APPEND_NIL]);;

(* One side of one iteration of Birkhoff_check2: if the picked trace cs is   *)
(* not a disk trace of r1, the closure keeps the validity invariant and the  *)
(* basis test must fail (else chkbP + Kempe_validP contradict), so the       *)
(* recursive check on the other side holds.                                  *)

let BIRKHOFF_STEP = prove
 (`!(H:(A)hypermap) n' m cps r1 ctu1 gtu1 cs chk.
     minimal_counter_example H /\
     (!r'. scycle H (rlink H) r' /\ LENGTH r' <= SUC n'
           ==> ~nontrivial_ring H 0 r') /\
     ALL (Birkhoff_check1 (SUC n') m) cps /\
     LENGTH r1 = SUC n' + 1 /\ nontrivial_ring H m r1 /\
     scycle H (rlink H) r1 /\
     kempe_valid n' (\et. ~ring_trace (snip_disk H r1) r1 (rotr1 et))
                   ctu1 CtreeEmpty GtreeEmpty gtu1 /\
     LENGTH cs = SUC n' + 1 /\ sumt cs = Color0 /\
     ~ring_trace (snip_disk H r1) r1 (rotr1 cs) /\
     do_Birkhoff_check2 (SUC n') (\t. EX (ctree_disjoint t) (MAP cpcolor cps))
       (BUTLAST cs) ctu1 gtu1 chk
     ==> chk (FST(kempe_tree_closure n' (SUC n') ctu1
                    (ctree_of_ttail (etrace (BUTLAST cs))) gtu1))
             (gtree_pair_sub
               (SND(kempe_tree_closure n' (SUC n') ctu1
                      (ctree_of_ttail (etrace (BUTLAST cs))) gtu1)) T) /\
         kempe_valid n' (\et. ~ring_trace (snip_disk H r1) r1 (rotr1 et))
           (FST(kempe_tree_closure n' (SUC n') ctu1
                  (ctree_of_ttail (etrace (BUTLAST cs))) gtu1))
           CtreeEmpty GtreeEmpty
           (gtree_pair_sub
             (SND(kempe_tree_closure n' (SUC n') ctu1
                    (ctree_of_ttail (etrace (BUTLAST cs))) gtu1)) T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `planar_hypermap (H:(A)hypermap) /\ bridgeless H /\ plain_hypermap H /\
    ~four_colorable H /\ cubic_hypermap H /\ connected_hypermap H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC; MCE_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r1:(A)list = []) /\ 2 <= LENGTH (r1:(A)list) /\
                ~(cs:color list = [])` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\y:A. y IN dart H) r1` ASSUME_TAC THENL
   [MATCH_MP_TAC SCYCLE_GE2_ALL_DART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `kempe_closed (ring_trace (snip_disk (H:(A)hypermap) r1) r1)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC DISK_RING_CLOSED THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `do_Birkhoff_check2 (SUC n') (\t. EX (ctree_disjoint t) (MAP cpcolor cps))
      (BUTLAST cs) ctu1 gtu1 chk` THEN
  REWRITE_TAC[do_Birkhoff_check2] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC n' - 1 = n'`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `pr = kempe_tree_closure n' (SUC n') ctu1
                     (ctree_of_ttail (etrace (BUTLAST cs))) gtu1` THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (ASSUME_TAC o REWRITE_RULE[GTREE_EMPTY_IFF]) MP_TAC) THEN
  SUBGOAL_THEN
   `kempe_valid n'
      (\et. ~ring_trace (snip_disk (H:(A)hypermap) r1) r1 (rotr1 et))
      (FST pr) CtreeEmpty GtreeEmpty (gtree_pair_sub (SND pr) T)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n':num`;
      `\et. ~ring_trace (snip_disk (H:(A)hypermap) r1) r1 (rotr1 et)`;
      `SUC n'`; `ctu1:ctree`;
      `ctree_of_ttail (etrace (BUTLAST (cs:color list)))`; `gtu1:gtree`]
      KEMPE_TREE_CLOSURE_CORRECT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`n':num`;
        `\et. ~ring_trace (snip_disk (H:(A)hypermap) r1) r1 (rotr1 et)`;
        `ctu1:ctree`; `ctree_of_ttail (etrace (BUTLAST (cs:color list)))`;
        `GtreeEmpty`; `gtu1:gtree`] KEMPE_VALID_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `~MEM Color0 (etrace (BUTLAST (cs:color list)))`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[etrace; MEM_COLOR0_PERMT]; ALL_TAC] THEN
      X_GEN_TAC `et0:color list` THEN ASM_SIMP_TAC[CTREE_OF_TTAIL_MEM] THEN
      DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC KEMPE_COCLOSURE_SELF THEN BETA_TAC THEN
        REWRITE_TAC[etrace; CTRACE_A_PERMT] THEN
        ASM_SIMP_TAC[CTRACE_A_BUTLAST_EQ; ROTR1_PERMT] THEN DISCH_TAC THEN
        UNDISCH_TAC
         `~ring_trace (snip_disk (H:(A)hypermap) r1) r1 (rotr1 cs)` THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `rotr1 cs = permt (inv_eperm (etrace_perm (BUTLAST cs)))
                           (permt (etrace_perm (BUTLAST cs)) (rotr1 cs))`
        SUBST1_TAC THENL
         [REWRITE_TAC[PERMT_INV_CANCEL]; MATCH_MP_TAC RING_TRACE_PERMT] THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[etrace; LENGTH_PERMT; LENGTH_BUTLAST_1] THEN ARITH_TAC];
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ACCEPT_TAC) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `SUC n'`; `m:num`; `cps:((cpstep)list)list`;
                 `r1:(A)list`] BIRKHOFF_VALID_CHKBP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `et1:color list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH (et1:color list) = SUC n'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`snip_disk (H:(A)hypermap) r1`; `r1:(A)list`;
                   `ctrace et1`] RING_TRACE_LENGTH) THEN
    ASM_REWRITE_TAC[ctrace; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`n':num`;
    `\et. ~ring_trace (snip_disk (H:(A)hypermap) r1) r1 (rotr1 et)`;
    `FST(pr:ctree#gtree_pair)`; `CtreeEmpty`; `GtreeEmpty`;
    `gtree_pair_sub (SND (pr:ctree#gtree_pair)) T`] KEMPE_VALIDP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `et1:color list`) THEN
  ASM_REWRITE_TAC[kempe_coclosure] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\X:color list.
       ring_trace (snip_disk (H:(A)hypermap) r1) r1 (rotr1 X)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC KEMPE_CLOSED_ROTR1 THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      BETA_TAC THEN REWRITE_TAC[CTRACE_A_ROT1; ROTR1_ROT1] THEN
        ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `etx:color list` MP_TAC) THEN BETA_TAC THEN
    REWRITE_TAC[TAUT `~p /\ p <=> F`]]);;

(* The double recursion on the iteration count.                              *)

let BIRKHOFF_VALID_INDUCT = prove
 (`!(H:(A)hypermap) n' m cps.
     minimal_counter_example H /\
     (!r'. scycle H (rlink H) r' /\ LENGTH r' <= SUC n'
           ==> ~nontrivial_ring H 0 r') /\
     ALL (Birkhoff_check1 (SUC n') m) cps
     ==> !nm r1 ctu1 gtu1 ctu2 gtu2.
           LENGTH r1 = SUC n' + 1 /\ nontrivial_ring H m r1 /\
           scycle H (rlink H) r1 /\
           kempe_valid n' (\et. ~ring_trace (snip_disk H r1) r1 (rotr1 et))
                         ctu1 CtreeEmpty GtreeEmpty gtu1 /\
           kempe_valid n' (\et. ~ring_trace (snip_disk H (rev_ring H r1))
                                            (rev_ring H r1) (rotr1 et))
                         ctu2 CtreeEmpty GtreeEmpty gtu2
           ==> ~(Birkhoff_check2 (SUC n')
                   (\t. EX (ctree_disjoint t) (MAP cpcolor cps))
                   ctu1 gtu1 nm ctu2 gtu2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[birkhoff_check2]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `planar_hypermap (H:(A)hypermap) /\ bridgeless H /\ plain_hypermap H /\
    ~four_colorable H /\ cubic_hypermap H /\ connected_hypermap H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC; MCE_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r1:(A)list = []) /\ 2 <= LENGTH (r1:(A)list)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\y:A. y IN dart H) r1` ASSUME_TAC THENL
   [MATCH_MP_TAC SCYCLE_GE2_ALL_DART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `proper_ring (H:(A)hypermap) r1` ASSUME_TAC THENL
   [MATCH_MP_TAC NONTRIVIAL_RING_PROPER THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (rev_ring H r1) = SUC n' + 1 /\
                nontrivial_ring H m (rev_ring H r1) /\
                scycle H (rlink H) (rev_ring H r1) /\
                rev_ring H (rev_ring (H:(A)hypermap) r1) = r1`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCYCLE_REV_RING; NONTRIVIAL_REV_RING; REV_REV_RING] THEN
    ASM_REWRITE_TAC[rev_ring; LENGTH_REVERSE; LENGTH_MAP]; ALL_TAC] THEN
  ABBREV_TAC `r2 = rev_ring (H:(A)hypermap) r1` THEN
  REWRITE_TAC[birkhoff_check2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `cs = ctree_pick_rev ctu1 ctu2` THEN
  ASM_CASES_TAC `cs:color list = []` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (cs:color list) = SUC n' + 1 /\ sumt cs = Color0`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cs" THEN REWRITE_TAC[SUMT_CTREE_PICK_REV] THEN
    MP_TAC(ISPECL [`SUC n'`; `ctu1:ctree`; `ctu2:ctree`]
      SIZE_CTREE_PICK_REV) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `kempe_valid n'
        (\et. ~ring_trace (snip_disk (H:(A)hypermap) r2) r2 (rotr1 et))
        ctu2 CtreeEmpty GtreeEmpty gtu2` THEN
      REWRITE_TAC[kempe_valid] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[LENGTH_EQ_NIL]];
    ALL_TAC] THEN
  PURE_ONCE_REWRITE_TAC[TAUT `~p <=> p ==> F`] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `ring_trace (snip_disk (H:(A)hypermap) r1) r1 (rotr1 cs)` THENL
   [ASM_CASES_TAC `ring_trace (snip_disk (H:(A)hypermap) r2) r2
                              (rotr1 (REVERSE cs))` THENL
     [UNDISCH_TAC `~four_colorable (H:(A)hypermap)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC COLORABLE_FROM_RING THEN
      MAP_EVERY EXISTS_TAC [`r1:(A)list`; `rotr1 (cs:color list)`] THEN
      ASM_REWRITE_TAC[ROT1_ROTR1] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `r1:(A)list`;
                     `rotr1 (REVERSE (cs:color list))`] DISK_REM_COTRACE) THEN
      ASM_REWRITE_TAC[ROT1_ROTR1];
      MP_TAC(ISPECL [`H:(A)hypermap`; `n':num`; `m:num`;
                     `cps:((cpstep)list)list`;
                     `r2:(A)list`; `ctu2:ctree`; `gtu2:gtree`;
                     `REVERSE (cs:color list)`;
                     `Birkhoff_check2 (SUC n')
                        (\t. EX (ctree_disjoint t) (MAP cpcolor cps))
                        ctu1 gtu1 nm`]
                    BIRKHOFF_STEP) THEN
      ASM_SIMP_TAC[BUTLAST_REVERSE_TL; SUMT_REVERSE; LENGTH_REVERSE] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`r1:(A)list`; `ctu1:ctree`; `gtu1:gtree`;
        `FST(kempe_tree_closure n' (SUC n') ctu2
               (ctree_of_ttail (etrace (REVERSE (TL (cs:color list))))) gtu2)`;
        `gtree_pair_sub
           (SND(kempe_tree_closure n' (SUC n') ctu2
                  (ctree_of_ttail (etrace (REVERSE (TL (cs:color list)))))
                  gtu2)) T`]) THEN
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`H:(A)hypermap`; `n':num`; `m:num`;
                   `cps:((cpstep)list)list`;
                   `r1:(A)list`; `ctu1:ctree`; `gtu1:gtree`; `cs:color list`;
                   `Birkhoff_check2 (SUC n')
                      (\t. EX (ctree_disjoint t) (MAP cpcolor cps))
                      ctu2 gtu2 nm`]
                  BIRKHOFF_STEP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`r2:(A)list`; `ctu2:ctree`; `gtu2:gtree`;
      `FST(kempe_tree_closure n' (SUC n') ctu1
             (ctree_of_ttail (etrace (BUTLAST (cs:color list)))) gtu1)`;
      `gtree_pair_sub
         (SND(kempe_tree_closure n' (SUC n') ctu1
                (ctree_of_ttail (etrace (BUTLAST (cs:color list)))) gtu1))
         T`]) THEN
    ASM_REWRITE_TAC[]]);;

(* Birkhoff_valid (Coq birkhoff.v:191).                                      *)

let BIRKHOFF_VALID = prove
 (`!(H:(A)hypermap) n.
     minimal_counter_example H /\
     (!r. scycle H (rlink H) r /\ LENGTH r <= n ==> ~nontrivial_ring H 0 r)
     ==> !m r. Birkhoff_check n m /\ scycle H (rlink H) r /\ LENGTH r = n + 1
               ==> ~nontrivial_ring H m r`,
  GEN_TAC THEN GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n':num` SUBST1_TAC)
    (SPEC `n:num` num_CASES) THENL
   [STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `r:(A)list`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?x:A. r = [x]` (X_CHOOSE_THEN `x:A` SUBST_ALL_TAC) THENL
     [UNDISCH_TAC `LENGTH (r:(A)list) = 0 + 1` THEN
      REWRITE_TAC[ARITH_RULE `0 + 1 = SUC 0`; LENGTH_EQ_CONS;
                  LENGTH_EQ_NIL] THEN
      MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC NTR_MONO THEN MATCH_MP_TAC NTR_SING THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `r:(A)list`] THEN
    REWRITE_TAC[birkhoff_check] THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `n':num`; `m:num`;
      `cps:((cpstep)list)list`]
                  BIRKHOFF_VALID_INDUCT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`niter:num`; `r:(A)list`;
      `ctree_init_tree(SUC n')`; `gtree_init_tree(SUC n')`;
      `ctree_init_tree(SUC n')`; `gtree_init_tree(SUC n')`]) THEN
    ASM_REWRITE_TAC[KEMPE_VALID_INIT]]);;

(* The Birkhoff theorem (Coq birkhoff.v:345): a minimal counter-example has  *)
(* no nontrivial ring of size at most 5, except possibly rings of size 5     *)
(* with a single face on one side.                                           *)

let BIRKHOFF = prove
 (`!(H:(A)hypermap). minimal_counter_example H
     ==> !r. LENGTH r <= 5 /\ scycle H (rlink H) r
             ==> ~nontrivial_ring H (if LENGTH r = 5 then 1 else 0) r`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
   (ISPEC `H:(A)hypermap` BIRKHOFF_VALID)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. n <= 4
        ==> !r:(A)list. scycle H (rlink H) r /\ LENGTH r <= n
                        ==> ~nontrivial_ring H 0 r`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN DISCH_TAC THEN X_GEN_TAC `r:(A)list` THEN STRIP_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL; LE; NTR_EMPTY]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_CASES_TAC `LENGTH (r:(A)list) <= n` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `LENGTH (r:(A)list) = n + 1` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `n = 0 \/ n = 1 \/ n = 2 \/ n = 3`
     (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `?x:A. r = [x]` (X_CHOOSE_THEN `x:A` SUBST_ALL_TAC) THENL
       [UNDISCH_TAC `LENGTH (r:(A)list) = 0 + 1` THEN
        REWRITE_TAC[ARITH_RULE `0 + 1 = SUC 0`; LENGTH_EQ_CONS;
                    LENGTH_EQ_NIL] THEN
        MESON_TAC[];
        MATCH_MP_TAC NTR_SING THEN ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[birkhoff2];
      ASM_MESON_TAC[birkhoff3];
      ASM_MESON_TAC[birkhoff4]];
    X_GEN_TAC `r:(A)list` THEN STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[birkhoff5; ARITH_RULE `4 <= 4 /\ 5 = 4 + 1`];
      ASM_MESON_TAC[ARITH_RULE `l <= 5 /\ ~(l = 5) ==> l <= 4`; LE_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Spoke rings (Coq birkhoff.v, section SpokeRing).  The spoke ring of a     *)
(* dart x is the list of the spokes face(edge y) of the darts y of the face  *)
(* of x, in reverse order.                                                   *)
(* ------------------------------------------------------------------------- *)

let spoke = new_definition
  `spoke (H:(A)hypermap) y = face_map H (edge_map H y)`;;

let spoke_ring = new_definition
  `spoke_ring (H:(A)hypermap) x = MAP (spoke H) (REVERSE (orbit_list (face_map
    H) x))`;;

let INJ_SPOKE = prove
 (`!(H:(A)hypermap) y1 y2. spoke H y1 = spoke H y2 ==> y1 = y2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[spoke] THEN
  DISCH_THEN(MP_TAC o AP_TERM `node_map (H:(A)hypermap)`) THEN
  REWRITE_TAC[edgeK]);;

let SPOKE_EQ = prove
 (`!(H:(A)hypermap) y z. (y = spoke H z <=> z = node_map H y)`,
  REWRITE_TAC[spoke] THEN MESON_TAC[edgeK; nodeK]);;

let SPOKE_NODE = prove
 (`!(H:(A)hypermap) y. spoke H (node_map H y) = y`,
  REWRITE_TAC[spoke; nodeK]);;

let NODE_NODE_EQ_SPOKE = prove
 (`!(H:(A)hypermap) y.
     cubic_hypermap H ==> node_map H (node_map H y) = spoke H y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[spoke] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `y:A`] edgeK) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `y:A`] CUBIC_EQ_U) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[NODEI]);;

let CFACE_MEM_ORBIT_LIST = prove
 (`!(H:(A)hypermap) x z.
     x IN dart H ==> (cface H x z <=> MEM z (orbit_list (face_map H) x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cface; face] THEN
  MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
    MEM_ORBIT_LIST) THEN
  ASM_SIMP_TAC[FACE_MAP_PERMUTES; FINITE_DART]);;

let SIZE_SPOKE_RING = prove
 (`!(H:(A)hypermap) x. x IN dart H ==> LENGTH (spoke_ring H x) = arity H x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[spoke_ring; LENGTH_MAP; LENGTH_REVERSE; arity] THEN
  MATCH_MP_TAC LENGTH_ORBIT_LIST THEN MATCH_MP_TAC ORBIT_SIZE_POS THEN
  EXISTS_TAC `dart(H:(A)hypermap)` THEN
  ASM_SIMP_TAC[FACE_MAP_PERMUTES; FINITE_DART]);;

let MEM_SPOKE_RING = prove
 (`!(H:(A)hypermap) x y.
     x IN dart H ==> (MEM y (spoke_ring H x) <=> cface H x (node_map H y))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[spoke_ring; MEM_MAP; MEM_REVERSE; SPOKE_EQ] THEN
  ASM_SIMP_TAC[CFACE_MEM_ORBIT_LIST] THEN MESON_TAC[]);;

let SPOKE_RING_DART = prove
 (`!(H:(A)hypermap) x z.
     x IN dart H /\ MEM z (spoke_ring H x) ==> z IN dart H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `node_map H (z:A) IN dart H` MP_TAC THENL
   [ASM_MESON_TAC[MEM_SPOKE_RING; CFT_DART];
    MESON_TAC[NODE_MAP_IN_DART; nodeK; EDGE_MAP_IN_DART; FACE_MAP_IN_DART]]);;

let FBAND_SPOKE_RING = prove
 (`!(H:(A)hypermap) x y.
     x IN dart H /\ y IN dart H
     ==> (fband H (spoke_ring H x) y <=> adj H x y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FBAND_MEM_IFF; adj; rlink; GSYM cface] THEN
  ASM_SIMP_TAC[MEM_SPOKE_RING] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `node_map (H:(A)hypermap) z`;
    EXISTS_TAC `face_map (H:(A)hypermap) (edge_map H z)`] THEN
  CFACE_TAC[]);;

let NEXT_SPOKE_RING = prove
 (`!(H:(A)hypermap) x y.
     plain_hypermap H /\ cubic_hypermap H /\ x IN dart H /\
     MEM y (spoke_ring H x)
     ==> nextc (spoke_ring H x) y = face_map H (spoke H y)`,
  REWRITE_TAC[spoke_ring] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `PAIRWISE (\a b:A. ~(a = b)) (orbit_list (face_map (H:(A)hypermap)) x) /\
    list_cycle (\a b:A. face_map H a = b) (orbit_list (face_map H) x)`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
      ORBIT_LIST_PAIRWISE) THEN
    MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
      LIST_CYCLE_ORBIT_LIST) THEN
    ASM_SIMP_TAC[FACE_MAP_PERMUTES; FINITE_DART] THEN
    REWRITE_TAC[orbit_list] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `l = orbit_list (face_map (H:(A)hypermap)) x` THEN
  SUBGOAL_THEN `MEM (node_map (H:(A)hypermap) y) l` ASSUME_TAC THENL
   [UNDISCH_TAC `MEM y (MAP (spoke (H:(A)hypermap)) (REVERSE l))` THEN
    REWRITE_TAC[MEM_MAP; MEM_REVERSE; SPOKE_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nextc (MAP (spoke (H:(A)hypermap)) (REVERSE l)) y =
    spoke H (prevc l (node_map H y))`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`spoke (H:(A)hypermap)`; `REVERSE (l:(A)list)`;
                   `node_map (H:(A)hypermap) y`] NEXTC_MAP) THEN
    ASM_REWRITE_TAC[MEM_REVERSE; PAIRWISE_REVERSE; SPOKE_NODE; prevc] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC PAIRWISE_IMP_MEM THEN EXISTS_TAC `\a b:A. ~(a = b)` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MESON_TAC[INJ_SPOKE]];
    ALL_TAC] THEN
  ABBREV_TAC `p = prevc (l:(A)list) (node_map (H:(A)hypermap) y)` THEN
  SUBGOAL_THEN `MEM (p:A) l /\ nextc l p = node_map H y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_SIMP_TAC[PREVC_MEM; NEXTC_PREVC]; ALL_TAC] THEN
  SUBGOAL_THEN `face_map H (p:A) = node_map H y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `l:(A)list`; `p:A`]
      NEXTC_CYCLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `p = edge_map H (node_map H (node_map H (y:A)))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `face_map H (p:A) = node_map H y` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[faceK];
    ALL_TAC] THEN
  REWRITE_TAC[spoke] THEN
    ASM_SIMP_TAC[CFT_PLAIN_EE; NODE_NODE_EQ_SPOKE; spoke]);;

(* ------------------------------------------------------------------------- *)
(* List cycles from the successor property (Coq cycle_from_next).            *)
(* ------------------------------------------------------------------------- *)

let LIST_PATH_TRANSFER = prove
 (`!(R:A->A->bool) r.
     (!y. MEM y r ==> R y (nextc r y))
     ==> !l z. MEM z r /\ ALL (\y. MEM y r) l /\
               list_path (\a b. nextc r a = b) z l
               ==> list_path R z l`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_path; ALL] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LIST_CYCLE_FROM_NEXTC = prove
 (`!(R:A->A->bool) r.
     ~(r = []) /\ PAIRWISE (\x y. ~(x = y)) r /\
     (!y. MEM y r ==> R y (nextc r y))
     ==> list_cycle R r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[list_cycle] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`R:A->A->bool`; `r:(A)list`] LIST_PATH_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[MEM_LAST; GSYM ALL_MEM] THEN
  MP_TAC(ISPEC `r:(A)list` LIST_CYCLE_NEXTC) THEN
  ASM_REWRITE_TAC[list_cycle]);;

(* ------------------------------------------------------------------------- *)
(* The inverse of the node map of a cubic map.                               *)
(* ------------------------------------------------------------------------- *)

let INVERSE_NODE_CUBIC = prove
 (`!(H:(A)hypermap) w.
     cubic_hypermap H /\ w IN dart H
     ==> inverse (node_map H) w = node_map H (node_map H w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`node_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`]
    PERMUTES_INVERSE_EQ) THEN
  ASM_SIMP_TAC[NODE_MAP_PERMUTES] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC CUBIC_EQ THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A 2-ring [x; y] with y <> edge x is nontrivial; hence "double darts" are  *)
(* impossible in a minimal counter-example (Coq double_dart).                *)
(* ------------------------------------------------------------------------- *)

let NONTRIVIAL_CYCLE2 = prove
 (`!(H:(A)hypermap) x y.
     minimal_counter_example H /\ x IN dart H /\ y IN dart H /\
     scycle H (rlink H) [x; y] /\ ~(edge_map H x = y)
     ==> nontrivial_ring H 0 [x; y]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `planar_hypermap H /\ bridgeless (H:(A)hypermap) /\
                plain_hypermap H /\ cubic_hypermap H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC]; ALL_TAC] THEN
  SUBGOAL_THEN `cface H (edge_map H (x:A)) y` ASSUME_TAC THENL
   [UNDISCH_TAC `scycle H (rlink H) [x:A; y]` THEN
    REWRITE_TAC[scycle; list_cycle; NOT_CONS_NIL; LAST; TL; HD; list_path;
                rlink] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `node_map H x IN dart H /\ edge_map H x IN dart H /\
                node_map H (edge_map H (x:A)) IN dart H /\
                face_map H x IN dart H /\ edge_map H (edge_map H x) = x /\
                face_map H (edge_map H x) = node_map H (node_map H x)`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_IN_DART; EDGE_MAP_IN_DART; FACE_MAP_IN_DART;
                 CFT_PLAIN_EE] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CUBIC_EQ' THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `[x:A; y]`] NONTRIVIAL0P) THEN
  ASM_REWRITE_TAC[ALL] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `node_map H (x:A)` THEN REWRITE_TAC[IN; diskF] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[DISKN_NODE_EQ] THEN MATCH_MP_TAC RING_IN_DISKN THEN
      ASM_REWRITE_TAC[MEM];
      CFACE_TAC[]];
    EXISTS_TAC `node_map H (edge_map H (x:A))` THEN
    ASM_REWRITE_TAC[diskFC] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[DISKN_NODE_EQ] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `[x:A; y]`; `x:A`] DISKN_EDGE_RING) THEN
      ASM_REWRITE_TAC[ALL; MEM; PROPER_TWO];
      CFACE_TAC[]]]);;

let DOUBLE_DART = prove
 (`!(H:(A)hypermap) x y.
     minimal_counter_example H /\ x IN dart H /\ y IN dart H /\
     cface H x y /\ cface H (edge_map H x) (edge_map H y)
     ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bridgeless (H:(A)hypermap) /\ plain_hypermap H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map H (y:A) IN dart H` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `scycle H (rlink H) [x:A; edge_map H y]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `[x:A; edge_map H y]`] SRCYCLEI) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; ALL] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[srcycle; NOT_CONS_NIL; HD; TL; srpath; ALL] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nontrivial_ring H 0 [x:A; edge_map H y]` ASSUME_TAC THENL
   [MATCH_MP_TAC NONTRIVIAL_CYCLE2 THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[EDGEI];
    ALL_TAC] THEN
  MP_TAC(ISPEC `H:(A)hypermap` BIRKHOFF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `[x:A; edge_map H y]`) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The spoke ring is a simple rlink cycle whose disk is the face of x.       *)
(* ------------------------------------------------------------------------- *)

let FACE_SIMPLE_SPOKE_RING = prove
 (`!(H:(A)hypermap) x.
     minimal_counter_example H /\ x IN dart H
     ==> face_simple H (spoke_ring H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FACE_SIMPLE_EQ_PAIRWISE; spoke_ring; PAIRWISE_MAP;
              PAIRWISE_REVERSE] THEN
  MATCH_MP_TAC PAIRWISE_IMP_MEM THEN EXISTS_TAC `\a b:A. ~(a = b)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `cface H x (a:A) /\ cface H x (b:A)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[CFACE_MEM_ORBIT_LIST]; ALL_TAC] THEN
    SUBGOAL_THEN `b:A = a` MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC DOUBLE_DART THEN EXISTS_TAC `H:(A)hypermap` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cface H (spoke H b) (spoke H (a:A))` THEN
    REWRITE_TAC[spoke] THEN CFACE_TAC[];
    MP_TAC(ISPECL [`face_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
      ORBIT_LIST_PAIRWISE) THEN
    ASM_SIMP_TAC[FACE_MAP_PERMUTES; FINITE_DART] THEN
      REWRITE_TAC[orbit_list]]);;

let SPOKE_RING_PAIRWISE = prove
 (`!(H:(A)hypermap) x.
     minimal_counter_example H /\ x IN dart H
     ==> PAIRWISE (\a b:A. ~(a = b)) (spoke_ring H x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_SIMPLE_PAIRWISE_GEN THEN
  EXISTS_TAC `H:(A)hypermap` THEN MATCH_MP_TAC FACE_SIMPLE_SPOKE_RING THEN
  ASM_REWRITE_TAC[]);;

let SCYCLE_SPOKE_RING = prove
 (`!(H:(A)hypermap) x.
     minimal_counter_example H /\ x IN dart H
     ==> scycle H (rlink H) (spoke_ring H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `plain_hypermap H /\ bridgeless (H:(A)hypermap) /\
                cubic_hypermap H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC]; ALL_TAC] THEN
  ASM_SIMP_TAC[scycle; FACE_SIMPLE_SPOKE_RING] THEN
  MATCH_MP_TAC LIST_CYCLE_FROM_NEXTC THEN
  ASM_SIMP_TAC[SPOKE_RING_PAIRWISE] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM LENGTH_EQ_NIL; SIZE_SPOKE_RING] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] ARITY_POS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL
     [MATCH_MP_TAC SPOKE_RING_DART THEN EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NEXT_SPOKE_RING] THEN REWRITE_TAC[spoke] THEN CFACE_TAC[]]);;

let DISKF_SPOKE_RING_BWD = prove
 (`!(H:(A)hypermap) x y.
     minimal_counter_example H /\ x IN dart H /\ cface H x y
     ==> diskF H (spoke_ring H x) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `plain_hypermap H /\ bridgeless (H:(A)hypermap) /\
                cubic_hypermap H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (face_map H (edge_map H (y:A))) (spoke_ring H x)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEM_SPOKE_RING] THEN ASM_REWRITE_TAC[edgeK]; ALL_TAC] THEN
  REWRITE_TAC[diskF] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM(ISPECL [`H:(A)hypermap`;
    `y:A`] edgeK)] THEN
    ASM_SIMP_TAC[DISKN_NODE_EQ; EDGE_MAP_IN_DART; FACE_MAP_IN_DART] THEN
    MATCH_MP_TAC RING_IN_DISKN THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART; FACE_MAP_IN_DART];
    REWRITE_TAC[FBAND_MEM_IFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `cface H x (node_map H (z:A))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM MEM_SPOKE_RING]; CFACE_TAC[]]]);;

let SPOKE_DISK_PATH = prove
 (`!(H:(A)hypermap) x.
     plain_hypermap H /\ cubic_hypermap H /\ x IN dart H
     ==> !p a. cface H x a /\ list_path (dlink H (spoke_ring H x)) a p /\
               ~fband H (spoke_ring H x) (LAST(CONS a p))
               ==> cface H x (LAST(CONS a p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LAST] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN
  SUBGOAL_THEN `LAST(CONS (a:A)(CONS h t)) = LAST(CONS h t)` SUBST1_TAC THENL
   [REWRITE_TAC[LAST; NOT_CONS_NIL]; ALL_TAC] THEN
  REWRITE_TAC[list_path; dlink; clink] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `MEM (h:A) (spoke_ring (H:(A)hypermap) x)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MEM_SPOKE_RING] THEN CFACE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `fband (H:(A)hypermap) (spoke_ring H x) (h:A)`
    ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `~fband (H:(A)hypermap) (spoke_ring H x) (LAST (CONS h t))` THEN
    UNDISCH_TAC `list_path (dlink (H:(A)hypermap) (spoke_ring H x)) h t` THEN
    STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THEN
    REWRITE_TAC[list_path; LAST; dlink; NOT_CONS_NIL] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN CFACE_TAC[]]);;

let SPOKE_RFZ0 = prove
 (`!(H:(A)hypermap) x y0.
     plain_hypermap H /\ cubic_hypermap H /\ x IN dart H /\
     MEM y0 (spoke_ring H x)
     ==> MEM (face_map H (inverse (node_map H) y0)) (spoke_ring H x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y0:A) IN dart H` ASSUME_TAC THENL
   [MATCH_MP_TAC SPOKE_RING_DART THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `MEM (y0:A) (spoke_ring H x)` THEN
  ASM_SIMP_TAC[MEM_SPOKE_RING; CFT_PLAIN_NF; INVERSE_NODE_CUBIC] THEN
  CFACE_TAC[]);;

let DISKF_SPOKE_RING_FWD = prove
 (`!(H:(A)hypermap) x y.
     minimal_counter_example H /\ x IN dart H /\ diskF H (spoke_ring H x) y
     ==> cface H x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `plain_hypermap H /\ bridgeless (H:(A)hypermap) /\
                cubic_hypermap H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC]; ALL_TAC] THEN
  UNDISCH_TAC `diskF (H:(A)hypermap) (spoke_ring H x) y` THEN
  REWRITE_TAC[diskF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `spoke_ring (H:(A)hypermap) x`; `y:A`]
    DISKN_DLINK_WITNESS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A` (X_CHOOSE_THEN `p:(A)list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:A) IN dart H` ASSUME_TAC THENL
   [MATCH_MP_TAC SPOKE_RING_DART THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `MEM (face_map H (inverse (node_map H) (y0:A))) (spoke_ring H x)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SPOKE_RFZ0]; ALL_TAC] THEN
  SUBGOAL_THEN `inverse (node_map H) (y0:A) IN dart H` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INVERSE_NODE_CUBIC; NODE_MAP_IN_DART]; ALL_TAC] THEN
  UNDISCH_TAC `LAST (inverse (node_map (H:(A)hypermap)) y0 :: p) = y` THEN
  UNDISCH_TAC `list_path (dlink (H:(A)hypermap) (spoke_ring H x))
                         (inverse (node_map H) y0) p` THEN
  STRUCT_CASES_TAC(ISPEC `p:(A)list` list_CASES) THEN
  REWRITE_TAC[list_path; LAST; NOT_CONS_NIL] THEN REPEAT STRIP_TAC THENL
   [CFACE_TAC[];
    UNDISCH_TAC `dlink (H:(A)hypermap) (spoke_ring H x)
                       (inverse (node_map H) y0) h` THEN
    REWRITE_TAC[dlink; clink] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `h:A = node_map H y0` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC NODEI THEN
        UNDISCH_TAC `inverse (node_map (H:(A)hypermap)) y0 = node_map H h` THEN
        ASM_SIMP_TAC[INVERSE_NODE_CUBIC] THEN MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] SPOKE_DISK_PATH) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`t:(A)list`;
       `node_map (H:(A)hypermap) y0`]) THEN
      ASM_REWRITE_TAC[LAST; NOT_CONS_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[GSYM MEM_SPOKE_RING];
      SUBGOAL_THEN `MEM (h:A) (spoke_ring (H:(A)hypermap) x)` ASSUME_TAC THENL
       [UNDISCH_TAC
         `face_map (H:(A)hypermap) (inverse (node_map H) y0) = h` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(if t = ([]:(A)list) then h else LAST t) = y` THEN
      UNDISCH_TAC `list_path (dlink (H:(A)hypermap) (spoke_ring H x)) h t` THEN
      STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THEN
      REWRITE_TAC[list_path; LAST; dlink; NOT_CONS_NIL] THEN
      ASM_MESON_TAC[FBAND_MEM_IFF; CFACE_REFL]]]);;

let DISKF_SPOKE_RING = prove
 (`!(H:(A)hypermap) x y.
     minimal_counter_example H /\ x IN dart H
     ==> (diskF H (spoke_ring H x) y <=> cface H x y)`,
  MESON_TAC[DISKF_SPOKE_RING_FWD; DISKF_SPOKE_RING_BWD]);;

(* ------------------------------------------------------------------------- *)
(* The spoke ring is chordless: a chord would give a nontrivial 3-ring.      *)
(* ------------------------------------------------------------------------- *)

let SPOKE_RING_NEXTC_EL = prove
 (`!(H:(A)hypermap) x i j.
     minimal_counter_example H /\ x IN dart H /\
     i < LENGTH (spoke_ring H x) /\ j < LENGTH (spoke_ring H x) /\
     ~(j = (i + 1) MOD LENGTH (spoke_ring H x))
     ==> ~(EL j (spoke_ring H x) =
           nextc (spoke_ring H x) (EL i (spoke_ring H x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SPOKE_RING_PAIRWISE; NEXTC_EL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`spoke_ring (H:(A)hypermap) x`; `j:num`;
                 `(i + 1) MOD LENGTH(spoke_ring (H:(A)hypermap) x)`]
    EL_PAIRWISE_INJ) THEN
  ASM_SIMP_TAC[SPOKE_RING_PAIRWISE; MOD_LT_EQ] THEN
  UNDISCH_TAC `i < LENGTH (spoke_ring (H:(A)hypermap) x)` THEN ARITH_TAC);;

let CHORDLESS_SPOKE_RING = prove
 (`!(H:(A)hypermap) x.
     minimal_counter_example H /\ x IN dart H
     ==> chordless H (spoke_ring H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `plain_hypermap H /\ bridgeless (H:(A)hypermap) /\
                cubic_hypermap H /\ planar_hypermap H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC]; ALL_TAC] THEN
  SUBGOAL_THEN `scycle (H:(A)hypermap) (rlink H) (spoke_ring H x)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCYCLE_SPOKE_RING]; ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\a b:A. ~(a = b)) (spoke_ring (H:(A)hypermap) x)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[SPOKE_RING_PAIRWISE]; ALL_TAC] THEN
  ASM_SIMP_TAC[CHORDLESS_RING_EQ] THEN
  MAP_EVERY X_GEN_TAC [`y1:A`; `y2:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `y1:A = y2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y1:A) IN dart H /\ (y2:A) IN dart H` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SPOKE_RING_DART THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:A. cface H y1 z /\ cface H (edge_map H z) y2`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `adj H (y1:A) y2` THEN REWRITE_TAC[adj; rlink; GSYM cface] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cface H x (node_map H (y1:A)) /\ cface H x (node_map H (y2:A))`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM MEM_SPOKE_RING]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(z:A) IN dart H /\ node_map H (y1:A) IN dart H /\
    node_map H (y2:A) IN dart H /\ edge_map H (z:A) IN dart H /\
    edge_map H (node_map H (y1:A)) IN dart H /\
    edge_map H (node_map H (y2:A)) IN dart H`
   STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `scycle H (rlink H) [node_map H (y2:A); edge_map H z;
   edge_map H (node_map H y1)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `[node_map H (y2:A); edge_map H z;
    edge_map H (node_map H y1)]`] SRCYCLEI) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; ALL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[srcycle; NOT_CONS_NIL; HD; TL; srpath; ALL] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nontrivial_ring H 0 [node_map H (y2:A); edge_map H z;
   edge_map H (node_map H y1)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `[node_map H (y2:A); edge_map H z;
    edge_map H (node_map H y1)]`] NONTRIVIAL0P) THEN
    ASM_REWRITE_TAC[ALL] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `node_map H (edge_map H (node_map H (y1:A)))` THEN
      ABBREV_TAC `t:A = node_map H (edge_map H (node_map H (y1:A)))` THEN
      SUBGOAL_THEN `(t:A) IN dart H` ASSUME_TAC THENL
       [CFACE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `node_map H (t:A) = face_map H (node_map H (y1:A))`
       ASSUME_TAC THENL
       [EXPAND_TAC "t" THEN ASM_SIMP_TAC[CUBIC_EQ'; CFT_PLAIN_EE];
        ALL_TAC] THEN
      SUBGOAL_THEN `MEM (t:A) (spoke_ring H x)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[MEM_SPOKE_RING] THEN CFACE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `nextc (spoke_ring H x) (t:A) = y1` ASSUME_TAC THENL
       [ASM_SIMP_TAC[NEXT_SPOKE_RING] THEN REWRITE_TAC[spoke] THEN
        EXPAND_TAC "t" THEN REWRITE_TAC[nodeK];
        ALL_TAC] THEN
      REWRITE_TAC[IN; diskF] THEN CONJ_TAC THENL
       [EXPAND_TAC "t" THEN ASM_SIMP_TAC[DISKN_NODE_EQ] THEN
        MATCH_MP_TAC RING_IN_DISKN THEN ASM_REWRITE_TAC[MEM];
        CFACE_TAC[]];
      EXISTS_TAC `node_map H (node_map H (y1:A))` THEN
      ABBREV_TAC `w:A = node_map H (node_map H (y1:A))` THEN
      SUBGOAL_THEN `(w:A) IN dart H` ASSUME_TAC THENL
       [CFACE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `node_map H (w:A) = y1` ASSUME_TAC THENL
       [EXPAND_TAC "w" THEN ASM_SIMP_TAC[CUBIC_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN `face_map H (edge_map H (y1:A)) = w` ASSUME_TAC THENL
       [CFACE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `nextc (spoke_ring H x) (y1:A) = face_map H w`
      ASSUME_TAC THENL
       [ASM_SIMP_TAC[NEXT_SPOKE_RING] THEN REWRITE_TAC[spoke] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `MEM (nextc (spoke_ring H x) (y1:A)) (spoke_ring H x)`
       ASSUME_TAC THENL
       [MATCH_MP_TAC NEXTC_MEM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[diskFC] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
          [SYM(ASSUME `node_map H (node_map H (y1:A)) = w`)] THEN
        MP_TAC(ISPECL [`H:(A)hypermap`; `[node_map H (y2:A); edge_map H z;
         edge_map H (node_map H y1)]`; `node_map H (y1:A)`]
          DISKN_NODE_EQ) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN
         `node_map H (y1:A) = edge_map H (edge_map H (node_map H (y1:A)))`
         (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
         [ASM_SIMP_TAC[CFT_PLAIN_EE]; ALL_TAC] THEN
        MATCH_MP_TAC DISKN_EDGE_RING THEN ASM_REWRITE_TAC[ALL; MEM] THEN
        REWRITE_TAC[proper_ring] THEN MESON_TAC[];
        CFACE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `H:(A)hypermap` BIRKHOFF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `[node_map H (y2:A); edge_map H z;
   edge_map H (node_map H y1)]`) THEN REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* list_find P l: the first index of l satisfying P (LENGTH l if none).      *)
(* ------------------------------------------------------------------------- *)

let list_find = new_recursive_definition list_RECURSION
 `(list_find (P:A->bool) [] = 0) /\
  (list_find P (CONS h t) = if P h then 0 else SUC(list_find P t))`;;

let LIST_FIND_LT = prove
 (`!(P:A->bool) l. list_find P l < LENGTH l <=> EX P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_find; LENGTH; EX] THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LT_SUC; LT_0] THEN ASM_ARITH_TAC);;

let EL_LIST_FIND = prove
 (`!(P:A->bool) l. EX P l ==> P (EL (list_find P l) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[EX; list_find] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EL; HD; TL] THEN ASM_MESON_TAC[]);;

let LIST_FIND_CONG = prove
 (`!(P:A->bool) Q l.
     (!x. MEM x l ==> (P x <=> Q x)) ==> list_find P l = list_find Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_find; MEM] THEN ASM_MESON_TAC[]);;

let COLOR_NEQ =
  let d = CONJUNCTS(distinctness "color") in
  end_itlist CONJ (d @ map GSYM d);;

let COLOR_INDEX_DIFFER = prove
 (`!i1 i2 n. i1 < n /\ i2 < n /\ n <= 4 /\ ~(i1 = i2) /\
             (i2 = (i1 + 1) MOD n \/ i1 = (i2 + 1) MOD n)
    ==> ~((if i2 = 2 /\ n = 3 then Color3
           else if i2 = 0 \/ i2 = 2 then Color1 else Color2) =
          (if i1 = 2 /\ n = 3 then Color3
           else if i1 = 0 \/ i1 = 2 then Color1 else Color2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `i1 < 4 /\ i2 < 4` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC
   (MATCH_MP (ARITH_RULE `i1 < 4 ==> i1 = 0 \/ i1 = 1 \/ i1 = 2 \/ i1 = 3`)
             (ASSUME `i1 < 4`)) THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC
   (MATCH_MP (ARITH_RULE `i2 < 4 ==> i2 = 0 \/ i2 = 1 \/ i2 = 2 \/ i2 = 3`)
             (ASSUME `i2 < 4`)) THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC
   (MATCH_MP
     (ARITH_RULE `n <= 4 ==> n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4`)
     (ASSUME `n <= 4`)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COLOR_NEQ]);;

let FBAND_EX = prove
 (`!(H:(A)hypermap) p z. fband H p z <=> EX (cface H z) p`,
  REWRITE_TAC[fband; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Every face of a minimal counter-example has arity at least 5: a smaller   *)
(* spoke ring is trivial by Birkhoff, hence an explicit 4-colouring exists.  *)
(* ------------------------------------------------------------------------- *)

let MIN_ARITY = prove
 (`!(H:(A)hypermap) x.
     minimal_counter_example H /\ x IN dart H ==> 4 < arity H x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `plain_hypermap H /\ bridgeless (H:(A)hypermap) /\
                cubic_hypermap H /\ planar_hypermap H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC]; ALL_TAC] THEN
  SUBGOAL_THEN `scycle (H:(A)hypermap) (rlink H) (spoke_ring H x)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCYCLE_SPOKE_RING]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\y:A. y IN dart H) (spoke_ring H x)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC SPOKE_RING_DART THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\a b:A. ~(a = b)) (spoke_ring (H:(A)hypermap) x)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[SPOKE_RING_PAIRWISE]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SIZE_SPOKE_RING] THEN REWRITE_TAC[GSYM NOT_LE] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC
   `?y:A. y IN dart (H:(A)hypermap) /\ diskFC H (spoke_ring H x) y` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `nontrivial_ring H 0 (spoke_ring (H:(A)hypermap) x)`
     ASSUME_TAC THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `spoke_ring (H:(A)hypermap) (x:A)`]
        NONTRIVIAL0P) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `x:A` THEN REWRITE_TAC[IN] THEN
        ASM_SIMP_TAC[DISKF_SPOKE_RING; CFACE_REFL];
        EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (spoke_ring (H:(A)hypermap) x) <= 5 /\
                  ~(LENGTH (spoke_ring (H:(A)hypermap) x) = 5)`
     STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `H:(A)hypermap` BIRKHOFF) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `spoke_ring (H:(A)hypermap) x`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `four_colorable (H:(A)hypermap)` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[minimal_counter_example]] THEN
  REWRITE_TAC[four_colorable] THEN
  EXISTS_TAC
   `\y:A. if cface H x y then Color0
          else if list_find (cface H y) (spoke_ring H x) = 2 /\
                  LENGTH(spoke_ring H x) = 3 then Color3
          else if list_find (cface H y) (spoke_ring H x) = 0 \/
                  list_find (cface H y) (spoke_ring H x) = 2
               then Color1 else Color2` THEN
  REWRITE_TAC[coloring] THEN CONJ_TAC THENL
   [BETA_TAC THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `edge_map H (u:A) IN dart H` ASSUME_TAC THENL
     [ASM_SIMP_TAC[EDGE_MAP_IN_DART]; ALL_TAC] THEN
    ASM_CASES_TAC `cface H x (u:A)` THENL
     [SUBGOAL_THEN `~cface H x (edge_map H (u:A))` ASSUME_TAC THENL
       [CFACE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "color"];
      ALL_TAC] THEN
    ASM_CASES_TAC `cface H x (edge_map H (u:A))` THENL
     [ASM_REWRITE_TAC[] THEN REPEAT COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "color"];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `i1 = list_find (cface H (u:A)) (spoke_ring H x)` THEN
    ABBREV_TAC
     `i2 = list_find (cface H (edge_map H (u:A))) (spoke_ring H x)` THEN
    SUBGOAL_THEN `EX (cface H (u:A)) (spoke_ring H x) /\
                  EX (cface H (edge_map H (u:A))) (spoke_ring H x)`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM FBAND_EX] THEN
      UNDISCH_TAC `~(?y:A. y IN dart H /\ diskFC H (spoke_ring H x) y)` THEN
      MATCH_MP_TAC(TAUT `(~p ==> q) ==> ~q ==> p`) THEN DISCH_TAC THENL
       [EXISTS_TAC `u:A`; EXISTS_TAC `edge_map H (u:A)`] THEN
      ASM_REWRITE_TAC[diskFC] THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `u:A`] DISKF_SPOKE_RING) THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `edge_map H (u:A)`]
        DISKF_SPOKE_RING) THEN
      REWRITE_TAC[diskF] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `i1 < LENGTH (spoke_ring (H:(A)hypermap) x) /\
                  i2 < LENGTH (spoke_ring (H:(A)hypermap) x)`
     STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["i1"; "i2"] THEN ASM_REWRITE_TAC[LIST_FIND_LT];
      ALL_TAC] THEN
    ABBREV_TAC `z1 = EL i1 (spoke_ring (H:(A)hypermap) x)` THEN
    ABBREV_TAC `z2 = EL i2 (spoke_ring (H:(A)hypermap) x)` THEN
    SUBGOAL_THEN `cface H (u:A) z1 /\ cface H (edge_map H u) z2`
     STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["z1"; "z2"; "i1"; "i2"] THEN
      ASM_SIMP_TAC[EL_LIST_FIND];
      ALL_TAC] THEN
    SUBGOAL_THEN `MEM (z1:A) (spoke_ring H x) /\ MEM (z2:A) (spoke_ring H x)`
     STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["z1"; "z2"] THEN ASM_SIMP_TAC[MEM_EL];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z1:A = z2) /\ adj H z1 z2` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[adj] THEN CONJ_TAC THENL
       [CFACE_TAC[]; EXISTS_TAC `u:A` THEN CFACE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(i1:num = i2)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `EL i2 (spoke_ring (H:(A)hypermap) x) = z1` THEN
      UNDISCH_TAC `EL i2 (spoke_ring (H:(A)hypermap) x) = z2` THEN
      UNDISCH_TAC `~(z1:A = z2)` THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `i2 = (i1 + 1) MOD LENGTH(spoke_ring (H:(A)hypermap) x) \/
                  i1 = (i2 + 1) MOD LENGTH(spoke_ring (H:(A)hypermap) x)`
     ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~a /\ ~b ==> F) ==> a \/ b`) THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `spoke_ring (H:(A)hypermap) (x:A)`;
                     `z1:A`; `z2:A`] CHORDLESS_RING) THEN
      ASM_SIMP_TAC[CHORDLESS_SPOKE_RING] THEN
      MAP_EVERY EXPAND_TAC ["z1"; "z2"] THEN
      ASM_SIMP_TAC[SPOKE_RING_NEXTC_EL];
      ALL_TAC] THEN
    MATCH_MP_TAC COLOR_INDEX_DIFFER THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[CFACE_RIGHT_FACE] THEN
    MP_TAC(ISPECL [`cface (H:(A)hypermap) (face_map H (u:A))`;
                   `cface (H:(A)hypermap) (u:A)`;
                   `spoke_ring (H:(A)hypermap) x`] LIST_FIND_CONG) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `z:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[CFACE_LEFT_FACE];
      DISCH_THEN(fun th -> REWRITE_TAC[th])]]);;

(* ------------------------------------------------------------------------- *)
(* If x is adjacent to both y and edge y then one of them is a spoke of x.   *)
(* ------------------------------------------------------------------------- *)

let ADJ11_EDGE = prove
 (`!(H:(A)hypermap) x y.
     minimal_counter_example H /\ x IN dart H /\ y IN dart H /\
     adj H x y /\ adj H x (edge_map H y)
     ==> MEM y (spoke_ring H x) \/ MEM (edge_map H y) (spoke_ring H x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `plain_hypermap H /\ bridgeless (H:(A)hypermap) /\
                cubic_hypermap H`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[minimal_counter_example; MCE_CUBIC]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map H (y:A) IN dart H` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~a /\ ~b ==> F) ==> a \/ b`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `fband (H:(A)hypermap) (spoke_ring H x) (y:A) /\
                fband H (spoke_ring H x) (edge_map H y)`
   MP_TAC THENL
   [ASM_SIMP_TAC[FBAND_SPOKE_RING]; ALL_TAC] THEN
  REWRITE_TAC[FBAND_MEM_IFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z:A) IN dart H /\ (t:A) IN dart H` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SPOKE_RING_DART THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `adj H (z:A) t` ASSUME_TAC THENL
   [REWRITE_TAC[adj] THEN EXISTS_TAC `y:A` THEN CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\a b:A. ~(a = b)) (spoke_ring H x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SPOKE_RING_PAIRWISE]; ALL_TAC] THEN
  SUBGOAL_THEN `chordless (H:(A)hypermap) (spoke_ring H x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CHORDLESS_SPOKE_RING]; ALL_TAC] THEN
  ASM_CASES_TAC `t = nextc (spoke_ring H x) (z:A)` THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `z:A`] NEXT_SPOKE_RING) THEN
    ASM_REWRITE_TAC[spoke] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `y:A`; `z:A`] DOUBLE_DART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CFACE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `MEM (z:A) (spoke_ring H x)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `z = nextc (spoke_ring H x) (t:A)` THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `t:A`] NEXT_SPOKE_RING) THEN
    ASM_REWRITE_TAC[spoke] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `t:A`; `edge_map H (y:A)`]
      DOUBLE_DART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CFACE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `MEM (edge_map H (y:A)) (spoke_ring H x)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `z:A = t` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `spoke_ring (H:(A)hypermap) x`; `z:A`;
                   `t:A`] CHORDLESS_RING) THEN
    ASM_REWRITE_TAC[];
    CFACE_TAC[]]);;
