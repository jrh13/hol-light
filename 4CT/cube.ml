(* ========================================================================= *)
(* 4CT/cube.ml                                                               *)
(*                                                                           *)
(* cube.v: the cubic reduction.  cube G is the plain cubic hypermap on the   *)
(* six copies cube_tag # A of the darts of G: over a dart x the tags CTn,    *)
(* CTen, CTf, CTnf form a 4-cycle of the face map (which then moves on to    *)
(* face_map G x), the CTe darts follow the edges and the CTfe darts the      *)
(* nodes of G.  Hence cube G has a face for each face, node and edge of G    *)
(* and the same components, so the same genus: PLAIN_CUBE, CUBIC_CUBE,       *)
(* CUBE_COLORABLE, BRIDGELESS_CUBE, GENUS_CUBE, PLANAR_CUBE.  GCOMP_HOM and  *)
(* GCOMP_STEPS are the generic connectivity facts used by the counting.      *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/coloring.ml";;
needs "4CT/jordan.ml";;
needs "4CT/walkup.ml";;
needs "4CT/embed_prelim.ml";;
needs "4CT/cfmap.ml";;
needs "4CT/birkhoff.ml";;

(* ------------------------------------------------------------------------- *)
(* The construction: the six tags, the three maps on tagged darts (the Coq   *)
(* definitions), the dart set and the maps guarded to be the identity off    *)
(* the darts, and the hypermap cube G.                                       *)
(* ------------------------------------------------------------------------- *)

let cube_tag_INDUCT,cube_tag_RECURSION = define_type
  "cube_tag = CTn | CTen | CTf | CTnf | CTe | CTfe";;

let cube_edge = define
 `(cube_edge (e:A->A) (n:A->A) (fa:A->A) (CTen,x) = (CTnf, e x)) /\
  (cube_edge e n fa (CTf,x)  = (CTe,  n(fa x))) /\
  (cube_edge e n fa (CTnf,x) = (CTen, n(fa x))) /\
  (cube_edge e n fa (CTe,x)  = (CTf,  e x)) /\
  (cube_edge e n fa (CTfe,x) = (CTn,  x)) /\
  (cube_edge e n fa (CTn,x)  = (CTfe, x))`;;

let cube_node = define
 `(cube_node (e:A->A) (n:A->A) (fa:A->A) (CTn,x)  = (CTen, n x)) /\
  (cube_node e n fa (CTen,x) = (CTfe, x)) /\
  (cube_node e n fa (CTf,x)  = (CTnf, e x)) /\
  (cube_node e n fa (CTnf,x) = (CTe,  n(fa x))) /\
  (cube_node e n fa (CTe,x)  = (CTf,  x)) /\
  (cube_node e n fa (CTfe,x) = (CTn,  fa(e x)))`;;

let cube_face = define
 `(cube_face (e:A->A) (n:A->A) (fa:A->A) (CTn,x)  = (CTen, x)) /\
  (cube_face e n fa (CTen,x) = (CTf,  x)) /\
  (cube_face e n fa (CTf,x)  = (CTnf, x)) /\
  (cube_face e n fa (CTnf,x) = (CTn,  fa x)) /\
  (cube_face e n fa (CTe,x)  = (CTe,  e x)) /\
  (cube_face e n fa (CTfe,x) = (CTfe, n x))`;;

let cube_D = new_definition
 `cube_D (G:(A)hypermap) = (:cube_tag) CROSS (dart G)`;;

let cube_emap = new_definition
 `cube_emap (G:(A)hypermap) u =
    if SND u IN dart G
    then cube_edge (edge_map G) (node_map G) (face_map G) u else u`;;

let cube_nmap = new_definition
 `cube_nmap (G:(A)hypermap) u =
    if SND u IN dart G
    then cube_node (edge_map G) (node_map G) (face_map G) u else u`;;

let cube_fmap = new_definition
 `cube_fmap (G:(A)hypermap) u =
    if SND u IN dart G
    then cube_face (edge_map G) (node_map G) (face_map G) u else u`;;

let cube = new_definition
 `cube (G:(A)hypermap) =
  mk_hypermap(cube_D G, cube_emap G, cube_nmap G, cube_fmap G)`;;

(* ------------------------------------------------------------------------- *)
(* The dart set and the values of the maps on the darts.                     *)
(* ------------------------------------------------------------------------- *)

let UNIV_CUBE_TAG = prove
 (`(:cube_tag) = {CTn,CTen,CTf,CTnf,CTe,CTfe}`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC cube_tag_INDUCT THEN REWRITE_TAC[]);;

let CARD_CUBE_TAG = prove
 (`FINITE(:cube_tag) /\ CARD(:cube_tag) = 6`,
  REWRITE_TAC[UNIV_CUBE_TAG; FINITE_INSERT; FINITE_EMPTY;
              ARITH_RULE `6 = SUC(SUC(SUC(SUC(SUC(SUC 0)))))`] THEN
  REPEAT(MATCH_MP_TAC CARD_INS_STEP THEN
         REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY;
                     distinctness "cube_tag"]) THEN
  REWRITE_TAC[CARD_CLAUSES]);;

let IN_CUBE_D = prove
 (`!G:(A)hypermap tg x. (tg,x) IN cube_D G <=> x IN dart G`,
  REWRITE_TAC[cube_D; IN_CROSS; IN_UNIV]);;

let FINITE_CUBE_D = prove
 (`!G:(A)hypermap. FINITE(cube_D G)`,
  SIMP_TAC[cube_D; FINITE_CROSS; CARD_CUBE_TAG; FINITE_DART]);;

let CUBE_MAPS = prove
 (`!G:(A)hypermap x.
     x IN dart G
     ==> cube_emap G (CTn,x) = (CTfe,x) /\
         cube_emap G (CTen,x) = (CTnf,edge_map G x) /\
         cube_emap G (CTf,x) = (CTe,node_map G (face_map G x)) /\
         cube_emap G (CTnf,x) = (CTen,node_map G (face_map G x)) /\
         cube_emap G (CTe,x) = (CTf,edge_map G x) /\
         cube_emap G (CTfe,x) = (CTn,x) /\
         cube_nmap G (CTn,x) = (CTen,node_map G x) /\
         cube_nmap G (CTen,x) = (CTfe,x) /\
         cube_nmap G (CTf,x) = (CTnf,edge_map G x) /\
         cube_nmap G (CTnf,x) = (CTe,node_map G (face_map G x)) /\
         cube_nmap G (CTe,x) = (CTf,x) /\
         cube_nmap G (CTfe,x) = (CTn,face_map G (edge_map G x)) /\
         cube_fmap G (CTn,x) = (CTen,x) /\
         cube_fmap G (CTen,x) = (CTf,x) /\
         cube_fmap G (CTf,x) = (CTnf,x) /\
         cube_fmap G (CTnf,x) = (CTn,face_map G x) /\
         cube_fmap G (CTe,x) = (CTe,edge_map G x) /\
         cube_fmap G (CTfe,x) = (CTfe,node_map G x)`,
  SIMP_TAC[cube_emap; cube_nmap; cube_fmap; SND; cube_edge; cube_node;
           cube_face]);;

let CUBE_MAPS_OFF = prove
 (`!G:(A)hypermap u.
     ~(u IN cube_D G)
     ==> cube_emap G u = u /\ cube_nmap G u = u /\ cube_fmap G u = u`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_CUBE_D] THEN
  SIMP_TAC[cube_emap; cube_nmap; cube_fmap; SND]);;

(* Case analysis on the tag of a dart (tg,x) with x IN dart G.               *)

let CUBE_TAG_TAC =
  REWRITE_TAC[FORALL_PAIR_THM; IN_CUBE_D] THEN
  MAP_EVERY X_GEN_TAC [`tg:cube_tag`; `x:A`] THEN DISCH_TAC THEN
  STRUCT_CASES_TAC(ISPEC `tg:cube_tag` (cases "cube_tag")) THEN
  ASM_SIMP_TAC[CUBE_MAPS; IN_CUBE_D; FST; SND; PAIR_EQ;
               distinctness "cube_tag"; EDGE_MAP_IN_DART;
               NODE_MAP_IN_DART; FACE_MAP_IN_DART; faceK; edgeK; nodeK];;

let CUBE_MAPS_IN_D = prove
 (`!G:(A)hypermap u.
     u IN cube_D G
     ==> cube_emap G u IN cube_D G /\ cube_nmap G u IN cube_D G /\
         cube_fmap G u IN cube_D G`,
  GEN_TAC THEN CUBE_TAG_TAC);;

let CUBE_NEQ = prove
 (`!G:(A)hypermap u.
     u IN cube_D G
     ==> ~(cube_emap G u = u) /\ ~(cube_nmap G u = u) /\
         ~(cube_nmap G (cube_nmap G u) = u)`,
  GEN_TAC THEN CUBE_TAG_TAC);;

let CUBE_CANCEL = prove
 (`!G:(A)hypermap u.
     cube_emap G (cube_nmap G (cube_fmap G u)) = u /\
     cube_emap G (cube_emap G u) = u /\
     cube_nmap G (cube_nmap G (cube_nmap G u)) = u`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`tg:cube_tag`; `x:A`] THEN
  ASM_CASES_TAC `(x:A) IN dart G` THENL
   [STRUCT_CASES_TAC(ISPEC `tg:cube_tag` (cases "cube_tag")) THEN
    ASM_SIMP_TAC[CUBE_MAPS; EDGE_MAP_IN_DART; NODE_MAP_IN_DART;
                 FACE_MAP_IN_DART; faceK; edgeK; nodeK];
    ASM_SIMP_TAC[cube_emap; cube_nmap; cube_fmap; SND]]);;

(* ------------------------------------------------------------------------- *)
(* cube G is a hypermap with the intended components; it is plain and cubic. *)
(* ------------------------------------------------------------------------- *)

let CUBE_PERMUTES = prove
 (`!G:(A)hypermap.
     cube_emap G permutes cube_D G /\ cube_nmap G permutes cube_D G /\
     cube_fmap G permutes cube_D G`,
  GEN_TAC THEN SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_CUBE_D] THEN
  MESON_TAC[CUBE_MAPS_OFF; CUBE_MAPS_IN_D; CUBE_CANCEL]);;

let CUBE_COMPONENTS = prove
 (`!G:(A)hypermap.
     dart(cube G) = cube_D G /\ edge_map(cube G) = cube_emap G /\
     node_map(cube G) = cube_nmap G /\ face_map(cube G) = cube_fmap G`,
  GEN_TAC THEN REWRITE_TAC[cube] THEN MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  REWRITE_TAC[hypermap_pred; FST; SND; FINITE_CUBE_D; CUBE_PERMUTES;
              FUN_EQ_THM; o_THM; I_THM; CUBE_CANCEL]);;

let IN_DART_CUBE = prove
 (`!G:(A)hypermap tg x. (tg,x) IN dart(cube G) <=> x IN dart G`,
  REWRITE_TAC[CUBE_COMPONENTS; IN_CUBE_D]);;

let PLAIN_CUBE = prove
 (`!G:(A)hypermap. plain_hypermap (cube G)`,
  GEN_TAC THEN REWRITE_TAC[plain_hypermap; CUBE_COMPONENTS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORBIT_SIZE_EQ_2 THEN
  EXISTS_TAC `cube_D (G:(A)hypermap)` THEN
  ASM_SIMP_TAC[FINITE_CUBE_D; CUBE_PERMUTES; CUBE_CANCEL; CUBE_NEQ]);;

let CUBIC_CUBE = prove
 (`!G:(A)hypermap. cubic_hypermap (cube G)`,
  GEN_TAC THEN REWRITE_TAC[cubic_hypermap; CUBE_COMPONENTS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORBIT_SIZE_EQ_3 THEN
  EXISTS_TAC `cube_D (G:(A)hypermap)` THEN
  ASM_SIMP_TAC[FINITE_CUBE_D; CUBE_PERMUTES; CUBE_CANCEL; CUBE_NEQ]);;

(* ------------------------------------------------------------------------- *)
(* A colouring of cube G restricts to a colouring of G on the CTnf darts.    *)
(* ------------------------------------------------------------------------- *)

let CUBE_COLORABLE = prove
 (`!G:(A)hypermap. four_colorable (cube G) ==> four_colorable G`,
  GEN_TAC THEN REWRITE_TAC[four_colorable; coloring; CUBE_COMPONENTS;
                           FORALL_PAIR_THM; IN_CUBE_D] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:cube_tag#A->color`
    (CONJUNCTS_THEN2 (LABEL_TAC "kE") (LABEL_TAC "kF"))) THEN
  EXISTS_TAC `\x:A. (k:cube_tag#A->color) (CTnf,x)` THEN REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `face_map G (x:A) IN dart G` ASSUME_TAC THENL
    [ASM_SIMP_TAC[FACE_MAP_IN_DART]; ALL_TAC]) THEN
  REMOVE_THEN "kE" (MP_TAC o SPECL [`CTen`; `x:A`]) THEN
  REMOVE_THEN "kF" (fun th ->
    MAP_EVERY (fun t -> MP_TAC(SPECL [t; `x:A`] th)) [`CTen`; `CTf`] THEN
    MAP_EVERY (fun t -> MP_TAC(SPECL [t; `x:A`] th)) [`CTnf`] THEN
    MAP_EVERY (fun t -> MP_TAC(SPECL [t; `face_map G (x:A)`] th))
              [`CTn`; `CTen`; `CTf`]) THEN
  ASM_SIMP_TAC[CUBE_MAPS] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Faces of cube G: a face invariant, the tag classes CTe / CTfe are closed  *)
(* under the face map, and on the CTnf darts cface (cube G) is cface G.      *)
(* ------------------------------------------------------------------------- *)

let CFACE_CUBE_STEP = prove
 (`!G:(A)hypermap x.
     x IN dart G
     ==> cface (cube G) (CTnf,x) (CTnf,face_map G x) /\
         cface (cube G) (CTn,x) (CTnf,x) /\
         cface (cube G) (CTen,x) (CTnf,x) /\
         cface (cube G) (CTf,x) (CTnf,x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `SUC(SUC(SUC(SUC 0)))`;
                   `(CTnf,x):cube_tag#A`] CFT_ITER);
    MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `SUC(SUC(SUC 0))`;
                   `(CTn,x):cube_tag#A`] CFT_ITER);
    MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `SUC(SUC 0)`;
                   `(CTen,x):cube_tag#A`] CFT_ITER);
    MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `SUC 0`;
                   `(CTf,x):cube_tag#A`] CFT_ITER)] THEN
  REWRITE_TAC[ITER; CUBE_COMPONENTS] THEN
  ASM_SIMP_TAC[CUBE_MAPS; FACE_MAP_IN_DART]);;

let CFACE_CUBE_INV = prove
 (`!G:(A)hypermap P u v.
     (!tg x. x IN dart G ==> (P (cube_fmap G (tg,x)) <=> P (tg,x))) /\
     u IN dart(cube G) /\ cface (cube G) u v
     ==> (P v <=> P u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`face_map(cube(G:(A)hypermap))`; `dart(cube(G:(A)hypermap))`;
                 `P:cube_tag#A->bool`; `u:cube_tag#A`; `v:cube_tag#A`]
                ORBIT_INVARIANT) THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES; GSYM face; GSYM cface] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_DART_CUBE; CUBE_COMPONENTS] THEN
  ASM_SIMP_TAC[]);;

let FST_CUBE_FMAP = prove
 (`!G:(A)hypermap u.
     u IN dart(cube G)
     ==> (FST(face_map (cube G) u) = CTe <=> FST u = CTe) /\
         (FST(face_map (cube G) u) = CTfe <=> FST u = CTfe)`,
  GEN_TAC THEN REWRITE_TAC[CUBE_COMPONENTS] THEN CUBE_TAG_TAC);;

let CFACE_CUBE_TAG = prove
 (`!G:(A)hypermap u v.
     u IN dart(cube G) /\ cface (cube G) u v
     ==> (FST v = CTe <=> FST u = CTe) /\ (FST v = CTfe <=> FST u = CTfe)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `\w:cube_tag#A. FST w = CTe`;
                   `u:cube_tag#A`; `v:cube_tag#A`] CFACE_CUBE_INV);
    MP_TAC(ISPECL [`G:(A)hypermap`; `\w:cube_tag#A. FST w = CTfe`;
                   `u:cube_tag#A`; `v:cube_tag#A`] CFACE_CUBE_INV)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CUBE_TAG_TAC);;

let CFACE_INV_FACE = prove
 (`!G:(A)hypermap x z.
     z IN dart G
     ==> (cface G x (edge_map G (node_map G z)) <=> cface G x z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `edge_map G (node_map G (z:A))`; `x:A`]
                CFACE_RIGHT_FACE) THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; nodeK] THEN MESON_TAC[]);;

let CFACE_CUBE_NF = prove
 (`!G:(A)hypermap x y.
     x IN dart G /\ y IN dart G
     ==> (cface (cube G) (CTnf,x) (CTnf,y) <=> cface G x y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`G:(A)hypermap`;
      `\w:cube_tag#A. FST w = CTe \/ FST w = CTfe \/
                      cface G x (if FST w = CTnf then SND w
                                 else edge_map G (node_map G (SND w)))`;
      `(CTnf,x):cube_tag#A`; `(CTnf,y):cube_tag#A`] CFACE_CUBE_INV) THEN
    ASM_REWRITE_TAC[IN_DART_CUBE; FST; SND; distinctness "cube_tag";
                    CFACE_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    STRUCT_CASES_TAC(ISPEC `tg:cube_tag` (cases "cube_tag")) THEN
    ASM_SIMP_TAC[CUBE_MAPS; FST; SND; distinctness "cube_tag"; faceK;
                 CFACE_INV_FACE];
    DISCH_THEN(MP_TAC o REWRITE_RULE[cface; face; orbit_map; IN_ELIM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ITER; CFACE_REFL] THEN
    SUBGOAL_THEN `ITER n (face_map G) (x:A) IN dart G` ASSUME_TAC THENL
     [ASM_MESON_TAC[ITER_PERMUTES_IN; FACE_MAP_PERMUTES]; ALL_TAC] THEN
    MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `(CTnf,x):cube_tag#A`;
                   `(CTnf,ITER n (face_map G) x):cube_tag#A`;
                   `(CTnf,face_map G (ITER n (face_map G) x)):cube_tag#A`]
                  CFACE_TRANS) THEN
    ASM_SIMP_TAC[IN_DART_CUBE; CFACE_CUBE_STEP]]);;

let BRIDGELESS_CUBE = prove
 (`!G:(A)hypermap. bridgeless (cube G) <=> bridgeless G`,
  GEN_TAC THEN REWRITE_TAC[bridgeless; CUBE_COMPONENTS] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(CTen,x):cube_tag#A`) THEN
    SUBGOAL_THEN `edge_map G (x:A) IN dart G` ASSUME_TAC THENL
     [ASM_SIMP_TAC[EDGE_MAP_IN_DART]; ALL_TAC] THEN
    MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `(CTen,x):cube_tag#A`;
                   `(CTnf,x):cube_tag#A`; `(CTnf,edge_map G x):cube_tag#A`]
                  CFACE_TRANS) THEN
    ASM_SIMP_TAC[IN_DART_CUBE; IN_CUBE_D; CUBE_MAPS; CFACE_CUBE_STEP;
                 CFACE_CUBE_NF] THEN
    MESON_TAC[];
    DISCH_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; IN_CUBE_D] THEN
    MAP_EVERY X_GEN_TAC [`tg:cube_tag`; `x:A`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `edge_map G x IN dart G /\ node_map G (face_map G (x:A)) IN dart G`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART];
      ALL_TAC] THEN
    STRUCT_CASES_TAC(ISPEC `tg:cube_tag` (cases "cube_tag")) THEN
    ASM_SIMP_TAC[CUBE_MAPS] THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`G:(A)hypermap`; `(CTn,x):cube_tag#A`;
                     `(CTfe,x):cube_tag#A`] CFACE_CUBE_TAG);
      MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `(CTen,x):cube_tag#A`;
                     `(CTnf,x):cube_tag#A`; `(CTnf,edge_map G x):cube_tag#A`]
                    CFACE_TRANS) THEN
      ASM_SIMP_TAC[IN_DART_CUBE; CFACE_CUBE_STEP; CFACE_CUBE_NF];
      MP_TAC(ISPECL [`G:(A)hypermap`; `(CTf,x):cube_tag#A`;
                     `(CTe,node_map G (face_map G x)):cube_tag#A`]
                    CFACE_CUBE_TAG);
      MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `(CTnf,x):cube_tag#A`;
                     `(CTen,node_map G (face_map G x)):cube_tag#A`;
                     `(CTnf,node_map G (face_map G x)):cube_tag#A`]
                    CFACE_TRANS) THEN
      ASM_SIMP_TAC[IN_DART_CUBE; CFACE_CUBE_STEP; CFACE_CUBE_NF] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `node_map G (face_map G (x:A))`) THEN
      ASM_REWRITE_TAC[faceK] THEN ASM_MESON_TAC[CFACE_SYM];
      MP_TAC(ISPECL [`G:(A)hypermap`; `(CTe,x):cube_tag#A`;
                     `(CTf,edge_map G x):cube_tag#A`] CFACE_CUBE_TAG);
      MP_TAC(ISPECL [`G:(A)hypermap`; `(CTfe,x):cube_tag#A`;
                     `(CTn,x):cube_tag#A`] CFACE_CUBE_TAG)] THEN
    ASM_REWRITE_TAC[IN_DART_CUBE; FST; distinctness "cube_tag"]]);;

(* ------------------------------------------------------------------------- *)
(* Generic connectivity facts (used downstream too), and the components of   *)
(* cube G: every dart is connected to the CTnf dart over the same dart of    *)
(* G, and on the CTnf darts gcomp (cube G) is gcomp G.                       *)
(* ------------------------------------------------------------------------- *)

let GCOMP_HOM = prove
 (`!(H1:(A)hypermap) (H2:(B)hypermap) (proj:A->B).
     (!u v. glink H1 u v ==> gcomp H2 (proj u) (proj v))
     ==> !u v. gcomp H1 u v ==> gcomp H2 (proj u) (proj v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [gcomp] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `p:num->A`
    (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
      (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `!i. i <= n ==> gcomp H2 ((proj:A->B)((p:num->A) 0)) (proj(p i))`
   (fun th -> MESON_TAC[th; LE_REFL]) THEN
  INDUCT_TAC THEN REWRITE_TAC[GCOMP_REFL] THEN DISCH_TAC THEN
  MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `(proj:A->B)((p:num->A) i)` THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  TRY(REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_ARITH_TAC);;

let GCOMP_STEPS = prove
 (`!G:(A)hypermap x.
     x IN dart G
     ==> gcomp G x (edge_map G x) /\ gcomp G x (node_map G x) /\
         gcomp G x (face_map G x) /\
         gcomp G x (node_map G (face_map G x)) /\
         gcomp G x (face_map G (edge_map G x))`,
  MESON_TAC[GCOMP_GLINK; GCOMP_TRANS; glink]);;

let GLINK_CUBE_PROJ = prove
 (`!G:(A)hypermap u v. glink (cube G) u v ==> gcomp G (SND u) (SND v)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; glink; CUBE_COMPONENTS] THEN
  MAP_EVERY X_GEN_TAC [`tg:cube_tag`; `x:A`] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(x:A) IN dart G` THENL
   [STRUCT_CASES_TAC(ISPEC `tg:cube_tag` (cases "cube_tag")) THEN
    ASM_SIMP_TAC[CUBE_MAPS; PAIR_EQ; SND] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GCOMP_STEPS; GCOMP_REFL];
    ASM_SIMP_TAC[cube_emap; cube_nmap; cube_fmap; SND; PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[GCOMP_REFL]]);;

let CUBE_GCOMP_VERT = prove
 (`!G:(A)hypermap tg x. x IN dart G ==> gcomp (cube G) (CTnf,x) (tg,x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `gcomp (cube G) (CTn,x) (CTen,x) /\ gcomp (cube G) (CTen,x) (CTf,x) /\
    gcomp (cube G) (CTf,x) (CTnf,x) /\ gcomp (cube G) (CTn,x) (CTfe,x) /\
    gcomp (cube G) (CTe,x) (CTf,x:A)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC GCOMP_GLINK THEN
    ASM_SIMP_TAC[glink; CUBE_COMPONENTS; CUBE_MAPS];
    STRUCT_CASES_TAC(ISPEC `tg:cube_tag` (cases "cube_tag")) THEN
    ASM_MESON_TAC[GCOMP_TRANS; GCOMP_SYM; GCOMP_REFL]]);;

let GLINK_G_LIFT = prove
 (`!G:(A)hypermap x y. glink G x y ==> gcomp (cube G) (CTnf,x) (CTnf,y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:A) IN dart G` THENL
   [ALL_TAC;
    SUBGOAL_THEN `edge_map G x = x /\ node_map G x = x /\ face_map G (x:A) = x`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES; FACE_MAP_PERMUTES;
                    permutes];
      REWRITE_TAC[glink] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GCOMP_REFL]]] THEN
  SUBGOAL_THEN
   `edge_map G x IN dart G /\ node_map G x IN dart G /\
    face_map G (x:A) IN dart G`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `gcomp (cube G) (CTen,x) (CTnf,edge_map G x) /\
    gcomp (cube G) (CTn,x) (CTen,node_map G x) /\
    gcomp (cube G) (CTnf,x) (CTn,face_map G (x:A))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC GCOMP_GLINK THEN
    ASM_SIMP_TAC[glink; CUBE_COMPONENTS; CUBE_MAPS];
    REWRITE_TAC[glink] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CUBE_GCOMP_VERT; GCOMP_TRANS; GCOMP_SYM]]);;

let GCOMP_CUBE_NF = prove
 (`!G:(A)hypermap x y. gcomp (cube G) (CTnf,x) (CTnf,y) <=> gcomp G x y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `G:(A)hypermap`;
                   `SND:cube_tag#A->A`] GCOMP_HOM) THEN
    REWRITE_TAC[GLINK_CUBE_PROJ] THEN
    DISCH_THEN(MP_TAC o SPECL [`(CTnf,x):cube_tag#A`;
                               `(CTnf,y):cube_tag#A`]) THEN
    REWRITE_TAC[SND];
    MP_TAC(ISPECL [`G:(A)hypermap`; `cube(G:(A)hypermap)`;
                   `\z:A. (CTnf,z)`] GCOMP_HOM) THEN
    REWRITE_TAC[GLINK_G_LIFT] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN REWRITE_TAC[]]);;

let COMPONENT_EQ_IFF_GCOMP = prove
 (`!H:(A)hypermap a b.
     a IN dart H /\ b IN dart H
     ==> (component H a = component H b <=> gcomp H a b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[component; EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[GCOMP_REFL; GCOMP_SYM; GCOMP_TRANS]);;

let NUMBER_COMPONENTS_CUBE = prove
 (`!G:(A)hypermap. number_of_components(cube G) = number_of_components G`,
  GEN_TAC THEN REWRITE_TAC[number_of_components; SET_OF_COMPONENTS_IMAGE] THEN
  SUBGOAL_THEN
   `IMAGE (component (cube G)) (dart(cube G)) =
    IMAGE (\x:A. component (cube G) (CTnf,x)) (dart G)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_DART_CUBE] THEN
    MESON_TAC[COMPONENT_EQ_IFF_GCOMP; IN_DART_CUBE; CUBE_GCOMP_VERT;
              GCOMP_SYM];
    MATCH_MP_TAC CARD_IMAGE_KERNEL THEN
    SIMP_TAC[FINITE_DART; COMPONENT_EQ_IFF_GCOMP; IN_DART_CUBE;
             GCOMP_CUBE_NF]]);;

(* ------------------------------------------------------------------------- *)
(* Counting: 6|G| darts, 3|G| edges, 2|G| nodes, and the faces are the       *)
(* edges (CTe darts), the nodes (CTfe darts) and the faces (the other darts) *)
(* of G; hence the genus is that of G.                                       *)
(* ------------------------------------------------------------------------- *)

let CARD_DART_CUBE = prove
 (`!G:(A)hypermap. CARD(dart(cube G)) = 6 * CARD(dart G)`,
  SIMP_TAC[CUBE_COMPONENTS; cube_D; CARD_CROSS; CARD_CUBE_TAG; FINITE_DART]);;

let NUMBER_EDGES_NODES_CUBE = prove
 (`!G:(A)hypermap.
     2 * number_of_edges(cube G) = 6 * CARD(dart G) /\
     3 * number_of_nodes(cube G) = 6 * CARD(dart G)`,
  GEN_TAC THEN
  REWRITE_TAC[number_of_edges; number_of_nodes; edge_set; node_set;
              GSYM CARD_DART_CUBE] THEN
  CONJ_TAC THEN MATCH_MP_TAC UNIFORM_ORBIT_CARD THEN
  REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES] THEN
  MESON_TAC[PLAIN_CUBE; CUBIC_CUBE; plain_hypermap; cubic_hypermap]);;

let SLICE_EQ = prove
 (`!G:(A)hypermap.
     {u | u IN dart(cube G) /\ FST u = CTe} =
     IMAGE (\x:A. (CTe,x)) (dart G) /\
     {u | u IN dart(cube G) /\ FST u = CTfe} =
     IMAGE (\x:A. (CTfe,x)) (dart G)`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; IN_IMAGE;
              IN_DART_CUBE; PAIR_EQ; FST] THEN
  MESON_TAC[]);;

let FACES_SLICE = prove
 (`!G:(A)hypermap.
     CARD(set_of_orbits (IMAGE (\x:A. (CTe,x)) (dart G))
                        (face_map(cube G))) = number_of_edges G /\
     CARD(set_of_orbits (IMAGE (\x:A. (CTfe,x)) (dart G))
                        (face_map(cube G))) = number_of_nodes G`,
  GEN_TAC THEN
  REWRITE_TAC[number_of_edges; number_of_nodes; edge_set; node_set] THEN
  CONJ_TAC THEN MATCH_MP_TAC ORBIT_COUNT_IMAGE THEN
  SIMP_TAC[FINITE_DART; EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES; CUBE_COMPONENTS;
           CUBE_MAPS; PAIR_EQ]);;

let FACES_REST = prove
 (`!G:(A)hypermap.
     CARD(set_of_orbits
            {u | u IN dart(cube G) /\ ~(FST u = CTe) /\ ~(FST u = CTfe)}
            (face_map(cube G))) =
     number_of_faces G`,
  GEN_TAC THEN REWRITE_TAC[number_of_faces; face_set; SET_OF_ORBITS_IMAGE] THEN
  SUBGOAL_THEN
   `IMAGE (orbit_map (face_map(cube G)))
          {u | u IN dart(cube G) /\ ~(FST u = CTe) /\ ~(FST u = CTfe)} =
    IMAGE (\x:A. orbit_map (face_map(cube G)) (CTnf,x)) (dart G)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM; IN_DART_CUBE; FST] THEN
    X_GEN_TAC `z:cube_tag#A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `tg:cube_tag` (X_CHOOSE_THEN `x:A`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`cube(G:(A)hypermap)`; `(tg,x):cube_tag#A`;
                     `(CTnf,x):cube_tag#A`] ORBIT_EQ_CFACE) THEN
      ASM_REWRITE_TAC[IN_DART_CUBE] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `~(tg = CTe)` THEN UNDISCH_TAC `~(tg = CTfe)` THEN
      STRUCT_CASES_TAC(ISPEC `tg:cube_tag` (cases "cube_tag")) THEN
      ASM_SIMP_TAC[CFACE_CUBE_STEP; CFACE_REFL; distinctness "cube_tag"];
      DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`CTnf`; `x:A`] THEN
      ASM_REWRITE_TAC[distinctness "cube_tag"]];
    MATCH_MP_TAC CARD_IMAGE_KERNEL THEN
    SIMP_TAC[FINITE_DART; ORBIT_EQ_CFACE; IN_DART_CUBE; CFACE_CUBE_NF]]);;

let NUMBER_FACES_CUBE = prove
 (`!G:(A)hypermap. number_of_faces(cube G) = euler_rhs G`,
  GEN_TAC THEN REWRITE_TAC[euler_rhs] THEN
  GEN_REWRITE_TAC LAND_CONV [number_of_faces] THEN REWRITE_TAC[face_set] THEN
  MP_TAC(ISPECL [`face_map(cube(G:(A)hypermap))`; `dart(cube(G:(A)hypermap))`;
                 `{u:cube_tag#A | u IN dart(cube(G:(A)hypermap)) /\
                                  FST u = CTe}`] CARD_ORBITS_SPLIT_CL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[FINITE_DART; FACE_MAP_IN_DART; FST_CUBE_FMAP];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`face_map(cube(G:(A)hypermap))`;
                 `dart(cube(G:(A)hypermap)) DIFF
                  {u:cube_tag#A | u IN dart(cube(G:(A)hypermap)) /\
                                  FST u = CTe}`;
                 `{u:cube_tag#A | u IN dart(cube(G:(A)hypermap)) /\
                                  FST u = CTfe}`] CARD_ORBITS_SPLIT_CL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[FINITE_DART; FINITE_DIFF; FACE_MAP_IN_DART; FST_CUBE_FMAP;
              distinctness "cube_tag"];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `(dart(cube G) DIFF {u | u IN dart(cube G) /\ FST u = CTe}) DIFF
    {u | u IN dart(cube G) /\ FST u = CTfe} =
    {u:cube_tag#A | u IN dart(cube(G:(A)hypermap)) /\
                    ~(FST u = CTe) /\ ~(FST u = CTfe)}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SLICE_EQ; FACES_SLICE; FACES_REST] THEN ARITH_TAC);;

let GENUS_CUBE = prove
 (`!G:(A)hypermap. genus(cube G) = genus G`,
  GEN_TAC THEN REWRITE_TAC[genus] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[euler_lhs; NUMBER_COMPONENTS_CUBE; CARD_DART_CUBE] THEN
  MP_TAC(SPEC `G:(A)hypermap` NUMBER_EDGES_NODES_CUBE) THEN
  REWRITE_TAC[euler_rhs; NUMBER_FACES_CUBE] THEN ARITH_TAC);;

let PLANAR_CUBE = prove
 (`!G:(A)hypermap. planar_hypermap(cube G) <=> planar_hypermap G`,
  REWRITE_TAC[planar_hypermap; GENUS_CUBE]);;
