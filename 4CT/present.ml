(* ========================================================================= *)
(* 4CT/present.ml                                                            *)
(*                                                                           *)
(* present.v: the notions and step lemmas of the seven presentation scripts  *)
(* (hub sizes 5 to 11).  valid_hub, excluded_arity, successful, forced_part  *)
(* and succeeds_in; the step lemmas SUCCEED_BY_SPLIT, SUCCEED_BY_SIMILARITY, *)
(* SUCCEED_BY_REDUCIBILITY and SUCCEED_BY_HUBCAP; EXCLUDE_ARITY; the quiz    *)
(* tree the_quiz_tree = cfquiz_tree (ZIP the_configs the_configs_sym) and    *)
(* NO_FIT_THE_REDPART.  Coq's reducibility is the computational check        *)
(* check_reducibility.                                                       *)
(*                                                                           *)
(* Coq quantifies the hypermap G inside the definitions; a HOL definition    *)
(* cannot bind the dart type, so successful, forced_part, succeeds_in and    *)
(* excluded_arity take the argument (:A) fixing the dart type and quantify   *)
(* over all G : (A)hypermap inside.  The no-embedding step is                *)
(* NOT_EMBED_REDUCIBLE_CONFIG.  The mirror of a minimal counter-example is   *)
(* one (Coq coloring.v:369), via the genus invariance genus (mirror G) =     *)
(* genus G proved here.                                                      *)
(* ========================================================================= *)

needs "4CT/hubcap.ml";;
needs "4CT/redpart.ml";;
needs "4CT/configurations.ml";;
needs "4CT/cfreducible.ml";;
needs "4CT/quiz.ml";;
needs "4CT/cube.ml";;

(* ------------------------------------------------------------------------- *)
(* Minimal counter-examples: the geometric facts present.v gets by coercion. *)
(* ------------------------------------------------------------------------- *)

let MCE_PLAIN = prove
 (`!(G:(A)hypermap). minimal_counter_example G ==> plain_hypermap G`,
  REWRITE_TAC[minimal_counter_example] THEN SIMP_TAC[]);;

let MCE_PLANAR = prove
 (`!(G:(A)hypermap). minimal_counter_example G ==> planar_hypermap G`,
  REWRITE_TAC[minimal_counter_example] THEN SIMP_TAC[]);;

let MCE_BRIDGELESS = prove
 (`!(G:(A)hypermap). minimal_counter_example G ==> bridgeless G`,
  REWRITE_TAC[minimal_counter_example] THEN SIMP_TAC[]);;

let MCE_PLAIN_CUBIC = prove
 (`!(G:(A)hypermap). minimal_counter_example G ==> plain_cubic G`,
  REWRITE_TAC[plain_cubic] THEN MESON_TAC[MCE_PLAIN; MCE_CUBIC]);;

(* Coq birkhoff.v:669 minimal_counter_example_is_plain_cubic_pentagonal,     *)
(* from MIN_ARITY.                                                           *)
let MCE_PENTAGONAL = prove
 (`!(G:(A)hypermap). minimal_counter_example G ==> pentagonal G`,
  REWRITE_TAC[pentagonal] THEN MESON_TAC[MIN_ARITY]);;

let MCE_PLAIN_CUBIC_PENTAGONAL = prove
 (`!(G:(A)hypermap). minimal_counter_example G ==> plain_cubic_pentagonal G`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[plain_cubic_pentagonal; plain_cubic] THEN
  ASM_MESON_TAC[MCE_CUBIC; MCE_PENTAGONAL; minimal_counter_example]);;

(* ------------------------------------------------------------------------- *)
(* The mirror of a minimal counter-example (Coq coloring.v:369). Needs the   *)
(* genus invariance (Coq hypermap.v genus_mirror): the mirror's maps are (f  *)
(* o n, n^-1, f^-1) and f o n = n^-1 o e^-1 o n, so the three orbit counts   *)
(* and the components agree.                                                 *)
(* ------------------------------------------------------------------------- *)

let GLINK_MIRROR_GCOMP = prove
 (`!(H:(A)hypermap) u v. glink (mirror H) u v ==> gcomp H u v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glink; MIRROR_COMPONENTS; o_THM] THEN
  ASM_CASES_TAC `(u:A) IN dart H` THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `u:A`] GCOMP_STEPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GCOMP_TRANS THENL
     [EXISTS_TAC `node_map (H:(A)hypermap) u` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[GCOMP_STEPS; NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE];
      EXISTS_TAC `node_map (H:(A)hypermap) u` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[GCOMP_STEPS; NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE]];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MAPS_OUTSIDE_DART th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[GCOMP_REFL]]);;

let GLINK_GCOMP_MIRROR = prove
 (`!(H:(A)hypermap) u v. glink H u v ==> gcomp (mirror H) u v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glink] THEN
  ASM_CASES_TAC `(u:A) IN dart H` THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC GCOMP_TRANS THEN
      EXISTS_TAC `face_map H (edge_map (H:(A)hypermap) u)` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`mirror (H:(A)hypermap)`; `u:A`] GCOMP_STEPS) THEN
        ASM_REWRITE_TAC[DART_MIRROR; MIRROR_COMPONENTS; o_THM] THEN SIMP_TAC[];
        MP_TAC(ISPECL [`mirror (H:(A)hypermap)`;
                       `face_map H (edge_map (H:(A)hypermap) u)`]
               GCOMP_STEPS) THEN
        ASM_REWRITE_TAC[DART_MIRROR; MIRROR_COMPONENTS; o_THM; edgeK] THEN
        ASM_SIMP_TAC[FACE_MAP_PERMUTES; EDGE_MAP_PERMUTES; PERMUTES_IN_IMAGE]];
      MATCH_MP_TAC GCOMP_SYM THEN
      MP_TAC(ISPECL [`mirror (H:(A)hypermap)`; `node_map (H:(A)hypermap) u`]
             GCOMP_STEPS) THEN
      ASM_REWRITE_TAC[DART_MIRROR; MIRROR_COMPONENTS; o_THM; nodeK] THEN
      ASM_SIMP_TAC[NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE];
      MATCH_MP_TAC GCOMP_SYM THEN
      MP_TAC(ISPECL [`mirror (H:(A)hypermap)`; `face_map (H:(A)hypermap) u`]
             GCOMP_STEPS) THEN
      ASM_REWRITE_TAC[DART_MIRROR; MIRROR_COMPONENTS; o_THM; faceK] THEN
      ASM_SIMP_TAC[FACE_MAP_PERMUTES; PERMUTES_IN_IMAGE]];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MAPS_OUTSIDE_DART th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[GCOMP_REFL]]);;

let GCOMP_MIRROR = prove
 (`!(H:(A)hypermap) x y. gcomp (mirror H) x y <=> gcomp H x y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MP_TAC(ISPECL [`mirror (H:(A)hypermap)`; `H:(A)hypermap`; `\u:A. u`]
           GCOMP_HOM);
    MP_TAC(ISPECL [`H:(A)hypermap`; `mirror (H:(A)hypermap)`; `\u:A. u`]
           GCOMP_HOM)] THEN
  REWRITE_TAC[GLINK_MIRROR_GCOMP; GLINK_GCOMP_MIRROR] THEN SIMP_TAC[]);;

let SET_OF_COMPONENTS_MIRROR = prove
 (`!(H:(A)hypermap). set_of_components (mirror H) = set_of_components H`,
  REWRITE_TAC[set_of_components; component; DART_MIRROR; GCOMP_MIRROR]);;

let FE_INVERSE_NODE = prove
 (`!(H:(A)hypermap). face_map H o edge_map H = inverse (node_map H)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`]
         PERMUTES_INVERSE_EQ) THEN
  REWRITE_TAC[NODE_MAP_PERMUTES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[edgeK]);;

let EN_INVERSE_FACE = prove
 (`!(H:(A)hypermap). edge_map H o node_map H = inverse (face_map H)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`]
         PERMUTES_INVERSE_EQ) THEN
  REWRITE_TAC[FACE_MAP_PERMUTES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[nodeK]);;

let ORBITS_INVERSE = prove
 (`!(p:A->A) s. FINITE s /\ p permutes s
                ==> set_of_orbits s (inverse p) = set_of_orbits s p`,
  REWRITE_TAC[set_of_orbits; EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[ORBIT_MAP_INVERSE]);;

(* f o n = n^-1 o e^-1 o n: the mirror edge orbits are the edge orbits       *)
(* conjugated by n.                                                          *)
let CARD_ORBITS_MIRROR_EDGE = prove
 (`!(H:(A)hypermap).
     CARD (set_of_orbits (dart H) (face_map H o node_map H)) =
     CARD (set_of_orbits (dart H) (edge_map H))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`face_map H o edge_map (H:(A)hypermap)`;
                 `inverse (edge_map (H:(A)hypermap))`;
                 `face_map H o node_map (H:(A)hypermap)`;
                 `dart (H:(A)hypermap)`] ORBIT_COUNT_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART] THEN
    SIMP_TAC[PERMUTES_INVERSE; EDGE_MAP_PERMUTES] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_THM; edgeK] THEN
      MP_TAC(ISPECL [`edge_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`]
             PERMUTES_INVERSES) THEN
      REWRITE_TAC[EDGE_MAP_PERMUTES] THEN SIMP_TAC[];
      MP_TAC(ISPECL
             [`face_map H o edge_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`]
             PERMUTES_INJECTIVE) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC PERMUTES_COMPOSE THEN
        REWRITE_TAC[EDGE_MAP_PERMUTES; FACE_MAP_PERMUTES];
        SIMP_TAC[]]];
    SUBGOAL_THEN
      `IMAGE (face_map H o edge_map (H:(A)hypermap)) (dart H) = dart H`
      SUBST1_TAC THENL
     [MATCH_MP_TAC PERMUTES_IMAGE THEN MATCH_MP_TAC PERMUTES_COMPOSE THEN
      REWRITE_TAC[EDGE_MAP_PERMUTES; FACE_MAP_PERMUTES];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC ORBITS_INVERSE THEN
    REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES]]);;

let GENUS_MIRROR = prove
 (`!(H:(A)hypermap). genus (mirror H) = genus H`,
  GEN_TAC THEN
  REWRITE_TAC[genus; euler_lhs; euler_rhs; number_of_components;
              number_of_edges; number_of_nodes; number_of_faces; edge_set;
              node_set; face_set; DART_MIRROR; MIRROR_COMPONENTS;
              SET_OF_COMPONENTS_MIRROR; CARD_ORBITS_MIRROR_EDGE;
              FE_INVERSE_NODE; EN_INVERSE_FACE] THEN
  SIMP_TAC[ORBITS_INVERSE; FINITE_DART; NODE_MAP_PERMUTES;
           FACE_MAP_PERMUTES]);;

let PLANAR_MIRROR = prove
 (`!(H:(A)hypermap). planar_hypermap (mirror H) <=> planar_hypermap H`,
  REWRITE_TAC[planar_hypermap; GENUS_MIRROR]);;

let MCE_MIRROR = prove
 (`!(G:(A)hypermap). minimal_counter_example G
                     ==> minimal_counter_example (mirror G)`,
  GEN_TAC THEN
  REWRITE_TAC[minimal_counter_example; PLANAR_MIRROR; BRIDGELESS_MIRROR;
              PLAIN_MIRROR; PRECUBIC_MIRROR; DART_MIRROR] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[COLORABLE_MIRROR]);;

(* ------------------------------------------------------------------------- *)
(* Small part-list facts.                                                    *)
(* ------------------------------------------------------------------------- *)

let DROP_PART_ALL = prove
 (`!n p. size_part p <= n ==> drop_part n p = Pnil`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SIZE_PART_EQ_0; SIZE_DROP_PART] THEN
  ASM_ARITH_TAC);;

let TAKE_PART_ALL = prove
 (`!n p. size_part p <= n ==> take_part n p = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `p:part`] CAT_TAKE_DROP_PART) THEN
  ASM_SIMP_TAC[DROP_PART_ALL; CAT_PART_NIL]);;

let ROT_PART_OVERSIZE = prove
 (`!n p. size_part p <= n ==> rot_part n p = p`,
  SIMP_TAC[rot_part; DROP_PART_ALL; TAKE_PART_ALL; cat_part]);;

let LENGTH_THE_CONFIGS_SYM = prove
 (`LENGTH the_configs_sym = 633`,
  REWRITE_TAC[the_configs_sym; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let QUASICUBIC_SET_OF_LIST = prove
 (`!(H:(A)hypermap) l.
     quasicubic H (set_of_list l) <=> quasicubic H (\z. MEM z l)`,
  REWRITE_TAC[quasicubic; IN_SET_OF_LIST; IN]);;

(* ------------------------------------------------------------------------- *)
(* Definitions (Coq present.v:73-86).                                        *)
(* ------------------------------------------------------------------------- *)

(* Coq `reducibility` (reducible_in_range over cfreducible), realized        *)
(* through the computational check (see the header).                         *)
let check_reducibility = new_definition
 `check_reducibility <=> !cf. MEM cf the_configs ==> check_reducible cf`;;

let valid_hub = new_definition
 `valid_hub (G:(A)hypermap) x <=>
  minimal_counter_example G /\ x IN dart G /\ &0 < dscore G x`;;

let excluded_arity = new_definition
 `excluded_arity (u:A->bool) n <=>
    check_reducibility ==> !(G:(A)hypermap) x. valid_hub G x ==>
    ~(arity G x = n)`;;

let successful = new_definition
 `successful (u:A->bool) p <=>
  !(G:(A)hypermap) x. valid_hub G x ==> ~exact_fitp G x p`;;

let forced_part = new_definition
 `forced_part (u:A->bool) p0 p <=>
    !(G:(A)hypermap) x. valid_hub G x /\ exact_fitp G x p0 ==>
    exact_fitp G x p`;;

let succeeds_in = new_definition
 `succeeds_in (u:A->bool) p0 p <=> forced_part u p0 p ==> successful u p`;;

(* ------------------------------------------------------------------------- *)
(* Presentation (Coq EXCLUDE_ARITY).                                         *)
(* ------------------------------------------------------------------------- *)

let EXCLUDE_ARITY = prove
 (`!n. (check_reducibility ==> succeeds_in (:A) (pcons_ n) (pcons_ n))
       ==> excluded_arity (:A) n`,
  GEN_TAC THEN
  REWRITE_TAC[excluded_arity; succeeds_in; forced_part; successful] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `check_reducibility`)) THEN
  ANTS_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`G:(A)hypermap`; `x:A`]) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EXACT_FITP_PCONS_ THEN
  ASM_MESON_TAC[valid_hub; MCE_PENTAGONAL]);;

(* ------------------------------------------------------------------------- *)
(* Pcase (Coq SUCCEED_BY_SPLIT).                                             *)
(* ------------------------------------------------------------------------- *)

let SUCCEED_BY_SPLIT = prove
 (`!i j k lo p0 p.
     good_split i j k p /\
     succeeds_in (:A)
       (if good_split i j k p0 then split_part i j k lo p0
        else split_part i j k lo p)
       (split_part i j k lo p) /\
     (successful (:A)
        (if good_split i j k p0 then split_part i j k lo p0
         else split_part i j k lo p)
      ==> succeeds_in (:A) p0 (split_part i j k (~lo) p))
     ==> succeeds_in (:A) p0 p`,
  REPEAT GEN_TAC THEN
  (* FITP_SPLIT at valid hubs, the side being an equivalence with lo.      *)
  SUBGOAL_THEN
   `!q lo'. good_split i j k q
            ==> !(G:(A)hypermap) x.
                  valid_hub G x
                  ==> (exact_fitp G x (split_part i j k lo' q) <=>
                       (fitc i j k G x <=> ~lo') /\ exact_fitp G x q)`
  ASSUME_TAC THENL
   [REWRITE_TAC[valid_hub] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `G:(A)hypermap` FITP_SPLIT) THEN
    ASM_SIMP_TAC[MCE_PENTAGONAL] THEN BOOL_CASES_TAC `lo':bool` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p0l = if good_split i j k p0 then split_part i j k lo p0
                    else split_part i j k lo p` THEN
  REWRITE_TAC[succeeds_in; forced_part; successful] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  (* p0l forces the lo side of p, which is therefore successful; then p0l  *)
  (* is successful, p0 forces the other side, and that is successful too.  *)
  SUBGOAL_THEN
   `!(G:(A)hypermap) x. valid_hub G x /\ exact_fitp G x p0l
                        ==> exact_fitp G x (split_part i j k lo p)`
  ASSUME_TAC THENL
   [EXPAND_TAC "p0l" THEN COND_CASES_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(G:(A)hypermap) x. valid_hub G x
                        ==> ~exact_fitp G x (split_part i j k lo p)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(G:(A)hypermap) x. valid_hub G x
                        ==> ~exact_fitp G x (split_part i j k (~lo) p)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Similar (Coq SUCCEED_BY_SIMILARITY).                                      *)
(* ------------------------------------------------------------------------- *)

let SUCCEED_BY_SIMILARITY = prove
 (`!j mir ps p0 p.
     successful (:A) ps /\
     size_part ps =
     size_part (rot_part j (if mir then mirror_part p else p)) /\
     cmp_part (rot_part j (if mir then mirror_part p else p)) ps = Psubset
     ==> succeeds_in (:A) p0 p`,
  REPEAT GEN_TAC THEN ABBREV_TAC `q = if mir then mirror_part p else p` THEN
  REWRITE_TAC[succeeds_in; successful] THEN STRIP_TAC THEN
  DISCH_THEN(K ALL_TAC) THEN MAP_EVERY X_GEN_TAC [`G:(A)hypermap`; `x:A`] THEN
  REPEAT STRIP_TAC THEN
  (* q fits at a valid hub: at x in G or in the mirror of G.                *)
  SUBGOAL_THEN `?G1:(A)hypermap x1. valid_hub G1 x1 /\ exact_fitp G1 x1 q`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN COND_CASES_TAC THENL
     [EXISTS_TAC `mirror (G:(A)hypermap)`; EXISTS_TAC `G:(A)hypermap`] THEN
    EXISTS_TAC `x:A` THEN UNDISCH_TAC `valid_hub (G:(A)hypermap) x` THEN
    REWRITE_TAC[valid_hub; DART_MIRROR] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MCE_MIRROR; DSCORE_MIRROR; MCE_PLAIN; MCE_CUBIC;
                 GSYM FITP_MIRROR; MIRROR_MIRROR_PART];
    ALL_TAC] THEN
  (* So does its rotation rot_part j q, j steps along the face.             *)
  SUBGOAL_THEN `?x2:A. valid_hub G1 x2 /\ exact_fitp G1 x2 (rot_part j q)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `size_part q <= j` THEN ASM_SIMP_TAC[ROT_PART_OVERSIZE] THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `ITER j (face_map G1) (x1:A)` THEN
    MP_TAC(ISPECL [`j:num`; `q:part`] FITP_ROT) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
    UNDISCH_TAC `valid_hub (G1:(A)hypermap) x1` THEN
    REWRITE_TAC[valid_hub; ITER_FACE_IN_DART_EQ] THEN STRIP_TAC THEN
    ASM_MESON_TAC[DSCORE_CFACE; CFT_ITER];
    ASM_MESON_TAC[EXACT_FIT_PSUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* The quiz tree and NO_FIT_THE_REDPART (Coq present.v:160-187).             *)
(* ------------------------------------------------------------------------- *)

let the_quiz_tree = new_definition
 `the_quiz_tree = cfquiz_tree (ZIP the_configs the_configs_sym)`;;

(* Assembling embed_context for a configuration whose quiz fits at y in Gm,  *)
(* from the cfquiz.ml facts and QUIZ_PREEMBEDDING.                           *)
let CONFIG_EMBED_CONTEXT = prove
 (`!(Gm:(A)hypermap) cf y u.
     minimal_counter_example Gm /\ isQuizR (cfquiz cf) /\
     y IN dart Gm /\ fitqz Gm y (cfquiz cf) /\
     u IN dart (FST (cfmap cf)) /\
     valid_quiz (FST (cfmap cf)) (cfring cf) u (cfquiz cf)
     ==> embed_context Gm (FST (cfmap cf)) (cfring cf)
     (embedqz Gm (FST (cfmap cf)) y u (cfquiz cf))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CFQUIZ_CFMAP_PROPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CFRING_NODE_SCYCLE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CFQUIZ_GOOD_RING) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CPRADIUS2P) THEN
  REWRITE_TAC[radius2_kernel] THEN DISCH_TAC THEN
  (SUBGOAL_THEN `quasicubic (FST (cfmap cf)) (set_of_list (cfring cf))`
   ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP CONFIG_PROG_CUBIC o
                 MATCH_MP CFQUIZ_CONFIG_PROG) THEN
     DISCH_THEN(MP_TAC o MATCH_MP CPMAP_CUBIC) THEN
     REWRITE_TAC[cfring; cfmap] THEN SIMP_TAC[];
     ALL_TAC]) THEN
  REWRITE_TAC[embed_context] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MCE_PLANAR; MCE_PLAIN; MCE_CUBIC; MCE_BRIDGELESS; MCE_CONNECTED;
               MCE_PENTAGONAL] THEN
  REWRITE_TAC[GSYM QUASICUBIC_SET_OF_LIST] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC QUIZ_PREEMBEDDING THEN
    ASM_SIMP_TAC[MCE_PLAIN_CUBIC; plain_quasicubic];
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC EMBEDQZ_IN_DART THEN
    ASM_REWRITE_TAC[]]);;

(* Close the current case (fitqz G1 y1 .. with G1 = G or mirror G) by the    *)
(* no-embedding theorem.                                                     *)
let EMBED_FINISH_TAC =
  FIRST_ASSUM(fun th ->
    if not(is_app_of "fitqz" (concl th)) then failwith "EMBED_FINISH_TAC" else
    let g1 = rand(rator(rator(concl th))) and y1 = rand(rator(concl th)) in
    MP_TAC(ISPECL [g1; `EL i the_configs`; y1;
                   `u1:num`] CONFIG_EMBED_CONTEXT) THEN
    ASM_SIMP_TAC[MCE_MIRROR] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [g1; `EL i the_configs`;
                   list_mk_comb(
                    `embedqz:(A)hypermap->(num)hypermap->A->num->quiz->num->A`,
                                [g1; `FST (cfmap (EL i the_configs))`;
                                 y1; `u1:num`;
                                 `cfquiz (EL i the_configs)`])]
                                   NOT_EMBED_REDUCIBLE_CONFIG) THEN
    ASM_REWRITE_TAC[]);;

let NO_QZT_FIT_THE_QUIZ_TREE = prove
 (`!(G:(A)hypermap). check_reducibility /\ minimal_counter_example G
                     ==> !y. y IN dart G ==> ~qzt_fit G y the_quiz_tree`,
  REWRITE_TAC[the_quiz_tree] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `y:A`; `ZIP the_configs the_configs_sym`]
         QZT_FIT_CFQUIZ) THEN
  (ANTS_TAC THENL [ASM_SIMP_TAC[MCE_PLAIN_CUBIC]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `qz:quiz` STRIP_ASSUME_TAC))) THEN
  (SUBGOAL_THEN `i < LENGTH the_configs` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "<" (concl th))) THEN
     SIMP_TAC[LENGTH_ZIP; LENGTH_THE_CONFIGS; LENGTH_THE_CONFIGS_SYM];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `FST (EL i (ZIP the_configs the_configs_sym)) = EL i the_configs`
   ASSUME_TAC THENL
    [MATCH_MP_TAC EL_ZIP_FST THEN
     ASM_REWRITE_TAC[LENGTH_THE_CONFIGS; LENGTH_THE_CONFIGS_SYM];
     ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `FST (EL i (ZIP the_configs the_configs_sym)) = EL i the_configs`]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> is_eq(concl th) && lhs(concl th) = `qz:quiz`)) THEN
  (SUBGOAL_THEN `check_reducible (EL i the_configs)` ASSUME_TAC THENL
    [UNDISCH_TAC `check_reducibility` THEN REWRITE_TAC[check_reducibility] THEN
     DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MEM_EL THEN
     ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  MP_TAC(SPEC `EL i the_configs` VALID_CFQUIZ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:num` STRIP_ASSUME_TAC) THEN EMBED_FINISH_TAC);;

let NO_FIT_THE_REDPART = prove
 (`!(G:(A)hypermap).
     check_reducibility /\ minimal_counter_example G
     ==> !x p'. x IN dart G /\ redpart the_quiz_tree p'
                ==> ~exact_fitp G x p'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `the_quiz_tree`; `p':part`]
         NO_FIT_REDPART) THEN
  ASM_SIMP_TAC[MCE_PLAIN_CUBIC_PENTAGONAL] THEN
  MP_TAC(ISPEC `G:(A)hypermap` NO_QZT_FIT_THE_QUIZ_TREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reducible / Hubcap (Coq SUCCEED_BY_REDUCIBILITY / SUCCEED_BY_HUBCAP).     *)
(* ------------------------------------------------------------------------- *)

let SUCCEED_BY_REDUCIBILITY = prove
 (`!p0 p. check_reducibility /\ redpart the_quiz_tree p
          ==> succeeds_in (:A) p0 p`,
  REWRITE_TAC[succeeds_in; successful; valid_hub] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `G:(A)hypermap` NO_FIT_THE_REDPART) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `p:part`]) THEN ASM_REWRITE_TAC[]);;

let SUCCEED_BY_HUBCAP = prove
 (`!hc p0 p. check_reducibility /\
             hubcap_cover (size_part p) hc /\
             hubcap_fit (redpart the_quiz_tree) (the_drule_fork (size_part p))
             (size_part p) p hc
             ==> succeeds_in (:A) p0 p`,
  REWRITE_TAC[succeeds_in; successful; valid_hub] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `size_part p`; `redpart the_quiz_tree`;
                 `the_drule_fork (size_part p)`; `x:A`; `p:part`; `hc:hubcap`]
         HUBCAP_FIT_BOUND) THEN
  ASM_SIMP_TAC[MCE_PLAIN_CUBIC_PENTAGONAL; the_drule_fork;
               drule_fork_values] THEN
  MP_TAC(ISPEC `G:(A)hypermap` NO_FIT_THE_REDPART) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[]);;

