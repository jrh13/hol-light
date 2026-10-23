(* ========================================================================= *)
(* 4CT/four_color.ml                                                         *)
(*                                                                           *)
(* combinatorial4ct.v: the combinatorial Four Colour Theorem,                *)
(* FOUR_COLOR_HYPERMAP: reducibility ==> !H. planar_hypermap H /\ bridgeless *)
(* H ==> four_colorable H (Coq four_color_hypermap : planar_bridgeless G ->  *)
(* four_colorable G).  The proof: the cube reduction (CUBE_HYPERMAP, from    *)
(* the cube.ml lemmas) makes the map plain and precubic, and a minimal       *)
(* non-four-colourable such map (strong induction on the number of darts,    *)
(* PBPP_FOUR_COLORABLE) would be a minimal counter-example, which            *)
(* UNAVOIDABILITY excludes.                                                  *)
(*                                                                           *)
(* reducibility says that every one of the 633 configurations of             *)
(* configurations.ml passes check_reducible (cfreducible.ml); it is what the *)
(* computation of Part 2 establishes (part2_final.ml discharges it to give   *)
(* FOUR_COLOR), and it implies Coq's form, every configuration cfreducible   *)
(* (REDUCIBILITY_IMP_CFREDUCIBLE, via CHECK_REDUCIBLE_VALID).                *)
(* ========================================================================= *)

needs "4CT/cube.ml";;
needs "4CT/configurations.ml";;
needs "4CT/cfreducible.ml";;
needs "4CT/unavoidability.ml";;

(* ------------------------------------------------------------------------- *)
(* reducibility (Gonthier present.v:73 and cfreducible.v:82:                 *)
(* reducible_in_range 0 (size the_configs) the_configs, i.e. every           *)
(* configuration is cfreducible).  HOL states it as the check itself: every  *)
(* configuration of the_configs (configurations.ml, entry for entry Coq's    *)
(* configurations.v) passes check_reducible.  This is check_reducibility of  *)
(* present.ml (REDUCIBILITY_CHECK) and what the computation proves; it       *)
(* implies Coq's form by CHECK_REDUCIBLE_VALID                               *)
(* (REDUCIBILITY_IMP_CFREDUCIBLE).                                           *)
(* ------------------------------------------------------------------------- *)

let reducibility = new_definition
 `reducibility <=> !cf. MEM cf the_configs ==> check_reducible cf`;;

let REDUCIBILITY_CHECK = prove
 (`reducibility <=> check_reducibility`,
  REWRITE_TAC[reducibility; check_reducibility]);;

(* Coq's form of reducibility: every configuration is cfreducible.           *)
let REDUCIBILITY_IMP_CFREDUCIBLE = prove
 (`reducibility ==> !cf. MEM cf the_configs ==> cfreducible cf`,
  REWRITE_TAC[reducibility] THEN MESON_TAC[CHECK_REDUCIBLE_VALID]);;

(* ------------------------------------------------------------------------- *)
(* UNAVOIDABILITY (Gonthier unavoidability.v:20):                            *)
(*    reducibility ==> !G. ~minimal_counter_example G,                       *)
(* the discharging argument of unavoidability.ml (UNAVOIDABILITY_CHECK).     *)
(* ------------------------------------------------------------------------- *)

let UNAVOIDABILITY = prove
 (`reducibility ==> !H:(A)hypermap. ~(minimal_counter_example H)`,
  REWRITE_TAC[REDUCIBILITY_CHECK; UNAVOIDABILITY_CHECK]);;

(* ------------------------------------------------------------------------- *)
(* The cube reduction (Gonthier cube.v): cube G is a plain cubic hypermap,   *)
(* over the richer dart type cube_tag # A, that is planar/bridgeless iff G   *)
(* is, and 4-colorable only if G is.                                         *)
(* ------------------------------------------------------------------------- *)

let CUBE_HYPERMAP = prove
 (`!H:(A)hypermap.
     planar_hypermap H /\ bridgeless H
     ==> ?C:(cube_tag#A)hypermap.
            planar_bridgeless_plain_precubic C /\
            (four_colorable C ==> four_colorable H)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `cube (H:(A)hypermap)` THEN
  REWRITE_TAC[planar_bridgeless_plain_precubic; planar_bridgeless_plain;
              planar_bridgeless;
              PLANAR_CUBE; BRIDGELESS_CUBE; PLAIN_CUBE] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CUBE_COLORABLE; CUBIC_PRECUBIC; CUBIC_CUBE]);;

(* ------------------------------------------------------------------------- *)
(* The induction (Gonthier combinatorial4ct.v lines 24-29): every            *)
(* planar_bridgeless_plain_precubic hypermap is four-colourable, by strong   *)
(* induction on CARD(dart): a non-four-colourable one all of whose smaller   *)
(* such maps are four-colourable is a minimal_counter_example, which         *)
(* UNAVOIDABILITY excludes.                                                  *)
(* ------------------------------------------------------------------------- *)

let PBPP_FOUR_COLORABLE = prove
 (`reducibility
   ==> !H:(A)hypermap. planar_bridgeless_plain_precubic H
                       ==> four_colorable H`,
  DISCH_THEN(ASSUME_TAC o MATCH_MP UNAVOIDABILITY) THEN
  SUBGOAL_THEN
   `!n (H:(A)hypermap).
        CARD(dart H) = n /\ planar_bridgeless_plain_precubic H
        ==> four_colorable H`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `H:(A)hypermap` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
  REWRITE_TAC[planar_bridgeless_plain_precubic; planar_bridgeless_plain;
              planar_bridgeless] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `H:(A)hypermap` o
    check (is_neg o snd o dest_forall o concl)) THEN
  ASM_REWRITE_TAC[minimal_counter_example] THEN
  MATCH_MP_TAC(TAUT `b ==> ~(~a /\ b) ==> a`) THEN
  X_GEN_TAC `H':(A)hypermap` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(dart(H':(A)hypermap))`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `H':(A)hypermap`) THEN
  ASM_REWRITE_TAC[planar_bridgeless_plain_precubic; planar_bridgeless_plain;
                  planar_bridgeless]);;

(* ------------------------------------------------------------------------- *)
(* FOUR_COLOR_HYPERMAP (Gonthier combinatorial4ct.v): the combinatorial 4CT. *)
(* ------------------------------------------------------------------------- *)

let FOUR_COLOR_HYPERMAP = prove
 (`reducibility
   ==> !H:(A)hypermap. planar_hypermap H /\ bridgeless H ==> four_colorable H`,
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PBPP_FOUR_COLORABLE) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `H:(A)hypermap` CUBE_HYPERMAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(cube_tag#A)hypermap` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
    check (fun th -> let _,b = dest_forall(concl th) in is_imp b)) THEN
  ASM_REWRITE_TAC[]);;
