(* ========================================================================= *)
(* 4CT/discharge.ml                                                          *)
(*                                                                           *)
(* discharge.v: discharging arities to the neighbouring faces.  The 32       *)
(* discharge rules of Robertson, Sanders, Seymour and Thomas as part         *)
(* patterns (the_drules), the discharge score dscore of a face, the proof    *)
(* that some face has positive score (DSCORE_ROOTS, POSZ_DSCORE, via         *)
(* CUBIC_EULER), the rule fork drule_fork_values, sort_drules and the bounds *)
(* consumed by hubcap.ml and unavoidability.ml (DBOUND1_EQ, DBOUND2_LEQ,     *)
(* DBOUNDK_EQ, DSCORE_CAP1, DSCORE_CAP2), and the mirror invariance          *)
(* DSCORE_MIRROR.                                                            *)
(*                                                                           *)
(* Scores are integers, as in Coq: dscore1 counts the fitting rules, dscore2 *)
(* is a difference and dscore x = 60 - 10 arity x + the sum of dscore2 over  *)
(* the face; sums over sets use isum (Library/isum.ml) and & is int_of_num.  *)
(* Coq's section variables (nhub and the drule_fork rf = (rs, rt)) are       *)
(* explicit arguments, the record drule_fork being the pair (rs, rt) with    *)
(* the predicate drule_fork_values nhub rs rt in place of its proof field.   *)
(* ========================================================================= *)

needs "Library/isum.ml";;
needs "4CT/part.ml";;
needs "4CT/part_mirror.ml";;
needs "4CT/part_converse.ml";;
needs "4CT/embed_prelim.ml";;

(* ------------------------------------------------------------------------- *)
(* The 32 discharge rules (37 part constants; drule1 is used twice), in      *)
(* Coq's PartSyntax: `$ s $` = Pcons s Pr59, `$[h] s $` = Pcons s h,         *)
(* `$[h f1] 6 $` = Pcons6 h f1, `$[h f1 f2] 7 $` = Pcons7 h f1 f2,           *)
(* `$[h f1 f2 f3] 8 $` = Pcons8 h f1 f2 f3; the atoms 5 6 7 8, the star,     *)
(* 6+ 7+ 8+ 9+ 6- 7- 8- 6?7 6?8 7?8 are Pr55 Pr66 Pr77 Pr88 Pr59 Pr69 Pr79   *)
(* Pr89 Pr99 Pr56 Pr57 Pr58 Pr67 Pr68 Pr78.  The primed Coq names drule2'    *)
(* etc. are drule2_P etc.                                                    *)
(* ------------------------------------------------------------------------- *)

let drule1 = new_definition
 `drule1 = Pcons Pr59 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))`
 ;;
let drule2 = new_definition
 `drule2 = Pcons Pr59 Pr59
 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))`
 ;;
let drule2_P = new_definition
 `drule2_P = Pcons Pr59 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr79 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))`
 ;;
let drule3 = new_definition
 `drule3 = Pcons Pr55 Pr59
 (Pcons Pr56 Pr59 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))`
 ;;
let drule3_P = new_definition
 `drule3_P = Pcons Pr55 Pr59
 (Pcons Pr56 Pr59
 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))`
 ;;
let drule4 = new_definition
 `drule4 = Pcons Pr56 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))`
 ;;
let drule4_P = new_definition
 `drule4_P = Pcons Pr56 Pr59
 (Pcons Pr66 Pr55
 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))`
 ;;
let drule5 = new_definition
 `drule5 = Pcons Pr66 Pr59
 (Pcons6 Pr56 Pr55
 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))`
 ;;
let drule6 = new_definition
 `drule6 = Pcons Pr66 Pr59
 (Pcons Pr55 Pr56
 (Pcons Pr79 Pr55 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))`
 ;;
let drule7 = new_definition
 `drule7 = Pcons Pr66 Pr59
 (Pcons6 Pr66 Pr56
 (Pcons Pr79 Pr55 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))`
 ;;
let drule8 = new_definition
 `drule8 = Pcons Pr55 Pr59
 (Pcons Pr56 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr59 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule9 = new_definition
 `drule9 = Pcons Pr56 Pr59
 (Pcons Pr56 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr59 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 Pnil))))))`;;
let drule10 = new_definition
 `drule10 = Pcons Pr55 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule10_P = new_definition
 `drule10_P =
 Pcons Pr55 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule11 = new_definition
 `drule11 = Pcons Pr66 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule12 = new_definition
 `drule12 = Pcons Pr55 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr55 Pr55 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule13 = new_definition
 `drule13 = Pcons Pr66 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr89 Pr55
 (Pcons Pr55 Pr59
 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule14 = new_definition
 `drule14 = Pcons Pr55 Pr59
 (Pcons Pr66 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule15 = new_definition
 `drule15 = Pcons Pr55 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil))))))`;;
let drule16 = new_definition
 `drule16 = Pcons Pr66 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil))))))`;;
let drule17 = new_definition
 `drule17 = Pcons Pr55 Pr59
 (Pcons Pr66 Pr66
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr55 Pr59 (Pcons Pr79 Pr59 (Pcons Pr55 Pr59 Pnil))))))`;;
let drule18 = new_definition
 `drule18 = Pcons Pr66 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr77 Pr55
 (Pcons Pr69 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 Pnil))))))`;;
let drule19 = new_definition
 `drule19 = Pcons Pr66 Pr59
 (Pcons Pr69 Pr59
 (Pcons Pr89 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr66 Pr55 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil))))))`;;
let drule20 = new_definition
 `drule20 = Pcons Pr55 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr66 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 Pnil))))))`;;
let drule21 = new_definition
 `drule21 = Pcons Pr56 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr77 Pr55
 (Pcons Pr69 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 Pnil))))))`;;
let drule22 = new_definition
 `drule22 = Pcons Pr55 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr77 Pr55
 (Pcons Pr69 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil))))))`;;
let drule23 = new_definition
 `drule23 = Pcons Pr55 Pr59
 (Pcons Pr77 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule24 = new_definition
 `drule24 = Pcons Pr55 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr77 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr66 Pr59 (Pcons Pr66 Pr59 (Pcons Pr55 Pr59 Pnil))))))`;;
let drule25 = new_definition
 `drule25 = Pcons Pr55 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr79 Pr59
 (Pcons7 Pr59 Pr59 Pr55
 (Pcons Pr55 Pr66 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule26 = new_definition
 `drule26 = Pcons Pr66 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr77 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr66 Pr59 Pnil))))))`;;
let drule27 = new_definition
 `drule27 = Pcons Pr79 Pr59
 (Pcons Pr66 Pr59
 (Pcons7 Pr66 Pr55 Pr69
 (Pcons Pr77 Pr59
 (Pcons Pr56 Pr55 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil))))))`;;
let drule28 = new_definition
 `drule28 = Pcons Pr55 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 Pnil)))))))`;;
let drule29 = new_definition
 `drule29 = Pcons Pr55 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr59 Pr59
 (Pcons Pr59 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 Pnil)))))))`;;
let drule30 = new_definition
 `drule30 = Pcons Pr55 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr66 Pr55
 (Pcons Pr55 Pr59 (Pcons Pr59 Pr59 (Pcons Pr59 Pr59 Pnil)))))))`;;
let drule31 = new_definition
 `drule31 = Pcons Pr55 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr55 Pr69
 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr69 Pr59 Pnil)))))))`;;
let drule31_P = new_definition
 `drule31_P =
 Pcons Pr55 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr55 Pr59
 (Pcons Pr55 Pr55
 (Pcons Pr69 Pr59 (Pcons Pr59 Pr59 (Pcons Pr69 Pr59 Pnil)))))))`;;
let drule32 = new_definition
 `drule32 = Pcons Pr55 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr77 Pr55
 (Pcons Pr79 Pr59
 (Pcons Pr66 Pr59
 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 (Pcons Pr55 Pr59 Pnil)))))))`;;

(* base_drules: 38 items (drule1 twice, Coq order).                          *)
let base_drules = new_definition
 `base_drules =
   [drule1; drule1; drule2; drule2_P; drule3; drule3_P; drule4;
    drule4_P; drule5;
    drule6; drule7; drule8; drule9; drule10; drule10_P;
    drule11; drule12; drule13; drule14; drule15; drule16; drule17;
    drule18; drule19;
    drule20; drule21; drule22; drule23; drule24; drule25; drule26; drule27;
    drule28; drule29;
    drule30; drule31; drule31_P; drule32]`;;

(* sym_drule p = the reflection of p across its third spoke (Coq inline:     *)
(* iter 5 (rot_part (size_part p).-1) (mirror_part p)).                      *)
let sym_drule = new_definition
 `sym_drule p = ITER 5 (rot_part (size_part p - 1)) (mirror_part p)`;;

let symmetrize_drules = new_recursive_definition list_RECURSION
 `(symmetrize_drules [] = []) /\
  (symmetrize_drules (CONS p r) =
     if cmp_part p (sym_drule p) = Psubset then CONS p (symmetrize_drules r)
     else CONS (sym_drule p) (CONS p (symmetrize_drules r)))`;;

let the_drules = new_definition `the_drules = symmetrize_drules base_drules`;;

(* ------------------------------------------------------------------------- *)
(* Scores (integers). dscore1 x = number of the_drules fitting exactly at    *)
(* inv_face2 x: the score transferred from the face of x to the face of edge *)
(* x.                                                                        *)
(* ------------------------------------------------------------------------- *)

let dscore1 = new_definition
 `dscore1 (H:(A)hypermap) x =
    (&(LENGTH (FILTER (\p. exact_fitp H (inv_face2 H x) p) the_drules)) : int)`
    ;;

let dscore2 = new_definition
 `dscore2 (H:(A)hypermap) x = dscore1 H (edge_map H x) - dscore1 H x`;;

let dscore = new_definition
 `dscore (H:(A)hypermap) x =
    (&60 : int) - &(10 * arity H x) + isum (face H x) (\y. dscore2 H y)`;;

(* The score of a face given as a set (used for the global count).           *)
let dscoreF = new_definition
 `dscoreF (H:(A)hypermap) (fc:A->bool) =
    (&60 : int) - &(10 * CARD fc) + isum fc (\y. dscore2 H y)`;;

(* ------------------------------------------------------------------------- *)
(* Rule selection for a hub size (Coq Section ScoreBound).                   *)
(* ------------------------------------------------------------------------- *)

let pick_source_drules = new_definition
 `pick_source_drules nhub (r:(part)list) = FILTER (\p. size_part p = nhub) r`;;

let pick_target_drules = new_recursive_definition list_RECURSION
 `(pick_target_drules nhub [] = []) /\
  (pick_target_drules nhub (CONS p r) =
     if mem_range (FST (converse_part p)) nhub
     then CONS (SND (converse_part p)) (pick_target_drules nhub r)
     else pick_target_drules nhub r)`;;

(* sort_drules p r = (the number of rules of r forced by p, the rules of r   *)
(* straddling p).                                                            *)
let sort_drules_rec = new_recursive_definition list_RECURSION
 `(sort_drules_rec p n rs [] = (n, rs)) /\
  (sort_drules_rec p n rs (CONS p' r') =
     if cmp_part p p' = Psubset then sort_drules_rec p (SUC n) rs r'
     else if cmp_part p p' = Pstraddle then sort_drules_rec p n (CONS p' rs) r'
     else sort_drules_rec p n rs r')`;;

let sort_drules = new_definition
 `sort_drules p r = sort_drules_rec p 0 [] r`;;

(* The drule fork for hub size nhub: (source rules, target rules).           *)
let drule_fork_values = new_definition
 `drule_fork_values nhub (rs:(part)list) (rt:(part)list) <=>
    rs = pick_source_drules nhub the_drules /\
    rt = pick_target_drules nhub the_drules`;;

let the_drule_fork = new_definition
 `the_drule_fork nhub =
  (pick_source_drules nhub the_drules, pick_target_drules nhub the_drules)`;;

let dbound1 = new_definition
 `dbound1 (H:(A)hypermap) (r:(part)list) x =
  LENGTH (FILTER (\p. fitp p H x) r)`;;

let dbound2 = new_definition
 `dbound2 (H:(A)hypermap) r r' x =
  (&(dbound1 H r x) : int) - &(dbound1 H r' x)`;;

(* dboundK nhub = 60 - 10 nhub for nhub >= 5 (and 10 below 5, like Coq).     *)
let dboundK = new_definition
 `dboundK nhub = if nhub <= 5 then (&10 : int) else --(&((nhub - 6) * 10))`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* dscore is constant on faces (Coq DSCORE_CFACE).                           *)
let DSCORE_CFACE = prove
 (`!(H:(A)hypermap) x y. x IN dart H /\ cface H x y
                         ==> dscore H x = dscore H y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dscore] THEN
  SUBGOAL_THEN `arity H (y:A) = arity H x` SUBST1_TAC THENL
   [MATCH_MP_TAC ARITY_CFACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `face H (y:A) = face H x` SUBST1_TAC THENL
   [REWRITE_TAC[face] THEN
    MP_TAC(ISPECL[`face_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`; `x:A`;
                  `y:A`] ORBIT_MAP_EQ) THEN
    ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `cface H (x:A) y` THEN
    REWRITE_TAC[cface; face];
    ALL_TAC] THEN
  REFL_TAC);;

(* dscore of a dart is the score of its face as a set.                       *)
let DSCORE_FACE = prove
 (`!(H:(A)hypermap) x. x IN dart H ==> dscore H x = dscoreF H (face H x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[dscore; dscoreF; arity; orbit_size; face]);;

(* Sums over the faces of H partition the sum over the darts.                *)
let ISUM_SET_OF_ORBITS = prove
 (`!(f:A->A) s (g:A->int).
     FINITE s /\ f permutes s ==>
     isum (set_of_orbits s f) (\t. isum t g) = isum s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`g:A->int`; `set_of_orbits (s:A->bool) f`]
         ISUM_UNIONS_NONZERO) THEN
  ASM_SIMP_TAC[UNIONS_SET_OF_ORBITS; FINITE_SET_OF_ORBITS] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL[`f:A->A`; `s:A->bool`; `t:A->bool`]
             FINITE_IN_SET_OF_ORBITS) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t1:A->bool`; `t2:A->bool`; `x:A`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL[`f:A->A`; `s:A->bool`] ORBITS_DISJOINT') THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL[`t1:A->bool`; `t2:A->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

(* The transfers cancel globally: edge_map permutes the darts.               *)
let ISUM_DSCORE2_ZERO = prove
 (`!(H:(A)hypermap). isum (dart H) (\y. dscore2 H y) = &0`,
  GEN_TAC THEN REWRITE_TAC[dscore2] THEN SIMP_TAC[ISUM_SUB; FINITE_DART] THEN
  MATCH_MP_TAC(INT_ARITH `a:int = b ==> a - b = &0`) THEN
  MP_TAC(ISPECL[`\y:A. dscore1 (H:(A)hypermap) y`; `edge_map (H:(A)hypermap)`;
                `dart (H:(A)hypermap)`]
               ISUM_BIJECTION) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MESON_TAC[EDGE_MAP_PERMUTES; PERMUTES_IN_IMAGE];
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      MESON_TAC[EDGE_MAP_PERMUTES; PERMUTES_SURJECTIVE; PERMUTES_IN_IMAGE;
                PERMUTES_INJECTIVE]];
    DISCH_THEN(fun th -> REWRITE_TAC[th; o_DEF])]);;

(* Coq dscore_roots: the face scores add up to 120 (10 times the cubic Euler *)
(* formula).                                                                 *)
let DSCORE_ROOTS = prove
 (`!(H:(A)hypermap).
     plain_cubic_connected H /\ planar_hypermap H /\ ~(dart H = {})
     ==> isum (face_set H) (\fc. dscoreF H fc) = (&120 : int)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `6 * number_of_faces (H:(A)hypermap) = CARD (dart H) + 12`
    MP_TAC THENL
   [ASM_MESON_TAC[CUBIC_EULER]; ALL_TAC] THEN
  REWRITE_TAC[number_of_faces] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE (face_set (H:(A)hypermap))` ASSUME_TAC THENL
   [REWRITE_TAC[face_set] THEN MATCH_MP_TAC FINITE_SET_OF_ORBITS THEN
    REWRITE_TAC[FINITE_DART];
    ALL_TAC] THEN
  REWRITE_TAC[dscoreF] THEN ASM_SIMP_TAC[ISUM_ADD; ISUM_SUB; ISUM_CONST] THEN
  SUBGOAL_THEN `isum (face_set H) (\fc. &(10 * CARD fc)) =
                isum (face_set (H:(A)hypermap)) (\fc. isum fc (\y:A. &10))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `fc:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE (fc:A->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL[`face_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`;
                    `fc:A->bool`] FINITE_IN_SET_OF_ORBITS) THEN
      ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES; GSYM face_set];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ISUM_CONST] THEN REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[face_set] THEN
  SIMP_TAC[ISUM_SET_OF_ORBITS; FINITE_DART; FACE_MAP_PERMUTES] THEN
  SIMP_TAC[ISUM_CONST; FINITE_DART] THEN REWRITE_TAC[ISUM_DSCORE2_ZERO] THEN
  UNDISCH_TAC `6 * CARD (face_set (H:(A)hypermap)) = CARD (dart H) + 12` THEN
  REWRITE_TAC[face_set; GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL;
              GSYM INT_OF_NUM_ADD] THEN
  INT_ARITH_TAC);;

(* Coq POSZ_DSCORE: some dart has positive score.                            *)
let POSZ_DSCORE = prove
 (`!(H:(A)hypermap).
     plain_cubic_connected H /\ planar_hypermap H /\ ~(dart H = {})
     ==> ?x. x IN dart H /\ (&0 : int) < dscore H x`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `H:(A)hypermap` DSCORE_ROOTS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `(~q ==> ~p) ==> p ==> q`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`; INT_NOT_LT] THEN
  DISCH_TAC THEN MATCH_MP_TAC(INT_ARITH `s:int <= &0 ==> ~(s = &120)`) THEN
  GEN_REWRITE_TAC RAND_CONV
    [GSYM(ISPEC `face_set (H:(A)hypermap)` ISUM_0)] THEN
  MATCH_MP_TAC ISUM_LE THEN
  SIMP_TAC[face_set; FINITE_SET_OF_ORBITS; FINITE_DART] THEN
  REWRITE_TAC[set_of_orbits; FORALL_IN_GSPEC; GSYM face] THEN
  ASM_SIMP_TAC[GSYM DSCORE_FACE]);;

(* Coq DBOUND1_EQ.                                                           *)
let DBOUND1_EQ = prove
 (`!(H:(A)hypermap) nhub rs rt x.
     plain_cubic_pentagonal H /\ drule_fork_values nhub rs rt /\
     x IN dart H /\ arity H x = nhub
     ==> dscore1 H (face_map H (face_map H x)) = (&(dbound1 H rs x) : int)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drule_fork_values] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[dscore1; dbound1; INV_FACE2_FF; pick_source_drules;
                  FILTER_FILTER; INT_OF_NUM_EQ] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[exact_fitp] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let DBOUND1_CONS = prove
 (`!(H:(A)hypermap) p r x.
     dbound1 H (CONS p r) x = (if fitp p H x then 1 else 0) + dbound1 H r x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dbound1; FILTER] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* sort_drules_rec preserves the fitting count (Coq sort_drulesP,            *)
(* generalised over the accumulators n and rs).                              *)
let SORT_DBOUND1_REC = prove
 (`!(H:(A)hypermap) p x.
     fitp p H x
     ==> !ru n rs. dbound1 H ru x + n + dbound1 H rs x =
                   FST (sort_drules_rec p n rs ru) +
                   dbound1 H (SND (sort_drules_rec p n rs ru)) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[sort_drules_rec] THENL
   [REWRITE_TAC[dbound1; FILTER; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `rs:(part)list`] THEN
  MP_TAC(SPEC `h:part`
   (MATCH_MP FITP_CMP (ASSUME `fitp p (H:(A)hypermap) x`))) THEN
  STRUCT_CASES_TAC(ISPEC `cmp_part p h` (cases "part_rel")) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[DBOUND1_CONS; distinctness "part_rel";
                                   REWRITE_RULE[apply_part_rel] th]) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th; DBOUND1_CONS]) THEN
  ARITH_TAC);;

(* Coq SORT_DBOUND1_EQ / sort_drulesP.                                       *)
let SORT_DBOUND1_EQ = prove
 (`!(H:(A)hypermap) p x ru.
     fitp p H x
     ==> dbound1 H ru x =
     FST (sort_drules p ru) + dbound1 H (SND (sort_drules p ru)) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sort_drules] THEN
  MP_TAC(SPECL[`ru:(part)list`; `0`; `[]:(part)list`]
         (MATCH_MP SORT_DBOUND1_REC (ASSUME `fitp p (H:(A)hypermap) x`))) THEN
  REWRITE_TAC[dbound1; FILTER; LENGTH; ADD_CLAUSES]);;

(* Each rule fitting exactly at y = inv_face2 (e (f (f x))) has a converse   *)
(* fitting at x among the target rules, so the exact-fit count is bounded.   *)
let DBOUND1_TARGET_LE = prove
 (`!(H:(A)hypermap) nhub x y l.
     (!r. exact_fitp H y r
          ==> mem_range (FST (converse_part r)) nhub /\
          fitp (SND (converse_part r)) H x)
     ==> LENGTH (FILTER (\p. exact_fitp H y p) l) <=
     dbound1 H (pick_target_drules nhub l) x`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "conv") THEN
  SPEC_TAC(`l:(part)list`, `l:(part)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; pick_target_drules; dbound1; LENGTH; LE_REFL] THEN
  ASM_CASES_TAC `exact_fitp H (y:A) (h:part)` THEN ASM_REWRITE_TAC[] THENL
   [REMOVE_THEN "conv" (MP_TAC o SPEC `h:part`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[FILTER; LENGTH] THEN
    UNDISCH_TAC `LENGTH (FILTER (\p. exact_fitp H (y:A) p) t) <=
                 dbound1 H (pick_target_drules nhub t) x` THEN
    REWRITE_TAC[dbound1] THEN ARITH_TAC;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER] THEN TRY COND_CASES_TAC THEN
    ASM_REWRITE_TAC[LENGTH] THEN
    UNDISCH_TAC `LENGTH (FILTER (\p. exact_fitp H (y:A) p) t) <=
                 dbound1 H (pick_target_drules nhub t) x` THEN
    REWRITE_TAC[dbound1] THEN ARITH_TAC]);;

(* Coq DBOUND2_LEQ (uses FITP_CONVERSE from part_converse.ml).               *)
let DBOUND2_LEQ = prove
 (`!(H:(A)hypermap) nhub rs rt x.
     plain_cubic_pentagonal H /\ drule_fork_values nhub rs rt /\
     x IN dart H /\ arity H x = nhub
     ==> dscore2 H (face_map H (face_map H x)) <= dbound2 H rt rs x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `plain_hypermap (H:(A)hypermap)` ASSUME_TAC THENL
   [UNDISCH_TAC `plain_cubic_pentagonal (H:(A)hypermap)` THEN
    SIMP_TAC[plain_cubic_pentagonal; plain_cubic];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `nhub:num`; `rs:(part)list`; `rt:(part)list`;
                `x:A`] DBOUND1_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[dscore2; dbound2] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INT_ARITH `a:int <= b ==> a - c <= b - c`) THEN
  UNDISCH_TAC `drule_fork_values nhub rs rt` THEN
  REWRITE_TAC[drule_fork_values] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC) THEN
  REWRITE_TAC[dscore1; INT_OF_NUM_LE] THEN MATCH_MP_TAC DBOUND1_TARGET_LE THEN
  X_GEN_TAC `r:part` THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:part`;
                `inv_face2 H (edge_map H (face_map H (face_map H (x:A))))`]
         FITP_CONVERSE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[INV_FACE2_IN_DART; EDGE_MAP_IN_DART; FACE_MAP_IN_DART];
    ALL_TAC] THEN
  REWRITE_TAC[FF_INV_FACE2] THEN
  SUBGOAL_THEN `edge_map H (edge_map H (face_map H (face_map H (x:A)))) =
                face_map H (face_map H x)` SUBST1_TAC THENL
   [MATCH_MP_TAC PLAIN_EQ THEN ASM_SIMP_TAC[FACE_MAP_IN_DART]; ALL_TAC] THEN
  REWRITE_TAC[INV_FACE2_FF; tight_fitp] THEN ASM_REWRITE_TAC[]);;

(* Coq DBOUNDK_EQ.                                                           *)
let DBOUNDK_EQ = prove
 (`!(H:(A)hypermap) nhub x.
     pentagonal H /\ x IN dart H /\ arity H x = nhub
     ==> dboundK nhub = (&60 : int) - &(10 * arity H x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pentagonal] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[dboundK] THEN
  DISCH_TAC THEN ASM_CASES_TAC `nhub <= 5` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `nhub = 5` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH] THEN INT_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&(nhub - 6) = &nhub - (&6:int)` SUBST1_TAC THENL
     [MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    INT_ARITH_TAC]);;

let FINITE_FACE = prove
 (`!(H:(A)hypermap) x. x IN dart H ==> FINITE (face H x)`,
  REWRITE_TAC[face] THEN
  MESON_TAC[ORBIT_FINITE; FINITE_DART; FACE_MAP_PERMUTES]);;

(* Coq DSCORE_CAP1: if every transfer is at most m, a positive-score dart    *)
(* has small arity: dscore x <= 60 - (10 - m) arity x.                       *)
let DSCORE_CAP1 = prove
 (`!(H:(A)hypermap) m.
     (!y. y IN dart H ==> dscore1 H y <= (&m : int))
     ==> !x. x IN dart H /\ (&0 : int) < dscore H x
             ==> !d. 59 < (10 - m) * d ==> arity H x < d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `m < 10` ASSUME_TAC THENL
   [REFUTE_THEN(MP_TAC o MATCH_MP (ARITH_RULE `~(m < 10) ==> 10 - m = 0`)) THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `59 < (10 - m) * d` THEN
                         REWRITE_TAC[th; MULT_CLAUSES]) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&60:int) <= (&10 - &m) * &(arity (H:(A)hypermap) x)`
  MP_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_SUB; LT_IMP_LE; INT_OF_NUM_MUL; INT_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(10 - m) * d` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `isum (face H x) (\y. dscore2 (H:(A)hypermap) y) <=
                isum (face H x) (\y. &m)` MP_TAC THENL
   [MATCH_MP_TAC ISUM_LE THEN ASM_SIMP_TAC[FINITE_FACE; GSYM cface] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[dscore2] THEN
    MATCH_MP_TAC(INT_ARITH `a:int <= m /\ &0 <= b ==> a - b <= m`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[CFT_DART; EDGE_MAP_IN_DART];
      REWRITE_TAC[dscore1; INT_POS]];
    ALL_TAC] THEN
  UNDISCH_TAC `(&0:int) < dscore (H:(A)hypermap) x` THEN
  ASM_SIMP_TAC[ISUM_CONST; FINITE_FACE] THEN
  REWRITE_TAC[dscore; arity; orbit_size; face; GSYM INT_OF_NUM_MUL] THEN
  INT_ARITH_TAC);;

(* All discharge rules have size 5..8 (symmetrization preserves size).       *)
let SIZE_ITER_ROT_PART = prove
 (`!n k q. size_part (ITER n (rot_part k) q) = size_part q`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; SIZE_ROT_PART]);;

let SIZE_SYM_DRULE = prove
 (`!p. size_part (sym_drule p) = size_part p`,
  REWRITE_TAC[sym_drule; SIZE_ITER_ROT_PART; SIZE_MIRROR_PART]);;

let ALL_SIZE_SYMMETRIZE = prove
 (`!P r. (!p. P p <=> P (sym_drule p)) /\ ALL P r
         ==> ALL P (symmetrize_drules r)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[symmetrize_drules; ALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun sym ->
    SUBGOAL_THEN `ALL P (symmetrize_drules t)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     ACCEPT_TAC sym; ALL_TAC] THEN
    MP_TAC(SPEC `h:part` sym) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL]));;

let ALL_SIZE_BASE_DRULES = prove
 (`ALL (\p. 5 <= size_part p /\ size_part p <= 8) base_drules`,
  REWRITE_TAC[base_drules; ALL; drule1; drule2; drule2_P; drule3; drule3_P;
              drule4; drule4_P; drule5; drule6; drule7; drule8; drule9;
              drule10; drule10_P; drule11; drule12; drule13; drule14; drule15;
              drule16; drule17; drule18; drule19; drule20; drule21; drule22;
              drule23; drule24; drule25; drule26; drule27; drule28; drule29;
              drule30; drule31; drule31_P; drule32; size_part] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ALL_SIZE_THE_DRULES = prove
 (`ALL (\p. 5 <= size_part p /\ size_part p <= 8) the_drules`,
  REWRITE_TAC[the_drules] THEN MATCH_MP_TAC ALL_SIZE_SYMMETRIZE THEN
  REWRITE_TAC[ALL_SIZE_BASE_DRULES; SIZE_SYM_DRULE]);;

(* Coq SOURCE_DRULES_RANGE.                                                  *)
let SOURCE_DRULES_RANGE = prove
 (`!nhub rs rt. ~(mem_range Pr58 nhub) /\ drule_fork_values nhub rs rt
                ==> rs = []`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drule_fork_values; mem_range] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pick_source_drules] THEN
  MATCH_MP_TAC FILTER_NONE THEN MP_TAC ALL_SIZE_THE_DRULES THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN REWRITE_TAC[] THEN
  X_GEN_TAC `p:part` THEN STRIP_TAC THEN ASM_ARITH_TAC);;

(* f o f stays in the face.                                                  *)
let CFACE_FF = prove
 (`!(H:(A)hypermap) x y. cface H x y
                         ==> cface H x (face_map H (face_map H y))`,
  REWRITE_TAC[cface; face; orbit_map; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `SUC(SUC n)` THEN ASM_REWRITE_TAC[ITER]);;

(* Reindexing a face sum by f and by f o f (bijections of the face).         *)
let ISUM_FACE_F = prove
 (`!(H:(A)hypermap) x (g:A->int).
     x IN dart H ==>
     isum (face H x) (\y. g (face_map H y)) = isum (face H x) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
         [`g:A->int`; `face_map (H:(A)hypermap)`; `face (H:(A)hypermap) x`]
         ISUM_INJECTION) THEN
  REWRITE_TAC[o_DEF; GSYM cface] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FINITE_FACE] THEN
  ASM_MESON_TAC[CFACE_TRANS; CFT_FACE; faceK]);;

let ISUM_FACE_FF = prove
 (`!(H:(A)hypermap) x (g:A->int).
     x IN dart H
     ==> isum (face H x) (\y. g (face_map H (face_map H y))) =
         isum (face H x) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `\y. (g:A->int) (face_map H y)`]
         ISUM_FACE_F) THEN
  ASM_SIMP_TAC[ISUM_FACE_F]);;

(* Coq DSCORE_CAP2.                                                          *)
let DSCORE_CAP2 = prove
 (`!(H:(A)hypermap) nhub rs rt x.
     plain_cubic_pentagonal H /\ drule_fork_values nhub rs rt /\
     x IN dart H /\ arity H x = nhub /\ (&0 : int) < dscore H x
     ==> (&0 : int) < dboundK nhub + isum (face H x) (\y. dbound2 H rt rs y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dboundK nhub = (&60 : int) - &(10 * arity (H:(A)hypermap) x)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC DBOUNDK_EQ THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `plain_cubic_pentagonal (H:(A)hypermap)` THEN
    SIMP_TAC[plain_cubic_pentagonal];
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LTE_TRANS THEN EXISTS_TAC `dscore (H:(A)hypermap) x` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[dscore] THEN
  MATCH_MP_TAC(INT_ARITH `a:int <= b ==> c + a <= c + b`) THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `x:A`; `\y. dscore2 (H:(A)hypermap) y`]
         ISUM_FACE_FF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC ISUM_LE THEN ASM_SIMP_TAC[FINITE_FACE] THEN X_GEN_TAC `y:A` THEN
  REWRITE_TAC[GSYM cface] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL
   [MATCH_MP_TAC CFT_DART THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `arity H (y:A) = nhub` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`H:(A)hypermap`; `x:A`; `y:A`] ARITY_CFACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `nhub:num`; `rs:(part)list`; `rt:(part)list`;
                `y:A`] DBOUND2_LEQ) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Coq dscore_mirror (discharge.v:219): the score is mirror-invariant.       *)
(* Arity and faces are preserved; the transfer count obeys Gonthier's        *)
(* score1F, dscore1 (mirror H) (f z) = dscore1 H z: a rule p fits exactly in *)
(* the mirror at f^3 z iff its reflection sym_drule p fits in H at inv_face2 *)
(* z (FITP_MIRROR and five backward rotations, ROT_ITER_FIT), and            *)
(* symmetrize_drules makes the_drules closed under sym_drule, so the two     *)
(* counts agree (SYMMETRIZE_COUNT_MIRROR).  Coq's hypothesis                 *)
(* planar_plain_cubic_connected is weakened to plain and cubic.              *)
(* ------------------------------------------------------------------------- *)

(* Iterating the face map (size q) times does not change exact fitting of q. *)
let FIT_ITER_SIZE = prove
 (`!(G:(A)hypermap) q n u.
     size_part q = n
     ==> (exact_fitp G (ITER n (face_map G) u) q <=> exact_fitp G u q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exact_fitp; ARITY_ITER_FACE_GEN] THEN
  ASM_CASES_TAC `arity G (u:A) = size_part q` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ITER n (face_map G) (u:A) = u` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[ITER_FACE_ARITY_GEN]);;

(* Rotating a part by (size - 1) = rotating back one spoke.                  *)
let ROT_PRED_FIT = prove
 (`!(G:(A)hypermap) q u.
     1 <= size_part q
     ==> (exact_fitp G u (rot_part (size_part q - 1) q) <=>
          exact_fitp G (face_map G u) q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL[`size_part q - 1`;`q:part`] FITP_ROT) THEN ANTS_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    ONCE_REWRITE_TAC[ISPECL[`G:(A)hypermap`;`face_map G (u:A)`] th]) THEN
  REWRITE_TAC[ITER_COMMUTE; GSYM(CONJUNCT2 ITER)] THEN
  SUBGOAL_THEN `SUC (size_part q - 1) = size_part q` SUBST1_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIT_ITER_SIZE THEN
  REWRITE_TAC[SIZE_ROT_PART]);;

let ROT_ITER_FIT = prove
 (`!(G:(A)hypermap) q. 1 <= size_part q
     ==> !k u. exact_fitp G u (ITER k (rot_part (size_part q - 1)) q) <=>
               exact_fitp G (ITER k (face_map G) u) q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  GEN_TAC THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `ITER k (rot_part (size_part q - 1)) q`;
                `u:A`] ROT_PRED_FIT) THEN
  REWRITE_TAC[SIZE_ITER_ROT_PART] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[ITER_COMMUTE]);;

(* The mirror's inv_face2 at f z is f^3 z; five mirror face steps from f^3 z *)
(* land on inv_face2 z.                                                      *)
let INV_FACE2_MIRROR_F = prove
 (`!(H:(A)hypermap) z.
     plain_hypermap H
     ==> inv_face2 (mirror H) (face_map H z) =
         face_map H (face_map H (face_map H z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inv_face2; MIRROR_COMPONENTS; o_THM] THEN
  ASM_SIMP_TAC[CFT_PLAIN_NF; CFT_PLAIN_EE]);;
let ITER5_MIRROR_FACE = prove
 (`!(H:(A)hypermap) z.
     ITER 5 (face_map (mirror H)) (face_map H (face_map H (face_map H z))) =
     inv_face2 H z`,
  REWRITE_TAC[ITER5; MIRROR_COMPONENTS; o_THM; faceK; inv_face2]);;

(* Psubset transfers exact fitting (same size).                              *)
let EXACT_FIT_PSUBSET = prove
 (`!(G:(A)hypermap) x p q.
     cmp_part p q = Psubset /\ size_part q = size_part p /\ exact_fitp G x p
     ==> exact_fitp G x q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exact_fitp] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL[`p:part`; `G:(A)hypermap`; `x:A`] FITP_CMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q:part`) THEN
  ASM_REWRITE_TAC[apply_part_rel]);;

(* The two reflection correspondences: p in the mirror at f^3 z <-> sym p in *)
(* H at inv_face2 z, and sym p in the mirror <-> p in H.                     *)
let SYM_FIT_MIRROR1 = prove
 (`!(H:(A)hypermap) z p.
     plain_hypermap H /\ cubic_hypermap H /\ z IN dart H /\ 1 <= size_part p
     ==> (exact_fitp (mirror H) (face_map H (face_map H (face_map H z))) p <=>
          exact_fitp H (inv_face2 H z) (sym_drule p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `H:(A)hypermap` FITP_MIRROR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o
    ISPECL[`p:part`;`face_map H (face_map H (face_map H (z:A)))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC IN_DART_EQS; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[sym_drule] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`;`mirror_part p`] ROT_ITER_FIT) THEN
  REWRITE_TAC[SIZE_MIRROR_PART] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ITER5; FF_INV_FACE2]);;
let SYM_FIT_MIRROR2 = prove
 (`!(H:(A)hypermap) z p.
     plain_hypermap H /\ cubic_hypermap H /\ z IN dart H /\ 1 <= size_part p
     ==> (exact_fitp (mirror H) (face_map H (face_map H (face_map H z)))
                     (sym_drule p) <=>
          exact_fitp H (inv_face2 H z) p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sym_drule] THEN
  MP_TAC(ISPECL[`mirror (H:(A)hypermap)`;`mirror_part p`] ROT_ITER_FIT) THEN
  REWRITE_TAC[SIZE_MIRROR_PART] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ITER5_MIRROR_FACE] THEN
  MP_TAC(ISPEC `H:(A)hypermap` FITP_MIRROR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o ISPECL[`mirror_part p`;`inv_face2 H (z:A)`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[INV_FACE2_IN_DART]; ALL_TAC] THEN
  REWRITE_TAC[MIRROR_MIRROR_PART] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* The exact-fit counts over a symmetrized rule list agree.                  *)
let SYMMETRIZE_COUNT_MIRROR = prove
 (`!(H:(A)hypermap) z. plain_hypermap H /\ cubic_hypermap H /\ z IN dart H
     ==> !r. ALL (\p. 1 <= size_part p) r
             ==> LENGTH (FILTER (\p. exact_fitp (mirror H)
                                       (face_map H (face_map H (face_map H z)))
                                       p)
                                (symmetrize_drules r)) =
                 LENGTH (FILTER (\p. exact_fitp H (inv_face2 H z) p)
                                (symmetrize_drules r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; symmetrize_drules; FILTER] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`; `h:part`] SYM_FIT_MIRROR1) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`; `h:part`] SYM_FIT_MIRROR2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[FILTER] THENL
   [(* h contains its reflection: h fits in the mirror iff it fits in H.    *)
    SUBGOAL_THEN
     `exact_fitp (mirror H) (face_map H (face_map H (face_map H (z:A)))) h <=>
      exact_fitp H (inv_face2 H z) h`
     (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[EXACT_FIT_PSUBSET; SIZE_SYM_DRULE]; ALL_TAC];
    (* h and its reflection, with swapped fits.                             *)
    ASM_REWRITE_TAC[]] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]));;

(* Gonthier's score1F.                                                       *)
let DSCORE1_MIRROR_FACE = prove
 (`!(H:(A)hypermap) z. plain_hypermap H /\ cubic_hypermap H /\ z IN dart H
     ==> dscore1 (mirror H) (face_map H z) = dscore1 H z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dscore1] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[INV_FACE2_MIRROR_F] THEN REWRITE_TAC[the_drules] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `z:A`] SYMMETRIZE_COUNT_MIRROR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC ALL_SIZE_BASE_DRULES THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let DSCORE2_MIRROR_FACE = prove
 (`!(H:(A)hypermap) y. plain_hypermap H /\ cubic_hypermap H /\ y IN dart H
     ==> dscore2 (mirror H) (face_map H y) = dscore2 H y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dscore2] THEN
  ASM_SIMP_TAC[EDGE_MIRROR_FACE; DSCORE1_MIRROR_FACE; EDGE_MAP_IN_DART]);;

(* Coq DSCORE_MIRROR.                                                        *)
let DSCORE_MIRROR = prove
 (`!(H:(A)hypermap). plain_hypermap H /\ cubic_hypermap H
     ==> !x. x IN dart H ==> dscore (mirror H) x = dscore H x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dscore] THEN
  ASM_SIMP_TAC[ARITY_MIRROR; FACE_MIRROR] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `x:A`;
                `\y. dscore2 (mirror (H:(A)hypermap)) y`] ISUM_FACE_F) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `y:A` THEN REWRITE_TAC[GSYM cface] THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC DSCORE2_MIRROR_FACE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CFT_DART THEN EXISTS_TAC `x:A` THEN
  ASM_REWRITE_TAC[]);;

