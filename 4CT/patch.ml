(* ========================================================================= *)
(* 4CT/patch.ml                                                              *)
(*                                                                           *)
(* patch.v: hypermap patching.  The predicate patch G Gd Gr hd hr bGd bGr    *)
(* says that G is glued from a disk map Gd and a remainder map Gr along a    *)
(* common ring; the genus (GENUS_PATCH), planarity, dart count,              *)
(* bridgelessness (PATCH_BRIDGELESS) and 4-colourability (COLORABLE_PATCH)   *)
(* of G are expressed in terms of those of Gd and Gr.                        *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/color.ml";;
needs "4CT/coloring.ml";;
needs "4CT/walkup.ml";;
needs "4CT/jordan.ml";;
needs "4CT/kempe.ml";;

(* ------------------------------------------------------------------------- *)
(* The patch predicate: hd : Gd -> G and hr : Gr -> G are injections whose   *)
(* images cover G and meet exactly on the ring MAP hd bGd = REVERSE(MAP hr   *)
(* bGr); bGd is a simple edge cycle of Gd, bGr a duplicate-free node cycle   *)
(* of Gr; hd preserves node links, and edge links off bGd; hr preserves edge *)
(* links, and node links off bGr.                                            *)
(* ------------------------------------------------------------------------- *)

let patch = new_definition
  `patch (G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap)
         (hd:A->B) (hr:E->B) (bGd:(A)list) (bGr:(E)list) <=>
   INJ hd (dart Gd) (dart G) /\
   INJ hr (dart Gr) (dart G) /\
   scycle Gd (\x y. edge_map Gd x = y) bGd /\
   (list_cycle (\x y. node_map Gr x = y) bGr /\
    PAIRWISE (\x y:E. ~(x = y)) bGr) /\
   MAP hr bGr = REVERSE (MAP hd bGd) /\
   (!x:B. x IN dart G ==>
        (x IN IMAGE hr (dart Gr) <=>
         ~(x IN IMAGE hd (dart Gd)) \/ MEM x (MAP hd bGd))) /\
   (!x:A. x IN dart Gd /\ ~MEM x bGd
        ==> hd(edge_map Gd x) = edge_map G (hd x)) /\
   (!x:A. x IN dart Gd ==> hd(node_map Gd x) = node_map G (hd x)) /\
   (!x:E. x IN dart Gr ==> hr(edge_map Gr x) = edge_map G (hr x)) /\
   (!x:E. x IN dart Gr /\ ~MEM x bGr
        ==> hr(node_map Gr x) = node_map G (hr x))`;;

(* ------------------------------------------------------------------------- *)
(* Generic facts: face steps, induction along gcomp, orbits in a component.  *)
(* ------------------------------------------------------------------------- *)

let CFACE_FACE_MAP_L = prove
 (`!H:(A)hypermap x. cface H (face_map H x) x`,
  MESON_TAC[CFT_FACE; CFACE_SYM_GEN]);;

let GCOMP_INDUCT = prove
 (`!(H:(A)hypermap) P x.
     P x /\ (!y z. P y /\ glink H y z ==> P z)
     ==> !y. gcomp H x y ==> P y`,
  MESON_TAC[GCOMP_GLINK_INDUCT]);;

let GCOMP_ITER = prove
 (`!(H:(A)hypermap) g k a. (!y. glink H y (g y)) ==> gcomp H a (ITER k g a)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_MESON_TAC[ITER; GCOMP_REFL; GCOMP_TRANS; GCOMP_GLINK]);;

let CFACE_IMP_GCOMP = prove
 (`!H:(A)hypermap x y. cface H x y ==> gcomp H x y`,
  REWRITE_TAC[cface; face; orbit_map; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GCOMP_ITER THEN REWRITE_TAC[glink]);;

(* The node analogue of GCOMP_EDGE_ORBIT (walkup.ml).                        *)

let GCOMP_NODE_ORBIT = prove
 (`!(H:(A)hypermap) a b. b IN orbit_map (node_map H) a ==> gcomp H a b`,
  REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GCOMP_ITER THEN REWRITE_TAC[glink]);;

(* ------------------------------------------------------------------------- *)
(* Counting orbits and components: splitting over a closed subset, and       *)
(* transfer along a map that respects the class relation (Gonthier's         *)
(* adjunction_n_comp / n_compC).                                             *)
(* ------------------------------------------------------------------------- *)

let ORBIT_IN_CLOSED = prove
 (`!f (t:A->bool) x.
     (!y. y IN t ==> f y IN t) /\ x IN t ==> orbit_map f x SUBSET t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; orbit_map; IN_ELIM_THM] THEN
  X_GEN_TAC `z:A` THEN DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER]);;

(* A set closed under a permutation of a finite set is closed under its      *)
(* inverse.                                                                  *)

let CLOSED_INVERSE_STEP = prove
 (`!(f:A->A) s t x.
     FINITE s /\ f permutes s /\ x IN s /\ (!y. t y ==> t (f y)) /\ t (f x)
     ==> t x`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `(x:A) IN orbit_map f (f x)` MP_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_SYM THEN EXISTS_TAC `s:A->bool` THEN
    ASM_MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL];
    REWRITE_TAC[ORBIT_MAP_ITER] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN ASM_SIMP_TAC[ITER]]);;

let IMAGE_ORBIT_INTERTWINE = prove
 (`!f g (s:A->bool) (h:A->B).
     (!y. y IN s ==> f y IN s) /\
     (!x. x IN s ==> h(f x) = g(h x))
     ==> !x. x IN s ==> IMAGE h (orbit_map f x) = orbit_map g (h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n x. x IN s ==> (h:A->B)(ITER n f x) = ITER n g (h x)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ITER_INTERTWINE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; orbit_map; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let SET_OF_ORBITS_SPLIT_UNION = prove
 (`!f (s:A->bool) t.
     FINITE s /\ f permutes s /\ t SUBSET s /\ (!y. y IN t ==> f y IN t)
     ==> set_of_orbits s f =
         set_of_orbits t f UNION set_of_orbits (s DIFF t) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_OF_ORBITS_IMAGE] THEN
  ASM SET_TAC[]);;

let SET_OF_ORBITS_SPLIT_DISJOINT = prove
 (`!f (s:A->bool) t.
     FINITE s /\ f permutes s /\ t SUBSET s /\ (!y. y IN t ==> f y IN t)
     ==> set_of_orbits t f INTER set_of_orbits (s DIFF t) f = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_OF_ORBITS_IMAGE] THEN
  SUBGOAL_THEN `!x. x IN t ==> orbit_map f x SUBSET (t:A->bool)` MP_TAC THENL
   [ASM_MESON_TAC[ORBIT_IN_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPEC `f:A->A` IN_ORBIT_MAP_REFL) THEN SET_TAC[]);;

let CARD_ORBITS_SPLIT = prove
 (`!f (s:A->bool) t.
     FINITE s /\ f permutes s /\ t SUBSET s /\ (!y. y IN t ==> f y IN t)
     ==> CARD(set_of_orbits s f) =
         CARD(set_of_orbits t f) + CARD(set_of_orbits (s DIFF t) f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `t:A->bool`]
    SET_OF_ORBITS_SPLIT_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CARD_UNION THEN
  ASM_SIMP_TAC[SET_OF_ORBITS_SPLIT_DISJOINT] THEN
  ASM_MESON_TAC[FINITE_SET_OF_ORBITS; FINITE_SUBSET; FINITE_DIFF]);;

let CARD_IMAGE_SPLIT = prove
 (`!(cl:A->B) s t.
     FINITE s /\ t SUBSET s /\
     (!x y. x IN t /\ y IN s /\ cl x = cl y ==> y IN t)
     ==> CARD(IMAGE cl s) = CARD(IMAGE cl t) + CARD(IMAGE cl (s DIFF t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (cl:A->B) s = IMAGE cl t UNION IMAGE cl (s DIFF t)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_UNION THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DIFF] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET]; ASM SET_TAC[]]);;

let CARD_IMAGE_REL = prove
 (`!(cl:B->C) (cl':A->D) (s:A->bool) (t:B->bool) (h:A->B).
     FINITE s /\ (!x. x IN s ==> h x IN t) /\
     (!z. z IN t ==> ?x. x IN s /\ cl z = cl(h x)) /\
     (!x y. x IN s /\ y IN s ==> (cl' x = cl' y <=> cl(h x) = cl(h y)))
     ==> CARD(IMAGE cl t) = CARD(IMAGE cl' s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (cl:B->C) t = IMAGE (\x. cl((h:A->B) x)) s`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC CARD_IMAGE_KERNEL THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let CARD_ORBITS_REL = prove
 (`!(f:B->B) (g:A->A) (s:A->bool) (t:B->bool) (h:A->B).
     FINITE s /\ (!x. x IN s ==> h x IN t) /\
     (!z. z IN t ==> ?x. x IN s /\ orbit_map f z = orbit_map f (h x)) /\
     (!x y. x IN s /\ y IN s
            ==> (orbit_map g x = orbit_map g y <=>
                 orbit_map f (h x) = orbit_map f (h y)))
     ==> CARD(set_of_orbits t f) = CARD(set_of_orbits s g)`,
  REWRITE_TAC[SET_OF_ORBITS_IMAGE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CARD_IMAGE_REL THEN EXISTS_TAC `h:A->B` THEN
  ASM_REWRITE_TAC[]);;

let CARD_ORBITS_INTERTWINE = prove
 (`!(f:B->B) (g:A->A) (s:A->bool) (h:A->B).
     FINITE s /\ (!y. y IN s ==> g y IN s) /\
     (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y) /\
     (!x. x IN s ==> h(g x) = f(h x))
     ==> CARD(set_of_orbits (IMAGE h s) f) = CARD(set_of_orbits s g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN s /\ y IN s ==> ((h:A->B) x = h y <=> x = y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!x. x IN s ==> orbit_map f (h x) = IMAGE (h:A->B) (orbit_map g x)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    MATCH_MP_TAC IMAGE_ORBIT_INTERTWINE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_ORBITS_REL THEN EXISTS_TAC `h:A->B` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC INJ_ON_IMAGE_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `s:A->bool`] THEN
  ASM_SIMP_TAC[ORBIT_IN_CLOSED]);;

let OUTER_CLOSED = prove
 (`!f (s:A->bool) c.
     FINITE s /\ f permutes s /\ c SUBSET s
     ==> (!y. y IN {x | x IN s /\ ?z. z IN c /\ x IN orbit_map f z}
              ==> f y IN {x | x IN s /\ ?z. z IN c /\ x IN orbit_map f z})`,
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    EXISTS_TAC `z:A` THEN ASM_SIMP_TAC[ORBIT_MAP_STEP]]);;

(* ------------------------------------------------------------------------- *)
(* The components of the patch predicate.                                    *)
(* ------------------------------------------------------------------------- *)

let PATCH_INJ_HD = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr ==> INJ hd (dart Gd) (dart G)`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_INJ_HR = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr ==> INJ hr (dart Gr) (dart G)`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_CYCLE_D = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> scycle Gd (\x y. edge_map Gd x = y) bGd`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_CYCLE_R = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) hr bGd bGr
   ==> list_cycle (\x y. node_map Gr x = y) bGr /\
       PAIRWISE (\x y:E. ~(x = y)) bGr`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_MAP_RING_R = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> MAP hr bGr = REVERSE (MAP hd bGd)`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_CODOM_R = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> (!x:B. x IN dart G ==>
        (x IN IMAGE hr (dart Gr) <=>
         ~(x IN IMAGE hd (dart Gd)) \/ MEM x (MAP hd bGd)))`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_EDGE_D = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> (!x:A. x IN dart Gd /\ ~MEM x bGd
        ==> hd(edge_map Gd x) = edge_map G (hd x))`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_NODE_D = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> (!x:A. x IN dart Gd ==> hd(node_map Gd x) = node_map G (hd x))`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_EDGE_R = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) hr bGd bGr
   ==> (!x:E. x IN dart Gr ==> hr(edge_map Gr x) = edge_map G (hr x))`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

let PATCH_NODE_R = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) hr bGd bGr
   ==> (!x:E. x IN dart Gr /\ ~MEM x bGr
        ==> hr(node_map Gr x) = node_map G (hr x))`,
  REWRITE_TAC[patch] THEN SIMP_TAC[]);;

(* Instantiate the seven patch variables of a lemma, then further terms.     *)

let PSPECL tms th =
  ISPECL ([`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(E)hypermap`; `hd:A->B`;
           `hr:E->B`; `bGd:(A)list`; `bGr:(E)list`] @ tms) th;;

let PATCH_HD_IN_DART = prove
 (`!G Gd Gr hd hr bGd bGr xd.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ xd IN dart Gd
     ==> hd xd IN dart G`,
  MESON_TAC[PATCH_INJ_HD; INJ]);;

let PATCH_HR_IN_DART = prove
 (`!G Gd Gr hd hr bGd bGr xr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ xr IN dart Gr
     ==> hr xr IN dart G`,
  MESON_TAC[PATCH_INJ_HR; INJ]);;

let PATCH_COVER = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> IMAGE hd (dart Gd) UNION IMAGE hr (dart Gr) = dart G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION] THEN
  X_GEN_TAC `x:B` THEN EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    ASM_MESON_TAC[PATCH_HD_IN_DART; PATCH_HR_IN_DART];
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:B` o MATCH_MP PATCH_CODOM_R) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The borders: duplicate-free cycles of darts, matched in reverse order.    *)
(* ------------------------------------------------------------------------- *)

let PATCH_PAIRWISE_D = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> PAIRWISE (\x y:A. ~(x = y)) bGd`,
  MESON_TAC[PATCH_CYCLE_D; SCYCLE_SIMPLE; FACE_SIMPLE_PAIRWISE_GEN]);;

let PATCH_LENGTH_R = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> LENGTH bGr = LENGTH bGd`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:(B)list->num` o
              MATCH_MP PATCH_MAP_RING_R) THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_REVERSE]);;

let LIST_PATH_EL_STEP = prove
 (`!(f:A->A) r a i. list_path (\x y. f x = y) a r /\ SUC i < LENGTH r
     ==> f(EL i r) = EL (SUC i) r`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `i:num`] THEN
  REWRITE_TAC[LENGTH; LT_SUC; list_path] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `j:num` SUBST1_TAC)
    (SPEC `i:num` num_CASES) THEN
  ONCE_REWRITE_TAC[EL] THEN REWRITE_TAC[HD; TL] THENL
   [POP_ASSUM(K ALL_TAC) THEN SPEC_TAC(`t:(A)list`,`t:(A)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT; list_path; EL; HD] THEN
    MESON_TAC[];
    ASM_MESON_TAC[]]);;

let LIST_CYCLE_EL = prove
 (`!(f:A->A) r i. list_cycle (\x y. f x = y) r /\ i < LENGTH r
     ==> f(EL i r) = EL ((i + 1) MOD LENGTH r) r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_cycle] THEN STRIP_TAC THEN
  ASM_CASES_TAC `SUC i < LENGTH(r:A list)` THENL
   [REWRITE_TAC[GSYM ADD1] THEN ASM_SIMP_TAC[MOD_LT] THEN
    ASM_MESON_TAC[LIST_PATH_EL_STEP];
    SUBGOAL_THEN `i = LENGTH(r:A list) - 1` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(LENGTH(r:A list) - 1 + 1) MOD LENGTH r = 0` SUBST1_TAC THENL
     [SUBGOAL_THEN `LENGTH(r:A list) - 1 + 1 = LENGTH r` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[MOD_REFL]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM LAST_EL] THEN
    UNDISCH_TAC `list_path (\x y:A. f x = y) (LAST r) r` THEN
    UNDISCH_TAC `~(r:A list = [])` THEN
    SPEC_TAC(`r:A list`,`r:A list`) THEN LIST_INDUCT_TAC THEN
    SIMP_TAC[NOT_CONS_NIL; EL; HD; list_path]]);;

let PATCH_BGRP = prove
 (`!G Gd Gr (hd:A->B) (hr:E->B) bGd bGr xr.
     patch G Gd Gr hd hr bGd bGr /\ MEM xr bGr
     ==> (?xd. MEM xd bGd /\ hd xd = hr(node_map Gr xr) /\
               hd(edge_map Gd xd) = hr xr)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_MAP_RING_R) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_LENGTH_R) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP PATCH_CYCLE_R) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_CYCLE o MATCH_MP PATCH_CYCLE_D) THEN
  ABBREV_TAC `n = LENGTH(bGd:(A)list)` THEN
  SUBGOAL_THEN
   `!j. j < n ==> (hr:E->B)(EL j bGr) = (hd:A->B)(EL (n - 1 - j) bGd)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `EL j:(B)list->B`) THEN
    ASM_SIMP_TAC[EL_MAP; EL_REVERSE; LENGTH_MAP;
                 ARITH_RULE `j < n ==> n - 1 - j < n`];
    ALL_TAC] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN `(i + 1) MOD n < n /\ ~(n = 0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `EL (n - 1 - (i + 1) MOD n) (bGd:(A)list)` THEN
  MP_TAC(ISPECL [`node_map (Gr:(E)hypermap)`; `bGr:(E)list`; `i:num`]
    LIST_CYCLE_EL) THEN
  MP_TAC(ISPECL [`edge_map (Gd:(A)hypermap)`; `bGd:(A)list`;
                 `n - 1 - (i + 1) MOD n`] LIST_CYCLE_EL) THEN
  ASM_SIMP_TAC[MOD_CYCLE_REVERSE; ARITH_RULE `j < n ==> n - 1 - j < n`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `n - 1 - (i + 1) MOD n` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MOD_ADD_NEQ = prove
 (`!n i k. 0 < k /\ k < n /\ i < n ==> ~((i + k) MOD n = i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `k:num`; `n:num`] MOD_ADD_CASES) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let LIST_CYCLE_IN_DOMAIN = prove
 (`!(f:A->A) s r.
     f permutes s /\ list_cycle (\x y. f x = y) r /\
     PAIRWISE (\x y. ~(x = y)) r /\ 2 <= LENGTH r
     ==> ALL (\z. z IN s) r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `r:(A)list`; `i:num`] LIST_CYCLE_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:(A)list`; `(i + 1) MOD LENGTH(r:(A)list)`; `i:num`]
    EL_PAIRWISE_INJ) THEN
  ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  ASM_MESON_TAC[PERMUTES_FIX_OUTSIDE; MOD_ADD_NEQ;
                ARITH_RULE `0 < 1 /\ (2 <= n ==> 1 < n)`]);;

let PATCH_BGD_IN_DART = prove
 (`!G Gd Gr (hd:A->B) (hr:E->B) bGd bGr.
     patch G Gd Gr hd hr bGd bGr /\ 2 <= LENGTH bGd
     ==> ALL (\z. z IN dart Gd) bGd`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `edge_map(Gd:(A)hypermap)` LIST_CYCLE_IN_DOMAIN) THEN
  ASM_REWRITE_TAC[EDGE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[PATCH_CYCLE_D; SCYCLE_CYCLE; PATCH_PAIRWISE_D]);;

let PATCH_BGR_IN_DART = prove
 (`!G Gd Gr (hd:A->B) (hr:E->B) bGd bGr.
     patch G Gd Gr hd hr bGd bGr /\ 2 <= LENGTH bGr
     ==> ALL (\z. z IN dart Gr) bGr`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `node_map(Gr:(E)hypermap)` LIST_CYCLE_IN_DOMAIN) THEN
  ASM_REWRITE_TAC[NODE_MAP_PERMUTES] THEN ASM_MESON_TAC[PATCH_CYCLE_R]);;

let PATCH_BGD_DART = prove
 (`!G Gd Gr (hd:A->B) (hr:E->B) bGd bGr x.
     patch G Gd Gr hd hr bGd bGr /\ 2 <= LENGTH bGd /\ MEM x bGd
     ==> x IN dart Gd`,
  MESON_TAC[REWRITE_RULE[GSYM ALL_MEM] PATCH_BGD_IN_DART]);;

let PATCH_BGR_DART = prove
 (`!G Gd Gr (hd:A->B) (hr:E->B) bGd bGr x.
     patch G Gd Gr hd hr bGd bGr /\ 2 <= LENGTH bGd /\ MEM x bGr
     ==> x IN dart Gr`,
  MESON_TAC[REWRITE_RULE[GSYM ALL_MEM] PATCH_BGR_IN_DART; PATCH_LENGTH_R]);;

let PATCH_HD_INJ = prove
 (`!G Gd Gr hd hr bGd bGr x y.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\
     x IN dart Gd /\ y IN dart Gd /\ hd x = hd y
     ==> x = y`,
  MESON_TAC[PATCH_INJ_HD; INJ]);;

let PATCH_HR_INJ = prove
 (`!G Gd Gr hd hr bGd bGr x y.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\
     x IN dart Gr /\ y IN dart Gr /\ hr x = hr y
     ==> x = y`,
  MESON_TAC[PATCH_INJ_HR; INJ]);;

let PATCH_BGD_HD_IN_IMAGE = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\ MEM x bGd
     ==> hd x IN IMAGE hr (dart Gr)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM ((hd:A->B) x) (REVERSE (MAP hd bGd))` MP_TAC THENL
   [ASM_MESON_TAC[MEM_MAP; MEM_REVERSE]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP PATCH_MAP_RING_R th)]) THEN
  REWRITE_TAC[MEM_MAP; IN_IMAGE] THEN ASM_MESON_TAC[PATCH_BGR_DART]);;

let PATCH_BGR_HR_IN_IMAGE = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\ MEM x bGr
     ==> hr x IN IMAGE hd (dart Gd)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM ((hr:E->B) x) (MAP hr bGr)` MP_TAC THENL
   [ASM_MESON_TAC[MEM_MAP]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PATCH_MAP_RING_R th]) THEN
  REWRITE_TAC[MEM_REVERSE; MEM_MAP; IN_IMAGE] THEN
  ASM_MESON_TAC[PATCH_BGD_DART]);;

let PATCH_HD_IN_IMAGE_HR = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gd
     ==> (hd x IN IMAGE hr (dart Gr) <=> MEM x bGd)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[PATCH_BGD_HD_IN_IMAGE]] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(hd:A->B) x` o MATCH_MP PATCH_CODOM_R) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PATCH_HD_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `(hd:A->B) x IN IMAGE hd (dart Gd)`
    (fun th -> ASM_REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[PATCH_BGD_DART; PATCH_HD_INJ]);;

let PATCH_HR_IN_IMAGE_HD = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr
     ==> (hr x IN IMAGE hd (dart Gd) <=> MEM x bGr)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[PATCH_BGR_HR_IN_IMAGE]] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(hr:E->B) x` o MATCH_MP PATCH_CODOM_R) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PATCH_HR_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `(hr:E->B) x IN IMAGE hr (dart Gr)`
    (fun th -> ASM_REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MAP (hd:A->B) bGd = REVERSE(MAP (hr:E->B) bGr)`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[PATCH_MAP_RING_R; REVERSE_REVERSE]; ALL_TAC] THEN
  REWRITE_TAC[MEM_REVERSE; MEM_MAP] THEN
  ASM_MESON_TAC[PATCH_BGR_DART; PATCH_HR_INJ]);;

let PATCH_BGD_ORBIT = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\ MEM x bGd
     ==> !y. MEM y bGd <=> y IN orbit_map (edge_map Gd) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_CYCLE o MATCH_MP PATCH_CYCLE_D) THEN
  MP_TAC(ISPECL [`edge_map(Gd:(A)hypermap)`; `bGd:(A)list`; `x:A`]
    ORBIT_CYCLE_MEM) THEN
  MP_TAC(ISPECL [`edge_map(Gd:(A)hypermap)`; `dart(Gd:(A)hypermap)`;
                 `bGd:(A)list`; `x:A`] LIST_CYCLE_MEM_ORBIT) THEN
  ASM_REWRITE_TAC[EDGE_MAP_PERMUTES; FINITE_DART] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PATCH_BGD_DART]; MESON_TAC[]]);;

let PATCH_BGR_ORBIT = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\ MEM x bGr
     ==> !y. MEM y bGr <=> y IN orbit_map (node_map Gr) x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_ORBIT THEN
  ASM_MESON_TAC[PATCH_CYCLE_R; PATCH_BGR_IN_DART; PATCH_LENGTH_R]);;

let PATCH_BGD_EDGE = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ MEM x bGd
     ==> MEM (edge_map Gd x) bGd`,
  MESON_TAC[PATCH_CYCLE_D; SCYCLE_CYCLE; LIST_CYCLE_F_CLOSED]);;

let PATCH_BGR_NODE = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ MEM x bGr
     ==> MEM (node_map Gr x) bGr`,
  MESON_TAC[PATCH_CYCLE_R; LIST_CYCLE_F_CLOSED]);;

let PATCH_BGD_EDGE_REV = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ x IN dart Gd /\
     MEM (edge_map Gd x) bGd
     ==> MEM x bGd`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`edge_map(Gd:(A)hypermap)`; `dart(Gd:(A)hypermap)`; `\y:A. MEM y bGd`]
   CLOSED_INVERSE_STEP)) THEN
  ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[PATCH_BGD_EDGE]);;

let PATCH_BGR_NODE_REV = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ x IN dart Gr /\
     MEM (node_map Gr x) bGr
     ==> MEM x bGr`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`node_map(Gr:(E)hypermap)`; `dart(Gr:(E)hypermap)`; `\y:E. MEM y bGr`]
   CLOSED_INVERSE_STEP)) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[PATCH_BGR_NODE]);;

(* ------------------------------------------------------------------------- *)
(* hd and hr also preserve face links, except where the face steps onto the  *)
(* border; a face step of Gr onto bGr becomes an edge-face detour in Gd.     *)
(* ------------------------------------------------------------------------- *)

let PATCH_FACE_D = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ x IN dart Gd /\ ~MEM x bGd
     ==> hd(face_map Gd x) = face_map G (hd x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~MEM (node_map Gd (face_map Gd (x:A))) bGd` ASSUME_TAC THENL
   [ASM_MESON_TAC[PATCH_BGD_EDGE; faceK]; ALL_TAC] THEN
  SUBGOAL_THEN `(hd:A->B) x = edge_map G (node_map G (hd (face_map Gd x)))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `node_map Gd (face_map Gd (x:A))` o
                MATCH_MP PATCH_EDGE_D) THEN
    FIRST_ASSUM(MP_TAC o SPEC `face_map Gd (x:A)` o MATCH_MP PATCH_NODE_D) THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; NODE_MAP_IN_DART; faceK];
    REWRITE_TAC[nodeK]]);;

let PATCH_FACE_R = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ x IN dart Gr /\
     ~MEM (face_map Gr x) bGr
     ==> hr(face_map Gr x) = face_map G (hr x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(hr:E->B) x = edge_map G (node_map G (hr (face_map Gr x)))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `node_map Gr (face_map Gr (x:E))` o
                MATCH_MP PATCH_EDGE_R) THEN
    FIRST_ASSUM(MP_TAC o SPEC `face_map Gr (x:E)` o MATCH_MP PATCH_NODE_R) THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; NODE_MAP_IN_DART; faceK];
    REWRITE_TAC[nodeK]]);;

let PATCH_HR_FACE_BORDER = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ MEM (face_map Gr x) bGr
     ==> ?xd. MEM xd bGd /\ hr x = edge_map G (hd xd) /\
              hr(face_map Gr x) = hd(edge_map Gd xd) /\
              face_map G (hr x) = hd(face_map Gd (edge_map Gd xd))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(PSPECL [`face_map Gr (x:E)`] PATCH_BGRP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xd:A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC))) THEN
  EXISTS_TAC `xd:A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `xd IN dart(Gd:(A)hypermap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PATCH_BGD_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `(hr:E->B) x = edge_map G (hd (xd:A))`
    (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(MP_TAC o SPEC `node_map Gr (face_map Gr (x:E))` o
                MATCH_MP PATCH_EDGE_R) THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; NODE_MAP_IN_DART; faceK];
    ALL_TAC] THEN
  SUBGOAL_THEN `(hd:A->B) xd = node_map G (hd (face_map Gd (edge_map Gd xd)))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `face_map Gd (edge_map Gd (xd:A))` o
                MATCH_MP PATCH_NODE_D) THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; edgeK];
    REWRITE_TAC[nodeK]]);;

(* ------------------------------------------------------------------------- *)
(* Faces: hd preserves cofaciality; hr preserves and reflects it.            *)
(* ------------------------------------------------------------------------- *)

let CFACE_AS_ITER = prove
 (`!H:(A)hypermap x y. cface H x y <=> ?n. y = ITER n (face_map H) x`,
  REWRITE_TAC[cface; face; ORBIT_MAP_ITER]);;

let ITER_FACE_IN_DART = prove
 (`!H:(A)hypermap n x. x IN dart H ==> ITER n (face_map H) x IN dart H`,
  MESON_TAC[ITER_PERMUTES_IN; FACE_MAP_PERMUTES]);;

let PATCH_FACE_CHAIN_UPTO = prove
 (`!G Gd Gr hd hr bGd bGr xd n.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ xd IN dart Gd /\
     (!k. k < n ==> ~MEM (ITER k (face_map Gd) xd) bGd)
     ==> ITER n (face_map G) (hd xd) = hd (ITER n (face_map Gd) xd)`,
  REPLICATE_TAC 8 GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `ITER n (face_map G) ((hd:A->B) xd) = hd (ITER n (face_map Gd) xd)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `k < n ==> k < SUC n`];
    ASM_MESON_TAC[PATCH_FACE_D; ITER_FACE_IN_DART; ARITH_RULE `n < SUC n`]]);;

let PATCH_FACE_CHAIN_HD = prove
 (`!G Gd Gr hd hr bGd bGr xd.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ xd IN dart Gd /\
     (!k. ~MEM (ITER k (face_map Gd) xd) bGd)
     ==> !n. ITER n (face_map G) (hd xd) = hd (ITER n (face_map Gd) xd)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATCH_FACE_CHAIN_UPTO THEN
  ASM_MESON_TAC[]);;

let PATCH_CFACE_HD_STEP = prove
 (`!G Gd Gr hd hr bGd bGr xd.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ xd IN dart Gd
     ==> cface G (hd xd) (hd (face_map Gd xd))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `MEM (xd:A) bGd` THENL
   [ALL_TAC; ASM_MESON_TAC[PATCH_FACE_D; CFT_FACE]] THEN
  ABBREV_TAC `d = orbit_size (face_map Gd) (xd:A)` THEN
  SUBGOAL_THEN
   `0 < d /\ ITER d (face_map Gd) (xd:A) = xd /\
    !k. 0 < k /\ k < d ==> ~(ITER k (face_map Gd) xd = xd)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    ASM_MESON_TAC[ORBIT_SIZE_POS; ITER_ORBIT_SIZE; ORBIT_SIZE_DIVIDES;
                  NOT_DIVIDES_LT; FINITE_DART; FACE_MAP_PERMUTES];
    ALL_TAC] THEN
  SUBGOAL_THEN `ITER (d - 1) (face_map G) ((hd:A->B) (face_map Gd xd)) = hd xd`
    (fun th -> MESON_TAC[th; CFT_ITER; CFACE_SYM_GEN]) THEN
  MP_TAC(PSPECL [`face_map Gd (xd:A)`; `d - 1`] PATCH_FACE_CHAIN_UPTO) THEN
  ASM_SIMP_TAC[FACE_MAP_IN_DART; ITER_SHIFT;
               ARITH_RULE `0 < d ==> SUC(d - 1) = d`] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_MESON_TAC[CFT_FACE_SIMPLE; CFT_ITER; PATCH_CYCLE_D;
                SCYCLE_SIMPLE;
                ARITH_RULE `k < d - 1 ==> 0 < SUC k /\ SUC k < d`]);;

let PATCH_CFACE_HD = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
   ==> (!x y:A. x IN dart Gd /\ cface Gd x y ==> cface G (hd x) (hd y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `n:num` SUBST1_TAC o REWRITE_RULE[CFACE_AS_ITER])) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ITER; CFACE_REFL] THEN
  ASM_MESON_TAC[CFT_TRANS; PATCH_CFACE_HD_STEP; ITER_FACE_IN_DART]);;

let PATCH_CFACE_HR_STEP = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr
     ==> cface G (hr x) (hr (face_map Gr x))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `MEM (face_map Gr (x:E)) bGr` THENL
   [ALL_TAC; ASM_MESON_TAC[PATCH_FACE_R; CFT_FACE]] THEN
  MP_TAC(PSPECL [`x:E`] PATCH_HR_FACE_BORDER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xd:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`edge_map Gd (xd:A)`;
    `face_map Gd (edge_map Gd (xd:A))`] o MATCH_MP PATCH_CFACE_HD) THEN
  MP_TAC(PSPECL [`xd:A`] PATCH_BGD_DART) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[EDGE_MAP_IN_DART; CFT_FACE] THEN CFACE_TAC[]);;

let PATCH_CFACE_HR_FWD = prove
 (`!G Gd Gr hd hr bGd bGr x y.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ cface Gr x y
     ==> cface G (hr x) (hr y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPLICATE_TAC 3 DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CFACE_AS_ITER] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ITER; CFACE_REFL] THEN
  ASM_MESON_TAC[CFT_TRANS; PATCH_CFACE_HR_STEP; ITER_FACE_IN_DART]);;

(* The invariant for pulling a G-face path from hr x back to Gr: the current *)
(* dart is either hr x' for x' cofacial with x, or lies in the disk, in the  *)
(* Gd-face of a border dart yd glued to hr x'.                               *)

let hr_face_inv = new_definition
 `hr_face_inv (G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap)
              (hd:A->B) (hr:E->B) bGd x z <=>
    z IN dart G /\
    ?x'. x' IN dart Gr /\ cface Gr x x' /\
         (z = hr x' \/
          ?xd yd. xd IN dart Gd /\ ~MEM xd bGd /\ z = hd xd /\
                  MEM yd bGd /\ hd yd = hr x' /\ cface Gd yd xd)`;;

let PATCH_HR_FACE_INV_STEP = prove
 (`!G Gd Gr hd hr bGd bGr x z.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ hr_face_inv G Gd Gr hd hr bGd x z
     ==> hr_face_inv G Gd Gr hd hr bGd x (face_map G z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hr_face_inv; IMP_CONJ] THEN
  REPLICATE_TAC 4 DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x':E` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ASM_SIMP_TAC[FACE_MAP_IN_DART] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCYCLE_SIMPLE o
              MATCH_MP PATCH_CYCLE_D) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
   [ASM_CASES_TAC `MEM (face_map Gr (x':E)) bGr` THENL
     [ALL_TAC;
      EXISTS_TAC `face_map Gr (x':E)` THEN
      ASM_MESON_TAC[FACE_MAP_IN_DART; CFT_TRANS; CFT_FACE;
                    PATCH_FACE_R]] THEN
    MP_TAC(PSPECL [`x':E`] PATCH_HR_FACE_BORDER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `xd:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `face_map Gr (x':E)` THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART] THEN CONJ_TAC THENL
     [CFACE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `MEM (face_map Gd (edge_map Gd (xd:A))) bGd` THENL
     [DISJ1_TAC THEN
      ASM_MESON_TAC[CFT_FACE_SIMPLE; CFT_FACE; PATCH_BGD_EDGE];
      DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`face_map Gd (edge_map Gd (xd:A))`;
                            `edge_map Gd (xd:A)`] THEN
      ASM_MESON_TAC[PATCH_BGD_DART; PATCH_BGD_EDGE; FACE_MAP_IN_DART;
                    EDGE_MAP_IN_DART; CFT_FACE]];
    DISCH_THEN(X_CHOOSE_THEN `xd:A` (X_CHOOSE_THEN `yd:A`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))))) THEN
    EXISTS_TAC `x':E` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `face_map G ((hd:A->B) xd) = hd (face_map Gd xd)`
    SUBST1_TAC THENL [ASM_MESON_TAC[PATCH_FACE_D]; ALL_TAC] THEN
    SUBGOAL_THEN `cface Gd yd (face_map Gd (xd:A))` ASSUME_TAC THENL
     [CFACE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `MEM (face_map Gd (xd:A)) bGd` THENL
     [DISJ1_TAC THEN ASM_MESON_TAC[CFT_FACE_SIMPLE];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`face_map Gd (xd:A)`; `yd:A`] THEN
      ASM_SIMP_TAC[FACE_MAP_IN_DART]]]);;

let PATCH_CFACE_HR_REV = prove
 (`!G Gd Gr hd hr bGd bGr x y.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ y IN dart Gr /\ cface G (hr x) (hr y)
     ==> cface Gr x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPLICATE_TAC 4 DISCH_TAC THEN
  REWRITE_TAC[CFACE_AS_ITER] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  SUBGOAL_THEN
   `hr_face_inv G Gd Gr (hd:A->B) (hr:E->B) bGd x (ITER n (face_map G) (hr x))`
  MP_TAC THENL
   [SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
     [REWRITE_TAC[hr_face_inv] THEN
      ASM_MESON_TAC[PATCH_HR_IN_DART; CFACE_REFL];
      MP_TAC(PSPECL [`x:E`; `ITER n (face_map G) ((hr:E->B) x)`]
                    PATCH_HR_FACE_INV_STEP) THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hr_face_inv]) THEN
    REWRITE_TAC[GSYM CFACE_AS_ITER] THEN
    ASM_MESON_TAC[PATCH_HR_INJ; PATCH_HD_IN_IMAGE_HR; IN_IMAGE]]);;

let PATCH_CFACE_HR = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
   ==> (!x y:E. x IN dart Gr /\ y IN dart Gr
                ==> (cface Gr x y <=> cface G (hr x) (hr y)))`,
  MESON_TAC[PATCH_CFACE_HR_FWD; PATCH_CFACE_HR_REV]);;

(* ------------------------------------------------------------------------- *)
(* Bridgelessness descends to the two parts.                                 *)
(* ------------------------------------------------------------------------- *)

let PATCH_BRIDGELESS = prove
 (`!G Gd Gr (hd:A->B) (hr:E->B) bGd bGr.
   patch G Gd Gr hd hr bGd bGr /\ bridgeless G /\ 2 <= LENGTH bGd
   ==> bridgeless Gd /\ bridgeless Gr`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bridgeless] THEN STRIP_TAC THEN
  CONJ_TAC THEN GEN_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(PSPECL [`x:A`] PATCH_HD_IN_DART) THEN
    FIRST_ASSUM(MP_TAC o SPEC `face_map Gd (edge_map Gd (x:A))` o
                MATCH_MP PATCH_NODE_D) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `face_map Gd (edge_map Gd (x:A))`] o
                MATCH_MP PATCH_CFACE_HD) THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; edgeK] THEN
    ANTS_TAC THENL [CFACE_TAC[]; REPEAT DISCH_TAC THEN CFACE_TAC[]];
    ASM_MESON_TAC[PATCH_HR_IN_DART; PATCH_EDGE_R; PATCH_CFACE_HR_FWD;
                  EDGE_MAP_IN_DART]]);;

(* ------------------------------------------------------------------------- *)
(* Counting darts: the two images cover G and meet in the ring.              *)
(* ------------------------------------------------------------------------- *)

let PATCH_IMAGE_HD_SUBSET = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
     ==> IMAGE hd (dart Gd) SUBSET dart G`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[PATCH_HD_IN_DART]);;

let PATCH_IMAGE_HR_SUBSET = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr
     ==> IMAGE hr (dart Gr) SUBSET dart G`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[PATCH_HR_IN_DART]);;

let PATCH_IN_IMAGE_HD = prove
 (`!G Gd Gr hd hr bGd bGr z.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ z IN dart G /\
     ~(z IN IMAGE hr (dart Gr))
     ==> z IN IMAGE hd (dart Gd)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_COVER) THEN
  ASM SET_TAC[]);;

let PATCH_IN_IMAGE_HR = prove
 (`!G Gd Gr hd hr bGd bGr z.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ z IN dart G /\
     ~(z IN IMAGE hd (dart Gd))
     ==> z IN IMAGE hr (dart Gr)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP PATCH_COVER) THEN
  ASM SET_TAC[]);;

let PATCH_RING_INTER = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
   ==> IMAGE hd (dart Gd) INTER IMAGE hr (dart Gr) = set_of_list (MAP hd bGd)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_SET_OF_LIST; MEM_MAP] THEN
  X_GEN_TAC `z:B` THEN EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[PATCH_HD_IN_IMAGE_HR; IN_IMAGE];
    ASM_MESON_TAC[PATCH_BGD_DART; PATCH_BGD_HD_IN_IMAGE; IN_IMAGE]]);;

let CARD_SET_OF_LIST_PAIRWISE = prove
 (`!l:(A)list. PAIRWISE (\x y. ~(x = y)) l ==> CARD(set_of_list l) = LENGTH l`,
  MESON_TAC[HAS_SIZE_SET_OF_LIST; HAS_SIZE]);;

let PATCH_CARD_RING = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
   ==> CARD(set_of_list (MAP hd bGd)) = LENGTH bGd`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (bGd:(A)list) = LENGTH (MAP (hd:A->B) bGd)`
  SUBST1_TAC THENL [REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_SET_OF_LIST_PAIRWISE THEN
  MATCH_MP_TAC PAIRWISE_INJ_MAP THEN
  ASM_MESON_TAC[PATCH_PAIRWISE_D; PATCH_BGD_DART; PATCH_HD_INJ]);;

let CARD_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
   ==> CARD(dart G) + LENGTH bGd = CARD(dart Gd) + CARD(dart Gr)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(PSPECL [] PATCH_COVER) THEN MP_TAC(PSPECL [] PATCH_RING_INTER) THEN
  MP_TAC(PSPECL [] PATCH_CARD_RING) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  SUBGOAL_THEN
   `CARD(IMAGE (hd:A->B) (dart Gd)) = CARD(dart Gd) /\
    CARD(IMAGE (hr:E->B) (dart Gr)) = CARD(dart Gr)`
  (fun th -> REWRITE_TAC[GSYM th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    REWRITE_TAC[FINITE_DART] THEN
    ASM_MESON_TAC[PATCH_HD_INJ; PATCH_HR_INJ];
    MATCH_MP_TAC CARD_UNION_INTER_EQ THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_DART]]);;

(* ------------------------------------------------------------------------- *)
(* Counting nodes and edges: the border is a single node orbit of Gr and a   *)
(* single edge orbit of Gd; the other orbits transfer along hd and hr.       *)
(* ------------------------------------------------------------------------- *)

let PATCH_COMPL_HD = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> dart G DIFF IMAGE hd (dart Gd) =
         IMAGE hr (dart Gr DIFF set_of_list bGr)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF] THEN
  X_GEN_TAC `z:B` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `z IN IMAGE (hr:E->B) (dart Gr)` MP_TAC THENL
     [ASM_MESON_TAC[PATCH_IN_IMAGE_HR]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_HR_IN_IMAGE_HD];
    GEN_REWRITE_TAC LAND_CONV [IN_IMAGE] THEN
    REWRITE_TAC[IN_DIFF; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_HR_IN_IMAGE_HD; PATCH_HR_IN_DART]]);;

let PATCH_COMPL_HR = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> dart G DIFF IMAGE hr (dart Gr) =
         IMAGE hd (dart Gd DIFF set_of_list bGd)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF] THEN
  X_GEN_TAC `z:B` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `z IN IMAGE (hd:A->B) (dart Gd)` MP_TAC THENL
     [ASM_MESON_TAC[PATCH_IN_IMAGE_HD]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_HD_IN_IMAGE_HR];
    GEN_REWRITE_TAC LAND_CONV [IN_IMAGE] THEN
    REWRITE_TAC[IN_DIFF; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_HD_IN_IMAGE_HR; PATCH_HD_IN_DART]]);;

let PATCH_BGR_ORBITS = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> CARD(set_of_orbits (set_of_list bGr) (node_map Gr)) = 1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_SET_OF_ORBITS_1 THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SET_OF_LIST_EQ_EMPTY; LENGTH_EQ_NIL; PATCH_LENGTH_R;
                  ARITH_RULE `2 <= n ==> ~(n = 0)`];
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_BGR_ORBIT]]);;

let PATCH_BGD_ORBITS = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> CARD(set_of_orbits (set_of_list bGd) (edge_map Gd)) = 1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_SET_OF_ORBITS_1 THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SET_OF_LIST_EQ_EMPTY; LENGTH_EQ_NIL;
                  ARITH_RULE `2 <= n ==> ~(n = 0)`];
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_BGD_ORBIT]]);;

let NODES_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> number_of_nodes G + 1 = number_of_nodes Gd + number_of_nodes Gr`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_nodes; node_set] THEN
  MP_TAC(ISPECL [`node_map (G:(B)hypermap)`; `dart(G:(B)hypermap)`;
                 `IMAGE (hd:A->B) (dart Gd)`] CARD_ORBITS_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; IN_IMAGE] THEN
    ASM_MESON_TAC[PATCH_IMAGE_HD_SUBSET; PATCH_NODE_D; NODE_MAP_IN_DART];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`node_map (Gr:(E)hypermap)`; `dart(Gr:(E)hypermap)`;
                 `set_of_list (bGr:(E)list)`] CARD_ORBITS_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES; SUBSET; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_BGR_DART; PATCH_BGR_NODE];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(PSPECL [] PATCH_BGR_ORBITS) THEN MP_TAC(PSPECL [] PATCH_COMPL_HD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `CARD(set_of_orbits (IMAGE (hd:A->B) (dart Gd)) (node_map G)) =
    CARD(set_of_orbits (dart Gd) (node_map Gd)) /\
    CARD(set_of_orbits (IMAGE (hr:E->B) (dart Gr DIFF set_of_list bGr))
                       (node_map G)) =
    CARD(set_of_orbits (dart Gr DIFF set_of_list bGr) (node_map Gr))`
  (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
  CONJ_TAC THEN MATCH_MP_TAC CARD_ORBITS_INTERTWINE THEN
  ASM_SIMP_TAC[FINITE_DIFF; FINITE_DART; IN_DIFF; IN_SET_OF_LIST] THENL
   [ASM_MESON_TAC[NODE_MAP_IN_DART; PATCH_HD_INJ; PATCH_NODE_D];
    ASM_MESON_TAC[PATCH_HR_INJ; PATCH_NODE_R; NODE_MAP_IN_DART;
                  PATCH_BGR_NODE_REV]]);;

let EDGES_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> number_of_edges G + 1 = number_of_edges Gd + number_of_edges Gr`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_edges; edge_set] THEN
  MP_TAC(ISPECL [`edge_map (G:(B)hypermap)`; `dart(G:(B)hypermap)`;
                 `IMAGE (hr:E->B) (dart Gr)`] CARD_ORBITS_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; IN_IMAGE] THEN
    ASM_MESON_TAC[PATCH_IMAGE_HR_SUBSET; PATCH_EDGE_R; EDGE_MAP_IN_DART];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`edge_map (Gd:(A)hypermap)`; `dart(Gd:(A)hypermap)`;
                 `set_of_list (bGd:(A)list)`] CARD_ORBITS_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES; SUBSET; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[PATCH_BGD_DART; PATCH_BGD_EDGE];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(PSPECL [] PATCH_BGD_ORBITS) THEN MP_TAC(PSPECL [] PATCH_COMPL_HR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `CARD(set_of_orbits (IMAGE (hr:E->B) (dart Gr)) (edge_map G)) =
    CARD(set_of_orbits (dart Gr) (edge_map Gr)) /\
    CARD(set_of_orbits (IMAGE (hd:A->B) (dart Gd DIFF set_of_list bGd))
                       (edge_map G)) =
    CARD(set_of_orbits (dart Gd DIFF set_of_list bGd) (edge_map Gd))`
  (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
  CONJ_TAC THEN MATCH_MP_TAC CARD_ORBITS_INTERTWINE THEN
  ASM_SIMP_TAC[FINITE_DIFF; FINITE_DART; IN_DIFF; IN_SET_OF_LIST] THENL
   [ASM_MESON_TAC[EDGE_MAP_IN_DART; PATCH_HR_INJ; PATCH_EDGE_R];
    ASM_MESON_TAC[PATCH_HD_INJ; PATCH_EDGE_D; EDGE_MAP_IN_DART;
                  PATCH_BGD_EDGE_REV]]);;

(* ------------------------------------------------------------------------- *)
(* Counting faces: the faces of G meeting IMAGE hr ("outer") correspond to   *)
(* the faces of Gr; the others to the faces of Gd avoiding the border; and   *)
(* the border darts of Gd lie on LENGTH bGd distinct faces of Gd.            *)
(* ------------------------------------------------------------------------- *)

let ORBIT_EQ_CFACE = prove
 (`!H:(A)hypermap x y.
     x IN dart H /\ y IN dart H
     ==> (orbit_map (face_map H) x = orbit_map (face_map H) y <=>
          cface H x y)`,
  REWRITE_TAC[cface; face] THEN
  MESON_TAC[ORBIT_MAP_EQ; IN_ORBIT_MAP_REFL; FINITE_DART; FACE_MAP_PERMUTES]);;

let OUTER_SUPERSET = prove
 (`!f (s:A->bool) c y.
     y IN c /\ c SUBSET s
     ==> y IN {x | x IN s /\ ?z. z IN c /\ x IN orbit_map f z}`,
  REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN MESON_TAC[IN_ORBIT_MAP_REFL]);;

let PATCH_FACES_OUTER = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> CARD(set_of_orbits
                {x | x IN dart G /\
                     ?z. z IN IMAGE hr (dart Gr) /\
                         x IN orbit_map (face_map G) z}
                (face_map G)) = number_of_faces Gr`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_of_faces; face_set] THEN
  MATCH_MP_TAC CARD_ORBITS_REL THEN EXISTS_TAC `hr:E->B` THEN
  REWRITE_TAC[FINITE_DART; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PATCH_HR_IN_DART; IN_IMAGE; IN_ORBIT_MAP_REFL];
    REWRITE_TAC[IN_IMAGE] THEN
    ASM_MESON_TAC[ORBIT_MAP_EQ; FINITE_DART; FACE_MAP_PERMUTES;
                  PATCH_HR_IN_DART];
    MAP_EVERY X_GEN_TAC [`x:E`; `y:E`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(hr:E->B) x IN dart G /\ hr y IN dart G`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PATCH_HR_IN_DART]; ALL_TAC] THEN
    ASM_SIMP_TAC[ORBIT_EQ_CFACE] THEN
    MP_TAC(PSPECL [] PATCH_CFACE_HR) THEN ASM_SIMP_TAC[]]);;

let PATCH_FBAND_IN_OUTER = prove
 (`!G Gd Gr hd hr bGd bGr xd b.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     xd IN dart Gd /\ MEM b bGd /\ cface Gd xd b
     ==> hd xd IN {x | x IN dart G /\
                       ?z. z IN IMAGE hr (dart Gr) /\
                           x IN orbit_map (face_map G) z}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PATCH_HD_IN_DART]; ALL_TAC] THEN
  EXISTS_TAC `(hd:A->B) b` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PATCH_BGD_HD_IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM face; GSYM cface] THEN
  ASM_MESON_TAC[PATCH_CFACE_HD; CFACE_SYM_GEN]);;

let PATCH_NONFBAND_NOT_OUTER = prove
 (`!G Gd Gr hd hr bGd bGr xd.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     xd IN dart Gd /\
     (!b. MEM b bGd ==> ~cface Gd xd b)
     ==> ~(hd xd IN {x | x IN dart G /\
                         ?z. z IN IMAGE hr (dart Gr) /\
                             x IN orbit_map (face_map G) z})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:B`
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `zr:E` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `!k. ~MEM (ITER k (face_map Gd) (xd:A)) bGd` ASSUME_TAC THENL
   [ASM_MESON_TAC[CFT_ITER]; ALL_TAC] THEN
  SUBGOAL_THEN `z IN orbit_map (face_map G) ((hd:A->B) xd)` MP_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_SYM THEN EXISTS_TAC `dart(G:(B)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
    ASM_MESON_TAC[PATCH_HR_IN_DART];
    ALL_TAC] THEN
  REWRITE_TAC[ORBIT_MAP_ITER] THEN
  MP_TAC(PSPECL [`xd:A`] PATCH_FACE_CHAIN_HD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` ASSUME_TAC) THEN
  MP_TAC(PSPECL [`ITER n (face_map Gd) (xd:A)`] PATCH_HD_IN_IMAGE_HR) THEN
  ASM_SIMP_TAC[ITER_FACE_IN_DART] THEN ASM_MESON_TAC[IN_IMAGE]);;

let PATCH_COMPL_OUTER = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> dart G DIFF
         {x | x IN dart G /\
              ?z. z IN IMAGE hr (dart Gr) /\ x IN orbit_map (face_map G) z} =
         IMAGE hd (dart Gd DIFF
                   {x | x IN dart Gd /\ ?b. MEM b bGd /\ cface Gd x b})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF] THEN
  X_GEN_TAC `z:B` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`face_map (G:(B)hypermap)`; `dart (G:(B)hypermap)`;
                   `IMAGE (hr:E->B) (dart Gr)`; `z:B`] OUTER_SUPERSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `z IN IMAGE (hd:A->B) (dart Gd)` MP_TAC THENL
     [MATCH_MP_TAC(PSPECL [`z:B`] PATCH_IN_IMAGE_HD) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PATCH_IMAGE_HR_SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `xd:A`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    EXISTS_TAC `xd:A` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(PSPECL [`xd:A`; `b:A`] PATCH_FBAND_IN_OUTER) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `xd:A`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
    MP_TAC(PSPECL [`xd:A`] PATCH_NONFBAND_NOT_OUTER) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[PATCH_HD_IN_DART]]);;

let PATCH_FACES_BORDER_COUNT = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> CARD(set_of_orbits {x | x IN dart Gd /\ ?b. MEM b bGd /\ cface Gd x b}
                            (face_map Gd)) = LENGTH bGd`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `set_of_orbits {x | x IN dart Gd /\ ?b. MEM b bGd /\ cface Gd x b}
                  (face_map Gd) =
    IMAGE (orbit_map (face_map Gd)) (set_of_list (bGd:(A)list))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SET_OF_ORBITS_IMAGE; EXTENSION; IN_IMAGE; IN_ELIM_THM;
                IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[ORBIT_EQ_CFACE; PATCH_BGD_DART; CFACE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(set_of_list (bGd:(A)list)) = LENGTH bGd`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
   [ASM_MESON_TAC[CARD_SET_OF_LIST_PAIRWISE; PATCH_PAIRWISE_D]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  REWRITE_TAC[FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  ASM_MESON_TAC[ORBIT_EQ_CFACE; PATCH_BGD_DART; CFT_FACE_SIMPLE;
                PATCH_CYCLE_D; SCYCLE_SIMPLE]);;

let FACES_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> number_of_faces G + LENGTH bGd =
         number_of_faces Gd + number_of_faces Gr`,
  REPEAT STRIP_TAC THEN
  MP_TAC(PSPECL [] PATCH_FACES_OUTER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[number_of_faces; face_set] THEN
  MP_TAC(ISPECL [`face_map (G:(B)hypermap)`; `dart(G:(B)hypermap)`;
    `{x | x IN dart G /\
          ?z. z IN IMAGE (hr:E->B) (dart Gr) /\
              x IN orbit_map (face_map G) z}`]
    CARD_ORBITS_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC OUTER_CLOSED THEN
      ASM_MESON_TAC[FINITE_DART; FACE_MAP_PERMUTES; PATCH_IMAGE_HR_SUBSET]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`face_map (Gd:(A)hypermap)`; `dart(Gd:(A)hypermap)`;
    `{x | x IN dart (Gd:(A)hypermap) /\ ?b. MEM b bGd /\ cface Gd x b}`]
    CARD_ORBITS_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[FACE_MAP_IN_DART; CFACE_LEFT_FACE];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(PSPECL [] PATCH_FACES_BORDER_COUNT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(PSPECL [] PATCH_COMPL_OUTER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `CARD(set_of_orbits
      (IMAGE (hd:A->B)
         (dart Gd DIFF {x | x IN dart Gd /\ ?b. MEM b bGd /\ cface Gd x b}))
      (face_map G)) =
    CARD(set_of_orbits
      (dart Gd DIFF {x | x IN dart Gd /\ ?b. MEM b bGd /\ cface Gd x b})
      (face_map Gd))`
  SUBST1_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  MATCH_MP_TAC CARD_ORBITS_INTERTWINE THEN
  ASM_SIMP_TAC[FINITE_DIFF; FINITE_DART; IN_DIFF; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[FACE_MAP_IN_DART; CFACE_LEFT_FACE];
    ASM_MESON_TAC[PATCH_HD_INJ];
    ASM_MESON_TAC[PATCH_FACE_D; CFACE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Counting components: the components of G meeting IMAGE hr correspond to   *)
(* those of Gr, the others to the components of Gd avoiding the border, and  *)
(* the border lies in a single component of Gd.                              *)
(* ------------------------------------------------------------------------- *)

let PATCH_GCOMP_HD_EDGE = prove
 (`!G Gd Gr hd hr bGd bGr y.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ y IN dart Gd
     ==> gcomp G (hd y) (hd (edge_map Gd y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(hd:A->B) y = node_map G (hd (face_map Gd (edge_map Gd y)))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `face_map Gd (edge_map Gd (y:A))` o
                MATCH_MP PATCH_NODE_D) THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; edgeK];
    ALL_TAC] THEN
  MATCH_MP_TAC GCOMP_TRANS THEN
  EXISTS_TAC `(hd:A->B) (face_map Gd (edge_map Gd y))` THEN CONJ_TAC THENL
   [MESON_TAC[GCOMP_SYM_GLINK; glink];
    MATCH_MP_TAC GCOMP_SYM THEN MATCH_MP_TAC CFACE_IMP_GCOMP THEN
    ASM_MESON_TAC[PATCH_CFACE_HD_STEP; EDGE_MAP_IN_DART]]);;

let PATCH_GCOMP_HD = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ x IN dart Gd
     ==> !y. gcomp Gd x y ==> gcomp G (hd x) (hd y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. gcomp Gd x y ==> y IN dart Gd /\ gcomp G ((hd:A->B) x) (hd y)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC GCOMP_INDUCT THEN ASM_REWRITE_TAC[GCOMP_REFL] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN REWRITE_TAC[glink] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[MAPS_IN_DART] THEN
  MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `(hd:A->B) u` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[PATCH_GCOMP_HD_EDGE];
    ASM_MESON_TAC[PATCH_NODE_D; GCOMP_GLINK; glink];
    ASM_MESON_TAC[CFACE_IMP_GCOMP; PATCH_CFACE_HD_STEP]]);;

let PATCH_GCOMP_HR_NODE = prove
 (`!G Gd Gr hd hr bGd bGr y.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     y IN dart Gr
     ==> gcomp G (hr y) (hr (node_map Gr y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GCOMP_SYM THEN
  SUBGOAL_THEN
   `(hr:E->B) y = hr (face_map Gr (edge_map Gr (node_map Gr y)))`
   (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
   [REWRITE_TAC[nodeK]; ALL_TAC] THEN
  MATCH_MP_TAC GCOMP_TRANS THEN
  EXISTS_TAC `(hr:E->B) (edge_map Gr (node_map Gr y))` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PATCH_EDGE_R; NODE_MAP_IN_DART; GCOMP_GLINK; glink];
    MATCH_MP_TAC CFACE_IMP_GCOMP THEN
    ASM_MESON_TAC[PATCH_CFACE_HR_STEP; EDGE_MAP_IN_DART; NODE_MAP_IN_DART]]);;

let PATCH_GCOMP_HR = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr
     ==> !y. gcomp Gr x y ==> gcomp G (hr x) (hr y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. gcomp Gr x y ==> y IN dart Gr /\ gcomp G ((hr:E->B) x) (hr y)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC GCOMP_INDUCT THEN ASM_REWRITE_TAC[GCOMP_REFL] THEN
  MAP_EVERY X_GEN_TAC [`u:E`; `v:E`] THEN REWRITE_TAC[glink] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[MAPS_IN_DART] THEN
  MATCH_MP_TAC GCOMP_TRANS THEN EXISTS_TAC `(hr:E->B) u` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[PATCH_EDGE_R; GCOMP_GLINK; glink];
    ASM_MESON_TAC[PATCH_GCOMP_HR_NODE];
    ASM_MESON_TAC[CFACE_IMP_GCOMP; PATCH_CFACE_HR_STEP]]);;

let PATCH_GLINK_HD_IMAGE = prove
 (`!G Gd Gr hd hr bGd bGr xd v.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ xd IN dart Gd /\
     ~MEM xd bGd /\ glink G (hd xd) v
     ==> ?yd. yd IN dart Gd /\ v = hd yd /\ glink Gd xd yd`,
  REWRITE_TAC[glink] THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `edge_map Gd (xd:A)`;
    EXISTS_TAC `node_map Gd (xd:A)`;
    EXISTS_TAC `face_map Gd (xd:A)`] THEN
  ASM_SIMP_TAC[MAPS_IN_DART] THEN
  ASM_MESON_TAC[PATCH_EDGE_D; PATCH_NODE_D; PATCH_FACE_D]);;

let PATCH_GCOMP_HD_PULLBACK = prove
 (`!G Gd Gr hd hr bGd bGr xd.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ xd IN dart Gd /\
     (!b. MEM b bGd ==> ~gcomp Gd xd b)
     ==> !w. gcomp G (hd xd) w
             ==> ?z. w = hd z /\ z IN dart Gd /\ gcomp Gd xd z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GCOMP_INDUCT THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[GCOMP_REFL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `v:B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~MEM (z:A) bGd` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(PSPECL [`z:A`; `v:B`] PATCH_GLINK_HD_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `yd:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `yd:A` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_TRANS THEN
  EXISTS_TAC `z:A` THEN ASM_SIMP_TAC[GCOMP_GLINK]);;

let PATCH_BGD_GCOMP = prove
 (`!G Gd Gr hd hr bGd bGr a b.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     MEM a bGd /\ MEM b bGd
     ==> gcomp Gd a b`,
  MESON_TAC[PATCH_BGD_ORBIT; GCOMP_EDGE_ORBIT]);;

let PATCH_BGR_GCOMP = prove
 (`!G Gd Gr hd hr bGd bGr a b.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     MEM a bGr /\ MEM b bGr
     ==> gcomp Gr a b`,
  MESON_TAC[PATCH_BGR_ORBIT; GCOMP_NODE_ORBIT]);;

let PATCH_HR_NODE_IMAGE = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ MEM x bGr
     ==> node_map G (hr x) IN IMAGE hd (dart Gd)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(hr:E->B) x IN IMAGE (hd:A->B) (dart Gd)` MP_TAC THENL
   [ASM_MESON_TAC[PATCH_BGR_HR_IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `xd:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `node_map Gd (xd:A)` THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN ASM_MESON_TAC[PATCH_NODE_D]);;

let PATCH_HR_FACE_IMAGE = prove
 (`!G Gd Gr hd hr bGd bGr x.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ MEM (face_map Gr x) bGr
     ==> face_map G (hr x) IN IMAGE hd (dart Gd)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(PSPECL [`x:E`] PATCH_HR_FACE_BORDER) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  ASM_MESON_TAC[PATCH_BGD_DART; FACE_MAP_IN_DART; EDGE_MAP_IN_DART]);;

(* The invariant for pulling a G-path from hr x back to Gr: the current dart *)
(* is hr x' for some x' in the component of x, or lies in the disk while x'  *)
(* is on the border.                                                         *)

let hr_comp_inv = new_definition
 `hr_comp_inv (G:(B)hypermap) (Gd:(A)hypermap) (Gr:(E)hypermap)
              (hd:A->B) (hr:E->B) bGr x w <=>
    w IN dart G /\
    ?x'. x' IN dart Gr /\ gcomp Gr x x' /\
         (w = hr x' \/ MEM x' bGr /\ w IN IMAGE hd (dart Gd))`;;

let PATCH_HR_COMP_INV_STEP = prove
 (`!G Gd Gr hd hr bGd bGr x w v.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ hr_comp_inv G Gd Gr hd hr bGr x w /\ glink G w v
     ==> hr_comp_inv G Gd Gr hd hr bGr x v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hr_comp_inv; IMP_CONJ] THEN
  REPLICATE_TAC 4 DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x':E` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[glink] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[MAPS_IN_DART] THENL
   [EXISTS_TAC `edge_map Gr (x':E)` THEN
    ASM_MESON_TAC[EDGE_MAP_IN_DART; GCOMP_TRANS; GCOMP_GLINK; glink;
                  PATCH_EDGE_R];
    ASM_CASES_TAC `MEM (x':E) bGr` THENL
     [EXISTS_TAC `x':E` THEN ASM_MESON_TAC[PATCH_HR_NODE_IMAGE];
      EXISTS_TAC `node_map Gr (x':E)` THEN
      ASM_MESON_TAC[NODE_MAP_IN_DART; GCOMP_TRANS; GCOMP_GLINK; glink;
                    PATCH_NODE_R]];
    EXISTS_TAC `face_map Gr (x':E)` THEN
    ASM_MESON_TAC[FACE_MAP_IN_DART; GCOMP_TRANS; GCOMP_GLINK; glink;
                  PATCH_HR_FACE_IMAGE; PATCH_FACE_R];
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `xd:A`
                  (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
                GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  (ASM_CASES_TAC `MEM (xd:A) bGd` THENL
    [ALL_TAC;
     EXISTS_TAC `x':E` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
     ASM_MESON_TAC[PATCH_EDGE_D; PATCH_NODE_D; PATCH_FACE_D;
                   MAPS_IN_DART]]) THEN
  (SUBGOAL_THEN
    `?x''. x'' IN dart Gr /\ MEM x'' bGr /\ (hd:A->B) xd = (hr:E->B) x''`
   STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[PATCH_BGD_HD_IN_IMAGE; IN_IMAGE; PATCH_HR_IN_IMAGE_HD];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `gcomp Gr x (x'':E)` ASSUME_TAC THENL
    [ASM_MESON_TAC[GCOMP_TRANS; PATCH_BGR_GCOMP]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `edge_map Gr (x'':E)` THEN
    ASM_MESON_TAC[EDGE_MAP_IN_DART; GCOMP_TRANS; GCOMP_GLINK; glink;
                  PATCH_EDGE_R];
    EXISTS_TAC `x':E` THEN ASM_MESON_TAC[PATCH_HR_NODE_IMAGE];
    ASM_CASES_TAC `MEM (face_map Gr (x'':E)) bGr` THENL
     [EXISTS_TAC `x':E` THEN ASM_MESON_TAC[PATCH_HR_FACE_IMAGE];
      EXISTS_TAC `face_map Gr (x'':E)` THEN
      ASM_MESON_TAC[FACE_MAP_IN_DART; GCOMP_TRANS; GCOMP_GLINK; glink;
                    PATCH_FACE_R]]]);;

let PATCH_HR_COMP_INV_END = prove
 (`!G Gd Gr hd hr bGd bGr x y.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ y IN dart Gr /\ hr_comp_inv G Gd Gr hd hr bGr x (hr y)
     ==> gcomp Gr x y`,
  REWRITE_TAC[hr_comp_inv] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[PATCH_HR_INJ];
    ASM_MESON_TAC[PATCH_HR_IN_IMAGE_HD; PATCH_BGR_GCOMP; GCOMP_TRANS]]);;

let PATCH_GCOMP_HR_REV = prove
 (`!G Gd Gr hd hr bGd bGr x y.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     x IN dart Gr /\ y IN dart Gr /\ gcomp G (hr x) (hr y)
     ==> gcomp Gr x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(PSPECL [`x:E`; `y:E`] PATCH_HR_COMP_INV_END) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`G:(B)hypermap`;
                 `hr_comp_inv G Gd Gr (hd:A->B) (hr:E->B) bGr x`;
                 `(hr:E->B) x`] GCOMP_INDUCT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[hr_comp_inv] THEN
      ASM_MESON_TAC[PATCH_HR_IN_DART; GCOMP_REFL];
      ASM_MESON_TAC[PATCH_HR_COMP_INV_STEP]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PATCH_HD_IN_RCOMP = prove
 (`!G Gd Gr hd hr bGd bGr xd.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     xd IN dart Gd
     ==> ((?zr. zr IN dart Gr /\ gcomp G (hr zr) (hd xd)) <=>
          (?b. MEM b bGd /\ gcomp Gd xd b))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `zr:E` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `?b:A. MEM b bGd /\ gcomp Gd xd b` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(PSPECL [`xd:A`] PATCH_GCOMP_HD_PULLBACK) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(hr:E->B) zr`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[GCOMP_SYM]; ALL_TAC] THEN
    ASM_MESON_TAC[PATCH_HD_IN_IMAGE_HR; IN_IMAGE];
    ASM_MESON_TAC[PATCH_GCOMP_HD; PATCH_BGD_HD_IN_IMAGE; IN_IMAGE; GCOMP_SYM;
                  PATCH_BGD_DART]]);;

let PATCH_COMPONENTS_R = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> CARD(IMAGE (component G)
                    {w | w IN dart G /\
                         ?zr. zr IN dart Gr /\ gcomp G (hr zr) w}) =
         number_of_components Gr`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NCOMP_IMAGE] THEN
  MATCH_MP_TAC CARD_IMAGE_REL THEN EXISTS_TAC `hr:E->B` THEN
  REWRITE_TAC[FINITE_DART; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PATCH_HR_IN_DART; GCOMP_REFL];
    ASM_MESON_TAC[GCOMP_EQ_COMPONENT];
    MAP_EVERY X_GEN_TAC [`x:E`; `y:E`] THEN STRIP_TAC THEN
    MP_TAC(PSPECL [`x:E`] PATCH_GCOMP_HR) THEN
    MP_TAC(PSPECL [`x:E`; `y:E`] PATCH_GCOMP_HR_REV) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[GCOMP_EQ_COMPONENT; COMPONENT_EQ_GCOMP; PATCH_HR_IN_DART]]);;

let PATCH_COMPONENTS_D = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> CARD(IMAGE (component G)
               (dart G DIFF
                {w | w IN dart G /\
                     ?zr. zr IN dart Gr /\ gcomp G (hr zr) w})) =
         CARD(IMAGE (component Gd)
               (dart Gd DIFF
                {xd | xd IN dart Gd /\ ?b. MEM b bGd /\ gcomp Gd xd b}))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_REL THEN
  EXISTS_TAC `hd:A->B` THEN
  ASM_SIMP_TAC[FINITE_DIFF; FINITE_DART; IN_DIFF; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PATCH_HD_IN_DART; PATCH_HD_IN_RCOMP];
    X_GEN_TAC `z:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `z IN IMAGE (hd:A->B) (dart Gd)` MP_TAC THENL
     [ASM_MESON_TAC[PATCH_IN_IMAGE_HD; IN_IMAGE; GCOMP_REFL]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `xd:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `xd:A` THEN ASM_MESON_TAC[PATCH_HD_IN_RCOMP];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    MP_TAC(PSPECL [`x:A`] PATCH_GCOMP_HD) THEN
    MP_TAC(PSPECL [`x:A`] PATCH_GCOMP_HD_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "pull") THEN DISCH_THEN(LABEL_TAC "push") THEN
    EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC GCOMP_EQ_COMPONENT THENL
     [REMOVE_THEN "push" MATCH_MP_TAC THEN ASM_MESON_TAC[COMPONENT_EQ_GCOMP];
      REMOVE_THEN "pull" (MP_TAC o SPEC `(hd:A->B) y`) THEN ANTS_TAC THENL
       [ASM_MESON_TAC[COMPONENT_EQ_GCOMP; PATCH_HD_IN_DART]; ALL_TAC] THEN
      ASM_MESON_TAC[PATCH_HD_INJ]]]);;

let PATCH_COMPONENTS_BORDER = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> CARD(IMAGE (component Gd)
                    {xd | xd IN dart Gd /\
                          ?b. MEM b bGd /\ gcomp Gd xd b}) = 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM (HD bGd) (bGd:(A)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HD_MEM; LENGTH_EQ_NIL; ARITH_RULE `2 <= n ==> ~(n = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (component Gd)
          {xd | xd IN dart Gd /\ ?b. MEM b bGd /\ gcomp Gd xd b} =
    {component (Gd:(A)hypermap) (HD bGd)}`
  SUBST1_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_SING]] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING; IN_ELIM_THM] THEN
  X_GEN_TAC `c:A->bool` THEN EQ_TAC THENL
   [ASM_MESON_TAC[GCOMP_EQ_COMPONENT; GCOMP_TRANS; PATCH_BGD_GCOMP];
    ASM_MESON_TAC[PATCH_BGD_DART; GCOMP_REFL]]);;

let COMPONENTS_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> number_of_components G + 1 =
         number_of_components Gd + number_of_components Gr`,
  REPEAT STRIP_TAC THEN
  MP_TAC(PSPECL [] PATCH_COMPONENTS_R) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[NCOMP_IMAGE] THEN
  MP_TAC(ISPECL [`component (G:(B)hypermap)`; `dart(G:(B)hypermap)`;
    `{w | w IN dart G /\ ?zr. zr IN dart Gr /\ gcomp G ((hr:E->B) zr) w}`]
    CARD_IMAGE_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[COMPONENT_EQ_GCOMP; GCOMP_TRANS];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`component (Gd:(A)hypermap)`; `dart(Gd:(A)hypermap)`;
    `{xd | xd IN dart (Gd:(A)hypermap) /\ ?b. MEM b bGd /\ gcomp Gd xd b}`]
    CARD_IMAGE_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DART; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[COMPONENT_EQ_GCOMP; GCOMP_TRANS; GCOMP_SYM];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(PSPECL [] PATCH_COMPONENTS_BORDER) THEN
  MP_TAC(PSPECL [] PATCH_COMPONENTS_D) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Genus and planarity: additivity follows from the five counts and the      *)
(* Euler relations of the three maps.                                        *)
(* ------------------------------------------------------------------------- *)

let GENUS_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
     ==> genus G = genus Gd + genus Gr`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (MP_TAC o PSPECL [])
    [COMPONENTS_PATCH; CARD_PATCH; EDGES_PATCH; NODES_PATCH; FACES_PATCH] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `G:(B)hypermap` EVEN_GENUS) THEN
  MP_TAC(ISPEC `Gd:(A)hypermap` EVEN_GENUS) THEN
  MP_TAC(ISPEC `Gr:(E)hypermap` EVEN_GENUS) THEN
  REWRITE_TAC[even_genus; euler_lhs; euler_rhs] THEN ARITH_TAC);;

let PLANAR_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
   ==> (planar_hypermap G <=> planar_hypermap Gd /\ planar_hypermap Gr)`,
  REWRITE_TAC[planar_hypermap] THEN MESON_TAC[GENUS_PATCH; ADD_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Colourings: trace lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let PTRACE_REVERSE = prove
 (`!lc:color list. ptrace(REVERSE lc) = REVERSE(ptrace lc)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE; ptrace] THEN
  POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC(ISPEC `t:color list` list_CASES) THEN
  REWRITE_TAC[REVERSE; APPEND; ptrace] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[PTRACE_SNOC; REVERSE_EQ_EMPTY; NOT_CONS_NIL; LAST_REVERSE;
               GSYM(CONJUNCT2 REVERSE); HD; REVERSE_APPEND; APPEND] THEN
  REWRITE_TAC[ADDC_COMM]);;

let TRACE_COL_HD = prove
 (`!l:color list. ~(l = [])
    ==> trace_col l = CONS (addc (LAST l) (HD l)) (ptrace l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TRACE_COL_CONS; HD]);;

let TRACE_COL_REVERSE = prove
 (`!lc:color list. ~(lc = [])
   ==> trace_col(REVERSE lc) = REVERSE(rot1(trace_col lc))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(REVERSE (lc:color list) = [])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REVERSE_EQ_EMPTY]; ALL_TAC] THEN
  ASM_SIMP_TAC[TRACE_COL_HD; LAST_REVERSE; HD_REVERSE] THEN
  ONCE_REWRITE_TAC[ADDC_COMM] THEN
  REWRITE_TAC[rot1; NOT_CONS_NIL; HD; TL] THEN
  REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND; PTRACE_REVERSE; ADDC_COMM]);;

let TRACE_COL_PTRACE_EQ = prove
 (`!l1 l2:color list.
    ~(l1 = []) /\ ~(l2 = []) /\ trace_col l1 = trace_col l2
    ==> ptrace l1 = ptrace l2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `CONS (addc (LAST l1) (HD l1)) (ptrace l1) =
    CONS (addc (LAST l2) (HD l2)) (ptrace (l2:color list))`
  MP_TAC THENL [ASM_MESON_TAC[TRACE_COL_HD]; SIMP_TAC[CONS_11]]);;

let COLORING_ADDC = prove
 (`!H:(A)hypermap k c. coloring H k ==> coloring H (addc c o k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coloring; o_THM] THEN STRIP_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THENL
   [REWRITE_TAC[ADDC_CANCEL_L] THEN ASM_MESON_TAC[];
    AP_TERM_TAC THEN ASM_MESON_TAC[]]);;

let UNTRACE_PTRACE_HD = prove
 (`!l:color list. ~(l = []) ==> untrace (HD l) (ptrace l) = l`,
  SUBGOAL_THEN `!l c:color. untrace c (ptrace (CONS c l)) = CONS c l`
    (fun th -> LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD; th]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ptrace; untrace; ADDC_SELF_CANCEL]);;

let UNTRACE_ADDC = prove
 (`!et c0 c:color. untrace (addc c c0) et = MAP (addc c) (untrace c0 et)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[untrace; MAP] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `addc (addc c c0) (a0:color) = addc c (addc c0 a0)`
    SUBST1_TAC THENL
   [REWRITE_TAC[ADDC_ASSOC]; ASM_REWRITE_TAC[]]);;

let PTRACE_EQ_IMPLIES_ADDC = prove
 (`!l1 l2:color list.
    ~(l1 = []) /\ ~(l2 = []) /\ ptrace l1 = ptrace l2
    ==> l1 = MAP (addc (addc (HD l1) (HD l2))) l2`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `untrace (HD (l1:color list)) (ptrace l2)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(l2:color list) = untrace (HD l2) (ptrace l2)`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC UNTRACE_PTRACE_HD THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM UNTRACE_ADDC; ADDC_CANCEL_SELF2]];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC UNTRACE_PTRACE_HD THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Colourability: a colouring of G restricts to Gd and Gr with matching ring *)
(* traces; conversely colourings of Gd and Gr whose traces match can be      *)
(* shifted to agree on the ring and then glued.                              *)
(* ------------------------------------------------------------------------- *)

let PATCH_COLORING_HD = prove
 (`!G Gd Gr hd hr bGd bGr k.
    patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ coloring G k
    ==> coloring Gd (k o hd)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:A. x IN dart Gd ==> (k:B->color)(hd(face_map Gd x)) = k(hd x)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[CFACE_COLORING; PATCH_CFACE_HD_STEP; PATCH_HD_IN_DART];
    ALL_TAC] THEN
  REWRITE_TAC[coloring; o_THM] THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(hd:A->B) x = node_map G (hd (face_map Gd (edge_map Gd x)))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `face_map Gd (edge_map Gd (x:A))` o
                MATCH_MP PATCH_NODE_D) THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; edgeK];
    ASM_MESON_TAC[COLORING_NODE_NEQ; PATCH_HD_IN_DART; FACE_MAP_IN_DART;
                  EDGE_MAP_IN_DART]]);;

let PATCH_COLORING_HR = prove
 (`!G Gd Gr hd hr bGd bGr k.
    patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
    coloring G k
    ==> coloring Gr (k o hr)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[coloring; o_THM] THEN
  CONJ_TAC THEN X_GEN_TAC `x:E` THEN DISCH_TAC THENL
   [ASM_MESON_TAC[PATCH_EDGE_R; coloring; PATCH_HR_IN_DART];
    ASM_MESON_TAC[CFACE_COLORING; PATCH_CFACE_HR_STEP; PATCH_HR_IN_DART]]);;

let COLORABLE_PATCH_IMP = prove
 (`!G Gd Gr hd hr bGd bGr k.
    patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
    coloring G k
    ==> ?et. ring_trace Gd bGd et /\ ring_trace Gr bGr (REVERSE(rot1 et))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `trace_col (MAP ((k:B->color) o (hd:A->B)) bGd)` THEN
  REWRITE_TAC[ring_trace] THEN CONJ_TAC THENL
   [EXISTS_TAC `(k:B->color) o (hd:A->B)` THEN
    ASM_MESON_TAC[PATCH_COLORING_HD];
    ALL_TAC] THEN
  EXISTS_TAC `(k:B->color) o (hr:E->B)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PATCH_COLORING_HR]; ALL_TAC] THEN
  REWRITE_TAC[MAP_o] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PATCH_MAP_RING_R th]) THEN
  REWRITE_TAC[GSYM MAP_REVERSE] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC TRACE_COL_REVERSE THEN REWRITE_TAC[MAP_EQ_NIL] THEN
  ASM_MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `2 <= n ==> ~(n = 0)`]);;

let PATCH_GLUE_COLORING = prove
 (`!G Gd Gr hd hr bGd bGr kd kr.
     patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
     coloring Gd kd /\ coloring Gr kr /\
     (!xd xr. MEM xd bGd /\ MEM xr bGr /\ hd xd = hr xr ==> kd xd = kr xr)
     ==> four_colorable G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coloring] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?k:B->color. (!xr. xr IN dart Gr ==> k((hr:E->B) xr) = (kr:E->color) xr) /\
                 (!xd. xd IN dart Gd ==> k((hd:A->B) xd) = (kd:A->color) xd)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `\z:B. if z IN IMAGE (hr:E->B) (dart Gr)
            then (kr:E->color)(@xr. xr IN dart Gr /\ hr xr = z)
            else (kd:A->color)(@xd. xd IN dart Gd /\ hd xd = z)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(hr:E->B) xr IN IMAGE hr (dart Gr)`
        (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC INJ_SELECT THEN
      EXISTS_TAC `dart(G:(B)hypermap)` THEN ASM_MESON_TAC[PATCH_INJ_HR];
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `xr:E` STRIP_ASSUME_TAC o
                      GEN_REWRITE_RULE I [IN_IMAGE]) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(@y. y IN dart Gr /\ (hr:E->B) y = hr xr) = xr`
        SUBST1_TAC THENL
         [MATCH_MP_TAC INJ_SELECT THEN EXISTS_TAC `dart(G:(B)hypermap)` THEN
          ASM_MESON_TAC[PATCH_INJ_HR];
          ASM_MESON_TAC[PATCH_HD_IN_IMAGE_HR; PATCH_HR_IN_IMAGE_HD; IN_IMAGE]];
        AP_TERM_TAC THEN MATCH_MP_TAC INJ_SELECT THEN
        EXISTS_TAC `dart(G:(B)hypermap)` THEN ASM_MESON_TAC[PATCH_INJ_HD]]];
    ALL_TAC] THEN
  REWRITE_TAC[four_colorable; coloring] THEN EXISTS_TAC `k:B->color` THEN
  SUBGOAL_THEN
   `!z:B. z IN dart G
          ==> ~((k:B->color)(edge_map G z) = k z) /\ k(face_map G z) = k z`
   (fun th -> MESON_TAC[th]) THEN
  X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  ASM_CASES_TAC `z IN IMAGE (hr:E->B) (dart Gr)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `xr:E`
                    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
                  GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[PATCH_EDGE_R; EDGE_MAP_IN_DART]; ALL_TAC] THEN
    ASM_CASES_TAC `MEM (face_map Gr (xr:E)) bGr` THENL
     [ALL_TAC; ASM_MESON_TAC[PATCH_FACE_R; FACE_MAP_IN_DART]] THEN
    MP_TAC(PSPECL [`xr:E`] PATCH_HR_FACE_BORDER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `xd:A` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN
     `xd IN dart Gd /\ edge_map Gd xd IN dart Gd /\
      face_map Gd (edge_map Gd xd) IN dart (Gd:(A)hypermap)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PATCH_BGD_DART; EDGE_MAP_IN_DART; FACE_MAP_IN_DART];
      ALL_TAC] THEN
    SUBGOAL_THEN `(kd:A->color) (edge_map Gd xd) = kr (face_map Gr (xr:E))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[PATCH_BGD_EDGE];
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN `z IN IMAGE (hd:A->B) (dart Gd)` MP_TAC THENL
     [ASM_MESON_TAC[PATCH_IN_IMAGE_HD]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `xd:A`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `~MEM (xd:A) bGd` ASSUME_TAC THENL
     [ASM_MESON_TAC[PATCH_HD_IN_IMAGE_HR]; ALL_TAC] THEN
    SUBGOAL_THEN
     `edge_map G ((hd:A->B) xd) = hd (edge_map Gd xd) /\
      face_map G (hd xd) = hd (face_map Gd xd)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PATCH_EDGE_D; PATCH_FACE_D]; ALL_TAC] THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART; FACE_MAP_IN_DART]]);;

let COLORABLE_PATCH_REV = prove
 (`!G Gd Gr hd hr bGd bGr et.
    patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd /\
    ring_trace Gd bGd et /\ ring_trace Gr bGr (REVERSE(rot1 et))
    ==> four_colorable G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_trace] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `kd:A->color` STRIP_ASSUME_TAC)
                     (X_CHOOSE_THEN `kr:E->color` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `~(bGd:(A)list = []) /\ ~(bGr:(E)list = [])`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; PATCH_LENGTH_R;
                  ARITH_RULE `2 <= n ==> ~(n = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `trace_col (MAP (kr:E->color) bGr) =
    trace_col (MAP (kd:A->color) (REVERSE bGd))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `REVERSE (rot1 et) = trace_col (MAP (kr:E->color) bGr)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `et = trace_col (MAP (kd:A->color) bGd)` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM MAP_REVERSE] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC TRACE_COL_REVERSE THEN
    ASM_REWRITE_TAC[MAP_EQ_NIL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`MAP (kr:E->color) bGr`; `MAP (kd:A->color) (REVERSE bGd)`]
    PTRACE_EQ_IMPLIES_ADDC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MAP_EQ_NIL; REVERSE_EQ_EMPTY] THEN
    MATCH_MP_TAC TRACE_COL_PTRACE_EQ THEN
    ASM_REWRITE_TAC[MAP_EQ_NIL; REVERSE_EQ_EMPTY];
    ALL_TAC] THEN
  ABBREV_TAC `c = addc (HD (MAP (kr:E->color) bGr))
                       (HD (MAP (kd:A->color) (REVERSE bGd)))` THEN
  REWRITE_TAC[GSYM MAP_o] THEN DISCH_TAC THEN
  MP_TAC(PSPECL [`addc c o (kd:A->color)`; `kr:E->color`]
                PATCH_GLUE_COLORING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COLORING_ADDC]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`xd:A`; `xr:E`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`bGr:(E)list`; `bGd:(A)list`; `hd:A->B`; `hr:E->B`;
                       `addc c o (kd:A->color)`; `kr:E->color`]
                BORDER_MATCH) THEN
  ASM_REWRITE_TAC[INJ; IN_UNIV; IN_SET_OF_LIST] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PATCH_CYCLE_R];
    ASM_MESON_TAC[PATCH_HD_INJ; PATCH_BGD_DART];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PATCH_MAP_RING_R th]) THEN
    REWRITE_TAC[MAP_REVERSE]]);;

let COLORABLE_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
   patch G Gd Gr (hd:A->B) (hr:E->B) bGd bGr /\ 2 <= LENGTH bGd
   ==> (four_colorable G <=>
        ?et. ring_trace Gd bGd et /\ ring_trace Gr bGr (REVERSE(rot1 et)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[four_colorable] THEN ASM_MESON_TAC[COLORABLE_PATCH_IMP];
    ASM_MESON_TAC[COLORABLE_PATCH_REV]]);;
