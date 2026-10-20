(* ========================================================================= *)
(* 4CT/sew.ml                                                                *)
(*                                                                           *)
(* sew.v: sewing two bordered maps along a ring.  A disk map Gd:(A)hypermap  *)
(* with a simple edge-cycle bGd and a remainder map Gr:(B)hypermap with a    *)
(* node-cycle bGr of the same length are glued into sew_map : (A+B)hypermap  *)
(* whose darts are the darts of Gd (INL) and the darts of Gr off bGr (INR);  *)
(* a border dart of Gr is identified (sewr) with the dart of bGd in the      *)
(* mirror position (sew_hrd).  Unlike Coq, the face map is defined as the    *)
(* inverse of edge o node, so the hypermap law is free and everything        *)
(* reduces to sew_edge and sew_node being permutations of the dart set.      *)
(* Main theorem: SEW_MAP_PATCH, the sewn map is a patch of Gd and Gr.        *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/coloring.ml";;
needs "4CT/kempe.ml";;
needs "4CT/patch.ml";;
needs "4CT/revsnip.ml";;

(* ------------------------------------------------------------------------- *)
(* Position of an element in a list (Coq index) and the border bijection     *)
(* hdr : bGd -> bGr, hrd : bGr -> bGd (mirror positions; EL is total so no   *)
(* default element is needed).                                               *)
(* ------------------------------------------------------------------------- *)

let INDEXL = define
 `(INDEXL (x:A) [] = 0) /\
  (INDEXL x (CONS h t) = if x = h then 0 else SUC (INDEXL x t))`;;

let INDEXL_EL_UNIQ = prove
 (`!l i. PAIRWISE (\x y:A. ~(x = y)) l /\ i < LENGTH l
         ==> INDEXL (EL i l) l = i`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[EL; HD; TL; INDEXL; LT_SUC; PAIRWISE; GSYM ALL_MEM] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[SUC_INJ] THEN
  ASM_MESON_TAC[MEM_EXISTS_EL]);;

let sew_hdr = new_definition
 `sew_hdr (bGd:A list) (bGr:B list) (xd:A) =
  EL (INDEXL xd bGd) (REVERSE bGr)`;;

let sew_hrd = new_definition
 `sew_hrd (bGd:A list) (bGr:B list) (xr:B) =
  EL (INDEXL xr (REVERSE bGr)) bGd`;;

let SEW_HDR_EL = prove
 (`!(bGd:A list) (bGr:B list) i.
     PAIRWISE (\x y. ~(x = y)) bGd /\ i < LENGTH bGd
     ==> sew_hdr bGd bGr (EL i bGd) = EL i (REVERSE bGr)`,
  SIMP_TAC[sew_hdr; INDEXL_EL_UNIQ]);;

let SEW_HRD_EL = prove
 (`!(bGd:A list) (bGr:B list) i.
     PAIRWISE (\x y. ~(x = y)) bGr /\ i < LENGTH bGr
     ==> sew_hrd bGd bGr (EL i (REVERSE bGr)) = EL i bGd`,
  SIMP_TAC[sew_hrd; INDEXL_EL_UNIQ; PAIRWISE_NEQ_REVERSE; LENGTH_REVERSE]);;

let SEW_HRD_MAP = prove
 (`!(bGd:A list) (bGr:B list).
     LENGTH bGd = LENGTH bGr /\ PAIRWISE (\x y. ~(x = y)) bGr
     ==> MAP (sew_hrd bGd bGr) bGr = REVERSE bGd`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[REVERSE_REVERSE]
    `REVERSE l1 = l2 ==> l1 = REVERSE (l2:A list)`) THEN
  REWRITE_TAC[MAP_REVERSE; LIST_EQ; LENGTH_MAP; LENGTH_REVERSE] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_REVERSE; SEW_HRD_EL]);;

(* ------------------------------------------------------------------------- *)
(* The sewn map (Coq sew_dart / sewd / sewr / sew_edge / sew_node /          *)
(* sew_map) and the side conditions sew_context (Coq cycEbGd, cycNbGr,       *)
(* sz_bG).  The maps are the identity off the dart set sew_D.                *)
(* ------------------------------------------------------------------------- *)

let sewd = new_definition
 `sewd (xd:A) = (INL xd:A+B)`;;

let sewr = new_definition
 `sewr (bGd:A list) (bGr:B list) (xr:B) =
    if MEM xr bGr then INL (sew_hrd bGd bGr xr) else (INR xr:A+B)`;;

let sew_D = new_definition
 `sew_D (Gd:(A)hypermap) (Gr:(B)hypermap) (bGr:B list) =
    IMAGE INL (dart Gd) UNION IMAGE INR {xr | xr IN dart Gr /\ ~MEM xr bGr}`;;

let sew_edge = new_recursive_definition sum_RECURSION
 `(sew_edge (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr (INL xd) =
     if xd IN dart Gd then
       (if MEM xd bGd then sewr bGd bGr (edge_map Gr (sew_hdr bGd bGr xd))
                      else sewd (edge_map Gd xd))
     else (INL xd:A+B)) /\
  (sew_edge (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr (INR xr) =
     if xr IN dart Gr /\ ~MEM xr bGr then sewr bGd bGr (edge_map Gr xr)
     else (INR xr:A+B))`;;

let sew_node = new_recursive_definition sum_RECURSION
 `(sew_node (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr (INL xd) =
     if xd IN dart Gd then sewd (node_map Gd xd) else (INL xd:A+B)) /\
  (sew_node (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr (INR xr) =
     if xr IN dart Gr /\ ~MEM xr bGr then sewr bGd bGr (node_map Gr xr)
     else (INR xr:A+B))`;;

let sew_face = new_definition
 `sew_face (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr =
    inverse (sew_edge Gd Gr bGd bGr o sew_node Gd Gr bGd bGr)`;;

let sew_map = new_definition
 `sew_map (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr =
    mk_hypermap (sew_D Gd Gr bGr, sew_edge Gd Gr bGd bGr,
                 sew_node Gd Gr bGd bGr, sew_face Gd Gr bGd bGr)`;;

let sew_context = new_definition
 `sew_context (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr <=>
    list_cycle (\x y. edge_map Gd x = y) bGd /\
    PAIRWISE (\x y. ~(x = y)) bGd /\ ALL (\w. w IN dart Gd) bGd /\
    face_simple Gd bGd /\
    list_cycle (\x y. node_map Gr x = y) bGr /\
    PAIRWISE (\x y. ~(x = y)) bGr /\ ALL (\w. w IN dart Gr) bGr /\
    LENGTH bGd = LENGTH bGr`;;

(* ------------------------------------------------------------------------- *)
(* Basic facts: the dart set, the cycles are closed under their maps, the    *)
(* border bijection, the clauses of sewr.                                    *)
(* ------------------------------------------------------------------------- *)

let IN_SEW_D = prove
 (`(!(Gd:(A)hypermap) (Gr:(B)hypermap) bGr xd.
       (INL xd:A+B) IN sew_D Gd Gr bGr <=> xd IN dart Gd) /\
   (!(Gd:(A)hypermap) (Gr:(B)hypermap) bGr xr.
       (INR xr:A+B) IN sew_D Gd Gr bGr <=> xr IN dart Gr /\ ~MEM xr bGr)`,
  REWRITE_TAC[sew_D; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[injectivity "sum"; distinctness "sum"]);;

let FINITE_SEW_D = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGr. FINITE (sew_D Gd Gr bGr)`,
  SIMP_TAC[sew_D; FINITE_UNION; FINITE_IMAGE; FINITE_DART; FINITE_RESTRICT]);;

let LIST_CYCLE_MEM_IMAGE = prove
 (`!(f:A->A) s r a.
     f permutes s /\ list_cycle (\x y. f x = y) r
     ==> (MEM (f a) r <=> MEM a r)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MP_TAC(ISPECL [`\(x:A) y. (f:A->A) x = y`; `r:A list`; `(f:A->A) a`]
      CYCLE_MEM_PRED) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PERMUTES_INJ];
    ASM_MESON_TAC[LIST_CYCLE_F_CLOSED]]);;

let MEM_EL_REVERSE = prove
 (`!(l:A list) i. i < LENGTH l ==> MEM (EL i (REVERSE l)) l`,
  MESON_TAC[MEM_EL; MEM_REVERSE; LENGTH_REVERSE]);;

let SEW_HDR_HRD = prove
 (`!(bGd:A list) (bGr:B list).
     LENGTH bGd = LENGTH bGr /\
     PAIRWISE (\x y. ~(x = y)) bGd /\ PAIRWISE (\x y. ~(x = y)) bGr
     ==> (!xd. MEM xd bGd
               ==> MEM (sew_hdr bGd bGr xd) bGr /\
                   sew_hrd bGd bGr (sew_hdr bGd bGr xd) = xd) /\
         (!xr. MEM xr bGr
               ==> MEM (sew_hrd bGd bGr xr) bGd /\
                   sew_hdr bGd bGr (sew_hrd bGd bGr xr) = xr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THENL
   [DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [MEM_EXISTS_EL]);
    DISCH_THEN(MP_TAC o REWRITE_RULE[MEM_EXISTS_EL; LENGTH_REVERSE] o
               ONCE_REWRITE_RULE[GSYM MEM_REVERSE])] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  (SUBGOAL_THEN `i < LENGTH(bGd:A list) /\ i < LENGTH(bGr:B list)`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[SEW_HDR_EL; SEW_HRD_EL; MEM_EL; MEM_EL_REVERSE]);;

let SEW_CONTEXT_FACTS = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> (!xd. MEM xd bGd ==> xd IN dart Gd) /\
         (!xr. MEM xr bGr ==> xr IN dart Gr) /\
         (!xd. MEM (edge_map Gd xd) bGd <=> MEM xd bGd) /\
         (!xr. MEM (node_map Gr xr) bGr <=> MEM xr bGr) /\
         (!xd. MEM xd bGd
               ==> MEM (sew_hdr bGd bGr xd) bGr /\
                   sew_hdr bGd bGr xd IN dart Gr /\
                   sew_hrd bGd bGr (sew_hdr bGd bGr xd) = xd) /\
         (!xr. MEM xr bGr
               ==> MEM (sew_hrd bGd bGr xr) bGd /\
                   sew_hrd bGd bGr xr IN dart Gd /\
                   sew_hdr bGd bGr (sew_hrd bGd bGr xr) = xr)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sew_context; GSYM ALL_MEM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`bGd:A list`; `bGr:B list`] SEW_HDR_HRD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`edge_map (Gd:(A)hypermap)`; `dart (Gd:(A)hypermap)`;
                   `bGd:A list`] LIST_CYCLE_MEM_IMAGE) THEN
    ASM_REWRITE_TAC[EDGE_MAP_PERMUTES];
    MP_TAC(ISPECL [`node_map (Gr:(B)hypermap)`; `dart (Gr:(B)hypermap)`;
                   `bGr:B list`] LIST_CYCLE_MEM_IMAGE) THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES]]);;

let SEWR_CLAUSES = prove
 (`!(bGd:A list) (bGr:B list).
     (!xr. MEM xr bGr ==> sewr bGd bGr xr = INL (sew_hrd bGd bGr xr)) /\
     (!xr. ~MEM xr bGr ==> sewr bGd bGr xr = INR xr) /\
     (!xr xd. sewr bGd bGr xr = INL xd <=>
              MEM xr bGr /\ xd = sew_hrd bGd bGr xr) /\
     (!xr yr. sewr bGd bGr xr = INR yr <=> ~MEM xr bGr /\ yr = xr)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sewr] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "sum"; distinctness "sum"; SUM_DISTINCT_SYM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The dart set is covered by the images of sewr and of the interior disk    *)
(* darts; the sewn maps on these two kinds of darts.                         *)
(* ------------------------------------------------------------------------- *)

let SEW_D_CASES = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr w.
     sew_context Gd Gr bGd bGr
     ==> (w IN sew_D Gd Gr bGr <=>
          (?xr. xr IN dart Gr /\ sewr bGd bGr xr = w) \/
          (?xd. xd IN dart Gd /\ ~MEM xd bGd /\ INL xd = w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP SEW_CONTEXT_FACTS) THEN
  SPEC_TAC(`w:A+B`,`w:A+B`) THEN MATCH_MP_TAC sum_INDUCT THEN
  REWRITE_TAC[IN_SEW_D; SEWR_CLAUSES; injectivity "sum"; distinctness "sum";
              SUM_DISTINCT_SYM] THEN
  ASM_MESON_TAC[]);;

let SEWR_IN_D = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> !xr. xr IN dart Gr ==> sewr bGd bGr xr IN sew_D Gd Gr bGr`,
  MESON_TAC[SEW_D_CASES]);;

let SEWR_INJ = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> !xr yr. sewr bGd bGr xr = sewr bGd bGr yr ==> xr = yr`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP SEW_CONTEXT_FACTS) THEN
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`MEM (xr:B) bGr`; `MEM (yr:B) bGr`] THEN
  ASM_SIMP_TAC[SEWR_CLAUSES; injectivity "sum"; distinctness "sum";
               SUM_DISTINCT_SYM] THEN
  ASM_MESON_TAC[]);;

let SEWR_INL_MEM = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> !xr xd. sewr bGd bGr xr = INL xd ==> MEM xd bGd`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP SEW_CONTEXT_FACTS) THEN
  REWRITE_TAC[SEWR_CLAUSES] THEN ASM_MESON_TAC[]);;

let SEW_EDGE_SEWR = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> !xr. xr IN dart Gr
              ==> sew_edge Gd Gr bGd bGr (sewr bGd bGr xr) =
                  sewr bGd bGr (edge_map Gr xr)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP SEW_CONTEXT_FACTS) THEN
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `MEM (xr:B) bGr` THEN ASM_SIMP_TAC[SEWR_CLAUSES; sew_edge]);;

let SEW_NODE_SEWR = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr xr.
     xr IN dart Gr /\ ~MEM xr bGr
     ==> sew_node Gd Gr bGd bGr (sewr bGd bGr xr) =
         sewr bGd bGr (node_map Gr xr)`,
  SIMP_TAC[SEWR_CLAUSES; sew_node]);;

(* ------------------------------------------------------------------------- *)
(* sew_edge and sew_node permute the dart set, so sew_map is a hypermap      *)
(* with the intended components.                                             *)
(* ------------------------------------------------------------------------- *)

let SEW_NODE_PERMUTES = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> sew_node Gd Gr bGd bGr permutes sew_D Gd Gr bGr`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP SEW_CONTEXT_FACTS) THEN
  SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_SEW_D] THEN
  SUBGOAL_THEN
   `(!xd. xd IN dart Gd
          ==> sew_node (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr (INL xd) =
              INL (node_map Gd xd)) /\
    (!xr. xr IN dart Gr /\ ~MEM xr bGr
          ==> sew_node (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr (INR xr) =
              INR (node_map Gr xr))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[sew_node; sewd; SEWR_CLAUSES]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC sum_INDUCT THEN SIMP_TAC[IN_SEW_D; sew_node];
    MATCH_MP_TAC sum_INDUCT THEN
    ASM_SIMP_TAC[IN_SEW_D; NODE_MAP_IN_DART];
    MATCH_MP_TAC sum_INDUCT THEN CONJ_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC sum_INDUCT THEN REWRITE_TAC[IN_SEW_D] THEN
    ASM_MESON_TAC[injectivity "sum"; distinctness "sum"; NODEI]]);;

let SEW_EDGE_PERMUTES = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> sew_edge Gd Gr bGd bGr permutes sew_D Gd Gr bGr`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SEW_CONTEXT_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEW_EDGE_SEWR) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEWR_INJ) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEWR_IN_D) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEWR_INL_MEM) THEN
  SUBGOAL_THEN
   `!xd. xd IN dart Gd /\ ~MEM xd bGd
         ==> sew_edge (Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr (INL xd) =
             INL (edge_map Gd xd)`
  ASSUME_TAC THENL [SIMP_TAC[sew_edge; sewd]; ALL_TAC] THEN
  SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_SEW_D] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC sum_INDUCT THEN SIMP_TAC[IN_SEW_D; sew_edge];
    X_GEN_TAC `w:A+B` THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC LAND_CONV [MATCH_MP SEW_D_CASES th]) THEN
    STRIP_TAC THEN ASM_MESON_TAC[EDGE_MAP_IN_DART; IN_SEW_D];
    MAP_EVERY X_GEN_TAC [`x:A+B`; `y:A+B`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SEW_D_CASES th]) THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[EDGEI; injectivity "sum"]]);;

let SEW_MAP_COMPONENTS = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> dart (sew_map Gd Gr bGd bGr) = sew_D Gd Gr bGr /\
         edge_map (sew_map Gd Gr bGd bGr) = sew_edge Gd Gr bGd bGr /\
         node_map (sew_map Gd Gr bGd bGr) = sew_node Gd Gr bGd bGr /\
         face_map (sew_map Gd Gr bGd bGr) = sew_face Gd Gr bGd bGr`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sew_map] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  REWRITE_TAC[hypermap_pred; FST; SND; sew_face] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEW_EDGE_PERMUTES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEW_NODE_PERMUTES) THEN
  SUBGOAL_THEN
   `(sew_edge Gd Gr bGd bGr o sew_node Gd Gr bGd bGr) permutes
    sew_D (Gd:(A)hypermap) (Gr:(B)hypermap) bGr`
  ASSUME_TAC THENL [ASM_MESON_TAC[PERMUTES_COMPOSE]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_SEW_D; PERMUTES_INVERSE; o_ASSOC] THEN
  ASM_MESON_TAC[PERMUTES_INVERSES_o]);;

(* ------------------------------------------------------------------------- *)
(* The patch theorem.                                                        *)
(* ------------------------------------------------------------------------- *)

let SEWR_REV_SEWD = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> MAP (sewr bGd bGr) bGr = REVERSE (MAP sewd bGd)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sew_context] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `MAP (sewr bGd bGr) bGr = MAP ((INL:A->A+B) o sew_hrd bGd bGr) bGr`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
    SIMP_TAC[SEWR_CLAUSES];
    ASM_SIMP_TAC[MAP_o; SEW_HRD_MAP; MAP_REVERSE] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM] sewd]]);;

let SEW_COVER = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> !x. x IN sew_D Gd Gr bGr
             ==> (x IN IMAGE (sewr bGd bGr) (dart Gr) <=>
                  ~(x IN IMAGE sewd (dart Gd)) \/ MEM x (MAP sewd bGd))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SEW_CONTEXT_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEWR_INL_MEM) THEN
  X_GEN_TAC `x:A+B` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SEW_D_CASES th]) THEN
  REWRITE_TAC[IN_IMAGE; MEM_MAP; REWRITE_RULE[GSYM FUN_EQ_THM] sewd] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[injectivity "sum"] THENL
   [SUBGOAL_THEN
     `?y. sewr (bGd:A list) (bGr:B list) xr = sewr bGd bGr y /\
          y IN dart (Gr:(B)hypermap)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `MEM (xr:B) bGr` THEN
    ASM_SIMP_TAC[SEWR_CLAUSES; injectivity "sum"; distinctness "sum";
                 SUM_DISTINCT_SYM] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let SEW_MAP_PATCH = prove
 (`!(Gd:(A)hypermap) (Gr:(B)hypermap) bGd bGr.
     sew_context Gd Gr bGd bGr
     ==> patch (sew_map Gd Gr bGd bGr) Gd Gr
               (sewd:A->A+B) ((sewr:A list->B list->B->A+B) bGd bGr) bGd bGr`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[patch; scycle; MATCH_MP SEW_MAP_COMPONENTS th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sew_context]) THEN
  ASM_SIMP_TAC[SEW_COVER] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INJ; sewd; IN_SEW_D; injectivity "sum"] THEN MESON_TAC[];
    REWRITE_TAC[INJ] THEN ASM_MESON_TAC[SEWR_IN_D; SEWR_INJ];
    ASM_MESON_TAC[SEWR_REV_SEWD];
    SIMP_TAC[sew_edge; sewd];
    SIMP_TAC[sew_node; sewd];
    ASM_MESON_TAC[SEW_EDGE_SEWR];
    ASM_MESON_TAC[SEW_NODE_SEWR]]);;
